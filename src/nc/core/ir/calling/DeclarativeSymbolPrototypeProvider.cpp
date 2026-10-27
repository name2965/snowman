/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "DeclarativeSymbolPrototypeProvider.h"

#include <algorithm>
#include <climits>
#include <cstdint>
#include <exception>
#include <initializer_list>
#include <istream>
#include <limits>
#include <set>
#include <sstream>
#include <streambuf>
#include <unordered_map>
#include <utility>

#include <boost/property_tree/json_parser.hpp>
#include <boost/property_tree/ptree.hpp>

#include "FunctionPrototype.h"

namespace nc {
namespace core {
namespace ir {
namespace calling {

namespace {

using boost::property_tree::ptree;

const std::size_t MAX_TARGETS = 256;
const std::size_t MAX_SYMBOLS_PER_TARGET = 1000000;
const std::size_t MAX_PARAMETERS = 1024;
const unsigned int MAX_CALLBACK_DEPTH = 16;

QString diagnosticText(const std::string &value) {
    const std::size_t length = std::min(
        value.size(), static_cast<std::size_t>(
            (std::numeric_limits<int>::max)()));
    return QString::fromUtf8(value.data(), static_cast<int>(length));
}

enum class JsonKind {
    OBJECT,
    ARRAY,
    STRING,
    NUMBER,
    BOOLEAN,
    NIL
};

using JsonShape = std::vector<JsonKind>;

/**
 * PropertyTree intentionally stores every JSON scalar as text. This small
 * lexical pass preserves the JSON kinds so the schema can reject, for
 * example, "32" where a number is required or "true" where a boolean is
 * required. PropertyTree remains responsible for UTF-8 string decoding and
 * constructing the data tree.
 */
class JsonShapeParser {
    const std::string &input_;
    std::size_t position_;
    std::string error_;

    bool fail(const char *message) {
        if (error_.empty()) {
            std::ostringstream stream;
            stream << "JSON byte " << position_ << ": " << message;
            error_ = stream.str();
        }
        return false;
    }

    void skipWhitespace() {
        while (position_ < input_.size()) {
            const char character = input_[position_];
            if (character != ' ' && character != '\t' &&
                character != '\r' && character != '\n') {
                break;
            }
            ++position_;
        }
    }

    bool consume(char expected) {
        if (position_ >= input_.size() || input_[position_] != expected) {
            return false;
        }
        ++position_;
        return true;
    }

    bool parseHexQuad(std::uint16_t &result) {
        result = 0;
        for (int digit = 0; digit < 4; ++digit) {
            if (position_ >= input_.size()) {
                return fail("truncated Unicode escape");
            }
            const char hex = input_[position_++];
            unsigned int value;
            if (hex >= '0' && hex <= '9') {
                value = static_cast<unsigned int>(hex - '0');
            } else if (hex >= 'a' && hex <= 'f') {
                value = static_cast<unsigned int>(hex - 'a') + 10;
            } else if (hex >= 'A' && hex <= 'F') {
                value = static_cast<unsigned int>(hex - 'A') + 10;
            } else {
                return fail("invalid Unicode escape");
            }
            result = static_cast<std::uint16_t>(result * 16 + value);
        }
        return true;
    }

    bool parseStringToken() {
        if (!consume('"')) {
            return fail("expected a string");
        }
        while (position_ < input_.size()) {
            const unsigned char character =
                static_cast<unsigned char>(input_[position_++]);
            if (character == '"') {
                return true;
            }
            if (character < 0x20) {
                return fail("unescaped control character in a string");
            }
            if (character >= 0x80) {
                std::uint32_t codepoint;
                std::uint32_t minimum;
                int continuationCount;
                if ((character & 0xe0) == 0xc0) {
                    codepoint = character & 0x1f;
                    minimum = 0x80;
                    continuationCount = 1;
                } else if ((character & 0xf0) == 0xe0) {
                    codepoint = character & 0x0f;
                    minimum = 0x800;
                    continuationCount = 2;
                } else if ((character & 0xf8) == 0xf0) {
                    codepoint = character & 0x07;
                    minimum = 0x10000;
                    continuationCount = 3;
                } else {
                    return fail("invalid UTF-8 leading byte");
                }
                for (int index = 0; index < continuationCount; ++index) {
                    if (position_ >= input_.size()) {
                        return fail("truncated UTF-8 sequence");
                    }
                    const unsigned char continuation =
                        static_cast<unsigned char>(input_[position_++]);
                    if ((continuation & 0xc0) != 0x80) {
                        return fail("invalid UTF-8 continuation byte");
                    }
                    codepoint = (codepoint << 6) | (continuation & 0x3f);
                }
                if (codepoint < minimum || codepoint > 0x10ffff ||
                    (codepoint >= 0xd800 && codepoint <= 0xdfff)) {
                    return fail("invalid UTF-8 code point");
                }
                continue;
            }
            if (character != '\\') {
                continue;
            }
            if (position_ >= input_.size()) {
                return fail("unterminated string escape");
            }
            const char escape = input_[position_++];
            if (escape == '"' || escape == '\\' || escape == '/' ||
                escape == 'b' || escape == 'f' || escape == 'n' ||
                escape == 'r' || escape == 't') {
                continue;
            }
            if (escape != 'u') {
                return fail("invalid string escape");
            }
            std::uint16_t codeUnit;
            if (!parseHexQuad(codeUnit)) {
                return false;
            }
            if (codeUnit >= 0xd800 && codeUnit <= 0xdbff) {
                if (!consume('\\') || !consume('u')) {
                    return fail("high surrogate is not followed by a low surrogate");
                }
                std::uint16_t lowSurrogate;
                if (!parseHexQuad(lowSurrogate)) {
                    return false;
                }
                if (lowSurrogate < 0xdc00 || lowSurrogate > 0xdfff) {
                    return fail("invalid low surrogate");
                }
            } else if (codeUnit >= 0xdc00 && codeUnit <= 0xdfff) {
                return fail("unpaired low surrogate");
            }
        }
        return fail("unterminated string");
    }

    bool parseNumberToken() {
        if (consume('-') && position_ >= input_.size()) {
            return fail("truncated number");
        }

        if (consume('0')) {
            if (position_ < input_.size() && input_[position_] >= '0' &&
                input_[position_] <= '9') {
                return fail("leading zero in a number");
            }
        } else {
            if (position_ >= input_.size() || input_[position_] < '1' ||
                input_[position_] > '9') {
                return fail("invalid number");
            }
            do {
                ++position_;
            } while (position_ < input_.size() &&
                     input_[position_] >= '0' && input_[position_] <= '9');
        }

        if (consume('.')) {
            if (position_ >= input_.size() || input_[position_] < '0' ||
                input_[position_] > '9') {
                return fail("fraction has no digits");
            }
            do {
                ++position_;
            } while (position_ < input_.size() &&
                     input_[position_] >= '0' && input_[position_] <= '9');
        }

        if (position_ < input_.size() &&
            (input_[position_] == 'e' || input_[position_] == 'E')) {
            ++position_;
            if (position_ < input_.size() &&
                (input_[position_] == '+' || input_[position_] == '-')) {
                ++position_;
            }
            if (position_ >= input_.size() || input_[position_] < '0' ||
                input_[position_] > '9') {
                return fail("exponent has no digits");
            }
            do {
                ++position_;
            } while (position_ < input_.size() &&
                     input_[position_] >= '0' && input_[position_] <= '9');
        }
        return true;
    }

    bool parseLiteral(const char *literal) {
        for (const char *character = literal; *character; ++character) {
            if (position_ >= input_.size() ||
                input_[position_] != *character) {
                return fail("invalid literal");
            }
            ++position_;
        }
        return true;
    }

    bool parseValue(JsonShape &result, unsigned int depth) {
        if (depth > 128) {
            return fail("JSON nesting is too deep");
        }
        skipWhitespace();
        if (position_ >= input_.size()) {
            return fail("expected a value");
        }

        const char first = input_[position_];
        if (first == '{') {
            result.push_back(JsonKind::OBJECT);
            ++position_;
            skipWhitespace();
            if (consume('}')) {
                return true;
            }
            for (;;) {
                if (!parseStringToken()) {
                    return false;
                }
                skipWhitespace();
                if (!consume(':')) {
                    return fail("expected ':' after an object key");
                }
                if (!parseValue(result, depth + 1)) {
                    return false;
                }
                skipWhitespace();
                if (consume('}')) {
                    return true;
                }
                if (!consume(',')) {
                    return fail("expected ',' or '}' in an object");
                }
                skipWhitespace();
            }
        }

        if (first == '[') {
            result.push_back(JsonKind::ARRAY);
            ++position_;
            skipWhitespace();
            if (consume(']')) {
                return true;
            }
            for (;;) {
                if (!parseValue(result, depth + 1)) {
                    return false;
                }
                skipWhitespace();
                if (consume(']')) {
                    return true;
                }
                if (!consume(',')) {
                    return fail("expected ',' or ']' in an array");
                }
                skipWhitespace();
            }
        }

        if (first == '"') {
            result.push_back(JsonKind::STRING);
            return parseStringToken();
        }
        if (first == '-' || (first >= '0' && first <= '9')) {
            result.push_back(JsonKind::NUMBER);
            return parseNumberToken();
        }
        if (first == 't') {
            result.push_back(JsonKind::BOOLEAN);
            return parseLiteral("true");
        }
        if (first == 'f') {
            result.push_back(JsonKind::BOOLEAN);
            return parseLiteral("false");
        }
        if (first == 'n') {
            result.push_back(JsonKind::NIL);
            return parseLiteral("null");
        }
        return fail("invalid value");
    }

public:
    explicit JsonShapeParser(const std::string &input):
        input_(input), position_(0)
    {}

    bool parse(JsonShape &result) {
        result.clear();
        if (!parseValue(result, 0)) {
            return false;
        }
        skipWhitespace();
        if (position_ != input_.size()) {
            return fail("trailing content after the root value");
        }
        return true;
    }

    const std::string &error() const { return error_; }
};

/** Read-only stream view which avoids copying the complete JSON into an
 * istringstream before PropertyTree parses it. */
class StringViewStreamBuffer: public std::streambuf {
public:
    explicit StringViewStreamBuffer(const std::string &input) {
        char *begin = const_cast<char *>(input.c_str());
        setg(begin, begin, begin + input.size());
    }
};

class DocumentParser {
    std::string error_;
    std::unordered_map<const ptree *, JsonKind> kinds_;

    bool fail(const std::string &path, const std::string &message) {
        if (error_.empty()) {
            error_ = path + ": " + message;
        }
        return false;
    }

    bool indexKinds(const ptree &node, JsonShape::const_iterator &shape,
                    const JsonShape::const_iterator &shapeEnd,
                    const std::string &path) {
        if (shape == shapeEnd) {
            return fail(path, "JSON parser structure mismatch");
        }
        kinds_[&node] = *shape++;
        std::size_t index = 0;
        for (auto nodeChild = node.begin();
             nodeChild != node.end(); ++nodeChild) {
            if (!indexKinds(nodeChild->second, shape, shapeEnd,
                            path + "[" + std::to_string(index) + "]")) {
                return false;
            }
            ++index;
        }
        return true;
    }

    bool hasKind(const ptree &node, JsonKind expected) const {
        const auto position = kinds_.find(&node);
        return position != kinds_.end() && position->second == expected;
    }

    bool validateObject(
            const ptree &node, const std::string &path,
            std::initializer_list<const char *> allowed,
            std::initializer_list<const char *> required) {
        if (!hasKind(node, JsonKind::OBJECT)) {
            return fail(path, "expected an object");
        }

        std::set<std::string> allowedSet;
        for (const char *name : allowed) {
            allowedSet.insert(name);
        }

        std::set<std::string> present;
        for (const auto &member : node) {
            if (member.first.empty()) {
                return fail(path, "expected an object, not an array");
            }
            if (!allowedSet.count(member.first)) {
                return fail(path + "." + member.first,
                            "unknown member");
            }
            if (!present.insert(member.first).second) {
                return fail(path + "." + member.first,
                            "duplicate member");
            }
        }

        for (const char *name : required) {
            if (!present.count(name)) {
                return fail(path + "." + name, "missing required member");
            }
        }
        return true;
    }

    bool validateArray(const ptree &node, const std::string &path,
                       std::size_t maximumSize) {
        if (!hasKind(node, JsonKind::ARRAY)) {
            return fail(path, "expected an array");
        }
        if (node.size() > maximumSize) {
            return fail(path, "array exceeds the schema limit");
        }
        for (const auto &element : node) {
            if (!element.first.empty()) {
                return fail(path, "expected an array, not an object");
            }
        }
        return true;
    }

    const ptree *member(const ptree &node, const char *name) const {
        for (const auto &candidate : node) {
            if (candidate.first == name) {
                return &candidate.second;
            }
        }
        return nullptr;
    }

    bool scalar(const ptree &node, const std::string &path,
                JsonKind expected, std::string &value) {
        if (!hasKind(node, expected) || !node.empty()) {
            return fail(path, "value has the wrong JSON type");
        }
        value = node.data();
        return true;
    }

    bool nonEmptyString(const ptree &node, const std::string &path,
                        std::string &value) {
        if (!scalar(node, path, JsonKind::STRING, value)) {
            return false;
        }
        if (value.empty()) {
            return fail(path, "value must not be empty");
        }
        return true;
    }

    bool qString(const std::string &value, const std::string &path,
                 QString &result) {
        if (value.size() > static_cast<std::size_t>(
                (std::numeric_limits<int>::max)())) {
            return fail(path, "UTF-8 string is too large");
        }
        result = QString::fromUtf8(
            value.data(), static_cast<int>(value.size()));
        return true;
    }

    bool nonEmptyQString(const ptree &node, const std::string &path,
                         QString &result) {
        std::string value;
        return nonEmptyString(node, path, value) &&
               qString(value, path, result);
    }

    bool exactKeyQString(const ptree &node, const std::string &path,
                         QString &result) {
        if (!nonEmptyQString(node, path, result)) {
            return false;
        }
        /* The registry preserves exact identities. Reject accidental outer
         * whitespace at this file-format boundary rather than silently
         * creating a hard-to-match export key. */
        if (result.trimmed() != result) {
            return fail(path,
                        "exact identity key must not have surrounding whitespace");
        }
        return true;
    }

    bool optionalQString(const ptree *node, const std::string &path,
                         QString &result) {
        if (!node) {
            result = QString();
            return true;
        }
        std::string value;
        return scalar(*node, path, JsonKind::STRING, value) &&
               qString(value, path, result);
    }

    static bool isIdentifierStart(char character) {
        return (character >= 'a' && character <= 'z') ||
               (character >= 'A' && character <= 'Z') ||
               character == '_';
    }

    static bool isIdentifierContinuation(char character) {
        return isIdentifierStart(character) ||
               (character >= '0' && character <= '9');
    }

    static bool isCxxKeyword(const std::string &value) {
        static const std::set<std::string> keywords = {
            "alignas", "alignof", "and", "and_eq", "asm", "auto",
            "bitand", "bitor", "bool", "break", "case", "catch",
            "char", "char16_t", "char32_t", "class", "compl", "const",
            "constexpr", "const_cast", "continue", "decltype", "default",
            "delete", "do", "double", "dynamic_cast", "else", "enum",
            "explicit", "export", "extern", "false", "float", "for",
            "friend", "goto", "if", "inline", "int", "long", "mutable",
            "namespace", "new", "noexcept", "not", "not_eq", "nullptr",
            "operator", "or", "or_eq", "private", "protected", "public",
            "register", "reinterpret_cast", "return", "short", "signed",
            "sizeof", "static", "static_assert", "static_cast", "struct",
            "switch", "template", "this", "thread_local", "throw", "true",
            "try", "typedef", "typeid", "typename", "union", "unsigned",
            "using", "virtual", "void", "volatile", "wchar_t", "while",
            "xor", "xor_eq"
        };
        return keywords.find(value) != keywords.end();
    }

    static bool isBuiltinTypeKeyword(const std::string &value) {
        static const std::set<std::string> typeKeywords = {
            "bool", "char", "char16_t", "char32_t", "double", "float",
            "int", "long", "short", "signed", "unsigned", "void",
            "wchar_t"
        };
        return typeKeywords.find(value) != typeKeywords.end();
    }

    static bool isBuiltinTypeKeyword(const QString &value) {
        return value == QLatin1String("bool") ||
               value == QLatin1String("char") ||
               value == QLatin1String("char16_t") ||
               value == QLatin1String("char32_t") ||
               value == QLatin1String("double") ||
               value == QLatin1String("float") ||
               value == QLatin1String("int") ||
               value == QLatin1String("long") ||
               value == QLatin1String("short") ||
               value == QLatin1String("signed") ||
               value == QLatin1String("unsigned") ||
               value == QLatin1String("void") ||
               value == QLatin1String("wchar_t");
    }

    bool sourceIdentifierValue(const std::string &value,
                               const std::string &path,
                               bool allowTypeKeyword) {
        if (value.empty() || !isIdentifierStart(value.front())) {
            return fail(path, "expected a C/C++ identifier");
        }
        for (char character : value) {
            if (!isIdentifierContinuation(character)) {
                return fail(path, "expected an ASCII C/C++ identifier");
            }
        }
        if (isCxxKeyword(value) &&
            (!allowTypeKeyword || !isBuiltinTypeKeyword(value))) {
            return fail(path, "C/C++ keyword cannot be used as an identifier");
        }
        return true;
    }

    bool sourceIdentifier(const ptree &node, const std::string &path,
                          QString &result, bool allowTypeKeyword = false) {
        std::string value;
        return nonEmptyString(node, path, value) &&
               sourceIdentifierValue(value, path, allowTypeKeyword) &&
               qString(value, path, result);
    }

    bool optionalSourceIdentifier(const ptree *node,
                                  const std::string &path,
                                  QString &result,
                                  bool allowTypeKeyword = false) {
        if (!node) {
            result = QString();
            return true;
        }
        std::string value;
        if (!scalar(*node, path, JsonKind::STRING, value)) {
            return false;
        }
        if (value.empty()) {
            return fail(path,
                        "explicit source identifier must not be empty");
        }
        return sourceIdentifierValue(value, path, allowTypeKeyword) &&
               qString(value, path, result);
    }

    bool boolean(const ptree &node, const std::string &path, bool &result) {
        std::string value;
        if (!scalar(node, path, JsonKind::BOOLEAN, value)) {
            return false;
        }
        if (value == "true") {
            result = true;
            return true;
        }
        if (value == "false") {
            result = false;
            return true;
        }
        return fail(path, "expected true or false");
    }

    bool signedInteger(const ptree &node, const std::string &path,
                       std::int64_t minimum, std::int64_t maximum,
                       std::int64_t &result) {
        std::string value;
        if (!scalar(node, path, JsonKind::NUMBER, value)) {
            return false;
        }
        if (value.empty()) {
            return fail(path, "expected an integer");
        }

        std::size_t position = 0;
        bool negative = false;
        if (value[position] == '-') {
            negative = true;
            if (++position == value.size()) {
                return fail(path, "expected an integer");
            }
        }

        std::uint64_t magnitude = 0;
        const std::uint64_t positiveLimit =
            static_cast<std::uint64_t>(
                (std::numeric_limits<std::int64_t>::max)());
        const std::uint64_t limit = negative ? positiveLimit + 1 :
                                               positiveLimit;
        for (; position < value.size(); ++position) {
            const char character = value[position];
            if (character < '0' || character > '9') {
                return fail(path, "expected an integer");
            }
            const unsigned int digit =
                static_cast<unsigned int>(character - '0');
            if (magnitude > (limit - digit) / 10) {
                return fail(path, "integer is out of range");
            }
            magnitude = magnitude * 10 + digit;
        }

        if (negative) {
            if (magnitude == positiveLimit + 1) {
                result = (std::numeric_limits<std::int64_t>::min)();
            } else {
                result = -static_cast<std::int64_t>(magnitude);
            }
        } else {
            result = static_cast<std::int64_t>(magnitude);
        }

        if (result < minimum || result > maximum) {
            return fail(path, "integer is outside the allowed range");
        }
        return true;
    }

    bool type(const ptree &node, const std::string &path,
              SmallBitSize targetBitness,
              TypeDescription &result) {
        if (!validateObject(
                node, path,
                {"kind", "size", "unsigned", "display_name"},
                {"kind", "size", "unsigned"})) {
            return false;
        }

        std::string kindName;
        if (!nonEmptyString(*member(node, "kind"), path + ".kind",
                            kindName)) {
            return false;
        }

        std::int64_t size = 0;
        if (!signedInteger(
                *member(node, "size"), path + ".size", 0,
                (std::numeric_limits<SmallBitSize>::max)(), size)) {
            return false;
        }

        bool isUnsigned = false;
        if (!boolean(*member(node, "unsigned"), path + ".unsigned",
                     isUnsigned)) {
            return false;
        }

        QString displayName;
        if (!optionalSourceIdentifier(
                member(node, "display_name"), path + ".display_name",
                displayName, true)) {
            return false;
        }

        TypeDescription::Kind kind;
        if (kindName == "void") {
            if (size != 0 || isUnsigned) {
                return fail(path,
                            "void must have size 0 and unsigned false");
            }
            kind = TypeDescription::VOID;
        } else if (kindName == "integer") {
            if (size == 0 || size > targetBitness) {
                return fail(path,
                            "integer size must fit one target ABI slot");
            }
            kind = TypeDescription::INTEGER;
        } else if (kindName == "pointer") {
            if (size != targetBitness || !isUnsigned) {
                return fail(path,
                            "pointer size must equal target bitness and be unsigned true");
            }
            kind = TypeDescription::POINTER;
        } else {
            return fail(path + ".kind", "unsupported scalar type kind");
        }

        if (!displayName.isEmpty() &&
            isBuiltinTypeKeyword(displayName))
        {
            bool compatibleBuiltin = false;
            if (kind == TypeDescription::VOID) {
                compatibleBuiltin = displayName == QLatin1String("void");
            } else if (kind == TypeDescription::INTEGER) {
                compatibleBuiltin =
                    (size == 32 && !isUnsigned &&
                     (displayName == QLatin1String("int") ||
                      displayName == QLatin1String("signed"))) ||
                    (size == 32 && isUnsigned &&
                     displayName == QLatin1String("unsigned")) ||
                    (size == 16 && !isUnsigned &&
                     displayName == QLatin1String("short"));
            }
            if (!compatibleBuiltin) {
                return fail(path + ".display_name",
                            "built-in spelling contradicts scalar kind, size, or signedness");
            }
        }

        result = TypeDescription(
            kind, static_cast<SmallBitSize>(size), isUnsigned,
            std::move(displayName));
        return true;
    }

    bool pointeeAccess(const ptree &node, const std::string &path,
                       ParameterDescription::PointeeAccess &result) {
        std::string value;
        if (!nonEmptyString(node, path, value)) {
            return false;
        }
        if (value == "none") {
            result = ParameterDescription::PointeeAccess::NONE;
        } else if (value == "read") {
            result = ParameterDescription::PointeeAccess::READ;
        } else if (value == "write") {
            result = ParameterDescription::PointeeAccess::WRITE;
        } else if (value == "read_write") {
            result = ParameterDescription::PointeeAccess::READ_WRITE;
        } else {
            return fail(path, "unsupported pointee access mode");
        }
        return true;
    }

    bool prototype(const ptree &node, const std::string &path,
                   unsigned int depth, SmallBitSize targetBitness,
                   std::shared_ptr<const FunctionPrototype> &result) {
        if (depth > MAX_CALLBACK_DEPTH) {
            return fail(path, "callback prototype nesting is too deep");
        }
        if (!validateObject(
                node, path,
                {"return_type", "parameters", "source_calling_convention",
                 "abi_convention", "preferred_name",
                 "memory_effects_complete", "variadic"},
                {"return_type", "parameters"})) {
            return false;
        }

        TypeDescription returnType(
            TypeDescription::VOID, 0, false);
        if (!type(*member(node, "return_type"), path + ".return_type",
                  targetBitness, returnType)) {
            return false;
        }

        const ptree &parameterNodes = *member(node, "parameters");
        if (!validateArray(
                parameterNodes, path + ".parameters", MAX_PARAMETERS)) {
            return false;
        }

        std::vector<ParameterDescription> parameters;
        parameters.reserve(parameterNodes.size());
        std::set<QString> parameterNames;
        std::size_t index = 0;
        for (const auto &element : parameterNodes) {
            const std::string parameterPath = path + ".parameters[" +
                std::to_string(index) + "]";
            const ptree &parameterNode = element.second;
            if (!validateObject(
                    parameterNode, parameterPath,
                    {"name", "type", "pointee_access", "callback"},
                    {"name", "type"})) {
                return false;
            }

            QString name;
            if (!sourceIdentifier(*member(parameterNode, "name"),
                                  parameterPath + ".name", name)) {
                return false;
            }
            if (!parameterNames.insert(name).second) {
                return fail(parameterPath + ".name",
                            "duplicate parameter identifier");
            }

            TypeDescription parameterType(
                TypeDescription::VOID, 0, false);
            if (!type(*member(parameterNode, "type"),
                      parameterPath + ".type", targetBitness,
                      parameterType)) {
                return false;
            }
            if (parameterType.kind() == TypeDescription::VOID) {
                return fail(parameterPath + ".type",
                            "a parameter cannot have void type");
            }

            ParameterDescription::PointeeAccess access =
                parameterType.kind() == TypeDescription::POINTER ?
                    ParameterDescription::PointeeAccess::READ_WRITE :
                    ParameterDescription::PointeeAccess::NONE;
            if (const ptree *accessNode =
                    member(parameterNode, "pointee_access")) {
                if (!pointeeAccess(
                        *accessNode, parameterPath + ".pointee_access",
                        access)) {
                    return false;
                }
            }
            if (parameterType.kind() != TypeDescription::POINTER &&
                access != ParameterDescription::PointeeAccess::NONE) {
                return fail(parameterPath + ".pointee_access",
                            "only pointer parameters can have pointee effects");
            }

            std::shared_ptr<const FunctionPrototype> callback;
            if (const ptree *callbackNode =
                    member(parameterNode, "callback")) {
                if (parameterType.kind() != TypeDescription::POINTER) {
                    return fail(parameterPath + ".callback",
                                "a callback parameter must be a pointer");
                }
                if (!prototype(*callbackNode, parameterPath + ".callback",
                               depth + 1, targetBitness, callback)) {
                    return false;
                }
            }

            parameters.push_back(ParameterDescription(
                std::move(name), std::move(parameterType), access,
                std::move(callback)));
            ++index;
        }

        QString sourceCallingConvention;
        if (!optionalSourceIdentifier(
                member(node, "source_calling_convention"),
                path + ".source_calling_convention",
                sourceCallingConvention)) {
            return false;
        }

        QString abiConventionName;
        const ptree *abiConventionNode = member(node, "abi_convention");
        if (depth == 0) {
            if (abiConventionNode) {
                return fail(path + ".abi_convention",
                            "top-level ABI convention belongs in the symbol record");
            }
        } else if (!abiConventionNode) {
            return fail(path + ".abi_convention",
                        "callback ABI convention is required");
        } else if (!exactKeyQString(
                       *abiConventionNode, path + ".abi_convention",
                       abiConventionName)) {
            return false;
        }

        QString preferredName;
        if (!optionalSourceIdentifier(
                member(node, "preferred_name"),
                path + ".preferred_name", preferredName)) {
            return false;
        }

        bool effectsComplete = false;
        if (const ptree *completeNode =
                member(node, "memory_effects_complete")) {
            if (!boolean(*completeNode,
                         path + ".memory_effects_complete",
                         effectsComplete)) {
                return false;
            }
        }

        bool variadic = false;
        if (const ptree *variadicNode = member(node, "variadic")) {
            if (!boolean(*variadicNode, path + ".variadic", variadic)) {
                return false;
            }
        }

        result = std::make_shared<const FunctionPrototype>(
            std::move(returnType), std::move(parameters),
            std::move(sourceCallingConvention), std::move(preferredName),
            effectsComplete, std::move(abiConventionName), variadic);
        return true;
    }

    bool symbol(const ptree &node, const std::string &path,
                SmallBitSize targetBitness,
                NamedSymbolPrototype &result) {
        if (!validateObject(
                node, path,
                {"module", "name", "convention", "stack_arguments_size",
                 "noreturn", "prototype"},
                {"module", "name", "convention", "prototype"})) {
            return false;
        }

        QString moduleName;
        QString name;
        QString convention;
        if (!exactKeyQString(*member(node, "module"), path + ".module",
                             moduleName) ||
            !exactKeyQString(*member(node, "name"), path + ".name", name) ||
            !exactKeyQString(*member(node, "convention"),
                             path + ".convention", convention)) {
            return false;
        }

        boost::optional<ByteSize> stackArgumentsSize = boost::none;
        if (const ptree *sizeNode = member(node, "stack_arguments_size")) {
            std::int64_t value = 0;
            if (!signedInteger(
                    *sizeNode, path + ".stack_arguments_size", 0,
                    (std::numeric_limits<std::int64_t>::max)(), value)) {
                return false;
            }
            stackArgumentsSize = static_cast<ByteSize>(value);
        }

        bool doesNotReturn = false;
        if (const ptree *noReturnNode = member(node, "noreturn")) {
            if (!boolean(*noReturnNode, path + ".noreturn",
                         doesNotReturn)) {
                return false;
            }
        }

        std::shared_ptr<const FunctionPrototype> functionPrototype;
        if (!prototype(*member(node, "prototype"), path + ".prototype", 0,
                       targetBitness, functionPrototype)) {
            return false;
        }
        if (functionPrototype->variadic() && stackArgumentsSize) {
            return fail(path + ".stack_arguments_size",
                        "a variadic call has no fixed total stack extent");
        }

        result = NamedSymbolPrototype(
            std::move(moduleName), std::move(name),
            SymbolPrototypeRecord(
                std::move(functionPrototype), std::move(convention),
                stackArgumentsSize, doesNotReturn));
        return true;
    }

public:
    const std::string &error() const { return error_; }

    bool parse(const ptree &root, const JsonShape &shape,
               QString &id, int &priority,
               std::vector<DeclarativeSymbolPrototypeProvider::TargetRecords>
                   &targets) {
        JsonShape::const_iterator shapePosition = shape.begin();
        if (!indexKinds(root, shapePosition, shape.end(), "$") ||
            shapePosition != shape.end()) {
            if (error_.empty()) {
                fail("$", "JSON parser structure mismatch");
            }
            return false;
        }
        if (!validateObject(
                root, "$",
                {"schema", "schema_version", "provider", "targets"},
                {"schema", "schema_version", "provider", "targets"})) {
            return false;
        }

        std::string schema;
        if (!nonEmptyString(*member(root, "schema"), "$.schema", schema)) {
            return false;
        }
        if (schema != DeclarativeSymbolPrototypeProvider::schemaName()) {
            return fail("$.schema", "unsupported schema identifier");
        }

        std::int64_t version = 0;
        if (!signedInteger(
                *member(root, "schema_version"), "$.schema_version", 0,
                (std::numeric_limits<int>::max)(), version)) {
            return false;
        }
        if (version != DeclarativeSymbolPrototypeProvider::schemaVersion()) {
            return fail("$.schema_version", "unsupported schema version");
        }

        const ptree &provider = *member(root, "provider");
        if (!validateObject(provider, "$.provider", {"id", "priority"},
                            {"id", "priority"})) {
            return false;
        }
        if (!nonEmptyQString(*member(provider, "id"), "$.provider.id", id)) {
            return false;
        }
        std::int64_t parsedPriority = 0;
        if (!signedInteger(
                *member(provider, "priority"), "$.provider.priority",
                (std::numeric_limits<int>::min)(),
                (std::numeric_limits<int>::max)(), parsedPriority)) {
            return false;
        }
        priority = static_cast<int>(parsedPriority);

        const ptree &targetNodes = *member(root, "targets");
        if (!validateArray(targetNodes, "$.targets", MAX_TARGETS)) {
            return false;
        }
        if (targetNodes.empty()) {
            return fail("$.targets", "at least one target is required");
        }

        std::size_t targetIndex = 0;
        for (const auto &targetElement : targetNodes) {
            const std::string targetPath = "$.targets[" +
                std::to_string(targetIndex) + "]";
            const ptree &targetNode = targetElement.second;
            if (!validateObject(
                    targetNode, targetPath,
                    {"architecture", "operating_system", "bitness",
                     "symbols"},
                    {"architecture", "operating_system", "bitness",
                     "symbols"})) {
                return false;
            }

            QString architecture;
            QString operatingSystem;
            if (!exactKeyQString(
                    *member(targetNode, "architecture"),
                    targetPath + ".architecture", architecture) ||
                !exactKeyQString(
                    *member(targetNode, "operating_system"),
                    targetPath + ".operating_system", operatingSystem)) {
                return false;
            }

            std::int64_t bitness = 0;
            if (!signedInteger(
                    *member(targetNode, "bitness"),
                    targetPath + ".bitness", 1,
                    (std::numeric_limits<SmallBitSize>::max)(), bitness)) {
                return false;
            }
            if (bitness % CHAR_BIT != 0) {
                return fail(targetPath + ".bitness",
                            "target bitness must be byte-aligned");
            }

            for (const auto &existing : targets) {
                if (existing.architecture == architecture &&
                    existing.operatingSystem == operatingSystem &&
                    existing.bitness == bitness) {
                    return fail(targetPath,
                                "duplicate target selector");
                }
            }

            const ptree &symbolNodes = *member(targetNode, "symbols");
            if (!validateArray(symbolNodes, targetPath + ".symbols",
                               MAX_SYMBOLS_PER_TARGET)) {
                return false;
            }
            if (symbolNodes.empty()) {
                return fail(targetPath + ".symbols",
                            "at least one symbol is required");
            }

            std::vector<NamedSymbolPrototype> prototypes;
            prototypes.reserve(symbolNodes.size());
            std::set<std::pair<QString, QString>> prototypeKeys;
            std::size_t symbolIndex = 0;
            for (const auto &symbolElement : symbolNodes) {
                NamedSymbolPrototype candidate = NamedSymbolPrototype(
                    QString(), SymbolPrototypeRecord(
                        std::shared_ptr<const FunctionPrototype>(),
                        QString()));
                const std::string symbolPath = targetPath + ".symbols[" +
                    std::to_string(symbolIndex) + "]";
                if (!symbol(symbolElement.second, symbolPath,
                            static_cast<SmallBitSize>(bitness), candidate)) {
                    return false;
                }
                /* Windows import-module identity is case-insensitive, while
                 * the registry intentionally performs exact comparisons.
                 * The Windows lookup boundary canonicalizes descriptor names
                 * to lower case. Reject a catalog key which can therefore
                 * never match, instead of accepting a seemingly valid
                 * provider and silently producing unknown prototypes. */
                if (operatingSystem == QLatin1String("windows") &&
                    candidate.moduleName() !=
                        candidate.moduleName().toLower())
                {
                    return fail(
                        symbolPath + ".module",
                        "Windows module keys must be lower-case canonical names");
                }
                if (!prototypeKeys.insert(std::make_pair(
                        candidate.moduleName(), candidate.name())).second)
                {
                    return fail(symbolPath,
                                "duplicate exact module/name pair");
                }
                prototypes.push_back(std::move(candidate));
                ++symbolIndex;
            }

            targets.push_back(
                DeclarativeSymbolPrototypeProvider::TargetRecords(
                    std::move(architecture), std::move(operatingSystem),
                    static_cast<SmallBitSize>(bitness),
                    std::move(prototypes)));
            ++targetIndex;
        }

        return true;
    }
};

} // anonymous namespace

const char *DeclarativeSymbolPrototypeProvider::schemaName() {
    return "snowman.symbol-prototypes";
}

int DeclarativeSymbolPrototypeProvider::schemaVersion() {
    return 1;
}

std::shared_ptr<const DeclarativeSymbolPrototypeProvider>
DeclarativeSymbolPrototypeProvider::fromJson(
        const std::string &json, QString *error) {
    if (error) {
        *error = QString();
    }

    try {
        JsonShape shape;
        JsonShapeParser shapeParser(json);
        if (!shapeParser.parse(shape)) {
            if (error) {
                *error = diagnosticText(shapeParser.error());
            }
            return std::shared_ptr<const DeclarativeSymbolPrototypeProvider>();
        }

        StringViewStreamBuffer streamBuffer(json);
        std::istream stream(&streamBuffer);
        ptree root;
        boost::property_tree::read_json(stream, root);

        DocumentParser parser;
        QString id;
        int priority = 0;
        std::vector<TargetRecords> targets;
        if (!parser.parse(root, shape, id, priority, targets)) {
            if (error) {
                *error = diagnosticText(parser.error());
            }
            return std::shared_ptr<const DeclarativeSymbolPrototypeProvider>();
        }

        return std::shared_ptr<const DeclarativeSymbolPrototypeProvider>(
            new DeclarativeSymbolPrototypeProvider(
                std::move(id), priority, std::move(targets)));
    } catch (const boost::property_tree::json_parser::json_parser_error
                 &exception) {
        if (error) {
            const std::string message = exception.message();
            *error = diagnosticText(message);
        }
    } catch (const std::exception &exception) {
        if (error) {
            const std::string message = exception.what();
            *error = diagnosticText(message);
        }
    }
    return std::shared_ptr<const DeclarativeSymbolPrototypeProvider>();
}

std::shared_ptr<const DeclarativeSymbolPrototypeProvider>
DeclarativeSymbolPrototypeProvider::fromJson(
        const QByteArray &json, QString *error) {
    const int size = json.size();
    return fromJson(
        size > 0 ? std::string(json.constData(), static_cast<std::size_t>(size)) :
                   std::string(),
        error);
}

std::vector<NamedSymbolPrototype>
DeclarativeSymbolPrototypeProvider::getPrototypes(
        const SymbolPrototypeTarget &target) const {
    for (const TargetRecords &candidate : targets_) {
        if (candidate.architecture == target.architecture() &&
            candidate.operatingSystem == target.operatingSystem() &&
            candidate.bitness == target.bitness()) {
            return candidate.prototypes;
        }
    }
    return std::vector<NamedSymbolPrototype>();
}

std::size_t DeclarativeSymbolPrototypeProvider::prototypeCount(
        const SymbolPrototypeTarget &target) const {
    for (const TargetRecords &candidate : targets_) {
        if (candidate.architecture == target.architecture() &&
            candidate.operatingSystem == target.operatingSystem() &&
            candidate.bitness == target.bitness()) {
            return candidate.prototypes.size();
        }
    }
    return 0;
}

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
