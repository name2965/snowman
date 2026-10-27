/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

//
// SmartDec decompiler - SmartDec is a native code to C/C++ decompiler
// Copyright (C) 2015 Alexander Chernov, Katerina Troshina, Yegor Derevenets,
// Alexander Fokin, Sergey Levin, Leonid Tsvetkov
//
// This file is part of SmartDec decompiler.
//
// SmartDec decompiler is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// SmartDec decompiler is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with SmartDec decompiler.  If not, see <http://www.gnu.org/licenses/>.
//

#include "PeParser.h"

#include <algorithm>
#include <cstddef>
#include <limits>

#include <QCoreApplication> /* For Q_DECLARE_TR_FUNCTIONS. */
#include <QIODevice>

#include <nc/common/ByteOrder.h>
#include <nc/common/Foreach.h>
#include <nc/common/LogToken.h>
#include <nc/common/StringToInt.h>
#include <nc/common/Types.h>
#include <nc/common/make_unique.h>

#include <nc/core/image/Image.h>
#include <nc/core/image/Reader.h>
#include <nc/core/image/Relocation.h>
#include <nc/core/image/Section.h>
#include <nc/core/input/ParseError.h>
#include <nc/core/input/Utils.h>

#include "pe.h"

namespace nc {
namespace input {
namespace pe {

namespace {

using nc::core::input::read;
using nc::core::input::getAsciizString;
using nc::core::input::ParseError;

const ByteOrder peByteOrder = ByteOrder::LittleEndian;

bool seekFileHeader(QIODevice *source) {
    IMAGE_DOS_HEADER dosHeader;

    if (!read(source, dosHeader)) {
        return false;
    }

    peByteOrder.convertFrom(dosHeader.e_magic);
    peByteOrder.convertFrom(dosHeader.e_lfanew);

    if (dosHeader.e_magic != IMAGE_DOS_SIGNATURE) {
        return false;
    }

    if (!source->seek(dosHeader.e_lfanew)) {
        return false;
    }

    uint32_t signature;
    if (!read(source, signature)) {
        return false;
    }
    peByteOrder.convertFrom(signature);

    if (signature != IMAGE_NT_SIGNATURE) {
        return false;
    }

    return true;
}

struct IMPORT_LOOKUP_TABLE_ENTRY32 {
    uint32_t RawValue;
};

struct IMPORT_LOOKUP_TABLE_ENTRY64 {
    uint64_t RawValue;
};

static_assert(sizeof(IMPORT_LOOKUP_TABLE_ENTRY32) == sizeof(uint32_t), "");
static_assert(sizeof(IMPORT_LOOKUP_TABLE_ENTRY64) == sizeof(uint64_t), "");

struct DELAY_IMPORT_DESCRIPTOR {
    uint32_t Attributes;
    uint32_t Name;
    uint32_t ModuleHandle;
    uint32_t ImportAddressTable;
    uint32_t ImportNameTable;
    uint32_t BoundImportAddressTable;
    uint32_t UnloadImportAddressTable;
    uint32_t TimeDateStamp;
};

static_assert(sizeof(DELAY_IMPORT_DESCRIPTOR) == 32, "");

struct AMD64_RUNTIME_FUNCTION {
    uint32_t BeginAddress;
    uint32_t EndAddress;
    uint32_t UnwindInfoAddress;
};

static_assert(sizeof(AMD64_RUNTIME_FUNCTION) == 12, "");

template<class IMAGE_OPTIONAL_HEADER, class IMPORT_LOOKUP_TABLE_ENTRY>
class PeParserImpl {
    Q_DECLARE_TR_FUNCTIONS(PeParserImpl)

    QIODevice *source_;
    core::image::Image *image_;
    const LogToken &log_;

    ByteAddr optionalHeaderOffset_;
    IMAGE_FILE_HEADER &fileHeader_;
    IMAGE_OPTIONAL_HEADER optionalHeader_;
    std::size_t dataDirectoryCount_ = 0;

public:
    PeParserImpl(QIODevice *source, core::image::Image *image, const LogToken &log, IMAGE_FILE_HEADER &fileHeader):
        source_(source), image_(image), log_(log), fileHeader_(fileHeader)
    {}

    void parse() {
        optionalHeaderOffset_ = source_->pos() - sizeof(optionalHeader_.Magic);

        parseFileHeader();
        parseOptionalHeader();
        parseSections();
        parseRuntimeFunctions();
        parseSymbols();
        parseImports();
        parseDelayImports();
        parseBaseRelocs();
        parseExports();

        ByteAddr entryPoint = 0;
        if (getLinearAddress(
                optionalHeader_.AddressOfEntryPoint, true, entryPoint))
        {
            image_->setEntryPoint(entryPoint);
        } else {
            log_.warning(tr("Image entry point address overflows the address space."));
        }
    }

private:
    bool getFileRange(uint64_t offset, uint64_t size,
                      qint64 &fileOffset, qint64 &fileSize) const {
        const uint64_t maximum = static_cast<uint64_t>(
            (std::numeric_limits<qint64>::max)());
        if (offset > maximum || size > maximum - offset) {
            return false;
        }

        const qint64 sourceSize = source_->size();
        if (sourceSize < 0 || offset + size >
                static_cast<uint64_t>(sourceSize))
        {
            return false;
        }

        fileOffset = static_cast<qint64>(offset);
        fileSize = static_cast<qint64>(size);
        return true;
    }

    QString readFileAsciizString(uint64_t offset,
                                 uint64_t maximumSize) const {
        static const uint64_t MaximumCoffNameSize = 1048576;

        qint64 fileOffset = 0;
        qint64 fileSize = 0;
        const uint64_t readSize = std::min(
            maximumSize, MaximumCoffNameSize);
        if (readSize == 0 ||
            !getFileRange(offset, readSize, fileOffset, fileSize))
        {
            return QString();
        }

        const qint64 oldPosition = source_->pos();
        if (!source_->seek(fileOffset)) {
            return QString();
        }
        QByteArray bytes = source_->read(fileSize);
        source_->seek(oldPosition);
        if (bytes.size() != fileSize) {
            return QString();
        }

        const char *begin = bytes.constData();
        const char *end = begin + bytes.size();
        const char *terminator = std::find(begin, end, '\0');
        if (terminator == end) {
            return QString();
        }
        return QString::fromLatin1(
            begin, static_cast<int>(terminator - begin));
    }

    bool getImageRange(uint64_t value, bool valueIsRva, uint64_t size,
                       ByteAddr &result) const {
        if (size == 0 ||
            !getImageAddress(value, valueIsRva, result))
        {
            return false;
        }

        const core::image::Section *section =
            image_->getSectionContainingAddress(result);
        return section && size <= static_cast<uint64_t>(
            section->endAddr() - result);
    }

    const core::image::Section *getStoredSectionContainingAddress(
            ByteAddr address) const {
        foreach (const core::image::Section *section, image_->sections()) {
            if (section->containsAddress(address)) {
                return section;
            }
        }
        return nullptr;
    }

    static bool getRelativeAddend(uint64_t value, uint64_t base,
                                  ByteSize &result) {
        const uint64_t maximum = static_cast<uint64_t>(
            (std::numeric_limits<ByteSize>::max)());
        if (value >= base) {
            const uint64_t difference = value - base;
            if (difference > maximum) {
                return false;
            }
            result = static_cast<ByteSize>(difference);
        } else {
            const uint64_t difference = base - value;
            if (difference > maximum + uint64_t(1)) {
                return false;
            }
            if (difference == maximum + uint64_t(1)) {
                result = (std::numeric_limits<ByteSize>::min)();
            } else {
                result = -static_cast<ByteSize>(difference);
            }
        }
        return true;
    }

    void parseFileHeader() {
        /*
         * fileHeader_.Characteristics contains endianness flags:
         * IMAGE_FILE_BYTES_REVERSED_LO for little endian,
         * IMAGE_FILE_BYTES_REVERSED_HI for big endian.
         * However, it is unclear how to get these flags without
         * knowing the endianness in which Characteristics are stored...
         */
        peByteOrder.convertFrom(fileHeader_.PointerToSymbolTable);
        peByteOrder.convertFrom(fileHeader_.NumberOfSymbols);
        peByteOrder.convertFrom(fileHeader_.NumberOfSections);
        peByteOrder.convertFrom(fileHeader_.SizeOfOptionalHeader);
    }

    void parseOptionalHeader() {
        if (!source_->seek(optionalHeaderOffset_)) {
            throw ParseError(tr("Cannot seek to the optional header."));
        }

        const std::size_t fixedHeaderSize =
            offsetof(IMAGE_OPTIONAL_HEADER, DataDirectory);
        if (fileHeader_.SizeOfOptionalHeader < fixedHeaderSize) {
            throw ParseError(tr("The PE optional header is truncated."));
        }

        optionalHeader_ = IMAGE_OPTIONAL_HEADER();
        const std::size_t readSize = std::min<std::size_t>(
            fileHeader_.SizeOfOptionalHeader, sizeof(optionalHeader_));
        if (source_->read(
                reinterpret_cast<char *>(&optionalHeader_), readSize) !=
            static_cast<qint64>(readSize))
        {
            throw ParseError(tr("Cannot read the optional header."));
        }

        peByteOrder.convertFrom(optionalHeader_.Magic);
        peByteOrder.convertFrom(optionalHeader_.ImageBase);
        peByteOrder.convertFrom(optionalHeader_.AddressOfEntryPoint);
        peByteOrder.convertFrom(optionalHeader_.NumberOfRvaAndSizes);

        const std::size_t physicalDirectoryCount =
            (readSize - fixedHeaderSize) /
            sizeof(optionalHeader_.DataDirectory[0]);
        const std::size_t maximumDirectoryCount =
            sizeof(optionalHeader_.DataDirectory) /
            sizeof(optionalHeader_.DataDirectory[0]);
        dataDirectoryCount_ = std::min<std::size_t>(
            optionalHeader_.NumberOfRvaAndSizes,
            std::min(physicalDirectoryCount, maximumDirectoryCount));

        for (std::size_t index = 0;
             index < dataDirectoryCount_; ++index)
        {
            peByteOrder.convertFrom(
                optionalHeader_.DataDirectory[index].VirtualAddress);
            peByteOrder.convertFrom(
                optionalHeader_.DataDirectory[index].Size);
        }
        for (std::size_t index = dataDirectoryCount_;
             index < maximumDirectoryCount; ++index)
        {
            optionalHeader_.DataDirectory[index] = IMAGE_DATA_DIRECTORY();
        }
    }

    void parseSections() {
        if (!source_->seek(optionalHeaderOffset_ + fileHeader_.SizeOfOptionalHeader)) {
            log_.warning(tr("Cannot seek to the section header table."));
            return;
        }

        for (std::size_t i = 0; i < fileHeader_.NumberOfSections; ++i) {
            IMAGE_SECTION_HEADER sectionHeader;
            if (!read(source_, sectionHeader)) {
                log_.warning(tr("Cannot read the section header number %1.").arg(i));
                return;
            }

            peByteOrder.convertFrom(sectionHeader.VirtualAddress);
            peByteOrder.convertFrom(sectionHeader.Misc.VirtualSize);
            peByteOrder.convertFrom(sectionHeader.SizeOfRawData);
            peByteOrder.convertFrom(sectionHeader.Characteristics);
            peByteOrder.convertFrom(sectionHeader.PointerToRawData);

            ByteAddr sectionAddress = 0;
            const uint64_t sectionSize = std::max<uint64_t>(
                sectionHeader.Misc.VirtualSize,
                sectionHeader.SizeOfRawData);
            if (!getLinearAddress(
                    sectionHeader.VirtualAddress, true, sectionAddress) ||
                sectionSize > static_cast<uint64_t>(
                    (std::numeric_limits<ByteAddr>::max)()) -
                    static_cast<uint64_t>(sectionAddress))
            {
                throw ParseError(tr(
                    "Image section number %1 exceeds the address space.").arg(i));
            }

            auto section = std::make_unique<core::image::Section>(
                getAsciizString(sectionHeader.Name), sectionAddress,
                static_cast<ByteSize>(sectionSize));

            section->setAllocated((sectionHeader.Characteristics & IMAGE_SCN_MEM_DISCARDABLE) == 0);
            section->setReadable(sectionHeader.Characteristics & IMAGE_SCN_MEM_READ);
            section->setWritable(sectionHeader.Characteristics & IMAGE_SCN_MEM_WRITE);
            section->setExecutable(sectionHeader.Characteristics & IMAGE_SCN_MEM_EXECUTE);

            section->setCode(sectionHeader.Characteristics & IMAGE_SCN_CNT_CODE);
            section->setData(sectionHeader.Characteristics & IMAGE_SCN_CNT_INITIALIZED_DATA);
            section->setBss(sectionHeader.Characteristics & IMAGE_SCN_CNT_UNINITIALIZED_DATA);

            if (sectionHeader.SizeOfRawData == 0) {
                log_.debug(tr("Section %1 has no raw data.").arg(section->name()));
            } else {
                log_.debug(tr("Reading contents of section %1 (size of raw data = 0x%2).").arg(section->name()).arg(sectionHeader.SizeOfRawData));

                qint64 rawOffset = 0;
                qint64 rawSize = 0;
                if (sectionHeader.SizeOfRawData >
                        static_cast<uint64_t>(
                            (std::numeric_limits<int>::max)()) ||
                    !getFileRange(
                        sectionHeader.PointerToRawData,
                        sectionHeader.SizeOfRawData,
                        rawOffset, rawSize))
                {
                    throw ParseError(tr(
                        "Raw data of image section number %1 is outside of the input file.").arg(i));
                }

                const qint64 oldPosition = source_->pos();
                if (!source_->seek(rawOffset)) {
                    throw ParseError(tr(
                        "Cannot seek to the data of image section number %1.").arg(i));
                }
                QByteArray bytes = source_->read(rawSize);
                if (!source_->seek(oldPosition)) {
                    throw ParseError(tr(
                        "Cannot return to the image section table."));
                }
                if (bytes.size() != rawSize) {
                    throw ParseError(tr(
                        "Cannot read all raw data of image section number %1.").arg(i));
                }
                section->setContent(std::move(bytes));
            }

            image_->addSection(std::move(section));
        }
    }

    void parseSymbols() {
        if (!fileHeader_.PointerToSymbolTable || !fileHeader_.NumberOfSymbols) {
            return;
        }

        static const uint32_t MaximumCoffSymbolCount = 1048576;
        if (fileHeader_.NumberOfSymbols > MaximumCoffSymbolCount) {
            log_.warning(tr("COFF symbol table has too many records."));
            return;
        }

        /*
         * http://www.delorie.com/djgpp/doc/coff/symtab.html
         */
        const uint64_t symbolTableOffset =
            fileHeader_.PointerToSymbolTable;
        const uint64_t symbolTableSize =
            uint64_t(fileHeader_.NumberOfSymbols) * sizeof(IMAGE_SYMBOL);
        qint64 checkedOffset = 0;
        qint64 checkedSize = 0;
        if (!getFileRange(symbolTableOffset, symbolTableSize,
                          checkedOffset, checkedSize))
        {
            log_.warning(tr("COFF symbol table is outside of the input file."));
            return;
        }

        const uint64_t stringTableOffset =
            symbolTableOffset + symbolTableSize;
        if (!getFileRange(stringTableOffset, sizeof(uint32_t),
                          checkedOffset, checkedSize) ||
            !source_->seek(checkedOffset))
        {
            log_.warning(tr("Cannot read the size of the COFF string table."));
            return;
        }
        uint32_t stringTableSize;
        if (!read(source_, stringTableSize)) {
            log_.warning(tr("Cannot read the size of the COFF string table."));
            return;
        }
        peByteOrder.convertFrom(stringTableSize);

        if (stringTableSize < sizeof(stringTableSize) ||
            !getFileRange(stringTableOffset, stringTableSize,
                          checkedOffset, checkedSize))
        {
            log_.warning(tr("COFF string table has an invalid size."));
            return;
        }

        for (uint32_t index = 0;
             index < fileHeader_.NumberOfSymbols;)
        {
            const uint64_t recordOffset = symbolTableOffset +
                uint64_t(index) * sizeof(IMAGE_SYMBOL);
            if (!source_->seek(static_cast<qint64>(recordOffset))) {
                log_.warning(tr("Cannot seek to a COFF symbol record."));
                return;
            }

            IMAGE_SYMBOL symbol = {};
            if (!read(source_, symbol)) {
                log_.warning(tr("Cannot read a COFF symbol record."));
                return;
            }
            if (symbol.NumberOfAuxSymbols >
                    fileHeader_.NumberOfSymbols - index - 1)
            {
                log_.warning(tr(
                    "COFF symbol record has too many auxiliary records."));
                return;
            }

            peByteOrder.convertFrom(symbol.Type);
            peByteOrder.convertFrom(symbol.Value);
            peByteOrder.convertFrom(symbol.SectionNumber);

            using core::image::Symbol;
            using core::image::SymbolType;

            SymbolType type;
            /*
             * Microsoft tools set this field to 0x20 (function) or 0x0 (not a function).
             * -- http://www.kishorekumar.net/pecoff_v8.1.htm
             */
            if (symbol.Type == 0x20) {
                type = SymbolType::FUNCTION;
            } else {
                type = SymbolType::NOTYPE;
            }

            QString name;
            if (symbol.N.Name.Short) {
                name = getAsciizString(symbol.N.ShortName);
            } else {
                peByteOrder.convertFrom(symbol.N.Name.Long);
                if (symbol.N.Name.Long >= sizeof(stringTableSize) &&
                    symbol.N.Name.Long < stringTableSize)
                {
                    name = readFileAsciizString(
                        stringTableOffset + symbol.N.Name.Long,
                        stringTableSize - symbol.N.Name.Long);
                }
            }

            ByteAddr value = symbol.Value;
            const core::image::Section *section = nullptr;

            const std::size_t sectionNumber = symbol.SectionNumber > 0 ?
                static_cast<std::size_t>(symbol.SectionNumber - 1) :
                image_->sections().size();
            if (sectionNumber < image_->sections().size()) {
                section = image_->sections()[sectionNumber];
                if (static_cast<uint64_t>(symbol.Value) >
                        static_cast<uint64_t>(
                            (std::numeric_limits<ByteAddr>::max)()) -
                        static_cast<uint64_t>(section->addr()))
                {
                    log_.warning(tr(
                        "COFF symbol value exceeds the address space."));
                    index += uint32_t(symbol.NumberOfAuxSymbols) + 1;
                    continue;
                }
                value = section->addr() + symbol.Value;
            }

            image_->addSymbol(std::make_unique<Symbol>(type, name, value, section));
            index += uint32_t(symbol.NumberOfAuxSymbols) + 1;
        }

        foreach (auto section, image_->sections()) {
            if (section->name().startsWith('/')) {
                if (auto offset = stringToInt<uint32_t>(section->name().mid(1))) {
                    QString newName;
                    if (*offset >= sizeof(stringTableSize) &&
                        *offset < stringTableSize)
                    {
                        newName = readFileAsciizString(
                            stringTableOffset + *offset,
                            stringTableSize - *offset);
                    }
                    if (!newName.isEmpty()) {
                        section->setName(newName);
                    }
                }
            }
        }
    }

    void parseImports() {
        const auto &directory = optionalHeader_.DataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT];
        if (directory.VirtualAddress == 0) {
            return;
        }

        auto reader = core::image::Reader(image_);

        IMAGE_IMPORT_DESCRIPTOR descriptor;
        ByteAddr descriptorAddress = 0;
        if (!getImageAddress(
                directory.VirtualAddress, true, descriptorAddress))
        {
            log_.warning(tr(
                "Image import directory is outside of the image sections."));
            return;
        }
        const auto *descriptorSection = image_->getSectionContainingAddress(descriptorAddress);
        if (!descriptorSection) {
            log_.warning(tr("Image import directory is outside of the image sections."));
            return;
        }

        ByteSize descriptorCount = (descriptorSection->endAddr() - descriptorAddress) / sizeof(descriptor);
        if (directory.Size == 0) {
            log_.warning(tr(
                "Image import directory has no size; using its section boundary."));
        } else if (directory.Size < sizeof(descriptor)) {
            log_.warning(tr("Image import directory is truncated."));
            return;
        } else {
            descriptorCount = std::min(descriptorCount, static_cast<ByteSize>(directory.Size / sizeof(descriptor)));
            if (directory.Size % sizeof(descriptor) != 0) {
                log_.warning(tr(
                    "Image import directory has a truncated descriptor."));
            }
        }
        descriptorCount = std::min<ByteSize>(descriptorCount, 4096);
        ByteSize remainingImportEntries = 65536;
        bool foundTerminator = false;

        for (ByteSize i = 0; i < descriptorCount; ++i, descriptorAddress += sizeof(descriptor)) {
            if (image_->readBytes(descriptorAddress, reinterpret_cast<char *>(&descriptor), sizeof(descriptor)) !=
                sizeof(descriptor)) {
                log_.warning(tr("Cannot read the image import descriptor number %1.").arg(i));
                return;
            }

            peByteOrder.convertFrom(descriptor.OriginalFirstThunk);
            peByteOrder.convertFrom(descriptor.TimeDateStamp);
            peByteOrder.convertFrom(descriptor.ForwarderChain);
            peByteOrder.convertFrom(descriptor.Name);
            peByteOrder.convertFrom(descriptor.FirstThunk);

            if (descriptor.OriginalFirstThunk == 0 && descriptor.TimeDateStamp == 0 && descriptor.ForwarderChain == 0 &&
                descriptor.Name == 0 && descriptor.FirstThunk == 0) {
                foundTerminator = true;
                break;
            }

            if (descriptor.Name == 0 || descriptor.FirstThunk == 0) {
                log_.warning(tr("Image import descriptor number %1 is malformed.").arg(i));
                continue;
            }

            ByteAddr dllNameAddress = 0;
            ByteAddr lookupTableAddress = 0;
            ByteAddr importAddressTableAddress = 0;
            /* When OriginalFirstThunk is absent, the on-disk IAT is the only
             * possible source of names. A bound or loader-resolved IAT holds
             * target addresses instead; PE metadata contains no general way
             * to reconstruct the discarded Hint/Name entries. */
            const uint32_t lookupTable = descriptor.OriginalFirstThunk ?
                descriptor.OriginalFirstThunk : descriptor.FirstThunk;
            if (!getImageAddress(
                    descriptor.Name, true, dllNameAddress) ||
                !getImageAddress(
                    lookupTable, true, lookupTableAddress) ||
                !getImageAddress(
                    descriptor.FirstThunk, true,
                    importAddressTableAddress))
            {
                log_.warning(tr(
                    "Image import descriptor number %1 contains an invalid address.").arg(i));
                continue;
            }

            auto dllName = reader.readAsciizString(dllNameAddress, 1024);
            if (dllName.isEmpty()) {
                log_.warning(tr(
                    "Cannot read the name of an imported DLL."));
                continue;
            }
            log_.debug(tr("Found imports from DLL: %1").arg(dllName));

            parseImportAddressTable(dllName, lookupTableAddress,
                                    importAddressTableAddress,
                                    remainingImportEntries, true);
            if (remainingImportEntries == 0) {
                log_.warning(tr("Image has too many import table entries."));
                return;
            }
        }

        if (!foundTerminator) {
            log_.warning(tr("Image import descriptor table is not null-terminated within its directory."));
        }
    }

    bool getLinearAddress(uint64_t value, bool valueIsRva,
                          ByteAddr &result) const {
        const uint64_t base = static_cast<uint64_t>(optionalHeader_.ImageBase);
        uint64_t address = value;
        if (valueIsRva) {
            if (address > (std::numeric_limits<uint64_t>::max)() - base) {
                return false;
            }
            address += base;
        }
        if (address > static_cast<uint64_t>(
                (std::numeric_limits<ByteAddr>::max)()))
        {
            return false;
        }

        result = static_cast<ByteAddr>(address);
        return true;
    }

    bool getImageAddress(uint64_t value, bool valueIsRva,
                         ByteAddr &result) const {
        if (value == 0 || !getLinearAddress(value, valueIsRva, result)) {
            return false;
        }
        return image_->getSectionContainingAddress(result) != nullptr;
    }

    void parseRuntimeFunctions() {
        /* IMAGE_RUNTIME_FUNCTION_ENTRY is architecture-specific. The AMD64
         * form is a sorted array of exact [begin,end) code ranges and is
         * authoritative function-boundary evidence. Other PE machines use
         * different packed formats and must not be guessed here. */
        if (fileHeader_.Machine != IMAGE_FILE_MACHINE_AMD64) {
            return;
        }

        const auto &directory =
            optionalHeader_.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXCEPTION];
        if (directory.VirtualAddress == 0 ||
            directory.Size < sizeof(AMD64_RUNTIME_FUNCTION))
        {
            return;
        }

        ByteAddr directoryAddress = 0;
        if (!getImageAddress(
                directory.VirtualAddress, true, directoryAddress))
        {
            log_.warning(tr(
                "Image exception directory is outside of the image sections."));
            return;
        }
        const core::image::Section *directorySection =
            image_->getSectionContainingAddress(directoryAddress);
        if (!directorySection) {
            return;
        }

        ByteSize entryCount = std::min<ByteSize>(
            directory.Size / sizeof(AMD64_RUNTIME_FUNCTION),
            (directorySection->endAddr() - directoryAddress) /
                sizeof(AMD64_RUNTIME_FUNCTION));
        /* A malformed image must not turn metadata parsing into an
         * unbounded whole-file scan. */
        entryCount = std::min<ByteSize>(entryCount, 1048576);
        if (directory.Size % sizeof(AMD64_RUNTIME_FUNCTION) != 0) {
            log_.warning(tr(
                "Image exception directory has a truncated runtime-function entry."));
        }

        for (ByteSize index = 0; index < entryCount; ++index) {
            AMD64_RUNTIME_FUNCTION entry = {};
            const ByteAddr entryAddress = directoryAddress +
                index * sizeof(AMD64_RUNTIME_FUNCTION);
            if (image_->readBytes(
                    entryAddress, reinterpret_cast<char *>(&entry),
                    sizeof(entry)) != sizeof(entry))
            {
                log_.warning(tr(
                    "Cannot read runtime-function entry number %1.").arg(index));
                return;
            }
            peByteOrder.convertFrom(entry.BeginAddress);
            peByteOrder.convertFrom(entry.EndAddress);
            peByteOrder.convertFrom(entry.UnwindInfoAddress);

            if (entry.BeginAddress >= entry.EndAddress ||
                entry.UnwindInfoAddress == 0 ||
                entry.UnwindInfoAddress % 4 != 0)
            {
                continue;
            }

            ByteAddr beginAddress = 0;
            ByteAddr lastAddress = 0;
            ByteAddr unwindAddress = 0;
            if (!getImageAddress(
                    entry.BeginAddress, true, beginAddress) ||
                !getImageAddress(
                    entry.EndAddress - 1, true, lastAddress) ||
                !getImageAddress(
                    entry.UnwindInfoAddress, true, unwindAddress))
            {
                continue;
            }

            uint8_t unwindVersionAndFlags = 0;
            if (image_->readBytes(
                    unwindAddress, &unwindVersionAndFlags,
                    sizeof(unwindVersionAndFlags)) !=
                    sizeof(unwindVersionAndFlags) ||
                (unwindVersionAndFlags & 0x7) == 0 ||
                ((unwindVersionAndFlags >> 3) & 0x4) != 0)
            {
                /* Chained unwind records describe secondary regions of an
                 * existing function, not independent callable entries. */
                continue;
            }

            const core::image::Section *beginSection =
                image_->getSectionContainingAddress(beginAddress);
            const core::image::Section *endSection =
                image_->getSectionContainingAddress(lastAddress);
            if (!beginSection || !endSection ||
                beginSection != endSection ||
                !beginSection->isExecutable() ||
                !endSection->isExecutable())
            {
                continue;
            }

            image_->addFunctionEntry(beginAddress);
        }
    }

    void parseDelayImports() {
        const auto &directory =
            optionalHeader_.DataDirectory[IMAGE_DIRECTORY_ENTRY_DELAY_IMPORT];
        if (directory.VirtualAddress == 0) {
            return;
        }

        ByteAddr descriptorAddress = 0;
        if (!getImageAddress(
                directory.VirtualAddress, true, descriptorAddress))
        {
            log_.warning(tr(
                "Image delay-import directory is outside of the image sections."));
            return;
        }
        const auto *descriptorSection =
            image_->getSectionContainingAddress(descriptorAddress);
        if (!descriptorSection) {
            log_.warning(tr("Image delay-import directory is outside of the image sections."));
            return;
        }

        DELAY_IMPORT_DESCRIPTOR descriptor;
        ByteSize descriptorCount =
            (descriptorSection->endAddr() - descriptorAddress) /
            sizeof(descriptor);
        if (directory.Size == 0) {
            log_.warning(tr(
                "Image delay-import directory has no size; using its section boundary."));
        } else if (directory.Size < sizeof(descriptor)) {
            log_.warning(tr(
                "Image delay-import directory is truncated."));
            return;
        } else {
            descriptorCount = std::min(
                descriptorCount,
                static_cast<ByteSize>(directory.Size / sizeof(descriptor)));
            if (directory.Size % sizeof(descriptor) != 0) {
                log_.warning(tr(
                    "Image delay-import directory has a truncated descriptor."));
            }
        }
        descriptorCount = std::min<ByteSize>(descriptorCount, 4096);

        core::image::Reader reader(image_);
        ByteSize remainingImportEntries = 65536;
        bool foundTerminator = false;
        for (ByteSize i = 0; i < descriptorCount;
             ++i, descriptorAddress += sizeof(descriptor))
        {
            if (image_->readBytes(
                    descriptorAddress,
                    reinterpret_cast<char *>(&descriptor),
                    sizeof(descriptor)) != sizeof(descriptor))
            {
                log_.warning(tr(
                    "Cannot read the image delay-import descriptor number %1.").arg(i));
                return;
            }

            peByteOrder.convertFrom(descriptor.Attributes);
            peByteOrder.convertFrom(descriptor.Name);
            peByteOrder.convertFrom(descriptor.ModuleHandle);
            peByteOrder.convertFrom(descriptor.ImportAddressTable);
            peByteOrder.convertFrom(descriptor.ImportNameTable);
            peByteOrder.convertFrom(descriptor.BoundImportAddressTable);
            peByteOrder.convertFrom(descriptor.UnloadImportAddressTable);
            peByteOrder.convertFrom(descriptor.TimeDateStamp);

            if (descriptor.Attributes == 0 && descriptor.Name == 0 &&
                descriptor.ModuleHandle == 0 &&
                descriptor.ImportAddressTable == 0 &&
                descriptor.ImportNameTable == 0 &&
                descriptor.BoundImportAddressTable == 0 &&
                descriptor.UnloadImportAddressTable == 0 &&
                descriptor.TimeDateStamp == 0)
            {
                foundTerminator = true;
                break;
            }

            /* Version one defines only bit zero (fields are RVAs). Unknown
             * bits can change the interpretation of every pointer. */
            if (descriptor.Attributes & ~uint32_t(1)) {
                log_.warning(tr(
                    "Image delay-import descriptor number %1 has unsupported attributes.").arg(i));
                continue;
            }
            const bool fieldsAreRvas = (descriptor.Attributes & 1) != 0;

            ByteAddr nameAddress = 0;
            ByteAddr lookupTableAddress = 0;
            ByteAddr importAddressTableAddress = 0;
            if (!getImageAddress(
                    descriptor.Name, fieldsAreRvas, nameAddress) ||
                !getImageAddress(
                    descriptor.ImportNameTable, fieldsAreRvas,
                    lookupTableAddress) ||
                !getImageAddress(
                    descriptor.ImportAddressTable, fieldsAreRvas,
                    importAddressTableAddress))
            {
                log_.warning(tr(
                    "Image delay-import descriptor number %1 is malformed.").arg(i));
                continue;
            }

            const QString dllName =
                reader.readAsciizString(nameAddress, 1024);
            if (dllName.isEmpty()) {
                log_.warning(tr(
                    "Cannot read the name of a delay-imported DLL."));
                continue;
            }
            log_.debug(tr("Found delay imports from DLL: %1").arg(dllName));

            parseImportAddressTable(
                dllName, lookupTableAddress, importAddressTableAddress,
                remainingImportEntries, fieldsAreRvas);
            if (remainingImportEntries == 0) {
                log_.warning(tr(
                    "Image has too many delay-import table entries."));
                return;
            }
        }

        if (!foundTerminator) {
            log_.warning(tr(
                "Image delay-import descriptor table is not null-terminated within its directory."));
        }
    }

    void parseImportAddressTable(const QString &dllName, ByteAddr lookupTableAddress,
                                 ByteAddr importAddressTableAddress,
                                 ByteSize &remainingImportEntries,
                                 bool namesAreRvas) {
        auto reader = core::image::Reader(image_);

        const auto *lookupSection = image_->getSectionContainingAddress(lookupTableAddress);
        const auto *importSection = image_->getSectionContainingAddress(importAddressTableAddress);
        if (!lookupSection || !importSection) {
            log_.warning(tr("Import lookup or address table is outside of the image sections."));
            return;
        }

        const ByteSize entrySize = sizeof(IMPORT_LOOKUP_TABLE_ENTRY);
        auto lookupEntryCount = (lookupSection->endAddr() - lookupTableAddress) / entrySize;
        auto importEntryCount = (importSection->endAddr() - importAddressTableAddress) / entrySize;
        auto entryCount = std::min(std::min(lookupEntryCount, importEntryCount), remainingImportEntries);

        IMPORT_LOOKUP_TABLE_ENTRY entry;
        bool foundTerminator = false;
        for (ByteSize i = 0; i < entryCount; ++i) {
            auto lookupEntryAddress = lookupTableAddress + i * entrySize;
            auto importEntryAddress = importAddressTableAddress + i * entrySize;

            if (image_->readBytes(lookupEntryAddress, reinterpret_cast<char *>(&entry), sizeof(entry)) !=
                sizeof(entry)) {
                log_.warning(tr("Cannot read an import lookup table entry."));
                return;
            }

            peByteOrder.convertFrom(entry.RawValue);

            if (entry.RawValue == 0) {
                foundTerminator = true;
                break;
            }
            --remainingImportEntries;

            const uint64_t rawEntry =
                static_cast<uint64_t>(entry.RawValue);
            const uint64_t ordinalFlag =
                uint64_t(1) << (entrySize * 8 - 1);
            const uint64_t entryValue = rawEntry & ~ordinalFlag;
            if (rawEntry & ordinalFlag) {
                if ((entryValue & ~uint64_t(0xffff)) != 0) {
                    log_.warning(tr(
                        "Import-by-ordinal entry has nonzero reserved bits."));
                    continue;
                }
                const uint64_t ordinal = entryValue & 0xffff;
                log_.debug(tr("Found an import by ordinal value: %1").arg(ordinal));

                image_->addRelocation(std::make_unique<core::image::Relocation>(
                    importEntryAddress,
                    image_->addSymbol(std::make_unique<core::image::Symbol>(
                        core::image::SymbolType::FUNCTION,
                        tr("%1:%2").arg(dllName).arg(ordinal), boost::none,
                        nullptr, dllName,
                        core::image::ExternalNameOrigin::UNKNOWN)),
                    entrySize));
            } else {
                /* A Hint/Name entry has a 31-bit RVA in both formats.
                 * Bits 62..31 are reserved in a PE32+ RVA-based thunk. */
                if (namesAreRvas &&
                    entryValue > uint64_t(0x7fffffff))
                {
                    log_.warning(tr(
                        "Imported function name RVA has nonzero reserved bits."));
                    continue;
                }

                ByteAddr nameAddress = 0;
                if (!getImageAddress(
                        entryValue, namesAreRvas, nameAddress))
                {
                    log_.warning(tr(
                        "Imported function name is outside of the image sections."));
                    continue;
                }
                const core::image::Section *nameSection =
                    image_->getSectionContainingAddress(nameAddress);
                if (!nameSection ||
                    nameSection->endAddr() - nameAddress <=
                        static_cast<ByteSize>(
                            sizeof(IMAGE_IMPORT_BY_NAME().Hint)))
                {
                    log_.warning(tr(
                        "Imported function name record is truncated."));
                    continue;
                }
                auto name = reader.readAsciizString(
                    nameAddress + sizeof(IMAGE_IMPORT_BY_NAME().Hint),
                    1024);

                if (name.isEmpty()) {
                    log_.warning(tr("Cannot read the name of an imported function."));
                    continue;
                }

                log_.debug(tr("Found an import by name: %1").arg(name));

                image_->addRelocation(std::make_unique<core::image::Relocation>(
                    importEntryAddress,
                    image_->addSymbol(std::make_unique<core::image::Symbol>(core::image::SymbolType::FUNCTION,
                                                                            std::move(name), boost::none,
                                                                            nullptr, dllName,
                                                                            core::image::ExternalNameOrigin::OBJECT_FILE)),
                    entrySize));
            }
        }

        if (!foundTerminator) {
            log_.warning(tr("Import lookup table is not null-terminated within its section."));
        }
    }

    void parseExports() {
        const auto &dataDirectory =
            optionalHeader_.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXPORT];
        if (dataDirectory.VirtualAddress == 0) {
            return;
        }

        ByteAddr directoryAddress = 0;
        if (dataDirectory.Size < sizeof(IMAGE_EXPORT_DIRECTORY) ||
            !getImageRange(dataDirectory.VirtualAddress, true,
                           sizeof(IMAGE_EXPORT_DIRECTORY), directoryAddress))
        {
            log_.warning(tr("Image export directory is truncated."));
            return;
        }

        const uint64_t forwarderRangeEnd =
            uint64_t(dataDirectory.VirtualAddress) + dataDirectory.Size;
        if (forwarderRangeEnd > uint64_t(1) << 32) {
            log_.warning(tr("Image export directory RVA range overflows."));
            return;
        }

        IMAGE_EXPORT_DIRECTORY directory = {};
        if (image_->readBytes(
                directoryAddress, reinterpret_cast<char *>(&directory),
                sizeof(directory)) != sizeof(directory))
        {
            log_.warning(tr("Cannot read the image export directory."));
            return;
        }

        peByteOrder.convertFrom(directory.Characteristics);
        peByteOrder.convertFrom(directory.Name);
        peByteOrder.convertFrom(directory.Base);
        peByteOrder.convertFrom(directory.NumberOfFunctions);
        peByteOrder.convertFrom(directory.NumberOfNames);
        peByteOrder.convertFrom(directory.AddressOfFunctions);
        peByteOrder.convertFrom(directory.AddressOfNames);
        peByteOrder.convertFrom(directory.AddressOfNameOrdinal);

        static const uint32_t MaximumExportCount = 1048576;
        if (directory.NumberOfFunctions > MaximumExportCount ||
            directory.NumberOfNames > MaximumExportCount)
        {
            log_.warning(tr("Image export directory has invalid table sizes."));
            return;
        }
        if (directory.NumberOfNames == 0) {
            return;
        }

        ByteAddr functionTableAddress = 0;
        ByteAddr nameTableAddress = 0;
        ByteAddr ordinalTableAddress = 0;
        if (!getImageRange(
                directory.AddressOfFunctions, true,
                uint64_t(directory.NumberOfFunctions) * sizeof(DWORD),
                functionTableAddress) ||
            !getImageRange(
                directory.AddressOfNames, true,
                uint64_t(directory.NumberOfNames) * sizeof(DWORD),
                nameTableAddress) ||
            !getImageRange(
                directory.AddressOfNameOrdinal, true,
                uint64_t(directory.NumberOfNames) * sizeof(WORD),
                ordinalTableAddress))
        {
            log_.warning(tr("Image export table is outside of the image sections."));
            return;
        }

        core::image::Reader reader(image_);
        for (uint32_t i = 0; i < directory.NumberOfNames; ++i) {
            WORD ordinal = 0;
            DWORD nameRVA = 0;
            if (image_->readBytes(
                    nameTableAddress + uint64_t(i) * sizeof(nameRVA),
                    reinterpret_cast<char *>(&nameRVA),
                    sizeof(nameRVA)) != sizeof(nameRVA))
            {
                log_.warning(tr("Cannot read the address value of the export directory item number %1.").arg(i));
                return;
            }
            if (image_->readBytes(
                    ordinalTableAddress + uint64_t(i) * sizeof(ordinal),
                    reinterpret_cast<char *>(&ordinal),
                    sizeof(ordinal)) != sizeof(ordinal))
            {
                log_.warning(tr("Cannot read the ordinal value of the export directory item number %1.").arg(i));
                return;
            }
            peByteOrder.convertFrom(nameRVA);
            peByteOrder.convertFrom(ordinal);

            if (ordinal >= directory.NumberOfFunctions) {
                log_.warning(tr(
                    "Image export directory item number %1 has an invalid ordinal index.").arg(i));
                continue;
            }

            DWORD entry = 0;
            if (image_->readBytes(
                    functionTableAddress + uint64_t(ordinal) * sizeof(entry),
                    reinterpret_cast<char *>(&entry),
                    sizeof(entry)) != sizeof(entry))
            {
                log_.warning(
                    tr("Cannot read the function address value of the export directory item number %1.").arg(i));
                return;
            }

            peByteOrder.convertFrom(entry);

            if (entry >= dataDirectory.VirtualAddress &&
                uint64_t(entry) < forwarderRangeEnd)
            {
                /* An export address inside the export directory is a
                 * forwarder string, not executable code in this image. */
                continue;
            }

            ByteAddr nameAddress = 0;
            ByteAddr entryAddress = 0;
            if (!getImageAddress(nameRVA, true, nameAddress) ||
                !getImageAddress(entry, true, entryAddress))
            {
                log_.warning(tr(
                    "Image export directory item number %1 has an invalid RVA.").arg(i));
                continue;
            }
            QString name = reader.readAsciizString(nameAddress, 1024);
            if (name.isEmpty()) {
                log_.warning(tr(
                    "Cannot read the name of export directory item number %1.").arg(i));
                continue;
            }
            image_->addSymbol(std::make_unique<core::image::Symbol>(
                core::image::SymbolType::FUNCTION, std::move(name),
                entryAddress));
        }
    }

    void parseBaseRelocs() {
        const auto &directory =
            optionalHeader_.DataDirectory[IMAGE_DIRECTORY_ENTRY_BASERELOC];
        if (directory.VirtualAddress == 0) {
            return;
        }

        ByteAddr headerAddress = 0;
        if (directory.Size < sizeof(IMAGE_BASE_RELOC_BLOCK_HEADER) ||
            !getLinearAddress(
                directory.VirtualAddress, true, headerAddress))
        {
            log_.warning(tr("Image base relocation directory is truncated."));
            return;
        }
        const core::image::Section *directorySection =
            getStoredSectionContainingAddress(headerAddress);
        if (!directorySection ||
            directory.Size > static_cast<uint64_t>(
                directorySection->endAddr() - headerAddress))
        {
            log_.warning(tr("Image base relocation directory is truncated."));
            return;
        }
        const ByteAddr end = headerAddress + directory.Size;

        const core::image::Symbol *baseSymbol = image_->addSymbol(std::make_unique<core::image::Symbol>(
            core::image::SymbolType::NOTYPE, "(image base)", optionalHeader_.ImageBase));

        ByteSize remainingRelocations = 1048576;
        while (headerAddress < end) {
            if (end - headerAddress <
                    static_cast<ByteSize>(
                        sizeof(IMAGE_BASE_RELOC_BLOCK_HEADER)))
            {
                log_.warning(tr("Image base relocation header is truncated."));
                return;
            }

            IMAGE_BASE_RELOC_BLOCK_HEADER header = {};
            if (directorySection->readBytes(
                    headerAddress, reinterpret_cast<char *>(&header),
                    sizeof(header)) != sizeof(header))
            {
                log_.warning(tr("Cannot read the image base reloc header."));
                return;
            }
            peByteOrder.convertFrom(header.PageRVA);
            peByteOrder.convertFrom(header.Size);

            if (header.Size < sizeof(header) ||
                header.Size > static_cast<uint64_t>(end - headerAddress) ||
                header.Size % 4 != 0)
            {
                log_.warning(tr("Image base relocation block has an invalid size."));
                return;
            }

            const uint32_t count =
                (header.Size - sizeof(header)) / sizeof(WORD);
            if (count > static_cast<uint64_t>(remainingRelocations)) {
                log_.warning(tr("Image has too many base relocation entries."));
                return;
            }
            remainingRelocations -= count;

            for (uint32_t i = 0; i < count; ++i) {
                WORD reloc = 0;
                if (directorySection->readBytes(
                        headerAddress + sizeof(header) +
                            uint64_t(i) * sizeof(reloc),
                        reinterpret_cast<char *>(&reloc),
                        sizeof(reloc)) != sizeof(reloc))
                {
                    log_.warning(tr("Cannot read the base reloc number %1.").arg(i));
                    return;
                }
                peByteOrder.convertFrom(reloc);
                const WORD type = reloc >> 12;
                const WORD offset = reloc & 0x0fff;
                if (type == IMAGE_REL_BASED_ABSOLUTE) {
                    continue;
                }

                const uint64_t targetRva =
                    uint64_t(header.PageRVA) + offset;
                if (targetRva > (std::numeric_limits<uint32_t>::max)()) {
                    log_.warning(tr("Base relocation target RVA overflows."));
                    continue;
                }

                ByteAddr address = 0;
                ByteSize addend = 0;
                ByteSize size = 0;

                switch (type) {
                    case IMAGE_REL_BASED_HIGHLOW:
                        {
                            size = 4;
                            if (!getImageRange(
                                    targetRva, true, size, address))
                            {
                                log_.warning(tr("Base relocation target is outside of the image sections."));
                                continue;
                            }
                            DWORD currentValue = 0;
                            if (image_->readBytes(
                                    address,
                                    reinterpret_cast<char *>(&currentValue),
                                    sizeof(currentValue)) !=
                                    sizeof(currentValue))
                            {
                                log_.warning(tr("Cannot read reloc at %1.").arg(address));
                                continue;
                            }
                            peByteOrder.convertFrom(currentValue);
                            if (!getRelativeAddend(
                                    currentValue,
                                    static_cast<uint64_t>(optionalHeader_.ImageBase),
                                    addend))
                            {
                                log_.warning(tr("Base relocation addend overflows."));
                                continue;
                            }
                            break;
                        }
                    case IMAGE_REL_BASED_DIR64:
                        {
                            size = 8;
                            if (!getImageRange(
                                    targetRva, true, size, address))
                            {
                                log_.warning(tr("Base relocation target is outside of the image sections."));
                                continue;
                            }
                            uint64_t currentValue = 0;
                            if (image_->readBytes(
                                    address,
                                    reinterpret_cast<char *>(&currentValue),
                                    sizeof(currentValue)) !=
                                    sizeof(currentValue))
                            {
                                log_.warning(tr("Cannot read reloc at %1.").arg(address));
                                continue;
                            }
                            peByteOrder.convertFrom(currentValue);
                            if (!getRelativeAddend(
                                    currentValue,
                                    static_cast<uint64_t>(optionalHeader_.ImageBase),
                                    addend))
                            {
                                log_.warning(tr("Base relocation addend overflows."));
                                continue;
                            }
                            break;
                        }
                    default:
                        log_.warning(tr("Unknown base reloc type %1.").arg(type));
                        continue;
                }

                image_->addRelocation(std::make_unique<core::image::Relocation>(address, baseSymbol, size, addend));
            }
            headerAddress += header.Size;
        }
    }
};

} // anonymous namespace

PeParser::PeParser():
    core::input::Parser(QLatin1String("PE"))
{}

bool PeParser::doCanParse(QIODevice *source) const {
    return seekFileHeader(source);
}

void PeParser::doParse(QIODevice *source, core::image::Image *image, const LogToken &log) const {
    if (!seekFileHeader(source)) {
        throw ParseError(tr("PE signature doesn't match."));
    }

    IMAGE_FILE_HEADER fileHeader;
    if (!read(source, fileHeader)) {
        throw ParseError(tr("Cannot read the file header."));
    }

    peByteOrder.convertFrom(fileHeader.Machine);
    switch (fileHeader.Machine) {
        case IMAGE_FILE_MACHINE_I386:
            image->platform().setArchitecture(QLatin1String("i386"));
            break;
        case IMAGE_FILE_MACHINE_AMD64:
            image->platform().setArchitecture(QLatin1String("x86-64"));
            break;
        case IMAGE_FILE_MACHINE_ARM: /* FALLTHROUGH */
        case IMAGE_FILE_MACHINE_THUMB:
            image->platform().setArchitecture(QLatin1String("arm-le"));
            break;
        default:
            throw ParseError(tr("Unknown machine id: 0x%1.").arg(fileHeader.Machine, 0, 16));
    }

    /* Just a guess. */
    image->platform().setOperatingSystem(core::image::Platform::Windows);

    WORD optionalHeaderMagic;
    if (!read(source, optionalHeaderMagic)) {
        throw ParseError(tr("Cannot read magic of the optional header."));
    }

    peByteOrder.convertFrom(optionalHeaderMagic);
    switch (optionalHeaderMagic) {
        case IMAGE_NT_OPTIONAL_HDR32_MAGIC:
            log.debug(tr("Parsing as a PE32 file."));
            PeParserImpl<IMAGE_OPTIONAL_HEADER32, IMPORT_LOOKUP_TABLE_ENTRY32>(source, image, log, fileHeader).parse();
            break;
        case IMAGE_NT_OPTIONAL_HDR64_MAGIC:
            log.debug(("Parsing as a PE32+ file."));
            PeParserImpl<IMAGE_OPTIONAL_HEADER64, IMPORT_LOOKUP_TABLE_ENTRY64>(source, image, log, fileHeader).parse();
            break;
        default:
            throw ParseError(tr("Unknown optional header magic: 0x%1").arg(optionalHeaderMagic, 0, 16));
    }
}

} // namespace pe
} // namespace input
} // namespace nc

/* vim:set et sts=4 sw=4: */
