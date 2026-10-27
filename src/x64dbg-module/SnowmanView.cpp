#include <nc/config.h>
#include <nc/common/Branding.h>
#include <nc/common/CheckedAddress.h>
#include <nc/common/make_unique.h>
#include <nc/common/Types.h>
#include <nc/core/image/ByteSource.h>
#include <nc/core/Context.h>
#include <nc/core/arch/Instruction.h>
#include <nc/core/arch/Architecture.h>
#include <nc/core/image/Image.h>
#include <nc/core/mangling/DefaultDemangler.h>
#include <nc/core/image/Section.h>
#include <nc/core/image/Relocation.h>
#include <nc/core/ir/calling/DeclarativeSymbolPrototypeProvider.h>
#include <nc/gui/MainWindow.h>
#include <nc/gui/Project.h>
#include <nc/gui/InstructionsView.h>
#include <nc/gui/CxxView.h>

#include "SnowmanView.h"
#include "pluginmain.h"
#include <QVBoxLayout>
#include <QPlainTextEdit>
#include <QTreeView>
#include <QApplication>
#include <QDir>
#include <QFile>
#include <QFileInfo>
#include <algorithm>
#include <climits>
#include <cstdint>
#include <exception>
#include <limits>
#include <memory>
#include <string>
#include <vector>
#include <_scriptapi_module.h>
#include <_scriptapi_memory.h>
#include <_scriptapi_function.h>
#include <_scriptapi_symbol.h>

using namespace Script;

namespace
{

const qint64 maximumPrototypeDatabaseSize =
    static_cast<qint64>(32) * 1024 * 1024;

QString wideEnvironmentVariable(const wchar_t *name)
{
    /* qgetenv()/QFile::decodeName uses the process ANSI code page on
     * Windows. Read the override with the wide API so paths outside that
     * code page remain lossless. */
    std::vector<wchar_t> buffer(256);
    for (;;) {
        const DWORD length = GetEnvironmentVariableW(
            name, buffer.data(), static_cast<DWORD>(buffer.size()));
        if (length == 0) {
            return QString();
        }
        if (length < buffer.size()) {
            return QString::fromWCharArray(
                buffer.data(), static_cast<int>(length));
        }
        if (length > 32767) {
            return QString();
        }
        /* On insufficient capacity the returned length includes the null
         * terminator. The next call can therefore use it directly. */
        buffer.resize(static_cast<std::size_t>(length));
    }
}

QString pluginDirectory()
{
    /* Resolve relative to this module, not x64dbg's process working
     * directory. One metadata document can contain both 32- and 64-bit
     * targets, so the same filename works beside snowman.dp32 and dp64. */
    static int moduleAnchor;
    HMODULE module = nullptr;
    if (!GetModuleHandleExW(
            GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS |
                GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
            reinterpret_cast<LPCWSTR>(&moduleAnchor), &module))
    {
        return QString();
    }

    std::vector<wchar_t> buffer(1024);
    for (;;) {
        const DWORD length = GetModuleFileNameW(
            module, buffer.data(), static_cast<DWORD>(buffer.size()));
        if (length == 0) {
            return QString();
        }
        if (length < buffer.size()) {
            return QFileInfo(QString::fromWCharArray(
                buffer.data(), static_cast<int>(length))).absolutePath();
        }
        if (buffer.size() >= 32768) {
            return QString();
        }
        buffer.resize(std::min<std::size_t>(
            buffer.size() * 2, static_cast<std::size_t>(32768)));
    }
}

std::shared_ptr<const
    nc::core::ir::calling::DeclarativeSymbolPrototypeProvider>
loadSymbolPrototypeProviderImpl()
{
    const QString configuredPath = wideEnvironmentVariable(
        L"SNOWMAN_SYMBOL_PROTOTYPES");
    const bool explicitlyConfigured = !configuredPath.isEmpty();
    QString path;
    if (explicitlyConfigured) {
        if (!QDir::isAbsolutePath(configuredPath)) {
            const QByteArray printablePath = QDir::toNativeSeparators(
                configuredPath).toUtf8();
            _plugin_logprintf(
                "[Snowman] SNOWMAN_SYMBOL_PROTOTYPES must be an absolute "
                "path; refusing relative metadata path: %s\n",
                printablePath.constData());
            return std::shared_ptr<const
                nc::core::ir::calling::DeclarativeSymbolPrototypeProvider>();
        }
        path = configuredPath;
    } else {
        const QString directory = pluginDirectory();
        if (!directory.isEmpty()) {
            path = QDir(directory).filePath(
                QLatin1String("snowman-symbol-prototypes.json"));
        }
    }

    if (path.isEmpty()) {
        _plugin_logprintf(
            "[Snowman] Cannot locate the plugin directory; set "
            "SNOWMAN_SYMBOL_PROTOTYPES to an absolute metadata path.\n");
        return std::shared_ptr<const
            nc::core::ir::calling::DeclarativeSymbolPrototypeProvider>();
    }

    QFile file(path);
    if (!file.exists()) {
        const QByteArray printablePath = QDir::toNativeSeparators(
            path).toUtf8();
        if (explicitlyConfigured) {
            _plugin_logprintf(
                "[Snowman] Symbol prototype database does not exist: %s\n",
                printablePath.constData());
        } else {
            _plugin_logprintf(
                "[Snowman] No symbol prototype database found at %s; "
                "external ABI contracts will remain conservative.\n",
                printablePath.constData());
        }
        return std::shared_ptr<const
            nc::core::ir::calling::DeclarativeSymbolPrototypeProvider>();
    }
    if (!file.open(QIODevice::ReadOnly)) {
        const QByteArray printablePath = QDir::toNativeSeparators(
            path).toUtf8();
        const QByteArray printableError = file.errorString().toUtf8();
        _plugin_logprintf(
            "[Snowman] Cannot read symbol prototype database %s: %s\n",
            printablePath.constData(), printableError.constData());
        return std::shared_ptr<const
            nc::core::ir::calling::DeclarativeSymbolPrototypeProvider>();
    }
    const qint64 expectedSize = file.size();
    if (expectedSize < 0 ||
        expectedSize > maximumPrototypeDatabaseSize) {
        const QByteArray printablePath = QDir::toNativeSeparators(
            path).toUtf8();
        _plugin_logprintf(
            "[Snowman] Symbol prototype database exceeds the 32 MiB "
            "safety limit: %s\n", printablePath.constData());
        return std::shared_ptr<const
            nc::core::ir::calling::DeclarativeSymbolPrototypeProvider>();
    }

    QByteArray contents = file.read(
        maximumPrototypeDatabaseSize + 1);
    if (contents.size() > maximumPrototypeDatabaseSize || !file.atEnd()) {
        const QByteArray printablePath = QDir::toNativeSeparators(
            path).toUtf8();
        _plugin_logprintf(
            "[Snowman] Symbol prototype database grew beyond the 32 MiB "
            "safety limit while reading: %s\n", printablePath.constData());
        return std::shared_ptr<const
            nc::core::ir::calling::DeclarativeSymbolPrototypeProvider>();
    }
    if (contents.size() != expectedSize) {
        const QByteArray printablePath = QDir::toNativeSeparators(
            path).toUtf8();
        _plugin_logprintf(
            "[Snowman] Short read while loading symbol prototype database: "
            "%s\n", printablePath.constData());
        return std::shared_ptr<const
            nc::core::ir::calling::DeclarativeSymbolPrototypeProvider>();
    }

    /* Keep one raw input representation during parsing. The declarative
     * parser builds typed node storage, so retaining QByteArray as well would
     * cause an avoidable peak-memory penalty in x32dbg. */
    const std::string json(
        contents.constData(), static_cast<std::size_t>(contents.size()));
    contents.clear();
    contents.squeeze();

    QString error;
    const auto provider = nc::core::ir::calling::
        DeclarativeSymbolPrototypeProvider::fromJson(json, &error);
    if (!provider) {
        const QByteArray printablePath = QDir::toNativeSeparators(
            path).toUtf8();
        const QByteArray printableError = error.toUtf8();
        _plugin_logprintf(
            "[Snowman] Rejected symbol prototype database %s: %s\n",
            printablePath.constData(), printableError.constData());
        return provider;
    }

    const QByteArray printablePath = QDir::toNativeSeparators(path).toUtf8();
    const QByteArray printableId = provider->id().toUtf8();
    const nc::SmallBitSize targetBitness =
        static_cast<nc::SmallBitSize>(sizeof(void *) * CHAR_BIT);
    const nc::core::ir::calling::SymbolPrototypeTarget target(
        QLatin1String("x86"), QLatin1String("windows"), targetBitness);
    const std::size_t matchingRecords = provider->prototypeCount(target);
    if (matchingRecords == 0) {
        _plugin_logprintf(
            "[Snowman] Symbol prototype provider '%s' from %s has no "
            "records for x86/windows/%u; external ABI contracts will "
            "remain conservative in this module.\n",
            printableId.constData(), printablePath.constData(),
            static_cast<unsigned int>(targetBitness));
        return provider;
    }
    _plugin_logprintf(
        "[Snowman] Loaded symbol prototype provider '%s' from %s with %u "
        "records for x86/windows/%u.\n",
        printableId.constData(), printablePath.constData(),
        static_cast<unsigned int>(matchingRecords),
        static_cast<unsigned int>(targetBitness));
    return provider;
}

std::shared_ptr<const
    nc::core::ir::calling::DeclarativeSymbolPrototypeProvider>
loadSymbolPrototypeProvider()
{
    try {
        return loadSymbolPrototypeProviderImpl();
    } catch (const std::exception &exception) {
        _plugin_logprintf(
            "[Snowman] Cannot load the symbol prototype database: %s\n",
            exception.what());
    } catch (...) {
        _plugin_logprintf(
            "[Snowman] Cannot load the symbol prototype database: "
            "unknown failure.\n");
    }
    return std::shared_ptr<const
        nc::core::ir::calling::DeclarativeSymbolPrototypeProvider>();
}

std::shared_ptr<const
    nc::core::ir::calling::DeclarativeSymbolPrototypeProvider>
symbolPrototypeProvider()
{
    /* Parsing a full SDK catalog is intentionally process-wide and immutable.
     * The provider itself is target-aware and safe to share across Projects. */
    static const auto provider = loadSymbolPrototypeProvider();
    return provider;
}

/*
 * Minimal PE structures used while parsing a module which is already mapped
 * into the debuggee. Using fixed-width fields here avoids depending on the
 * Windows SDK's PE structure declarations and their packing.
 */
struct PeImportDescriptor
{
    std::uint32_t originalFirstThunk;
    std::uint32_t timeDateStamp;
    std::uint32_t forwarderChain;
    std::uint32_t name;
    std::uint32_t firstThunk;
};

static_assert(sizeof(PeImportDescriptor) == 20, "Unexpected PE import descriptor size");

struct PeDelayImportDescriptor
{
    std::uint32_t attributes;
    std::uint32_t name;
    std::uint32_t moduleHandle;
    std::uint32_t importAddressTable;
    std::uint32_t importNameTable;
    std::uint32_t boundImportAddressTable;
    std::uint32_t unloadImportAddressTable;
    std::uint32_t timeDateStamp;
};

static_assert(sizeof(PeDelayImportDescriptor) == 32,
              "Unexpected PE delay-import descriptor size");

struct PeAmd64RuntimeFunction
{
    std::uint32_t beginAddress;
    std::uint32_t endAddress;
    std::uint32_t unwindInfoAddress;
};

static_assert(sizeof(PeAmd64RuntimeFunction) == 12,
              "Unexpected AMD64 runtime-function entry size");

struct PeSectionHeader
{
    char name[8];
    std::uint32_t virtualSize;
    std::uint32_t virtualAddress;
    std::uint32_t sizeOfRawData;
    std::uint32_t pointerToRawData;
    std::uint32_t pointerToRelocations;
    std::uint32_t pointerToLineNumbers;
    std::uint16_t numberOfRelocations;
    std::uint16_t numberOfLineNumbers;
    std::uint32_t characteristics;
};

static_assert(sizeof(PeSectionHeader) == 40, "Unexpected PE section header size");

struct PeSectionAttributes
{
    duint address;
    std::uint32_t characteristics;
};

bool isRangeInsideModule(duint offset, duint length, duint moduleSize)
{
    return offset <= moduleSize && length <= moduleSize - offset;
}

bool readModuleBytes(duint moduleBase, duint moduleSize, duint offset, void* buffer, duint size)
{
    if (!isRangeInsideModule(offset, size, moduleSize) ||
        moduleBase > (std::numeric_limits<duint>::max)() - offset)
        return false;

    duint sizeRead = 0;
    return Memory::Read(moduleBase + offset, buffer, size, &sizeRead) && sizeRead == size;
}

template<typename T>
bool readModuleValue(duint moduleBase, duint moduleSize, duint offset, T& value)
{
    return readModuleBytes(moduleBase, moduleSize, offset, &value, sizeof(value));
}

std::vector<PeSectionAttributes> readPeSectionAttributes(duint moduleBase, duint moduleSize)
{
    const duint dosNtHeaderOffset = 0x3c;
    const std::uint16_t dosSignature = 0x5a4d;       // MZ
    const std::uint32_t ntSignature = 0x00004550;    // PE\0\0
    const duint fileHeaderSize = 20;
    const duint numberOfSectionsOffsetFromNt = sizeof(std::uint32_t) + sizeof(std::uint16_t);
    const duint optionalHeaderSizeOffsetFromNt = sizeof(std::uint32_t) + 16;
    const duint optionalHeaderOffsetFromNt = sizeof(std::uint32_t) + fileHeaderSize;

    std::vector<PeSectionAttributes> result;
    std::uint16_t mz = 0;
    std::uint32_t ntOffset32 = 0;
    if (!readModuleValue(moduleBase, moduleSize, 0, mz) || mz != dosSignature ||
        !readModuleValue(moduleBase, moduleSize, dosNtHeaderOffset, ntOffset32))
        return result;

    const duint ntOffset = ntOffset32;
    std::uint32_t pe = 0;
    std::uint16_t numberOfSections = 0;
    std::uint16_t optionalHeaderSize = 0;
    if (!isRangeInsideModule(ntOffset, optionalHeaderOffsetFromNt, moduleSize) ||
        !readModuleValue(moduleBase, moduleSize, ntOffset, pe) || pe != ntSignature ||
        !readModuleValue(moduleBase, moduleSize, ntOffset + numberOfSectionsOffsetFromNt,
                         numberOfSections) ||
        !readModuleValue(moduleBase, moduleSize, ntOffset + optionalHeaderSizeOffsetFromNt,
                         optionalHeaderSize))
        return result;

    if (!isRangeInsideModule(ntOffset,
                             optionalHeaderOffsetFromNt + optionalHeaderSize, moduleSize))
        return result;
    const duint sectionTableOffset = ntOffset + optionalHeaderOffsetFromNt + optionalHeaderSize;
    const duint sectionCount = numberOfSections;
    if (sectionCount > 4096 ||
        !isRangeInsideModule(sectionTableOffset,
                             sectionCount * sizeof(PeSectionHeader), moduleSize))
        return result;

    const duint maxAddress = (std::numeric_limits<duint>::max)();
    result.reserve(static_cast<std::size_t>(sectionCount));
    for (duint index = 0; index < sectionCount; ++index)
    {
        PeSectionHeader header = {};
        if (!readModuleValue(moduleBase, moduleSize,
                             sectionTableOffset + index * sizeof(header), header))
            break;
        if (moduleBase > maxAddress - header.virtualAddress)
            continue;
        result.push_back({moduleBase + header.virtualAddress, header.characteristics});
    }
    return result;
}

bool applyPeSectionAttributes(nc::core::image::Section* section,
                              const std::vector<PeSectionAttributes>& attributes)
{
    const std::uint32_t containsCode = 0x00000020;
    const std::uint32_t containsInitializedData = 0x00000040;
    const std::uint32_t containsUninitializedData = 0x00000080;
    const std::uint32_t executable = 0x20000000;
    const std::uint32_t readable = 0x40000000;
    const std::uint32_t writable = 0x80000000;

    for (const auto& item : attributes)
    {
        if (item.address != static_cast<duint>(section->addr()))
            continue;

        /* SectionListFromAddr only reports sections mapped in the debuggee. */
        section->setAllocated(true);
        section->setReadable(item.characteristics & readable);
        section->setWritable(item.characteristics & writable);
        section->setExecutable(item.characteristics & executable);
        section->setCode(item.characteristics & containsCode);
        section->setData(item.characteristics & containsInitializedData);
        section->setBss(item.characteristics & containsUninitializedData);
        return true;
    }
    return false;
}

QString readModuleString(duint moduleBase, duint moduleSize, duint offset)
{
    if (!isRangeInsideModule(offset, 1, moduleSize) ||
        moduleBase > (std::numeric_limits<duint>::max)() - offset)
        return QString();

    char buffer[1024];
    duint bytesToRead = moduleSize - offset;
    if (bytesToRead > sizeof(buffer))
        bytesToRead = sizeof(buffer);

    duint sizeRead = 0;
    Memory::Read(moduleBase + offset, buffer, bytesToRead, &sizeRead);
    if (!sizeRead)
        return QString();

    duint length = 0;
    while (length < sizeRead && buffer[length])
        ++length;

    if (length == sizeRead)
        return QString();

    return QString::fromLatin1(buffer, static_cast<int>(length));
}

const nc::core::image::Symbol* getFunctionSymbol(nc::core::image::Image* image, std::uint64_t address)
{
    const auto symbol = image->getSymbol(address);
    if (symbol && symbol->type() == nc::core::image::SymbolType::FUNCTION && !symbol->name().isEmpty())
        return symbol;
    return nullptr;
}

int externalNameOriginRank(nc::core::image::ExternalNameOrigin origin)
{
    switch (origin)
    {
    case nc::core::image::ExternalNameOrigin::OBJECT_FILE:
        return 2;
    case nc::core::image::ExternalNameOrigin::DEBUGGER:
        return 1;
    case nc::core::image::ExternalNameOrigin::UNKNOWN:
        return 0;
    }
    return 0;
}

void addImportRelocation(nc::core::image::Image* image, duint slotAddress, duint pointerSize,
                         QString moduleName, QString name,
                         nc::core::image::ExternalNameOrigin nameOrigin,
                         const nc::core::image::Symbol* resolvedSymbol = nullptr)
{
    const auto existingRelocation = image->getRelocation(slotAddress);

    /* A PE import descriptor is stronger identity evidence than a debugger's
     * unqualified display name. Preserve the latter while attaching the DLL
     * name to a separate external symbol used by the relocation. */
    if (name.isEmpty() && existingRelocation)
    {
        name = existingRelocation->symbol()->name();
        nameOrigin = existingRelocation->symbol()->externalNameOrigin();
    }
    if (name.isEmpty())
    {
        const auto slotSymbol = getFunctionSymbol(image, slotAddress);
        if (slotSymbol)
        {
            name = slotSymbol->name();
            nameOrigin = slotSymbol->externalNameOrigin();
        }
    }
    if (name.isEmpty() && resolvedSymbol)
    {
        name = resolvedSymbol->name();
        nameOrigin = resolvedSymbol->externalNameOrigin();
    }
    if (name.isEmpty())
        return;

    if (resolvedSymbol &&
        nameOrigin != nc::core::image::ExternalNameOrigin::OBJECT_FILE &&
        name == resolvedSymbol->name())
    {
        const QString resolvedModule = resolvedSymbol->moduleName();
        if (!moduleName.isEmpty() && !resolvedModule.isEmpty() &&
            moduleName.compare(resolvedModule, Qt::CaseInsensitive) != 0)
        {
            /* The descriptor and debugger disagree about the identity behind
             * this slot.  Retain a display name, but never attach API
             * semantics to the mixed evidence. */
            nameOrigin = nc::core::image::ExternalNameOrigin::UNKNOWN;
        }
        else if (moduleName.isEmpty())
            moduleName = resolvedModule;
    }

    if (existingRelocation && !existingRelocation->symbol()->name().isEmpty())
    {
        const auto existing = existingRelocation->symbol();
        const QString existingModule = existing->moduleName();
        const bool modulesConflict = !moduleName.isEmpty() &&
            !existingModule.isEmpty() &&
            existingModule.compare(moduleName, Qt::CaseInsensitive) != 0;
        const int incomingRank = externalNameOriginRank(nameOrigin);
        const int existingRank =
            externalNameOriginRank(existing->externalNameOrigin());

        if (modulesConflict ||
            (incomingRank == existingRank && existing->name() != name))
        {
            /* Contradictory evidence for one IAT slot must not retain either
             * candidate's semantic authority. Keep a display name, but make
             * prototype lookup reject it through UNKNOWN provenance. */
            nameOrigin = nc::core::image::ExternalNameOrigin::UNKNOWN;
        }
        else if (existingRank > incomingRank)
        {
            if (existingModule.isEmpty() && !moduleName.isEmpty())
            {
                name = existing->name();
                nameOrigin = existing->externalNameOrigin();
            }
            else
                return;
        }
        else if (existingRank == incomingRank && existing->name() == name)
        {
            if (moduleName.isEmpty())
                moduleName = existingModule;
            if (moduleName == existingModule)
                return;
        }

        if (moduleName.isEmpty())
            moduleName = existingModule;
    }

    const auto symbol = image->addSymbol(std::make_unique<nc::core::image::Symbol>(
        nc::core::image::SymbolType::FUNCTION, std::move(name), boost::none,
        nullptr, std::move(moduleName), nameOrigin));
    image->addRelocation(std::make_unique<nc::core::image::Relocation>(
        slotAddress, symbol, pointerSize));
}

template<typename Thunk>
void addImportThunks(nc::core::image::Image* image, duint moduleBase, duint moduleSize,
                     const PeImportDescriptor& descriptor, duint& remainingThunkEntries)
{
    if (!descriptor.firstThunk || !remainingThunkEntries)
        return;

    const bool hasOriginalFirstThunk = descriptor.originalFirstThunk != 0;
    const duint lookupTable = hasOriginalFirstThunk ? descriptor.originalFirstThunk : descriptor.firstThunk;
    const duint addressTable = descriptor.firstThunk;
    const Thunk ordinalFlag = static_cast<Thunk>(1) << (sizeof(Thunk) * CHAR_BIT - 1);
    const Thunk ordinalMask = static_cast<Thunk>(0xffff);
    const Thunk ordinalEncodingMask = ordinalFlag | ordinalMask;
    const Thunk nameMask = ~ordinalFlag;
    const duint maxEntriesPerTable = 65536;
    const QString dllName = readModuleString(moduleBase, moduleSize, descriptor.name);

    for (duint index = 0; index < maxEntriesPerTable && remainingThunkEntries; ++index)
    {
        --remainingThunkEntries;
        const duint entryOffset = index * sizeof(Thunk);
        if (entryOffset / sizeof(Thunk) != index)
            break;
        if (!isRangeInsideModule(lookupTable, entryOffset + sizeof(Thunk), moduleSize) ||
            !isRangeInsideModule(addressTable, entryOffset + sizeof(Thunk), moduleSize))
            break;

        const duint lookupOffset = lookupTable + entryOffset;
        const duint slotOffset = addressTable + entryOffset;
        Thunk lookupValue = 0;
        if (!readModuleValue(moduleBase, moduleSize, lookupOffset, lookupValue) || !lookupValue)
            break;

        const duint slotAddress = moduleBase + slotOffset;

        Thunk resolvedAddress = 0;
        const nc::core::image::Symbol* resolvedSymbol = nullptr;
        if (readModuleValue(moduleBase, moduleSize, slotOffset, resolvedAddress))
            resolvedSymbol = getFunctionSymbol(image, resolvedAddress);

        if (!hasOriginalFirstThunk)
        {
            /* The loader normally overwrites FT when OFT is absent. */
            if (resolvedSymbol)
            {
                addImportRelocation(image, slotAddress, sizeof(Thunk), dllName,
                                    QString(),
                                    nc::core::image::ExternalNameOrigin::UNKNOWN,
                                    resolvedSymbol);
                continue;
            }

            /* Accept only a valid ordinal encoding or a module-bounded name RVA. */
            QString name;
            auto nameOrigin = nc::core::image::ExternalNameOrigin::UNKNOWN;
            if ((lookupValue & ordinalFlag) && !(lookupValue & ~ordinalEncodingMask))
            {
                const auto ordinal = static_cast<qulonglong>(lookupValue & ordinalMask);
                if (!dllName.isEmpty())
                    name = QString("%1:%2").arg(dllName).arg(ordinal);
                else
                    name = QString("ordinal_%1").arg(ordinal);
            }
            else if (!(lookupValue & ordinalFlag))
            {
                const auto nameRva = static_cast<duint>(lookupValue & nameMask);
                if (isRangeInsideModule(nameRva, sizeof(std::uint16_t) + 1, moduleSize))
                {
                    name = readModuleString(moduleBase, moduleSize, nameRva + sizeof(std::uint16_t));
                    if (!name.isEmpty())
                        nameOrigin = nc::core::image::ExternalNameOrigin::OBJECT_FILE;
                }
            }
            addImportRelocation(image, slotAddress, sizeof(Thunk), dllName,
                                std::move(name), nameOrigin);
            continue;
        }

        QString name;
        auto nameOrigin = nc::core::image::ExternalNameOrigin::UNKNOWN;
        if (lookupValue & ordinalFlag)
        {
            const auto ordinal = static_cast<qulonglong>(lookupValue & ordinalMask);
            if (resolvedSymbol)
            {
                name = resolvedSymbol->name();
                nameOrigin = resolvedSymbol->externalNameOrigin();
            }
            else if (!dllName.isEmpty())
                name = QString("%1:%2").arg(dllName).arg(ordinal);
            else
                name = QString("ordinal_%1").arg(ordinal);
        }
        else
        {
            const auto nameRva = static_cast<duint>(lookupValue & nameMask);
            if (isRangeInsideModule(nameRva, sizeof(std::uint16_t) + 1, moduleSize))
            {
                name = readModuleString(moduleBase, moduleSize, nameRva + sizeof(std::uint16_t));
                if (!name.isEmpty())
                    nameOrigin = nc::core::image::ExternalNameOrigin::OBJECT_FILE;
            }
            if (name.isEmpty() && resolvedSymbol)
            {
                name = resolvedSymbol->name();
                nameOrigin = resolvedSymbol->externalNameOrigin();
            }
        }

        addImportRelocation(image, slotAddress, sizeof(Thunk), dllName,
                            std::move(name), nameOrigin, resolvedSymbol);
    }
}

void addStandardImportDirectoryRelocations(
    nc::core::image::Image* image, duint moduleBase, duint moduleSize,
    duint importRva, duint importSize, bool is64Bit,
    duint& remainingThunkEntries)
{
    if (!isRangeInsideModule(
            importRva, sizeof(PeImportDescriptor), moduleSize))
        return;

    /* Invalid or absent sizes occur in packed images; then use guarded
     * null-termination within the mapped module. */
    const duint descriptorsInModule =
        (moduleSize - importRva) / sizeof(PeImportDescriptor);
    duint descriptorCount = 0;
    if (importSize >= sizeof(PeImportDescriptor) &&
        isRangeInsideModule(importRva, importSize, moduleSize))
        descriptorCount = importSize / sizeof(PeImportDescriptor);
    else
        descriptorCount = descriptorsInModule;
    if (descriptorCount > 4096)
        descriptorCount = 4096;

    for (duint index = 0;
         index < descriptorCount && remainingThunkEntries; ++index)
    {
        PeImportDescriptor descriptor = {};
        const duint descriptorOffset =
            importRva + index * sizeof(PeImportDescriptor);
        if (!readModuleValue(
                moduleBase, moduleSize, descriptorOffset, descriptor))
            break;
        if (!descriptor.originalFirstThunk && !descriptor.timeDateStamp &&
            !descriptor.forwarderChain && !descriptor.name &&
            !descriptor.firstThunk)
            break;

        if (is64Bit)
            addImportThunks<std::uint64_t>(
                image, moduleBase, moduleSize, descriptor,
                remainingThunkEntries);
        else
            addImportThunks<std::uint32_t>(
                image, moduleBase, moduleSize, descriptor,
                remainingThunkEntries);
    }
}

bool delayImportFieldToRva(std::uint32_t field, bool fieldsAreRvas,
                           duint moduleBase, duint moduleSize,
                           std::uint32_t& result)
{
    if (!field)
    {
        result = 0;
        return true;
    }

    duint rva = field;
    if (!fieldsAreRvas)
    {
        /* The legacy form stores 32-bit preferred virtual addresses.  Do
         * not truncate a 64-bit image base in order to make them fit. */
        if (static_cast<duint>(field) < moduleBase)
            return false;
        rva = static_cast<duint>(field) - moduleBase;
    }
    if (rva >= moduleSize ||
        rva > (std::numeric_limits<std::uint32_t>::max)())
        return false;

    result = static_cast<std::uint32_t>(rva);
    return true;
}

void addDelayImportDirectoryRelocations(
    nc::core::image::Image* image, duint moduleBase, duint moduleSize,
    duint delayRva, duint delaySize, bool is64Bit,
    duint& remainingThunkEntries)
{
    if (!isRangeInsideModule(
            delayRva, sizeof(PeDelayImportDescriptor), moduleSize))
        return;

    const duint descriptorsInModule =
        (moduleSize - delayRva) / sizeof(PeDelayImportDescriptor);
    duint descriptorCount = 0;
    if (delaySize >= sizeof(PeDelayImportDescriptor) &&
        isRangeInsideModule(delayRva, delaySize, moduleSize))
        descriptorCount = delaySize / sizeof(PeDelayImportDescriptor);
    else
        descriptorCount = descriptorsInModule;
    if (descriptorCount > 4096)
        descriptorCount = 4096;

    for (duint index = 0;
         index < descriptorCount && remainingThunkEntries; ++index)
    {
        PeDelayImportDescriptor delay = {};
        const duint descriptorOffset =
            delayRva + index * sizeof(PeDelayImportDescriptor);
        if (!readModuleValue(
                moduleBase, moduleSize, descriptorOffset, delay))
            break;
        if (!delay.attributes && !delay.name && !delay.moduleHandle &&
            !delay.importAddressTable && !delay.importNameTable &&
            !delay.boundImportAddressTable &&
            !delay.unloadImportAddressTable && !delay.timeDateStamp)
            break;

        /* Version one defines only the RVA flag. Unknown attribute bits can
         * change the interpretation of every pointer, so fail closed. */
        if (delay.attributes & ~std::uint32_t(1))
            continue;
        const bool fieldsAreRvas = (delay.attributes & 1) != 0;

        PeImportDescriptor descriptor = {};
        if (!delayImportFieldToRva(
                delay.name, fieldsAreRvas, moduleBase, moduleSize,
                descriptor.name) ||
            !delayImportFieldToRva(
                delay.importAddressTable, fieldsAreRvas,
                moduleBase, moduleSize, descriptor.firstThunk) ||
            !delayImportFieldToRva(
                delay.importNameTable, fieldsAreRvas,
                moduleBase, moduleSize, descriptor.originalFirstThunk))
            continue;
        if (!descriptor.name || !descriptor.firstThunk)
            continue;

        if (is64Bit)
            addImportThunks<std::uint64_t>(
                image, moduleBase, moduleSize, descriptor,
                remainingThunkEntries);
        else
            addImportThunks<std::uint32_t>(
                image, moduleBase, moduleSize, descriptor,
                remainingThunkEntries);
    }
}

void addAmd64RuntimeFunctionEntries(
    nc::core::image::Image* image, duint moduleBase, duint moduleSize,
    duint directoryRva, duint directorySize)
{
    if (!directoryRva ||
        directorySize < sizeof(PeAmd64RuntimeFunction) ||
        !isRangeInsideModule(directoryRva, directorySize, moduleSize))
        return;

    duint count = directorySize / sizeof(PeAmd64RuntimeFunction);
    if (count > 1048576)
        count = 1048576;
    const duint maxAddress = (std::numeric_limits<duint>::max)();

    for (duint index = 0; index < count; ++index)
    {
        PeAmd64RuntimeFunction entry = {};
        const duint offset =
            directoryRva + index * sizeof(PeAmd64RuntimeFunction);
        if (!readModuleValue(
                moduleBase, moduleSize, offset, entry))
            break;
        if (entry.beginAddress >= entry.endAddress ||
            !entry.unwindInfoAddress ||
            entry.unwindInfoAddress % 4 != 0 ||
            !isRangeInsideModule(
                entry.beginAddress,
                static_cast<duint>(entry.endAddress) - entry.beginAddress,
                moduleSize) ||
            !isRangeInsideModule(
                entry.unwindInfoAddress, 1, moduleSize) ||
            moduleBase > maxAddress - entry.beginAddress ||
            moduleBase > maxAddress - (entry.endAddress - 1))
            continue;

        const duint begin = moduleBase + entry.beginAddress;
        const duint last = moduleBase + entry.endAddress - 1;
        if (begin > static_cast<duint>(
                (std::numeric_limits<nc::ByteAddr>::max)()) ||
            last > static_cast<duint>(
                (std::numeric_limits<nc::ByteAddr>::max)()))
            continue;
        const auto beginSection = image->getSectionContainingAddress(begin);
        const auto endSection = image->getSectionContainingAddress(last);
        if (!beginSection || !endSection ||
            !beginSection->isExecutable() || !endSection->isExecutable())
            continue;

        image->addFunctionEntry(static_cast<nc::ByteAddr>(begin));
    }
}

void addPeImportRelocations(nc::core::image::Image* image, duint moduleBase, duint moduleSize)
{
    /* PE/COFF offsets and magic values, all relative to the mapped image. */
    const duint dosNtHeaderOffset = 0x3c;
    const std::uint16_t dosSignature = 0x5a4d;       // MZ
    const std::uint32_t ntSignature = 0x00004550;    // PE\0\0
    const std::uint16_t pe32Magic = 0x10b;
    const std::uint16_t pe32PlusMagic = 0x20b;
    const duint fileHeaderSize = 20;
    const duint optionalHeaderOffsetFromNt = sizeof(std::uint32_t) + fileHeaderSize;
    const duint optionalHeaderSizeFieldFromNt = sizeof(std::uint32_t) + 16;

    std::uint16_t mz = 0;
    std::uint32_t ntOffset32 = 0;
    if (!readModuleValue(moduleBase, moduleSize, 0, mz) || mz != dosSignature ||
        !readModuleValue(moduleBase, moduleSize, dosNtHeaderOffset, ntOffset32))
        return;

    const duint ntOffset = ntOffset32;
    std::uint32_t pe = 0;
    std::uint16_t optionalHeaderSize = 0;
    std::uint16_t optionalMagic = 0;
    if (!isRangeInsideModule(ntOffset, optionalHeaderOffsetFromNt + sizeof(optionalMagic), moduleSize) ||
        !readModuleValue(moduleBase, moduleSize, ntOffset, pe) || pe != ntSignature ||
        !readModuleValue(moduleBase, moduleSize, ntOffset + optionalHeaderSizeFieldFromNt, optionalHeaderSize) ||
        !readModuleValue(moduleBase, moduleSize, ntOffset + optionalHeaderOffsetFromNt, optionalMagic))
        return;

    duint numberOfDirectoriesOffset = 0;
    duint dataDirectoriesOffset = 0;
    if (optionalMagic == pe32Magic)
    {
        numberOfDirectoriesOffset = 92;
        dataDirectoriesOffset = 96;
    }
    else if (optionalMagic == pe32PlusMagic)
    {
        numberOfDirectoriesOffset = 108;
        dataDirectoriesOffset = 112;
    }
    else
        return;

    /* Read both the ordinary import directory (entry 1) and the delay-import
     * directory (entry 13). They produce the same relocation provenance for
     * the core analyzer; only their descriptor encodings differ. */
    const duint importDirectoryOffset = dataDirectoriesOffset + 8;
    const duint exceptionDirectoryOffset = dataDirectoriesOffset + 3 * 8;
    const duint delayImportDirectoryOffset = dataDirectoriesOffset + 13 * 8;

    const duint optionalHeaderOffset = ntOffset + optionalHeaderOffsetFromNt;
    if (!isRangeInsideModule(optionalHeaderOffset, optionalHeaderSize, moduleSize))
        return;
    if (optionalHeaderSize <
        numberOfDirectoriesOffset + sizeof(std::uint32_t))
        return;

    std::uint32_t numberOfDirectories = 0;
    if (!readModuleValue(moduleBase, moduleSize, optionalHeaderOffset + numberOfDirectoriesOffset,
                         numberOfDirectories))
        return;

    duint remainingThunkEntries = 65536;
    const bool is64Bit = optionalMagic == pe32PlusMagic;
    if (is64Bit && numberOfDirectories > 3 &&
        optionalHeaderSize >= exceptionDirectoryOffset + 8)
    {
        std::uint32_t exceptionRva = 0;
        std::uint32_t exceptionSize = 0;
        if (readModuleValue(
                moduleBase, moduleSize,
                optionalHeaderOffset + exceptionDirectoryOffset,
                exceptionRva) &&
            readModuleValue(
                moduleBase, moduleSize,
                optionalHeaderOffset + exceptionDirectoryOffset +
                    sizeof(exceptionRva), exceptionSize))
            addAmd64RuntimeFunctionEntries(
                image, moduleBase, moduleSize,
                exceptionRva, exceptionSize);
    }

    if (numberOfDirectories > 1 &&
        optionalHeaderSize >= importDirectoryOffset + 8)
    {
        std::uint32_t importRva = 0;
        std::uint32_t importSize = 0;
        if (readModuleValue(
                moduleBase, moduleSize,
                optionalHeaderOffset + importDirectoryOffset,
                importRva) &&
            readModuleValue(
                moduleBase, moduleSize,
                optionalHeaderOffset + importDirectoryOffset +
                    sizeof(importRva), importSize) && importRva)
            addStandardImportDirectoryRelocations(
                image, moduleBase, moduleSize, importRva, importSize,
                is64Bit, remainingThunkEntries);
    }

    if (remainingThunkEntries && numberOfDirectories > 13 &&
        optionalHeaderSize >= delayImportDirectoryOffset + 8)
    {
        std::uint32_t delayRva = 0;
        std::uint32_t delaySize = 0;
        if (readModuleValue(
                moduleBase, moduleSize,
                optionalHeaderOffset + delayImportDirectoryOffset,
                delayRva) &&
            readModuleValue(
                moduleBase, moduleSize,
                optionalHeaderOffset + delayImportDirectoryOffset +
                    sizeof(delayRva), delaySize) && delayRva)
            addDelayImportDirectoryRelocations(
                image, moduleBase, moduleSize, delayRva, delaySize,
                is64Bit, remainingThunkEntries);
    }
}

/* FunctionInfo changed from an absolute start VA to module + RVA in newer SDKs. */
template<typename FunctionInfo>
auto getX64DbgFunctionAddress(const FunctionInfo& function, duint& address, int)
    -> decltype(Module::BaseFromName(function.mod),
                static_cast<duint>(function.rvaStart), bool())
{
    const duint functionModuleBase = Module::BaseFromName(function.mod);
    const duint rva = static_cast<duint>(function.rvaStart);
    const duint maxAddress = (std::numeric_limits<duint>::max)();
    if (!functionModuleBase || rva > maxAddress - functionModuleBase)
        return false;

    address = functionModuleBase + rva;
    return true;
}

template<typename FunctionInfo>
auto getX64DbgFunctionAddress(const FunctionInfo& function, duint& address, long)
    -> decltype(static_cast<duint>(function.start), bool())
{
    address = static_cast<duint>(function.start);
    return true;
}

void addX64DbgFunctionSymbols(nc::core::image::Image* image, duint moduleBase,
                              duint moduleSize)
{
    nc::CheckedByteRange moduleRange = {0, 0, 0};
    if (!moduleSize ||
        !nc::checkedByteRange(
            static_cast<nc::ConstantValue>(moduleBase),
            static_cast<nc::ConstantValue>(moduleSize), moduleRange))
        return;

    BridgeList<Script::Function::FunctionInfo> functions;
    (void)Script::Function::GetList(&functions);

    for (int i = 0; i < functions.Count(); ++i)
    {
        duint address = 0;
        nc::ByteAddr checkedAddress = 0;
        if (!getX64DbgFunctionAddress(functions[i], address, 0) ||
            !nc::checkedByteAddressAdd(
                static_cast<nc::ConstantValue>(address), 0,
                checkedAddress) ||
            checkedAddress < moduleRange.begin ||
            checkedAddress >= moduleRange.end)
            continue;

        image->addFunctionEntry(checkedAddress);

        const auto existing = image->getSymbol(checkedAddress);
        if (existing && existing->type() == nc::core::image::SymbolType::FUNCTION)
            continue;

        /*
         * An empty name deliberately preserves Snowman's fun_<address>
         * fallback while still carrying the stronger FUNCTION type.
         */
        image->addSymbol(std::make_unique<nc::core::image::Symbol>(
            nc::core::image::SymbolType::FUNCTION,
            existing ? existing->name() : QString(), checkedAddress));
    }
}

} // anonymous namespace

class DbgByteSource : public nc::core::image::ByteSource
{
public:
    explicit DbgByteSource(nc::ByteAddr lowerBound, nc::ByteAddr upperBound)
        : mLowerBound(lowerBound),
        mUpperBound(upperBound)
    {
    }

    nc::ByteSize readBytes(nc::ByteAddr addr, void *buf, nc::ByteSize size) const override
    {
        if (size <= 0 || addr < mLowerBound || addr >= mUpperBound)
            return 0;

        const nc::ByteSize available = mUpperBound - addr;
        if (size > available)
            size = available;

        duint sizeRead = 0;
        Memory::Read(static_cast<duint>(addr), buf, static_cast<duint>(size), &sizeRead);
        if (sizeRead > static_cast<duint>(size))
            sizeRead = static_cast<duint>(size);
        return static_cast<nc::ByteSize>(sizeRead);
    }

private:
    nc::ByteAddr mLowerBound;
    nc::ByteAddr mUpperBound;
};

static std::unique_ptr<nc::gui::Project> MakeProject(duint base, duint size)
{
    using namespace Script;

    auto project = std::make_unique<nc::gui::Project>();
    auto image = project->image().get();

    if (const auto provider = symbolPrototypeProvider())
        project->addSymbolPrototypeProvider(provider);

    //set architecture
#ifdef _WIN64
    image->platform().setArchitecture(QLatin1String("x86-64"));
#else //x86
    image->platform().setArchitecture(QLatin1String("i386"));
#endif //_WIN64

    //set OS
    image->platform().setOperatingSystem(nc::core::image::Platform::Windows);

    //set demangler
    image->setDemangler(std::make_unique<nc::core::mangling::DefaultDemangler>());

    //create sections
    auto success = false;
    auto moduleBase = Module::BaseFromAddr(base);
    duint moduleSize = 0;
    nc::CheckedByteRange moduleRange = {0, 0, 0};
    bool hasCheckedModuleRange = false;
    if (moduleBase)
    {
        moduleSize = Module::SizeFromAddr(moduleBase);
        hasCheckedModuleRange = moduleSize && nc::checkedByteRange(
            static_cast<nc::ConstantValue>(moduleBase),
            static_cast<nc::ConstantValue>(moduleSize), moduleRange);
    }
    if (hasCheckedModuleRange)
    {
        const auto peSectionAttributes = readPeSectionAttributes(
            moduleBase, moduleSize);
        BridgeList<Module::ModuleSectionInfo> sections;
        if (Module::SectionListFromAddr(moduleBase, &sections))
        {
            for (auto i = 0; i < sections.Count(); i++)
            {
                nc::CheckedByteRange sectionRange = {0, 0, 0};
                if (!sections[i].size ||
                    !nc::checkedByteRange(
                        static_cast<nc::ConstantValue>(sections[i].addr),
                        static_cast<nc::ConstantValue>(sections[i].size),
                        sectionRange) ||
                    !nc::containsByteRange(moduleRange, sectionRange))
                    continue;

                auto section = std::make_unique<nc::core::image::Section>(
                    sections[i].name, sectionRange.begin, sectionRange.size);
                if (!applyPeSectionAttributes(section.get(), peSectionAttributes))
                {
                    /* Keep permissive behavior for malformed or headerless modules. */
                    section->setReadable(true);
                    section->setWritable(true);
                    section->setExecutable(true);
                    section->setCode(true);
                    section->setData(true);
                    section->setAllocated(true);
                }
                section->setExternalByteSource(
                    std::make_unique<DbgByteSource>(
                        sectionRange.begin, sectionRange.end));
                image->addSection(std::move(section));
                success = true;
            }
        }
    }

    //add a made-up section in case there was an error with the module sections.
    if (!success)
    {
        nc::CheckedByteRange fallbackRange = {0, 0, 0};
        const bool hasFallbackRange = hasCheckedModuleRange ||
            (size && nc::checkedByteRange(
                static_cast<nc::ConstantValue>(base),
                static_cast<nc::ConstantValue>(size), fallbackRange));
        if (hasFallbackRange)
        {
            if (hasCheckedModuleRange)
                fallbackRange = moduleRange;
            auto section = std::make_unique<nc::core::image::Section>(
                ".text", fallbackRange.begin, fallbackRange.size);
            section->setReadable(true);
            section->setWritable(true);
            section->setExecutable(true);
            section->setCode(true);
            section->setData(true);
            section->setAllocated(true);
            section->setExternalByteSource(
                std::make_unique<DbgByteSource>(
                    fallbackRange.begin, fallbackRange.end));
            image->addSection(std::move(section));
        }
    }

    //add symbols
    BridgeList<Symbol::SymbolInfo> symbols;
    if (Symbol::GetList(&symbols))
    {
        for (auto i = 0; i < symbols.Count(); i++)
        {
            const auto & symbol = symbols[i];
            auto modBase = Module::BaseFromName(symbol.mod);
            if (!modBase)
                continue;
            const duint ownerSize = Module::SizeFromAddr(modBase);
            nc::CheckedByteRange ownerRange = {0, 0, 0};
            nc::ByteAddr va = 0;
            if (!ownerSize ||
                !nc::checkedByteRange(
                    static_cast<nc::ConstantValue>(modBase),
                    static_cast<nc::ConstantValue>(ownerSize),
                    ownerRange) ||
                !nc::checkedByteAddressAdd(
                    static_cast<nc::ConstantValue>(modBase),
                    static_cast<nc::ConstantValue>(symbol.rva), va) ||
                va < ownerRange.begin || va >= ownerRange.end ||
                Module::BaseFromAddr(static_cast<duint>(va)) != modBase)
                continue;

            auto name = QString::fromUtf8(symbol.name);
            if(symbol.type == Symbol::Import) //IAT entry
            {
                const nc::ConstantValue pointerSize =
                    static_cast<nc::ConstantValue>(
                        image->platform().architecture()->bitness() /
                        CHAR_BIT);
                nc::CheckedByteRange pointerRange = {0, 0, 0};
                if (!name.isEmpty() && pointerSize &&
                    hasCheckedModuleRange && modBase == moduleBase &&
                    nc::checkedByteRange(
                        static_cast<nc::ConstantValue>(va), pointerSize,
                        pointerRange) &&
                    nc::containsByteRange(ownerRange, pointerRange) &&
                    nc::containsByteRange(moduleRange, pointerRange) &&
                    Module::BaseFromAddr(static_cast<duint>(
                        pointerRange.end - 1)) == modBase)
                    image->addRelocation(
                        std::make_unique<nc::core::image::Relocation>(
                            va,
                            image->addSymbol(std::make_unique<nc::core::image::Symbol>(
                                nc::core::image::SymbolType::FUNCTION, name,
                                boost::none, nullptr,
                                /* symbol.mod owns the IAT slot; it is not the
                                 * target DLL identity.  The PE descriptor or
                                 * resolved target supplies that separately. */
                                QString(),
                                nc::core::image::ExternalNameOrigin::DEBUGGER)),
                            static_cast<nc::ByteSize>(pointerSize)));
            }
            else //Function or Export
                image->addSymbol(std::make_unique<nc::core::image::Symbol>(
                    nc::core::image::SymbolType::FUNCTION, name, va, nullptr,
                    QString::fromUtf8(symbol.mod),
                    nc::core::image::ExternalNameOrigin::DEBUGGER));
        }
    }

    /* Preserve boundaries recovered by x64dbg even when no symbol exists. */
    if (hasCheckedModuleRange)
        addX64DbgFunctionSymbols(image, moduleBase, moduleSize);

    /* Fill gaps left by debugger metadata from PE imports, delay imports,
     * and AMD64 unwind-backed function boundaries. */
    if (hasCheckedModuleRange)
        addPeImportRelocations(image, moduleBase, moduleSize);

    return project;
}

void SnowmanView::decompileAt(const SnowmanRange* ranges, duint count) const
{
    if (!ranges || !count)
        return;

    nc::CheckedByteRange firstRange = {0, 0, 0};
    if (!nc::checkedInclusiveByteRange(
            static_cast<nc::ConstantValue>(ranges[0].start),
            static_cast<nc::ConstantValue>(ranges[0].end), firstRange))
        return;

    nc::gui::MainWindow* mainWindow = (nc::gui::MainWindow*)mSnowmanMainWindow;
    duint base = Module::BaseFromAddr(
        static_cast<duint>(firstRange.begin));
    duint size = Module::SizeFromAddr(base);
    if(!base || !size) //we are not inside a module
        base = DbgMemFindBaseAddr(
            static_cast<duint>(firstRange.begin), &size);

    nc::CheckedByteRange backingRange = {0, 0, 0};
    if (!size || !nc::checkedByteRange(
            static_cast<nc::ConstantValue>(base),
            static_cast<nc::ConstantValue>(size), backingRange))
        return;

    mainWindow->open(MakeProject(base, size));
    mainWindow->project()->setName("Snowman");
    for(duint i = 0; i < count; i++)
    {
        nc::CheckedByteRange range = {0, 0, 0};
        if (!nc::checkedInclusiveByteRange(
                static_cast<nc::ConstantValue>(ranges[i].start),
                static_cast<nc::ConstantValue>(ranges[i].end), range))
            continue;
        if (!nc::containsByteRange(backingRange, range))
            continue;
        mainWindow->project()->disassemble(
            mainWindow->project()->image().get(), range.begin, range.end);
    }
    mainWindow->project()->decompile();
}

SnowmanView::SnowmanView(QWidget* parent) : QWidget(parent)
{
    nc::Branding branding = nc::branding();
    branding.setApplicationName("Snowman");
    branding.setOrganizationDomain("x64dbg.com");
    branding.setOrganizationName("x64dbg");
    nc::gui::MainWindow* mainWindow = new nc::gui::MainWindow(std::move(branding), parent);
    mainWindow->setAutoFillBackground(true);
    QVBoxLayout* layout = new QVBoxLayout();
    layout->addWidget(mainWindow);
    layout->setMargin(0);
    setLayout(layout);

    mSnowmanMainWindow = mainWindow;

    //remove open/quit options
    mainWindow->openAction()->setEnabled(false);
    mainWindow->openAction()->setVisible(false);
    mainWindow->quitAction()->setEnabled(false);
    mainWindow->quitAction()->setVisible(false);

    //add command to jump from snowman to x64dbg
    mJumpFromInstructionsViewAction = new QAction(tr("Show in x64dbg"), this);
    mJumpFromInstructionsViewAction->setShortcut(Qt::CTRL + Qt::Key_Backspace);
    mJumpFromInstructionsViewAction->setShortcutContext(Qt::WidgetWithChildrenShortcut);
    connect(mJumpFromInstructionsViewAction, SIGNAL(triggered()), this, SLOT(jumpFromInstructionsView()));
    mainWindow->instructionsView()->treeView()->addAction(mJumpFromInstructionsViewAction);

    mJumpFromCxxViewAction = new QAction(tr("Show in x64dbg"), this);
    mJumpFromCxxViewAction->setShortcut(Qt::CTRL + Qt::Key_Backspace);
    mJumpFromCxxViewAction->setShortcutContext(Qt::WidgetWithChildrenShortcut);
    connect(mJumpFromCxxViewAction, SIGNAL(triggered()), this, SLOT(jumpFromCxxView()));
    mainWindow->cxxView()->textEdit()->addAction(mJumpFromCxxViewAction);

    connect(mainWindow->instructionsView(), SIGNAL(contextMenuCreated(QMenu*)), this, SLOT(populateInstructionsContextMenu(QMenu*)));
    connect(mainWindow->cxxView(), SIGNAL(contextMenuCreated(QMenu*)), this, SLOT(populateCxxContextMenu(QMenu*)));

    qApp->setStyleSheet(R"(nc--gui--CxxView QPlainTextEdit {
    color: white;
    background-color: #272822;
}

nc--gui--CxxFormatting {
  qproperty-textColor: #FFFFFF;
  qproperty-singleLineCommentColor: #57A64A;
  qproperty-multiLineLineCommentColor: #57A64A;
  qproperty-keywordColor: #569CD6;
  qproperty-operatorColor: #B4B4B4;
  qproperty-numberColor: #B5CEA8;
  qproperty-macroColor: #BD63C5;
  qproperty-stringColor: #D69D85;
  qproperty-escapeCharColor: #4EC9B3;
}
)" + qApp->styleSheet());
}

void SnowmanView::closeEvent(QCloseEvent* event)
{
    Q_UNUSED(event);
    mSnowmanMainWindow->close();
}

void SnowmanView::populateInstructionsContextMenu(QMenu* menu) const
{
    for (QAction* action : menu->actions())
    {
        if (action->shortcut() == QKeySequence(QKeySequence::FindNext))
            action->setShortcut(QKeySequence("Ctrl+F3"));
    }
    nc::gui::MainWindow* mainWindow = (nc::gui::MainWindow*)mSnowmanMainWindow;
    if (!mainWindow->instructionsView()->selectedInstructions().empty())
    {
        menu->addSeparator();
        menu->addAction(mJumpFromInstructionsViewAction);
    }
}

void SnowmanView::populateCxxContextMenu(QMenu* menu) const
{
    for (QAction* action : menu->actions())
    {
        if (action->shortcut() == QKeySequence(QKeySequence::FindNext))
            action->setShortcut(QKeySequence("Ctrl+F3"));
    }
    nc::gui::MainWindow* mainWindow = (nc::gui::MainWindow*)mSnowmanMainWindow;
    if (!mainWindow->cxxView()->selectedInstructions().empty())
    {
        menu->addSeparator();
        menu->addAction(mJumpFromCxxViewAction);
    }
}

void SnowmanView::jumpFromInstructionsView() const
{
    nc::gui::MainWindow* mainWindow = (nc::gui::MainWindow*)mSnowmanMainWindow;
    for (auto instruction : mainWindow->instructionsView()->selectedInstructions())
    {
        duint addr = instruction->addr();
        DbgCmdExecDirect(QString().sprintf("disasm \"%p\"", addr).toUtf8().constData());
        GuiShowCpu();
        break;
    }
}

void SnowmanView::jumpFromCxxView() const
{
    nc::gui::MainWindow* mainWindow = (nc::gui::MainWindow*)mSnowmanMainWindow;
    for (auto instruction : mainWindow->cxxView()->selectedInstructions())
    {
        duint addr = instruction->addr();
        DbgCmdExecDirect(QString().sprintf("disasm \"%p\"", addr).toUtf8().constData());
        GuiShowCpu();
        break;
    }
}
