#include <nc/config.h>
#include <nc/common/Branding.h>
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
#include <nc/gui/MainWindow.h>
#include <nc/gui/Project.h>
#include <nc/gui/InstructionsView.h>
#include <nc/gui/CxxView.h>

#include "SnowmanView.h"
#include <QVBoxLayout>
#include <QPlainTextEdit>
#include <QTreeView>
#include <QApplication>
#include <climits>
#include <cstdint>
#include <cstring>
#include <limits>
#include <vector>
#include <_scriptapi_module.h>
#include <_scriptapi_memory.h>
#include <_scriptapi_symbol.h>

using namespace Script;

namespace
{

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

bool isRangeInsideModule(duint offset, duint length, duint moduleSize)
{
    return offset <= moduleSize && length <= moduleSize - offset;
}

bool readModuleBytes(duint moduleBase, duint moduleSize, duint offset, void* buffer, duint size)
{
    if (!isRangeInsideModule(offset, size, moduleSize))
        return false;

    duint sizeRead = 0;
    return Memory::Read(moduleBase + offset, buffer, size, &sizeRead) && sizeRead == size;
}

template<typename T>
bool readModuleValue(duint moduleBase, duint moduleSize, duint offset, T& value)
{
    return readModuleBytes(moduleBase, moduleSize, offset, &value, sizeof(value));
}

QString readModuleString(duint moduleBase, duint moduleSize, duint offset)
{
    if (!isRangeInsideModule(offset, 1, moduleSize))
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

bool hasNameAtAddress(const nc::core::image::Image* image, duint address)
{
    const auto relocation = image->getRelocation(address);
    if (relocation && !relocation->symbol()->name().isEmpty())
        return true;

    const auto symbol = image->getSymbol(address);
    return symbol && !symbol->name().isEmpty();
}

void addImportRelocation(nc::core::image::Image* image, duint slotAddress, duint pointerSize,
                         QString name, const nc::core::image::Symbol* resolvedSymbol = nullptr)
{
    /* Keep a usable name already supplied by x64dbg. */
    if (hasNameAtAddress(image, slotAddress))
        return;

    const nc::core::image::Symbol* symbol = resolvedSymbol;
    if (!symbol)
    {
        if (name.isEmpty())
            return;
        symbol = image->addSymbol(std::make_unique<nc::core::image::Symbol>(
            nc::core::image::SymbolType::FUNCTION, std::move(name), boost::none));
    }

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
        if (hasNameAtAddress(image, slotAddress))
            continue;

        Thunk resolvedAddress = 0;
        const nc::core::image::Symbol* resolvedSymbol = nullptr;
        if (readModuleValue(moduleBase, moduleSize, slotOffset, resolvedAddress))
            resolvedSymbol = getFunctionSymbol(image, resolvedAddress);

        if (!hasOriginalFirstThunk)
        {
            /* The loader normally overwrites FT when OFT is absent. */
            if (resolvedSymbol)
            {
                addImportRelocation(image, slotAddress, sizeof(Thunk), QString(), resolvedSymbol);
                continue;
            }

            /* Accept only a valid ordinal encoding or a module-bounded name RVA. */
            QString name;
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
                    name = readModuleString(moduleBase, moduleSize, nameRva + sizeof(std::uint16_t));
            }
            addImportRelocation(image, slotAddress, sizeof(Thunk), std::move(name));
            continue;
        }

        QString name;
        if (lookupValue & ordinalFlag)
        {
            const auto ordinal = static_cast<qulonglong>(lookupValue & ordinalMask);
            if (resolvedSymbol)
                name = resolvedSymbol->name();
            else if (!dllName.isEmpty())
                name = QString("%1:%2").arg(dllName).arg(ordinal);
            else
                name = QString("ordinal_%1").arg(ordinal);
        }
        else
        {
            const auto nameRva = static_cast<duint>(lookupValue & nameMask);
            if (isRangeInsideModule(nameRva, sizeof(std::uint16_t) + 1, moduleSize))
                name = readModuleString(moduleBase, moduleSize, nameRva + sizeof(std::uint16_t));
            if (name.isEmpty() && resolvedSymbol)
                name = resolvedSymbol->name();
        }

        addImportRelocation(image, slotAddress, sizeof(Thunk), std::move(name));
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

    /* The import directory is data-directory entry 1 (8 bytes per entry). */
    const duint importDirectoryOffset = dataDirectoriesOffset + 8;
    if (optionalHeaderSize < importDirectoryOffset + 8)
        return;

    const duint optionalHeaderOffset = ntOffset + optionalHeaderOffsetFromNt;
    if (!isRangeInsideModule(optionalHeaderOffset, optionalHeaderSize, moduleSize))
        return;

    std::uint32_t numberOfDirectories = 0;
    std::uint32_t importRva32 = 0;
    std::uint32_t importSize32 = 0;
    if (!readModuleValue(moduleBase, moduleSize, optionalHeaderOffset + numberOfDirectoriesOffset,
                         numberOfDirectories) || numberOfDirectories <= 1 ||
        !readModuleValue(moduleBase, moduleSize, optionalHeaderOffset + importDirectoryOffset, importRva32) ||
        !readModuleValue(moduleBase, moduleSize,
                         optionalHeaderOffset + importDirectoryOffset + sizeof(importRva32), importSize32) ||
        !importRva32)
        return;

    const duint importRva = importRva32;
    if (!isRangeInsideModule(importRva, sizeof(PeImportDescriptor), moduleSize))
        return;

    /* Invalid or absent sizes occur in packed images; then use guarded null-termination. */
    const duint descriptorsInModule = (moduleSize - importRva) / sizeof(PeImportDescriptor);
    const duint importSize = importSize32;
    duint descriptorCount = 0;
    if (importSize >= sizeof(PeImportDescriptor) &&
        isRangeInsideModule(importRva, importSize, moduleSize))
        descriptorCount = importSize / sizeof(PeImportDescriptor);
    else
        descriptorCount = descriptorsInModule;
    if (descriptorCount > 4096)
        descriptorCount = 4096;

    duint remainingThunkEntries = 65536;
    for (duint index = 0; index < descriptorCount; ++index)
    {
        PeImportDescriptor descriptor = {};
        const duint descriptorOffset = importRva + index * sizeof(PeImportDescriptor);
        if (!readModuleValue(moduleBase, moduleSize, descriptorOffset, descriptor))
            break;
        if (!descriptor.originalFirstThunk && !descriptor.timeDateStamp && !descriptor.forwarderChain &&
            !descriptor.name && !descriptor.firstThunk)
            break;

        if (optionalMagic == pe32PlusMagic)
            addImportThunks<std::uint64_t>(image, moduleBase, moduleSize, descriptor,
                                           remainingThunkEntries);
        else
            addImportThunks<std::uint32_t>(image, moduleBase, moduleSize, descriptor,
                                           remainingThunkEntries);

        if (!remainingThunkEntries)
            break;
    }
}

bool getImportThunkSlot(const unsigned char* instruction, duint instructionAddress,
                        duint& slotAddress)
{
    /*
     * Linkers commonly emit one of these six-byte import jump thunks:
     *
     *   x86:    ff 25 <absolute IAT address>
     *   x86-64: ff 25 <RIP-relative displacement>
     */
    if (instruction[0] != 0xff || instruction[1] != 0x25)
        return false;

#ifdef _WIN64
    std::int32_t displacement = 0;
    std::memcpy(&displacement, instruction + 2, sizeof(displacement));

    const duint instructionSize = 6;
    const duint maxAddress = (std::numeric_limits<duint>::max)();
    if (instructionAddress > maxAddress - instructionSize)
        return false;
    const duint nextInstruction = instructionAddress + instructionSize;

    if (displacement < 0)
    {
        const duint distance = static_cast<duint>(-
            static_cast<std::int64_t>(displacement));
        if (distance > nextInstruction)
            return false;
        slotAddress = nextInstruction - distance;
    }
    else
    {
        const duint distance = static_cast<duint>(displacement);
        if (nextInstruction > maxAddress - distance)
            return false;
        slotAddress = nextInstruction + distance;
    }
#else
    std::uint32_t absoluteAddress = 0;
    std::memcpy(&absoluteAddress, instruction + 2, sizeof(absoluteAddress));
    slotAddress = static_cast<duint>(absoluteAddress);
#endif

    return true;
}

void addImportThunkSymbols(nc::core::image::Image* image, duint moduleBase, duint moduleSize)
{
    const duint instructionSize = 6;
    const duint chunkSize = 64 * 1024;
    const duint maxThunkSymbols = 65536;
    const duint maxAddress = (std::numeric_limits<duint>::max)();
    if (!moduleSize || moduleBase > maxAddress - moduleSize)
        return;
    const duint moduleEnd = moduleBase + moduleSize;
    std::vector<unsigned char> bytes(chunkSize + instructionSize - 1);
    duint thunkSymbols = 0;

    for (const auto section : image->sections())
    {
        if (!section->isExecutable() || section->addr() < 0 || section->size() <= 0)
            continue;

        const auto sectionAddress64 = static_cast<std::uint64_t>(section->addr());
        const auto sectionSize64 = static_cast<std::uint64_t>(section->size());
        if (sectionAddress64 > maxAddress)
            continue;
        const duint sectionAddress = static_cast<duint>(sectionAddress64);
        if (sectionAddress >= moduleEnd || sectionSize64 >
            static_cast<std::uint64_t>(maxAddress - sectionAddress))
            continue;

        const duint sectionEnd = sectionAddress + static_cast<duint>(sectionSize64);
        duint current = sectionAddress > moduleBase ? sectionAddress : moduleBase;
        const duint end = sectionEnd < moduleEnd ? sectionEnd : moduleEnd;

        while (current < end)
        {
            const duint remaining = end - current;
            const duint candidates = chunkSize < remaining ? chunkSize : remaining;
            const duint requestedSize = candidates + instructionSize - 1;
            const duint bytesToRead = remaining < requestedSize ? remaining : requestedSize;
            duint sizeRead = 0;
            Memory::Read(current, bytes.data(), bytesToRead, &sizeRead);
            if (sizeRead > bytesToRead)
                sizeRead = bytesToRead;

            const duint readableCandidates = sizeRead >= instructionSize ?
                sizeRead - instructionSize + 1 : 0;
            const duint candidateCount = candidates < readableCandidates ?
                candidates : readableCandidates;
            for (duint offset = 0; offset < candidateCount; ++offset)
            {
                duint slotAddress = 0;
                if (!getImportThunkSlot(bytes.data() + offset, current + offset, slotAddress) ||
                    slotAddress < moduleBase || slotAddress >= moduleEnd)
                    continue;

                const auto relocation = image->getRelocation(slotAddress);
                const nc::core::image::Symbol* importSymbol = nullptr;
                if (relocation &&
                    relocation->symbol()->type() == nc::core::image::SymbolType::FUNCTION &&
                    !relocation->symbol()->name().isEmpty())
                    importSymbol = relocation->symbol();
                else
                    importSymbol = getFunctionSymbol(image, slotAddress);
                if (!importSymbol)
                    continue;

                const duint thunkAddress = current + offset;
                if (hasNameAtAddress(image, thunkAddress))
                    continue;

                image->addSymbol(std::make_unique<nc::core::image::Symbol>(
                    nc::core::image::SymbolType::FUNCTION,
                    importSymbol->name(), thunkAddress));
                if (++thunkSymbols >= maxThunkSymbols)
                    return;
            }

            current += candidates;
        }
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
        if (addr < mLowerBound || addr + size >= mUpperBound)
            return 0;
        duint sizeRead = 0;
        Memory::Read(addr, buf, size, &sizeRead);
        return sizeRead;
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
    if (moduleBase)
    {
        BridgeList<Module::ModuleSectionInfo> sections;
        if (Module::SectionListFromAddr(moduleBase, &sections))
        {
            success = true;
            for (auto i = 0; i < sections.Count(); i++)
            {
                auto sectionAddr = sections[i].addr;
                auto sectionSize = sections[i].size;
                auto section = std::make_unique<nc::core::image::Section>(sections[i].name, sectionAddr, sectionSize);
                section->setReadable(true);
                section->setWritable(true);
                section->setExecutable(true);
                section->setCode(true);
                section->setData(true);
                section->setAllocated(true);
                section->setExternalByteSource(std::make_unique<DbgByteSource>(sectionAddr, sectionAddr + sectionSize));
                image->addSection(std::move(section));
            }
        }
    }

    //add a made-up section in case there was an error with the module sections.
    if (!success)
    {
        auto section = std::make_unique<nc::core::image::Section>(".text", base, size);
        section->setReadable(true);
        section->setWritable(true);
        section->setExecutable(true);
        section->setCode(true);
        section->setData(true);
        section->setAllocated(true);
        section->setExternalByteSource(std::make_unique<DbgByteSource>(base, base + size));
        image->addSection(std::move(section));
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
            auto va = modBase + symbol.rva;
            auto name = QString::fromUtf8(symbol.name);
            if(symbol.type == Symbol::Import) //IAT entry
            {
                if (!name.isEmpty())
                    image->addRelocation(
                        std::make_unique<nc::core::image::Relocation>(
                            va,
                            image->addSymbol(std::make_unique<nc::core::image::Symbol>(
                                nc::core::image::SymbolType::FUNCTION, name, boost::none)),
                            image->platform().architecture()->bitness() / CHAR_BIT));
            }
            else //Function or Export
                image->addSymbol(std::make_unique<nc::core::image::Symbol>(nc::core::image::SymbolType::FUNCTION, name, va));
        }
    }

    /* Fill gaps left by Symbol::GetList from the mapped module's PE imports. */
    addPeImportRelocations(image, base, size);

    /* Give direct calls to linker-generated import jump thunks the IAT name. */
    addImportThunkSymbols(image, base, size);

    return project;
}

void SnowmanView::decompileAt(const SnowmanRange* ranges, duint count) const
{
    nc::gui::MainWindow* mainWindow = (nc::gui::MainWindow*)mSnowmanMainWindow;
    duint base = Module::BaseFromAddr(ranges->start);
    duint size = Module::SizeFromAddr(base);
    if(!base || !size) //we are not inside a module
        base = DbgMemFindBaseAddr(ranges->start, &size);
    mainWindow->open(MakeProject(base, size));
    mainWindow->project()->setName("Snowman");
    for(duint i = 0; i < count; i++)
        mainWindow->project()->disassemble(mainWindow->project()->image().get(), ranges[i].start, ranges[i].end + 1);
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
