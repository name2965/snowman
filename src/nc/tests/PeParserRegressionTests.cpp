/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include <cstdlib>
#include <cstring>
#include <iostream>
#include <memory>

#include <QBuffer>
#include <QByteArray>
#include <QIODevice>
#include <QString>

#include <nc/common/Exception.h>
#include <nc/common/LogToken.h>
#include <nc/common/Types.h>
#include <nc/core/image/Image.h>
#include <nc/core/image/Relocation.h>
#include <nc/core/image/Symbol.h>
#include <nc/input/pe/PeParser.h>

namespace {

const int NtHeaderOffset = 0x80;
const int FileHeaderOffset = NtHeaderOffset + 4;
const int OptionalHeaderOffset = FileHeaderOffset + 20;
const int DataDirectoryOffset = OptionalHeaderOffset + 112;
const int SectionTableOffset = OptionalHeaderOffset + 240;

const nc::ByteAddr ImageBase = 0x140000000LL;
const uint32_t ExceptionRva = 0x2000;
const uint32_t UnwindInfoRva = 0x2050;
const uint32_t DelayDirectoryRva = 0x2100;
const uint32_t DllNameRva = 0x2180;
const uint32_t DelayIatRva = 0x21a0;
const uint32_t DelayIntRva = 0x21c0;
const uint32_t HintNameRva = 0x21e0;
const uint32_t ExportDirectoryRva = 0x2200;
const uint32_t ExportFunctionTableRva = 0x2280;
const uint32_t ExportNameTableRva = 0x2290;
const uint32_t ExportOrdinalTableRva = 0x22a0;
const uint32_t BaseRelocationRva = 0x2300;

const int RdataFileOffset = 0x400;

void check(bool condition, const char *message) {
    if (!condition) {
        std::cerr << message << '\n';
        std::exit(1);
    }
}

template<class Integer>
void writeLittleEndian(QByteArray &bytes, int offset, Integer value) {
    for (std::size_t index = 0; index < sizeof(Integer); ++index) {
        bytes[offset + static_cast<int>(index)] =
            static_cast<char>((value >> (index * 8)) & 0xff);
    }
}

void writeBytes(QByteArray &bytes, int offset, const char *data,
                std::size_t size) {
    std::memcpy(bytes.data() + offset, data, size);
}

int rdataOffset(uint32_t rva) {
    return RdataFileOffset + static_cast<int>(rva - ExceptionRva);
}

void writeSection(QByteArray &bytes, int offset, const char *name,
                  uint32_t virtualSize, uint32_t virtualAddress,
                  uint32_t rawSize, uint32_t rawOffset,
                  uint32_t characteristics) {
    writeBytes(bytes, offset, name, std::strlen(name));
    writeLittleEndian<uint32_t>(bytes, offset + 8, virtualSize);
    writeLittleEndian<uint32_t>(bytes, offset + 12, virtualAddress);
    writeLittleEndian<uint32_t>(bytes, offset + 16, rawSize);
    writeLittleEndian<uint32_t>(bytes, offset + 20, rawOffset);
    writeLittleEndian<uint32_t>(bytes, offset + 36, characteristics);
}

QByteArray makePe64Image() {
    QByteArray bytes(0x800, 0);

    writeLittleEndian<uint16_t>(bytes, 0, 0x5a4d);
    writeLittleEndian<uint32_t>(bytes, 0x3c, NtHeaderOffset);
    writeLittleEndian<uint32_t>(bytes, NtHeaderOffset, 0x00004550);

    writeLittleEndian<uint16_t>(bytes, FileHeaderOffset, 0x8664);
    writeLittleEndian<uint16_t>(bytes, FileHeaderOffset + 2, 2);
    writeLittleEndian<uint16_t>(bytes, FileHeaderOffset + 16, 240);
    writeLittleEndian<uint16_t>(bytes, FileHeaderOffset + 18, 0x22);

    writeLittleEndian<uint16_t>(bytes, OptionalHeaderOffset, 0x20b);
    writeLittleEndian<uint32_t>(bytes, OptionalHeaderOffset + 16, 0x1000);
    writeLittleEndian<uint64_t>(
        bytes, OptionalHeaderOffset + 24,
        static_cast<uint64_t>(ImageBase));
    writeLittleEndian<uint32_t>(bytes, OptionalHeaderOffset + 32, 0x1000);
    writeLittleEndian<uint32_t>(bytes, OptionalHeaderOffset + 36, 0x200);
    writeLittleEndian<uint32_t>(bytes, OptionalHeaderOffset + 108, 16);

    writeLittleEndian<uint32_t>(
        bytes, DataDirectoryOffset + 3 * 8, ExceptionRva);
    writeLittleEndian<uint32_t>(bytes, DataDirectoryOffset + 3 * 8 + 4, 12);
    writeLittleEndian<uint32_t>(
        bytes, DataDirectoryOffset + 13 * 8, DelayDirectoryRva);
    writeLittleEndian<uint32_t>(bytes, DataDirectoryOffset + 13 * 8 + 4, 64);

    writeSection(bytes, SectionTableOffset, ".text", 0x100, 0x1000,
                 0x200, 0x200, 0x60000020);
    writeSection(bytes, SectionTableOffset + 40, ".rdata", 0x400,
                 ExceptionRva, 0x400, RdataFileOffset, 0x40000040);

    writeLittleEndian<uint32_t>(
        bytes, rdataOffset(ExceptionRva), 0x1000);
    writeLittleEndian<uint32_t>(
        bytes, rdataOffset(ExceptionRva) + 4, 0x1010);
    writeLittleEndian<uint32_t>(
        bytes, rdataOffset(ExceptionRva) + 8, UnwindInfoRva);
    bytes[rdataOffset(UnwindInfoRva)] = 1; /* UNWIND_INFO version one. */

    const int descriptor = rdataOffset(DelayDirectoryRva);
    writeLittleEndian<uint32_t>(bytes, descriptor, 1); /* RVA based. */
    writeLittleEndian<uint32_t>(bytes, descriptor + 4, DllNameRva);
    writeLittleEndian<uint32_t>(bytes, descriptor + 12, DelayIatRva);
    writeLittleEndian<uint32_t>(bytes, descriptor + 16, DelayIntRva);

    writeBytes(bytes, rdataOffset(DllNameRva), "sample.dll", 11);
    writeLittleEndian<uint64_t>(
        bytes, rdataOffset(DelayIntRva), HintNameRva);
    writeLittleEndian<uint16_t>(bytes, rdataOffset(HintNameRva), 0);
    writeBytes(bytes, rdataOffset(HintNameRva) + 2, "DelayedFn", 10);

    return bytes;
}

void addExports(QByteArray &bytes) {
    writeLittleEndian<uint32_t>(
        bytes, DataDirectoryOffset, ExportDirectoryRva);
    writeLittleEndian<uint32_t>(bytes, DataDirectoryOffset + 4, 0x80);

    const int directory = rdataOffset(ExportDirectoryRva);
    writeLittleEndian<uint32_t>(bytes, directory + 16, 1); /* Base. */
    writeLittleEndian<uint32_t>(bytes, directory + 20, 2);
    writeLittleEndian<uint32_t>(bytes, directory + 24, 2);
    writeLittleEndian<uint32_t>(
        bytes, directory + 28, ExportFunctionTableRva);
    writeLittleEndian<uint32_t>(
        bytes, directory + 32, ExportNameTableRva);
    writeLittleEndian<uint32_t>(
        bytes, directory + 36, ExportOrdinalTableRva);

    writeLittleEndian<uint32_t>(
        bytes, rdataOffset(ExportFunctionTableRva), 0x1000);
    writeLittleEndian<uint32_t>(
        bytes, rdataOffset(ExportFunctionTableRva) + 4, 0x2240);
    writeLittleEndian<uint32_t>(
        bytes, rdataOffset(ExportNameTableRva), 0x22b0);
    writeLittleEndian<uint32_t>(
        bytes, rdataOffset(ExportNameTableRva) + 4, 0x22c0);
    writeLittleEndian<uint16_t>(
        bytes, rdataOffset(ExportOrdinalTableRva), 0);
    writeLittleEndian<uint16_t>(
        bytes, rdataOffset(ExportOrdinalTableRva) + 2, 1);
    writeBytes(bytes, rdataOffset(0x2240), "other.Target", 13);
    writeBytes(bytes, rdataOffset(0x22b0), "RealExport", 11);
    writeBytes(bytes, rdataOffset(0x22c0), "ForwardedExport", 16);
}

void addBaseRelocation(QByteArray &bytes, uint32_t blockSize = 12) {
    writeLittleEndian<uint32_t>(
        bytes, DataDirectoryOffset + 5 * 8, BaseRelocationRva);
    writeLittleEndian<uint32_t>(bytes, DataDirectoryOffset + 5 * 8 + 4, 12);

    const int block = rdataOffset(BaseRelocationRva);
    writeLittleEndian<uint32_t>(bytes, block, 0x1000);
    writeLittleEndian<uint32_t>(bytes, block + 4, blockSize);
    writeLittleEndian<uint16_t>(bytes, block + 8, 0xa008);
    writeLittleEndian<uint16_t>(bytes, block + 10, 0);
    writeLittleEndian<uint64_t>(
        bytes, 0x208, static_cast<uint64_t>(ImageBase + 0x1234));
    writeLittleEndian<uint32_t>(
        bytes, SectionTableOffset + 40 + 36, 0x42000040);
}

const nc::core::image::Symbol *findSymbol(
        const nc::core::image::Image &image, const char *name) {
    for (const auto *symbol: image.symbols()) {
        if (symbol->name() == QLatin1String(name)) {
            return symbol;
        }
    }
    return nullptr;
}

std::unique_ptr<nc::core::image::Image> parseImage(QByteArray bytes) {
    QBuffer source(&bytes);
    check(source.open(QIODevice::ReadOnly), "Cannot open the PE test buffer.");

    nc::input::pe::PeParser parser;
    check(parser.canParse(&source), "Generated PE image was not recognized.");

    std::unique_ptr<nc::core::image::Image> image(
        new nc::core::image::Image());
    nc::LogToken log;
    parser.parse(&source, image.get(), log);
    return image;
}

void testRuntimeFunctionAndDelayImport() {
    const auto image = parseImage(makePe64Image());

    check(image->functionEntries().count(ImageBase + 0x1000) == 1,
          "AMD64 runtime function did not create a function boundary.");

    const nc::core::image::Relocation *relocation =
        image->getRelocation(ImageBase + DelayIatRva);
    check(relocation != nullptr,
          "Delay import did not create an IAT relocation.");
    check(relocation->size() == 8,
          "PE32+ delay import relocation has the wrong pointer size.");
    check(relocation->symbol()->name() == QLatin1String("DelayedFn"),
          "Delay import symbol has the wrong name.");
    check(relocation->symbol()->moduleName() == QLatin1String("sample.dll"),
          "Delay import symbol lost its source module.");
}

void testChainedRuntimeFunctionIsNotAnEntry() {
    QByteArray bytes = makePe64Image();
    bytes[rdataOffset(UnwindInfoRva)] =
        static_cast<char>((4 << 3) | 1); /* UNW_FLAG_CHAININFO. */
    const auto image = parseImage(bytes);
    check(image->functionEntries().empty(),
          "Chained unwind region was treated as a callable function entry.");
}

void testMalformedDelayImportsAreRejected() {
    QByteArray bytes = makePe64Image();
    writeLittleEndian<uint64_t>(
        bytes, rdataOffset(DelayIntRva), uint64_t(0x80000000));
    auto image = parseImage(bytes);
    check(image->getRelocation(ImageBase + DelayIatRva) == nullptr,
          "Reserved PE32+ thunk bits were accepted as a name RVA.");

    bytes = makePe64Image();
    writeLittleEndian<uint32_t>(
        bytes, rdataOffset(DelayDirectoryRva), 3);
    image = parseImage(bytes);
    check(image->getRelocation(ImageBase + DelayIatRva) == nullptr,
          "Unknown delay-import attributes were accepted.");
}

void testUndeclaredDataDirectoriesAreIgnored() {
    QByteArray bytes = makePe64Image();
    writeLittleEndian<uint32_t>(bytes, OptionalHeaderOffset + 108, 4);
    const auto image = parseImage(bytes);

    check(image->functionEntries().count(ImageBase + 0x1000) == 1,
          "Declared exception directory was not parsed.");
    check(image->getRelocation(ImageBase + DelayIatRva) == nullptr,
          "Directory beyond NumberOfRvaAndSizes was parsed.");
}

void testSectionAddressOverflowIsRejected() {
    QByteArray bytes = makePe64Image();
    writeLittleEndian<uint64_t>(
        bytes, OptionalHeaderOffset + 24,
        uint64_t(0x7ffffffffffff800));

    bool rejected = false;
    try {
        parseImage(bytes);
    } catch (const nc::Exception &) {
        rejected = true;
    }
    check(rejected, "Overflowing image-base plus section RVA was accepted.");
}

void testExportsUseCheckedRvasAndRecognizeForwarders() {
    QByteArray bytes = makePe64Image();
    addExports(bytes);
    auto image = parseImage(bytes);

    const nc::core::image::Symbol *realExport =
        findSymbol(*image, "RealExport");
    check(realExport && realExport->value() &&
              *realExport->value() == ImageBase + 0x1000,
          "A valid named export was not recovered.");
    check(findSymbol(*image, "ForwardedExport") == nullptr,
          "An export forwarder was treated as local executable code.");

    bytes = makePe64Image();
    addExports(bytes);
    writeLittleEndian<uint16_t>(
        bytes, rdataOffset(ExportOrdinalTableRva) + 2, 2);
    image = parseImage(bytes);
    check(findSymbol(*image, "RealExport") != nullptr,
          "A malformed export ordinal discarded earlier valid exports.");
    check(findSymbol(*image, "ForwardedExport") == nullptr,
          "An out-of-range export ordinal was dereferenced.");

    bytes = makePe64Image();
    addExports(bytes);
    writeLittleEndian<uint32_t>(
        bytes, rdataOffset(ExportDirectoryRva) + 32, 0xfffffff0);
    image = parseImage(bytes);
    check(findSymbol(*image, "RealExport") == nullptr,
          "Overflowing export-table address arithmetic was accepted.");
}

void testBaseRelocationsAreBoundedAndKeep64BitAddresses() {
    QByteArray bytes = makePe64Image();
    addBaseRelocation(bytes);
    auto image = parseImage(bytes);

    const nc::core::image::Relocation *relocation =
        image->getRelocation(ImageBase + 0x1008);
    check(relocation != nullptr,
          "Base relocation outside a section named .reloc was ignored.");
    check(relocation->address() == ImageBase + 0x1008 &&
              relocation->size() == 8 && relocation->addend() == 0x1234,
          "DIR64 relocation lost its width, address, or addend.");

    const uint32_t malformedSizes[] = {0, 7, 16};
    for (uint32_t size: malformedSizes) {
        bytes = makePe64Image();
        addBaseRelocation(bytes, size);
        writeBytes(bytes, SectionTableOffset + 40, ".reloc", 6);
        image = parseImage(bytes);
        check(image->getRelocation(ImageBase + 0x1008) == nullptr,
              "Malformed base relocation block was accepted.");
    }
}

void testMalformedCoffTablesDoNotAllocateOrReadOutOfRange() {
    QByteArray bytes = makePe64Image();
    writeLittleEndian<uint32_t>(bytes, FileHeaderOffset + 8, 0x780);
    writeLittleEndian<uint32_t>(bytes, FileHeaderOffset + 12, 0xffffffff);
    auto image = parseImage(bytes);
    check(image != nullptr, "Oversized COFF symbol count was not rejected safely.");

    bytes = makePe64Image();
    writeLittleEndian<uint32_t>(bytes, FileHeaderOffset + 8, 0x780);
    writeLittleEndian<uint32_t>(bytes, FileHeaderOffset + 12, 1);
    writeBytes(bytes, 0x780, "coff", 5);
    writeLittleEndian<uint32_t>(bytes, 0x792, 3);
    image = parseImage(bytes);
    check(findSymbol(*image, "coff") == nullptr,
          "Undersized COFF string table was accepted.");
}

void testRawSectionRangeIsValidatedBeforeAllocation() {
    QByteArray bytes = makePe64Image();
    writeLittleEndian<uint32_t>(
        bytes, SectionTableOffset + 40 + 16, 0x100000);

    bool rejected = false;
    try {
        parseImage(bytes);
    } catch (const nc::Exception &) {
        rejected = true;
    }
    check(rejected, "Out-of-file section raw data was accepted.");
}

} // anonymous namespace

int main() {
    testRuntimeFunctionAndDelayImport();
    testChainedRuntimeFunctionIsNotAnEntry();
    testMalformedDelayImportsAreRejected();
    testUndeclaredDataDirectoriesAreIgnored();
    testSectionAddressOverflowIsRejected();
    testExportsUseCheckedRvasAndRecognizeForwarders();
    testBaseRelocationsAreBoundedAndKeep64BitAddresses();
    testMalformedCoffTablesDoNotAllocateOrReadOutOfRange();
    testRawSectionRangeIsValidatedBeforeAllocation();
    return 0;
}

/* vim:set et sts=4 sw=4: */
