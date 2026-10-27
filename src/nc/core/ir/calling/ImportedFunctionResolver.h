/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <functional>

#include <nc/common/Types.h>

namespace nc {
namespace core {

namespace image {
class Image;
class Relocation;
class Symbol;
}

namespace ir {

class Call;
class Function;
class Statement;

namespace dflow {
class Dataflow;
}

namespace calling {

/** Exact lookup for a relocation starting at a byte address. */
typedef std::function<const image::Relocation *(ByteAddr)>
    ImportRelocationLookup;

/**
 * Checks that no visible write on a CFG path preceding \p statement may
 * overlap one exact import slot.
 *
 * Global image memory is deliberately not part of the ordinary reaching-
 * definitions lattice. This query supplies the missing, conservative guard
 * for relocation-based semantic decisions. Exact and partial writes, opaque
 * assembly, and unresolved writes through the image-memory domain fail
 * closed.
 *
 * Relocation slots are modeled as static linkage memory, separate from
 * caller-owned memory covered by synthetic TrackedMemoryInvalidation nodes.
 * Those contract-derived nodes are deliberately excluded so import proofs
 * remain monotone across semantic passes. Open-world code which discovers
 * and patches an arbitrary IAT without an explicit decoded write or inline
 * assembly is outside this static-image model.
 *
 * A write after the statement is considered only when a CFG cycle can bring
 * it back before a later execution of the statement.
 */
bool isImportSlotUnmodifiedBefore(
    const Statement *statement, const dflow::Dataflow &dataflow,
    SmallBitSize pointerSize, ByteAddr slot);

/**
 * Checks whether any statement in one recovered Function may overwrite an
 * exact import slot.
 *
 * This deliberately ignores execution order. It is intended for
 * whole-program guards around persistent or destructive import semantics:
 * if any analyzed function can visibly patch the slot, a static relocation
 * is no longer an invariant. Missing or unconverged analysis fails closed.
 */
bool mayFunctionOverwriteImportSlot(
    const Function *function, const dflow::Dataflow &dataflow,
    SmallBitSize pointerSize, ByteAddr slot);

/**
 * Resolves an indirect call whose value is proved to originate from an
 * import relocation.
 *
 * The resolver follows exact copy definitions only. Every reaching
 * definition must be complete and must resolve to the same Symbol object.
 * Incoming, unknown, partial, conflicting, or cyclic definitions fail
 * closed.
 *
 * \return The imported function symbol, or nullptr when the origin cannot be
 *         proved uniquely.
 */
const image::Symbol *resolveImportedFunction(
    const Call *call, const dflow::Dataflow &dataflow,
    const image::Image &image);

/**
 * Architecture-independent overload used when the caller already owns an
 * exact relocation index. The pointer size is in bits.
 */
const image::Symbol *resolveImportedFunction(
    const Call *call, const dflow::Dataflow &dataflow,
    SmallBitSize pointerSize, const ImportRelocationLookup &lookup);

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
