/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "ImportedFunctionResolver.h"

#include <climits>

#include <nc/core/arch/Architecture.h>
#include <nc/core/image/Image.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/dflow/Dataflow.h>

namespace nc {
namespace core {
namespace ir {
namespace calling {

const image::Symbol *resolveImportedFunction(
        const Call *call, const dflow::Dataflow &dataflow,
        const image::Image &image) {
    if (!call || !dataflow.converged()) {
        return nullptr;
    }

    const arch::Architecture *architecture =
        image.platform().architecture();
    if (!architecture || architecture->bitness() <= 0 ||
        architecture->bitness() % CHAR_BIT != 0)
    {
        return nullptr;
    }

    return resolveImportedFunction(
        call, dataflow, architecture->bitness(),
        [&image](ByteAddr slot) {
            return image.getRelocation(slot);
        });
}

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
