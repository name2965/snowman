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

#include "IRGenerator.h"

#include <cassert>
#include <climits>
#include <limits>
#include <queue>

#include <boost/range/algorithm_ext/is_sorted.hpp>
#include <boost/unordered_set.hpp>

#include <nc/common/Foreach.h>
#include <nc/common/Range.h>
#include <nc/common/make_unique.h>

#include <nc/core/arch/Architecture.h>
#include <nc/core/arch/Disassembler.h>
#include <nc/core/arch/Instructions.h>
#include <nc/core/image/Image.h>
#include <nc/core/image/Reader.h>
#include <nc/core/image/Section.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/Program.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/dflow/Dataflow.h>
#include <nc/core/ir/dflow/DataflowAnalyzer.h>
#include <nc/core/ir/dflow/Value.h>
#include <nc/core/ir/misc/ArrayAccess.h>
#include <nc/core/ir/misc/PatternRecognition.h>

#include "InstructionAnalyzer.h"

namespace nc {
namespace core {
namespace irgen {

IRGenerator::IRGenerator(const image::Image *image, const arch::Instructions *instructions, ir::Program *program,
    const CancellationToken &canceled, const LogToken &log):
    image_(image), instructions_(instructions), program_(program), canceled_(canceled), log_(log)
{
    assert(image);
    assert(instructions);
    assert(program);
}

IRGenerator::~IRGenerator() {}

void IRGenerator::generate() {
    image_->platform().architecture()->createInstructionAnalyzer()->createStatements(instructions_, program_, canceled_, log_);

#ifndef NDEBUG
    /*
     * Check statements are sorted by their instructions' addresses.
     * ir::Program::createBasicBlock(ByteAddr) relies on this while splitting basic blocks.
     */
    foreach (auto basicBlock, program_->basicBlocks()) {
        assert((boost::is_sorted(basicBlock->statements(), [](const ir::Statement *a, const ir::Statement *b) -> bool {
            return a->instruction()->addr() < b->instruction()->addr();
        })));
    }
#endif

    /* Compute jump targets. */
    foreach (auto basicBlock, program_->basicBlocks()) {
        computeJumpTargets(basicBlock);
        canceled_.poll();
    }

#ifndef NDEBUG
    /*
     * Check that a terminator statement is always the last statement in the basic block.
     */
    foreach (auto basicBlock, program_->basicBlocks()) {
        foreach (auto statement, basicBlock->statements()) {
            if (statement->isTerminator()) {
                assert(statement == basicBlock->statements().back());
            }
        }
    }
#endif

    /* Add jumps to direct successors where necessary. */
    foreach (auto basicBlock, program_->basicBlocks()) {
        addJumpToDirectSuccessor(basicBlock);
        canceled_.poll();
    }
}

void IRGenerator::computeJumpTargets(ir::BasicBlock *basicBlock) {
    assert(basicBlock != nullptr);

    /* Prepare context for quick and dirty dataflow analysis. */
    ir::dflow::Dataflow dataflow;
    ir::dflow::DataflowAnalyzer analyzer(dataflow, image_->platform().architecture(), canceled_, log_);
    ir::dflow::ReachingDefinitions definitions;

    foreach (auto statement, basicBlock->statements()) {
        /* Do not expose the previous prefix as a completed result while the
         * next transfer function is still updating it. */
        dataflow.setAnalysisStatus(ir::dflow::DataflowStatus::RUNNING);
        analyzer.execute(statement, definitions);

        /* This is a straight-line abstract interpretation of the current
         * block prefix, rather than a bounded global CFG iteration.  The
         * facts are complete for that local domain once execute() returns.
         * Mark that explicitly so semantic pattern recognizers can reject
         * genuinely unfinished global analyses without disabling the jump
         * table discovery for which this local analyzer exists. */
        dataflow.setConverged(true);

        switch (statement->kind()) {
            case ir::Statement::INLINE_ASSEMBLY: {
                /*
                 * Inline assembly can do unpredictable things.
                 * Therefore, clear the reaching definitions.
                 */
                definitions.clear();
                break;
            }
            case ir::Statement::CALL: {
                auto call = statement->asCall();
                const ir::dflow::Value *addressValue =
                    dataflow.findValue(call->target());

                /* Record information about the function entry. */
                if (addressValue &&
                    addressValue->abstractValue().isConcrete()) {
                    ByteAddr address = addressValue->abstractValue().asConcrete().value();

                    program_->addCalledAddress(address);
                    program_->createBasicBlock(address);
                } else {
                    foreach (ByteAddr address, getJumpTableEntries(call->target(), dataflow)) {
                        program_->addCalledAddress(address);
                        program_->createBasicBlock(address);
                    }
                }

                /*
                 * A call can do unpredictable things.
                 * Therefore, clear the reaching definitions.
                 */
                definitions.clear();
                break;
            }
            case ir::Statement::JUMP: {
                auto jump = statement->as<ir::Jump>();

                /* If the target basic block is unknown, try to guess it. */
                computeJumpTarget(jump->thenTarget(), dataflow);
                computeJumpTarget(jump->elseTarget(), dataflow);

                break;
            }
        }

        if (statement->isTerminator() && statement->basicBlock()->address() && statement->instruction()) {
            program_->createBasicBlock(statement->instruction()->endAddr());
        }
    }
}

void IRGenerator::computeJumpTarget(ir::JumpTarget &target, const ir::dflow::Dataflow &dataflow) {
    if (target.address() && !target.basicBlock() && !target.table()) {
        const ir::dflow::Value *addressValue =
            dataflow.findValue(target.address());

        if (addressValue && addressValue->abstractValue().isConcrete()) {
            target.setBasicBlock(program_->createBasicBlock(addressValue->abstractValue().asConcrete().value()));
        } else {
            auto entries = getJumpTableEntries(target.address(), dataflow);

            if (!entries.empty()) {
                auto table = std::make_unique<ir::JumpTable>();

                foreach (ByteAddr targetAddress, entries) {
                    table->push_back(ir::JumpTableEntry(targetAddress, program_->createBasicBlock(targetAddress)));
                }
                target.setTable(std::move(table));
            }
        }
    }
}

std::vector<ByteAddr> IRGenerator::getJumpTableEntries(const ir::Term *target, const ir::dflow::Dataflow &dataflow) {
    std::vector<ByteAddr> result;

    auto arrayAccess = ir::misc::recognizeArrayAccess(target, dataflow);
    if (!arrayAccess) {
        return result;
    }

    const SmallBitSize targetSize = target->size();
    if (targetSize <= 0 || targetSize % CHAR_BIT != 0 ||
        targetSize > static_cast<SmallBitSize>(sizeof(ByteAddr) * CHAR_BIT))
    {
        return result;
    }

    ConstantValue maximumAddress = static_cast<ConstantValue>(
        (std::numeric_limits<ByteAddr>::max)());
    if (targetSize < static_cast<SmallBitSize>(
            sizeof(ConstantValue) * CHAR_BIT))
    {
        const ConstantValue targetAddressMask =
            (ConstantValue(1) << targetSize) - 1;
        if (targetAddressMask < maximumAddress) {
            maximumAddress = targetAddressMask;
        }
    }
    if (arrayAccess.base() > maximumAddress ||
        arrayAccess.stride() == 0 ||
        arrayAccess.stride() > maximumAddress)
    {
        return result;
    }

    /* Safety net. */
    const std::size_t maxTableEntries = 65536;
    const ByteSize entrySize = targetSize / CHAR_BIT;

    image::Reader reader(image_);

    auto byteOrder = image_->platform().architecture()->getByteOrder(ir::MemoryDomain::MEMORY);

    ByteAddr address = static_cast<ByteAddr>(arrayAccess.base());
    const ByteAddr stride = static_cast<ByteAddr>(arrayAccess.stride());
    const ByteAddr maximumEntryStart =
        static_cast<ByteAddr>(maximumAddress) - (entrySize - 1);
    while (address <= maximumEntryStart) {
        auto entry = reader.readInt<ByteAddr>(address, entrySize, byteOrder);
        if (!entry) {
            break;
        }
        if (!isInstructionAddress(*entry)) {
            break;
        }
        if (result.size() >= maxTableEntries) {
            log_.warning(tr("Jump table at address %1 has more than %2 entries.").arg(address).arg(maxTableEntries));
            break;
        }
        result.push_back(*entry);
        if (address > static_cast<ByteAddr>(maximumAddress) - stride) {
            break;
        }
        address += stride;
    }

    return result;
}

bool IRGenerator::isInstructionAddress(ByteAddr address) {
    if (instructions_->get(address)) {
        return true;
    }

    auto section = image_->getSectionContainingAddress(address);
    if (!section || !section->isExecutable()) {
        return false;
    }

    if (!disassembler_) {
        disassembler_ = image_->platform().architecture()->createDisassembler();
    }

    return disassembler_->disassembleSingleInstruction(address, section) != nullptr;
}

void IRGenerator::addJumpToDirectSuccessor(ir::BasicBlock *basicBlock) {
    assert(basicBlock != nullptr);

    if (!basicBlock->getTerminator()) {
        if (basicBlock->successorAddress() && basicBlock->successorAddress() != basicBlock->address()) {
            if (auto directSuccessor = program_->getBasicBlockStartingAt(*basicBlock->successorAddress())) {
                basicBlock->pushBack(std::make_unique<ir::Jump>(ir::JumpTarget(directSuccessor)));
            }
        }
    }
}

} // namespace irgen
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
