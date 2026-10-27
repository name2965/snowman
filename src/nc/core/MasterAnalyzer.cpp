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

#include "MasterAnalyzer.h"

#include <limits>
#include <stdexcept>

#include <nc/common/Foreach.h>
#include <nc/common/make_unique.h>

#include <nc/core/Context.h>
#include <nc/core/arch/Architecture.h>
#include <nc/core/arch/Instructions.h>
#include <nc/core/image/Image.h>
#include <nc/core/image/Section.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/CFG.h>
#include <nc/core/ir/Dominators.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Functions.h>
#include <nc/core/ir/FunctionsGenerator.h>
#include <nc/core/ir/Program.h>
#include <nc/core/ir/PostDominators.h>
#include <nc/core/ir/calling/Conventions.h>
#include <nc/core/ir/calling/Hooks.h>
#include <nc/core/ir/calling/SignatureAnalyzer.h>
#include <nc/core/ir/calling/Signatures.h>
#include <nc/core/ir/cflow/Graphs.h>
#include <nc/core/ir/cflow/GraphBuilder.h>
#include <nc/core/ir/cflow/StructureAnalyzer.h>
#include <nc/core/ir/cgen/CodeGenerator.h>
#include <nc/core/ir/cgen/NameGenerator.h>
#include <nc/core/ir/dflow/Dataflows.h>
#include <nc/core/ir/dflow/DataflowAnalyzer.h>
#include <nc/core/ir/dflow/DefUseGraph.h>
#include <nc/core/ir/dflow/ExpressionIdentity.h>
#include <nc/core/ir/dflow/ValueProvenance.h>
#include <nc/core/ir/idiom/IdiomAnalyzer.h>
#include <nc/core/ir/idiom/Idioms.h>
#include <nc/core/ir/liveness/Livenesses.h>
#include <nc/core/ir/liveness/LivenessAnalyzer.h>
#include <nc/core/ir/types/TypeAnalyzer.h>
#include <nc/core/ir/types/Types.h>
#include <nc/core/ir/vars/VariableAnalyzer.h>
#include <nc/core/ir/vars/Variables.h>
#include <nc/core/irgen/IRGenerator.h>
#include <nc/core/likec/Tree.h>
#include <nc/core/mangling/Demangler.h>

namespace nc {
namespace core {

namespace {

/*
 * Dataflow facts and hook patches are keyed by IR pointers.  In particular,
 * callback statements installed by Hooks capture the Dataflow of the pass
 * which created them.  Destroy every downstream consumer first, remove all
 * callbacks while their Dataflow objects are still alive, and only then drop
 * the old Dataflows.  This ordering is also used before virtual analysis
 * entry points so a subclass cannot accidentally observe products from two
 * different passes.
 */
void discardDataflowConsumers(Context &context) {
    context.setTree(nullptr);
    context.setTypes(nullptr);
    context.setIdioms(nullptr);
    context.setGraphs(nullptr);
    context.setVariables(nullptr);
    context.setLivenesses(nullptr);
}

void discardDataflowProducts(Context &context) {
    discardDataflowConsumers(context);

    if (context.hooks() && context.functions()) {
        foreach (ir::Function *function, context.functions()->list()) {
            context.hooks()->deinstrument(function);
        }
    }

    context.setDataflows(nullptr);
}

/** Drops everything owned by or referring through the active Hooks object.
 * Hooks must die before their referenced Signatures and Conventions. */
void discardHookProducts(Context &context) {
    discardDataflowProducts(context);
    context.setHooks(nullptr);
    context.setSignatures(nullptr);
    context.setConventions(nullptr);
}

/** Drops every analysis product keyed by cloned Function/Statement pointers. */
void discardFunctionProducts(Context &context) {
    discardHookProducts(context);
    context.setFunctions(nullptr);
}

} // anonymous namespace

MasterAnalyzer::~MasterAnalyzer() {}

void MasterAnalyzer::createProgram(Context &context) const {
    context.logToken().info(tr("Creating intermediate representation of the program."));

    std::unique_ptr<ir::Program> program(new ir::Program());

    /*
     * Create known entries before IR generation. This makes the instruction
     * analyzer start a basic block at each boundary instead of discovering
     * and splitting it only after fall-through edges have been constructed.
     */
    auto addFunctionEntry = [&](ByteAddr address,
                                bool requireExecutableSection) {
        const auto &instruction = context.instructions()->get(address);
        if (!instruction) {
            return;
        }

        if (requireExecutableSection) {
            const auto section =
                context.image()->getSectionContainingAddress(address);
            if (!section || !section->isExecutable() ||
                instruction->size() <= 0 ||
                address > (std::numeric_limits<ByteAddr>::max)() -
                    instruction->size() ||
                !section->containsAddress(
                    address + instruction->size() - 1))
            {
                return;
            }
        }

        program->addFunctionEntry(address);
        program->createBasicBlock(address);
    };

    if (context.image()->entrypoint()) {
        addFunctionEntry(*context.image()->entrypoint(), false);
    }

    foreach (ByteAddr address, context.image()->functionEntries()) {
        addFunctionEntry(address, false);
    }

    /* Object formats and debugger bridges commonly express exports or debug
     * functions as symbols without duplicating them in functionEntries().
     * Treat only executable, exactly decoded symbol values as boundaries;
     * this excludes imported IAT data and arbitrary interior-byte labels. */
    foreach (const auto symbol, context.image()->symbols()) {
        if (symbol->type() == image::SymbolType::FUNCTION &&
            symbol->value() &&
            *symbol->value() <= static_cast<ConstantValue>(
                (std::numeric_limits<ByteAddr>::max)()))
        {
            addFunctionEntry(
                static_cast<ByteAddr>(*symbol->value()), true);
        }
    }

    core::irgen::IRGenerator(context.image().get(), context.instructions().get(), program.get(),
        context.cancellationToken(), context.logToken())
    .generate();

    /* Public phase methods may be rerun independently. Publish the new
     * Program only after invalidating every product keyed by the old one. */
    discardFunctionProducts(context);
    context.setProgram(std::move(program));
}

void MasterAnalyzer::createFunctions(Context &context) const {
    context.logToken().info(tr("Creating functions."));

    std::unique_ptr<ir::Functions> functions(new ir::Functions);

    ir::FunctionsGenerator().makeFunctions(*context.program(), *functions);

    /* Function clones own all statements instrumented by Hooks. Remove those
     * patches and their captured Dataflows before replacing the clone set. */
    discardHookProducts(context);
    context.setFunctions(std::move(functions));
}

void MasterAnalyzer::createHooks(Context &context) const {
    context.logToken().info(tr("Creating hooks."));

    /* Recreating this public phase after a prior dataflow pass must first
     * remove callbacks and patches owned by the old Hooks object. Destroy the
     * old Hooks before the registries to which it holds references. */
    discardHookProducts(context);
    auto signatures = std::make_unique<ir::calling::Signatures>();
    auto conventions = std::make_unique<ir::calling::Conventions>();
    auto hooks = std::make_unique<ir::calling::Hooks>(
        *conventions, *signatures);
    hooks->setConventionDetector([this, &context](const ir::calling::CalleeId &calleeId) {
        this->detectCallingConvention(context, calleeId);
    });

    /* Construct the mutually-referencing set off-context, then publish the
     * registries before the Hooks object which refers to them. */
    context.setSignatures(std::move(signatures));
    context.setConventions(std::move(conventions));
    context.setHooks(std::move(hooks));
}

void MasterAnalyzer::detectCallingConventions(Context &) const {
    return;
}

void MasterAnalyzer::detectCallingConvention(Context &context, const ir::calling::CalleeId &calleeId) const {
    if (!context.image()->platform().architecture()->conventions().empty()) {
        context.conventions()->setConvention(calleeId, context.image()->platform().architecture()->conventions().front());
    }
}

void MasterAnalyzer::dataflowAnalysis(Context &context) const {
    context.logToken().info(tr("Dataflow analysis."));

    /* Keep this public phase safe when it is called independently of
     * decompile().  decompile() performs the same invalidation before the
     * virtual dispatch so overrides receive an equally clean snapshot. */
    discardDataflowProducts(context);
    context.setDataflows(std::make_unique<ir::dflow::Dataflows>());

    foreach (auto function, context.functions()->list()) {
        dataflowAnalysis(context, function);
        context.cancellationToken().poll();
    }
}

void MasterAnalyzer::dataflowAnalysis(Context &context, ir::Function *function) const {
    context.logToken().info(tr("Dataflow analysis of %1.").arg(getFunctionName(context, function)));

    /* This overload is public and can replace one result independently.
     * Consumers aggregate facts from the whole Dataflows map and therefore
     * become stale even when only one function is recomputed. */
    discardDataflowConsumers(context);
    if (!context.dataflows()) {
        context.setDataflows(std::make_unique<ir::dflow::Dataflows>());
    }

    std::unique_ptr<ir::dflow::Dataflow> dataflow(new ir::dflow::Dataflow());

    try {
        context.hooks()->instrument(function, dataflow.get());

        ir::dflow::DataflowAnalyzer(*dataflow, context.image()->platform().architecture(), context.cancellationToken(),
                                    context.logToken()).analyze(ir::CFG(function->basicBlocks()));

        context.hooks()->finalizeInstrumentation(function, *dataflow);

        auto old = context.dataflows()->find(function);
        if (old != context.dataflows()->end()) {
            /* Hooks::instrument() already replaced every callback with one
             * capturing this new object. unique_ptr replacement is noexcept,
             * so the old Dataflow cannot outlive those callbacks by accident. */
            old->second = std::move(dataflow);
        } else {
            context.dataflows()->emplace(function, std::move(dataflow));
        }
    } catch (...) {
        /* Callback statements capture dataflow.get().  Never leave them in
         * the Function when analysis or publication of that Dataflow fails. */
        context.hooks()->deinstrument(function);
        /* An older result for this function no longer matches the now-removed
         * instrumentation and must not remain visible as a current product. */
        context.dataflows()->erase(function);
        throw;
    }
}

void MasterAnalyzer::reconstructSignatures(Context &context) const {
    context.logToken().info(tr("Reconstructing function signatures."));

    /* Signature analysis computes a complete snapshot. Replacing the
     * inferred layer prevents facts which disappeared after a refined
     * dataflow pass from surviving indefinitely. */
    context.signatures()->beginInferenceUpdate();
    try {
        ir::calling::SignatureAnalyzer(*context.signatures(), *context.dataflows(), *context.hooks(),
            *context.livenesses(), context.cancellationToken(), context.logToken())
            .analyze();
        context.signatures()->finishInferenceUpdate();
    } catch (...) {
        context.signatures()->cancelInferenceUpdate();
        throw;
    }
}

bool MasterAnalyzer::applyExternalSignatures(Context &, bool) const {
    return false;
}

void MasterAnalyzer::reconstructVariables(Context &context) const {
    context.logToken().info(tr("Reconstructing variables."));

    std::unique_ptr<ir::vars::Variables> variables(new ir::vars::Variables());

    ir::vars::VariableAnalyzer(*variables, *context.dataflows(), context.image()->platform().architecture())
        .analyze();

    context.setVariables(std::move(variables));
}

void MasterAnalyzer::livenessAnalysis(Context &context) const {
    context.logToken().info(tr("Liveness analysis."));

    context.setLivenesses(std::make_unique<ir::liveness::Livenesses>());

    foreach (const ir::Function *function, context.functions()->list()) {
        livenessAnalysis(context, function);
    }
}

void MasterAnalyzer::livenessAnalysis(Context &context, const ir::Function *function) const {
    context.logToken().info(tr("Liveness analysis of %1.").arg(getFunctionName(context, function)));

    std::unique_ptr<ir::liveness::Liveness> liveness(new ir::liveness::Liveness());

    ir::liveness::LivenessAnalyzer(*liveness, function,
        *context.dataflows()->at(function), context.image()->platform().architecture(),
        context.graphs() ? context.graphs()->at(function).get() : nullptr, *context.hooks(),
        context.signatures(), context.logToken())
    .analyze();

    context.livenesses()->emplace(function, std::move(liveness));
}

void MasterAnalyzer::analyzeIdioms(Context &context) const {
    context.logToken().info(tr("Recovering semantic idioms."));

    auto idioms = std::make_unique<ir::idiom::Idioms>();
    foreach (const ir::Function *function, context.functions()->list()) {
        auto functionIdioms = std::make_unique<ir::idiom::FunctionIdioms>();
        ir::idiom::IdiomAnalyzer(
            *functionIdioms, function, *context.graphs()->at(function),
            *context.dataflows()->at(function),
            *context.livenesses()->at(function), context.cancellationToken())
            .analyze();
        idioms->emplace(function, std::move(functionIdioms));
        context.cancellationToken().poll();
    }

    context.setIdioms(std::move(idioms));
}

void MasterAnalyzer::reconstructTypes(Context &context) const {
    context.logToken().info(tr("Reconstructing types."));

    std::unique_ptr<ir::types::Types> types(new ir::types::Types());

    ir::types::TypeAnalyzer(
        *types, *context.functions(), *context.dataflows(), *context.variables(),
        *context.livenesses(), *context.hooks(), *context.signatures(),
        context.cancellationToken())
    .analyze();

    context.setTypes(std::move(types));
}

void MasterAnalyzer::structuralAnalysis(Context &context) const {
    context.logToken().info(tr("Structural analysis."));

    context.setGraphs(std::make_unique<ir::cflow::Graphs>());

    foreach (auto function, context.functions()->list()) {
        structuralAnalysis(context, function);
        context.cancellationToken().poll();
    }
}

void MasterAnalyzer::structuralAnalysis(Context &context, const ir::Function *function) const {
    context.logToken().info(tr("Structural analysis of %1.").arg(getFunctionName(context, function)));

    std::unique_ptr<ir::cflow::Graph> graph(new ir::cflow::Graph());

    ir::cflow::GraphBuilder()(*graph, function);
    const ir::dflow::Dataflow &dataflow =
        *context.dataflows()->at(function);
    ir::CFG cfg(function->basicBlocks());
    ir::Dominators dominators(
        cfg, context.cancellationToken(), function->entry());
    ir::PostDominators postdominators(
        cfg, context.cancellationToken());
    ir::dflow::DefUseGraph defUse(dataflow);
    ir::dflow::ValueProvenance provenance(
        dataflow, defUse, dominators, cfg);
    ir::dflow::ExpressionIdentity expressionIdentity(
        dataflow, defUse, provenance);
    ir::cflow::StructureAnalyzer(
        *graph, dataflow, defUse, provenance, expressionIdentity,
        postdominators).analyze();

    context.graphs()->emplace(function, std::move(graph));
}

void MasterAnalyzer::generateTree(Context &context) const {
    context.logToken().info(tr("Generating AST."));

    auto tree = std::make_unique<nc::core::likec::Tree>();

    ir::cgen::CodeGenerator(*tree, *context.image(), *context.functions(), *context.hooks(),
        *context.signatures(), *context.dataflows(), *context.variables(), *context.graphs(),
        *context.livenesses(), *context.idioms(), *context.types(),
        context.cancellationToken())
        .makeCompilationUnit();

    context.setTree(std::move(tree));
}

void MasterAnalyzer::decompile(Context &context) const {
    context.logToken().info(tr("Decompiling."));

    createProgram(context);
    context.cancellationToken().poll();

    auto discardPointerKeyedAnalysis = [&]() {
        /* Destroy dependants before the Function clones they reference. */
        discardFunctionProducts(context);
    };

    auto restorePristineProgram = [&]() {
        discardPointerKeyedAnalysis();
        /* Do not expose a partially refined Program if regeneration itself
         * fails (for example because cancellation was requested). */
        context.setProgram(nullptr);
        createProgram(context);
    };

    auto clearInferredSignatures = [&]() {
        context.signatures()->beginInferenceUpdate();
        try {
            context.signatures()->finishInferenceUpdate();
        } catch (...) {
            context.signatures()->cancelInferenceUpdate();
            throw;
        }
    };

    auto runDataflowAnalysis = [&]() {
        /* Invalidate before virtual dispatch as an override is not required
         * to call MasterAnalyzer::dataflowAnalysis(). */
        discardDataflowProducts(context);
        dataflowAnalysis(context);
    };

    /*
     * External contracts can refine function entries or control flow only
     * after the first converged dataflow pass. Rebuild every pointer-keyed
     * product from the stable Program when this happens. The final iteration
     * disables Program mutation, so the Functions used below always reflect
     * every refinement accepted by an earlier iteration.
     *
     * A hard bound prevents recursive or adversarial metadata from repeatedly
     * restarting whole-program analysis. One round normally finds all
     * refinements; sixteen rounds also cover every callback nesting level
     * accepted by the version-one declarative metadata schema.
     */
    const unsigned int maximumProgramRefinements = 16;
    const unsigned int maximumSemanticContractRefinements = 16;
    unsigned int programRefinements = 0;
    bool externalContractsDisabled = false;
    for (;;) {
        createFunctions(context);
        context.cancellationToken().poll();

        createHooks(context);
        context.cancellationToken().poll();

        detectCallingConventions(context);
        context.cancellationToken().poll();

        bool restartForProgramRefinement = false;
        bool reportedProgramRefinementLimit = false;
        unsigned int semanticContractRefinements = 0;
        bool programMutationArmed = false;
        for (;;) {
            /* A stable pass must start and finish with the same effective
             * signature and convention facts. Then its dataflow and liveness
             * products were computed under exactly the contracts retained
             * for subsequent phases. */
            const std::uint64_t signatureRevision =
                context.signatures()->revision();
            const std::uint64_t conventionRevision =
                context.conventions()->revision();

            runDataflowAnalysis();
            context.cancellationToken().poll();

            livenessAnalysis(context);
            context.cancellationToken().poll();

            reconstructSignatures(context);
            context.cancellationToken().poll();

            if (externalContractsDisabled) {
                const bool inferredFactsStable =
                    context.signatures()->revision() == signatureRevision &&
                    context.conventions()->revision() == conventionRevision;
                if (inferredFactsStable) {
                    break;
                }
                if (semanticContractRefinements >=
                        maximumSemanticContractRefinements) {
                    context.logToken().warning(tr(
                        "Inferred signature refinement limit reached; "
                        "continuing without derived signatures."));
                    clearInferredSignatures();
                    runDataflowAnalysis();
                    context.cancellationToken().poll();
                    livenessAnalysis(context);
                    context.cancellationToken().poll();
                    break;
                }
                ++semanticContractRefinements;
                continue;
            }

            const bool programRefinementAllowed =
                programRefinements < maximumProgramRefinements;
            const bool preExternalContractsStable =
                context.signatures()->revision() == signatureRevision &&
                context.conventions()->revision() == conventionRevision;
            const bool allowProgramMutation =
                programMutationArmed && preExternalContractsStable &&
                programRefinementAllowed;
            bool programRefinementRequired = false;
            context.signatures()->beginExternalUpdate();
            try {
                context.conventions()->beginExternalUpdate();
            } catch (...) {
                context.signatures()->cancelExternalUpdate();
                throw;
            }
            try {
                programRefinementRequired = applyExternalSignatures(
                    context, allowProgramMutation);
            } catch (...) {
                context.conventions()->cancelExternalUpdate();
                context.signatures()->cancelExternalUpdate();
                if (allowProgramMutation) {
                    try {
                        restorePristineProgram();
                    } catch (...) {
                        context.setProgram(nullptr);
                    }
                }
                throw;
            }
            try {
                /* Signature commit may structurally compare prototypes and
                 * allocate. Commit that half first; convention commit is
                 * allocation-free and noexcept. */
                context.signatures()->finishExternalUpdate();
            } catch (...) {
                context.conventions()->cancelExternalUpdate();
                context.signatures()->cancelExternalUpdate();
                if (allowProgramMutation) {
                    try {
                        restorePristineProgram();
                    } catch (...) {
                        context.setProgram(nullptr);
                    }
                }
                throw;
            }
            context.conventions()->finishExternalUpdate();
            try {
                context.cancellationToken().poll();
            } catch (...) {
                if (allowProgramMutation) {
                    try {
                        restorePristineProgram();
                    } catch (...) {
                        context.setProgram(nullptr);
                    }
                }
                throw;
            }

            const bool contractsStable =
                context.signatures()->revision() == signatureRevision &&
                context.conventions()->revision() == conventionRevision;

            if (allowProgramMutation && !contractsStable) {
                /* The preceding dry pass promised a stable contract
                 * snapshot. A provider which changes it only after mutation
                 * is enabled may already have changed Program, so abort
                 * instead of emitting results built from mixed revisions. */
                try {
                    restorePristineProgram();
                } catch (...) {
                    context.setProgram(nullptr);
                }
                throw std::logic_error(
                    "external contracts changed during an armed Program refinement");
            }

            if (programRefinementRequired && allowProgramMutation) {
                ++programRefinements;
                restartForProgramRefinement = true;
                break;
            }

            if (contractsStable) {
                if (!programRefinementRequired) {
                    break;
                }

                if (!programRefinementAllowed) {
                    if (!reportedProgramRefinementLimit) {
                        context.logToken().warning(tr(
                            "Program refinement limit reached; ignoring additional "
                            "late control-flow and function-entry refinements."));
                        reportedProgramRefinementLimit = true;
                    }
                    break;
                }

                /* Confirm the proof with a complete semantic pass under the
                 * same revisions. Only that pass may split functions or
                 * remove control-flow edges. */
                programMutationArmed = true;
                continue;
            }

            programMutationArmed = false;
            if (semanticContractRefinements >=
                    maximumSemanticContractRefinements) {
                context.logToken().warning(tr(
                    "Semantic contract refinement limit reached; continuing with "
                    "the last conservative contract snapshot."));

                /* Do not run another producer after the bound. Neither side
                 * of an oscillating external snapshot is known to be a safe
                 * meet: a contract can create the memory effects which make
                 * its own evidence disappear on the next pass. Drop both
                 * derived layers before the frozen pass, retaining only
                 * persistent target facts. This is conservative and makes
                 * the final dataflow and every downstream consumer observe
                 * one coherent contract set. */
                clearInferredSignatures();

                context.signatures()->beginExternalUpdate();
                try {
                    context.conventions()->beginExternalUpdate();
                } catch (...) {
                    context.signatures()->cancelExternalUpdate();
                    throw;
                }
                try {
                    context.signatures()->finishExternalUpdate();
                } catch (...) {
                    context.conventions()->cancelExternalUpdate();
                    context.signatures()->cancelExternalUpdate();
                    throw;
                }
                context.conventions()->finishExternalUpdate();

                /* A stable external proof may already have destructively
                 * refined Program in an earlier outer iteration. Registry
                 * rollback cannot restore such control-flow edges. Rebuild
                 * pristine IR from the decoded instructions and restart all
                 * pointer-keyed products with external producers disabled. */
                restorePristineProgram();
                try {
                    context.cancellationToken().poll();
                } catch (...) {
                    /* restorePristineProgram already invalidated every
                     * old-Program pointer. Do not leave a partially useful
                     * context after cancellation at this boundary. */
                    context.setProgram(nullptr);
                    throw;
                }
                externalContractsDisabled = true;
                restartForProgramRefinement = true;
                break;
            }
            ++semanticContractRefinements;
        }

        if (!restartForProgramRefinement) {
            break;
        }

        discardPointerKeyedAnalysis();
    }

    reconstructVariables(context);
    context.cancellationToken().poll();

    structuralAnalysis(context);
    context.cancellationToken().poll();

    livenessAnalysis(context);
    context.cancellationToken().poll();

    analyzeIdioms(context);
    context.cancellationToken().poll();

    reconstructTypes(context);
    context.cancellationToken().poll();

    generateTree(context);
    context.cancellationToken().poll();

    context.logToken().info(tr("Decompilation completed."));
}

QString MasterAnalyzer::getFunctionName(Context &context, const ir::Function *function) const {
    return ir::cgen::NameGenerator(*context.image()).getFunctionName(function).name();
}

} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
