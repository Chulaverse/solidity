/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

#include <libyul/backends/evm/SSAEVMCodeTransform.h>

#include <libyul/backends/evm/SSAControlFlowGraphBuilder.h>

#include <libsolutil/StringUtils.h>
#include <libsolutil/Visitor.h>

#include <libevmasm/Instruction.h>

#include <range/v3/range/conversion.hpp>
#include <range/v3/view/zip.hpp>

using namespace solidity;
using namespace solidity::yul;

namespace
{

std::string ssaCfgVarToString(SSACFG const& _ssacfg, SSACFG::ValueId _var)
{
	if (_var.value == std::numeric_limits<size_t>::max())
		return std::string("INVALID");
	auto const& info = _ssacfg.valueInfo(_var);
	return std::visit(
		util::GenericVisitor{
			[&](SSACFG::UnreachableValue const&) -> std::string {
				return "[unreachable]";
			},
			[&](SSACFG::LiteralValue const& _literal) {
				std::stringstream str;
				str << _literal.value;
				return str.str();
			},
			[&](auto const&) {
				return "v" + std::to_string(_var.value);
			}
		},
		info
	);
}

}

std::vector<StackTooDeepError> SSAEVMCodeTransform::run(
	AbstractAssembly& _assembly,
	AsmAnalysisInfo& _analysisInfo,
	Block const& _block,
	EVMDialect const& _dialect,
	BuiltinContext& _builtinContext,
	UseNamedLabels _useNamedLabelsForFunctions
)
{
	std::unique_ptr<ControlFlow> controlFlow = SSAControlFlowGraphBuilder::build(_analysisInfo, _dialect, _block);

	SSACFGLiveness liveness(*controlFlow->mainGraph);
	SSAEVMCodeTransform mainCodeTransform(
		_assembly,
		_builtinContext,
		_useNamedLabelsForFunctions,
		*controlFlow->mainGraph,
		liveness
	);

	// Force main entry block to start from an empty stack.
	mainCodeTransform.blockData(SSACFG::BlockId{0}).stackIn = std::make_optional(std::vector<StackSlot>{});
	mainCodeTransform(SSACFG::BlockId{0});

	std::vector<StackTooDeepError> stackErrors;
	if (!mainCodeTransform.m_stackErrors.empty())
		stackErrors = std::move(mainCodeTransform.m_stackErrors);

	for (auto const& [function, functionGraph]: controlFlow->functionGraphMapping)
	{
		SSACFGLiveness functionLiveness(*functionGraph);
		SSAEVMCodeTransform functionCodeTransform(
			_assembly,
			_builtinContext,
			_useNamedLabelsForFunctions,
			*functionGraph,
			functionLiveness
		);
		functionCodeTransform(*function, *functionGraph);
		if (!functionCodeTransform.m_stackErrors.empty())
			stackErrors.insert(stackErrors.end(), functionCodeTransform.m_stackErrors.begin(), functionCodeTransform.m_stackErrors.end());
	}

	return stackErrors;
}

SSAEVMCodeTransform::SSAEVMCodeTransform(
	AbstractAssembly& _assembly,
	BuiltinContext& _builtinContext,
	UseNamedLabels _useNamedLabelsForFunctions,
	SSACFG const& _cfg,
	SSACFGLiveness const& _liveness
):
	m_assembly(_assembly),
	m_builtinContext(_builtinContext),
	m_cfg(_cfg),
	m_liveness(_liveness),
	m_functionLabels([&](){
		std::map<Scope::Function const*, AbstractAssembly::LabelID> functionLabels;

		if (_cfg.function)
		{
			std::set<YulString> assignedFunctionNames;
			bool nameAlreadySeen = !assignedFunctionNames.insert(_cfg.function->name).second;
			if (_useNamedLabelsForFunctions == UseNamedLabels::YesAndForceUnique)
				yulAssert(!nameAlreadySeen);
			bool useNamedLabel = _useNamedLabelsForFunctions != UseNamedLabels::Never && !nameAlreadySeen;
			functionLabels[_cfg.function] = useNamedLabel ?
				m_assembly.namedLabel(
					_cfg.function->name.str(),
					_cfg.arguments.size(),
					_cfg.returns.size(),
					_cfg.debugData ? _cfg.debugData->astID : std::nullopt
				) :
				m_assembly.newLabelId();
		}
		return functionLabels;
	}()),
	m_blockData(_cfg.numBlocks())
{
}

AbstractAssembly::LabelID SSAEVMCodeTransform::getFunctionLabel(Scope::Function const& _function)
{
	return m_functionLabels.at(&_function);
}

void SSAEVMCodeTransform::pop()
{
	yulAssert(!m_stack.empty());
	m_stack.pop_back();
	m_assembly.appendInstruction(evmasm::Instruction::POP);
}

void SSAEVMCodeTransform::swap(size_t _depth)
{
	m_assembly.appendInstruction(evmasm::swapInstruction(static_cast<unsigned>(_depth)));
	yulAssert(m_stack.size() > _depth);
	std::swap(m_stack[m_stack.size() - _depth - 1], m_stack.back());
}

void SSAEVMCodeTransform::operator()(SSACFG::BlockId _block)
{
	{
		// TODO: remove - only used for debugging
		m_currentBlock = _block;
	}

	ScopedSaveAndRestore stackSave{m_stack, {}};

	{
		auto& label = blockData(_block).label;
		if (!label)
			label = m_assembly.newLabelId();
		m_assembly.appendLabel(*label);
	}

	{
		auto& stackIn = blockData(_block).stackIn;
		yulAssert(stackIn, "No starting layout for block b" + std::to_string(_block.value));
		// if (!stackIn)
		//	stackIn = liveness(_block).liveIn | ranges::to<std::vector<StackSlot>>;
		m_stack = *stackIn | ranges::to<std::vector<StackSlot>>;
	}
	m_assembly.setStackHeight(static_cast<int>(m_stack.size()));
	std::cout << "Generate block b" << _block.value << ": " << stackToString(m_stack) << std::endl;

	yulAssert(m_cfg.block(_block).operations.size() == m_liveness.operationsLiveOut(_block).size());
	for (auto&& [op, liveOut]: ranges::zip_view(m_cfg.block(_block).operations, m_liveness.operationsLiveOut(_block)))
		(*this)(op, liveOut);
}

void SSAEVMCodeTransform::operator()(SSACFG::Operation const& _operation, std::set<SSACFG::ValueId> const& _liveOut)
{
	// todo
}

void SSAEVMCodeTransform::operator()(Scope::Function const& _function, SSACFG const& _functionGraph)
{
	// todo
}

void SSAEVMCodeTransform::createStackTop(
	std::vector<StackSlot> const& _targetTop,
	std::set<SSACFG::ValueId> const& _liveOut
)
{
	// todo
}

void SSAEVMCodeTransform::bringUpSlot(StackSlot const& _slot)
{
	// todo
}

void SSAEVMCodeTransform::createExactStack(std::vector<StackSlot> const& _target)
{
	// todo
}

std::string SSAEVMCodeTransform::stackToString(std::vector<StackSlot> const& _stack)
{
	return "[" + util::joinHumanReadable(_stack | ranges::views::transform([&](StackSlot const& _slot) { return stackSlotToString(_slot); })) + "]";
}

std::string SSAEVMCodeTransform::stackSlotToString(StackSlot const& _slot)
{
	return std::visit(util::GenericVisitor{
		[&](SSACFG::ValueId _value) {
			return ssaCfgVarToString(m_cfg, _value);
		},
		[](AbstractAssembly::LabelID _label) {
			return "LABEL[" + std::to_string(_label) + "]";
		}
	}, _slot);
}
