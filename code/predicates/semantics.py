# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/semantics.py

"""Semantic analysis of first-order logic constructs."""
import functools
import itertools
from typing import AbstractSet, FrozenSet, Generic, Mapping, Tuple, TypeVar

from logic_utils import frozen, frozendict

from predicates.syntax import *

#: A generic type for a universe element in a model.
T = TypeVar('T')


@frozen
class Model(Generic[T]):
	"""An immutable model for first-order logic constructs.

	Attributes:
		universe (`~typing.FrozenSet`\\[`T`]): the set of elements to which
			terms can be evaluated and over which quantifications are defined.
		constant_meanings (`~typing.Mapping`\\[`str`, `T`]): mapping from each
			constant name to the universe element to which it evaluates.
		relation_arities (`~typing.Mapping`\\[`str`, `int`]): mapping from
			each relation name to the arity of the relation, or to ``-1`` if the
			relation is the empty relation.
		relation_meanings (`~typing.Mapping`\\[`str`, `~typing.AbstractSet`\\[`~typing.Tuple`\\[`T`, ...]]]):
			mapping from each n-ary relation name to argument n-tuples (of
			universe elements) for which the relation is true.
		function_arities (`~typing.Mapping`\\[`str`, `int`]): mapping from
			each function name to the arity of the function.
		function_meanings (`~typing.Mapping`\\[`str`, `~typing.Mapping`\\[`~typing.Tuple`\\[`T`, ...], `T`]]):
			mapping from each n-ary function name to the mapping from each
			argument n-tuple (of universe elements) to the universe element that
			the function outputs given these arguments.
	"""
	universe: FrozenSet[T]
	constant_meanings: Mapping[str, T]
	relation_arities: Mapping[str, int]
	relation_meanings: Mapping[str, AbstractSet[Tuple[T, ...]]]
	function_arities: Mapping[str, int]
	function_meanings: Mapping[str, Mapping[Tuple[T, ...], T]]


	def __init__(self, universe: AbstractSet[T],
				 constant_meanings: Mapping[str, T],
				 relation_meanings: Mapping[str, AbstractSet[Tuple[T, ...]]],
				 function_meanings: Mapping[str, Mapping[Tuple[T, ...], T]] =
				 frozendict()) -> None:
		"""Initializes a `Model` from its universe and constant, relation, and
		function meanings.

		Parameters:
			universe: the set of elements to which terms are to be evaluated
				and over which quantifications are to be defined.
			constant_meanings: mapping from each constant name to a universe
				element to which it is to be evaluated.
			relation_meanings: mapping from each relation name that is to
				be the name of an n-ary relation, to the argument n-tuples (of
				universe elements) for which the relation is to be true.
			function_meanings: mapping from each function name that is to
				be the name of an n-ary function, to a mapping from each
				argument n-tuple (of universe elements) to a universe element
				that the function is to output given these arguments.
		"""
		self.universe = frozenset(universe)

		for constant in constant_meanings:
			assert is_constant(constant)
			assert constant_meanings[constant] in universe
		self.constant_meanings = frozendict(constant_meanings)

		relation_arities = {}
		for relation in relation_meanings:
			assert is_relation(relation)
			relation_meaning = relation_meanings[relation]
			if len(relation_meaning) == 0:
				arity = -1  # any
			else:
				some_arguments = next(iter(relation_meaning))
				arity = len(some_arguments)
				for arguments in relation_meaning:
					assert len(arguments) == arity
					for argument in arguments:
						assert argument in universe
			relation_arities[relation] = arity
		self.relation_meanings = \
			frozendict({relation: frozenset(relation_meanings[relation]) for
						relation in relation_meanings})
		self.relation_arities = frozendict(relation_arities)

		function_arities = {}
		for function in function_meanings:
			assert is_function(function)
			function_meaning = function_meanings[function]
			assert len(function_meaning) > 0
			some_argument = next(iter(function_meaning))
			arity = len(some_argument)
			assert arity > 0
			assert len(function_meaning) == len(universe) ** arity
			for arguments in function_meaning:
				assert len(arguments) == arity
				for argument in arguments:
					assert argument in universe
				assert function_meaning[arguments] in universe
			function_arities[function] = arity
		self.function_meanings = \
			frozendict({function: frozendict(function_meanings[function]) for
						function in function_meanings})
		self.function_arities = frozendict(function_arities)


	def __repr__(self) -> str:
		"""Computes a string representation of the current model.

		Returns:
			A string representation of the current model.
		"""
		return 'Universe=' + str(self.universe) + '; Constant Meanings=' + \
			   str(self.constant_meanings) + '; Relation Meanings=' + \
			   str(self.relation_meanings) + \
			   ('; Function Meanings=' + str(self.function_meanings)
				if len(self.function_meanings) > 0 else '')


	def evaluate_term(self, term: Term,
					  assignment: Mapping[str, T] = frozendict()) -> T:
		"""Calculates the value of the given term in the current model, for the
		given assignment of values to variables names.

		Parameters:
			term: term to calculate the value of, for the constants and
				functions of which the current model has meanings.
			assignment: mapping from each variable name in the given term to a
				universe element to which it is to be evaluated.

		Returns:
			The value (in the universe of the current model) of the given
			term in the current model, for the given assignment of values to
			variable names.
		"""
		assert term.constants().issubset(self.constant_meanings.keys())
		assert term.variables().issubset(assignment.keys())
		for function, arity in term.functions():
			assert function in self.function_meanings and \
				   self.function_arities[function] == arity
			# Task 7.7
		return self._evaluate_term_helper(term, assignment)

	def _evaluate_term_helper(self, term: Term,
					  assignment: Mapping[str, T] = frozendict()) -> T:
		if is_variable(term.root):
			return assignment[term.root]
		elif is_constant(term.root):
			return self.constant_meanings[term.root]
		elif is_function(term.root):
			mapping = self.function_meanings[term.root]
			key = tuple([self._evaluate_term_helper(term, assignment) for term in term.arguments])
			return mapping[key]


	def evaluate_formula(self, formula: Formula,
						 assignment: Mapping[str, T] = frozendict()) -> bool:
		"""Calculates the truth value of the given formula in the current model,
		for the given assignment of values to free occurrences of variables
		names.

		Parameters:
			formula: formula to calculate the truth value of, for the constants,
				functions, and relations of which the current model has
				meanings.
			assignment: mapping from each variable name that has a free
				occurrence in the given formula to a universe element to which
				it is to be evaluated.

		Returns:
			The truth value of the given formula in the current model, for the
			given assignment of values to free occurrences of variable names.
		"""
		assert formula.constants().issubset(self.constant_meanings.keys())
		assert formula.free_variables().issubset(assignment.keys())
		for function, arity in formula.functions():
			assert function in self.function_meanings and \
				   self.function_arities[function] == arity
		for relation, arity in formula.relations():
			assert relation in self.relation_meanings and \
				   self.relation_arities[relation] in {-1, arity}
		# Task 7.8
		return self._evaluate_formula_helper(formula, assignment)

	def _evaluate_formula_helper(self, formula: Formula,
						 assignment: Mapping[str, T] = frozendict()) -> bool:

		if is_equality(formula.root):
			l_eval = self.evaluate_term(formula.arguments[0], assignment)
			r_eval = self.evaluate_term(formula.arguments[1], assignment)
			return l_eval == r_eval
		elif is_relation(formula.root):
			subset = tuple([self.evaluate_term(term, assignment) for term in formula.arguments])
			return subset in self.relation_meanings[formula.root]
		elif is_unary(formula.root):
			return not self._evaluate_formula_helper(formula.first, assignment)
		elif is_binary(formula.root):
			l_eval = self._evaluate_formula_helper(formula.first, assignment)
			r_eval = self._evaluate_formula_helper(formula.second, assignment)
			if formula.root == '&':
				return l_eval and r_eval
			elif formula.root == '|':
				return l_eval or r_eval
			elif formula.root == '->':
				return (not l_eval) or r_eval
		elif is_quantifier(formula.root):
			if formula.root == 'A':
				predicate_func = lambda a, b: a and b
			elif formula.root == 'E':
				predicate_func = lambda a, b: a or b
			results = []
			for elem in self.universe:
				curr_assign = dict(assignment)
				curr_assign[formula.variable] = elem
				results.append(self._evaluate_formula_helper(formula.predicate, curr_assign))
			return functools.reduce(predicate_func, results)


	def is_model_of(self, formulas: AbstractSet[Formula]) -> bool:
		"""Checks if the current model is a model for the given formulas.

		Returns:
			``True`` if each of the given formulas evaluates to true in the
			current model for any assignment of elements from the universe of
			the current model to the free occurrences of variables in that
			formula, ``False`` otherwise.
		"""
		for formula in formulas:
			assert formula.constants().issubset(self.constant_meanings.keys())
			for function, arity in formula.functions():
				assert function in self.function_meanings and \
					   self.function_arities[function] == arity
			for relation, arity in formula.relations():
				assert relation in self.relation_meanings and \
					   self.relation_arities[relation] in {-1, arity}
		# Task 7.9
		validity_results = [self._is_model_of_specific(formula) for formula in formulas]
		is_model_valid = functools.reduce(lambda a, b: a and b, validity_results)
		if not is_model_valid:
			return False
		else:
			results = [self._evaluate_formula_all_assignments(formula) for formula in formulas]
			return functools.reduce(lambda a, b: a and b, results)


	def _evaluate_formula_all_assignments(self, formula):
		free_variables = formula.free_variables()
		perm_iter = itertools.product(list(self.universe), repeat=len(free_variables))
		all_assignments = [dict(zip(free_variables, perm)) for perm in perm_iter]
		evaluations = [self.evaluate_formula(formula, assignment) for assignment in all_assignments]
		return functools.reduce(lambda a, b: a and b, evaluations)


	def _is_model_of_specific(self, formula):
		res = self._check_constants(formula.constants()) and self._check_functions(
			formula.functions()) and self._check_relations(formula.relations())
		return res


	def _check_constants(self, constants):
		return constants.issubset(set(self.constant_meanings.keys()))


	def _check_functions(self, functions):
		names, arities = set([name for name, _ in functions]), set([arity for _, arity in functions])
		names_validity = names.issubset(set(self.function_meanings.keys()))

		arity_validity = True
		for name, arity in functions:
			if not arity == self.function_arities[name]:
				return False

		return names_validity


	def _check_relations(self, relations):
		names, arities = set([name for name, _ in relations]), set([arity for _, arity in relations])
		names_validity = names.issubset(set(self.relation_meanings.keys()))
        #
		# for name, arity in relations:
		# 	if not arity == self.relation_arities[name]:
		# 		return False

		return names_validity
