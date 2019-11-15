# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""
import itertools
from typing import AbstractSet, Iterable, Iterator, List, Mapping

from propositions.syntax import *
from propositions.proofs import *

NOT_OP = '~'
NOR_OP = '-|'
NAND_OP = '-&'
IFF_OP = '<->'
XOR_OP = '+'
IMPLY_OP = '->'
OR_OP = '|'
AND_OP = '&'
F_OP = 'F'
T_OP = 'T'

PIPE = '|'

Model = Mapping[str, bool]


def is_model(model: Model) -> bool:
    """Checks if the given dictionary a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not (is_variable(key) and type(model[key]) is bool):
            return False
    return True


def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()


def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1
    root = formula.root
    if is_constant(root):
        return root == 'T'
    elif is_variable(root):
        return model[root]
    elif is_unary(root):
        return not evaluate(formula.first, model)
    elif is_binary(root):
        res_l = evaluate(formula.first, model)
        res_r = evaluate(formula.second, model)

        if root == AND_OP:
            return res_l and res_r
        elif root == OR_OP:
            return res_l or res_r
        elif root == IMPLY_OP:
            return not res_l or res_r
        elif root == XOR_OP:
            return (res_l and not res_r) or (not res_l and res_r)
        elif root == IFF_OP:
            return (not res_l and not res_r) or (res_l and res_r)
        elif root == NAND_OP:
            return not (res_l and res_r)
        elif root == NOR_OP:
            return not (res_l or res_r)


def all_models(variables: List[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: list of variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]
    """
    perm_iter = itertools.product([False, True], repeat=len(variables))
    for perm in perm_iter:
        yield dict(zip(variables, perm))


def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.
    """
    # Task 2.3
    for model in models:
        yield evaluate(formula, model)


def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4
    __print_header(formula)
    __print_body(formula)


def __print_body(formula):
    vars = list(formula.variables())
    vars.sort()
    models = all_models(vars)
    for model in models:
        print(PIPE, end='')
        for var in vars:
            print(' {}{} |'.format(str(model[var])[0], ' ' * (len(var) - 1)), end='')
        eval = evaluate(formula, model)
        print(' {}{} |'.format(str(eval)[0], ' ' * (len(repr(formula)) - 1)))


def __print_header(formula):
    print(PIPE, end='')
    vars = list(formula.variables())
    vars.sort()
    for var in vars:
        print(' {} |'.format(var), end='')
    print(' {} |'.format(repr(formula)))
    print(PIPE, end='')
    for var in vars:
        print('-{}-|'.format('-' * len(var)), end='')
    print('-{}-|'.format('-' * len(repr(formula))))


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a
    for val in truth_values(formula, all_models(formula.variables())):
        if val is False:
            return False
    else:
        return True


def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    for val in truth_values(formula, all_models(formula.variables())):
        if val is True:
            return False
    else:
        return True


def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c
    return not is_contradiction(formula)


def synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single clause that
      evaluates to ``True`` in the given model, and to ``False`` in any other
      model over the same variables.

    Parameters:
        model: model in which the synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    # Task 2.6
    items = list(model.items())
    return __synthesize_model_helper(items, 0)


def __synthesize_model_helper(items, idx):
    var, val = items[idx]
    if idx == len(items) - 1:
        return Formula(var) if val else Formula('~', Formula(var))
    else:
        return Formula('&', Formula(var) if val else Formula('~', Formula(var)),
                       __synthesize_model_helper(items, idx + 1))


def synthesize(variables: List[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables, from
    the given specification of which value the formula should have on each
    possible model over these variables.

    Parameters:
        variables: the set of variables for the synthesize formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7
    models = list(itertools.compress(all_models(variables), values))
    if len(models) == 0:
        formula = Formula(variables[0])
        return Formula('&', formula, Formula('~', formula))
    else:
        return __synthesize_helper(0, models)


def __synthesize_helper(i, models):
    formula = synthesize_for_model(models[i])
    if i == len(models) - 1:
        return formula
    else:
        return Formula('|', formula, __synthesize_helper(i + 1, models))


# Tasks for Chapter 4


def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.
    """
    assert is_model(model)
    # Task 4.2
    for assumption in rule.assumptions:
        if not evaluate(assumption, model):
            return True
    else:
        return evaluate(rule.conclusion, model)


def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
    for model in all_models(rule.variables()):
        if not evaluate_inference(rule, model):
            return False
    else:
        return True
