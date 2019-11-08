# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulae to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *


def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5
    p, q = Formula('p'), Formula('q')
    sub_map = dict()
    sub_map[NAND_OP] = Formula(NOT_OP, Formula(AND_OP, p, q))
    sub_map[NOR_OP] = Formula(NOT_OP, Formula(OR_OP, p, q))

    xor_1 = Formula(AND_OP, Formula(NOT_OP, p), q)
    xor_2 = Formula(AND_OP, p, Formula(NOT_OP, q))
    sub_map[XOR_OP] = Formula(OR_OP, xor_1, xor_2)

    iff_1 = Formula(AND_OP, p, q)
    iff_2 = Formula(AND_OP, Formula(NOT_OP, p), Formula(NOT_OP, q))
    sub_map[IFF_OP] = Formula(OR_OP, iff_1, iff_2)

    implies_1 = Formula(NOT_OP, p)
    sub_map[IMPLIES] = Formula(OR_OP, implies_1, q)

    sub_map[F_OP] = Formula(AND_OP, p, Formula(NOT_OP, p))
    sub_map[T_OP] = Formula(OR_OP, p, Formula(NOT_OP, p))
    return formula.substitute_operators(sub_map)


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
