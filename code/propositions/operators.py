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
    p, q = Formula('p'), Formula('q')
    sub_map = dict()

    nand_1 = Formula(AND_OP, p, q)
    sub_map[NAND_OP] = Formula(NOT_OP, nand_1)

    iff_3 = Formula(AND_OP, Formula(NOT_OP, p), Formula(NOT_OP, q))
    iff_2 = Formula(AND_OP, p, q)
    iff_1 = Formula(AND_OP, Formula(NOT_OP, iff_2), Formula(NOT_OP, iff_3))
    sub_map[IFF_OP] = Formula(NOT_OP, iff_1)

    xor_5 = Formula(AND_OP, Formula(NOT_OP, p), q)
    xor_4 = Formula(AND_OP, p, Formula(NOT_OP, q))
    xor_3 = Formula(NOT_OP, xor_5)
    xor_2 = Formula(NOT_OP, xor_4)
    xor_1 = Formula(AND_OP, xor_2, xor_3)
    sub_map[XOR_OP] = Formula(NOT_OP, xor_1)

    nor_2 = Formula(NOT_OP, q)
    nor_1 = Formula(NOT_OP, p)
    sub_map[NOR_OP] = Formula(AND_OP, nor_1, nor_2)

    or_3 = Formula(NOT_OP, q)
    or_2 = Formula(NOT_OP, p)
    or_1 = Formula(AND_OP, or_2, or_3)
    sub_map[OR_OP] = Formula(NOT_OP, or_1)

    f_2 = Formula(NOT_OP, p)
    f_1 = p
    sub_map[F_OP] = Formula(AND_OP, f_1, f_2)

    t_1 = Formula(AND_OP, p, Formula(NOT_OP, p))
    sub_map[T_OP] = Formula(NOT_OP, t_1)

    imply_3 = q
    imply_2 = Formula(NOT_OP, p)
    imply_1 = Formula(AND_OP, Formula(NOT_OP, imply_2), Formula(NOT_OP, imply_3))
    sub_map[IMPLY_OP] = Formula(NOT_OP, imply_1)

    return formula.substitute_operators(sub_map)


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
    p, q = Formula('p'), Formula('q')
    sub_map = dict()

    sub_map[NOT_OP] = Formula(NAND_OP, p, p)

    and_1 = Formula(NAND_OP, p, q)
    sub_map[AND_OP] = Formula(NAND_OP, and_1, and_1)

    formula = to_not_and(formula)
    return formula.substitute_operators(sub_map)


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
    p, q = Formula('p'), Formula('q')
    sub_dict = dict()

    and_3 = Formula(IMPLY_OP, p, Formula(NOT_OP, q))
    and_2 = Formula(IMPLY_OP, Formula(NOT_OP, p), q)
    and_1 = Formula(IMPLY_OP, and_2, and_3)
    sub_dict[AND_OP] = Formula(NOT_OP, and_1)

    formula = to_not_and(formula)
    return formula.substitute_operators(sub_dict)


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
    p, q, f = Formula('p'), Formula('q'), Formula(F_OP)
    sub_dict = dict()

    sub_dict[NOT_OP] = Formula(IMPLY_OP, p, f)

    formula = to_implies_not(formula)
    return formula.substitute_operators(sub_dict)
