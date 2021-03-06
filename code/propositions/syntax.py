# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulae."""

from __future__ import annotations
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen

PREFIX_ERR_MSG = 'Not a valid prefix of a formula'

IMPLIES = '->'

OR = '|'

R_BRACK = ')'

L_BRACK = '('

NEG = '~'


def is_variable(s: str) -> bool:
    """Checks if the given string is an atomic proposition.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is an atomic proposition, ``False``
        otherwise.
    """
    return s[0] >= 'p' and s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())


def is_constant(s: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return s == 'T' or s == 'F'


def is_unary(s: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return s == '~'


def is_binary(s: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    # return s == '&' or s == '|' or s == '->'
    # For Chapter 3:
    return s in {'&', '|', '->', '+', '<->', '-&', '-|'}


@frozen
class Formula:
    """An immutable propositional formula in tree representation.

    Attributes:
        root (`str`): the constant, atomic proposition, or operator at the root
            of the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand to the
            root, if the root is a binary operator.
    """
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None) -> None:
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand to the root, if the root is a unary or
                binary operator.
            second: the second operand to the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root) and type(first) is Formula and \
                   type(second) is Formula
            self.root, self.first, self.second = root, first, second

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            does not equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 1.1
        if is_variable(self.root):
            return self.root
        elif is_constant(self.root):
            return self.root
        elif is_unary(self.root):
            return NEG + str(self.first)
        elif is_binary(self.root):
            return L_BRACK + str(self.first) + self.root + str(self.second) + R_BRACK

    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current formula.

        Returns:
            A set of all atomic propositions used in the current formula.
        """
        # Task 1.2
        if is_variable(self.root):
            return {self.root}
        elif is_constant(self.root):
            return set()
        elif is_unary(self.root):
            return self.first.variables()
        elif is_binary(self.root):
            return set.union(self.first.variables(), self.second.variables())

    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3
        if is_variable(self.root):
            return set()
        elif is_constant(self.root):
            return {self.root}
        elif is_unary(self.root):
            return set.union({self.root}, self.first.operators())
        elif is_binary(self.root):
            return set.union({self.root}, self.first.operators(), self.second.operators())

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the first token of the string is a variable name (e.g.,
            ``'x12'``), then the parsed prefix will be that entire variable name
            (and not just a part of it, such as ``'x1'``). If no prefix of the
            given string is a valid standard string representation of a formula
            then returned pair should be of ``None`` and an error message, where
            the error message is a string with some human-readable content.
        """
        # Task 1.4

        # Base case
        if s == '':
            return None, PREFIX_ERR_MSG
        elif len(s) == 1:
            return (Formula(s), '') if ('p' <= s <= 'z' or is_constant(s)) else (None, PREFIX_ERR_MSG)
        elif 'p' <= s[0] <= 'z':
            i = 1
            while (i < len(s)) and ('0' <= s[i] <= '9'):
                i += 1
            return Formula(s[:i]), s[i:]
        elif is_constant(s[0]):
            return Formula(s[0]), s[1:]

        # Induction
        elif is_unary(s[0]):
            ff, rr = Formula.parse_prefix(s[1:])
            if ff is None:
                return None, PREFIX_ERR_MSG
            else:
                return Formula(s[0], ff), rr
        elif s[0] == L_BRACK:
            # ff and ff2 are the left and right hand sides of the formula, respectively
            ff, rr = Formula.parse_prefix(s[1:])
            if len(rr) < 1:
                return None, PREFIX_ERR_MSG
            else:
                if is_binary(rr[0]):
                    end_len = 1
                elif len(rr) >= 2:
                    if is_binary(rr[0:2]):
                        end_len = 2
                    elif is_binary(rr[0:3]):
                        end_len = 3
                    else:
                        return None, PREFIX_ERR_MSG
                else:
                    return None, PREFIX_ERR_MSG
                ff2, rr2 = Formula.parse_prefix(rr[end_len:])
                if ff2 is None:
                    return None, PREFIX_ERR_MSG
                else:
                    if len(rr2) > 0 and rr2[0] == R_BRACK:
                        rr2 = rr2[1:]
                    else:
                        return None, PREFIX_ERR_MSG
                    return Formula(rr[0:end_len], ff, ff2), rr2
        else:
            return None, PREFIX_ERR_MSG

    @staticmethod
    def is_formula(s: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            s: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # Task 1.5
        ff, rr = Formula.parse_prefix(s)
        return rr == ''

    @staticmethod
    def parse(s: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(s)
        # Task 1.6
        ff, rr = Formula.parse_prefix(s)
        return ff

    # Optional tasks for Chapter 1

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

    @staticmethod
    def parse_polish(s: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

    # Tasks for Chapter 3

    def substitute_variables(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each variable `v` that is a key
        in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.

        Returns:
            The resulting formula.

        Examples:
            >>> Formula.parse('((p->p)|z)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)')})
            (((q&r)->(q&r))|z)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3
        if is_variable(self.root):
            if self.root in substitution_map.keys():
                return substitution_map[self.root]
            else:
                return self
        elif is_unary(self.root):
            return Formula(self.root, self.first.substitute_variables(substitution_map))
        elif is_binary(self.root):
            l_formula = self.first.substitute_variables(substitution_map)
            r_formula = self.second.substitute_variables(substitution_map)
            return Formula(self.root, l_formula, r_formula)
        else:
            return self

    def substitute_operators(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.

        Returns:
            The resulting formula.

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_binary(operator) or is_unary(operator) or \
                   is_constant(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4
        if is_variable(self.root):
            return self
        elif is_constant(self.root):
            if self.root in substitution_map.keys():
                return substitution_map[self.root]
            else:
                return self
        else:
            l_formula = self.first.substitute_operators(substitution_map)
            r_formula = None if is_unary(self.root) else self.second.substitute_operators(substitution_map)
            if self.root in substitution_map.keys():
                sub_dict = {'p': l_formula, 'q': r_formula}
                return substitution_map[self.root].substitute_variables(sub_dict)
            else:
                return Formula(self.root, l_formula, r_formula)
