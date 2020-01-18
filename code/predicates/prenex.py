# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for first-order predicate logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))


def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3.1
    if is_unary(formula.root):
        return is_quantifier_free(formula.first)
    elif is_binary(formula.root):
        return is_quantifier_free(formula.first) and is_quantifier_free(formula.second)
    elif is_relation(formula.root) or is_equality(formula.root):
        return True
    elif is_quantifier(formula.root):
        return False


def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3.2

    if not is_quantifier(formula.root):
        return is_quantifier_free(formula)
    else:
        return is_in_prenex_normal_form(formula.predicate)


def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))


def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both quantified
        and free occurrences or is quantified by more than one quantifier,
        ``True`` otherwise.
    """
    forbidden_variables = set(formula.free_variables())

    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)


def uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.5

    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

    if is_quantifier(formula.root):
        orig_pred_formula, pred_proof = uniquely_rename_quantified_variables(formula.predicate)
        old_var = formula.variable
        fresh_var = next(fresh_variable_name_generator)
        pred_formula = orig_pred_formula.substitute({old_var: Term(fresh_var)})
        new_formula = Formula.parse(f'{formula.root}{fresh_var}[{pred_formula}]')
        s0 = prover.add_proof(pred_proof.conclusion, pred_proof)

        ante = pred_proof.lines[-1].formula
        cond = equivalence_of(formula, new_formula)
        f1 = f'({ante}->{cond})'
        axiom_i = 14 if formula.root == 'A' else 15
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_i]
        m1 = {'R': formula.predicate.substitute({old_var: Term('_')}),
              'Q': orig_pred_formula.substitute({old_var: Term('_')}),
              'x': old_var,
              'y': fresh_var}
        s1 = prover.add_instantiated_assumption(f1, axiom, m1)

        f2 = cond
        s2 = prover.add_mp(f2, s0, s1)


    elif is_unary(formula.root):
        first_formula, first_proof = uniquely_rename_quantified_variables(formula.first)
        new_formula = f'{formula.root}{first_formula}'
        s_first = prover.add_proof(first_proof.conclusion, first_proof)
        prover.add_tautological_implication(equivalence_of(formula, Formula.parse(new_formula)), {s_first})

    elif is_binary(formula.root):
        first_formula, first_proof = uniquely_rename_quantified_variables(formula.first)
        second_formula, second_proof = uniquely_rename_quantified_variables(formula.second)
        new_formula = f'({first_formula}{formula.root}{second_formula})'
        s_first = prover.add_proof(first_proof.conclusion, first_proof)
        s_second = prover.add_proof(second_proof.conclusion, second_proof)
        prover.add_tautological_implication(equivalence_of(formula, Formula.parse(new_formula)), {s_first, s_second})
    elif is_equality(formula.root) or is_relation(formula.root):
        new_formula = formula
        prover.add_tautology(equivalence_of(formula, formula))
        prover.add_tautology(equivalence_of(formula, new_formula))

    return Formula.parse(new_formula) if isinstance(new_formula, str) else new_formula, prover.qed()


def pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6
    orig_formula = formula

    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    if not is_quantifier(orig_formula.first.root):
        result_formula = orig_formula

        f0 = equivalence_of(orig_formula, result_formula)
        s0 = prover.add_tautology(f0)

        return result_formula, prover.qed()

    else:
        formula_without_neg = orig_formula.first
        orig_formula_quantifier = formula_without_neg.root
        flipped_formula_quantifier = 'E' if orig_formula_quantifier == 'A' else 'A'
        formula_var = formula_without_neg.variable
        negated_predicate = Formula.parse(f'~{formula_without_neg.predicate}')
        pulled_out_predicate, pulled_out_proof = pull_out_quantifications_across_negation(negated_predicate)
        result_formula = Formula.parse(f'{flipped_formula_quantifier}{formula_var}[{pulled_out_predicate}]')

        prev_proof_ln = prover.add_proof(pulled_out_proof.conclusion, pulled_out_proof)

        neg_pred = Formula.parse(f'~{formula_without_neg.predicate}')
        flipped_formula_with_neg_pred = Formula.parse(f'{flipped_formula_quantifier}{formula_var}[{neg_pred}]')
        ante = pulled_out_proof.conclusion
        cond = equivalence_of(flipped_formula_with_neg_pred, result_formula)
        f0 = Formula.parse(f'({ante}->{cond})')
        axiom_i = 14 if flipped_formula_quantifier == 'A' else 15
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_i]
        m0 = {'R': neg_pred.substitute({formula_var: Term('_')}),
              'Q': pulled_out_predicate.substitute({formula_var: Term('_')}),
              'x': formula_var,
              'y': formula_var}
        s0 = prover.add_instantiated_assumption(f0, axiom, m0)

        flipped_w_neg_eq_result = cond
        s_flipped_w_neg_eq_result = prover.add_mp(flipped_w_neg_eq_result, prev_proof_ln, s0)

        orig_eq_intermediate = equivalence_of(orig_formula, flipped_formula_with_neg_pred)
        axiom_i = 0 if orig_formula_quantifier == 'A' else 1
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_i]
        m2 = {'x': formula_var,
              'R': formula_without_neg.predicate.substitute({formula_var: Term('_')})}
        s_orig_eq_intermediate = prover.add_instantiated_assumption(orig_eq_intermediate, axiom, m2)

        orig_eq_result = equivalence_of(orig_formula, result_formula)
        s_final = prover.add_tautological_implication(orig_eq_result,
                                                      {s_flipped_w_neg_eq_result, s_orig_eq_intermediate})

        return result_formula, prover.qed()


def pull_out_quantifications_from_left_across_binary_operator(formula:
Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.1
    orig_formula = formula

    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    if not is_quantifier(orig_formula.first.root):
        result_formula = orig_formula

        f0 = equivalence_of(orig_formula, result_formula)
        s0 = prover.add_tautology(f0)

        return result_formula, prover.qed()

    else:
        orig_formula_op = orig_formula.root
        orig_formula_first = orig_formula.first
        orig_formula_second = orig_formula.second

        predicate_op_second = Formula.parse(f'({orig_formula_first.predicate}{orig_formula_op}{orig_formula_second})')
        orig_formula_quantifier = orig_formula_first.root
        flipped_formula_quantifier = 'E' if orig_formula_quantifier == 'A' else 'A'
        result_formula_quantifier = flipped_formula_quantifier if orig_formula_op == '->' else orig_formula_quantifier
        formula_var = orig_formula_first.variable

        pulled_out_predicate, pulled_out_proof = pull_out_quantifications_from_left_across_binary_operator(
            predicate_op_second)
        result_formula = Formula.parse(f'{result_formula_quantifier}{formula_var}[{pulled_out_predicate}]')

        prev_proof_ln = prover.add_proof(pulled_out_proof.conclusion, pulled_out_proof)

        # neg_pred = Formula.parse(f'~{formula_without_neg.predicate}')
        quan_w_pred_op_sec = Formula.parse(f'{result_formula_quantifier}{formula_var}[{predicate_op_second}]')
        ante = pulled_out_proof.conclusion
        cond = equivalence_of(quan_w_pred_op_sec, result_formula)
        f0 = Formula.parse(f'({ante}->{cond})')
        axiom_i = 14 if result_formula_quantifier == 'A' else 15
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_i]
        m0 = {'R': predicate_op_second.substitute({formula_var: Term('_')}),
              'Q': pulled_out_predicate.substitute({formula_var: Term('_')}),
              'x': formula_var,
              'y': formula_var}
        s0 = prover.add_instantiated_assumption(f0, axiom, m0)

        quan_w_pred_op_sec_EQ_result = cond
        s_quan_w_pred_op_sec_EQ_result = prover.add_mp(quan_w_pred_op_sec_EQ_result, prev_proof_ln, s0)

        orig_EQ_quan_w_pred_op_sec = equivalence_of(orig_formula, quan_w_pred_op_sec)
        axiom_i = _get_axiom_for_binary_and_quantifier_from_left(orig_formula_op, orig_formula_quantifier)
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_i]
        m2 = {'x': formula_var,
              'R': orig_formula_first.predicate.substitute({formula_var: Term('_')}),
              'Q': orig_formula_second}
        s_orig_EQ_quan_w_pred_op_sec = prover.add_instantiated_assumption(orig_EQ_quan_w_pred_op_sec, axiom, m2)

        orig_eq_result = equivalence_of(orig_formula, result_formula)
        s_final = prover.add_tautological_implication(orig_eq_result,
                                                      {s_quan_w_pred_op_sec_EQ_result, s_orig_EQ_quan_w_pred_op_sec})

        return result_formula, prover.qed()


def _get_axiom_for_binary_and_quantifier_from_left(binary_op, quantifier):
    if quantifier == 'A':
        if binary_op == '&':
            return 2
        elif binary_op == '|':
            return 6
        elif binary_op == '->':
            return 10
    elif quantifier == 'E':
        if binary_op == '&':
            return 3
        elif binary_op == '|':
            return 7
        elif binary_op == '->':
            return 11


def pull_out_quantifications_from_right_across_binary_operator(formula:
Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.2

    orig_formula = formula

    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    if not is_quantifier(orig_formula.second.root):
        result_formula = orig_formula

        f0 = equivalence_of(orig_formula, result_formula)
        s0 = prover.add_tautology(f0)

        return result_formula, prover.qed()

    else:
        orig_formula_op = orig_formula.root
        orig_formula_first = orig_formula.first
        orig_formula_second = orig_formula.second

        first_op_predicate = Formula.parse(f'({orig_formula_first}{orig_formula_op}{orig_formula_second.predicate})')
        orig_formula_quantifier = orig_formula_second.root
        result_formula_quantifier = orig_formula_quantifier
        formula_var = orig_formula_second.variable

        pulled_out_predicate, pulled_out_proof = pull_out_quantifications_from_right_across_binary_operator(
            first_op_predicate)
        result_formula = Formula.parse(f'{result_formula_quantifier}{formula_var}[{pulled_out_predicate}]')

        prev_proof_ln = prover.add_proof(pulled_out_proof.conclusion, pulled_out_proof)

        quan_w_first_op_pred = Formula.parse(f'{result_formula_quantifier}{formula_var}[{first_op_predicate}]')
        ante = pulled_out_proof.conclusion
        cond = equivalence_of(quan_w_first_op_pred, result_formula)
        f0 = Formula.parse(f'({ante}->{cond})')
        axiom_i = 14 if result_formula_quantifier == 'A' else 15
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_i]
        m0 = {'R': first_op_predicate.substitute({formula_var: Term('_')}),
              'Q': pulled_out_predicate.substitute({formula_var: Term('_')}),
              'x': formula_var,
              'y': formula_var}
        s0 = prover.add_instantiated_assumption(f0, axiom, m0)

        quan_w_first_op_pred_EQ_result = cond
        s_quan_w_first_op_pred_EQ_result = prover.add_mp(quan_w_first_op_pred_EQ_result, prev_proof_ln, s0)

        orig_EQ_quan_w_first_op_pred = equivalence_of(orig_formula, quan_w_first_op_pred)
        axiom_i = _get_axiom_for_binary_and_quantifier_from_right(orig_formula_op, orig_formula_quantifier)
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_i]
        m2 = {'x': formula_var,
              'R': orig_formula_second.predicate.substitute({formula_var: Term('_')}),
              'Q': orig_formula_first}
        s_orig_EQ_quan_w_first_op_pred = prover.add_instantiated_assumption(orig_EQ_quan_w_first_op_pred, axiom, m2)

        orig_eq_result = equivalence_of(orig_formula, result_formula)
        s_final = prover.add_tautological_implication(orig_eq_result,
                                                      {s_quan_w_first_op_pred_EQ_result,
                                                       s_orig_EQ_quan_w_first_op_pred})

        return result_formula, prover.qed()


def _get_axiom_for_binary_and_quantifier_from_right(binary_op, quantifier):
    if quantifier == 'A':
        if binary_op == '&':
            return 4
        elif binary_op == '|':
            return 8
        elif binary_op == '->':
            return 12
    elif quantifier == 'E':
        if binary_op == '&':
            return 5
        elif binary_op == '|':
            return 9
        elif binary_op == '->':
            return 13


def pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8
    orig_formula = formula
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

    pulled_from_left_f, pulled_from_left_p = pull_out_quantifications_from_left_across_binary_operator(orig_formula)
    pulled_from_left_s = prover.add_proof(pulled_from_left_p.conclusion, pulled_from_left_p)

    inner_pred_of_pulled_from_left, reversed_quans_and_vars = _get_inner_pred_of_quan_formula(pulled_from_left_f)
    pulled_from_right_f, pulled_from_right_p = pull_out_quantifications_from_right_across_binary_operator(
        inner_pred_of_pulled_from_left)
    pulled_from_right_s = prover.add_proof(pulled_from_right_p.conclusion, pulled_from_right_p)

    curr_R = inner_pred_of_pulled_from_left
    curr_Q = pulled_from_right_f
    last_proof_ln = pulled_from_right_s

    for curr_quan, curr_var in reversed_quans_and_vars:
        ante = prover._lines[last_proof_ln].formula
        quantified_R = Formula.parse(f'{curr_quan}{curr_var}[{curr_R}]')
        quantified_Q = Formula.parse(f'{curr_quan}{curr_var}[{curr_Q}]')
        cond = equivalence_of(quantified_R, quantified_Q)
        f0 = Formula.parse(f'({ante}->{cond})')
        axiom_i = 14 if curr_quan == 'A' else 15
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_i]
        m0 = {'R': curr_R.substitute({curr_var: Term('_')}),
              'Q': curr_Q.substitute({curr_var: Term('_')}),
              'x': curr_var,
              'y': curr_var}
        s0 = prover.add_instantiated_assumption(f0, axiom, m0)

        f_mp = cond
        last_proof_ln = prover.add_mp(f_mp, last_proof_ln, s0)

        curr_R, curr_Q = quantified_R, quantified_Q

    result_formula = curr_Q
    orig_EQ_result = equivalence_of(orig_formula, result_formula)
    s_final = prover.add_tautological_implication(orig_EQ_result, {pulled_from_left_s, last_proof_ln})

    return result_formula, prover.qed()


def _get_inner_pred_of_quan_formula(quantified_formula):
    if not is_quantifier(quantified_formula.root):
        return quantified_formula, []
    list_of_quan_and_var = []
    list_of_quan_and_var.append((quantified_formula.root, quantified_formula.variable))
    curr_pred = quantified_formula.predicate
    while is_quantifier(curr_pred.root):
        list_of_quan_and_var.append((curr_pred.root, curr_pred.variable))
        curr_pred = curr_pred.predicate
    reversed_list_of_quan_and_var = reversed(list_of_quan_and_var)
    return curr_pred, reversed_list_of_quan_and_var


def to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9
    orig_formula = formula
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

    if is_relation(formula.root) or is_equality(formula.root):
        formula_EQ_formula = equivalence_of(orig_formula, orig_formula)
        s_formula_EQ_formula = prover.add_tautology(formula_EQ_formula)
        result_formula = orig_formula

    elif is_quantifier(formula.root):
        orig_predicate = orig_formula.predicate
        original_quantifier = orig_formula.root
        original_var = orig_formula.variable
        predicate_in_prenex_f, predicate_in_prenex_p = to_prenex_normal_form_from_uniquely_named_variables(
            orig_predicate)
        result_formula = Formula.parse(f'{original_quantifier}{original_var}[{predicate_in_prenex_f}]')
        predicate_in_prenex_s = prover.add_proof(predicate_in_prenex_p.conclusion, predicate_in_prenex_p)

        orig_first_EQ_first_in_prenex = predicate_in_prenex_p.conclusion
        cond = equivalence_of(orig_formula, result_formula)
        f0 = Formula.parse(f'({orig_first_EQ_first_in_prenex}->{cond})')
        axiom_i = 14 if original_quantifier == 'A' else 15
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_i]
        m0 = {'R': orig_predicate.substitute({original_var: Term('_')}),
              'Q': predicate_in_prenex_f.substitute({original_var: Term('_')}),
              'x': original_var,
              'y': original_var}
        s0 = prover.add_instantiated_assumption(f0, axiom, m0)

        f1 = cond
        s1 = prover.add_mp(f1, predicate_in_prenex_s, s0)

    elif is_unary(formula.root):
        orig_first = orig_formula.first
        orig_op = formula.root
        first_in_prenex_f, first_in_prenex_p = to_prenex_normal_form_from_uniquely_named_variables(orig_first)
        neg_first_in_prenex = Formula.parse(f'{orig_op}{first_in_prenex_f}')
        first_in_prenex_s = prover.add_proof(first_in_prenex_p.conclusion, first_in_prenex_p)

        result_formula, result_formula_p = pull_out_quantifications_across_negation(neg_first_in_prenex)
        neg_first_in_prenex_EQ_result_s = prover.add_proof(result_formula_p.conclusion, result_formula_p)

        orig_EQ_neg_first_in_prenex = equivalence_of(orig_formula, neg_first_in_prenex)
        orig_first_EQ_first_in_prenex = first_in_prenex_p.conclusion
        add_neg_f = Formula.parse(f'({orig_first_EQ_first_in_prenex}->{orig_EQ_neg_first_in_prenex})')
        add_neg_s = prover.add_tautology(add_neg_f)

        f_mp = orig_EQ_neg_first_in_prenex
        orig_EQ_neg_first_in_prenex_s = prover.add_mp(f_mp, first_in_prenex_s, add_neg_s)

        orig_EQ_result = equivalence_of(orig_formula, result_formula)
        prover.add_tautological_implication(orig_EQ_result,
                                            {orig_EQ_neg_first_in_prenex_s, neg_first_in_prenex_EQ_result_s})

    elif is_binary(formula.root):
        orig_first = orig_formula.first
        orig_second = orig_formula.second
        orig_op = formula.root
        first_in_prenex_f, first_in_prenex_p = to_prenex_normal_form_from_uniquely_named_variables(orig_first)
        second_in_prenex_f, second_in_prenex_p = to_prenex_normal_form_from_uniquely_named_variables(orig_second)
        first_in_prenex_s = prover.add_proof(first_in_prenex_p.conclusion, first_in_prenex_p)
        second_in_prenex_s = prover.add_proof(second_in_prenex_p.conclusion, second_in_prenex_p)
        first_prenex_OP_second_prenex = Formula.parse(f'({first_in_prenex_f}{orig_op}{second_in_prenex_f})')

        result_formula, result_formula_p = pull_out_quantifications_across_binary_operator(
            first_prenex_OP_second_prenex)
        first_pnf_OP_second_PNF_EQ_result_s = prover.add_proof(result_formula_p.conclusion, result_formula_p)
        orig_EQ_result = equivalence_of(orig_formula, result_formula)

        orig_EQ_first_pnf_OP_second_pnf = equivalence_of(orig_formula, first_prenex_OP_second_prenex)
        orig_first_EQ_pnf_first = first_in_prenex_p.conclusion
        orig_second_EQ_pnf_second = second_in_prenex_p.conclusion

        first_EQ_and_second_EQ_f = f'({orig_first_EQ_pnf_first}&{orig_second_EQ_pnf_second})'
        first_EQ_and_second_EQ_s = prover.add_tautological_implication(first_EQ_and_second_EQ_f,
                                                                       {first_in_prenex_s, second_in_prenex_s})

        add_op_f = Formula.parse(
            f'(({orig_first_EQ_pnf_first}&{orig_second_EQ_pnf_second})->{orig_EQ_first_pnf_OP_second_pnf})')
        add_op_s = prover.add_tautology(add_op_f)

        f_mp = orig_EQ_first_pnf_OP_second_pnf
        orig_EQ_first_pnf_OP_second_pnf_s = prover.add_mp(f_mp, first_EQ_and_second_EQ_s, add_op_s)

        orig_EQ_result = equivalence_of(orig_formula, result_formula)
        prover.add_tautological_implication(orig_EQ_result,
                                            {first_pnf_OP_second_PNF_EQ_result_s, orig_EQ_first_pnf_OP_second_pnf_s})

    return result_formula, prover.qed()


def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.10

    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

    formula_with_unique_names_f, formula_with_unique_names_p = uniquely_rename_quantified_variables(formula)
    orig_EQ_unique_named_s = prover.add_proof(formula_with_unique_names_p.conclusion, formula_with_unique_names_p)
    formula_in_pnf_f, formula_in_pnf_p = to_prenex_normal_form_from_uniquely_named_variables(
        formula_with_unique_names_f)
    unique_named_EQ_pnf_unique_named_s = prover.add_proof(formula_in_pnf_p.conclusion, formula_in_pnf_p)
    orig_EQ_result = equivalence_of(formula, formula_in_pnf_f)
    prover.add_tautological_implication(orig_EQ_result, {orig_EQ_unique_named_s, unique_named_EQ_pnf_unique_named_s})
    return formula_in_pnf_f, prover.qed()