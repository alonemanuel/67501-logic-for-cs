# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.proofs import *
from propositions.deduction import *
from propositions.semantics import *
# from propositions.operators import *
from propositions.axiomatic_systems import *


def formulae_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulae that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable x that is assigned the value
    ``False``.

    Parameters:
        model: model to construct the formulae for.

    Returns:
        A list of the constructed formulae, ordered alphabetically by variable
        name.

    Examples:
        >>> formulae_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    # Task 6.1a
    vars = list(model.keys())
    vars.sort()
    return [Formula(var) if model[var] else Formula(NEG, Formula(var)) for var in vars]


def prove_in_model(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    # Task 6.1b

    if is_variable(formula.root):
        return _prove_var(formula, model)
    elif is_unary(formula.root):
        return _prove_neg(formula, model)
    elif is_binary(formula.root) and formula.root == IMPLIES:
        return _prove_implies(formula, model)


def _get_proof_elements(formula, model):
    eval = evaluate(formula, model)
    conclusion = formula if eval else Formula(NEG, formula)
    assumptions = formulae_capturing_model(model)
    statement = InferenceRule(assumptions, conclusion)
    rules = AXIOMATIC_SYSTEM
    return eval, conclusion, statement, rules


def _prove_var(formula, model):
    eval, conclusion, statement, rules = _get_proof_elements(formula, model)
    f = conclusion
    lines = []
    l = Proof.Line(f)
    lines.append(l)
    p = Proof(statement, rules, lines)
    return p


def _prove_neg(formula, model):
    eval, conclusion, statement, rules = _get_proof_elements(formula, model)
    f = formula.first
    p = prove_in_model(f, model)
    if eval:
        return p
    else:
        lines = p.lines
        f0 = Formula(IMPLIES, f, conclusion)
        l0 = Proof.Line(f0, NN, [])
        lines += (l0,)
        f1 = conclusion
        l1 = Proof.Line(f1, MP, [len(lines) - 2, len(lines) - 1])
        lines += (l1,)
        return Proof(statement, rules, lines)


def _prove_implies(formula, model):
    eval, conclusion, statement, rules = _get_proof_elements(formula, model)
    precedent, consequent = formula.first, formula.second
    if eval:
        if not evaluate(precedent, model):
            p = prove_in_model(precedent, model)
            lines = p.lines
            f0 = Formula.parse(f'(~{precedent}->{conclusion})')
            l0 = Proof.Line(f0, I2, [])

        else:
            p = prove_in_model(consequent, model)
            lines = p.lines
            f0 = Formula.parse(f'({consequent}->{conclusion})')
            l0 = Proof.Line(f0, I1, [])
        lines += (l0,)
        f1 = conclusion
        l1 = Proof.Line(f1, MP, [len(lines) - 2, len(lines) - 1])
        lines += (l1,)
        return Proof(statement, rules, lines)

    else:
        p_prec = prove_in_model(precedent, model)
        neg_cons = Formula(NEG, consequent)
        p_cons = prove_in_model(neg_cons, model)
        proof = combine_proofs(p_prec, p_cons, conclusion, NI)
        return proof


def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_of_negation: valid proof of `conclusion` from the same assumptions
            and inference rules of `proof_from_affirmation`, but with the last
            assumption being ``'~``\ `assumption` ``'`` instead of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If the two given proofs are of ``['p', 'q'] ==> '(q->p)'`` and of
        ``['p', '~q'] ==> ('q'->'p')``, then the returned proof is of
        ``['p'] ==> '(q->p)'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    # Task 6.2
    affirmation_p = remove_assumption(proof_from_affirmation)
    statement = proof_from_negation.statement
    negation_p = remove_assumption(proof_from_negation)
    p = combine_proofs(affirmation_p, negation_p, statement.conclusion, R)
    return p


def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulae that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulae to prove.

    Returns:
        A valid proof of the given tautology from the formulae that capture the
        given model, in the order returned by
        `formulae_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        If the given model is the empty dictionary, then the returned proof is
        of the given tautology from no assumptions.
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    # Task 6.3a
    len_model, len_formula = len(model), len(tautology.variables())
    if len_model == len_formula:
        return _prove_full_model(tautology, model)
    elif len_model == len_formula - 1:
        return _prove_one_less(tautology, model)
    elif len_model < len_formula - 1:
        return _prove_missing_model(tautology, model)


def _prove_missing_model(tautology, model):
    var = sorted(tautology.variables())[len(model)]
    m_affirmation, m_negation = dict(model), dict(model)
    m_affirmation[var], m_negation[var] = True, False
    p_affirmation = prove_tautology(tautology, m_affirmation)
    p_negation = prove_tautology(tautology, m_negation)
    return reduce_assumption(p_affirmation, p_negation)


def _prove_one_less(tautology, model):
    var = sorted(tautology.variables())[len(model)]
    m_affirmation, m_negation = dict(model), dict(model)
    m_affirmation[var], m_negation[var] = True, False
    p_affirmation = prove_in_model(tautology, m_affirmation)
    p_negation = prove_in_model(tautology, m_negation)
    return reduce_assumption(p_affirmation, p_negation)


def _prove_full_model(tautology, model):
    return prove_in_model(tautology, model)


def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    # Task 6.3b
    if is_tautology(formula):
        return prove_tautology(formula, dict())
    else:
        return _find_counter_example(formula)


def _find_counter_example(formula):
    for model in all_models(formula.variables()):
        if not evaluate(formula, model):
            return model


def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))
        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    # Task 6.4a
    if len(rule.assumptions) == 0:
        return rule.conclusion
    elif len(rule.assumptions) == 1:
        return Formula(IMPLIES, rule.assumptions[0], rule.conclusion)
    else:
        assump = rule.assumptions[0]
        reduced_rule = InferenceRule(rule.assumptions[1:], rule.conclusion)
        reduced_formula = encode_as_formula(reduced_rule)
        return Formula(IMPLIES, assump, reduced_formula)


def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion that contain
            no constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid assumptionless proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})
    # Task 6.4b
    statement = rule
    rules = AXIOMATIC_SYSTEM
    lines = []
    for assump in rule.assumptions:
        lines.append(Proof.Line(assump))

    encoded_formula = encode_as_formula(rule)
    p = prove_tautology(encoded_formula)
    lines += [Proof.Line(line.formula, line.rule, [i + len(lines) for i in line.assumptions]) for line in p.lines]
    curr_formula = encoded_formula
    for i, assump in enumerate(rule.assumptions):
        f = curr_formula.second
        l = Proof.Line(f, MP, [i, len(lines) - 1])
        lines.append(l)
        curr_formula = f

    return Proof(statement, rules, lines)


def model_or_inconsistency(formulae: List[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulae hold, or proves
    ``'~(p->p)'`` from these formula.

    Parameters:
        formulae: formulae that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulae hold if such exists,
        otherwise a proof of '~(p->p)' from the given formulae via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulae:
        assert formula.operators().issubset({'->', '~'})
    # Task 6.5
    vars = []
    for formula in formulae:
        vars += formula.variables()
    for model in all_models(vars):
        for formula in formulae:
            if not evaluate(formula, model):
                break
        else:
            return model
    else:
        rule = InferenceRule(formulae, Formula.parse('~(p->p)'))
        return prove_sound_inference(rule)




def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
