# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in propositional logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *


def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` into a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a
    statement = InferenceRule(antecedent_proof.statement.assumptions, consequent)
    rules = antecedent_proof.rules.union({MP, conditional})
    lines = [line for line in antecedent_proof.lines]
    lines.append(Proof.Line(Formula('->', antecedent_proof.statement.conclusion, consequent), conditional, []))
    lines.append(Proof.Line(consequent, MP, [len(lines) - 2, len(lines) - 1]))
    return Proof(statement, rules, lines)


def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulae `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``('``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
                    Formula('->', antecedent2_proof.statement.conclusion, consequent))
    ).is_specialization_of(double_conditional)
    # Task 5.3b
    statement = InferenceRule(antecedent1_proof.statement.assumptions, consequent)
    rules = antecedent1_proof.rules.union({double_conditional, MP})
    lines = [line for line in antecedent1_proof.lines]
    lines.append(Proof.Line(Formula(IMPLIES, antecedent1_proof.statement.conclusion,
                                    Formula(IMPLIES, antecedent2_proof.statement.conclusion, consequent)),
                            double_conditional, []))
    line_number = len(lines) - 1
    f2 = Formula(IMPLIES, antecedent2_proof.statement.conclusion, consequent)
    lines += [Proof.Line(line.formula, None if line.is_assumption() else line.rule,
                         None if line.is_assumption() else [i + len(lines) for i in line.assumptions]) for line in
              antecedent2_proof.lines]
    lines.append(Proof.Line(f2, MP, [line_number - 1, line_number]))
    lines.append(Proof.Line(consequent, MP, [len(lines) - 2, len(lines) - 1]))
    return Proof(statement, rules, lines)


def remove_assumption(proof: Proof) -> Proof:
    """Converts a proof of some `conclusion` formula, the last assumption of
    which is an assumption `assumption`, into a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of ``'(``\ `assumptions`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4
    antecedent = proof.statement.assumptions[-1]
    consequent = proof.statement.conclusion
    statement = InferenceRule(proof.statement.assumptions[:-1], Formula(IMPLIES, antecedent, consequent))
    rules = proof.rules.union({MP, I0, I1, D})
    lines = []

    lut = [None] * len(proof.lines)  # The number of additional new lines
    for i, line in enumerate(proof.lines):
        formula = line.formula
        if formula == antecedent:
            _deduction_I0(lines, antecedent, line)
        elif line.is_assumption():
            _deduction_assump(lines, antecedent, line)
        elif line.assumptions:
            _deduction_MP(lines, antecedent, line, lut)
        elif not line.assumptions:
            _deduction_other(lines, antecedent, line)
        lut[i] = len(lines) - 1
    return Proof(statement, rules, lines)


def _deduction_MP(lines, antedecent, line, lut):
    lr = lines[lut[line.assumptions[1]]].formula
    l = lr.first
    r = lr.second
    formula_D_l = Formula(IMPLIES, l, r.first)
    formula_D_r = Formula(IMPLIES, l, r.second)
    formula_D_lr = Formula(IMPLIES, formula_D_l, formula_D_r)
    formula_D = Formula(IMPLIES, lr, formula_D_lr)
    line_D = Proof.Line(formula_D, D, [])
    lines.append(line_D)

    line_MP = Proof.Line(formula_D_lr, MP, [lut[line.assumptions[1]], len(lines) - 1])
    lines.append(line_MP)

    formula_new = Formula(IMPLIES, antedecent, line.formula)
    line_new = Proof.Line(formula_new, MP, [lut[line.assumptions[0]], len(lines) - 1])
    lines.append(line_new)

    #
    #
    #
    # formula_D_l = Formula(IMPLIES, antedecent, l)
    # formula_D_r = Formula(IMPLIES, antedecent, r)
    # formula_MP = Formula(IMPLIES, formula_D_l, formula_D_r)
    # formula_D = Formula(IMPLIES, antedecent, Formula(IMPLIES, l, r))
    #
    # line_D = Proof.Line(formula_D, D, [])
    # line_MP = Proof.Line(formula_MP, MP, [len(lines) - 3, len(lines) - 2])
    #
    #
    # lines += [line_D, line_MP, line_new]


def _deduction_other(lines, antecedent, line):
    line_orig = line
    lines.append(line_orig)

    formula_I1_l = line.formula
    formula_I1_r = Formula(IMPLIES, antecedent, line.formula)
    formula_I1 = Formula(IMPLIES, formula_I1_l, formula_I1_r)
    line_I1 = Proof.Line(formula_I1, I1, [])
    lines.append(line_I1)

    line_MP = Proof.Line(formula_I1_r, MP, [len(lines) - 2, len(lines) - 1])
    lines.append(line_MP)
    return 2
    # formula_D_l = line.formula
    # formula_D_r = Formula(IMPLIES, antecedent, line.formula)
    # formula_D = Formula(IMPLIES, formula_D_l, formula_D_r)
    # line_D = Proof.Line(formula_D, D, [])
    #
    # formula_MP = Formula(IMPLIES, antecedent, line.formula)
    # line_MP = Proof.Line(formula_MP, MP, [len(lines) - 2, len(lines) - 1])
    #
    # lines += [line_orig, line_D, line_MP]


def _deduction_assump(lines, antecendent, line):
    line_orig = line

    formula_I1 = Formula(IMPLIES, line.formula, Formula(IMPLIES, antecendent, line.formula))
    line_I1 = Proof.Line(formula_I1, I1, [])

    formula = Formula(IMPLIES, antecendent, line.formula)
    new_line = Proof.Line(formula, MP, [len(lines) - 2, len(lines) - 1])

    lines += [line_orig, line_I1, new_line]
    return 2


def _deduction_I0(lines, antecendent, line):
    formula = Formula(IMPLIES, antecendent, line.formula)
    new_line = Proof.Line(formula, I0, [])
    lines.append(new_line)
    return 0


def proof_from_inconsistency(proof_of_affirmation: Proof,
                             proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6


def prove_by_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, into a proof of `formula` from
    the same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
