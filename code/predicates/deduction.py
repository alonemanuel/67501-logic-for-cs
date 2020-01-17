# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in predicate logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *


def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` orig_f, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: orig_f that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.1

    assumptions = proof.assumptions.difference({Schema(assumption)})
    antecedent = assumption
    consequent = proof.conclusion

    lut = [0] * len(proof.lines)  # The number of additional new lines
    prover = Prover(assumptions, print_as_proof_forms)

    for i, line in enumerate(proof.lines):
        orig_f = line.formula
        curr_f = f'({antecedent}->{orig_f})'
        if orig_f == assumption:
            lut[i] = prover.add_tautology(curr_f)

        elif isinstance(line, Proof.AssumptionLine):
            f_assump = line.formula
            a_assump = line.assumption
            m_assump = line.instantiation_map

            s0 = prover.add_instantiated_assumption(orig_f, a_assump, m_assump)

            f1 = f'({f_assump}->{curr_f})'
            s1 = prover.add_tautology(f1)

            lut[i] = prover.add_mp(curr_f, s0, s1)
        elif isinstance(line, Proof.MPLine):
            ante_ln = lut[line.antecedent_line_number]
            cond_ln = lut[line.conditional_line_number]
            lut[i] = prover.add_tautological_implication(curr_f, {ante_ln, cond_ln})
        elif isinstance(line, Proof.TautologyLine):
            lut[i] = prover.add_tautology(curr_f)
        elif isinstance(line, Proof.UGLine):
            predicate_ln = lut[line.predicate_line_number]
            predicate_f = prover._lines[predicate_ln].formula
            var0 = orig_f.variable
            f0 = f'A{var0}[{predicate_f}]'
            s0 = prover.add_ug(f0, predicate_ln)

            f1 = f'({f0}->{curr_f})'
            unquan = orig_f.predicate
            m1 = {'x': var0, 'Q': antecedent, 'R': unquan.substitute({var0: Term('_')})}
            s1 = prover.add_instantiated_assumption(f1, Prover.US, m1)

            lut[i] = prover.add_mp(curr_f, s0, s1)

    return prover.qed()


def proof_by_way_of_contradiction(proof: Proof, assumption: Formula,
                                  print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Return:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.2

    contradiction = proof.conclusion
    neg_contradiction = f'~{contradiction}'
    neg_assumption = f'~{assumption}'

    proof = remove_assumption(proof, assumption)
    assumptions = proof.assumptions
    prover = Prover(assumptions, print_as_proof_forms)
    _copy_lines_from_proof(proof, prover)
    orig_conclusion_ln = len(proof.lines) - 1

    f0 = neg_contradiction
    s0 = prover.add_tautology(f0)

    f1 = neg_assumption
    s1 = prover.add_tautological_implication(f1, {orig_conclusion_ln, s0})

    return prover.qed()


def _copy_lines_from_proof(proof_to_copy_from, prover_to_copy_to):
    prover = prover_to_copy_to
    for line in proof_to_copy_from.lines:
        instance = line.formula
        if isinstance(line, Proof.AssumptionLine):
            assumption = line.assumption
            inst_map = line.instantiation_map
            prover.add_instantiated_assumption(instance, assumption, inst_map)
        elif isinstance(line, Proof.TautologyLine):
            prover.add_tautology(instance)
        elif isinstance(line, Proof.UGLine):
            unquan_line_number = line.predicate_line_number
            prover.add_ug(instance, unquan_line_number)
        elif isinstance(line, Proof.MPLine):
            ante_ln = line.antecedent_line_number
            cond_ln = line.conditional_line_number
            prover.add_mp(instance, ante_ln, cond_ln)
