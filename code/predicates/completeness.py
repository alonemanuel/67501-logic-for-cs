# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/completeness.py

from typing import AbstractSet, Container, Set, Union

from logic_utils import fresh_constant_name_generator

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import *


def get_constants(formulas: AbstractSet[Formula]) -> Set[str]:
    """Finds all constant names in the given formulas.

    Parameters:
        formulas: formulas to find all constant names in.

    Returns:
        A set of all constant names used in one or more of the given formulas.
    """
    constants = set()
    for formula in formulas:
        constants.update(formula.constants())
    return constants


def get_relations(formulas):
    relations = set()
    for formula in formulas:
        relations.update(formula.relations())
    return relations


def is_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if the given set of sentences is primitively, universally, and
        existentially closed, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    return is_primitively_closed(sentences) and \
           is_universally_closed(sentences) and \
           is_existentially_closed(sentences)


def is_primitively_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    primitively closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every n-ary relation name from the given sentences, and
        for every n (not necessarily distinct) constant names from the given
        sentences, either the invocation of this relation name over these
        constant names (in order), or the negation of this invocation, is one of
        the given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.1
    relations = get_relations(sentences)
    relation_names, relation_arities = zip(*relations)
    constants = get_constants(sentences)

    power_set_dict = dict()
    for arity in relation_arities:
        perm_iter = itertools.product(constants, repeat=arity)
        if arity not in power_set_dict.keys():
            power_set_dict[arity] = perm_iter

    for relation_name, relation_arity in list(relations):
        for perm in power_set_dict[relation_arity]:
            pos_formula = Formula(relation_name, perm)
            neg_formula = Formula('~', pos_formula)
            if not ((pos_formula in sentences) or (neg_formula in sentences)):
                return False
    else:
        return True


def is_universally_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    universally closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every universally quantified sentence of the given
        sentences, and for every constant name from the given sentences, the
        predicate of this quantified sentence, with every free occurrence of the
        universal quantification variable replaced with this constant name, is
        one of the given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.2

    constants = get_constants(sentences)
    for sentence in sentences:
        if sentence.root == 'A':
            for c in constants:
                sub_predicate = sentence.predicate.substitute({sentence.variable: Term(c)})
                if sub_predicate not in sentences:
                    return False
    else:
        return True


def is_existentially_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    existentially closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every existentially quantified sentence of the given
        sentences there exists a constant name such that the predicate of this
        quantified sentence, with every free occurrence of the existential
        quantification variable replaced with this constant name, is one of the
        given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.3
    constants = get_constants(sentences)
    for sentence in sentences:
        if sentence.root == 'E':
            for c in constants:
                sub_predicate = sentence.predicate.substitute({sentence.variable: Term(c)})
                if sub_predicate in sentences:
                    break
            else:
                return False
    else:
        return True


def find_unsatisfied_quantifier_free_sentence(sentences: Container[Formula],
                                              model: Model[str],
                                              unsatisfied: Formula) -> Formula:
    """
    Given a closed set of prenex-normal-form sentences, given a model whose
    universe is the set of all constant names from the given sentences, and
    given a sentence from the given set that the given model does not satisfy,
    finds a quantifier-free sentence from the given set that the given model
    does not satisfy.
    
    Parameters:
        sentences: closed set of prenex-normal-form sentences, which is only to
            be accessed using containment queries, i.e., using the ``in``
            operator as in:

            >>> if sentence in sentences:
            ...     print('contained!')

        model: model for all element names from the given sentences, whose
            universe is `get_constants`\ ``(``\ `sentences`\ ``)``.
        unsatisfied: sentence (which possibly contains quantifiers) from the
            given sentences that is not satisfied by the given model.

    Returns:
        A quantifier-free sentence from the given sentences that is not
        satisfied by the given model.
    """
    # We assume that every sentence in sentences is of type formula, is in
    # prenex normal form, and has no free variables, and furthermore that the
    # set of constants that appear somewhere in sentences is model.universe;
    # but we cannot assert these since we cannot iterate over sentences.
    for constant in model.universe:
        assert is_constant(constant)
    assert is_in_prenex_normal_form(unsatisfied)
    assert len(unsatisfied.free_variables()) == 0
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)
    # Task 12.2
    constants = model.universe
    return _find_unsatisfied_quantifier_free_sentence_helper(sentences, model, unsatisfied, constants)


def _find_unsatisfied_quantifier_free_sentence_helper(sentences: Container[Formula],
                                                      model: Model[str],
                                                      unsatisfied: Formula, constants) -> Formula:
    root = unsatisfied.root
    if root == 'A':
        for c in constants:
            var = unsatisfied.variable
            sub_predicate = unsatisfied.predicate.substitute({var: Term(c)})
            if not model.evaluate_formula(sub_predicate):
                return _find_unsatisfied_quantifier_free_sentence_helper(sentences, model, sub_predicate, constants)
    elif root == 'E':
        for c in constants:
            var = unsatisfied.variable
            sub_predicate = unsatisfied.predicate.substitute({var: Term(c)})
            if sub_predicate in sentences:
                return _find_unsatisfied_quantifier_free_sentence_helper(sentences, model, sub_predicate, constants)
    else:
        return unsatisfied


def get_primitives(quantifier_free: Formula) -> Set[Formula]:
    """Finds all primitive subformulas of the given quantifier-free formula.

    Parameters:
        quantifier_free: quantifier-free formula whose subformulas are to
            be searched.

    Returns:
        The primitive subformulas (i.e., relation invocations) of the given
        quantifier-free formula.

    Examples:
        The primitive subformulas of ``'(R(c1,d)|~(Q(c1)->~R(c2,a)))'`` are
        ``'R(c1,d)'``, ``'Q(c1)'``, and ``'R(c2,a)'``.
    """
    assert is_quantifier_free(quantifier_free)
    # Task 12.3.1
    root = quantifier_free.root
    if is_relation(root):
        return {quantifier_free}
    elif is_equality(root):
        return set()
    elif is_binary(root):
        return set.union(get_primitives(quantifier_free.first), get_primitives(quantifier_free.second))
    elif is_unary(root):
        return get_primitives(quantifier_free.first)


def model_or_inconsistency(sentences: AbstractSet[Formula]) -> \
        Union[Model[str], Proof]:
    """Either finds a model in which the given closed set of prenex-normal-form
    sentences holds, or proves a contradiction from these sentences.

    Parameters:
        sentences: closed set of prenex-normal-form sentences to either find a
            model for or prove a contradiction from.

    Returns:
        A model in which all of the given sentences hold if such exists,
        otherwise a valid proof of  a contradiction from the given formulas via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_closed(sentences)
    # Task 12.3.2
    universe = get_constants(sentences)
    termed_universe = [Term(elem) for elem in get_constants(sentences)]
    constant_meanings = dict(zip(universe, universe))
    relation_meanings = dict()

    for sentence in sentences:
        if is_relation(sentence.root):
            relation_name = sentence.root
            if relation_name not in relation_meanings.keys():
                relation_meanings[relation_name] = {tuple([arg.root for arg in sentence.arguments])}
            else:
                relation_meanings[relation_name].update({tuple([arg.root for arg in sentence.arguments])})

    res_model = Model(universe, constant_meanings, relation_meanings)

    for sentence in sentences:
        if not res_model.evaluate_formula(sentence):
            return _build_inconsistency(sentences, sentence, res_model)
    else:
        return res_model


def _build_inconsistency(sentences, unsatisfied_sentence, model):
    unquan_unsat_sentence = find_unsatisfied_quantifier_free_sentence(sentences, model, unsatisfied_sentence)
    primitives = get_primitives(unquan_unsat_sentence)
    primitives_in_sentences = list()
    for primitive in primitives:
        if primitive in sentences:
            primitives_in_sentences.append(primitive)
        else:
            primitives_in_sentences.append(Formula('~', primitive))
    assumptions = Prover.AXIOMS.union(set(sentences))
    prover = Prover(assumptions)

    primitive_line_indices = set()
    for primitive in primitives_in_sentences:
        primitive_line_indices.update({prover.add_assumption(primitive)})
    primitive_line_indices.update({prover.add_assumption(unquan_unsat_sentence)})

    unsat_and_primitives = Formula.parse(f'({unquan_unsat_sentence}&{primitives_in_sentences[0]})')
    for primitive in primitives_in_sentences[1:]:
        unsat_and_primitives = Formula.parse(f'({unsat_and_primitives}&{primitive})')

    prover.add_tautological_implication(unsat_and_primitives, primitive_line_indices)
    return prover.qed()


def combine_contradictions(proof_from_affirmation: Proof,
                           proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs of contradictions, both from the same
    assumptions/axioms except that the latter has an extra assumption that is
    the negation of an extra assumption that the former has, into a single proof
    of a contradiction from only the common assumptions/axioms.

    Parameters:
        proof_from_affirmation: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        proof_from_negation: valid proof of a contradiction from the same
            assumptions/axioms of `proof_from_affirmation`, but with one
            simple assumption `assumption` replaced with its negation
            ``'~``\ `assumption` ``'``.

    Returns:
        A valid proof of a contradiction from only the assumptions/axioms common
        to the given proofs (i.e., without `assumption` or its negation).
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions)
    assert len(common_assumptions) == \
           len(proof_from_affirmation.assumptions) - 1
    assert len(common_assumptions) == len(proof_from_negation.assumptions) - 1
    affirmed_assumption = list(
        proof_from_affirmation.assumptions.difference(common_assumptions))[0]
    negated_assumption = list(
        proof_from_negation.assumptions.difference(common_assumptions))[0]
    assert len(affirmed_assumption.templates) == 0
    assert len(negated_assumption.templates) == 0
    assert negated_assumption.formula == \
           Formula('~', affirmed_assumption.formula)
    assert proof_from_affirmation.assumptions.issuperset(Prover.AXIOMS)
    assert proof_from_negation.assumptions.issuperset(Prover.AXIOMS)
    for assumption in common_assumptions.union({affirmed_assumption,
                                                negated_assumption}):
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.4

    common_assumptions = proof_from_affirmation.assumptions.intersection(proof_from_negation.assumptions)
    prover = Prover(common_assumptions)

    affirmed_assumption = list(proof_from_affirmation.assumptions.difference(common_assumptions))[0].formula
    negated_assumption = list(proof_from_negation.assumptions.difference(common_assumptions))[0].formula
    proof_of_not_affirmation = proof_by_way_of_contradiction(proof_from_affirmation, affirmed_assumption)
    proof_of_not_negation = proof_by_way_of_contradiction(proof_from_negation, negated_assumption)

    s_affirmation = prover.add_proof(proof_of_not_affirmation.conclusion, proof_of_not_affirmation)
    s_negation = prover.add_proof(proof_of_not_negation.conclusion, proof_of_not_negation)

    f_affirmation_AND_negation = Formula.parse(f'({affirmed_assumption}&{negated_assumption})')
    s_affirmation_AND_negation = prover.add_tautological_implication(f_affirmation_AND_negation,
                                                                     {s_affirmation, s_negation})

    return prover.qed()


def eliminate_universal_instantiation_assumption(proof: Proof, constant: str,
                                                 instantiation: Formula,
                                                 universal: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `universal` and `instantiation`, where the latter is a universal
    instantiation of the former, to a proof of a contradiction from the same
    assumptions without `instantiation`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        universal: assumption of the given proof that is universally quantified.
        instantiation: assumption of the given proof that is obtained from the
            predicate of `universal` by replacing all free occurrences of the
            universal quantification variable by some constant.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `instantiation`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(instantiation) in proof.assumptions
    assert Schema(universal) in proof.assumptions
    assert universal.root == 'A'
    assert instantiation == \
           universal.predicate.substitute({universal.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.5

    proof_of_not_instantiation = proof_by_way_of_contradiction(proof, instantiation)
    assumptions = proof_of_not_instantiation.assumptions
    prover = Prover(assumptions)
    f_not_instantiation = proof_of_not_instantiation.conclusion
    s_not_instantiation = prover.add_proof(f_not_instantiation, proof_of_not_instantiation)

    f_universal = universal
    s_universal = prover.add_assumption(f_universal)

    f_instantiation = instantiation

    universal_variables = universal.predicate.variables()
    instantiation_constants = instantiation.constants()
    var_instantiation = list(instantiation_constants.difference(universal_variables))[0]
    s_instantiation = prover.add_universal_instantiation(f_instantiation, s_universal, Term(var_instantiation))
    f_not_instantiation_AND_instantiation = Formula.parse(f'({f_not_instantiation}&{instantiation})')
    s_not_instantiation_AND_instantiation = prover.add_tautological_implication(f_not_instantiation_AND_instantiation,
                                                                                {s_not_instantiation, s_instantiation})

    return prover.qed()


def universal_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with all universal instantiations of each
    universally quantified sentence from these sentences, with respect to all
    constant names from these sentences.

    Parameters:
        sentences: prenex-normal-form sentences to augment with their universal
            instantiations.

    Returns:
        A set of all of the given sentences, and in addition any formula that
        can be obtained replacing in the predicate of any universally quantified
        sentence from the given sentences, all occurrences of the quantification
        variable with some constant from the given sentences.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.6

    sentences_superset = set(sentences)

    for const in get_constants(sentences):
        for sentence in sentences:
            if not sentence.root == 'A':
                continue
            else:
                var = sentence.variable
                instantiation = sentence.predicate.substitute({var: Term(const)})
                sentences_superset.update({instantiation})

    return sentences_superset


def replace_constant(proof: Proof, constant: str, variable: str = 'zz') -> \
        Proof:
    """Replaces all occurrences of the given constant in the given proof with
    the given variable.

    Parameters:
        proof: a valid proof.
        constant: a constant name that does not appear as a template constant
            name in any of the assumptions of the given proof.
        variable: a variable name that does not appear anywhere in given the
            proof or in its assumptions.

    Returns:
        A valid proof where every occurrence of the given constant name in the
        given proof and in its assumptions is replaced with the given variable
        name.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert is_variable(variable)
    for assumption in proof.assumptions:
        assert constant not in assumption.templates
        assert variable not in assumption.formula.variables()
    for line in proof.lines:
        assert variable not in line.formula.variables()
    # Task 12.7.1
    substituted_assumptions = set()
    for assumption in proof.assumptions:
        sub_assumption = _replace_schema(assumption, constant, variable)
        substituted_assumptions.update({sub_assumption})

    substituted_lines = list()
    for line in proof.lines:
        sub_formula = line.formula.substitute({constant: Term(variable)})
        if isinstance(line, Proof.AssumptionLine):
            sub_assumption = _replace_schema(line.assumption, constant, variable)
            sub_map = _replace_substitution_map(line.instantiation_map, constant, variable)
            substituted_lines.append(Proof.AssumptionLine(sub_formula, sub_assumption, sub_map))
        elif isinstance(line, Proof.MPLine):
            substituted_lines.append(
                Proof.MPLine(sub_formula, line.antecedent_line_number, line.conditional_line_number))
        elif isinstance(line, Proof.UGLine):
            substituted_lines.append(Proof.UGLine(sub_formula, line.predicate_line_number))
        elif isinstance(line, Proof.TautologyLine):
            substituted_lines.append(Proof.TautologyLine(sub_formula))

    sub_conclusion = substituted_lines[-1].formula
    return Proof(substituted_assumptions, sub_conclusion, substituted_lines)


def _replace_substitution_map(map, constant, variable):
    sub_map = dict(map)
    for key, value in map.items():
        sub_key = key
        # sub_key = variable if key == constant else key
        if isinstance(value, str):
            sub_val = variable if value == constant else value
        else:
            sub_val = value.substitute({constant: Term(variable)}) if constant in value.constants() else value
        sub_map[sub_key] = sub_val

    return sub_map


def _replace_schema(schema, constant, variable):
    sub_formula = schema.formula.substitute({constant: Term(variable)})
    if constant in schema.templates:
        sub_templates = schema.templates.difference({constant}).union({variable})
    else:
        sub_templates = schema.templates
    sub_schema = Schema(sub_formula, sub_templates)
    return sub_schema


def eliminate_existential_witness_assumption(proof: Proof, constant: str,
                                             witness: Formula,
                                             existential: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `existential` and `witness`, where the latter is an existential
    witness of the former, to a proof of a contradiction from the same
    assumptions without `witness`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        existential: assumption of the given proof that is existentially
            quantified.
        witness: assumption of the given proof that is obtained from the
            predicate of `existential` by replacing all free occurrences of the
            existential quantification variable by some constant that does not
            appear in any assumption of the given proof except for this
            assumption.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `witness`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(witness) in proof.assumptions
    assert Schema(existential) in proof.assumptions
    assert existential.root == 'E'
    assert witness == \
           existential.predicate.substitute(
               {existential.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    for assumption in proof.assumptions.difference({Schema(witness)}):
        assert constant not in assumption.formula.constants()
    # Task 12.7.2

    replaced_proof = replace_constant(proof, constant)
    witness = witness.substitute({constant: Term('zz')})

    proof_of_not_witness = proof_by_way_of_contradiction(replaced_proof, witness)
    assumptions = proof_of_not_witness.assumptions
    prover = Prover(assumptions)
    f_not_witness = proof_of_not_witness.conclusion
    s_not_witness = prover.add_proof(f_not_witness, proof_of_not_witness)

    f_existential = existential
    s_existential = prover.add_assumption(f_existential)

    f_universal_not_witness = Formula.parse(f'Azz[{f_not_witness}]')
    s_universal_not_witness = prover.add_ug(f_universal_not_witness, s_not_witness)

    f_existential_witness_AND_universal_not_witness = Formula.parse(f'({f_existential}&{f_universal_not_witness})')
    s_existential_witness_AND_universal_not_witness = prover.add_tautological_implication(
        f_existential_witness_AND_universal_not_witness, {s_existential, s_universal_not_witness})

    return prover.qed()


def existential_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with an existential witness that uses a new
    constant name, for each existentially quantified sentences from these
    sentences for which an existential witness is missing.

    Parameters:
        sentences: prenex-normal-form sentences to augment with any missing
            existential witnesses.

    Returns:
        A set of all of the given sentences, and in addition for every
        existentially quantified sentence from the given sentences, a formula
        obtained from the predicate of that quantified sentence by replacing all
        occurrences of the quantification variable with a new constant name
        obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_constant_name_generator`\ ``)``.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.8
