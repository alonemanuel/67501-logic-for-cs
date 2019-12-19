# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/functions.py

"""Syntactic conversion of first-order formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.semantics import *

EQ = '='

AND_OP = '&'

EXISTS = 'E'

IMPLIES = '->'

FORALL = 'A'


def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]


def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]


def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function meanings, replacing each function meaning with a canonically
    corresponding relation meaning.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            meanings in this model.

    Return:
        A model obtained from the given model by replacing every function
        meaning of a function name with a relation meaning of the canonically
        corresponding relation name, such that the relation meaning contains
        any tuple ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1`
        is the output of the function meaning for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_meanings:
        assert function_name_to_relation_name(function) not in \
               model.relation_meanings
    # Task 8.1
    new_relation_meanings = dict(model.relation_meanings)
    for func, func_mapping in model.function_meanings.items():
        relation_name = function_name_to_relation_name(func)
        relation_meaning = set()
        for func_args, func_res in func_mapping.items():
            curr_meaning = (func_res,) + func_args
            relation_meaning.add(curr_meaning)

        new_relation_meanings[relation_name] = relation_meaning

    return Model(model.universe, model.constant_meanings, new_relation_meanings, dict())


def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function meanings to a canonically
    corresponding model with meanings for the given function names, having each
    new function meaning replace a canonically corresponding relation meaning.

    Parameters:
        model: model to convert, that contains no function meanings.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has a meaning in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_meanings
        assert function_name_to_relation_name(function) in \
               model.relation_meanings

    # Task 8.2
    new_function_meanings = dict()
    new_relation_meanings = dict(model.relation_meanings)

    for orig_func_name in original_functions:
        curr_function_meaning = dict()
        relation_name = function_name_to_relation_name(orig_func_name)
        if len(model.relation_meanings[relation_name]) != len(model.universe) ** (model.relation_arities[
                                                                                      relation_name] - 1):
            return None
        else:
            for curr_meaning in model.relation_meanings[relation_name]:
                func_res = curr_meaning[0]
                func_args = tuple(curr_meaning[1:])
                if func_args in curr_function_meaning.keys():
                    return None
                curr_function_meaning[func_args] = func_res

        new_function_meanings[orig_func_name] = curr_function_meaning
        del new_relation_meanings[relation_name]

    return Model(model.universe, model.constant_meanings, new_relation_meanings, new_function_meanings)


def compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and that
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable of the last
        returned step evaluates in that model to the value of the given term.
    """
    assert is_function(term.root)

    # Task 8.3
    return _compile_term_helper(term, [])


def _compile_term_helper(term, z_list):
    if is_constant(term.root) or is_variable(term.root):
        return z_list
    elif is_function(term.root):
        new_args = []
        for arg in term.arguments:
            if is_constant(arg.root) or is_variable(arg.root):
                new_args.append(arg)
            if is_function(arg.root):
                inner_z_lst = compile_term(arg)
                z_list += inner_z_lst
                new_args.append(inner_z_lst[-1].arguments[0])
        new_z = Term(next(fresh_variable_name_generator))
        new_term = Term(term.root, new_args)
        z_formula = Formula('=', [new_z, new_term])
        z_list.append(z_formula)
        return z_list


def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function meanings.

    Parameters:
        formula: formula to convert, that contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function, arity in formula.functions()}.intersection(
        {relation for relation, arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 8.4
    if is_constant(formula.root) or is_variable(formula.root):
        return formula
    elif is_unary(formula.root):
        return Formula(formula.root, replace_functions_with_relations_in_formula(formula.first))
    elif is_binary(formula.root):
        first = replace_functions_with_relations_in_formula(formula.first)
        second = replace_functions_with_relations_in_formula(formula.second)
        return Formula(formula.root, first, second)
    elif is_relation(formula.root) or is_equality(formula.root):
        return _replace_functions_in_relation(formula)
    elif is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, replace_functions_with_relations_in_formula(formula.predicate))


def _replace_functions_in_relation(formula):
    z_list = []
    for arg in formula.arguments:
        if is_function(arg.root):
            z_list += compile_term(arg)
    z_list.reverse()
    curr_consequent = _get_base_formula(formula, z_list)

    for z_formula in z_list:
        z_var, z_func = z_formula.arguments
        ante = _get_ante(z_var, z_func)
        predicate = Formula(IMPLIES, ante, curr_consequent)
        curr_consequent = Formula(FORALL, z_var.root, predicate)

    return curr_consequent


def _get_ante(z_var, z_func):
    relation_name = function_name_to_relation_name(z_func.root)
    relation_args = (z_var,) + z_func.arguments
    return Formula(relation_name, relation_args)


def _get_base_formula(formula, z_list):
    base_formula_args = []
    arg_i = 0
    for arg in reversed(formula.arguments):
        if is_constant(arg.root) or is_variable(arg.root):
            base_formula_args.append(arg)
        elif is_function(arg.root):
            base_formula_args.append(z_list[arg_i].arguments[0])
            arg_i += 1
    base_formula_args.reverse()
    return Formula(formula.root, base_formula_args)


def replace_functions_with_relations_in_formulas(formulas:
AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function meanings.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with meanings for the functions of the
       former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, that contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas holds in a model `model` if and only if the
           returned formulas holds in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas holds in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function, arity in formula.functions()}
                           for formula in formulas]).intersection(
        set.union(*[{relation for relation, arity in
                     formula.relations()} for
                    formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'
    # Task 8.5
    new_formulas = [replace_functions_with_relations_in_formula(formula) for formula in formulas]
    all_funcs = [formula.functions() for formula in formulas]
    all_funcs = [item for sublist in all_funcs for item in sublist]
    verifications = [_get_verification_for_function(func_name, n_args) for func_name, n_args in all_funcs]
    return set(new_formulas + verifications)


def _get_verification_for_function(func_name, n_args):
    func_args = [Term(next(fresh_variable_name_generator)) for i in range(n_args)]
    verif1 = _get_verif_for_definition(func_name, func_args)
    verif2 = _get_verif_for_uniqueness(func_name, func_args)
    return Formula(AND_OP, verif1, verif2)


def _get_base_formula_for_definition(func_name, func_args):
    relation_name = function_name_to_relation_name(func_name)
    res_arg = Term(next(fresh_variable_name_generator))
    base_relation = Formula(relation_name, [res_arg] + func_args)
    base_formula = Formula(EXISTS, res_arg.root, base_relation)
    return base_formula


def _get_verif_for_definition(func_name, func_args):
    predicate = _get_base_formula_for_definition(func_name, func_args)
    return _verif_from_predicate(predicate, func_args)


def _verif_from_predicate(curr_predicate, func_args):
    for arg in func_args:
        curr_predicate = Formula(FORALL, arg.root, curr_predicate)
    return curr_predicate


def _get_base_formula_for_uniqueness(func_name, func_args):
    relation_name = function_name_to_relation_name(func_name)
    res_arg1, res_arg2 = [Term(next(fresh_variable_name_generator)) for i in [0, 1]]

    relation1 = Formula(relation_name, [res_arg1] + func_args)
    relation2 = Formula(relation_name, [res_arg2] + func_args)
    ante = Formula(AND_OP, relation1, relation2)
    consequent = Formula(EQ, [res_arg1, res_arg2])

    predicate = Formula(IMPLIES, ante, consequent)
    formula = Formula(FORALL, res_arg1.root, Formula(FORALL, res_arg2.root, predicate))
    return formula


def _get_verif_for_uniqueness(func_name, func_args):
    predicate = _get_base_formula_for_uniqueness(func_name, func_args)
    return _verif_from_predicate(predicate, func_args)


def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model for the returned formulas,
       the meaning of the relation name ``'SAME'`` is reflexive, symmetric, and
       transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model for the returned formulas, the meaning of this
       relation name respects the meaning of the relation name ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation, arity in formula.relations()}

    # Task 8.6
    SAME_basic_formulas = _get_SAME_basic_formulas()
    SAME_relation_formulas = _get_SAME_relation_formulas(formulas)
    SAME_equality_formulas = _get_SAME_equality_formulas(formulas)
    return set(SAME_basic_formulas + SAME_relation_formulas + SAME_equality_formulas)


def _get_SAME_relation_formulas(formulas):
    all_relations = [formula.relations() for formula in formulas]
    # Removing 0-ary relations
    all_relations = [item for sublist in all_relations for item in sublist if item[1] > 0]

    verifications = [_get_verification_for_relation(rel_name, n_args) for rel_name, n_args in all_relations]
    return verifications


def _get_verification_for_relation(rel_name, n_args):
    rel_args = [[Term(next(fresh_variable_name_generator)) for i in range(n_args)] for j in [0, 1]]
    predicate = _get_base_formula_for_relation(rel_name, rel_args)
    flattened_args = rel_args[0] + rel_args[1]
    formula = _verif_from_predicate(predicate, flattened_args)
    return formula


def _get_base_formula_for_relation(rel_name, rel_args):
    pairs_of_sames = [Formula('SAME', [rel_args[0][i], rel_args[1][i]]) for i in range(len(rel_args[0]))]
    l_side = pairs_of_sames[0]
    for pair in pairs_of_sames[1:]:
        l_side = Formula(AND_OP, pair, l_side)
    r_side = Formula(IMPLIES, Formula(rel_name, rel_args[0]), Formula(rel_name, rel_args[1]))
    return Formula(IMPLIES, l_side, r_side)


def _get_SAME_equality_formulas(formulas):
    replaced = [_get_SAME_equality_formula(formula) for formula in formulas]
    return replaced


def _get_SAME_equality_formula(formula):
    if is_equality(formula.root):
        return Formula('SAME', formula.arguments)
    elif is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, _get_SAME_equality_formula(formula.predicate))
    elif is_unary(formula.root):
        return Formula(formula.root, _get_SAME_equality_formula(formula.first))
    elif is_binary(formula.root):
        return Formula(formula.root, _get_SAME_equality_formula(formula.first),
                       _get_SAME_equality_formula(formula.second))

    else:
        return formula


def _get_SAME_basic_formulas():
    ref_var = Term(next(fresh_variable_name_generator))
    ref_predicate = Formula('SAME', [ref_var, ref_var])
    reflexitivity = Formula(FORALL, ref_var.root, ref_predicate)

    symm_var1, symm_var2 = [Term(next(fresh_variable_name_generator)) for _ in [0, 1]]
    symm_l_formula = Formula('SAME', [symm_var1, symm_var2])
    symm_ = Formula('SAME', [symm_var2, symm_var1])
    symm_predicate = Formula(IMPLIES, symm_l_formula, symm_)
    symmetry = Formula(FORALL, symm_var1.root, Formula(FORALL, symm_var2.root, symm_predicate))

    tran_var1, tran_var2, tran_var3 = [Term(next(fresh_variable_name_generator)) for _ in [0, 1, 2]]
    tran_l_and = Formula('SAME', [tran_var1, tran_var2])
    tran_r_and = Formula('SAME', [tran_var2, tran_var3])
    tran_l_formula = Formula(AND_OP, tran_l_and, tran_r_and)
    tran_r_formula = Formula('SAME', [tran_var1, tran_var3])
    tran_predicate = Formula(IMPLIES, tran_l_formula, tran_r_formula)
    transitivity = Formula(FORALL, tran_var1.root,
                           Formula(FORALL, tran_var2.root, Formula(FORALL, tran_var3.root, tran_predicate)))

    return [reflexitivity, symmetry, transitivity]


def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds a meaning for the relation name ``'SAME'`` in the given model, that
    canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no meaning for the relation name ``'SAME'``, to
            add the meaning to.

    Return:
        A model obtained from the given model by adding a meaning for the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_meanings
    # Task 8.7
    same_relation = set([(elem, elem) for elem in model.universe])
    new_relation_meanings = dict(model.relation_meanings)
    new_relation_meanings['SAME'] = same_relation
    new_model = Model(model.universe, model.constant_meanings, new_relation_meanings)
    return new_model


def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    meaning of ``'SAME'`` in the given model, in the sense that any set of
    formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function meanings, and
            contains a meaning for the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the meanings
            of all other relation names.

    Returns:
        A model that is a model for any set `formulas` if and only if
        the given model is a model for
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        ``'SAME'`` relation in the given model.
    """
    assert 'SAME' in model.relation_meanings and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_meanings) == 0

    # Initial equiv classes: each elem represents {elem}
    equiv_classes = [{x} for x in model.universe]
    for x, y in model.relation_meanings['SAME']:
        class_x = _get_equiv_class(equiv_classes, x)
        class_y = _get_equiv_class(equiv_classes, y)
        united = class_x.union(class_y)
        equiv_classes.remove(class_x)
        if class_x != class_y:
            equiv_classes.remove(class_y)
        equiv_classes += [united]

    repr_list = [list(equiv_class)[0] for equiv_class in equiv_classes]
    new_universe = set(repr_list)
    new_constant_meanings = dict()
    for const in model.constant_meanings.keys():
        const_equiv_class = _get_equiv_class(equiv_classes, model.constant_meanings[const])
        class_i = equiv_classes.index(const_equiv_class)
        const_repr = repr_list[class_i]
        new_constant_meanings[const] = const_repr

    new_relation_meanings = dict()
    for rel_name, rel_meaning in model.relation_meanings.items():
        if rel_name == 'SAME':
            continue
        new_meaning = []
        for rel_tuple in rel_meaning:
            new_tuple = []
            for elem in rel_tuple:
                elem_equiv_class = _get_equiv_class(equiv_classes, elem)
                class_i = equiv_classes.index(elem_equiv_class)
                elem_repr = repr_list[class_i]
                new_tuple.append(elem_repr)
            new_tuple = tuple(new_tuple)
            new_meaning.append(new_tuple)
        new_meaning = set(new_meaning)
        new_relation_meanings[rel_name] = new_meaning

    return Model(new_universe, new_constant_meanings, new_relation_meanings)


def _get_equiv_class(equiv_classes, elem):
    for equiv_class in equiv_classes:
        if elem in equiv_class:
            return equiv_class
