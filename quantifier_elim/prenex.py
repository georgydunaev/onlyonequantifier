"""Sound conversion of first-order formulas to Prenex Normal Form."""

from __future__ import annotations

from typing import List, Set, Tuple

from quantifier_elim.ast import (
    And,
    Exists,
    FalseF,
    ForAll,
    Formula,
    Iff,
    Impl,
    Not,
    Or,
    Predicate,
    TrueF,
    Var,
    fresh_var_name,
)
from quantifier_elim.simplify import to_nnf


def prenex_decompose(formula: Formula) -> Tuple[List[Tuple[str, str]], Formula]:
    """Decompose formula into a quantifier prefix and a quantifier-free matrix."""
    nnf_formula = to_nnf(formula)
    return _prenex_rec(nnf_formula)


def _prenex_rec(formula: Formula) -> Tuple[List[Tuple[str, str]], Formula]:
    if isinstance(formula, (TrueF, FalseF, Predicate)):
        return [], formula

    if isinstance(formula, Not):
        return [], formula

    if isinstance(formula, ForAll):
        sub_pref, sub_mat = _prenex_rec(formula.body)
        var = formula.var
        bound_in_sub = {v for _, v in sub_pref}
        if var in bound_in_sub:
            forbidden = bound_in_sub | sub_mat.all_vars()
            fresh = fresh_var_name(var, forbidden)
            sub_mat = sub_mat.substitute({var: Var(fresh)})
            var = fresh
        return [("forall", var)] + sub_pref, sub_mat

    if isinstance(formula, Exists):
        sub_pref, sub_mat = _prenex_rec(formula.body)
        var = formula.var
        bound_in_sub = {v for _, v in sub_pref}
        if var in bound_in_sub:
            forbidden = bound_in_sub | sub_mat.all_vars()
            fresh = fresh_var_name(var, forbidden)
            sub_mat = sub_mat.substitute({var: Var(fresh)})
            var = fresh
        return [("exists", var)] + sub_pref, sub_mat

    if isinstance(formula, And):
        return _lift_junction(formula.args, is_and=True)

    if isinstance(formula, Or):
        return _lift_junction(formula.args, is_and=False)

    return [], formula


def _lift_junction(args: Tuple[Formula, ...], is_and: bool) -> Tuple[List[Tuple[str, str]], Formula]:
    branch_results = [_prenex_rec(a) for a in args]

    # Collect free variables across all branches
    free_vars_all: Set[str] = set()
    for _, mat in branch_results:
        free_vars_all.update(mat.free_vars())

    # Variables already bound or free across the combined structure
    forbidden_vars: Set[str] = set(free_vars_all)
    seen_bound: Set[str] = set()
    combined_prefix: List[Tuple[str, str]] = []
    combined_matrix_args: List[Formula] = []

    for pref, mat in branch_results:
        renamed_mat = mat
        branch_pref: List[Tuple[str, str]] = []
        for q, v in pref:
            # Must rename if v is free in another branch, or already bound in prefix
            if v in free_vars_all or v in seen_bound:
                all_known = forbidden_vars | seen_bound | renamed_mat.all_vars()
                fresh = fresh_var_name(v, all_known)
                renamed_mat = renamed_mat.substitute({v: Var(fresh)})
                seen_bound.add(fresh)
                forbidden_vars.add(fresh)
                branch_pref.append((q, fresh))
            else:
                seen_bound.add(v)
                forbidden_vars.add(v)
                branch_pref.append((q, v))
        combined_prefix.extend(branch_pref)
        combined_matrix_args.append(renamed_mat)

    res_mat = And(*combined_matrix_args) if is_and else Or(*combined_matrix_args)
    return combined_prefix, res_mat


def to_prenex(formula: Formula) -> Formula:
    """Convert any first-order formula into Prenex Normal Form."""
    prefix, matrix = prenex_decompose(formula)
    res = matrix
    for q, v in reversed(prefix):
        if q == "forall":
            res = ForAll(v, res)
        else:
            res = Exists(v, res)
    return res
