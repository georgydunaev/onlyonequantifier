"""Quantifier elimination engine for Dense Linear Orders (DLO) and equality."""

from __future__ import annotations

from typing import Dict, List, Set

from quantifier_elim.ast import (
    And,
    Const,
    Eq,
    Exists,
    FalseF,
    ForAll,
    Formula,
    Iff,
    Impl,
    Lt,
    Not,
    Or,
    Predicate,
    Term,
    TrueF,
    Var,
)
from quantifier_elim.simplify import simplify, to_dnf_clauses


def eliminate_exists_dlo(var: str, matrix: Formula) -> Formula:
    """Eliminate an existential quantifier over a quantifier-free DLO formula."""
    sim_matrix = simplify(matrix)
    if var not in sim_matrix.free_vars():
        return sim_matrix

    clauses = to_dnf_clauses(sim_matrix)
    if not clauses:
        return FalseF()

    eliminated_clauses: List[Formula] = []
    for clause in clauses:
        res = _eliminate_exists_from_clause(var, clause)
        if isinstance(res, TrueF):
            return TrueF()
        if not isinstance(res, FalseF):
            eliminated_clauses.append(res)

    if not eliminated_clauses:
        return FalseF()
    if len(eliminated_clauses) == 1:
        return eliminated_clauses[0]
    return simplify(Or(*eliminated_clauses))


def _eliminate_exists_from_clause(var: str, clause: List[Formula]) -> Formula:
    """Eliminate an existential quantifier from a conjunction of positive literals."""
    # Check for equality involving var: var = t or t = var
    for idx, lit in enumerate(clause):
        if isinstance(lit, Predicate) and lit.name == "=":
            s, t = lit.args
            if isinstance(s, Var) and s.name == var and (not isinstance(t, Var) or t.name != var):
                subst = {var: t}
                remaining = [c.substitute(subst) for i, c in enumerate(clause) if i != idx]
                return simplify(And(*remaining))
            if isinstance(t, Var) and t.name == var and (not isinstance(s, Var) or s.name != var):
                subst = {var: s}
                remaining = [c.substitute(subst) for i, c in enumerate(clause) if i != idx]
                return simplify(And(*remaining))

    # No variable-eliminating equality; collect bounds
    lower_bounds: List[Term] = []
    upper_bounds: List[Term] = []
    rest: List[Formula] = []

    for lit in clause:
        if var not in lit.free_vars():
            rest.append(lit)
            continue

        if isinstance(lit, Predicate):
            if lit.name == "=":
                s, t = lit.args
                if s == t:
                    continue  # var = var is always true
                # If both sides are var, handled above.
            elif lit.name == "<":
                s, t = lit.args
                if s == t:
                    return FalseF()  # var < var is always false
                if isinstance(s, Var) and s.name == var:
                    upper_bounds.append(t)
                elif isinstance(t, Var) and t.name == var:
                    lower_bounds.append(s)
                else:
                    rest.append(lit)
            else:
                rest.append(lit)
        else:
            rest.append(lit)

    # DLO elimination: cross all lower bounds with all upper bounds
    cross_conditions: List[Formula] = []
    for l in lower_bounds:
        for u in upper_bounds:
            cross_conditions.append(Lt(l, u))

    return simplify(And(*(rest + cross_conditions)))


def eliminate_dlo(formula: Formula) -> Formula:
    """Full quantifier elimination for Dense Linear Orders without endpoints."""
    if isinstance(formula, (TrueF, FalseF)):
        return formula

    if isinstance(formula, Predicate):
        return simplify(formula)

    if isinstance(formula, Not):
        return simplify(Not(eliminate_dlo(formula.arg)))

    if isinstance(formula, And):
        return simplify(And(*(eliminate_dlo(a) for a in formula.args)))

    if isinstance(formula, Or):
        return simplify(Or(*(eliminate_dlo(a) for a in formula.args)))

    if isinstance(formula, Impl):
        return simplify(Impl(eliminate_dlo(formula.left), eliminate_dlo(formula.right)))

    if isinstance(formula, Iff):
        return simplify(Iff(eliminate_dlo(formula.left), eliminate_dlo(formula.right)))

    if isinstance(formula, Exists):
        qf_body = eliminate_dlo(formula.body)
        return eliminate_exists_dlo(formula.var, qf_body)

    if isinstance(formula, ForAll):
        # forall x. phi <==> ~exists x. ~phi
        qf_body = eliminate_dlo(formula.body)
        neg_body = simplify(Not(qf_body))
        elim_exists = eliminate_exists_dlo(formula.var, neg_body)
        return simplify(Not(elim_exists))

    return formula


def eliminate_quantifiers(formula: Formula) -> Formula:
    """Entry point for full quantifier elimination."""
    return eliminate_dlo(formula)
