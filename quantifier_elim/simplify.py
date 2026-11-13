"""Formula simplification, constant folding, NNF and DNF transformations."""

from __future__ import annotations

from typing import Dict, List, Optional, Set, Tuple

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


def simplify(formula: Formula, max_iterations: int = 50) -> Formula:
    """Simplify a first-order formula to a fixed point."""
    curr = formula
    for _ in range(max_iterations):
        nxt = _simplify_step(curr)
        if nxt == curr:
            return curr
        curr = nxt
    return curr


def _simplify_step(formula: Formula) -> Formula:
    if isinstance(formula, (TrueF, FalseF)):
        return formula

    if isinstance(formula, Predicate):
        return _simplify_predicate(formula)

    if isinstance(formula, Not):
        arg = _simplify_step(formula.arg)
        if isinstance(arg, TrueF):
            return FalseF()
        if isinstance(arg, FalseF):
            return TrueF()
        if isinstance(arg, Not):
            return arg.arg
        return Not(arg)

    if isinstance(formula, And):
        args: List[Formula] = []
        for a in formula.args:
            sim_a = _simplify_step(a)
            if isinstance(sim_a, FalseF):
                return FalseF()
            if isinstance(sim_a, And):
                args.extend(sim_a.args)
            elif not isinstance(sim_a, TrueF):
                args.append(sim_a)

        # Remove duplicates while preserving order
        unique_args: List[Formula] = []
        seen = set()
        for a in args:
            if a not in seen:
                seen.add(a)
                unique_args.append(a)

        # Check for complementary contradictions (A and ~A)
        for a in unique_args:
            if Not(a) in seen:
                return FalseF()
            if isinstance(a, Predicate) and a.name == "<":
                # Check for cycle: x < y and y < x
                s, t = a.args
                if Predicate("<", (t, s)) in seen:
                    return FalseF()
                # Check for x < y and x = y
                if Predicate("=", (s, t)) in seen or Predicate("=", (t, s)) in seen:
                    return FalseF()

        if not unique_args:
            return TrueF()
        if len(unique_args) == 1:
            return unique_args[0]
        return And(*unique_args)

    if isinstance(formula, Or):
        args = []
        for a in formula.args:
            sim_a = _simplify_step(a)
            if isinstance(sim_a, TrueF):
                return TrueF()
            if isinstance(sim_a, Or):
                args.extend(sim_a.args)
            elif not isinstance(sim_a, FalseF):
                args.append(sim_a)

        unique_args = []
        seen = set()
        for a in args:
            if a not in seen:
                seen.add(a)
                unique_args.append(a)

        # Check for complementary tautologies (A or ~A)
        for a in unique_args:
            if Not(a) in seen:
                return TrueF()
            if isinstance(a, Predicate) and a.name == "<":
                # Check for trichotomy: s < t or t < s or s = t
                s, t = a.args
                has_rev = Predicate("<", (t, s)) in seen
                has_eq = Predicate("=", (s, t)) in seen or Predicate("=", (t, s)) in seen
                if has_rev and has_eq:
                    return TrueF()

        if not unique_args:
            return FalseF()
        if len(unique_args) == 1:
            return unique_args[0]
        return Or(*unique_args)

    if isinstance(formula, Impl):
        left = _simplify_step(formula.left)
        right = _simplify_step(formula.right)
        if isinstance(left, FalseF) or isinstance(right, TrueF):
            return TrueF()
        if isinstance(left, TrueF):
            return right
        if isinstance(right, FalseF):
            return simplify(Not(left))
        if left == right:
            return TrueF()
        return Impl(left, right)

    if isinstance(formula, Iff):
        left = _simplify_step(formula.left)
        right = _simplify_step(formula.right)
        if left == right:
            return TrueF()
        if isinstance(left, TrueF):
            return right
        if isinstance(right, TrueF):
            return left
        if isinstance(left, FalseF):
            return simplify(Not(right))
        if isinstance(right, FalseF):
            return simplify(Not(left))
        return Iff(left, right)

    if isinstance(formula, ForAll):
        body = _simplify_step(formula.body)
        if formula.var not in body.free_vars():
            return body
        if isinstance(body, (TrueF, FalseF)):
            return body
        return ForAll(formula.var, body)

    if isinstance(formula, Exists):
        body = _simplify_step(formula.body)
        if formula.var not in body.free_vars():
            return body
        if isinstance(body, (TrueF, FalseF)):
            return body
        return Exists(formula.var, body)

    return formula


def _simplify_predicate(p: Predicate) -> Formula:
    if p.name == "<":
        s, t = p.args
        if s == t:
            return FalseF()
        if isinstance(s, Const) and isinstance(t, Const):
            if isinstance(s.val, (int, float)) and isinstance(t.val, (int, float)):
                return TrueF() if s.val < t.val else FalseF()
    elif p.name == "=":
        s, t = p.args
        if s == t:
            return TrueF()
        if isinstance(s, Const) and isinstance(t, Const):
            return TrueF() if s.val == t.val else FalseF()
    elif p.name == ">":
        return _simplify_predicate(Predicate("<", (p.args[1], p.args[0])))
    return p


def to_nnf(formula: Formula) -> Formula:
    """Convert a formula into Negation Normal Form (NNF)."""
    f = simplify(formula)
    if isinstance(f, (TrueF, FalseF, Predicate)):
        return f

    if isinstance(f, Not):
        arg = f.arg
        if isinstance(arg, TrueF):
            return FalseF()
        if isinstance(arg, FalseF):
            return TrueF()
        if isinstance(arg, Predicate):
            return Not(arg)
        if isinstance(arg, Not):
            return to_nnf(arg.arg)
        if isinstance(arg, And):
            return Or(*(to_nnf(Not(a)) for a in arg.args))
        if isinstance(arg, Or):
            return And(*(to_nnf(Not(a)) for a in arg.args))
        if isinstance(arg, Impl):
            return And(to_nnf(arg.left), to_nnf(Not(arg.right)))
        if isinstance(arg, Iff):
            return to_nnf(Not(And(Impl(arg.left, arg.right), Impl(arg.right, arg.left))))
        if isinstance(arg, ForAll):
            return Exists(arg.var, to_nnf(Not(arg.body)))
        if isinstance(arg, Exists):
            return ForAll(arg.var, to_nnf(Not(arg.body)))
        return Not(to_nnf(arg))

    if isinstance(f, And):
        return And(*(to_nnf(a) for a in f.args))

    if isinstance(f, Or):
        return Or(*(to_nnf(a) for a in f.args))

    if isinstance(f, Impl):
        return Or(to_nnf(Not(f.left)), to_nnf(f.right))

    if isinstance(f, Iff):
        return And(
            Or(to_nnf(Not(f.left)), to_nnf(f.right)),
            Or(to_nnf(Not(f.right)), to_nnf(f.left)),
        )

    if isinstance(f, ForAll):
        return ForAll(f.var, to_nnf(f.body))

    if isinstance(f, Exists):
        return Exists(f.var, to_nnf(f.body))

    return f


def expand_dlo_negations(formula: Formula) -> Formula:
    """Expand negated DLO relations into positive disjunctions."""
    if isinstance(formula, (TrueF, FalseF)):
        return formula

    if isinstance(formula, Predicate):
        if formula.name == ">":
            return Predicate("<", (formula.args[1], formula.args[0]))
        return formula

    if isinstance(formula, Not):
        arg = formula.arg
        if isinstance(arg, Predicate):
            if arg.name == "<":
                s, t = arg.args
                return Or(Predicate("<", (t, s)), Predicate("=", (s, t)))
            if arg.name == "=":
                s, t = arg.args
                return Or(Predicate("<", (s, t)), Predicate("<", (t, s)))
            if arg.name == ">":
                s, t = arg.args
                return Or(Predicate("<", (s, t)), Predicate("=", (s, t)))
        return Not(expand_dlo_negations(arg))

    if isinstance(formula, And):
        return And(*(expand_dlo_negations(a) for a in formula.args))

    if isinstance(formula, Or):
        return Or(*(expand_dlo_negations(a) for a in formula.args))

    if isinstance(formula, Impl):
        return Impl(expand_dlo_negations(formula.left), expand_dlo_negations(formula.right))

    if isinstance(formula, Iff):
        return Iff(expand_dlo_negations(formula.left), expand_dlo_negations(formula.right))

    if isinstance(formula, ForAll):
        return ForAll(formula.var, expand_dlo_negations(formula.body))

    if isinstance(formula, Exists):
        return Exists(formula.var, expand_dlo_negations(formula.body))

    return formula


def to_dnf_clauses(formula: Formula) -> List[List[Formula]]:
    """Convert a quantifier-free formula to DNF clauses (list of conjunctions)."""
    f = expand_dlo_negations(to_nnf(formula))
    return _extract_dnf_clauses(f)


def _extract_dnf_clauses(formula: Formula) -> List[List[Formula]]:
    f = simplify(formula)
    if isinstance(f, FalseF):
        return []
    if isinstance(f, TrueF):
        return [[]]

    if isinstance(f, Or):
        clauses: List[List[Formula]] = []
        for a in f.args:
            clauses.extend(_extract_dnf_clauses(a))
        return clauses

    if isinstance(f, And):
        curr_clauses: List[List[Formula]] = [[]]
        for a in f.args:
            a_cls = _extract_dnf_clauses(a)
            nxt_clauses: List[List[Formula]] = []
            for c1 in curr_clauses:
                for c2 in a_cls:
                    merged = list(c1) + list(c2)
                    sim_and = simplify(And(*merged))
                    if not isinstance(sim_and, FalseF):
                        if isinstance(sim_and, TrueF):
                            nxt_clauses.append([])
                        elif isinstance(sim_and, And):
                            nxt_clauses.append(list(sim_and.args))
                        else:
                            nxt_clauses.append([sim_and])
            curr_clauses = nxt_clauses
            if not curr_clauses:
                return []
        return curr_clauses

    return [[f]]


def to_dnf(formula: Formula) -> Formula:
    """Convert a quantifier-free formula into Disjunctive Normal Form (DNF)."""
    clauses = to_dnf_clauses(formula)
    if not clauses:
        return FalseF()
    or_args: List[Formula] = []
    for c in clauses:
        if not c:
            return TrueF()
        if len(c) == 1:
            or_args.append(c[0])
        else:
            or_args.append(And(*c))
    if len(or_args) == 1:
        return or_args[0]
    return Or(*or_args)
