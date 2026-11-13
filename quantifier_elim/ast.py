"""First-order abstract syntax tree for quantifier elimination."""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Any, Dict, List, Optional, Set, Tuple, Union


class Term(ABC):
    """Abstract base class for first-order terms."""

    @abstractmethod
    def vars(self) -> Set[str]:
        """Return the set of variable names occurring in this term."""
        pass

    @abstractmethod
    def substitute(self, subst: Dict[str, Term]) -> Term:
        """Apply term substitution to variables."""
        pass


class Var(Term):
    """First-order variable."""

    def __init__(self, name: str) -> None:
        self.name = name

    def vars(self) -> Set[str]:
        return {self.name}

    def substitute(self, subst: Dict[str, Term]) -> Term:
        return subst.get(self.name, self)

    def __repr__(self) -> str:
        return f"Var({self.name!r})"

    def __str__(self) -> str:
        return self.name

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Var) and self.name == other.name

    def __hash__(self) -> int:
        return hash(("Var", self.name))


class Const(Term):
    """First-order constant."""

    def __init__(self, val: Any) -> None:
        self.val = val

    def vars(self) -> Set[str]:
        return set()

    def substitute(self, subst: Dict[str, Term]) -> Term:
        return self

    def __repr__(self) -> str:
        return f"Const({self.val!r})"

    def __str__(self) -> str:
        return str(self.val)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Const) and self.val == other.val

    def __hash__(self) -> int:
        return hash(("Const", self.val))


class Formula(ABC):
    """Abstract base class for first-order formulas."""

    @abstractmethod
    def free_vars(self) -> Set[str]:
        """Return the set of free variables in this formula."""
        pass

    @abstractmethod
    def all_vars(self) -> Set[str]:
        """Return all variables (free and bound) occurring in this formula."""
        pass

    @abstractmethod
    def substitute(self, subst: Dict[str, Term]) -> Formula:
        """Apply capture-avoiding substitution to free variables."""
        pass


class TrueF(Formula):
    """Logical truth constant."""

    def free_vars(self) -> Set[str]:
        return set()

    def all_vars(self) -> Set[str]:
        return set()

    def substitute(self, subst: Dict[str, Term]) -> Formula:
        return self

    def __repr__(self) -> str:
        return "TrueF()"

    def __str__(self) -> str:
        return "True"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, TrueF)

    def __hash__(self) -> int:
        return hash("TrueF")


class FalseF(Formula):
    """Logical falsity constant."""

    def free_vars(self) -> Set[str]:
        return set()

    def all_vars(self) -> Set[str]:
        return set()

    def substitute(self, subst: Dict[str, Term]) -> Formula:
        return self

    def __repr__(self) -> str:
        return "FalseF()"

    def __str__(self) -> str:
        return "False"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, FalseF)

    def __hash__(self) -> int:
        return hash("FalseF")


class Predicate(Formula):
    """First-order predicate application."""

    def __init__(self, name: str, args: Tuple[Term, ...]) -> None:
        self.name = name
        self.args = tuple(args)

    def free_vars(self) -> Set[str]:
        res: Set[str] = set()
        for a in self.args:
            res.update(a.vars())
        return res

    def all_vars(self) -> Set[str]:
        return self.free_vars()

    def substitute(self, subst: Dict[str, Term]) -> Formula:
        new_args = tuple(a.substitute(subst) for a in self.args)
        return Predicate(self.name, new_args)

    def __repr__(self) -> str:
        return f"Predicate({self.name!r}, {self.args!r})"

    def __str__(self) -> str:
        if len(self.args) == 2 and self.name in ("<", "=", ">", "<=", ">="):
            return f"({self.args[0]} {self.name} {self.args[1]})"
        return f"{self.name}({', '.join(str(a) for a in self.args)})"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Predicate) and self.name == other.name and self.args == other.args

    def __hash__(self) -> int:
        return hash(("Predicate", self.name, self.args))


def Lt(left: Union[Term, str], right: Union[Term, str]) -> Predicate:
    """Helper for less-than relation."""
    l = Var(left) if isinstance(left, str) else left
    r = Var(right) if isinstance(right, str) else right
    return Predicate("<", (l, r))


def Eq(left: Union[Term, str], right: Union[Term, str]) -> Predicate:
    """Helper for equality relation."""
    l = Var(left) if isinstance(left, str) else left
    r = Var(right) if isinstance(right, str) else right
    return Predicate("=", (l, r))


def Gt(left: Union[Term, str], right: Union[Term, str]) -> Predicate:
    """Helper for greater-than relation."""
    l = Var(left) if isinstance(left, str) else left
    r = Var(right) if isinstance(right, str) else right
    return Predicate("<", (r, l))


def Le(left: Union[Term, str], right: Union[Term, str]) -> Formula:
    """Helper for less-than-or-equal relation."""
    l = Var(left) if isinstance(left, str) else left
    r = Var(right) if isinstance(right, str) else right
    return Or(Lt(l, r), Eq(l, r))


class Not(Formula):
    """Logical negation."""

    def __init__(self, arg: Formula) -> None:
        self.arg = arg

    def free_vars(self) -> Set[str]:
        return self.arg.free_vars()

    def all_vars(self) -> Set[str]:
        return self.arg.all_vars()

    def substitute(self, subst: Dict[str, Term]) -> Formula:
        return Not(self.arg.substitute(subst))

    def __repr__(self) -> str:
        return f"Not({self.arg!r})"

    def __str__(self) -> str:
        return f"~{self.arg}"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Not) and self.arg == other.arg

    def __hash__(self) -> int:
        return hash(("Not", self.arg))


class And(Formula):
    """Logical conjunction."""

    def __init__(self, *args: Formula) -> None:
        self.args = tuple(args)

    def free_vars(self) -> Set[str]:
        res: Set[str] = set()
        for a in self.args:
            res.update(a.free_vars())
        return res

    def all_vars(self) -> Set[str]:
        res: Set[str] = set()
        for a in self.args:
            res.update(a.all_vars())
        return res

    def substitute(self, subst: Dict[str, Term]) -> Formula:
        return And(*(a.substitute(subst) for a in self.args))

    def __repr__(self) -> str:
        return f"And{self.args!r}"

    def __str__(self) -> str:
        if not self.args:
            return "True"
        return f"({' & '.join(str(a) for a in self.args)})"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, And) and self.args == other.args

    def __hash__(self) -> int:
        return hash(("And", self.args))


class Or(Formula):
    """Logical disjunction."""

    def __init__(self, *args: Formula) -> None:
        self.args = tuple(args)

    def free_vars(self) -> Set[str]:
        res: Set[str] = set()
        for a in self.args:
            res.update(a.free_vars())
        return res

    def all_vars(self) -> Set[str]:
        res: Set[str] = set()
        for a in self.args:
            res.update(a.all_vars())
        return res

    def substitute(self, subst: Dict[str, Term]) -> Formula:
        return Or(*(a.substitute(subst) for a in self.args))

    def __repr__(self) -> str:
        return f"Or{self.args!r}"

    def __str__(self) -> str:
        if not self.args:
            return "False"
        return f"({' | '.join(str(a) for a in self.args)})"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Or) and self.args == other.args

    def __hash__(self) -> int:
        return hash(("Or", self.args))


class Impl(Formula):
    """Logical implication."""

    def __init__(self, left: Formula, right: Formula) -> None:
        self.left = left
        self.right = right

    def free_vars(self) -> Set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def all_vars(self) -> Set[str]:
        return self.left.all_vars() | self.right.all_vars()

    def substitute(self, subst: Dict[str, Term]) -> Formula:
        return Impl(self.left.substitute(subst), self.right.substitute(subst))

    def __repr__(self) -> str:
        return f"Impl({self.left!r}, {self.right!r})"

    def __str__(self) -> str:
        return f"({self.left} ==> {self.right})"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Impl) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("Impl", self.left, self.right))


class Iff(Formula):
    """Logical biconditional."""

    def __init__(self, left: Formula, right: Formula) -> None:
        self.left = left
        self.right = right

    def free_vars(self) -> Set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def all_vars(self) -> Set[str]:
        return self.left.all_vars() | self.right.all_vars()

    def substitute(self, subst: Dict[str, Term]) -> Formula:
        return Iff(self.left.substitute(subst), self.right.substitute(subst))

    def __repr__(self) -> str:
        return f"Iff({self.left!r}, {self.right!r})"

    def __str__(self) -> str:
        return f"({self.left} <==> {self.right})"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Iff) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("Iff", self.left, self.right))


class ForAll(Formula):
    """Universal quantifier."""

    def __init__(self, var: str, body: Formula) -> None:
        self.var = var
        self.body = body

    def free_vars(self) -> Set[str]:
        return self.body.free_vars() - {self.var}

    def all_vars(self) -> Set[str]:
        return self.body.all_vars() | {self.var}

    def substitute(self, subst: Dict[str, Term]) -> Formula:
        clean_subst = {k: v for k, v in subst.items() if k != self.var}
        subst_vars: Set[str] = set()
        for v in clean_subst.values():
            subst_vars.update(v.vars())
        if self.var in subst_vars:
            fresh = fresh_var_name(self.var, self.body.all_vars() | subst_vars)
            renamed_body = self.body.substitute({self.var: Var(fresh)})
            return ForAll(fresh, renamed_body.substitute(clean_subst))
        return ForAll(self.var, self.body.substitute(clean_subst))

    def __repr__(self) -> str:
        return f"ForAll({self.var!r}, {self.body!r})"

    def __str__(self) -> str:
        return f"(all {self.var}. {self.body})"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, ForAll) and self.var == other.var and self.body == other.body

    def __hash__(self) -> int:
        return hash(("ForAll", self.var, self.body))


class Exists(Formula):
    """Existential quantifier."""

    def __init__(self, var: str, body: Formula) -> None:
        self.var = var
        self.body = body

    def free_vars(self) -> Set[str]:
        return self.body.free_vars() - {self.var}

    def all_vars(self) -> Set[str]:
        return self.body.all_vars() | {self.var}

    def substitute(self, subst: Dict[str, Term]) -> Formula:
        clean_subst = {k: v for k, v in subst.items() if k != self.var}
        subst_vars: Set[str] = set()
        for v in clean_subst.values():
            subst_vars.update(v.vars())
        if self.var in subst_vars:
            fresh = fresh_var_name(self.var, self.body.all_vars() | subst_vars)
            renamed_body = self.body.substitute({self.var: Var(fresh)})
            return Exists(fresh, renamed_body.substitute(clean_subst))
        return Exists(self.var, self.body.substitute(clean_subst))

    def __repr__(self) -> str:
        return f"Exists({self.var!r}, {self.body!r})"

    def __str__(self) -> str:
        return f"(ex {self.var}. {self.body})"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Exists) and self.var == other.var and self.body == other.body

    def __hash__(self) -> int:
        return hash(("Exists", self.var, self.body))


def fresh_var_name(base: str, forbidden: Set[str]) -> str:
    """Generate a fresh variable name not in forbidden set."""
    candidate = base
    counter = 1
    while candidate in forbidden:
        candidate = f"{base}_{counter}"
        counter += 1
    return candidate
