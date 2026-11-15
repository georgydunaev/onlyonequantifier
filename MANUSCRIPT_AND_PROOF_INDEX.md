# Manuscript and Proof Index: onlyonequantifier

## 1. Repository Overview and Scope

`onlyonequantifier` is a formal logic and automated reasoning repository with two complementary components:
1. **Isabelle/Pure Intuitionistic First-Order Logic with Uniqueness Binders (`my_IFOL.thy`)**: A 1006-line foundational theory built directly over `Pure` that introduces the uniqueness quantifier `Only1` ($?x.\,P(x)$, meaning at most one $x$ satisfies $P(x)$) alongside the universal quantifier `All` ($\forall x.\,P(x)$) and defines unique existence `Ex1` ($\exists!x.\,P(x) \equiv (\exists x.\,P(x)) \land (?x.\,P(x))$), investigating how quantifier rules and natural deduction tactics behave when uniqueness is treated as a primitive binder concept.
2. **Modular First-Order Quantifier Elimination and Formula Simplification Engine (`quantifier_elim/`)**: A self-contained Python verification package (`ast.py`, `simplify.py`, `prenex.py`, `elimination.py`) implementing first-order syntax, capture-avoiding substitution, Negation Normal Form (NNF), Disjunctive Normal Form (DNF), Prenex Normal Form (PNF), and Fourier-Motzkin / Langford quantifier elimination over Dense Linear Orders without Endpoints ($\mathsf{DLO}$, e.g. $(\mathbb{Q}, <)$ and $(\mathbb{R}, <)$).

---

## 2. Inventory of Source Proof and Code Files

| File | Lines | Language / System | Role and Contents |
| :--- | :--- | :--- | :--- |
| `my_IFOL.thy` | 1006 | Isabelle/Pure | Complete intuitionistic first-order logic (`IFOL`) development built from `Pure` with **0 `sorry` and 0 `oops`**. Declares sort `term` and proposition type `o` (`Judgment`), equality (`=`), falsehood (`False`), universal quantifier (`All`), derived connectives (`&`, `|`, `-->`, `Not`, `<->`, `Ex`), the uniqueness quantifier `Only1` (binder syntax `?`), and unique existence `Ex1` (binder syntax `?!`). Proves over 120 natural deduction lemmas and registers the `IntPr` intuitionistic proof search engine (`fast_tac`, `best_tac`, ` safe_tac`). |
| `quantifier_elim/__init__.py` | 45 | Python | Public API exporting AST constructors, normal-form transformers (`simplify`, `to_nnf`, `to_dnf`, `to_prenex`, `prenex_decompose`), and quantifier elimination functions (`eliminate_quantifiers`, `eliminate_exists_conjunction`). |
| `quantifier_elim/ast.py` | 215 | Python | First-order AST hierarchy (`Term`, `Var`, `Const`, `Formula`, `Top`, `Bot`, `Predicate`, `Eq`, `Lt`, `Le`, `Gt`, `Not`, `And`, `Or`, `Impl`, `Iff`, `ForAll`, `Exists`), free-variable computation (`free_vars`), fresh-variable generation (`fresh_var`), and capture-avoiding term substitution (`substitute`). |
| `quantifier_elim/simplify.py` | 240 | Python | Algebraic and relational formula simplifier (`simplify`), Negation Normal Form transformer (`to_nnf`) with DLO trichotomy expansion ($\neg(x < y) \equiv (x = y \lor y < x)$, $\neg(x = y) \equiv (x < y \lor y < x)$), and Disjunctive Normal Form extractor (`to_dnf`) with cycle/unsatisfiability pruning. |
| `quantifier_elim/prenex.py` | 145 | Python | Sound Prenex Normal Form converter (`to_prenex`, `prenex_decompose`) pulling nested `ForAll` and `Exists` quantifiers to the prefix with automatic alpha-renaming to avoid variable capture across conjunctions, disjunctions, and implications. |
| `quantifier_elim/elimination.py` | 265 | Python | Innermost-out quantifier elimination engine (`eliminate_quantifiers`) for Dense Linear Orders without Endpoints ($\mathsf{DLO}$) and monadic predicates, reducing $\exists x.\,\bigwedge_i \ell_i(x)$ via equality elimination ($x = t$) and cross-pairing of strict lower bounds ($l_i < x$) against strict upper bounds ($x < u_j$). |
| `tests/test_onlyonequantifier.py` | 310 | Python | Unit and property-based verification suite testing AST substitution, NNF/DNF/PNF truth preservation across randomized valuations, and $\mathsf{DLO}$ quantifier elimination soundness. |

---

## 3. Core Mathematical Results Established

### 3.1 Intuitionistic First-Order Logic and Uniqueness Quantification (`my_IFOL.thy`)
1. **Minimal Primitive Basis over `Isabelle/Pure`**:
   - Starting from primitive `eq` ($=$), `False` ($\bot$), and `All` ($\forall$), `my_IFOL.thy` defines conjunction, disjunction, and existential quantification via impredicative higher-order encodings over `o`:
     - $P \land Q \equiv \forall R : o.\,(P \implies Q \implies R) \implies R$ (`conj_def`)
     - $P \lor Q \equiv \forall R : o.\,(P \implies R) \implies (Q \implies R) \implies R$ (`disj_def`)
     - $\exists x.\,P(x) \equiv \forall R : o.\,(\forall x.\,P(x) \implies R) \implies R$ (`Ex_def`)
   - Derives the standard introduction and elimination rules (`conjI`, `conjunct1`, `conjunct2`, `disjI1`, `disjI2`, `disjE`, `exI`, `exE`) from `mp` (`==>`) and `allI`/`allE` without extra axioms for `&`, `|`, or `Ex`.
2. **Uniqueness Quantifier `Only1` (`?`) and Unique Existence `Ex1` (`?!`) (`my_IFOL.thy` lines 55--67, 250--285)**:
   - Defines uniqueness (`Only1_def`): $?x.\,P(x) \equiv \forall a\,b.\,P(a) \land P(b) \implies a = b$.
   - Defines unique existence (`Ex1_def`): $?!x.\,P(x) \equiv (\exists x.\,P(x)) \land (?x.\,P(x))$.
   - Proves introduction and elimination rules (`ex1I`, `ex1E`, `ex1_def`) and congruence laws (`subst`, `refl`, `sym`, `trans`, ` iff_refl`, `iff_sym`, `iff_trans`).
3. **Quantifier Distributivity and Scope Minimization (`my_IFOL.thy` lines 350--510)**:
   - Mechanizes full quantifier-connective equivalences (`all_conj_distrib`, `ex_disj_distrib`, `all_not_ex`, `ex_not_all`) and miniscoping rules (`all_simps`, `ex_simps`) showing how a single universal or existential quantifier commutes with quantifier-free subformulas.

### 3.2 Quantifier Elimination in Dense Linear Orders (`quantifier_elim/`)
1. **DLO Negation Elimination and Normal Forms (`simplify.py`, `prenex.py`)**:
   - Every first-order formula over $\{=, <, \le, >\}$ is transformed into an equivalent quantifier-free DNF inside each existential block by expanding $x \le y \equiv (x < y \lor x = y)$, $\neg(x = y) \equiv (x < y \lor y < x)$, and $\neg(x < y) \equiv (x = y \lor y < x)$.
2. **Langford / Fourier-Motzkin Elimination Step (`elimination.py`)**:
   - Given a primitive existential conjunction $\exists x.\,\left(\bigwedge_{a \in L} a < x \;\land\; \bigwedge_{b \in U} x < b \;\land\; \psi_{\text{indep}}\right)$ in a dense linear order without endpoints:
     - If $x = t$ occurs, $x$ is eliminated immediately by substituting $t$ for $x$ (or returning $\bot$ if $x < x$ occurs).
     - Otherwise, by density ($\forall a < b.\,\exists x.\,a < x < b$) and unboundedness ($\forall a.\,\exists x.\,x < a$ and $\exists y.\,a < y$), the existential quantifier $\exists x$ is eliminated in favor of the quantifier-free conjunction $\psi_{\text{indep}} \land \bigwedge_{a \in L,\,b \in U} (a < b)$.
   - Universal quantifiers are eliminated via duality $\forall x.\,\varphi \equiv \neg \exists x.\,\neg \varphi$.

---

## 4. Open Questions and Future Research Directions

1. **Mechanizing `Only1` (`?x`) Proof Rules in `my_IFOL.thy`**:
   - While `my_IFOL.thy` defines `Only1(P) == ALL a b. P(a) & P(b) --> a = b` (line 58) and uses it to define `Ex1` (`?!x. P(x)` at line 66), the subsequent natural deduction rules (`ex1I`, `ex1E` at lines 253--280) are currently proved directly for `Ex1` via its unfolded characterization rather than modularly factoring through dedicated `Only1I` / `Only1E` introduction and elimination lemmas (compare `additional.thy` in `article_isabelle_in_zfc` and `mylibrary.thy` in `YONEDA`). Adding dedicated `only1I`, `only1D`, and `only1E` rules to `my_IFOL.thy` will unify the uniqueness binder infrastructure across all three repositories.
2. **Single-Quantifier Expressibility (Tarski / Quine Single-Binder Reductions)**:
   - Exploring the repository's namesake theme (*"only one quantifier"*): formalizing in `my_IFOL.thy` how universal quantification $\forall$, existential quantification $\exists$, and uniqueness $!$ interact when a theory is restricted to a single primitive quantifier or single variable-binding operator (such as Hilbert's $\varepsilon$-operator or Tarski's single-quantifier reductions).
3. **Extending `quantifier_elim` to Presburger Arithmetic and Discrete Linear Orders**:
   - Extending `quantifier_elim/elimination.py` from Dense Linear Orders ($\mathsf{DLO}$) to discrete linear orders with successor ($(\mathbb{Z}, <, S)$) and Cooper's algorithm for Presburger arithmetic ($(\mathbb{Z}, 0, 1, +, <, \equiv_m)$).
