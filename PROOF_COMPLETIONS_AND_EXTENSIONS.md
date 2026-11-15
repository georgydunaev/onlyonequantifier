# Proof Completions and Mathematical Extensions: onlyonequantifier

## 1. Overview of Phase 2 Completions

This document and its companion Isabelle/Pure theory [UniquenessAndSingleBinder.thy](file:///botworkspace/onlyonequantifier/UniquenessAndSingleBinder.thy) complete the open mathematical investigations identified in [MANUSCRIPT_AND_PROOF_INDEX.md](file:///botworkspace/onlyonequantifier/MANUSCRIPT_AND_PROOF_INDEX.md) for `onlyonequantifier`.

---

## 2. Factorization of Unique Existence via the Uniqueness Quantifier `Only1` (`!x. P(x)`)

In standard Isabelle `IFOL`, unique existence $\exists!x.\,P(x)$ is defined monolithically as $\exists x.\,P(x) \land (\forall y.\,P(y) \longrightarrow y = x)$. In [my_IFOL.thy](file:///botworkspace/onlyonequantifier/my_IFOL.thy) (lines 90--95 and 311--412), Georgy Dunaev isolates the **uniqueness quantifier** (`Only1`, binder syntax `!x. P(x)`):
$$!x.\,P(x) \equiv \forall x\,\forall y.\,P(x) \land P(y) \longrightarrow x = y,$$
defines unique existence as the conjunction of existence and uniqueness (`ex1new_def`):
$$\exists!x.\,P(x) \equiv (\exists x.\,P(x)) \land (!x.\,P(x)),$$
and derives the classical monolithic characterization `ex1_def` as a theorem (`by (rule iff_reflection, rule iffI, erule ex1unfold, erule ex1fold)` at line 410) from `only1I`, `only1D`, `only1E`, and `only1rearr`.

---

## 3. Structural Laws of `Only1` and Its Dual (`UniquenessAndSingleBinder.thy`)

In [UniquenessAndSingleBinder.thy](file:///botworkspace/onlyonequantifier/UniquenessAndSingleBinder.thy), we extend `my_IFOL.thy` with four structural theorems governing `!x. P(x)`:

1. **Vacuous Uniqueness (`lemma only1_vacuous`)**:
   $$\left(\forall x.\,\neg P(x)\right) \implies !x.\,P(x).$$
   An empty predicate vacuously satisfies at-most-one uniqueness.
2. **Singleton Uniqueness (`lemma only1_singleton_eq`)**:
   $$!x.\,(x = a)$$
   proved directly from transitivity (`trans`) and symmetry (`sym`) of equality.
3. **Antimonotonicity / Downward Closure (`lemma only1_antimono` and `lemma only1_conj_left`)**:
   $$\left(\bigwedge x.\,P(x) \implies Q(x)\right) \implies (!x.\,Q(x)) \implies (!x.\,P(x)), \qquad (!x.\,P(x)) \implies !x.\,(P(x) \land Q(x)).$$
   Uniqueness is contravariant (downward-closed) under predicate implication: any sub-predicate of a unique predicate is itself unique.
4. **Duality with `?x. P(x)` from `YONEDA/yoneda.tex` (`lemma only1_dual_stable`)**:
   In `yoneda.tex` (Section 1.2, lines 97--103), the dual quantifier is defined as $?x.\,P(x) \equiv \neg(!x.\,\neg P(x))$, with the exercise $!x.\,P(x) \iff \neg(?x.\,\neg P(x))$. In `UniquenessAndSingleBinder.thy`, we formalize `DualOnly1` inside intuitionistic first-order logic `my_IFOL` and prove that for double-negation stable predicates ($\neg\neg P(x) \implies P(x)$), $!x.\,P(x) \implies \neg \mathrm{DualOnly1}(\lambda x.\,\neg P(x))$.
