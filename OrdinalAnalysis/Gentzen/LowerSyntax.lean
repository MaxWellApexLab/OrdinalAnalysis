/-
  The *syntax* of `TI(≺)` at the coded ordering.

  Everything the lower-bound argument does to `TI precCode` is syntactic
  bookkeeping, and all of it is done once here so that no later file has to
  unfold `Setup.lean`'s definitions again:

  (a) **closedness** — `precCode` and every formula built from it by
      `precAt`/`below`/`Prog`/`TI`/`TIupto` at closed terms has no free
      variables.  That is what makes `univCl` a pure typing wrapper: the
      sentence `(TI precCode).univCl` and the formula `TI precCode` are the
      same object seen through `Rewriting.emb`.

  (b) **substitution normal forms** — the two substitution steps the
      ω-calculus performs (`omegaRule` on `below`, and then on the body of the
      resulting `∀¹`) written as equalities between formulas built from
      `precAt`/`Xat` at numerals.  Numerals are `Semiterm.Const`s, so every
      rewriting fixes them and the `bShift` bookkeeping collapses.

  (c) **de Morgan normal forms** — `∼(Prog precCode)` and `∼(below precCode)`
      as existentials, which is the shape the class `C` of the boundedness
      lemma has to be closed under.

  (d) **complexity** — closed forms for the cut-rank bookkeeping.

  Two traps from the pitfall notes govern the proofs below.

  * `XLang` is a `def`, so a symbol `Sum.inr XRel.X : LX.Rel 1` is only well
    typed after unfolding it at default transparency, and `simp`/`rw` refuse to
    traverse terms containing it: `rw [Semiformula.freeVariables_rel]` on
    `Xat t` fails with *"the target expression is not type-correct under the
    `implicit` transparency level"*.  `Idiom.lean` works around this for
    *evaluation* with its opaque `Xrel`.  For *syntax* the corresponding move is
    never to let `rw`/`simp` see `Semiformula.rel (Sum.inr XRel.X) ![t]` at
    all: `freeVariables_Xat`, `complexity_Xat` and `rew_Xat` below are stated
    with `Xat t` on the left and discharged by `rfl` or by a single `exact` of
    Foundation's arity-1 lemma — `exact`/`show` unify at *default*
    transparency and so go through where `rw` does not.  Afterwards every
    `simp` call matches on the head symbol `Xat` and never unfolds it.
  * `free` and `shift` are never commuted here; the only rewritings used are
    `Rew.subst` and `Rew.bShift`, and a composite is discharged in one
    `Rew.ext` rather than pushed through the quantifier by hand.

  A third, smaller trap: `fin_cases` is *not* in scope in this project (the
  relevant Mathlib tactic module is not transitively imported), so goals
  `∀ i : Fin 2, _` are split with `Fin.forall_fin_two` instead.
-/
import OrdinalAnalysis.Gentzen.Setup
import OrdinalAnalysis.Gentzen.CodedNotation
import OrdinalAnalysis.Gentzen.Idiom

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.LowerSyntax

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.CodedNotation

/-! ### Generic closedness and complexity lemmas

Statements about an arbitrary language.  Foundation has the `FVar?` analysis
(`Semiformula.fvar?_rew`, `Semiterm.fvar?_rew`) but not the two corollaries
used constantly below, nor the `lMap` counterpart of `complexity_rew`. -/

section Generic

variable {L : Language} {ξ : Type*} [DecidableEq ξ]

/-- A closed term stays closed under a rewriting whose bound-variable images
are closed. -/
theorem freeVariables_rew_term_eq_empty {n₁ n₂ : ℕ} (ω : Rew L ξ n₁ ξ n₂)
    {t : Semiterm L ξ n₁} (ht : t.freeVariables = ∅)
    (hb : ∀ i : Fin n₁, (ω #i).freeVariables = ∅) :
    (ω t).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiterm.fvar?_rew (ω := ω) (t := t) (x := x) hx with ⟨i, hi⟩ | ⟨z, hz, _⟩
  · rw [Semiterm.FVar?, hb i] at hi
    exact Finset.notMem_empty x hi
  · rw [Semiterm.FVar?, ht] at hz
    exact Finset.notMem_empty z hz

/-- A closed formula stays closed under a rewriting whose bound-variable images
are closed. -/
theorem freeVariables_rew_eq_empty {n₁ n₂ : ℕ} (ω : Rew L ξ n₁ ξ n₂)
    {φ : Semiformula L ξ n₁} (hφ : φ.freeVariables = ∅)
    (hb : ∀ i : Fin n₁, (ω #i).freeVariables = ∅) :
    (ω ▹ φ).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := ω) (φ := φ) (x := x) hx with ⟨i, hi⟩ | ⟨z, hz, _⟩
  · rw [Semiterm.FVar?, hb i] at hi
    exact Finset.notMem_empty x hi
  · rw [Semiformula.FVar?, hφ] at hz
    exact Finset.notMem_empty z hz

/-- `Rew.bShift` only touches bound variables. -/
@[simp] theorem freeVariables_bShift {n : ℕ} (t : Semiterm L ξ n) :
    (Rew.bShift t : Semiterm L ξ (n + 1)).freeVariables = t.freeVariables := by
  ext x
  exact Semiterm.fvar?_bShift

/-- Constants — in particular numerals — are closed terms. -/
@[simp] theorem freeVariables_const {n : ℕ} (c : Semiterm.Const L) :
    ((c : Semiterm L ξ n)).freeVariables = ∅ := by
  show (Rew.subst (![] : Fin 0 → Semiterm L ξ n) (Rew.emb c.term)).freeVariables = ∅
  exact freeVariables_rew_term_eq_empty _ Semiterm.freeVariables_emb (fun i => Fin.elim0 i)

end Generic

section GenericComplexity

variable {L₁ L₂ : Language} {ξ : Type*}

/-- A language map does not change the complexity of a formula.  Foundation has
`Semiformula.complexity_rew` but no `lMap` counterpart. -/
@[simp] theorem complexity_lMap {n : ℕ} (Φ : L₁ →ᵥ L₂) (φ : Semiformula L₁ ξ n) :
    (Semiformula.lMap Φ φ).complexity = φ.complexity := by
  induction φ using Semiformula.rec' <;> simp [*]

end GenericComplexity

/-! ### Numerals of `LX`

`numLX n` is the closed term `n̄`; it is the only term the ω-calculus ever
substitutes.  Both facts needed about it — that it is closed and that every
rewriting fixes it — are instances of the generic lemmas above. -/

/-- The `n`-th numeral of `LX`, as a closed term. -/
abbrev numLX (n : ℕ) : Semiterm LX ℕ 0 := Semiterm.numeral n

/-- **Every rewriting fixes a numeral**: numerals are constants.  This is the
lemma that removes all `bShift` bookkeeping from the substitution normal
forms. -/
@[simp] theorem rew_numeral {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) (k : ℕ) :
    ω (Semiterm.numeral k : Semiterm LX ℕ n₁) = (Semiterm.numeral k : Semiterm LX ℕ n₂) :=
  ω.const _

/-- Numerals are closed. -/
@[simp] theorem freeVariables_numeral {n : ℕ} (k : ℕ) :
    (Semiterm.numeral k : Semiterm LX ℕ n).freeVariables = ∅ :=
  freeVariables_const _

/-! ### The fresh predicate

Stated so that `rw`/`simp` never have to look at `Sum.inr XRel.X`. -/

/-- `X(t)` has exactly the free variables of `t`. -/
@[simp] theorem freeVariables_Xat {n : ℕ} (t : Semiterm LX ℕ n) :
    (Xat t).freeVariables = t.freeVariables := by
  ext x
  have h : (Xat t).FVar? x ↔ ∃ i : Fin 1, ((![t] : Fin 1 → Semiterm LX ℕ n) i).FVar? x :=
    Semiformula.fvar?_rel
  simpa using h

/-- `X(t)` is an atom. -/
@[simp] theorem complexity_Xat {n : ℕ} (t : Semiterm LX ℕ n) : (Xat t).complexity = 0 := rfl

/-- Rewriting commutes with `Xat`. -/
@[simp] theorem rew_Xat {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) (t : Semiterm LX ℕ n₁) :
    ω ▹ (Xat t) = Xat (ω t) :=
  Semiformula.rew_rel1 ω

/-! ### `precAt` -/

/-- `precAt` is a substitution instance, so its complexity is that of `prec`. -/
@[simp] theorem complexity_precAt (prec : Semiformula LX ℕ 2) {n : ℕ}
    (y x : Semiterm LX ℕ n) : (precAt prec y x).complexity = prec.complexity := by
  simp [precAt]

/-- Rewriting commutes with `precAt`, for any rewriting that fixes the free
variables: the two substitutions are composed in one `Rew.ext`, never pushed
through the quantifiers separately.

The hypothesis `hω` cannot be dropped.  `precAt prec y x = Rew.subst ![y,x] ▹ prec`
touches only bound variables, so a rewriting that *moves* a free variable of
`prec` would have to be reproduced on the right-hand side; every rewriting the
lower bound applies (`Rew.subst`, `Rew.bShift`, and the `q` of either) fixes
free variables. -/
theorem rew_precAt {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) (hω : ∀ z : ℕ, ω &z = &z)
    (prec : Semiformula LX ℕ 2) (y x : Semiterm LX ℕ n₁) :
    ω ▹ (precAt prec y x) = precAt prec (ω y) (ω x) := by
  have h : ω.comp (Rew.subst ![y, x]) = Rew.subst ![ω y, ω x] := by
    ext i
    case hb =>
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> simp [Rew.comp_app]
    case hf => simp [Rew.comp_app, hω]
  show (Rew.subst ![y, x] ▹ prec |> (Rewriting.app ω)) = Rew.subst ![ω y, ω x] ▹ prec
  rw [← TransitiveRewriting.comp_app, h]

/-- The instance used throughout: substitution commutes with `precAt`. -/
@[simp] theorem subst_precAt {n₁ n₂ : ℕ} (w : Fin n₁ → Semiterm LX ℕ n₂)
    (prec : Semiformula LX ℕ 2) (y x : Semiterm LX ℕ n₁) :
    (Rew.subst w) ▹ (precAt prec y x)
      = precAt prec (Rew.subst w y) (Rew.subst w x) :=
  rew_precAt _ (fun z => by simp) prec y x

/-- `Rew.bShift` commutes with `precAt` too. -/
@[simp] theorem bShift_precAt {n : ℕ} (prec : Semiformula LX ℕ 2)
    (y x : Semiterm LX ℕ n) :
    (Rew.bShift : Rew LX ℕ n ℕ (n + 1)) ▹ (precAt prec y x)
      = precAt prec (Rew.bShift y) (Rew.bShift x) :=
  rew_precAt _ (fun z => by simp) prec y x

/-- `precAt prec y x` is closed whenever `prec` and both terms are. -/
theorem freeVariables_precAt_eq_empty {prec : Semiformula LX ℕ 2}
    (hprec : prec.freeVariables = ∅) {n : ℕ} {y x : Semiterm LX ℕ n}
    (hy : y.freeVariables = ∅) (hx : x.freeVariables = ∅) :
    (precAt prec y x).freeVariables = ∅ := by
  refine freeVariables_rew_eq_empty _ hprec ?_
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · simpa using hy
  · simpa using hx

/-! ### (b) Substitution normal forms

The ω-calculus reaches `below prec` only through `omegaRule`, which substitutes
a numeral for the outer bound variable, and then reaches the body of the
resulting `∀¹` through a second `omegaRule`.  These are exactly those two
steps. -/

/-- One substitution into `below`.  The `bShift` produced by `Rew.q_subst` is
displayed explicitly; at a numeral it collapses (next lemma). -/
theorem subst_below (prec : Semiformula LX ℕ 2) (t : Semiterm LX ℕ 0) :
    (below prec)/[t] =
      ∀¹ (∼(precAt prec (#0 : Semiterm LX ℕ 1) (Rew.bShift t)) ⋎
          Xat (#0 : Semiterm LX ℕ 1)) := by
  simp [below, Rew.q_subst]

/-- The same at a numeral: `bShift` is the identity on numerals, so the result
is literally `∀ y (∼(y ≺ n̄) ⋎ X y)`. -/
@[simp] theorem subst_below_numeral (prec : Semiformula LX ℕ 2) (k : ℕ) :
    (below prec)/[numLX k] =
      ∀¹ (∼(precAt prec (#0 : Semiterm LX ℕ 1) (Semiterm.numeral k)) ⋎
          Xat (#0 : Semiterm LX ℕ 1)) := by
  rw [subst_below]
  simp

/-- The second substitution: the body of `(below prec)/[n̄]`, at a numeral. -/
@[simp] theorem subst_belowBody_numeral (prec : Semiformula LX ℕ 2) (k m : ℕ) :
    (∼(precAt prec (#0 : Semiterm LX ℕ 1) (Semiterm.numeral k)) ⋎
      Xat (#0 : Semiterm LX ℕ 1))/[numLX m] =
      ∼(precAt prec (numLX m) (numLX k)) ⋎ Xat (numLX m) := by
  simp

/-- `X(#0)` under a substitution. -/
@[simp] theorem subst_Xat_bvar (t : Semiterm LX ℕ 0) :
    (Xat (#0 : Semiterm LX ℕ 1))/[t] = Xat t := by
  simp

/-- The instance actually used: `(X #0)/[n̄] = X n̄`. -/
theorem subst_Xat_bvar_numeral (k : ℕ) :
    (Xat (#0 : Semiterm LX ℕ 1))/[numLX k] = Xat (numLX k) :=
  subst_Xat_bvar _

/-! ### (c) De Morgan normal forms -/

/-- `∼(∀ y ≺ x, X y) = ∃ y (y ≺ x ⋏ ∼X y)`. -/
theorem neg_below (prec : Semiformula LX ℕ 2) :
    ∼(below prec) =
      ∃¹ ((precAt prec (#0 : Semiterm LX ℕ 2) #1) ⋏ ∼(Xat (#0 : Semiterm LX ℕ 2))) := by
  simp [below]

/-- `∼Prog(≺) = ∃ x ((∀ y ≺ x, X y) ⋏ ∼X x)` — the premise shape of the `exs`
case in the boundedness lemma. -/
theorem neg_Prog (prec : Semiformula LX ℕ 2) :
    ∼(Prog prec) =
      ∃¹ ((below prec) ⋏ ∼(Xat (#0 : Semiterm LX ℕ 1))) := by
  simp [Prog]

/-! ### (a) Closedness -/

/-- `precCode` is X-free *and* closed: it is the `lMap`-image of the `emb` of an
arithmetic sentence, and both operations kill free variables. -/
@[simp] theorem freeVariables_precCode : precCode.freeVariables = ∅ := by
  simp [precCode, liftCode]

section Closed

variable {prec : Semiformula LX ℕ 2}

/-- `below prec` is closed when `prec` is. -/
theorem freeVariables_below (hprec : prec.freeVariables = ∅) :
    (below prec).freeVariables = ∅ := by
  have h : (precAt prec (#0 : Semiterm LX ℕ 2) #1).freeVariables = ∅ :=
    freeVariables_precAt_eq_empty hprec (by simp) (by simp)
  simp [below, h]

/-- `Prog prec` is closed when `prec` is. -/
theorem freeVariables_Prog (hprec : prec.freeVariables = ∅) :
    (Prog prec).freeVariables = ∅ := by
  have h := freeVariables_below hprec
  simp [Prog, h]

/-- `TI prec` is closed when `prec` is. -/
theorem freeVariables_TI (hprec : prec.freeVariables = ∅) :
    (TI prec).freeVariables = ∅ := by
  have h := freeVariables_Prog hprec
  simp [TI, h]

/-- `TIupto prec t` is closed when `prec` and the bound `t` are. -/
theorem freeVariables_TIupto (hprec : prec.freeVariables = ∅)
    {t : Semiterm LX ℕ 0} (ht : t.freeVariables = ∅) :
    (TIupto prec t).freeVariables = ∅ := by
  have hp := freeVariables_Prog hprec
  have h : (precAt prec (#0 : Semiterm LX ℕ 1) (Rew.bShift t)).freeVariables = ∅ :=
    freeVariables_precAt_eq_empty hprec (by simp) (by simpa using ht)
  simp [TIupto, hp, h]

end Closed

/-! The instances at the coded ordering. -/

@[simp] theorem freeVariables_precAt_precCode {n : ℕ} {y x : Semiterm LX ℕ n}
    (hy : y.freeVariables = ∅) (hx : x.freeVariables = ∅) :
    (precAt precCode y x).freeVariables = ∅ :=
  freeVariables_precAt_eq_empty freeVariables_precCode hy hx

@[simp] theorem freeVariables_below_precCode : (below precCode).freeVariables = ∅ :=
  freeVariables_below freeVariables_precCode

@[simp] theorem freeVariables_Prog_precCode : (Prog precCode).freeVariables = ∅ :=
  freeVariables_Prog freeVariables_precCode

@[simp] theorem freeVariables_TI_precCode : (TI precCode).freeVariables = ∅ :=
  freeVariables_TI freeVariables_precCode

@[simp] theorem freeVariables_TIupto_precCode {t : Semiterm LX ℕ 0}
    (ht : t.freeVariables = ∅) : (TIupto precCode t).freeVariables = ∅ :=
  freeVariables_TIupto freeVariables_precCode ht

/-! ### `univCl` is a typing wrapper

`Semiformula.univCl φ = (φ.univCl').toEmpty _` and `Semiformula.univCl'_eq_self_of`
makes `univCl'` the identity on closed formulas.  So the sentence
`(TI precCode).univCl` and the formula `TI precCode` are the same object seen
through the coercion `Rewriting.emb : Sentence LX → Proposition LX`, and since
that coercion is injective (`Semiformula.coe_inj`) the two levels are
interchangeable. -/

/-- `univCl'` is the identity on `TI precCode`. -/
theorem univCl'_TI_precCode : (TI precCode).univCl' = TI precCode :=
  Semiformula.univCl'_eq_self_of _ freeVariables_TI_precCode

/-- **The interchange lemma.**  Embedding the sentence `(TI precCode).univCl`
back into `Semiformula LX ℕ 0` returns `TI precCode` on the nose. -/
@[simp] theorem emb_univCl_TI_precCode :
    (Rewriting.emb ((TI precCode).univCl) : Semiformula LX ℕ 0) = TI precCode := by
  have h : ((TI precCode).univCl : Semiformula LX ℕ 0) = (TI precCode).univCl' :=
    Semiformula.coe_univCl_eq_univCl' _
  rw [show (Rewriting.emb ((TI precCode).univCl) : Semiformula LX ℕ 0)
        = ((TI precCode).univCl : Semiformula LX ℕ 0) from rfl, h, univCl'_TI_precCode]

/-- The same fact in `toEmpty` form: `univCl` merely retypes `TI precCode`. -/
theorem TI_univCl_eq :
    (TI precCode).univCl = (TI precCode).toEmpty freeVariables_TI_precCode := by
  apply (Semiformula.coe_inj _ _).mp
  rw [emb_univCl_TI_precCode, Semiformula.emb_toEmpty]

/-! ### (d) Complexity

Cut-rank bookkeeping: everything is `prec.complexity` plus a small constant. -/

@[simp] theorem complexity_below (prec : Semiformula LX ℕ 2) :
    (below prec).complexity = prec.complexity + 2 := by
  simp [below]

@[simp] theorem complexity_Prog (prec : Semiformula LX ℕ 2) :
    (Prog prec).complexity = prec.complexity + 4 := by
  simp [Prog]

@[simp] theorem complexity_TI (prec : Semiformula LX ℕ 2) :
    (TI prec).complexity = prec.complexity + 5 := by
  simp [TI]

@[simp] theorem complexity_TIupto (prec : Semiformula LX ℕ 2) (t : Semiterm LX ℕ 0) :
    (TIupto prec t).complexity = prec.complexity + 5 := by
  simp [TIupto]

/-- The complexity of `precCode` is that of the arithmetic graph formula
`precDef`: neither `Rewriting.emb` nor `lMap toLX` changes it. -/
@[simp] theorem complexity_precCode :
    precCode.complexity = (precDef.val : ArithmeticSemisentence 2).complexity := by
  simp [precCode, liftCode]

/-- Closed form for the target formula of the lower bound. -/
theorem complexity_TI_precCode :
    (TI precCode).complexity = (precDef.val : ArithmeticSemisentence 2).complexity + 5 := by
  simp

end OrdinalAnalysis.Gentzen.LowerSyntax
