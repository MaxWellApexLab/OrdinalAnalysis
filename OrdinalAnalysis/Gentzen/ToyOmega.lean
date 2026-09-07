/-
  The toy instance of Gentzen's upper bound: transfinite induction below a
  standard numeral for the ordinary ordering `<` of the natural numbers
  (order type ω).

  This file exercises the whole pipeline of `Setup.lean` on the simplest
  ordering before the ordinal notations below ε₀ enter:

    for every `n : ℕ`,   `PA[X] ⊢ TIupto (<) (numeral n)`.

  The proof is semantic, in the idiom of `Idiom.lean`.  Fix an arbitrary model
  `M` of `PA[X]` and pass to `Structure.Model LX M`, which is how Foundation
  reads the arithmetic operations `0, 1, +, *, <` off an arbitrary structure as
  genuine Lean operations.  The resulting carrier `V` is a model of `PA⁻` (its
  arithmetic reduct is, and that reduct *is* Foundation's `standardModel V`),
  and the induction schema of `PA[X]` — which contains instances mentioning `X`
  — gives ordinary induction for the formula `∀ y < x, X y`.  From that,
  progressiveness of `X` for `<` forces `X` below every element, in particular
  below the value of `numeral n`.  Completeness then returns a derivation.

  The reusable skeleton for the real theorem is:

    `standardModel_eq_reduct`   Foundation's standard structure is the reduct
    `reduct_models_peanoMinus`  a `PA[X]`-model is a `PA⁻`-model
    `models_peanoMinus`         so Foundation's `PA⁻` lemma library applies
    `induction_eval`            the induction axiom of `PA[X]` at any formula,
                                with the numerals read as `0` and `x + 1`
    `prog_implies_below`        progressiveness ⇒ `X` holds below every point
    `models_TIupto`             `TIupto` holds in every model of `PA[X]`
    `paLX_proves_of_models_ORing`
                                completeness, landing in a model with genuine
                                arithmetic operations
    `toy`                       the theorem
-/
import OrdinalAnalysis.Gentzen.Idiom

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Gentzen

namespace ToyOmega

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.Idiom

/-! ### The ordering -/

/-- `y < x`, with `y` the innermost bound variable (`#0`), matching the
convention of `precAt`.  The `“…”` notation elaborates `<` to
`Semiformula.Operator.LT.lt.operator ![#0, #1]`, i.e. (by `lt_def`) to
`Semiformula.rel Language.LT.lt ![#0, #1]` with `Language.LT.lt : LX.Rel 2`
the `Sum.inl` of arithmetic's `<`. -/
def ltFormula : Semiformula LX ℕ 2 := “#0 < #1”

/-! ### Arithmetic on the carrier of a `PA[X]`-model

Foundation's `PA⁻` library is stated for `[ORingStructure V]` with the
*standard* structure `standardModel V`.  A `PA[X]`-model `V` whose
`LX`-structure is compatible with `0, 1, +, *, <, =` on `V` (that is,
`[Structure.ORing LX V]`) has `standardModel V` equal to its arithmetic reduct,
so everything transfers.  `Structure.Model LX M` is such a `V` for every model
`M`; that is the whole point of passing to it in `toy` below. -/

section Arithmetic

variable {V : Type*} [ORingStructure V] [sV : Structure LX V] [Structure.ORing LX V]

@[simp] lemma eval_ltFormula (y x : V) (f : ℕ → V) :
    ltFormula.Eval ![y, x] f ↔ y < x := by
  simp [ltFormula]

/-- Foundation's standard `ℒₒᵣ`-structure on the carrier coincides with the
arithmetic reduct of the `LX`-structure.

Three elaboration hazards, none of them mathematical.  (i) The hypotheses of
`standardModel_unique'` are elaborated against its *explicit* argument `s`, so
`s` has to be introduced as a local instance first — otherwise Lean re-synthesises
`Structure ℒₒᵣ V` and picks `standardModel V`.  (ii) With `s` in place,
`Add`/`Mul`/`Eq`/`LT` hold definitionally, because `(Language.Add.add : LX.Func 2)`
*is* `Sum.inl Language.Add.add` and `Structure.lMap` is composition with
`toLX.func`.  (iii) `Zero`/`One` are not: the operator term is
`Semiterm.func Language.Zero.zero ![]`, whose value is
`Structure.func _ (fun i => Semiterm.val _ _ (![] i))`, and `Fin 0` has no eta,
so `Matrix.empty_eq` is needed to turn that argument back into `![]`. -/
lemma standardModel_eq_reduct : standardModel V = sV.lMap toLX := by
  let s : Structure ℒₒᵣ V := sV.lMap toLX
  have hZero : Structure.Zero ℒₒᵣ V := ⟨by
    simp only [Semiterm.Operator.val, Semiterm.Operator.Zero.term_eq, Semiterm.val_func,
      Matrix.empty_eq, s, Structure.lMap_func, Language.Hom.func_add₁]
    exact Structure.zero_eq_of_lang (L := LX) ![]⟩
  have hOne : Structure.One ℒₒᵣ V := ⟨by
    simp only [Semiterm.Operator.val, Semiterm.Operator.One.term_eq, Semiterm.val_func,
      Matrix.empty_eq, s, Structure.lMap_func, Language.Hom.func_add₁]
    exact Structure.one_eq_of_lang (L := LX) ![]⟩
  have hAdd : Structure.Add ℒₒᵣ V := ⟨Structure.Add.add (L := LX) (M := V)⟩
  have hMul : Structure.Mul ℒₒᵣ V := ⟨Structure.Mul.mul (L := LX) (M := V)⟩
  have hEq : Structure.Eq ℒₒᵣ V := ⟨Structure.Eq.eq (L := LX) (M := V)⟩
  have hLT : Structure.LT ℒₒᵣ V := ⟨Structure.LT.lt (L := LX) (M := V)⟩
  exact (standardModel_unique' V s hZero hOne hAdd hMul hEq hLT).symm

variable [Nonempty V]

omit [ORingStructure V] [Structure.ORing LX V] in
/-- The arithmetic reduct of a `PA[X]`-model satisfies `PA⁻`: the `PA⁻` half of
`paLX` is `Theory.lMap toLX 𝗣𝗔⁻`, and `Semiformula.models_lMap` strips the
translation.  (Stated for the reduct itself, so neither `ORingStructure V` nor
`Structure.ORing LX V` is used.) -/
lemma reduct_models_peanoMinus [V↓[LX] ⊧* paLX] :
    (sV.lMap toLX).toStruc ⊧* 𝗣𝗔⁻ := by
  refine ⟨?_⟩
  intro σ hσ
  have hmap : V↓[LX] ⊧ Semiformula.lMap toLX σ :=
    Theory.models (T := paLX) V
      (Set.mem_union_right _ (Set.mem_union_left _ ⟨σ, hσ, rfl⟩))
  exact Semiformula.models_lMap.mp hmap

/-- The carrier of a `PA[X]`-model, with Foundation's standard structure, is a
model of `PA⁻`; this unlocks Foundation's `PA⁻` lemma library (`not_neg`,
`le_iff_lt_succ`, `le_def`, and the ordered-semiring instances). -/
lemma models_peanoMinus [V↓[LX] ⊧* paLX] : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := by
  have h := reduct_models_peanoMinus (V := V)
  rw [← standardModel_eq_reduct] at h
  exact h

/-- The standard numeral evaluates to the cast of `n`.  Not needed for `toy`
(which holds for an arbitrary closed term), but it is what makes the statement
of `toy` mean what it should.  The `PA⁻` hypothesis has to be an instance
*binder*: `(n : V)` needs the `NatCast V` that `PA⁻` supplies, so it must be
available while the statement itself is elaborated.  Via `models_peanoMinus`
every `PA[X]`-model satisfies it. -/
lemma val_numeral [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (n : ℕ) (f : ℕ → V) :
    (Semiterm.numeral n : Semiterm LX ℕ 0).val ![] f = (n : V) := by
  simp [Semiterm.numeral, numeral_eq_natCast_app]

/-- The induction axiom of `PA[X]` at an arbitrary formula of `LX`, read in a
model whose arithmetic is genuine: `Idiom.paLX_induction` keeps the numerals as
term values because an arbitrary `Structure LX M` carries no `Zero M`/`Add M`;
here they reduce to `0` and `x + 1`. -/
lemma induction_eval [V↓[LX] ⊧* paLX] (φ : Semiformula LX ℕ 1) (f : ℕ → V) :
    φ.Eval ![0] f →
    (∀ x : V, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
    ∀ x : V, φ.Eval ![x] f := by
  have h : V↓[LX] ⊧ .univCl (succInd φ) :=
    Theory.models (T := paLX) V (succInd_mem_paLX φ)
  revert f
  simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
    Matrix.constant_eq_singleton] using h

/-- The core step, and the only place the induction schema of `PA[X]` is used:
if `X` is progressive for `<`, then `X` holds below every element.  The
induction is at the formula `below ltFormula = ∀ y < x, X y`, which mentions
`X` — an instance of `InductionScheme LX Set.univ` that is *not* an instance of
arithmetic induction. -/
theorem prog_implies_below [V↓[LX] ⊧* paLX] (f : ℕ → V)
    (hprog : ∀ x : V, (∀ y : V, y < x → Xrel V y) → Xrel V x) :
    ∀ x : V, ∀ y : V, y < x → Xrel V y := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_peanoMinus
  have key : ∀ x : V, (below ltFormula).Eval ![x] f := by
    apply induction_eval (below ltFormula) f
    · rw [eval_below]
      intro y hy
      simp only [eval_ltFormula] at hy
      exact (not_neg y hy).elim
    · intro x ih
      rw [eval_below] at ih ⊢
      simp only [eval_ltFormula] at ih ⊢
      intro y hy
      rcases le_def.mp (le_iff_lt_succ.mpr hy) with rfl | hlt
      · exact hprog y ih
      · exact ih y hlt
  intro x
  have hx := (eval_below ltFormula x f).mp (key x)
  simpa only [eval_ltFormula] using hx

/-- `TIupto (<) t` holds in every model of `PA[X]`, for every closed term `t`;
the bound plays no role, which is exactly why the ω case is the toy case. -/
theorem models_TIupto [V↓[LX] ⊧* paLX] (t : Semiterm LX ℕ 0) :
    V↓[LX] ⊧ (TIupto ltFormula t).univCl := by
  rw [models_iff]
  simp only [Semiformula.eval_univCl]
  intro f
  refine (eval_TIupto ltFormula t f).mpr ?_
  intro hprog
  simp only [eval_ltFormula] at hprog ⊢
  exact prog_implies_below f hprog (t.val ![] f)

end Arithmetic

/-! ### Completeness in the shape this file needs -/

/-- `Idiom.paLX_proves_of_models_eq` hands back a bare `Structure LX M`, which
carries no Lean-level `0, +, <`.  Foundation's fix is `Structure.Model LX M`:
an isomorphic copy on which the `LX`-operators *are* the Lean operations, so
that `ORingStructure` and `Structure.ORing LX` are available.  Elementary
equivalence transports the sentence back.

The universe instantiation `.{0, 0}` is what makes `M : Type 0`, so that
`Structure.Model LX M : Type 0` and no universe metavariable is left; the
packaged `Theory.Proof.complete_on_eq_models` cannot be used here for exactly
that reason. -/
theorem paLX_proves_of_models_ORing {σ : Sentence LX}
    (h : ∀ (V : Type) [ORingStructure V] [Nonempty V] [Structure LX V]
      [Structure.ORing LX V] [V↓[LX] ⊧* paLX], V↓[LX] ⊧ σ) :
    paLX ⊢ σ := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  have e : M ≡ₑ[LX] Structure.Model LX M := Structure.Model.elementaryEquiv LX M
  have hV : (Structure.Model LX M)↓[LX] ⊧* paLX := e.modelsTheory.mp hM
  exact e.models.mpr (h (Structure.Model LX M))

/-! ### The theorem -/

/-- Gentzen's upper bound for the ordering `<` of order type ω: for every `n`,
`PA[X]` proves transfinite induction for `<` below the standard numeral `n`.

`TIupto ltFormula t : Semiformula LX ℕ 0` is a formula with free variables of
type `ℕ` available (none occur here, but the type does not say so), not a
`Sentence LX = Semiformula LX Empty 0`, so the statement is its universal
closure — exactly as `Order.closedTI` does for the real order. -/
theorem toy (n : ℕ) :
    paLX ⊢ (TIupto ltFormula (Semiterm.numeral n)).univCl := by
  apply paLX_proves_of_models_ORing
  intro V _ _ _ _ _
  exact models_TIupto _

end ToyOmega

end Gentzen

end OrdinalAnalysis
