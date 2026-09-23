/-
  The image of `InductionScheme LX Set.univ`.

  Foundation's induction axiom is `univCl (succInd φ)` — a conjunction-free
  statement with two *nested* implications; `LK.lean`'s `indBody` uses a single
  conjunctive hypothesis.  `indBodyC` is the curried form, and
  `Combinators.lean`'s `allNums_curry` bridges the two *under* the `∀¹`-closure
  that `univCl` introduces.

  The route: `ofAxiom (indScheme₂_mem_ACA …)` → `specSets` at the arithmetical
  witnesses → `subst₁_allNums` → `app_indBody` → `subst₁_toSOAtB` →
  `allNums_curry` → the image identity (`coe_univCl_eq_univCl'`,
  `toSOAtB_allClosure`, `toSOAtB_rew` at `Rew.fixitr 0 m`, `toSOAtB_succInd`,
  `rew_indBodyC`).
-/
import OrdinalAnalysis.ACA.Combinators
import OrdinalAnalysis.ACA.Translate

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX XRel Xat toLX paLX)

/-! ### The two numerals of Foundation's induction matrix

`Semiterm.numeral` is built from `Operator.numeral`, i.e. from a `Rew.subst`
applied to a closed operator term, so neither `unTerm ‘0’ = ‘0’` nor
`unTerm ‘#0 + 1’ = ‘#0 + 1’` is `rfl`: the two sides are terms of *different*
languages built from *different* `Zero`/`One`/`Add` instances.  The route that
does work is to exhibit the `LX`-term as the `toLX`-image of the `ℒₒᵣ`-term and
then apply `unTerm_lMap`. -/

/-- `‘0’` of `LX` is the `toLX`-image of `‘0’` of `ℒₒᵣ`. -/
private theorem lMap_numeral_zero {ξ : Type*} {n : ℕ} :
    FirstOrder.Semiterm.lMap toLX (‘0’ : FirstOrder.Semiterm ℒₒᵣ ξ n) =
      (‘0’ : FirstOrder.Semiterm LX ξ n) := by
  simp [FirstOrder.Semiterm.numeral, FirstOrder.Semiterm.Operator.numeral,
    FirstOrder.Semiterm.Operator.const, FirstOrder.Semiterm.Operator.operator,
    FirstOrder.Semiterm.Operator.Zero.term_eq, FirstOrder.Rew.func]

/-- `‘#0 + 1’` of `LX` is the `toLX`-image of `‘#0 + 1’` of `ℒₒᵣ`. -/
private theorem lMap_succ_bvar {ξ : Type*} {n : ℕ} :
    FirstOrder.Semiterm.lMap toLX (‘#0 + 1’ : FirstOrder.Semiterm ℒₒᵣ ξ (n + 1)) =
      (‘#0 + 1’ : FirstOrder.Semiterm LX ξ (n + 1)) := by
  simp [FirstOrder.Semiterm.numeral, FirstOrder.Semiterm.Operator.numeral,
    FirstOrder.Semiterm.Operator.const, FirstOrder.Semiterm.Operator.operator,
    FirstOrder.Semiterm.Operator.One.term_eq,
    FirstOrder.Semiterm.Operator.Add.term_eq, FirstOrder.Rew.func]
  funext i
  cases i using Fin.cases with
  | zero => simp [Function.comp_def]
  | succ j =>
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      simp [Function.comp_def, Matrix.empty_eq]

/-- **`unTerm ‘0’ = ‘0’`.** -/
@[simp] theorem unTerm_numeral_zero {ξ : Type*} {n : ℕ} :
    unTerm (‘0’ : FirstOrder.Semiterm LX ξ n) = (‘0’ : FirstOrder.Semiterm ℒₒᵣ ξ n) := by
  rw [← lMap_numeral_zero]
  exact unTerm_lMap _

/-- **`unTerm ‘#0 + 1’ = ‘#0 + 1’`.** -/
@[simp] theorem unTerm_succ_bvar {ξ : Type*} {n : ℕ} :
    unTerm (‘#0 + 1’ : FirstOrder.Semiterm LX ξ (n + 1)) =
      (‘#0 + 1’ : FirstOrder.Semiterm ℒₒᵣ ξ (n + 1)) := by
  rw [← lMap_succ_bvar]
  exact unTerm_lMap _

/-! ### The curried induction body -/

/-- The **curried** induction body: Foundation's `succInd` shape. -/
def indBodyC {N n : ℕ} (φ : Semiproposition ℒₒᵣ N (n + 1)) : Semiproposition ℒₒᵣ N n :=
  (FirstOrder.Rew.subst (indZeroSub n) ▹ φ) 🡒
    ((∀¹ (φ 🡒 FirstOrder.Rew.subst (indSuccSub n) ▹ φ)) 🡒 (∀¹ φ))

/-- **`indBody` curried.**  `LK.lean`'s `indBody φ` is literally `(Z ⋏ S) 🡒 A`
and `indBodyC φ` is `Z 🡒 (S 🡒 A)`, so `allNums_curry` applies verbatim. -/
theorem provable_allNums_indBodyC {𝓢 : Set (Proposition ℒₒᵣ)}
    (h𝓢 : ∀ χ ∈ 𝓢, Semiproposition.shift₀ χ = χ) {n : ℕ}
    {φ : Semiproposition ℒₒᵣ 0 (n + 1)} (h : Provable 𝓢 (allNums (indBody φ))) :
    Provable 𝓢 (allNums (indBodyC φ)) :=
  allNums_curry h𝓢 h

/-- **A number-variable rewriting slides through `indBodyC`** — the curried
counterpart of `LK.lean`'s `rew_indBody`, with the same two composite
identities. -/
theorem rew_indBodyC {N n₁ n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    (φ : Semiproposition ℒₒᵣ N (n₁ + 1)) :
    ω ▹ indBodyC φ = indBodyC (ω.q ▹ φ) := by
  have ha : ω.comp (FirstOrder.Rew.subst (indZeroSub n₁)) =
      (FirstOrder.Rew.subst (indZeroSub n₂)).comp ω.q := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [FirstOrder.Rew.comp_app, zeroT]
      | succ i => simp [FirstOrder.Rew.comp_app]
    · simp [FirstOrder.Rew.comp_app]
  have hb : ω.q.comp (FirstOrder.Rew.subst (indSuccSub n₁)) =
      (FirstOrder.Rew.subst (indSuccSub n₂)).comp ω.q := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [FirstOrder.Rew.comp_app, succT]
      | succ i => simp [FirstOrder.Rew.comp_app]
    · simp [FirstOrder.Rew.comp_app]
  show ω ▹ ((FirstOrder.Rew.subst (indZeroSub n₁) ▹ φ) 🡒
      ((∀¹ (φ 🡒 FirstOrder.Rew.subst (indSuccSub n₁) ▹ φ)) 🡒 (∀¹ φ))) = _
  rw [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_imply,
    Semiformula.rew_all₀, Semiformula.rew_all₀, LogicalConnective.HomClass.map_imply,
    ← FirstOrder.TransitiveRewriting.comp_app, ← FirstOrder.TransitiveRewriting.comp_app,
    ha, hb, FirstOrder.TransitiveRewriting.comp_app, FirstOrder.TransitiveRewriting.comp_app]
  rfl

/-! ### The image of the induction scheme -/

variable {N : ℕ} {ψ : Semiformula ℒₒᵣ ℕ Empty N 1}

/-- **The image of Foundation's induction matrix.** -/
theorem toSOAtB_succInd {N : ℕ} (ψ : Semiformula ℒₒᵣ ℕ Empty N 1)
    (φ : FirstOrder.Semiformula LX ℕ 1) :
    toSOAtB ψ (FirstOrder.Arithmetic.succInd φ) = indBodyC (toSOAtB ψ φ) := by
  show toSOAtB ψ (φ/[(‘0’ : FirstOrder.Semiterm LX ℕ 0)] 🡒
      ((∀¹ (φ/[(#0 : FirstOrder.Semiterm LX ℕ 1)] 🡒
        φ/[(‘#0 + 1’ : FirstOrder.Semiterm LX ℕ 1)])) 🡒 ∀¹ (φ/[#0]))) = _
  have h0 : indZeroSub 0 = ![unTerm (‘0’ : FirstOrder.Semiterm LX ℕ 0)] := by
    rw [unTerm_numeral_zero]
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => exact j.elim0
  have h1 : indSuccSub 0 = ![unTerm (‘#0 + 1’ : FirstOrder.Semiterm LX ℕ 1)] := by
    rw [unTerm_succ_bvar]
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => exact j.elim0
  simp only [toSOAtB_imply, toSOAtB_all, toSOAtB_subst₁, unTerm_bvar,
    FirstOrder.Rewriting.subst1_bvar0_eq]
  unfold indBodyC
  rw [h0, h1]
  simp [FirstOrder.Rewriting.subst1_bvar0_eq]

/-- A free variable of `φ` is one of `succInd φ`. -/
private theorem fvar?_succInd {φ : FirstOrder.Semiformula LX ℕ 1} {x : ℕ}
    (h : φ.FVar? x) : (FirstOrder.Arithmetic.succInd φ).FVar? x := by
  show (φ/[(‘0’ : FirstOrder.Semiterm LX ℕ 0)] 🡒
      ((∀¹ (φ/[(#0 : FirstOrder.Semiterm LX ℕ 1)] 🡒
        φ/[(‘#0 + 1’ : FirstOrder.Semiterm LX ℕ 1)])) 🡒 ∀¹ (φ/[#0]))).FVar? x
  simp only [FirstOrder.Rewriting.subst1_bvar0_eq]
  simp [LogicalConnective.DeMorgan.imply, h]

/-- `Rew.fixitr 0 m` binds every free variable below `m`, so the result is
fixed by `shift`. -/
private theorem shift_fixitr_q {φ : FirstOrder.Semiformula LX ℕ 1} {m : ℕ}
    (hm : ∀ x, φ.FVar? x → x < m) :
    FirstOrder.Rewriting.shift ((FirstOrder.Rew.fixitr 0 m).q ▹ φ) =
      (FirstOrder.Rew.fixitr 0 m).q ▹ φ := by
  show FirstOrder.Rew.shift ▹ ((FirstOrder.Rew.fixitr 0 m).q ▹ φ) = _
  rw [← FirstOrder.TransitiveRewriting.comp_app]
  refine FirstOrder.Semiformula.rew_eq_of_funEqOn ?_ ?_
  · intro x
    cases x using Fin.cases with
    | zero => simp [FirstOrder.Rew.comp_app]
    | succ i => exact i.elim0
  · intro x hx
    have hlt : x < m := hm x hx
    simp [FirstOrder.Rew.comp_app, FirstOrder.Rew.fixitr_fvar, hlt]

/-- `unTerm` commutes with `Rew.fixitr` on free variables. -/
private theorem unTerm_fixitr (m : ℕ) (x : ℕ) :
    unTerm ((FirstOrder.Rew.fixitr 0 m : FirstOrder.Rew LX ℕ 0 ℕ (0 + m)) (&x)) =
      (FirstOrder.Rew.fixitr 0 m : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ (0 + m)) (&x) := by
  rw [FirstOrder.Rew.fixitr_fvar, FirstOrder.Rew.fixitr_fvar]
  split <;> rfl

/-- **The image of `InductionScheme LX Set.univ`.**  `ψ`'s set parameters stay
in bound slots for the length of the argument, so the image really is an
`ACA`-axiom; `specSets` puts the parameters back at the witnesses `Φ`. -/
theorem image_indScheme {N : ℕ} (ψ : Semiformula ℒₒᵣ ℕ Empty N 1)
    (hns : NoSetFvar (FirstOrder.Rewriting.emb ψ : Semiproposition ℒₒᵣ N 1))
    (Φ : Fin N → Semiformula ℒₒᵣ ℕ Empty 0 1)
    (hΦ : ∀ i, Arith (FirstOrder.Rewriting.emb (Φ i) : Semiformula ℒₒᵣ ℕ ℕ 0 1))
    (φ : FirstOrder.Semiformula LX ℕ 1) :
    Provable ACA (toSOAt (Semiproposition.subst₁ ψ Φ)
      (FirstOrder.Rewriting.emb (FirstOrder.Semiformula.univCl
        (FirstOrder.Arithmetic.succInd φ)))) := by
  have hm : ∀ x, φ.FVar? x → x < (FirstOrder.Arithmetic.succInd φ).fvSup :=
    fun x hx => FirstOrder.Semiformula.lt_fvSup_of_fvar? (fvar?_succInd hx)
  set m := (FirstOrder.Arithmetic.succInd φ).fvSup with hmdef
  set θ : FirstOrder.Semiformula LX ℕ (0 + m + 1) :=
    (FirstOrder.Rew.fixitr 0 m).q ▹ φ with hθ
  have hns' : NoSetFvar (toSOAtB ψ θ) := noSetFvar_toSOAtB hns θ
  have hsh : Semiproposition.shift₀ (toSOAtB ψ θ) = toSOAtB ψ θ := by
    show FirstOrder.Rewriting.shift (toSOAtB ψ θ) = _
    rw [← toSOAtB_shift, hθ, shift_fixitr_q hm]
  have hax : Provable ACA (indScheme₂ (toSOAtB ψ θ)) :=
    ofAxiom (indScheme₂_mem_ACA hns' hsh)
  have h1 : Provable ACA (Semiproposition.subst₁ (allNums (indBody (toSOAtB ψ θ)))
      (fun i => FirstOrder.Rewriting.emb (Φ i))) :=
    specSets _ _ (fun i => hΦ i) hax
  have e1 : Semiproposition.subst₁ (allNums (indBody (toSOAtB ψ θ)))
      (fun i => FirstOrder.Rewriting.emb (Φ i)) =
      allNums (indBody (toSOAt (Semiproposition.subst₁ ψ Φ) θ)) := by
    show (SecondOrder.Rew.subst (fun i => FirstOrder.Rewriting.emb (Φ i))).app
      (allNums (indBody (toSOAtB ψ θ))) = _
    rw [subst₁_allNums]
    congr 1
    show (SecondOrder.Rew.subst (fun i => FirstOrder.Rewriting.emb (Φ i))).app
      (indBody (toSOAtB ψ θ)) = _
    rw [app_indBody]
    congr 1
    exact subst₁_toSOAtB Φ θ
  rw [e1] at h1
  have h2 := provable_allNums_indBodyC ACA_shift₀_invariant h1
  have himg : toSOAt (Semiproposition.subst₁ ψ Φ)
      (FirstOrder.Rewriting.emb (FirstOrder.Semiformula.univCl
        (FirstOrder.Arithmetic.succInd φ))) =
      allNums (indBodyC (toSOAt (Semiproposition.subst₁ ψ Φ) θ)) := by
    rw [show (FirstOrder.Rewriting.emb (FirstOrder.Semiformula.univCl
          (FirstOrder.Arithmetic.succInd φ)) : FirstOrder.Proposition LX) =
        (FirstOrder.Arithmetic.succInd φ).univCl' from by simp]
    show toSOAtB (Semiproposition.subst₁ ψ Φ)
      (∀¹* ((FirstOrder.Rew.fixitr 0 m : FirstOrder.Rew LX ℕ 0 ℕ (0 + m)) ▹
        FirstOrder.Arithmetic.succInd φ)) = _
    rw [toSOAtB_allClosure]
    congr 1
    rw [toSOAtB_rew (ω := (FirstOrder.Rew.fixitr 0 m : FirstOrder.Rew LX ℕ 0 ℕ (0 + m)))
        (ω' := (FirstOrder.Rew.fixitr 0 m : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ (0 + m)))
        (fun i => i.elim0) (unTerm_fixitr m),
      toSOAtB_succInd, rew_indBodyC]
    congr 1
    exact (toSOAtB_rew (q_hb (ω := (FirstOrder.Rew.fixitr 0 m : FirstOrder.Rew LX ℕ 0 ℕ (0 + m)))
      (ω' := (FirstOrder.Rew.fixitr 0 m : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ (0 + m))) (fun i => i.elim0))
      (q_hf (unTerm_fixitr m)) φ).symm
  rw [himg]
  exact h2

end OrdinalAnalysis.ACA
