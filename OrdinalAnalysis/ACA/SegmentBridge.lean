/-
  **The bridge from
  `∀²X TI(≺₁, b̄, X)` to `tiUptoSegSO a`.**

  `ACA/Lifted.lean`'s `Relativise.concrete_tiUptoSeg_of_closedTI₁` performs the
  relativisation from `≺₁` to the `ε_{ε₀}`-segment ordering, but it consumes a
  `paLX`-*derivation* of transfinite induction for the guarded formula.  The
  output of the `(Prog)`/`(TIψ)` half of the argument is not a `paLX`-derivation
  — it is an `ACA`-derivation of a `Π¹₁` statement.  So the relativisation has to
  be available as an *implication inside `paLX`*, which can then be lifted and
  used with modus ponens.  That is `concrete_relImp` below; the rest of the file
  wires it to the second-order layer.

  With this in place the remaining gap in `|ACA| = ε_{ε₀}` is exactly design-note
  item (Prog): `aca_upper_bound_of_ti_epsilon` turns one `ACA`-proof of
  `∀²X TI(≺₁, ε̄_c, X)` per external `c < ε₀` into the full upper half.
-/
import OrdinalAnalysis.ACA.TowerInduction

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Layer 1: the relativisation as a `paLX`-implication -/

namespace OrdinalAnalysis.ACA.SegBridge

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.CodedVeblen
open OrdinalAnalysis.Gentzen.CodedVeblenJump
open OrdinalAnalysis.Gentzen.Epsilon1UpperBound
open OrdinalAnalysis.Gentzen.EpsilonSegmentOrder
open OrdinalAnalysis.Gentzen.Order (precTransStatement models_precTransStatement)
open OrdinalAnalysis.Gamma0Note (epsilonNote)
open OrdinalAnalysis.ACA.Relativise (segGuard segBound)

private theorem val_numeral_eq {M : Type*} [Nonempty M] [Structure LX M] (k : ℕ) {n : ℕ}
    (e : Fin n → M) (f : ℕ → M) :
    (Semiterm.numeral k : Semiterm LX ℕ n).val e f =
      (Semiterm.numeral k : Semiterm LX ℕ 0).val ![] f := by
  simp

@[simp] theorem freeVariables_segGuard : segGuard.freeVariables = ∅ := by
  have h : (precAt precCode₁ (#0 : Semiterm LX ℕ 1)
      (Semiterm.numeral segBound)).freeVariables = ∅ :=
    LowerSyntax.freeVariables_precAt_eq_empty freeVariables_precCode₁ (by simp) (by simp)
  show (∼(precAt precCode₁ (#0 : Semiterm LX ℕ 1) (Semiterm.numeral segBound)) ⋎
    Xat (#0 : Semiterm LX ℕ 1)).freeVariables = ∅
  simp [h]

/-- The matrix of the relativisation implication. -/
noncomputable def relImpBody (a b : Semiterm LX ℕ 0) : Semiformula LX ℕ 0 :=
  ∼(tiUptoAt precCode₁ segGuard b) ⋎
    tiUptoAt OrdinalAnalysis.ACA.precSeg (Xat (#0 : Semiterm LX ℕ 1)) a

/-- **The relativisation, as an implication inside `paLX`.** -/
noncomputable def relImpStatement (a b : Semiterm LX ℕ 0) : Sentence LX :=
  (relImpBody a b).univCl

theorem freeVariables_relImpBody {a b : Semiterm LX ℕ 0}
    (ha : a.freeVariables = ∅) (hb : b.freeVariables = ∅) :
    (relImpBody a b).freeVariables = ∅ := by
  have h1 : (tiUptoAt precCode₁ segGuard b).freeVariables = ∅ :=
    TowerSyntax.freeVariables_tiUptoAt freeVariables_precCode₁ freeVariables_segGuard hb
  have h2 : (tiUptoAt OrdinalAnalysis.ACA.precSeg (Xat (#0 : Semiterm LX ℕ 1))
      a).freeVariables = ∅ :=
    TowerSyntax.freeVariables_tiUptoAt (freeVariables_precCodeSeg (epsilonNote 0))
      (by simp) ha
  show (∼(tiUptoAt precCode₁ segGuard b) ⋎
    tiUptoAt OrdinalAnalysis.ACA.precSeg (Xat (#0 : Semiterm LX ℕ 1)) a).freeVariables = ∅
  simp [h1, h2]

/-- **The relativisation implication is a `paLX`-theorem** whenever `ā ≺₁ b̄`.

Same two uses of transitivity of `≺₁` as
`Lifted.Relativise.concrete_tiUptoSeg_of_closedTI₁`, but with the transfinite
induction for the guarded formula as a *hypothesis of the object-language
implication* rather than of the Lean theorem — which is what lets the
second-order layer discharge it with an `ACA`-derivation. -/
theorem concrete_relImp (a b : Semiterm LX ℕ 0) (hab : paLX ⊢ closedPrec₁ a b) :
    paLX ⊢ relImpStatement a b := by
  classical
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  have hTransM : M↓[LX] ⊧ precTransStatement precCode₁ :=
    consequence_iff_eq'.mp (Theory.Proof.sound concrete_precTrans₁) M
  have hTrans := (models_precTransStatement precCode₁).mp hTransM
  have habM : M↓[LX] ⊧ closedPrec₁ a b :=
    consequence_iff_eq'.mp (Theory.Proof.sound hab) M
  rw [models_iff] at habM
  simp only [closedPrec₁, Semiformula.eval_univCl, eval_precAt] at habM
  show M↓[LX] ⊧ (relImpBody a b).univCl
  rw [models_iff]
  simp only [relImpBody, Semiformula.eval_univCl, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq, eval_tiUptoAt]
  intro f
  -- the two evaluation normal forms
  have hguard : ∀ z : M,
      (Semiformula.Eval ![z] f segGuard ↔
        (¬ Semiformula.Eval ![z, (Semiterm.numeral segBound : Semiterm LX ℕ 0).val ![] f] f
              precCode₁ ∨
          Semiformula.Eval ![z] f (Xat (#0 : Semiterm LX ℕ 1)))) := by
    intro z
    show Semiformula.Eval ![z] f
        (∼(precAt precCode₁ (#0 : Semiterm LX ℕ 1) (Semiterm.numeral segBound)) ⋎
          Xat (#0 : Semiterm LX ℕ 1)) ↔ _
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
      LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, eval_precAt,
      Semiterm.val_bvar, Matrix.cons_val_fin_one, val_numeral_eq]
  have hseg : ∀ y x : M,
      (Semiformula.Eval ![y, x] f OrdinalAnalysis.ACA.precSeg ↔
        Semiformula.Eval ![y, x] f precCode₁ ∧
          Semiformula.Eval ![x, (Semiterm.numeral segBound : Semiterm LX ℕ 0).val ![] f] f
            precCode₁) := by
    intro y x
    show Semiformula.Eval ![y, x] f
        (precCode₁ ⋏ precAt precCode₁ (#1 : Semiterm LX ℕ 2)
          (epsilonNumeral (epsilonNote 0))) ↔ _
    have he : epsilonNumeral (epsilonNote 0) = (Semiterm.numeral segBound : Semiterm LX ℕ 2) :=
      rfl
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq, he,
      eval_precAt, Semiterm.val_bvar, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      val_numeral_eq]
  by_cases hTIb :
      (∀ x : M,
          (∀ y : M, Semiformula.Eval ![y, x] f precCode₁ →
            Semiformula.Eval ![y] f segGuard) → Semiformula.Eval ![x] f segGuard) →
        ∀ y : M, Semiformula.Eval ![y, b.val ![] f] f precCode₁ →
          Semiformula.Eval ![y] f segGuard
  · refine Or.inr ?_
    intro hProgSeg
    -- the guarded formula is `≺₁`-progressive
    have hProg₁ : ∀ x : M,
        (∀ y : M, Semiformula.Eval ![y, x] f precCode₁ →
          Semiformula.Eval ![y] f segGuard) → Semiformula.Eval ![x] f segGuard := by
      intro x hx
      rw [hguard x]
      by_cases hxE :
          Semiformula.Eval ![x, (Semiterm.numeral segBound : Semiterm LX ℕ 0).val ![] f] f
            precCode₁
      · refine Or.inr (hProgSeg x ?_)
        intro y hy
        rw [hseg y x] at hy
        rcases (hguard y).mp (hx y hy.1) with hn | hp
        · exact absurd (hTrans f y x _ hy.1 hxE) hn
        · exact hp
      · exact Or.inl hxE
    have hbelow := hTIb hProg₁
    intro y hy
    rw [hseg y (a.val ![] f)] at hy
    have hyb : Semiformula.Eval ![y, b.val ![] f] f precCode₁ :=
      hTrans f y (a.val ![] f) (b.val ![] f) hy.1 (habM f)
    rcases (hguard y).mp (hbelow y hyb) with hn | hp
    · exact absurd (hTrans f y (a.val ![] f) _ hy.1 hy.2) hn
    · exact hp
  · exact Or.inl hTIb

end OrdinalAnalysis.ACA.SegBridge

/-! ## Layer 2: the second-order bridge -/

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX Xat TIupto paLX)
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁)
open OrdinalAnalysis.ACA.TowerSyntax (emb_univCl_of_closed)

/-- **Route 2, in general**: instantiating `∀²X TI(≺₁,a,X)` at the lifting of a
first-order formula `φ` gives transfinite induction below `a` *for `φ`*. -/
theorem subst₁_tiBody_gen {n : ℕ} (φ : FirstOrder.Semiformula LX ℕ 1)
    (a : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.subst₁ (toSOAtB boundWitness (tiX a)) ![toSOAt segWitness φ] =
      toSOAt segWitness (Gentzen.tiUptoAt precCode₁ φ a) := by
  have hr : toSOAtB segWitness (Gentzen.tiUptoAt precCode₁ φ a) =
      tiUptoAtLift (lift (FirstOrder.Rewriting.emb Gentzen.InternalVNote.precDef₁.val))
        (toSOAtB segWitness φ) (unTerm a) := by
    rw [toSOAtB_tiUptoAt, toSOAtB_precCode₁]
  rw [tiBody_eq, subst₁_tiUptoAtLift, subst₁_lift, subst₁_emb_boundWitness]
  exact hr.symm

/-- The relativising formula, lifted — the arithmetical witness that `spec₂`
instantiates the set quantifier at. -/
def guardWitness : Semiformula ℒₒᵣ ℕ ℕ 0 1 := toSOAt segWitness Relativise.segGuard

theorem arith_guardWitness : Arith guardWitness := arith_toSOAt arith_segWitness _

/-- **From `∀²X TI(≺₁, b̄, X)` to transfinite induction along the segment
ordering below `ā`**, for any notation `a < b`.

Three steps: `spec₂` at `guardWitness` (route 2 of the design note, computed by
`subst₁_tiBody_gen`); the lifted relativisation implication; modus ponens. -/
theorem aca_tiUptoSeg_of_allTI (a b : Gamma0Note) (hab : a < b)
    (h : Provable ACA (allTI (Gentzen.Epsilon1UpperBound.gamma0Term b))) :
    Provable ACA (tiUptoSegSO a) := by
  have h1 : Provable ACA (toSOAt segWitness
      (Gentzen.tiUptoAt precCode₁ Relativise.segGuard
        (Gentzen.Epsilon1UpperBound.gamma0Term b))) := by
    have h2 := spec₂ h arith_guardWitness
    rwa [show guardWitness = toSOAt segWitness Relativise.segGuard from rfl,
      subst₁_tiBody_gen] at h2
  have h3 : Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      ((SegBridge.relImpBody (Gentzen.Epsilon1UpperBound.gamma0Term a)
        (Gentzen.Epsilon1UpperBound.gamma0Term b)).univCl))) :=
    lift_paLX_seg (SegBridge.concrete_relImp _ _
      (Gentzen.Epsilon1UpperBound.concrete_gamma0_prec hab))
  rw [emb_univCl_of_closed (SegBridge.freeVariables_relImpBody
    (by simp [Gentzen.Epsilon1UpperBound.gamma0Term])
    (by simp [Gentzen.Epsilon1UpperBound.gamma0Term]))] at h3
  have h4 : Provable ACA
      (∼(toSOAt segWitness (Gentzen.tiUptoAt precCode₁ Relativise.segGuard
          (Gentzen.Epsilon1UpperBound.gamma0Term b))) ⋎
        toSOAt segWitness (Gentzen.tiUptoAt precSeg (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
          (Gentzen.Epsilon1UpperBound.gamma0Term a))) := by
    have e : toSOAt segWitness (SegBridge.relImpBody
        (Gentzen.Epsilon1UpperBound.gamma0Term a)
        (Gentzen.Epsilon1UpperBound.gamma0Term b)) =
        ∼(toSOAt segWitness (Gentzen.tiUptoAt precCode₁ Relativise.segGuard
            (Gentzen.Epsilon1UpperBound.gamma0Term b))) ⋎
          toSOAt segWitness (Gentzen.tiUptoAt precSeg
            (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
            (Gentzen.Epsilon1UpperBound.gamma0Term a)) := by
      show toSOAtB segWitness (∼(Gentzen.tiUptoAt precCode₁ Relativise.segGuard
          (Gentzen.Epsilon1UpperBound.gamma0Term b)) ⋎
        Gentzen.tiUptoAt precSeg (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
          (Gentzen.Epsilon1UpperBound.gamma0Term a)) = _
      rw [toSOAtB_or, toSOAtB_neg]
    rwa [e] at h3
  have h5 := cutP h1 h4
  have e2 : tiUptoSegSO a = toSOAt segWitness (Gentzen.tiUptoAt precSeg
      (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
      (Gentzen.Epsilon1UpperBound.gamma0Term a)) := by
    have hp : precSeg.freeVariables = ∅ :=
      Gentzen.EpsilonSegmentOrder.freeVariables_precCodeSeg (Gamma0Note.epsilonNote 0)
    have ht : (Gentzen.Epsilon1UpperBound.gamma0Term a).freeVariables = ∅ := by
      simp [Gentzen.Epsilon1UpperBound.gamma0Term]
    have hcl : (TIupto precSeg (Gentzen.Epsilon1UpperBound.gamma0Term a)).freeVariables = ∅ :=
      Gentzen.LowerSyntax.freeVariables_TIupto hp ht
    rw [Gentzen.Epsilon1UpperBound.tiUptoAt_X_eq']
    show toSOAt segWitness (FirstOrder.Rewriting.emb
      ((TIupto precSeg (Gentzen.Epsilon1UpperBound.gamma0Term a)).univCl)) = _
    rw [emb_univCl_of_closed hcl]
  rw [e2]
  exact h5

end OrdinalAnalysis.ACA
