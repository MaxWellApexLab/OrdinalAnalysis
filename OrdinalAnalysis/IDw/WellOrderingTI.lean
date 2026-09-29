/-
  The class `Q = ⋃_k J(k, ·)`, BP78 Theorem 1 (`Q = M ∩ Ω_ω`), (10) (`Prog[Q, X] → Q ⊆ X`) and (12)
  (`TI[M, Ω_ω]`), inside models `N` of `IDw WFormWc` (`WModel N`), BP78 pp. 121–123 with `σ = ω`.
  Continues `IDw/WellOrderingW.lean` (skeleton items T1a, T1b, T1c, T10, T12 of
  `IDw/_draft/WellOrderingW_skel.lean`).

  Lemma 1 (`ConsStmt N`, BP78 Lemma 1, the Gentzen jump on `D_k`) is a hypothesis of `Q_iff` and
  `ti_M_OmegaW`: the direction `M ∩ Ω_ω ⊆ Q` uses `W_of_E`, which uses it.  `ti_Q` needs only
  `W_mono`.
-/
import OrdinalAnalysis.IDw.WellOrderingW
import OrdinalAnalysis.IDw.Lift

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OrdinalAnalysis.IDw.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.IDw.Internal

/-! ### T1a, T1b: internal facts (no model needed) -/

section Codes

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- T1a. A normal code below `Ω_ω` is below `Ω_{x+1}` (its levels are smaller numbers). -/
theorem lt_Omega_self_of_lt_OmegaW {x : V} (hx : isNF x) (h : iltb x tcOmegaW = 1) :
    iltb x (tcOmega x) = 1 := by
  revert hx h
  induction x using ISigma1.pi1_order_induction
  · definability
  case ind x ih =>
    intro hx h
    rcases nfA_cases (nfA_of_isNF hx) with
      rfl | ⟨j, rfl⟩ | ⟨j, a, rfl, -⟩ | ⟨z, w, rfl, hzN, -, -, -⟩ | rfl
    · exact iltb_zero_pos (tcOmega_ne_zero _)
    · exact (iltb_Omega_Omega_iff _ _).mpr (lt_tcOmega j)
    · refine (iltb_theta_Omega_iff _ _ _).mpr ?_
      have hne : tcTheta j a ≠ 0 := by
        intro h0
        have := congrArg kind h0
        simp at this
      have := tcLev_lt hne
      simpa using this.le
    · have hz : iltb z tcOmegaW = 1 := by
        rw [← iltb_cons_prin z w (Or.inr (Or.inr kind_tcOmegaW))]; exact h
      have IH := ih z (hd_lt_tcCons z w) hzN hz
      rw [iltb_cons_prin z w (Or.inl (kind_tcOmega _))]
      have hlt : iltb (tcOmega z) (tcOmega (tcCons z w)) = 1 :=
        (iltb_Omega_Omega_iff _ _).mpr (hd_lt_tcCons z w)
      exact iltb_trans (isTerm_of_isNF hzN) (isTerm_tcOmega z) (isTerm_tcOmega _) IH hlt
    · rw [iltb_tcOmegaW_tcOmegaW] at h; simp at h

end Codes

section Model

variable {N : Type} [ORingStructure N] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [s : Structure LXJ N]

/-- T1b. **`Ω_ω ∈ M`** (BP78 Theorem 1, first half). -/
theorem mmW_OmegaW : MMW (s := s) (tcOmegaW : N) :=
  ⟨⟨by simp [isNF, isNFb], by simp [isDom]⟩, fun j g h => by simp at h⟩

/-- BP78's `Q = ⋃_k W_k`. -/
def QW (x : N) : Prop := ∃ k, Jm k x

variable (M : WModel N)
include M

omit M in
theorem DkW.mono_le {j k y : N} (hjk : j ≤ k) (h : DkW k y) : DkW j y :=
  ⟨h.1, fun i hi δ hδ => h.2 i (lt_of_lt_of_le hi hjk) δ hδ⟩

/-- `Q ⊆ M ∩ Ω_ω`: `W_sub`, `iinE_of_lt_Omega`, `W_of_mem_E`, `W_mono`. -/
theorem mmW_of_QW {x : N} (hx : QW x) : MMW x ∧ iltb x tcOmegaW = 1 := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨hD, hΩ⟩ := W_sub M hk
  refine ⟨⟨hD.1, fun j g hg => ?_⟩, ?_⟩
  · rcases lt_or_ge j k with hjk | hkj
    · exact hD.2 j hjk g hg
    · exact W_mono M k j g hkj
        (W_of_mem_E M hk (iinE_of_lt_Omega hkj hD.1.1 hΩ hg))
  · exact iltb_trans (isTerm_of_fldW hD.1) (isTerm_tcOmega k) (by simp [isTerm]) hΩ
      (iltb_tcOmega_tcOmegaW k)

variable (hCons : ConsStmt N)

include hCons in
/-- T1c. **`Q = M ∩ Ω_ω`** (BP78 Theorem 1), relative to `ConsStmt N` (BP78 Lemma 1): `⊆` is
`mmW_of_QW`; `⊇` by `lt_Omega_self_of_lt_OmegaW` and `W_of_E` at the level `x` itself. -/
theorem Q_iff {x : N} : QW x ↔ MMW x ∧ iltb x tcOmegaW = 1 := by
  refine ⟨mmW_of_QW M, fun ⟨hM, hlt⟩ => ⟨x, ?_⟩⟩
  refine W_of_E M hCons x x ⟨hM.1, fun j _ δ hδ => hM.2 j δ hδ⟩
    (lt_Omega_self_of_lt_OmegaW hM.1.1 hlt) fun g hg => hM.2 x g hg

theorem dfn_QStep {X : N → Prop} (hX : LXJ.DefinablePred X) (k : N) :
    LXJ.DefinablePred fun z : N => Jm k z ∧ X z :=
  Language.Definable.and
    (dfn_Jm M (a := fun _ => k) (b := fun u => u 0) (by definability) (by definability)) hX

omit hCons in
/-- T10. **BP78 (10)**: `Q` is well ordered, `Prog[Q, X] → Q ⊆ X` for definable `X`: the induction
scheme of the level `k` of `x` applied to `Jm k z ∧ X z`; `Q ∩ x ⊆ D_k` since `D_j ⊆ D_k` for
`j ≥ k` and `J(j, ·) ⊆ J(k, ·)` for `j ≤ k` (`W_mono`). -/
theorem ti_Q {X : N → Prop} (hX : LXJ.DefinablePred X) (hP : ProgW QW X) :
    ∀ x, QW x → X x := by
  rintro x ⟨k, hk⟩
  refine (M.ind k (dfn_QStep M hX k) (fun x hA => ?_) x hk).2
  obtain ⟨hD, hΩ, hacc⟩ := hA
  have hJ : Jm k x := M.closure k x ⟨hD, hΩ, fun z hz hzx => (hacc z hz hzx).1⟩
  refine ⟨hJ, hP x ⟨k, hJ⟩ ?_⟩
  rintro y ⟨j, hy⟩ hyx
  have hDy : DkW k y := by
    rcases le_total j k with hjk | hkj
    · exact (W_sub M (W_mono M j k y hjk hy)).1
    · exact DkW.mono_le hkj (W_sub M hy).1
  exact (hacc y hDy hyx).2

include hCons in
/-- T12. **BP78 (12)**: `TI[M, Ω_ω]` (from (10) and Theorem 1). -/
theorem ti_M_OmegaW : TIW MMW (tcOmegaW : N) := by
  intro X hX hP x hx hlt
  refine ti_Q M hX ?_ x ((Q_iff M hCons).mpr ⟨hx, hlt⟩)
  intro y hy ih
  obtain ⟨hyM, hyΩ⟩ := (Q_iff M hCons).mp hy
  refine hP y hyM fun z hz hzy => ih z ((Q_iff M hCons).mpr ⟨hz, ?_⟩) hzy
  exact iltb_trans (isTerm_of_fldW hz.1) (isTerm_of_fldW hyM.1) (by simp [isTerm]) hzy hyΩ

end Model

/-! ### The bridge from models of `IDw WFormWc` -/

section Bridge

variable {N : Type} [ORingStructure N] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [s : Structure LXJ N]

/-- **`WModel` from an arithmetically standard model of `IDw WFormWc`**: closure and induction
are the axioms, order induction is `Lift.order_induction_definable`. -/
theorem WModel.of_models [Lift.ArithStd N] [hM : N↓[LXJ] ⊧* IDw WFormWc] : WModel N :=
  WModel.of_eval Lift.ArithStd.lMap_eq
    (Lift.eval_of_mem_IDwN WFormWc (closureAxJ_mem_IDw WFormWc))
    (fun F => Lift.eval_of_mem_IDwN WFormWc (indAxJ_mem_IDw WFormWc F))
    (fun hQ h => Lift.order_induction_definable WFormWc hQ h)

end Bridge

end OrdinalAnalysis.IDw.Upper
