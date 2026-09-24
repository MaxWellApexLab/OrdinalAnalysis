/-
  `ω · α` on the coded ϑ-notation, in every model of `IΣ₁` (Freund §5: `ω · Ω = Ω`,
  `ω · ϑ β = ϑ β`, `ω · ⟨αᵢ⟩ = ⟨1 + αᵢ⟩`), following `ThetaNote.omegaMul`:

  * `ionePlus_of_prin`, `iomegaMul_of_prin`: `1 + P = P` and `ω · P = P` for principal `P`;
  * `isNF_iomegaMul`: `ω · ·` preserves normal forms;
  * `iomegaMul_lt_iomegaMul`: `ω · ·` is strictly monotone;
  * `iomegaMul_lt_prin`: the principal codes are closed under `ω · ·` from below.
-/
import OrdinalAnalysis.ID1.Internal.ArithE

set_option autoImplicit false

namespace OrdinalAnalysis.ID1.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.Gentzen.InternalONote

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### `1 + ·` -/

/-- `1 + P = P` for principal `P`. -/
theorem ionePlus_of_prin {p : V} (hp : IsPrinC p) : ionePlus p = p := by
  rw [ionePlus, itoL_of_prinC hp, ione_eq, iaddL_cons_cons,
    if_neg (not_ige_of_iltb (iltb_zero_pos hp.ne_zero)), iaddL_zero_left (sumK_tcCons p 0),
    iofL_single_prin hp]

/-- `1 + ·` is strictly monotone on normal forms. -/
theorem ionePlus_lt_ionePlus {e e' : V} (he : isNF e) (he' : isNF e') (h : iltb e e' = 1) :
    iltb (ionePlus e) (ionePlus e') = 1 := by
  rw [ionePlus_eq_iadd, ionePlus_eq_iadd]
  exact iadd_lt_iadd_right isNF_ione he he' h

lemma ige_ionePlus {x z : V} (hx : isNF x) (hz : isNF z) (h : ige x z = 1) :
    ige (ionePlus x) (ionePlus z) = 1 := by
  rcases ige_eq_one.mp h with h | rfl
  · exact ige_of_iltb (ionePlus_lt_ionePlus hz hx h)
  · exact ige_self _

/-! ### `ω · ·` -/

@[simp] theorem iomegaMul_zero : iomegaMul (0 : V) = 0 := by simp [iomegaMul]

/-- `ω · P = P` for principal `P`; in particular `ω · Ω = Ω` and `ω · ϑ β = ϑ β`. -/
theorem iomegaMul_of_prin {p : V} (hp : IsPrinC p) : iomegaMul p = p := by
  rw [iomegaMul, itoL_of_prinC hp, imapOP_cons, imapOP_zero, ionePlus_of_prin hp,
    iofL_single_prin hp]

lemma isSL_imapOP : ∀ s : V, IsSL s → IsSL (imapOP s) := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro hs
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [imapOP_zero]; exact isSL_zero
    obtain ⟨x, s', rfl⟩ := eq_cons_of_sumK hs.2 hs0
    obtain ⟨hx, hs', hds⟩ := (isSL_cons_iff x s').mp hs
    rw [imapOP_cons]
    refine (isSL_cons_iff _ _).mpr ⟨isNF_ionePlus hx, ih s' (tl_lt_tcCons x s') hs', ?_⟩
    rcases eq_or_ne s' 0 with rfl | hs'0
    · exact Or.inl imapOP_zero
    · obtain ⟨z, w, rfl⟩ := eq_cons_of_sumK hs'.2 hs'0
      have hz : isNF z := ((isSL_cons_iff z w).mp hs').1
      rw [imapOP_cons, tcHd_tcCons]
      exact Or.inr (ige_ionePlus hx hz (by simpa using hds.resolve_left hs'0))

/-- **`ω · ·` preserves normal forms.** -/
theorem isNF_iomegaMul {a : V} (ha : isNF a) : isNF (iomegaMul a) := by
  have h := isSL_imapOP _ (isSL_itoL ha)
  exact isNF_iofL h.1 h.2

lemma imapOP_ne_zero {s : V} (hs : kind s = 3) : imapOP s ≠ 0 := by
  rw [eq_tcCons_of_kind hs, imapOP_cons]; exact tcCons_ne_zero _ _

lemma iltb_imapOP_aux : ∀ w : V, ∀ s ≤ w, ∀ s' ≤ w, s + s' ≤ w → IsSL s → IsSL s' →
    iltb s s' = 1 → iltb (imapOP s) (imapOP s') = 1 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro s _ s' _ hsum hs hs' h
    have hs'0 : s' ≠ 0 := by rintro rfl; exact not_iltb_zero s h
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [imapOP_zero]
      exact iltb_zero_pos (imapOP_ne_zero (kind_eq_three_of_sumK hs'.2 hs'0))
    obtain ⟨x, l, rfl⟩ := eq_cons_of_sumK hs.2 hs0
    obtain ⟨x', l', rfl⟩ := eq_cons_of_sumK hs'.2 hs'0
    obtain ⟨hx, hl, -⟩ := (isSL_cons_iff x l).mp hs
    obtain ⟨hx', hl', -⟩ := (isSL_cons_iff x' l').mp hs'
    rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at h
    rw [imapOP_cons, imapOP_cons, iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl (ionePlus_lt_ionePlus hx hx' h)
    · refine Or.inr ⟨rfl, ih (l + l') (lt_of_lt_of_le ?_ hsum) l le_self_add l' le_add_self
        le_rfl hl hl' h⟩
      exact add_lt_add_of_lt_of_le (tl_lt_tcCons x l) (tl_lt_tcCons x l').le

/-- **`ω · ·` is strictly monotone** on normal forms. -/
theorem iomegaMul_lt_iomegaMul {a b : V} (ha : isNF a) (hb : isNF b) (h : iltb a b = 1) :
    iltb (iomegaMul a) (iomegaMul b) = 1 := by
  have hsa := isSL_imapOP _ (isSL_itoL ha)
  have hsb := isSL_imapOP _ (isSL_itoL hb)
  exact iltb_iofL hsa.2 hsb.2
    (iltb_imapOP_aux _ _ le_self_add _ le_add_self le_rfl (isSL_itoL ha) (isSL_itoL hb)
      (iltb_itoL ha hb h))

/-- **The principal codes are closed under `ω · ·` from below.** -/
theorem iomegaMul_lt_prin {x p : V} (hp : IsPrinC p) (hx : isNF x) (h : iltb x p = 1) :
    iltb (iomegaMul x) p = 1 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [iomegaMul_zero]; exact iltb_zero_pos hp.ne_zero
  have hxt := isTerm_of_isNF hx
  have hl : iltb (ilead x) p = 1 := by
    rw [← iomegaPow_of_prin hp] at h
    exact (iltb_iomegaPow_iff_ilead hxt hx0 p).mp h
  have hop : iltb (ionePlus (ilead x)) p = 1 := by
    rw [ionePlus_eq_iadd]
    exact iadd_lt_prin hp isNF_ione (isNF_ilead hx hx0) (iltb_ione_prin hp) hl
  rw [iomegaMul, itoL_eq_cons hxt hx0, imapOP_cons, ← iomegaPow_of_prin hp]
  exact iltb_iofL_cons_iomegaPow _ hop

/-- `ω · α ≺ ϑ β` for `α ≺ ϑ β`. -/
theorem iomegaMul_lt_theta {x b : V} (hx : isNF x) (h : iltb x (tcTheta b) = 1) :
    iltb (iomegaMul x) (tcTheta b) = 1 :=
  iomegaMul_lt_prin (isPrinC_tcTheta b) hx h

end OrdinalAnalysis.ID1.Internal
