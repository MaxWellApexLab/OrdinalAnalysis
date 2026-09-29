import OrdinalAnalysis.KPi.Ord.Defs

/-!
# Regular uncountable ordinals are closed under the Veblen function

Support for B92 Def 4.2 and Lemma 4.4a: `φ = Ordinal.veblen` maps `κ × κ` into `κ` for every
regular uncountable initial ordinal `κ` (in particular every `κ ∈ R`).

Mathlib's `derivFamily_lt_ord_lift` needs the index type in `Type u` for `Ordinal.{max u v}`, whereas
`veblen` at `Ordinal.{1}` uses the index type `Iio ξ : Type 2`; the closure lemmas are therefore
re-proved here for index types in `Type 2`.
-/

set_option autoImplicit false

open Ordinal Cardinal Set Order

noncomputable section

namespace OrdinalAnalysis.KPi.Ord

theorem nfpFamily_lt' {ι : Type 2} {f : ι → Ordinal.{1} → Ordinal.{1}} {c : Ordinal.{1}}
    (hc : ℵ₀ < c.cof) (hι : #ι < Cardinal.lift.{2, 1} c.cof)
    (hf : ∀ i, ∀ b < c, f i b < c) {a : Ordinal.{1}} (ha : a < c) : nfpFamily f a < c := by
  unfold nfpFamily
  refine Ordinal.lift_iSup_lt_of_lt_cof ?_ (fun l => ?_)
  · rw [← Ordinal.lift_cof]
    have key : #(List ι) < Cardinal.lift.{2, 1} c.cof := by
      refine lt_of_le_of_lt (mk_list_le_max ι) (max_lt ?_ hι)
      rw [← Cardinal.lift_aleph0.{2, 1}]
      exact Cardinal.lift_lt.2 hc
    rwa [Cardinal.lift_id'.{1, 2}]
  · induction l with
    | nil => exact ha
    | cons i l H => exact hf _ _ H

theorem derivFamily_lt' {ι : Type 2} {f : ι → Ordinal.{1} → Ordinal.{1}} {κ : Ordinal.{1}}
    (h : IsRU κ) (hι : #ι < Cardinal.lift.{2, 1} κ.card)
    (hf : ∀ i, ∀ b < κ, f i b < κ) {a : Ordinal.{1}} (ha : a < κ) : derivFamily f a < κ := by
  have hc : ℵ₀ < κ.cof := h.aleph0_lt_cof
  have hι' : #ι < Cardinal.lift.{2, 1} κ.cof := by rwa [h.cof_eq]
  have hlim : IsSuccLimit κ := by
    rw [← h.ord]; exact Cardinal.isSuccLimit_ord h.unc.le
  revert ha
  induction a using Ordinal.limitRecOn with
  | zero =>
    intro ha
    rw [derivFamily_zero]
    exact nfpFamily_lt' hc hι' hf (hlim.bot_lt)
  | add_one b hb =>
    intro ha
    rw [derivFamily_add_one]
    have h1 : derivFamily f b < κ := hb (lt_of_lt_of_le (lt_add_one b) ha.le)
    exact nfpFamily_lt' hc hι' hf (hlim.add_one_lt h1)
  | limit b hb H =>
    intro ha
    rw [derivFamily_limit f hb]
    apply Ordinal.lift_iSup_lt_of_lt_cof
    · rw [← Ordinal.lift_cof, h.cof_eq, Cardinal.mk_Iio_ordinal]
      have : b.card < κ.card := (h.lt_iff).1 ha
      rw [Cardinal.lift_id'.{1, 2}]
      exact Cardinal.lift_lt.2 this
    · intro i
      exact H i.1 i.2 (i.2.trans ha)

/-- A regular uncountable cardinal is closed under `φ` (= mathlib's `veblen`). -/
theorem veblen_lt_of_RU {κ : Ordinal.{1}} (h : IsRU κ) :
    ∀ ξ, ξ < κ → ∀ η < κ, veblen ξ η < κ := by
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | _ ξ IH =>
    intro hξ η hη
    rcases eq_or_ne ξ 0 with rfl | hne
    · rw [veblen_zero_apply]
      have hp := Ordinal.isPrincipal_opow_ord h.unc.le
      rw [h.ord] at hp
      have hω : (ω : Ordinal.{1}) < κ := by
        rw [h.lt_iff, Ordinal.card_omega0]; exact h.unc
      exact hp hω hη
    · rw [veblen_of_ne_zero hne]
      refine derivFamily_lt' h ?_ ?_ hη
      · rw [Cardinal.mk_Iio_ordinal]
        exact Cardinal.lift_lt.2 ((h.lt_iff).1 hξ)
      · intro i b hb
        exact IH i.1 i.2 (i.2.trans hξ) b hb

end OrdinalAnalysis.KPi.Ord
