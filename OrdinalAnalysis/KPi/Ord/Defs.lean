import Mathlib

/-!
# Buchholz 1992, Def 4.1: the ordinals `I`, `Ω_σ` and the class `R`

All ordinals live in `Ordinal.{1}` (written `O`); cardinals of sets of such ordinals live in
`Cardinal.{2}` and are compared through `Cardinal.lift.{2, 1}`.
The least weakly inaccessible ordinal `Iord` (B92's `I`) exists in `Ordinal.{1}` because
`Ordinal.univ.{0, 1}` is a regular fixed point of `ω_` (Mathlib: `IsInaccessible.univ`, `omega_univ`).

* `Om σ`      : B92's `Ω_σ` (`Ω_0 = 0`, `Ω_σ = ℵ_σ` for `σ > 0`);
* `Iord`      : `I = min {σ | σ regular ∧ Ω_σ = σ}`;
* `Rset`      : `R = {I} ∪ {Ω_{σ+1} | σ < I}`;
* `IsRU κ`    : `κ` is a regular uncountable initial ordinal (every `κ ∈ R` is one).
-/

set_option autoImplicit false

open Ordinal Cardinal Set Order

noncomputable section

namespace OrdinalAnalysis.KPi.Ord

/-- Shorthand for `Ordinal.{1}`. -/
abbrev O := Ordinal.{1}

/-- Buchholz 1992, Def 4.1: `Ω₀ = 0`, `Ωσ = ℵσ` (`σ > 0`), as ordinals. -/
def Om (σ : Ordinal.{1}) : Ordinal.{1} := if σ = 0 then 0 else ω_ σ

/-- `σ` is a regular cardinal with `Ω_σ = σ` (a weakly inaccessible cardinal). -/
def IsWI (σ : Ordinal.{1}) : Prop := σ.card.IsRegular ∧ ω_ σ = σ

lemma exists_WI : ∃ σ : Ordinal.{1}, IsWI σ := by
  refine ⟨Ordinal.univ.{0, 1}, ?_, Ordinal.omega_univ⟩
  rw [Ordinal.card_univ]
  exact Cardinal.IsInaccessible.univ.isRegular

/-- B92 Def 4.1: `I := min {σ : σ regular & Ωσ = σ}`. -/
def Iord : Ordinal.{1} := sInf {σ | IsWI σ}

lemma Iord_spec : IsWI Iord := csInf_mem exists_WI

/-- B92 Def 4.1: `R = {I} ∪ {Ω_{σ+1} : σ < I}`. -/
def Rset : Set Ordinal.{1} := {Iord} ∪ {κ | ∃ σ < Iord, κ = ω_ (σ + 1)}

/-- A regular uncountable cardinal, as an initial ordinal. -/
structure IsRU (κ : Ordinal.{1}) : Prop where
  reg : κ.card.IsRegular
  ord : κ.card.ord = κ
  unc : ℵ₀ < κ.card

lemma IsRU.lt_iff {κ : Ordinal.{1}} (h : IsRU κ) {a : Ordinal.{1}} : a < κ ↔ a.card < κ.card := by
  conv_lhs => rw [← h.ord]
  exact Cardinal.lt_ord

lemma IsRU.cof_eq {κ : Ordinal.{1}} (h : IsRU κ) : κ.cof = κ.card := by
  conv_lhs => rw [← h.ord]
  exact h.reg.cof_ord

lemma IsRU.aleph0_lt_cof {κ : Ordinal.{1}} (h : IsRU κ) : ℵ₀ < κ.cof := by
  rw [h.cof_eq]; exact h.unc

lemma isRU_Iord : IsRU Iord := by
  have h := Iord_spec
  have hc : Iord.card = ℵ_ Iord := by
    conv_lhs => rw [← h.2]
    exact Ordinal.card_omega _
  refine ⟨h.1, ?_, ?_⟩
  · rw [hc, Cardinal.ord_aleph]; exact h.2
  · have hne : Iord ≠ 0 := by
      intro h0
      have := h.1.pos
      rw [h0] at this
      simp at this
    rw [hc, ← Cardinal.aleph_zero]
    exact Cardinal.aleph_lt_aleph.2 (pos_iff_ne_zero.2 hne)

lemma isRU_omega_succ (σ : Ordinal.{1}) : IsRU (ω_ (σ + 1)) := by
  have hc : (ω_ (σ + 1)).card = ℵ_ (σ + 1) := Ordinal.card_omega _
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]; exact Cardinal.isRegular_aleph_add_one σ
  · rw [hc, Cardinal.ord_aleph]
  · rw [hc, ← Cardinal.aleph_zero]
    exact Cardinal.aleph_lt_aleph.2 (by simp)

lemma Rset_isRU {κ : Ordinal.{1}} (h : κ ∈ Rset) : IsRU κ := by
  rcases h with h | ⟨σ, _, rfl⟩
  · rw [mem_singleton_iff.1 h]; exact isRU_Iord
  · exact isRU_omega_succ σ

lemma Iord_mem_Rset : Iord ∈ Rset := Or.inl rfl

lemma omega_succ_mem_Rset {σ : Ordinal.{1}} (h : σ < Iord) : ω_ (σ + 1) ∈ Rset := Or.inr ⟨σ, h, rfl⟩

end OrdinalAnalysis.KPi.Ord
