import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_or
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_rel

set_option autoImplicit false
namespace OrdinalAnalysis

variable {n : ℕ} (k : Fin n)


namespace IDn


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### Predicates plugged into an operator form -/

section Plug


variable (P : Pred n)


-- case_skeleton: generated header ends here

@[simp] theorem plugI_neg {m : ℕ} (φ : Semiformula (LIinfN n) ℕ m) :
    plugI k P (∼φ) = ∼(plugI k P φ) := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => exact (neg_plugRel k P r v).symm
  | hnrel r v =>
    show plugRel k P r v = ∼(plugNrel k P r v)
    rw [← neg_plugRel]; simp
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

/-- **Plugging commutes with rewriting**, for a class `C` of rewritings closed under lifting
along which the predicates commute. -/
theorem rew_plugI (P' : Pred n) (C : ∀ {n₁ n₂ : ℕ}, Rew (LIinfN n) ℕ n₁ ℕ n₂ → Prop)
    (hq : ∀ {n₁ n₂ : ℕ} {ω : Rew (LIinfN n) ℕ n₁ ℕ n₂}, C ω → C ω.q)
    (hP : ∀ {n₁ n₂ : ℕ} {ω : Rew (LIinfN n) ℕ n₁ ℕ n₂}, C ω → ∀ s, ω ▹ P n₁ s = P' n₂ (ω s)) :
    ∀ {n₁ : ℕ} (φ : Semiformula (LIinfN n) ℕ n₁) {n₂ : ℕ} {ω : Rew (LIinfN n) ℕ n₁ ℕ n₂}, C ω →
      ω ▹ plugI k P φ = plugI k P' (ω ▹ φ) := by
  intro n₁ φ
  induction φ using Semiformula.rec' with
  | hverum => intro n₂ ω _; simp
  | hfalsum => intro n₂ ω _; simp
  | hrel r v =>
    intro n₂ ω hω
    rw [plugI_rel, Semiformula.rew_rel, plugI_rel]
    rcases r with r | r
    · exact Semiformula.rew_rel _ _ _
    · cases r with
      | X => exact Semiformula.rew_rel _ _ _
      | stage a =>
        by_cases h : a = Stage.top k
        · simp only [plugRel, if_pos h]
          exact hP hω (v 0)
        · simp only [plugRel, if_neg h]
          exact Semiformula.rew_rel _ _ _
  | hnrel r v =>
    intro n₂ ω hω
    rw [plugI_nrel, Semiformula.rew_nrel, plugI_nrel]
    rcases r with r | r
    · exact Semiformula.rew_nrel _ _ _
    · cases r with
      | X => exact Semiformula.rew_nrel _ _ _
      | stage a =>
        by_cases h : a = Stage.top k
        · simp only [plugNrel, if_pos h, LogicalConnective.HomClass.map_neg]
          rw [hP hω (v 0)]
        · simp only [plugNrel, if_neg h]
          exact Semiformula.rew_nrel _ _ _
  | hand φ ψ ihφ ihψ =>
    intro n₂ ω hω
    simp only [plugI_and, LogicalConnective.HomClass.map_and, ihφ hω, ihψ hω]
  | hor φ ψ ihφ ihψ =>
    intro n₂ ω hω
    simp only [plugI_or, LogicalConnective.HomClass.map_or, ihφ hω, ihψ hω]
  | hall φ ih =>
    intro n₂ ω hω
    simp only [plugI_all, Rewriting.app_all, ih (hq hω)]
  | hexs φ ih =>
    intro n₂ ω hω
    simp only [plugI_exs, Rewriting.app_exs, ih (hq hω)]


end Plug
end IDn
end OrdinalAnalysis
