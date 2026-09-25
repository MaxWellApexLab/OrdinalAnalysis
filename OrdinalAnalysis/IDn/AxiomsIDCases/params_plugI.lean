import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_or
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_rel
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_neg
import OrdinalAnalysis.IDn.AxiomsIDCases.FixF_q
import OrdinalAnalysis.IDn.AxiomsIDCases.predOf_rew
import OrdinalAnalysis.IDn.AxiomsIDCases.NumF_q
import OrdinalAnalysis.IDn.AxiomsIDCases.rew_plugI_num
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_lMap_top
import OrdinalAnalysis.IDn.AxiomsIDCases.embK_substI
import OrdinalAnalysis.IDn.AxiomsIDCases.opShape_rew

set_option autoImplicit false
namespace OrdinalAnalysis

variable {n : ℕ} (k : Fin n)


namespace IDn


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### The two plugged forms -/

section PlugForms


variable (P : Pred n)


-- case_skeleton: generated header ends here

theorem params_plugI {S : Set (Stage n)}
    (hP : ∀ (m : ℕ) (s : Semiterm (LIinfN n) ℕ m), params (P m s) ⊆ S) :
    ∀ {m : ℕ} (φ : Semiformula (LIinfN n) ℕ m), params (plugI k P φ) ⊆ params φ ∪ S := by
  intro m φ
  induction φ using Semiformula.rec' with
  | hverum => exact Set.empty_subset _
  | hfalsum => exact Set.empty_subset _
  | hrel r v =>
    rw [plugI_rel]
    rcases r with r | r
    · exact Set.subset_union_left
    · cases r with
      | X => exact Set.subset_union_left
      | stage a =>
        by_cases h : a = Stage.top k
        · simp only [plugRel, if_pos h]; exact (hP _ _).trans Set.subset_union_right
        · simp only [plugRel, if_neg h]; exact Set.subset_union_left
  | hnrel r v =>
    rw [plugI_nrel]
    rcases r with r | r
    · exact Set.subset_union_left
    · cases r with
      | X => exact Set.subset_union_left
      | stage a =>
        by_cases h : a = Stage.top k
        · simp only [plugNrel, if_pos h, params_neg]
          exact (hP _ _).trans Set.subset_union_right
        · simp only [plugNrel, if_neg h]; exact Set.subset_union_left
  | hand φ ψ ihφ ihψ =>
    rw [plugI_and, params_and, params_and]
    exact Set.union_subset (ihφ.trans (Set.union_subset_union_left _ Set.subset_union_left))
      (ihψ.trans (Set.union_subset_union_left _ Set.subset_union_right))
  | hor φ ψ ihφ ihψ =>
    rw [plugI_or, params_or, params_or]
    exact Set.union_subset (ihφ.trans (Set.union_subset_union_left _ Set.subset_union_left))
      (ihψ.trans (Set.union_subset_union_left _ Set.subset_union_right))
  | hall φ ih => rw [plugI_all, params_all, params_all]; exact ih
  | hexs φ ih => rw [plugI_exs, params_exs, params_exs]; exact ih

theorem xFreeI_plugI (hP : ∀ (m : ℕ) (s : Semiterm (LIinfN n) ℕ m), XFreeI (P m s)) :
    ∀ {m : ℕ} (φ : Semiformula (LIinfN n) ℕ m), XFreeI φ → XFreeI (plugI k P φ) := by
  intro m φ
  induction φ using Semiformula.rec' with
  | hverum => intro _; trivial
  | hfalsum => intro _; trivial
  | hrel r v =>
    intro h
    rw [plugI_rel]
    rcases r with r | r
    · exact h
    · cases r with
      | X => exact h
      | stage a =>
        by_cases ha : a = Stage.top k
        · simp only [plugRel, if_pos ha]; exact hP _ _
        · simp only [plugRel, if_neg ha]; exact h
  | hnrel r v =>
    intro h
    rw [plugI_nrel]
    rcases r with r | r
    · exact h
    · cases r with
      | X => exact h
      | stage a =>
        by_cases ha : a = Stage.top k
        · simp only [plugNrel, if_pos ha]; exact (xFreeI_neg _).mpr (hP _ _)
        · simp only [plugNrel, if_neg ha]; exact h
  | hand φ ψ ihφ ihψ => intro h; exact ⟨ihφ h.1, ihψ h.2⟩
  | hor φ ψ ihφ ihψ => intro h; exact ⟨ihφ h.1, ihψ h.2⟩
  | hall φ ih => intro h; exact ih h
  | hexs φ ih => intro h; exact ih h

theorem freeVariables_plugI
    (hP : ∀ (m : ℕ) (s : Semiterm (LIinfN n) ℕ m), s.freeVariables = ∅ → (P m s).freeVariables = ∅) :
    ∀ {m : ℕ} (φ : Semiformula (LIinfN n) ℕ m), φ.freeVariables = ∅ →
      (plugI k P φ).freeVariables = ∅ := by
  intro m φ
  induction φ using Semiformula.rec' with
  | hverum => intro _; rfl
  | hfalsum => intro _; rfl
  | hrel r v =>
    intro h
    rw [plugI_rel]
    rcases r with r | r
    · exact h
    · cases r with
      | X => exact h
      | stage a =>
        by_cases ha : a = Stage.top k
        · simp only [plugRel, if_pos ha]; exact hP _ _ (freeVariables_rel_arg h 0)
        · simp only [plugRel, if_neg ha]; exact h
  | hnrel r v =>
    intro h
    rw [plugI_nrel]
    rcases r with r | r
    · exact h
    · cases r with
      | X => exact h
      | stage a =>
        by_cases ha : a = Stage.top k
        · simp only [plugNrel, if_pos ha, Semiformula.freeVariables_not]
          exact hP _ _ (freeVariables_nrel_arg h 0)
        · simp only [plugNrel, if_neg ha]; exact h
  | hand φ ψ ihφ ihψ =>
    intro h
    rw [Semiformula.freeVariables_and, Finset.union_eq_empty] at h
    rw [plugI_and, Semiformula.freeVariables_and, ihφ h.1, ihψ h.2, Finset.union_empty]
  | hor φ ψ ihφ ihψ =>
    intro h
    rw [Semiformula.freeVariables_or, Finset.union_eq_empty] at h
    rw [plugI_or, Semiformula.freeVariables_or, ihφ h.1, ihψ h.2, Finset.union_empty]
  | hall φ ih => intro h; rw [plugI_all, Semiformula.freeVariables_all]; exact ih h
  | hexs φ ih => intro h; rw [plugI_exs, Semiformula.freeVariables_exs]; exact ih h


end PlugForms
end IDn
end OrdinalAnalysis
