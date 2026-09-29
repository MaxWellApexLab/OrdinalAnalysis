/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\params_plugI.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.AxiomsIDCases.Defs
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_or
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_rel
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_neg
import OrdinalAnalysis.IDw.AxiomsIDCases.FixF_q
import OrdinalAnalysis.IDw.AxiomsIDCases.predOf_rew
import OrdinalAnalysis.IDw.AxiomsIDCases.NumF_q
import OrdinalAnalysis.IDw.AxiomsIDCases.rew_plugI_num
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_lMap_top
import OrdinalAnalysis.IDw.AxiomsIDCases.opShape_rew

set_option autoImplicit false
namespace OrdinalAnalysis

variable (k : ℕ)


namespace IDw


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### The two plugged forms -/

section PlugForms


variable (P : Pred)


-- case_skeleton: generated header ends here

theorem params_plugI {S : Set (Stage)}
    (hP : ∀ (m : ℕ) (s : Semiterm (LIinfW) ℕ m), params (P m s) ⊆ S) :
    ∀ {m : ℕ} (φ : Semiformula (LIinfW) ℕ m), params (plugI k P φ) ⊆ params φ ∪ S := by
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
      | jlev ℓ => exact Set.subset_union_left
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
      | jlev ℓ => exact Set.subset_union_left
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

theorem xFreeI_plugI (hP : ∀ (m : ℕ) (s : Semiterm (LIinfW) ℕ m), XFreeI (P m s)) :
    ∀ {m : ℕ} (φ : Semiformula (LIinfW) ℕ m), XFreeI φ → XFreeI (plugI k P φ) := by
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
      | jlev ℓ => exact h
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
      | jlev ℓ => exact h
  | hand φ ψ ihφ ihψ => intro h; exact ⟨ihφ h.1, ihψ h.2⟩
  | hor φ ψ ihφ ihψ => intro h; exact ⟨ihφ h.1, ihψ h.2⟩
  | hall φ ih => intro h; exact ih h
  | hexs φ ih => intro h; exact ih h

theorem freeVariables_plugI
    (hP : ∀ (m : ℕ) (s : Semiterm (LIinfW) ℕ m), s.freeVariables = ∅ → (P m s).freeVariables = ∅) :
    ∀ {m : ℕ} (φ : Semiformula (LIinfW) ℕ m), φ.freeVariables = ∅ →
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
      | jlev ℓ => exact h
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
      | jlev ℓ => exact h
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
end IDw
end OrdinalAnalysis
