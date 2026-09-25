import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_or

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

theorem plugI_rel {m j : ℕ} (r : (LIinfN n).Rel j) (v : Fin j → Semiterm (LIinfN n) ℕ m) :
    plugI k P (Semiformula.rel r v) = plugRel k P r v := rfl

theorem plugI_nrel {m j : ℕ} (r : (LIinfN n).Rel j) (v : Fin j → Semiterm (LIinfN n) ℕ m) :
    plugI k P (Semiformula.nrel r v) = plugNrel k P r v := rfl

theorem neg_plugRel {m j : ℕ} (r : (LIinfN n).Rel j) (v : Fin j → Semiterm (LIinfN n) ℕ m) :
    ∼(plugRel k P r v) = plugNrel k P r v := by
  rcases r with r | r
  · rfl
  · cases r with
    | X => rfl
    | stage a =>
      by_cases h : a = Stage.top k
      · simp only [plugRel, plugNrel, if_pos h]
      · simp only [plugRel, plugNrel, if_neg h]; rfl


end Plug
end IDn
end OrdinalAnalysis
