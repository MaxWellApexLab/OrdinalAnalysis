/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\plugI_rel.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.AxiomsIDCases.Defs
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_or

set_option autoImplicit false
namespace OrdinalAnalysis

variable (k : ℕ)


namespace IDw


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### Predicates plugged into an operator form -/

section Plug


variable (P : Pred)


-- case_skeleton: generated header ends here

theorem plugI_rel {m j : ℕ} (r : (LIinfW).Rel j) (v : Fin j → Semiterm (LIinfW) ℕ m) :
    plugI k P (Semiformula.rel r v) = plugRel k P r v := rfl

theorem plugI_nrel {m j : ℕ} (r : (LIinfW).Rel j) (v : Fin j → Semiterm (LIinfW) ℕ m) :
    plugI k P (Semiformula.nrel r v) = plugNrel k P r v := rfl

theorem neg_plugRel {m j : ℕ} (r : (LIinfW).Rel j) (v : Fin j → Semiterm (LIinfW) ℕ m) :
    ∼(plugRel k P r v) = plugNrel k P r v := by
  rcases r with r | r
  · rfl
  · cases r with
    | X => rfl
    | stage a =>
      by_cases h : a = Stage.top k
      · simp only [plugRel, plugNrel, if_pos h]
      · simp only [plugRel, plugNrel, if_neg h]; rfl
    | jlev ℓ => rfl


end Plug
end IDw
end OrdinalAnalysis
