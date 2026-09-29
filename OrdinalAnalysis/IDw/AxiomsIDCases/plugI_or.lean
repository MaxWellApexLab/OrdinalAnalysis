/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\plugI_or.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.AxiomsIDCases.Defs
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_verum

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

@[simp] theorem plugI_or {m : ℕ} (φ ψ : Semiformula (LIinfW) ℕ m) :
    plugI k P (φ ⋎ ψ) = plugI k P φ ⋎ plugI k P ψ := rfl

@[simp] theorem plugI_all {m : ℕ} (φ : Semiformula (LIinfW) ℕ (m + 1)) :
    plugI k P (∀¹ φ) = ∀¹ plugI k P φ := rfl

@[simp] theorem plugI_exs {m : ℕ} (φ : Semiformula (LIinfW) ℕ (m + 1)) :
    plugI k P (∃¹ φ) = ∃¹ plugI k P φ := rfl


end Plug
end IDw
end OrdinalAnalysis
