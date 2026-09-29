/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\plugI_verum.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.AxiomsIDCases.Defs

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

@[simp] theorem plugI_verum {m : ℕ} : plugI k P (⊤ : Semiformula (LIinfW) ℕ m) = ⊤ := rfl

@[simp] theorem plugI_falsum {m : ℕ} : plugI k P (⊥ : Semiformula (LIinfW) ℕ m) = ⊥ := rfl

@[simp] theorem plugI_and {m : ℕ} (φ ψ : Semiformula (LIinfW) ℕ m) :
    plugI k P (φ ⋏ ψ) = plugI k P φ ⋏ plugI k P ψ := rfl


end Plug
end IDw
end OrdinalAnalysis
