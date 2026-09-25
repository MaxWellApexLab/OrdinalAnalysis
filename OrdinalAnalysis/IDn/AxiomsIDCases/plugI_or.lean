import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_verum

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

@[simp] theorem plugI_or {m : ℕ} (φ ψ : Semiformula (LIinfN n) ℕ m) :
    plugI k P (φ ⋎ ψ) = plugI k P φ ⋎ plugI k P ψ := rfl

@[simp] theorem plugI_all {m : ℕ} (φ : Semiformula (LIinfN n) ℕ (m + 1)) :
    plugI k P (∀¹ φ) = ∀¹ plugI k P φ := rfl

@[simp] theorem plugI_exs {m : ℕ} (φ : Semiformula (LIinfN n) ℕ (m + 1)) :
    plugI k P (∃¹ φ) = ∃¹ plugI k P φ := rfl


end Plug
end IDn
end OrdinalAnalysis
