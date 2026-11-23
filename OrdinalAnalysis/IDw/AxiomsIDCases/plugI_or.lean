/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\plugI_or.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

module

public import OrdinalAnalysis.IDw.AxiomsIDCases.Defs
public import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_verum

@[expose] public section

set_option autoImplicit false
namespace OrdinalAnalysis

variable (k : ℕ)


namespace IDw


open FFL FFL.FirstOrder

open FFL.FirstOrder.Rewriting FFL.FirstOrder.TransitiveRewriting

open FFL.FirstOrder.LawfulSyntacticRewriting


/-! ### Predicates plugged into an operator form -/

section Plug


variable (P : Pred)


-- generated header ends here

@[simp] theorem plugI_or {m : ℕ} (φ ψ : Semiformula (LIinfW) ℕ m) :
    plugI k P (φ ⋎ ψ) = plugI k P φ ⋎ plugI k P ψ := rfl

@[simp] theorem plugI_all {m : ℕ} (φ : Semiformula (LIinfW) ℕ (m + 1)) :
    plugI k P (∀¹ φ) = ∀¹ plugI k P φ := rfl

@[simp] theorem plugI_exs {m : ℕ} (φ : Semiformula (LIinfW) ℕ (m + 1)) :
    plugI k P (∃¹ φ) = ∃¹ plugI k P φ := rfl


end Plug
end IDw
end OrdinalAnalysis
