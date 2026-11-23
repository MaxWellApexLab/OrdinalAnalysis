module

public import OrdinalAnalysis.IDn.AxiomsIDCases.Defs

@[expose] public section

set_option autoImplicit false
namespace OrdinalAnalysis

variable {n : ℕ} (k : Fin n)


namespace IDn


open FFL FFL.FirstOrder

open FFL.FirstOrder.Rewriting FFL.FirstOrder.TransitiveRewriting

open FFL.FirstOrder.LawfulSyntacticRewriting


/-! ### Predicates plugged into an operator form -/

section Plug


variable (P : Pred n)


-- generated header ends here

@[simp] theorem plugI_verum {m : ℕ} : plugI k P (⊤ : Semiformula (LIinfN n) ℕ m) = ⊤ := rfl

@[simp] theorem plugI_falsum {m : ℕ} : plugI k P (⊥ : Semiformula (LIinfN n) ℕ m) = ⊥ := rfl

@[simp] theorem plugI_and {m : ℕ} (φ ψ : Semiformula (LIinfN n) ℕ m) :
    plugI k P (φ ⋏ ψ) = plugI k P φ ⋏ plugI k P ψ := rfl


end Plug
end IDn
end OrdinalAnalysis
