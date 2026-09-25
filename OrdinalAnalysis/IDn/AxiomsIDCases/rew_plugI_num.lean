import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_or
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_rel
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_neg
import OrdinalAnalysis.IDn.AxiomsIDCases.FixF_q
import OrdinalAnalysis.IDn.AxiomsIDCases.predOf_rew
import OrdinalAnalysis.IDn.AxiomsIDCases.NumF_q

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

theorem rew_plugI_num (f : ℕ → ℕ) (G : Semiformula (LIinfN n) ℕ 1) (φ : Semiformula (LIinfN n) ℕ 1) :
    (numSubst₁ (n := n) f) ▹ plugI k (predOf G) φ =
      plugI k (predOf ((numSubst₁ (n := n) f) ▹ G)) ((numSubst₁ (n := n) f) ▹ φ) :=
  rew_plugI k (predOf G) (predOf ((numSubst₁ (n := n) f) ▹ G)) (NumF f) (fun h => h.q)
    (fun h s => predOf_numF f G h s) φ (numF_numSubst₁ f)


end Plug
end IDn
end OrdinalAnalysis
