module

public import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
public import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_verum
public import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_or
public import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_rel
public import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_neg
public import OrdinalAnalysis.IDn.AxiomsIDCases.FixF_q
public import OrdinalAnalysis.IDn.AxiomsIDCases.predOf_rew
public import OrdinalAnalysis.IDn.AxiomsIDCases.NumF_q

@[expose] public section

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
