/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\rew_plugI_num.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

module

public import OrdinalAnalysis.IDw.AxiomsIDCases.Defs
public import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_verum
public import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_or
public import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_rel
public import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_neg
public import OrdinalAnalysis.IDw.AxiomsIDCases.FixF_q
public import OrdinalAnalysis.IDw.AxiomsIDCases.predOf_rew
public import OrdinalAnalysis.IDw.AxiomsIDCases.NumF_q

@[expose] public section

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

theorem rew_plugI_num (f : ℕ → ℕ) (G : Semiformula (LIinfW) ℕ 1) (φ : Semiformula (LIinfW) ℕ 1) :
    (numSubst₁ f) ▹ plugI k (predOf G) φ =
      plugI k (predOf ((numSubst₁ f) ▹ G)) ((numSubst₁ f) ▹ φ) :=
  rew_plugI k (predOf G) (predOf ((numSubst₁ f) ▹ G)) (NumF f) (fun h => h.q)
    (fun h s => predOf_numF f G h s) φ (numF_numSubst₁ f)


end Plug
end IDw
end OrdinalAnalysis
