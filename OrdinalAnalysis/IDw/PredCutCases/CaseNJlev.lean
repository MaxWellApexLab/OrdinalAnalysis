import OrdinalAnalysis.IDw.PredCutAux

set_option autoImplicit false

namespace OrdinalAnalysis
namespace IDw

open LO LO.FirstOrder
-- case_skeleton: generated header ends here

/-- Case `njlev` of `predCut_aux` (statement modelled on `and`: `¬Jlev ℓ (s,t)` is a conjunction
with at most one conjunct, so the premise and its height bound are conditional on
`val s < ℓ`; only the heights change). -/
theorem predCut_aux_case_njlev
    {A : Semisentence LForm 2}
    {lv : ℕ}
    {μ r : ThetaVNoteD}
    (hμ : ∀ c : ThetaVNoteD, μ ≤ c → c < ThetaVNoteD.Omega lv →
      ∀ j : ℕ, c ≠ ThetaVNoteD.Omega j)
    (hr : r < ThetaVNoteD.Omega lv)
    (ihr : ∀ c : ThetaVNoteD, c < r → PredCutClaim A lv μ c)
    {H : Set ThetaVNoteD → Set ThetaVNoteD}
    {α : ThetaVNoteD}
    {Γ : Sequent (LIinfW)}
    {ℓ : WithTop ℕ}
    {s t : SyntacticTerm (LIinfW)}
    {α₀ : ThetaVNoteD}
    (p1 : α ∈ H ∅)
    (p2 : paramsVal Γ ⊆ H ∅)
    (p3 : njlevAt ℓ s t ∈ Γ)
    (p4 : s.freeVariables = ∅)
    (p5 : t.freeVariables = ∅)
    (p6 : ((termVal s : ℕ) : WithTop ℕ) < ℓ → α₀ < α)
    (p7 : ((termVal s : ℕ) : WithTop ℕ) < ℓ →
      IDwDerivable A r H α₀ (∼(IOmegaAt (termVal s) t) :: Γ))
    (ih7 : ((termVal s : ℕ) : WithTop ℕ) < ℓ →
      ThetaVNoteD.NiceS H → ThetaVNoteD.PhiClosed lv H → r ∈ H ∅ → α₀ < ThetaVNoteD.Omega lv →
      IDwDerivable A μ H (ThetaVNoteD.phiN lv r α₀) (∼(IOmegaAt (termVal s) t) :: Γ))
    : ThetaVNoteD.NiceS H → ThetaVNoteD.PhiClosed lv H → r ∈ H ∅ → α < ThetaVNoteD.Omega lv →
      IDwDerivable A μ H (ThetaVNoteD.phiN lv r α) Γ := by
  intro hH hP hrH hαΩ
  have hφ : ThetaVNoteD.phiN lv r α ∈ H ∅ := hP ∅ r α hr hαΩ hrH p1
  exact .njlev hφ p2 p3 p4 p5
    (fun h => ThetaVNoteD.phiN_lt_phiN_right hr (lt_trans (p6 h) hαΩ) hαΩ (p6 h))
    (fun h => ih7 h hH hP hrH (lt_trans (p6 h) hαΩ))
