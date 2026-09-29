import OrdinalAnalysis.IDw.PredCutAux

set_option autoImplicit false

namespace OrdinalAnalysis
namespace IDw

open LO LO.FirstOrder
-- case_skeleton: generated header ends here

/-- Case `jlev` of `predCut_aux` (statement modelled on `orL`: `Jlev ℓ (s,t)` is a one-disjunct
`⋁`, so the rule has one premise and only the height changes). -/
theorem predCut_aux_case_jlev
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
    (p3 : jlevAt ℓ s t ∈ Γ)
    (p4 : s.freeVariables = ∅)
    (p5 : t.freeVariables = ∅)
    (p6 : ((termVal s : ℕ) : WithTop ℕ) < ℓ)
    (p7 : α₀ < α)
    (p8 : IDwDerivable A r H α₀ (IOmegaAt (termVal s) t :: Γ))
    (ih8 : ThetaVNoteD.NiceS H → ThetaVNoteD.PhiClosed lv H → r ∈ H ∅ → α₀ < ThetaVNoteD.Omega lv →
      IDwDerivable A μ H (ThetaVNoteD.phiN lv r α₀) (IOmegaAt (termVal s) t :: Γ))
    : ThetaVNoteD.NiceS H → ThetaVNoteD.PhiClosed lv H → r ∈ H ∅ → α < ThetaVNoteD.Omega lv →
      IDwDerivable A μ H (ThetaVNoteD.phiN lv r α) Γ := by
  intro hH hP hrH hαΩ
  have hα₀Ω : α₀ < ThetaVNoteD.Omega lv := lt_trans p7 hαΩ
  have hφ : ThetaVNoteD.phiN lv r α ∈ H ∅ := hP ∅ r α hr hαΩ hrH p1
  have h0 : ThetaVNoteD.phiN lv r α₀ < ThetaVNoteD.phiN lv r α :=
    ThetaVNoteD.phiN_lt_phiN_right hr hα₀Ω hαΩ p7
  exact .jlev hφ p2 p3 p4 p5 p6 h0 (ih8 hH hP hrH hα₀Ω)
