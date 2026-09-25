import OrdinalAnalysis.IDn.PredCutCases.CaseLiteral
import OrdinalAnalysis.IDn.PredCutCases.CaseVerum
import OrdinalAnalysis.IDn.PredCutCases.CaseIdX
import OrdinalAnalysis.IDn.PredCutCases.CaseAnd
import OrdinalAnalysis.IDn.PredCutCases.CaseOrL
import OrdinalAnalysis.IDn.PredCutCases.CaseOrR
import OrdinalAnalysis.IDn.PredCutCases.CaseAll
import OrdinalAnalysis.IDn.PredCutCases.CaseExs
import OrdinalAnalysis.IDn.PredCutCases.CaseStage
import OrdinalAnalysis.IDn.PredCutCases.CaseNstage
import OrdinalAnalysis.IDn.PredCutCases.CaseFix
import OrdinalAnalysis.IDn.PredCutCases.CaseCut
set_option autoImplicit false

namespace OrdinalAnalysis
namespace IDn

open LO LO.FirstOrder
-- case_skeleton: generated header ends here

theorem predCut_aux
    {n : ℕ}
    {A : Fin n → Semisentence (LXIn n) 1}
    (hAb : FamilyLevelBounded A)
    {lv : ℕ}
    {μ r : ThetaWNoteD}
    (hμ : ∀ c : ThetaWNoteD, μ ≤ c → c < ThetaWNoteD.Omega lv →
      ∀ j : Fin n, c ≠ ThetaWNoteD.Omega j.val)
    (hr : r < ThetaWNoteD.Omega lv)
    (ihr : ∀ c : ThetaWNoteD, c < r → PredCutClaim A lv μ c)
    {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    (d : IDnDerivable A r H α Γ)
    : ThetaWNoteD.NiceS H → ThetaWNoteD.PhiClosed lv H → r ∈ H ∅ → α < ThetaWNoteD.Omega lv →
      IDnDerivable A μ H (ThetaWNoteD.phiN lv r α) Γ := by
  induction d with
  | literal p1 p2 p3 p4 => exact predCut_aux_case_literal hAb hμ hr ihr p1 p2 p3 p4
  | verum p1 p2 p3 => exact predCut_aux_case_verum hAb hμ hr ihr p1 p2 p3
  | idX t p1 p2 p3 p4 => exact predCut_aux_case_idX hAb hμ hr ihr t p1 p2 p3 p4
  | and p1 p2 p3 p4 p5 p6 p7 ih6 ih7 => exact predCut_aux_case_and hAb hμ hr ihr p1 p2 p3 p4 p5 p6 p7 ih6 ih7
  | orL p1 p2 p3 p4 p5 ih5 => exact predCut_aux_case_orL hAb hμ hr ihr p1 p2 p3 p4 p5 ih5
  | orR p1 p2 p3 p4 p5 p6 ih6 => exact predCut_aux_case_orR hAb hμ hr ihr p1 p2 p3 p4 p5 p6 ih6
  | all f p1 p2 p3 p4 p5 ih5 => exact predCut_aux_case_all hAb hμ hr ihr f p1 p2 p3 p4 p5 ih5
  | exs m p1 p2 p3 p4 p5 p6 ih6 => exact predCut_aux_case_exs hAb hμ hr ihr m p1 p2 p3 p4 p5 p6 ih6
  | stage g p1 p2 p3 p4 p5 p6 p7 p8 ih8 => exact predCut_aux_case_stage hAb hμ hr ihr g p1 p2 p3 p4 p5 p6 p7 p8 ih8
  | nstage f p1 p2 p3 p4 p5 ih5 => exact predCut_aux_case_nstage hAb hμ hr ihr f p1 p2 p3 p4 p5 ih5
  | fix p1 p2 p3 p4 p5 p6 ih6 => exact predCut_aux_case_fix hAb hμ hr ihr p1 p2 p3 p4 p5 p6 ih6
  | cut p1 p2 p3 p4 p5 p6 ih5 ih6 => exact predCut_aux_case_cut hAb hμ hr ihr p1 p2 p3 p4 p5 p6 ih5 ih6
