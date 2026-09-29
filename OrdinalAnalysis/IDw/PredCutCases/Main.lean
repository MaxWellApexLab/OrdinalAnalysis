/- Source: OrdinalAnalysis\IDn\PredCutCases\Main.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.PredCutCases.CaseLiteral
import OrdinalAnalysis.IDw.PredCutCases.CaseVerum
import OrdinalAnalysis.IDw.PredCutCases.CaseIdX
import OrdinalAnalysis.IDw.PredCutCases.CaseAnd
import OrdinalAnalysis.IDw.PredCutCases.CaseOrL
import OrdinalAnalysis.IDw.PredCutCases.CaseOrR
import OrdinalAnalysis.IDw.PredCutCases.CaseAll
import OrdinalAnalysis.IDw.PredCutCases.CaseExs
import OrdinalAnalysis.IDw.PredCutCases.CaseStage
import OrdinalAnalysis.IDw.PredCutCases.CaseNstage
import OrdinalAnalysis.IDw.PredCutCases.CaseFix
import OrdinalAnalysis.IDw.PredCutCases.CaseJlev
import OrdinalAnalysis.IDw.PredCutCases.CaseNJlev
import OrdinalAnalysis.IDw.PredCutCases.CaseCut
set_option autoImplicit false

namespace OrdinalAnalysis
namespace IDw

open LO LO.FirstOrder
-- case_skeleton: generated header ends here

theorem predCut_aux
    {A : Semisentence LForm 2}
    {lv : ℕ}
    {μ r : ThetaVNoteD}
    (hμ : ∀ c : ThetaVNoteD, μ ≤ c → c < ThetaVNoteD.Omega lv →
      ∀ j : ℕ, c ≠ ThetaVNoteD.Omega j)
    (hr : r < ThetaVNoteD.Omega lv)
    (ihr : ∀ c : ThetaVNoteD, c < r → PredCutClaim A lv μ c)
    {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent (LIinfW)}
    (d : IDwDerivable A r H α Γ)
    : ThetaVNoteD.NiceS H → ThetaVNoteD.PhiClosed lv H → r ∈ H ∅ → α < ThetaVNoteD.Omega lv →
      IDwDerivable A μ H (ThetaVNoteD.phiN lv r α) Γ := by
  induction d with
  | literal p1 p2 p3 p4 => exact predCut_aux_case_literal hμ hr ihr p1 p2 p3 p4
  | verum p1 p2 p3 => exact predCut_aux_case_verum hμ hr ihr p1 p2 p3
  | idX t p1 p2 p3 p4 => exact predCut_aux_case_idX hμ hr ihr t p1 p2 p3 p4
  | and p1 p2 p3 p4 p5 p6 p7 ih6 ih7 => exact predCut_aux_case_and hμ hr ihr p1 p2 p3 p4 p5 p6 p7 ih6 ih7
  | orL p1 p2 p3 p4 p5 ih5 => exact predCut_aux_case_orL hμ hr ihr p1 p2 p3 p4 p5 ih5
  | orR p1 p2 p3 p4 p5 p6 ih6 => exact predCut_aux_case_orR hμ hr ihr p1 p2 p3 p4 p5 p6 ih6
  | all f p1 p2 p3 p4 p5 ih5 => exact predCut_aux_case_all hμ hr ihr f p1 p2 p3 p4 p5 ih5
  | exs m p1 p2 p3 p4 p5 p6 ih6 => exact predCut_aux_case_exs hμ hr ihr m p1 p2 p3 p4 p5 p6 ih6
  | stage g p1 p2 p3 p4 p5 p6 p7 p8 ih8 => exact predCut_aux_case_stage hμ hr ihr g p1 p2 p3 p4 p5 p6 p7 p8 ih8
  | nstage f p1 p2 p3 p4 p5 ih5 => exact predCut_aux_case_nstage hμ hr ihr f p1 p2 p3 p4 p5 ih5
  | fix p1 p2 p3 p4 p5 p6 ih6 => exact predCut_aux_case_fix hμ hr ihr p1 p2 p3 p4 p5 p6 ih6
  | jlev p1 p2 p3 p4 p5 p6 p7 p8 ih8 => exact predCut_aux_case_jlev hμ hr ihr p1 p2 p3 p4 p5 p6 p7 p8 ih8
  | njlev p1 p2 p3 p4 p5 p6 p7 ih7 => exact predCut_aux_case_njlev hμ hr ihr p1 p2 p3 p4 p5 p6 p7 ih7
  | cut p1 p2 p3 p4 p5 p6 ih5 ih6 => exact predCut_aux_case_cut hμ hr ihr p1 p2 p3 p4 p5 p6 ih5 ih6
