/-
  **The collapsing theorem for `ID_ω`, from positivity alone.**  The fourteen per-rule
  cases (`Collapsing/Case*.lean`) fill `CollapseCases A`; with `collapseHyps` this turns the
  assembled theorems of `Collapsing/Theorem.lean` into statements whose only hypothesis on the
  operator form is `PositiveP A`.
-/

module

public import OrdinalAnalysis.IDw.Collapsing.Hyps
public import OrdinalAnalysis.IDw.Collapsing.CaseLiteral
public import OrdinalAnalysis.IDw.Collapsing.CaseVerum
public import OrdinalAnalysis.IDw.Collapsing.CaseIdX
public import OrdinalAnalysis.IDw.Collapsing.CaseAnd
public import OrdinalAnalysis.IDw.Collapsing.CaseOrL
public import OrdinalAnalysis.IDw.Collapsing.CaseOrR
public import OrdinalAnalysis.IDw.Collapsing.CaseAll
public import OrdinalAnalysis.IDw.Collapsing.CaseExs
public import OrdinalAnalysis.IDw.Collapsing.CaseStage
public import OrdinalAnalysis.IDw.Collapsing.CaseNstage
public import OrdinalAnalysis.IDw.Collapsing.CaseFix
public import OrdinalAnalysis.IDw.Collapsing.CaseJlev
public import OrdinalAnalysis.IDw.Collapsing.CaseNJlev
public import OrdinalAnalysis.IDw.Collapsing.CaseCut

@[expose] public section

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

variable {A : FormJ}

/-- The fourteen collapsing cases, for any positive operator form. -/
theorem collapseCases (hA : PositiveP A) : CollapseCases A :=
  let hyp := collapseHyps hA
  ⟨collapse_case_literal hyp, collapse_case_verum hyp, collapse_case_idX hyp,
   collapse_case_and hyp, collapse_case_orL hyp, collapse_case_orR hyp,
   collapse_case_all hyp, collapse_case_exs hyp, collapse_case_stage hyp,
   collapse_case_nstage hyp, collapse_case_fix hyp, collapse_case_jlev hyp,
   collapse_case_njlev hyp, collapse_case_cut hyp⟩

/-- **Collapsing at the limit** (`μ = Ω_ω`), for a positive form. -/
theorem collapseW (hA : PositiveP A) {k : ℕ} {γ α : ThetaVNoteD}
    {X : Set ThetaVNoteD} {Γ : Sequent LIinfW} (hΓ : ∀ φ ∈ Γ, SigmaW k φ)
    (hγ : γ ∈ ThetaVNoteD.HopS γ X) (hX : ThetaVNoteD.HullHypGe k γ X)
    (d : IDwDerivable A ThetaVNoteD.OmegaW (Hg γ X) α Γ) :
    IDwDerivable A (psi k (hat γ ThetaVNoteD.OmegaW α)) (Hg (hat γ ThetaVNoteD.OmegaW α) X)
      (psi k (hat γ ThetaVNoteD.OmegaW α)) Γ :=
  collapse_top (collapseCases hA) hΓ hγ hX d

/-- **The per-level corollary**, for a positive form: a `SigmaW k` sequent derived in `HopS 0`
at cut rank `muBarW m` has a cut-free-below-`Ω_{k+1}` derivation of a stage bound. -/
theorem collapseW_zero_bound (hA : PositiveP A) {m : WithTop ℕ} (k : ℕ)
    {α : ThetaVNoteD} {φ : Proposition LIinfW} (hφ : SigmaW k φ)
    (d : IDwDerivable A (muBarW m) (ThetaVNoteD.HopS ThetaVNoteD.zero) α [φ]) :
    ∃ b : StageAt k, b.1 = psi k (ThetaVNoteD.omegaPow (muBarW m + muBarW m + α)) ∧
      IDwDerivable A b.1 (ThetaVNoteD.HopS (ThetaVNoteD.omegaPow (muBarW m + muBarW m + α))) b.1
        (capSeq k b [φ]) :=
  collapse_zero_bound (collapseHyps hA) (collapseCases hA) k hφ d

end Collapsing

end IDw

end OrdinalAnalysis
