import OrdinalAnalysis.IDw.Collapsing.Statement
/-
  Theorem 4.8 for `ID_ω` (`Statement.lean`), all `m : WithTop ℕ` (transcribed from `IDn/Collapsing/CaseLiteral.lean`), the case of the clause (V) for a true literal of
  arithmetic (the empty conjunction) — proved (no `sorry`).

  Source: A. Freund, arXiv:2204.09321, Theorem 6.7, case (V) / literal
  (`ID1/Collapsing.lean`, case `literal`); W. Buchholz, *A simplified version of local
  predicativity* (1992), author preprint p. 27, proof of Theorem 4.8, case 1 (empty index set).

  **Across levels.**  This clause carries no premise and no side condition on a level `j`: the
  height and the parameter hull only need to be re-certified at `α̂ = γ + ω^{μ+μ+α}` in place of
  `γ`, exactly as in `ID1/Collapsing.lean`'s `literal` case (`hθη`, `hΓη` there); the multi-level
  facts `psi_hat_mem` (𝒜1, second half) and `gamma_le_hat` (𝒜1 monotonicity of `Hg`) of
  `Basic.lean` supply the level-`k` analogues (as used already in `CaseFix.lean`/`CaseStage.lean`
  for their own `hηH`/`hΓη`).

  The statement is `Cases.lean`'s `collapse_case_literal`, verbatim.
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

variable {A : FormJ}

/-- **Case `literal`**: (V) for a true literal of arithmetic (Buchholz case 1, empty index set). -/
theorem collapse_case_literal (hyp : CollapseHyps A) {m : WithTop ℕ} {α : ThetaVNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (hX : ThetaVNoteD.HullHypGe k γ X)
    {φ : Proposition LIinfW}
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅) (hφ : TrueLit φ) (hmem : φ ∈ Γ) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp hα
  exact .literal (mem_Hg_empty.mpr (psi_hat_mem hX hγ hα'))
    (hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)) hφ hmem

end Collapsing

end IDw

end OrdinalAnalysis
