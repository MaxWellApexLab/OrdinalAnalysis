/-
  Theorem 4.8 for `ID_n` (`Statement.lean`), the case of the clause (V) for a true literal of
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
import OrdinalAnalysis.IDn.Collapsing.Statement

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

namespace Collapsing

open LO LO.FirstOrder

variable {n : ℕ} {A : Fin n → Semisentence (LXIn n) 1}

/-- **Case `literal`**: (V) for a true literal of arithmetic (Buchholz case 1, empty index set). -/
theorem collapse_case_literal (hyp : CollapseHyps A) {m : ℕ} (hm : m ≤ n) {α : ThetaWNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaWNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : Fin n} {γ : ThetaWNoteD} {X : Set ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaWNoteD.HopS γ X)
    (hX : ThetaWNoteD.HullHypGe k.val γ X)
    {φ : Proposition (LIinfN n)}
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅) (hφ : TrueLit φ) (hmem : φ ∈ Γ) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp hα
  exact .literal (mem_Hg_empty.mpr (psi_hat_mem hX hγ hα'))
    (hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)) hφ hmem

end Collapsing

end IDn

end OrdinalAnalysis
