import OrdinalAnalysis.IDw.Collapsing.Statement
/-
  Theorem 4.8 for `ID_ω` (`Statement.lean`), all `m : WithTop ℕ` (transcribed from `IDn/Collapsing/CaseOrL.lean`), the case of the clause (W) for `φ ∨ ψ`, index `0`
  — proved (no `sorry`).

  Source: W. Buchholz, *A simplified version of local predicativity* (1992), author preprint
  p. 27, proof of Theorem 4.8, case 2 (a clause with index set `J = {0, 1}` — here `⋁_{i≺2}`,
  Buchholz's `⋁_{ι∈J}(A_ι)`: the witness index `0 ≺ α` lies in `H_γ[Θ] ∩ Ω_{k+1}` trivially,
  since `0` is in every nice operator); A. Freund, arXiv:2204.09321, Theorem 6.7, case (W) for
  `∨` (`ID1/Collapsing.lean`, case `orL`).

  The premise `φ :: Γ` is `Σ(Ω_{k+1})` since `Γ` is and `φ ∨ ψ ∈ Γ` is (`sigmaW_or`); the side
  induction hypothesis collapses it at the same level `k`, and the (W)-clause for `∨`, index
  `0`, concludes.

  The statement is `Cases.lean`'s `collapse_case_orL`, verbatim.
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

variable {A : FormJ}

/-- **Case `orL`**: (W) for `φ ∨ ψ`, index `0` (Buchholz case 2). -/
theorem collapse_case_orL (hyp : CollapseHyps A) {m : WithTop ℕ} {α : ThetaVNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (hX : ThetaVNoteD.HullHypGe k γ X)
    {φ ψ : Proposition LIinfW} {α₀ : ThetaVNoteD}
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅) (hmem : φ ⋎ ψ ∈ Γ)
    (h0 : α₀ < α) (d0 : IDwDerivable A (muBarW m) (Hg γ X) α₀ (φ :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp hα
  have hα₀ : α₀ ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp d0.height_mem
  have hσ : SigmaW k φ ∧ SigmaW k ψ := hΓ _ hmem
  have D0 := sih α₀ h0 k γ X _ (sigmaW_cons hσ.1 hΓ) hγ hX d0
  have hθ := psi_hat_lt_psi_hat (k := k) (m := m) hX hγ hα₀ hα' h0
  have hop : ∀ Z, Hg (hat γ (muBarW m) α₀) X Z ⊆ Hg (hat γ (muBarW m) α) X Z :=
    Hg_mono (le_of_lt (hat_lt_hat γ _ h0)) X
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBarW m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  have hηH : psi k (hat γ (muBarW m) α) ∈ Hg (hat γ (muBarW m) α) X ∅ :=
    mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')
  exact .orL hηH hΓη hmem hθ ((D0.mono_rank (le_of_lt hθ)).mono_op hop)

end Collapsing

end IDw

end OrdinalAnalysis
