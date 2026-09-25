/-
  Theorem 4.8 for `ID_n` (`Statement.lean`), the case of the clause (W) for `φ ∨ ψ`, index `1`
  — proved (no `sorry`).

  Source: W. Buchholz, *A simplified version of local predicativity* (1992), author preprint
  p. 27, proof of Theorem 4.8, case 2 (Buchholz's `⋁_{ι∈J}(A_ι)`, `J = {0, 1}`: the witness
  index `1` needs `1 ≺ α` at the conclusion, always true since `ψ_κ` of a domain point is
  principal, hence `> 1`); A. Freund, arXiv:2204.09321, Theorem 6.7, case (W) for `∨`
  (`ID1/Collapsing.lean`, case `orR`, which reproves `ThetaNote.one < θ(α+ω^β)` fresh from
  `θ(α+ω^β)` being principal rather than reusing the input's `ThetaNote.one < α` hypothesis;
  the same is done here for `ψ_k α̂`).

  The premise `ψ :: Γ` is `Σ(Ω_{k+1})` since `Γ` is and `φ ∨ ψ ∈ Γ` is (`sigmaW_or`); the side
  induction hypothesis collapses it at the same level `k`, `ψ_k α̂` is principal (hence `> 1`)
  since `α̂` is in the domain of `ϑ_k` (`dom_hat`), and the (W)-clause for `∨`, index `1`,
  concludes.

  The statement is `Cases.lean`'s `collapse_case_orR`, verbatim.
-/
import OrdinalAnalysis.IDn.Collapsing.Statement

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

namespace Collapsing

open LO LO.FirstOrder

variable {n : ℕ} {A : Fin n → Semisentence (LXIn n) 1}

/-- **Case `orR`**: (W) for `φ ∨ ψ`, index `1` (Buchholz case 2). -/
theorem collapse_case_orR (hyp : CollapseHyps A) {m : ℕ} (hm : m ≤ n) {α : ThetaWNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaWNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : Fin n} {γ : ThetaWNoteD} {X : Set ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaWNoteD.HopS γ X)
    (hX : ThetaWNoteD.HullHypGe k.val γ X)
    {φ ψ : Proposition (LIinfN n)} {α₀ : ThetaWNoteD}
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅) (hmem : φ ⋎ ψ ∈ Γ)
    (h1 : ThetaWNoteD.one < α) (h0 : α₀ < α)
    (d0 : IDnDerivable A (muBar m) (Hg γ X) α₀ (ψ :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp hα
  have hα₀ : α₀ ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp d0.height_mem
  have hσ : SigmaW k φ ∧ SigmaW k ψ := hΓ _ hmem
  have D0 := sih α₀ h0 k γ X _ (sigmaW_cons hσ.2 hΓ) hγ hX d0
  have hθ := psi_hat_lt_psi_hat (k := k.val) (m := m) hX hγ hα₀ hα' h0
  have hop : ∀ Z, Hg (hat γ (muBar m) α₀) X Z ⊆ Hg (hat γ (muBar m) α) X Z :=
    Hg_mono (le_of_lt (hat_lt_hat γ _ h0)) X
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBar m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  have hηH : psi k.val (hat γ (muBar m) α) ∈ Hg (hat γ (muBar m) α) X ∅ :=
    mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')
  -- `ψ_k α̂` is principal (it is `ϑ_k` of a domain point), hence `> 1`
  have hDα : (Notn.thetaWLevel k.val).D (hat γ (muBar m) α) := dom_hat (m := m) hX hγ hα'
  have hp : ThetaWTerm.IsPrin (psi k.val (hat γ (muBar m) α)).1 :=
    (Notn.thetaWLevel k.val).isPrin_theta hDα
  have hone : ThetaWNoteD.one < psi k.val (hat γ (muBar m) α) := ThetaWNoteD.one_lt_prin hp
  exact .orR hηH hΓη hmem hone hθ ((D0.mono_rank (le_of_lt hθ)).mono_op hop)

end Collapsing

end IDn

end OrdinalAnalysis
