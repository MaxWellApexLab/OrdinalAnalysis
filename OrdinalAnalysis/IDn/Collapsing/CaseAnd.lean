/-
  Theorem 4.8 for `ID_n` (`Statement.lean`), the case of the clause (V) for `φ ∧ ψ` — proved
  (no `sorry`).

  Source: W. Buchholz, *A simplified version of local predicativity* (1992), author preprint
  p. 27, proof of Theorem 4.8, case 1 (a clause with index set `J = {0, 1}` — here `⋀_{i≺2}`,
  Buchholz's `⋀_{ι∈J}(A_ι)`, is handled by the side induction hypothesis on each of the two
  premises separately, exactly as for a single index); A. Freund, arXiv:2204.09321,
  Theorem 6.7, case (V) for `∧` (`ID1/Collapsing.lean`, case `and`).

  Both premises `φ :: Γ` and `ψ :: Γ` are `Σ(Ω_{k+1})` since `Γ` is and `φ ∧ ψ ∈ Γ` is
  (`sigmaW_and`); the side induction hypothesis collapses each at the same level `k`, and the
  two collapsed derivations (raised to the common rank/operator `ψ_k α̂` / `H_α̂[Θ]`) are
  combined by the (V)-clause for `∧`.

  The statement is `Cases.lean`'s `collapse_case_and`, verbatim.
-/
import OrdinalAnalysis.IDn.Collapsing.Statement

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

namespace Collapsing

open LO LO.FirstOrder

variable {n : ℕ} {A : Fin n → Semisentence (LXIn n) 1}

/-- **Case `and`**: (V) for `φ ∧ ψ` (Buchholz case 1). -/
theorem collapse_case_and (hyp : CollapseHyps A) {m : ℕ} (hm : m ≤ n) {α : ThetaWNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaWNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : Fin n} {γ : ThetaWNoteD} {X : Set ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaWNoteD.HopS γ X)
    (hX : ThetaWNoteD.HullHypGe k.val γ X)
    {φ ψ : Proposition (LIinfN n)} {α₀ α₁ : ThetaWNoteD}
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅) (hmem : φ ⋏ ψ ∈ Γ)
    (h0 : α₀ < α) (h1 : α₁ < α)
    (d0 : IDnDerivable A (muBar m) (Hg γ X) α₀ (φ :: Γ))
    (d1 : IDnDerivable A (muBar m) (Hg γ X) α₁ (ψ :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp hα
  have hα₀ : α₀ ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp d0.height_mem
  have hα₁ : α₁ ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp d1.height_mem
  have hσ : SigmaW k φ ∧ SigmaW k ψ := hΓ _ hmem
  -- collapse both premises at the same level `k`
  have D0 := sih α₀ h0 k γ X _ (sigmaW_cons hσ.1 hΓ) hγ hX d0
  have D1 := sih α₁ h1 k γ X _ (sigmaW_cons hσ.2 hΓ) hγ hX d1
  -- raise both to the common rank `ψ_k α̂` and operator `H_α̂[Θ]`
  have hθ0 := psi_hat_lt_psi_hat (k := k.val) (m := m) hX hγ hα₀ hα' h0
  have hθ1 := psi_hat_lt_psi_hat (k := k.val) (m := m) hX hγ hα₁ hα' h1
  have hop0 : ∀ Z, Hg (hat γ (muBar m) α₀) X Z ⊆ Hg (hat γ (muBar m) α) X Z :=
    Hg_mono (le_of_lt (hat_lt_hat γ _ h0)) X
  have hop1 : ∀ Z, Hg (hat γ (muBar m) α₁) X Z ⊆ Hg (hat γ (muBar m) α) X Z :=
    Hg_mono (le_of_lt (hat_lt_hat γ _ h1)) X
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBar m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  have hηH : psi k.val (hat γ (muBar m) α) ∈ Hg (hat γ (muBar m) α) X ∅ :=
    mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')
  exact .and hηH hΓη hmem hθ0 hθ1
    ((D0.mono_rank (le_of_lt hθ0)).mono_op hop0) ((D1.mono_rank (le_of_lt hθ1)).mono_op hop1)

end Collapsing

end IDn

end OrdinalAnalysis
