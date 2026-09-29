/- Source: OrdinalAnalysis\IDn\Collapsing\CaseAll.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.Collapsing.Statement
/-
  Theorem 4.8 for `ID_n` (`Statement.lean`), the case of the clause (V) for `∀x φ(x)`, the
  ω-rule — proved (no `sorry`).

  Source: W. Buchholz, *A simplified version of local predicativity* (1992), author preprint
  p. 27, proof of Theorem 4.8, case 1 (the index set of `⋀_{m≺ω} φ(m̄)` is the finite `ω`, so
  every member is a "small" collapsed premise, no witness/boundedness bookkeeping needed);
  A. Freund, arXiv:2204.09321, Theorem 6.7, case (V)/`all` (`ID1/Collapsing.lean`, case `all`
  inside `collapsing_aux`).

  **Across levels.**  `∀x φ(x)` carries no stage parameter of its own (`sigmaW_all`/
  `sigmaW_subst` erase the quantifier and the substitution without touching `SigmaW`), so each
  premise `φ(m̄) :: Γ` is `Σ(Ω_{k+1})` at the *same* level `k` as `Γ`, and the side induction
  hypothesis collapses it there directly — no level bookkeeping, unlike `stage`/`nstage`/`fix`.
  For each `i : ℕ`, `f i ≺ α` lets the side induction hypothesis collapse the premise
  `φ(ī) :: Γ` to height `ψ_k(γ + ω^{μ+μ+f i})`, which is `≺ ψ_k α̂` by (𝒜2)
  (`psi_hat_lt_psi_hat`); boosting its rank and operator to the target (𝒜1)-height `ψ_k α̂`
  assembles the new ω-indexed family required by the (V) clause for `∀x φ(x)` itself.

  The statement is `Cases.lean`'s `collapse_case_all`, verbatim.
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

variable {A : FormJ}

/-- **Case `all`**: (V) for `∀x φ(x)`, the ω-rule (Buchholz case 1). -/
theorem collapse_case_all (hyp : CollapseHyps A) {m : WithTop ℕ} {α : ThetaVNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent (LIinfW)}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (hX : ThetaVNoteD.HullHypGe k γ X)
    {φ : Semiproposition (LIinfW) 1} (f : ℕ → ThetaVNoteD)
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅) (hmem : (∀¹ φ) ∈ Γ)
    (hf : ∀ i, f i < α)
    (d0 : ∀ i, IDwDerivable A (muBarW m) (Hg γ X) (f i) (φ/[numI i] :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp hα
  have hσ : SigmaW k φ := (sigmaW_all k φ).mp (hΓ _ hmem)
  have hσ' : ∀ i, SigmaW k (φ/[numI i]) := fun i => (sigmaW_subst k φ (numI i)).mpr hσ
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBarW m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  have hηH : psi k (hat γ (muBarW m) α) ∈ Hg (hat γ (muBarW m) α) X ∅ :=
    mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')
  -- the collapsed, boosted premise at index `i`
  have step : ∀ i, IDwDerivable A (psi k (hat γ (muBarW m) α)) (Hg (hat γ (muBarW m) α) X)
      (psi k (hat γ (muBarW m) (f i))) (φ/[numI i] :: Γ) := by
    intro i
    have hfi : f i ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp (d0 i).height_mem
    have D0 := sih (f i) (hf i) k γ X _ (sigmaW_cons (hσ' i) hΓ) hγ hX (d0 i)
    have hθ := psi_hat_lt_psi_hat (k := k) (m := m) hX hγ hfi hα' (hf i)
    have hop : ∀ Z, Hg (hat γ (muBarW m) (f i)) X Z ⊆ Hg (hat γ (muBarW m) α) X Z :=
      Hg_mono (le_of_lt (hat_lt_hat γ _ (hf i))) X
    exact (D0.mono_rank (le_of_lt hθ)).mono_op hop
  have hlt : ∀ i, psi k (hat γ (muBarW m) (f i)) < psi k (hat γ (muBarW m) α) := fun i =>
    psi_hat_lt_psi_hat (k := k) (m := m) hX hγ (mem_Hg_empty.mp (d0 i).height_mem) hα' (hf i)
  exact .all (fun i => psi k (hat γ (muBarW m) (f i))) hηH hΓη hmem hlt step

end Collapsing

end IDw

end OrdinalAnalysis
