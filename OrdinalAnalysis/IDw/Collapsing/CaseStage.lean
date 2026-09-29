/- Source: OrdinalAnalysis\IDn\Collapsing\CaseStage.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.Collapsing.Statement
/-
  Theorem 4.8 for `ID_n` (`Statement.lean`), the case of the clause (W) for a stage predicate
  `I_j^{≺δ} t` at any level `j` — proved (no `sorry`).

  Source: W. Buchholz, *A simplified version of local predicativity* (1992), author preprint
  p. 27, proof of Theorem 4.8, case 2: the witness `ι₀` of a disjunction `⋁(A_ι)_{ι∈J} ∈ Σ(κ)`
  lies in `k(A_{ι₀}) ∩ κ ⊆ H_γ[Θ] ∩ κ ⊆ ψ_κ(γ + 1) ⊆ ψ_κ α̂`; A. Freund, arXiv:2204.09321,
  Theorem 6.7, case (W) (`ID1/Collapsing.lean`, case `stage`).

  **Across levels.**  The principal formula `I_j^{≺δ} t` is `Σ(Ω_{k+1})`, so `j ≤ k`.  The
  witness `g ≺ δ ⪯ Ω_{j+1} ⪯ Ω_{k+1}` lies in `H_γ[Θ] ∩ Ω_{k+1}`, hence below `ψ_k α̂` ((𝒜3)).
  The premise `A_j(t, I_j^{≺g})` is `Σ(Ω_{k+1})` for every `j ≤ k` (`sigmaW_unfold_le`: its
  stage parameters are `(j, g)`, `g ≠ Ω_{j+1}`, and the tops of the levels `< j`), so the side
  induction hypothesis collapses it at the same level `k`.

  The statement is `Cases.lean`'s `collapse_case_stage`, verbatim.
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

variable {A : FormJ}

/-- **Case `stage`**: (W) for `I_j^{≺δ} t` at any level `j` (Buchholz case 2; `j ≤ k` since
`Γ ⊆ Σ(Ω_{k+1})`). -/
theorem collapse_case_stage (hyp : CollapseHyps A) {m : WithTop ℕ} {α : ThetaVNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (hX : ThetaVNoteD.HullHypGe k γ X)
    {j : ℕ} {a : StageAt j} {t : SyntacticTerm LIinfW} (g : StageAt j)
    {α₀ : ThetaVNoteD}
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅)
    (hmem : stageAt (⟨j, a⟩ : Stage) t ∈ Γ) (hga : g.1 < a.1) (hgα : g.1 < α)
    (hgH : g.1 ∈ Hg γ X ∅) (h0 : α₀ < α)
    (d0 : IDwDerivable A (muBarW m) (Hg γ X) α₀ (unfoldW A j g t :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp hα
  have hα₀ : α₀ ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp d0.height_mem
  have hg' : g.1 ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp hgH
  -- the level of the principal formula is `≤ k`
  have hjk : j ≤ k := (sigmaW_stageAt_iff k (⟨j, a⟩ : Stage) t).mp (hΓ _ hmem)
  have hgΩj : g.1 < ThetaVNoteD.Omega j := lt_of_lt_of_le hga a.2
  have hΩjk : ThetaVNoteD.Omega j ≤ ThetaVNoteD.Omega k := by
    rcases Nat.lt_or_eq_of_le hjk with h | h
    · exact le_of_lt (ThetaVNoteD.Omega_lt_Omega_iff.mpr h)
    · rw [h]
  have hgΩ : g.1 < ThetaVNoteD.Omega k := lt_of_lt_of_le hgΩj hΩjk
  -- the premise is `Σ(Ω_{k+1})`
  have hne : (⟨j, g⟩ : Stage) ≠ Stage.top k := fun e => by
    have := congrArg Stage.val e
    rw [Stage.val_top] at this
    exact absurd this (ne_of_lt hgΩ)
  have hσ := (sigmaW_unfold_le A hjk hne t).1
  have D0 := sih α₀ h0 k γ X _ (sigmaW_cons hσ hΓ) hγ hX d0
  -- the collapsed clause
  have hθ := psi_hat_lt_psi_hat (k := k) (m := m) hX hγ hα₀ hα' h0
  have hop : ∀ Z, Hg (hat γ (muBarW m) α₀) X Z ⊆ Hg (hat γ (muBarW m) α) X Z :=
    Hg_mono (le_of_lt (hat_lt_hat γ _ h0)) X
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBarW m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  exact .stage g (mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')) hΓη hmem hga
    (lt_psi_hat hX hγ hα' hg' hgΩ) (Hg_mono (gamma_le_hat γ _ α) X ∅ hgH) hθ
    ((D0.mono_rank (le_of_lt hθ)).mono_op hop)

end Collapsing

end IDw

end OrdinalAnalysis
