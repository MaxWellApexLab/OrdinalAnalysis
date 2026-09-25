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
import OrdinalAnalysis.IDn.Collapsing.Statement

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

namespace Collapsing

open LO LO.FirstOrder

variable {n : ℕ} {A : Fin n → Semisentence (LXIn n) 1}

/-- **Case `stage`**: (W) for `I_j^{≺δ} t` at any level `j` (Buchholz case 2; `j ≤ k` since
`Γ ⊆ Σ(Ω_{k+1})`). -/
theorem collapse_case_stage (hyp : CollapseHyps A) {m : ℕ} (hm : m ≤ n) {α : ThetaWNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaWNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : Fin n} {γ : ThetaWNoteD} {X : Set ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaWNoteD.HopS γ X)
    (hX : ThetaWNoteD.HullHypGe k.val γ X)
    {j : Fin n} {a : StageAt j.val} {t : SyntacticTerm (LIinfN n)} (g : StageAt j.val)
    {α₀ : ThetaWNoteD}
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅)
    (hmem : stageAt (⟨j, a⟩ : Stage n) t ∈ Γ) (hga : g.1 < a.1) (hgα : g.1 < α)
    (hgH : g.1 ∈ Hg γ X ∅) (h0 : α₀ < α)
    (d0 : IDnDerivable A (muBar m) (Hg γ X) α₀ (unfold (A j) j g t :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp hα
  have hα₀ : α₀ ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp d0.height_mem
  have hg' : g.1 ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp hgH
  -- the level of the principal formula is `≤ k`
  have hjk : j.val ≤ k.val := (sigmaW_stageAt_iff k (⟨j, a⟩ : Stage n) t).mp (hΓ _ hmem)
  have hgΩj : g.1 < ThetaWNoteD.Omega j.val := lt_of_lt_of_le hga a.2
  have hΩjk : ThetaWNoteD.Omega j.val ≤ ThetaWNoteD.Omega k.val := by
    rcases Nat.lt_or_eq_of_le hjk with h | h
    · exact le_of_lt (ThetaWNoteD.Omega_lt_Omega_iff.mpr h)
    · rw [h]
  have hgΩ : g.1 < ThetaWNoteD.Omega k.val := lt_of_lt_of_le hgΩj hΩjk
  -- the premise is `Σ(Ω_{k+1})`
  have hne : (⟨j, g⟩ : Stage n) ≠ Stage.top k := fun e => by
    have := congrArg Stage.val e
    rw [Stage.val_top] at this
    exact absurd this (ne_of_lt hgΩ)
  have hσ := (sigmaW_unfold_le (hyp.levelBounded j) hjk hne t).1
  have D0 := sih α₀ h0 k γ X _ (sigmaW_cons hσ hΓ) hγ hX d0
  -- the collapsed clause
  have hθ := psi_hat_lt_psi_hat (k := k.val) (m := m) hX hγ hα₀ hα' h0
  have hop : ∀ Z, Hg (hat γ (muBar m) α₀) X Z ⊆ Hg (hat γ (muBar m) α) X Z :=
    Hg_mono (le_of_lt (hat_lt_hat γ _ h0)) X
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBar m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  exact .stage g (mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')) hΓη hmem hga
    (lt_psi_hat hX hγ hα' hg' hgΩ) (Hg_mono (gamma_le_hat γ _ α) X ∅ hgH) hθ
    ((D0.mono_rank (le_of_lt hθ)).mono_op hop)

end Collapsing

end IDn

end OrdinalAnalysis
