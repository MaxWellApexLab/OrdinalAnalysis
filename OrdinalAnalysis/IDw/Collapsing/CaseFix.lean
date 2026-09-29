import OrdinalAnalysis.IDw.Collapsing.Statement
import OrdinalAnalysis.IDw.Boundedness
/-
  Theorem 4.8 for `ID_ω` (`Statement.lean`), all `m : WithTop ℕ` (transcribed from
  `IDn/Collapsing/CaseFix.lean`), the case of the clause (Fix) at a level `j`
  (the `Ω_{j+1}`-rule) — proved (no `sorry`).

  Source: A. Freund, arXiv:2204.09321, Theorem 6.7, case (Fix) (`ID1/Collapsing.lean`, case
  `fix`), with Theorem 5.9 (boundedness); W. Buchholz, *A simplified version of local
  predicativity* (1992), author preprint p. 27, proof of Theorem 4.8, cases 2 and 3 (Buchholz's
  `KPi` calculus has (Ref) in place of (Fix); the (Fix) clause is Freund's, per level).

  **Across levels.**  The principal formula `I_j t` is `Σ(Ω_{k+1})`, so `j ≤ k`.
  * `j = k` — Freund's case: the premise `Γ, A_k(t, I_k^{≺Ω_{k+1}})` is `Σ(Ω_{k+1})` (`A_k`
    positive in `I_k`, the `Q ↦ Jlev` slot is automatic); the side induction hypothesis collapses it to height
    `b := ψ_k α̂₀`; boundedness at level `k`, stage `b`, gives `Γ, A_k(t, I_k^{≺b})`; the clause
    (W) on `I_k t = I_k^{≺Ω_{k+1}} t` with the witness `b ≺ ψ_k α̂` concludes.
  * `j < k` — the premise `A_j(t, I_j^{≺Ω_{j+1}})` has only stage parameters of level `≤ j < k`,
    so it is `Σ(Ω_{k+1})` (`sigmaW_unfold_le`); it is collapsed at level `k` and (Fix) at level
    `j` is re-applied: its side condition `Ω_{j+1} ⪯ ψ_k α̂` holds since `Ω_{j+1} ⪯ Ω_k ≺ ψ_k α̂`
    (`Omega_le_psi`).  This is Buchholz's case 3 ((Ref), "follows immediately from (1), (2),
    and the S.I.H.").

  The statement is `Cases.lean`'s `collapse_case_fix`, verbatim.
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

variable {A : FormJ}

/-- **Case `fix`**: (Fix) at level `j` (the `Ω_{j+1}`-rule; `j ≤ k` since `Γ ⊆ Σ(Ω_{k+1})`;
`j = k` is Freund's (Fix) case of Theorem 6.7, `j < k` a plain (Ref)-like re-application). -/
theorem collapse_case_fix (hyp : CollapseHyps A) {m : WithTop ℕ} {α : ThetaVNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (hX : ThetaVNoteD.HullHypGe k γ X)
    {j : ℕ} {t : SyntacticTerm LIinfW} {α₀ : ThetaVNoteD}
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅) (hmem : IOmegaAt j t ∈ Γ)
    (hΩ : ThetaVNoteD.Omega j ≤ α) (h0 : α₀ < α)
    (d0 : IDwDerivable A (muBarW m) (Hg γ X) α₀
      (unfoldW A j (StageAt.top j) t :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp hα
  have hα₀ : α₀ ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp d0.height_mem
  -- the level of the principal formula is `≤ k`
  have hjk : j ≤ k := (sigmaW_stageAt_iff k (Stage.top j) t).mp (hΓ _ hmem)
  have hθ := psi_hat_lt_psi_hat (k := k) (m := m) hX hγ hα₀ hα' h0
  have hop : ∀ Z, Hg (hat γ (muBarW m) α₀) X Z ⊆ Hg (hat γ (muBarW m) α) X Z :=
    Hg_mono (le_of_lt (hat_lt_hat γ _ h0)) X
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBarW m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  have hηH : psi k (hat γ (muBarW m) α) ∈ Hg (hat γ (muBarW m) α) X ∅ :=
    mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')
  rcases Nat.lt_or_eq_of_le hjk with hlt | heq
  · -- `j < k`: collapse the premise at level `k`, re-apply (Fix) at level `j`
    have hne : (⟨j, StageAt.top j⟩ : Stage) ≠ Stage.top k := fun e => by
      have := congrArg (fun s : Stage => s.lvl) e
      simp only [Stage.lvl_top] at this
      exact absurd this (Nat.ne_of_lt hlt)
    have hσ := (sigmaW_unfold_le A (le_of_lt hlt) hne t).1
    have D0 := sih α₀ h0 k γ X _ (sigmaW_cons hσ hΓ) hγ hX d0
    exact .fix hηH hΓη hmem (Omega_le_psi hlt (dom_hat hX hγ hα')) hθ
      ((D0.mono_rank (le_of_lt hθ)).mono_op hop)
  · -- `j = k`: Freund's (Fix) case
    have hjk' : j = k := heq
    subst hjk'
    have hσ := sigmaW_unfold_top A hyp.positive (k := j) t
    have D0 := sih α₀ h0 j γ X _ (sigmaW_cons hσ hΓ) hγ hX d0
    let b : StageAt j := ⟨psi j (hat γ (muBarW m) α₀), le_of_lt (psi_lt_Omega _ _)⟩
    have hbH : b.1 ∈ Hg (hat γ (muBarW m) α₀) X ∅ :=
      mem_Hg_empty.mpr (psi_hat_mem hX hγ hα₀)
    have D1 := hyp.bound j b (Hg_isOperator _ _) hbH le_rfl (psi_lt_Omega _ _) D0
    rw [capAt_unfoldW_top] at D1
    exact .stage (a := StageAt.top j) b hηH hΓη hmem (psi_lt_Omega _ _) hθ
      (Hg_mono (le_of_lt (hat_lt_hat γ _ h0)) X ∅ hbH) hθ
      ((D1.mono_rank (le_of_lt hθ)).mono_op hop)

end Collapsing

end IDw

end OrdinalAnalysis
