/- Source: OrdinalAnalysis\IDn\Collapsing\CaseNstage.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.Collapsing.Statement
/-
  Theorem 4.8 for `ID_n` (`Statement.lean`), the case of the clause (V) for `¬I_j^{≺a} t` at any
  level `j` — proved (no `sorry`).

  Source: W. Buchholz, *A simplified version of local predicativity* (1992), author preprint
  p. 27, proof of Theorem 4.8, case 1: for `¬I_j^{≺a} t ≃ ⋀_{g≺a} ¬A_j(t, I_j^{≺g})`, the index
  set is bounded by `a ∈ H_γ[Θ] ∩ Ω_{k+1}`, so every `g ≺ a` may be adjoined to `Θ`, keeping
  `𝒜(Θ ∪ {g}; γ, κ, μ)`; A. Freund, arXiv:2204.09321, Theorem 6.7, case (V)/`nstage`
  (`ID1/Collapsing.lean`, case `nstage` inside `collapsing_aux`).

  **Across levels.**  The principal formula `¬I_j^{≺a} t` is `Σ(Ω_{k+1})`, so `j ≤ k` and
  `⟨j,a⟩ ≠ Stage.top k`, whence `a.1 ≺ Ω_{k+1}` (`sigmaW_nstageAt_iff`).  For each `g ≺ a`, the
  premise `¬A_j(t, I_j^{≺g})` is `Σ(Ω_{k+1})` for every `j ≤ k` (`sigmaW_unfold_le`, as in
  `stage`), and the side induction hypothesis collapses it at the same level `k`, with `Θ ∪ {g}`
  in place of `Θ` (Exercise 6.6's `X ∪ {g.1}` reading, via `HullHypGe.union_singleton`, exactly
  as in `ID1/Collapsing.lean`'s `nstage` case, which adjoins `X ∪ {g.1}` and calls the induction
  hypothesis with `α` unchanged since only `Θ`, not `γ`, moves).  Bookkeeping-wise the target
  operator's own adjunction `Hg (hat γ (muBarW m) α) X [{g.1}]` is exactly
  `Hg (hat γ (muBarW m) α) (X ∪ {g.1})` (`Hg_adjoin`), which is what `IDwDerivable.nstage`'s
  premise clause asks for.

  The statement is `Cases.lean`'s `collapse_case_nstage`, verbatim.
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

variable {A : FormJ}

/-- **Case `nstage`**: (V) for `¬I_j^{≺δ} t` at any level `j` (Buchholz case 1: the index set is
bounded by `δ ∈ H_γ[Θ] ∩ Ω_{k+1}`, and `Θ ∪ {g}` keeps `𝒜`). -/
theorem collapse_case_nstage (hyp : CollapseHyps A) {m : WithTop ℕ} {α : ThetaVNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (hX : ThetaVNoteD.HullHypGe k γ X)
    {j : ℕ} {a : StageAt j} {t : SyntacticTerm LIinfW}
    (f : StageAt j → ThetaVNoteD)
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅)
    (hmem : nstageAt (⟨j, a⟩ : Stage) t ∈ Γ)
    (hf : ∀ g : StageAt j, g.1 < a.1 → f g < α)
    (d0 : ∀ g : StageAt j, g.1 < a.1 →
      IDwDerivable A (muBarW m) (ThetaVNoteD.adjoin (Hg γ X) {g.1}) (f g)
        (∼(unfoldW A j g t) :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp hα
  -- the level of the principal formula is `≤ k`, and its bound is `≺ Ω_{k+1}`
  have hΓmem := (sigmaW_nstageAt_iff k (⟨j, a⟩ : Stage) t).mp (hΓ _ hmem)
  have hjk : j ≤ k := hΓmem.1
  have hane : (⟨j, a⟩ : Stage) ≠ Stage.top k := hΓmem.2
  have hΩjk : ThetaVNoteD.Omega j ≤ ThetaVNoteD.Omega k := by
    rcases Nat.lt_or_eq_of_le hjk with h | h
    · exact le_of_lt (ThetaVNoteD.Omega_lt_Omega_iff.mpr h)
    · rw [h]
  have haΩ : a.1 < ThetaVNoteD.Omega k := by
    rcases lt_or_eq_of_le (le_trans a.2 hΩjk) with h | heq
    · exact h
    · exfalso
      have hjk' : j = k := by
        by_contra hne'
        have hlt : j < k := lt_of_le_of_ne hjk hne'
        have hom : ThetaVNoteD.Omega j < ThetaVNoteD.Omega k :=
          ThetaVNoteD.Omega_lt_Omega_iff.mpr hlt
        rw [← heq] at hom
        exact absurd a.2 (not_le_of_gt hom)
      exact hane ((stage_eq_top_iff_of_lvl_eq (s := (⟨j, a⟩ : Stage)) hjk').mpr heq)
  -- `a.1 ∈ H_γ[Θ]`, from the parameters of the principal formula
  have haH : a.1 ∈ ThetaVNoteD.HopS γ X :=
    mem_Hg_empty.mp
      (hΓH (mem_paramsVal_of_mem_params (s := (⟨j, a⟩ : Stage)) hmem
        (by rw [params_nstageAt]; exact rfl)))
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBarW m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  have hηH : psi k (hat γ (muBarW m) α) ∈ Hg (hat γ (muBarW m) α) X ∅ :=
    mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')
  -- for each `g ≺ a`: collapse the premise with `Θ ∪ {g}` at the same level `k`, then boost
  have step : ∀ g : StageAt j, g.1 < a.1 →
      psi k (hat γ (muBarW m) (f g)) < psi k (hat γ (muBarW m) α) ∧
      IDwDerivable A (psi k (hat γ (muBarW m) α))
        (ThetaVNoteD.adjoin (Hg (hat γ (muBarW m) α) X) {g.1})
        (psi k (hat γ (muBarW m) (f g))) (∼(unfoldW A j g t) :: Γ) := by
    intro g hg
    have hgΩj : g.1 < ThetaVNoteD.Omega j := lt_of_lt_of_le hg a.2
    have hgΩ : g.1 < ThetaVNoteD.Omega k := lt_of_lt_of_le hgΩj hΩjk
    have hgne : (⟨j, g⟩ : Stage) ≠ Stage.top k := fun e => by
      have := congrArg Stage.val e
      rw [Stage.val_top] at this
      exact absurd this (ne_of_lt hgΩ)
    have hσg := (sigmaW_unfold_le A hjk hgne t).2
    have hX' : ThetaVNoteD.HullHypGe k γ (X ∪ {g.1}) := hX.union_singleton haH haΩ hg
    have hγX' : γ ∈ ThetaVNoteD.HopS γ (X ∪ {g.1}) :=
      ThetaVNoteD.HopS_mono Set.subset_union_left hγ
    have hαX' : α ∈ ThetaVNoteD.HopS γ (X ∪ {g.1}) :=
      ThetaVNoteD.HopS_mono Set.subset_union_left hα'
    have d0' : IDwDerivable A (muBarW m) (Hg γ (X ∪ {g.1})) (f g)
        (∼(unfoldW A j g t) :: Γ) := by
      rw [← Hg_adjoin]; exact d0 g hg
    have hfgH : f g ∈ ThetaVNoteD.HopS γ (X ∪ {g.1}) := mem_Hg_empty.mp d0'.height_mem
    have D0 := sih (f g) (hf g hg) k γ (X ∪ {g.1}) _ (sigmaW_cons hσg hΓ) hγX' hX' d0'
    have hθ := psi_hat_lt_psi_hat (k := k) (m := m) hX' hγX' hfgH hαX' (hf g hg)
    have hop' : ∀ Z, Hg (hat γ (muBarW m) (f g)) (X ∪ {g.1}) Z ⊆
        ThetaVNoteD.adjoin (Hg (hat γ (muBarW m) α) X) {g.1} Z := by
      intro Z
      rw [Hg_adjoin]
      exact Hg_mono (le_of_lt (hat_lt_hat γ _ (hf g hg))) (X ∪ {g.1}) Z
    exact ⟨hθ, (D0.mono_rank (le_of_lt hθ)).mono_op hop'⟩
  exact .nstage (fun g => psi k (hat γ (muBarW m) (f g))) hηH hΓη hmem
    (fun g hg => (step g hg).1) (fun g hg => (step g hg).2)

end Collapsing

end IDw

end OrdinalAnalysis
