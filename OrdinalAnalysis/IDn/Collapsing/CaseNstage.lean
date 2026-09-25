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
  operator's own adjunction `Hg (hat γ (muBar m) α) X [{g.1}]` is exactly
  `Hg (hat γ (muBar m) α) (X ∪ {g.1})` (`Hg_adjoin`), which is what `IDnDerivable.nstage`'s
  premise clause asks for.

  The statement is `Cases.lean`'s `collapse_case_nstage`, verbatim.
-/
import OrdinalAnalysis.IDn.Collapsing.Statement

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

namespace Collapsing

open LO LO.FirstOrder

variable {n : ℕ} {A : Fin n → Semisentence (LXIn n) 1}

/-- **Case `nstage`**: (V) for `¬I_j^{≺δ} t` at any level `j` (Buchholz case 1: the index set is
bounded by `δ ∈ H_γ[Θ] ∩ Ω_{k+1}`, and `Θ ∪ {g}` keeps `𝒜`). -/
theorem collapse_case_nstage (hyp : CollapseHyps A) {m : ℕ} (hm : m ≤ n) {α : ThetaWNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaWNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : Fin n} {γ : ThetaWNoteD} {X : Set ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaWNoteD.HopS γ X)
    (hX : ThetaWNoteD.HullHypGe k.val γ X)
    {j : Fin n} {a : StageAt j.val} {t : SyntacticTerm (LIinfN n)}
    (f : StageAt j.val → ThetaWNoteD)
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅)
    (hmem : nstageAt (⟨j, a⟩ : Stage n) t ∈ Γ)
    (hf : ∀ g : StageAt j.val, g.1 < a.1 → f g < α)
    (d0 : ∀ g : StageAt j.val, g.1 < a.1 →
      IDnDerivable A (muBar m) (ThetaWNoteD.adjoin (Hg γ X) {g.1}) (f g)
        (∼(unfold (A j) j g t) :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp hα
  -- the level of the principal formula is `≤ k`, and its bound is `≺ Ω_{k+1}`
  have hΓmem := (sigmaW_nstageAt_iff k (⟨j, a⟩ : Stage n) t).mp (hΓ _ hmem)
  have hjk : j.val ≤ k.val := hΓmem.1
  have hane : (⟨j, a⟩ : Stage n) ≠ Stage.top k := hΓmem.2
  have hΩjk : ThetaWNoteD.Omega j.val ≤ ThetaWNoteD.Omega k.val := by
    rcases Nat.lt_or_eq_of_le hjk with h | h
    · exact le_of_lt (ThetaWNoteD.Omega_lt_Omega_iff.mpr h)
    · rw [h]
  have haΩ : a.1 < ThetaWNoteD.Omega k.val := by
    rcases lt_or_eq_of_le (le_trans a.2 hΩjk) with h | heq
    · exact h
    · exfalso
      have hjk' : j.val = k.val := by
        by_contra hne'
        have hlt : j.val < k.val := lt_of_le_of_ne hjk hne'
        have hom : ThetaWNoteD.Omega j.val < ThetaWNoteD.Omega k.val :=
          ThetaWNoteD.Omega_lt_Omega_iff.mpr hlt
        rw [← heq] at hom
        exact absurd a.2 (not_le_of_gt hom)
      exact hane ((stage_eq_top_iff_of_lvl_eq (s := (⟨j, a⟩ : Stage n)) (Fin.ext hjk')).mpr heq)
  -- `a.1 ∈ H_γ[Θ]`, from the parameters of the principal formula
  have haH : a.1 ∈ ThetaWNoteD.HopS γ X :=
    mem_Hg_empty.mp
      (hΓH (mem_paramsVal_of_mem_params (s := (⟨j, a⟩ : Stage n)) hmem
        (by rw [params_nstageAt]; exact rfl)))
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBar m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  have hηH : psi k.val (hat γ (muBar m) α) ∈ Hg (hat γ (muBar m) α) X ∅ :=
    mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')
  -- for each `g ≺ a`: collapse the premise with `Θ ∪ {g}` at the same level `k`, then boost
  have step : ∀ g : StageAt j.val, g.1 < a.1 →
      psi k.val (hat γ (muBar m) (f g)) < psi k.val (hat γ (muBar m) α) ∧
      IDnDerivable A (psi k.val (hat γ (muBar m) α))
        (ThetaWNoteD.adjoin (Hg (hat γ (muBar m) α) X) {g.1})
        (psi k.val (hat γ (muBar m) (f g))) (∼(unfold (A j) j g t) :: Γ) := by
    intro g hg
    have hgΩj : g.1 < ThetaWNoteD.Omega j.val := lt_of_lt_of_le hg a.2
    have hgΩ : g.1 < ThetaWNoteD.Omega k.val := lt_of_lt_of_le hgΩj hΩjk
    have hgne : (⟨j, g⟩ : Stage n) ≠ Stage.top k := fun e => by
      have := congrArg Stage.val e
      rw [Stage.val_top] at this
      exact absurd this (ne_of_lt hgΩ)
    have hσg := (sigmaW_unfold_le (hyp.levelBounded j) hjk hgne t).2
    have hX' : ThetaWNoteD.HullHypGe k.val γ (X ∪ {g.1}) := hX.union_singleton haH haΩ hg
    have hγX' : γ ∈ ThetaWNoteD.HopS γ (X ∪ {g.1}) :=
      ThetaWNoteD.HopS_mono Set.subset_union_left hγ
    have hαX' : α ∈ ThetaWNoteD.HopS γ (X ∪ {g.1}) :=
      ThetaWNoteD.HopS_mono Set.subset_union_left hα'
    have d0' : IDnDerivable A (muBar m) (Hg γ (X ∪ {g.1})) (f g)
        (∼(unfold (A j) j g t) :: Γ) := by
      rw [← Hg_adjoin]; exact d0 g hg
    have hfgH : f g ∈ ThetaWNoteD.HopS γ (X ∪ {g.1}) := mem_Hg_empty.mp d0'.height_mem
    have D0 := sih (f g) (hf g hg) k γ (X ∪ {g.1}) _ (sigmaW_cons hσg hΓ) hγX' hX' d0'
    have hθ := psi_hat_lt_psi_hat (k := k.val) (m := m) hX' hγX' hfgH hαX' (hf g hg)
    have hop' : ∀ Z, Hg (hat γ (muBar m) (f g)) (X ∪ {g.1}) Z ⊆
        ThetaWNoteD.adjoin (Hg (hat γ (muBar m) α) X) {g.1} Z := by
      intro Z
      rw [Hg_adjoin]
      exact Hg_mono (le_of_lt (hat_lt_hat γ _ (hf g hg))) (X ∪ {g.1}) Z
    exact ⟨hθ, (D0.mono_rank (le_of_lt hθ)).mono_op hop'⟩
  exact .nstage (fun g => psi k.val (hat γ (muBar m) (f g))) hηH hΓη hmem
    (fun g hg => (step g hg).1) (fun g hg => (step g hg).2)

end Collapsing

end IDn

end OrdinalAnalysis
