import OrdinalAnalysis.IDw.Collapsing.Statement
/-
  Theorem 4.8 for `ID_ω` (`Statement.lean`), all `m : WithTop ℕ`, the case of the clause (njlev):
  (V) for `¬Jlev ℓ (s,t)`, a conjunction with at most one conjunct `¬I_{val s} t` (new in
  `ID_ω`; modelled on `CaseAnd.lean`) — proved (no `sorry`).

  Source: the design notes ("(Jlev) cases: like `orL`/`and`; the premise's
  `Σ(κ)` from `ℓ ≤ k`"); W. Buchholz, *A simplified version of local predicativity* (1992),
  author preprint p. 27, proof of Theorem 4.8, case 1 (a conjunction, handled premise by
  premise by the side induction hypothesis); A. Freund, arXiv:2204.09321, Theorem 6.7, case (V)
  for `∧`.

  Two subcases, on whether `val s < ℓ`.
  * `val s ≥ ℓ` — the conjunction is empty (no premise): the clause (njlev) applies directly at
    any height in the collapsed operator, as for a true literal; the implications in its
    premises are vacuous.
  * `val s < ℓ` — the principal formula `¬Jlev ℓ (s,t)` is `Σ(Ω_{k+1})`, i.e. `ℓ ≤ k`
    (`sigmaW_njlevAt_iff`), so `val s < k` (strictly: `¬I_k t` is not in `Σ(Ω_{k+1})`) and the
    premise `¬I_{val s} t` is `Σ(Ω_{k+1})` (`sigmaW_nstageAt_iff`).  The side induction
    hypothesis collapses it at the same level `k` and (njlev) is re-applied at the collapsed
    height.

  The statement is `Statement.lean`'s field `CollapseCases.njlev`, verbatim.
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

variable {A : FormJ}

/-- **Case `njlev`**: (V) for `¬Jlev ℓ (s,t)`, at most one conjunct `¬I_{val s} t`. -/
theorem collapse_case_njlev (hyp : CollapseHyps A) {m : WithTop ℕ} {α : ThetaVNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (hX : ThetaVNoteD.HullHypGe k γ X)
    {ℓ : WithTop ℕ} {s t : SyntacticTerm LIinfW} {α₀ : ThetaVNoteD}
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅) (hmem : njlevAt ℓ s t ∈ Γ)
    (hs : s.freeVariables = ∅) (ht : t.freeVariables = ∅)
    (h0 : ((termVal s : ℕ) : WithTop ℕ) < ℓ → α₀ < α)
    (d0 : ((termVal s : ℕ) : WithTop ℕ) < ℓ →
      IDwDerivable A (muBarW m) (Hg γ X) α₀ (∼(IOmegaAt (termVal s) t) :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp hα
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBarW m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  have hηH : psi k (hat γ (muBarW m) α) ∈ Hg (hat γ (muBarW m) α) X ∅ :=
    mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')
  by_cases hl : ((termVal s : ℕ) : WithTop ℕ) < ℓ
  · -- one conjunct `¬I_{val s} t`
    have hℓ : ℓ ≤ (k : WithTop ℕ) := (sigmaW_njlevAt_iff k ℓ s t).mp (hΓ _ hmem)
    have hlk : termVal s < k := WithTop.coe_lt_coe.mp (lt_of_lt_of_le hl hℓ)
    have hσ : SigmaW k (∼(IOmegaAt (termVal s) t)) := by
      show SigmaW k (nstageAt (Stage.top (termVal s)) t)
      rw [sigmaW_nstageAt_iff]
      exact ⟨by simp; omega, fun h => by simp at h; omega⟩
    have d0' := d0 hl
    have h0' := h0 hl
    have hα₀ : α₀ ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp d0'.height_mem
    have D0 := sih α₀ h0' k γ X _ (sigmaW_cons hσ hΓ) hγ hX d0'
    have hθ := psi_hat_lt_psi_hat (k := k) (m := m) hX hγ hα₀ hα' h0'
    have hop : ∀ Z, Hg (hat γ (muBarW m) α₀) X Z ⊆ Hg (hat γ (muBarW m) α) X Z :=
      Hg_mono (le_of_lt (hat_lt_hat γ _ h0')) X
    exact .njlev hηH hΓη hmem hs ht (fun _ => hθ)
      (fun _ => (D0.mono_rank (le_of_lt hθ)).mono_op hop)
  · -- empty conjunction: no premise
    exact .njlev (α₀ := psi k (hat γ (muBarW m) α)) hηH hΓη hmem hs ht
      (fun h => absurd h hl) (fun h => absurd h hl)

end Collapsing

end IDw

end OrdinalAnalysis
