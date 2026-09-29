import OrdinalAnalysis.IDw.Collapsing.Statement
/-
  Theorem 4.8 for `ID_ω` (`Statement.lean`), all `m : WithTop ℕ`, the case of the clause (jlev):
  (W) for `Jlev ℓ (s,t)`, the one relevant disjunct `I_{val s} t` (new in `ID_ω`; modelled on
  `CaseOrL.lean`) — proved (no `sorry`).

  Source: the design notes ("(Jlev) cases: like `orL`/`and`; the premise's
  `Σ(κ)` from `ℓ ≤ k`"); W. Buchholz, *A simplified version of local predicativity* (1992),
  author preprint p. 27, proof of Theorem 4.8, case 2 (a disjunction with one relevant disjunct);
  A. Freund, arXiv:2204.09321, Theorem 6.7, case (W) for `∨`.

  The principal formula `Jlev ℓ (s,t)` is `Σ(Ω_{k+1})`, i.e. `ℓ ≤ k` (`sigmaW_jlevAt_iff`), so
  `val s < ℓ ≤ k` and the premise `I_{val s} t` is `Σ(Ω_{k+1})` (`val s ≤ k`).  The side
  induction hypothesis collapses the premise `Γ, I_{val s} t` at the same level `k`, and the
  clause (jlev) is re-applied at the collapsed height `ψ_k α̂₀ ≺ ψ_k α̂`.  The clause needs no
  control on `Ω_{val s + 1}`: only the height and `paramsVal Γ` lie in the operator.

  The statement is `Statement.lean`'s field `CollapseCases.jlev`, verbatim.
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

variable {A : FormJ}

/-- **Case `jlev`**: (W) for `Jlev ℓ (s,t)`, the one disjunct `I_{val s} t`. -/
theorem collapse_case_jlev (hyp : CollapseHyps A) {m : WithTop ℕ} {α : ThetaVNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (hX : ThetaVNoteD.HullHypGe k γ X)
    {ℓ : WithTop ℕ} {s t : SyntacticTerm LIinfW} {α₀ : ThetaVNoteD}
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅) (hmem : jlevAt ℓ s t ∈ Γ)
    (hs : s.freeVariables = ∅) (ht : t.freeVariables = ∅)
    (hl : ((termVal s : ℕ) : WithTop ℕ) < ℓ) (h0 : α₀ < α)
    (d0 : IDwDerivable A (muBarW m) (Hg γ X) α₀ (IOmegaAt (termVal s) t :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp hα
  have hα₀ : α₀ ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp d0.height_mem
  -- `ℓ ≤ k`, hence `val s ≤ k` and the premise `I_{val s} t` is `Σ(Ω_{k+1})`
  have hℓ : ℓ ≤ (k : WithTop ℕ) := (sigmaW_jlevAt_iff k ℓ s t).mp (hΓ _ hmem)
  have hσ : SigmaW k (IOmegaAt (termVal s) t) :=
    WithTop.coe_le_coe.mp (le_trans hl.le hℓ)
  have D0 := sih α₀ h0 k γ X _ (sigmaW_cons hσ hΓ) hγ hX d0
  have hθ := psi_hat_lt_psi_hat (k := k) (m := m) hX hγ hα₀ hα' h0
  have hop : ∀ Z, Hg (hat γ (muBarW m) α₀) X Z ⊆ Hg (hat γ (muBarW m) α) X Z :=
    Hg_mono (le_of_lt (hat_lt_hat γ _ h0)) X
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBarW m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  have hηH : psi k (hat γ (muBarW m) α) ∈ Hg (hat γ (muBarW m) α) X ∅ :=
    mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')
  exact .jlev hηH hΓη hmem hs ht hl hθ ((D0.mono_rank (le_of_lt hθ)).mono_op hop)

end Collapsing

end IDw

end OrdinalAnalysis
