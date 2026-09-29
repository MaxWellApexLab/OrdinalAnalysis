/- Source: OrdinalAnalysis\IDn\Collapsing\CaseExs.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.Collapsing.Statement
/-
  Theorem 4.8 for `ID_n` (`Statement.lean`), the case of the clause (W) for `∃x φ(x)`, witness
  `i ≺ α` — proved (no `sorry`).

  Source: W. Buchholz, *A simplified version of local predicativity* (1992), author preprint
  p. 27, proof of Theorem 4.8, case 2 (the witness of a disjunction `⋁_{ι∈J}` lies in `H_γ[Θ] ∩
  κ`, hence below `ψ_κ α̂`; here the index set is `ω` itself, so the witness bound comes from
  `ψ_κ α̂` being principal, above every numeral, rather than from (𝒜3)); A. Freund,
  arXiv:2204.09321, Theorem 6.7, case (W)/`exs` (`ID1/Collapsing.lean`, case `exs` inside
  `collapsing_aux`).

  **Across levels.**  `∃x φ(x)` carries no stage parameter (as for `all`), so the premise
  `φ(ī) :: Γ` is `Σ(Ω_{k+1})` at the same level `k`, and the side induction hypothesis collapses
  it there directly.  The new witness bound `ī ≺ ψ_k α̂` holds because `ψ_k α̂` is principal
  (`isPrin_theta`, through the domain fact `dom_hat`) and every principal ordinal exceeds every
  numeral (`ThetaVNoteD.ofNat_lt_prin`).

  The statement is `Cases.lean`'s `collapse_case_exs`, verbatim.
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

variable {A : FormJ}

/-- **Case `exs`**: (W) for `∃x φ(x)`, witness `i ≺ α` (Buchholz case 2). -/
theorem collapse_case_exs (hyp : CollapseHyps A) {m : WithTop ℕ} {α : ThetaVNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (hX : ThetaVNoteD.HullHypGe k γ X)
    {φ : Semiproposition LIinfW 1} (i : ℕ) {α₀ : ThetaVNoteD}
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅) (hmem : (∃¹ φ) ∈ Γ)
    (hi : ThetaVNoteD.ofNat i < α) (h0 : α₀ < α)
    (d0 : IDwDerivable A (muBarW m) (Hg γ X) α₀ (φ/[numI i] :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp hα
  have hα₀ : α₀ ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp d0.height_mem
  have hσ : SigmaW k φ := (sigmaW_exs k φ).mp (hΓ _ hmem)
  have hσ' : SigmaW k (φ/[numI i]) := (sigmaW_subst k φ (numI i)).mpr hσ
  have D0 := sih α₀ h0 k γ X _ (sigmaW_cons hσ' hΓ) hγ hX d0
  have hθ := psi_hat_lt_psi_hat (k := k) (m := m) hX hγ hα₀ hα' h0
  have hop : ∀ Z, Hg (hat γ (muBarW m) α₀) X Z ⊆ Hg (hat γ (muBarW m) α) X Z :=
    Hg_mono (le_of_lt (hat_lt_hat γ _ h0)) X
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBarW m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  have hηH : psi k (hat γ (muBarW m) α) ∈ Hg (hat γ (muBarW m) α) X ∅ :=
    mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')
  have hDα : (Notn.thetaVLevel k).D (hat γ (muBarW m) α) := dom_hat hX hγ hα'
  have hp : ThetaVTerm.IsPrin (psi k (hat γ (muBarW m) α)).1 :=
    (Notn.thetaVLevel k).isPrin_theta hDα
  exact .exs i hηH hΓη hmem (ThetaVNoteD.ofNat_lt_prin hp i) hθ
    ((D0.mono_rank (le_of_lt hθ)).mono_op hop)

end Collapsing

end IDw

end OrdinalAnalysis
