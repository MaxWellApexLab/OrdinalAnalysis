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
  numeral (`ThetaWNoteD.ofNat_lt_prin`).

  The statement is `Cases.lean`'s `collapse_case_exs`, verbatim.
-/
import OrdinalAnalysis.IDn.Collapsing.Statement

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

namespace Collapsing

open LO LO.FirstOrder

variable {n : ℕ} {A : Fin n → Semisentence (LXIn n) 1}

/-- **Case `exs`**: (W) for `∃x φ(x)`, witness `i ≺ α` (Buchholz case 2). -/
theorem collapse_case_exs (hyp : CollapseHyps A) {m : ℕ} (hm : m ≤ n) {α : ThetaWNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaWNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : Fin n} {γ : ThetaWNoteD} {X : Set ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaWNoteD.HopS γ X)
    (hX : ThetaWNoteD.HullHypGe k.val γ X)
    {φ : Semiproposition (LIinfN n) 1} (i : ℕ) {α₀ : ThetaWNoteD}
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅) (hmem : (∃¹ φ) ∈ Γ)
    (hi : ThetaWNoteD.ofNat i < α) (h0 : α₀ < α)
    (d0 : IDnDerivable A (muBar m) (Hg γ X) α₀ (φ/[numI i] :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp hα
  have hα₀ : α₀ ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp d0.height_mem
  have hσ : SigmaW k φ := (sigmaW_exs k φ).mp (hΓ _ hmem)
  have hσ' : SigmaW k (φ/[numI i]) := (sigmaW_subst k φ (numI i)).mpr hσ
  have D0 := sih α₀ h0 k γ X _ (sigmaW_cons hσ' hΓ) hγ hX d0
  have hθ := psi_hat_lt_psi_hat (k := k.val) (m := m) hX hγ hα₀ hα' h0
  have hop : ∀ Z, Hg (hat γ (muBar m) α₀) X Z ⊆ Hg (hat γ (muBar m) α) X Z :=
    Hg_mono (le_of_lt (hat_lt_hat γ _ h0)) X
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBar m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  have hηH : psi k.val (hat γ (muBar m) α) ∈ Hg (hat γ (muBar m) α) X ∅ :=
    mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')
  have hDα : (Notn.thetaWLevel k.val).D (hat γ (muBar m) α) := dom_hat hX hγ hα'
  have hp : ThetaWTerm.IsPrin (psi k.val (hat γ (muBar m) α)).1 :=
    (Notn.thetaWLevel k.val).isPrin_theta hDα
  exact .exs i hηH hΓη hmem (ThetaWNoteD.ofNat_lt_prin hp i) hθ
    ((D0.mono_rank (le_of_lt hθ)).mono_op hop)

end Collapsing

end IDn

end OrdinalAnalysis
