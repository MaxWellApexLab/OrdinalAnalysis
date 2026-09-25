/-
  Predicative cut elimination for `ID_n`, at level `k`: Buchholz's Theorem 3.16 per level
  (Freund's Theorem 7.8 / Lemma 7.7 one level up), and its discharge of the collapsing
  theorem's hypothesis `CollapseHyps.predCut` (`IDn/Collapsing/Statement.lean`).

  Source: W. Buchholz, *A simplified version of local predicativity*, 1992, §1 ((φ.1)–(φ.4)),
  Theorem 3.16, Lemma 4.6 b); A. Freund, arXiv:2204.09321, Definition 7.6, Lemma 7.7,
  Theorem 7.8.

  **The theorem (`predicative_cut_elim`).**  For `k : ℕ` (Lean `Omega k` is `Ω_{k+1}`), a base
  rank `μ` such that no `Ω_j` lies in `[μ, Ω_{k+1})`, a nice `φ_k`-closed operator `H`, a cut
  rank `r ≺ Ω_{k+1}` with `r ∈ H(∅)` and a height `α ≺ Ω_{k+1}`:

      H ⊢^α_r Γ   ⇒   H ⊢^{φ_k(r, α)}_μ Γ,        φ_k(r, α) = ϑ_k(Ω_{k+1}·r + α).

  Buchholz states 3.16 as `H ⊢^α_{γ+ω^ρ} Γ ⇒ H ⊢^{φρα}_γ Γ`; here the Veblen index is the cut
  rank itself (a coarser bound, by (φ.4)), which removes every Cantor-normal-form decomposition
  of the rank segment from the proof (see `IDn/PredCutAux.lean`).  Proof: well-founded
  induction on `r` (`WellFoundedLT ThetaWNoteD`), inside it induction on the derivation
  (`predCut_aux`, `IDn/PredCutCases/Main.lean`, one case lemma per rule).

  **The adapter (`collapseHyps_predCut`).**  `CollapseHyps.predCut` verbatim, from
  `FamilyLevelBounded A` alone: `k = s + 1`, `μ = muBar (s + 1) = Ω_s + 1` (`noOmega_muBar`),
  `H = Hg γ' X` (nice; `φ_{s+1}`-closed by `phiClosed_HopS` from the field's hypothesis
  `ω^{muBar(s+2)+muBar(s+2)} ⪯ γ'`), `β' := φ_{s+1}(ρ₀, β)`.  `collapseHyps_of_levelBounded`
  then builds `CollapseHyps A` from `positive` and `levelBounded` only.
-/
import OrdinalAnalysis.IDn.PredCutCases.Main
import OrdinalAnalysis.IDn.Collapsing.Theorem

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder

variable {n : ℕ} {A : Fin n → Semisentence (LXIn n) 1}

/-- **Predicative cut elimination at level `k`** (Buchholz 1992, Theorem 3.16, with the cut
rank as Veblen index): if no `Ω_j` lies in `[μ, Ω_{k+1})`, then for every cut rank
`r ≺ Ω_{k+1}`, `H ⊢^α_r Γ` with `H` nice and `φ_k`-closed, `r ∈ H(∅)`, `α ≺ Ω_{k+1}` gives
`H ⊢^{φ_k(r, α)}_μ Γ`. -/
theorem predicative_cut_elim (hAb : FamilyLevelBounded A) {k : ℕ} {μ : ThetaWNoteD}
    (hμ : ∀ c : ThetaWNoteD, μ ≤ c → c < ThetaWNoteD.Omega k →
      ∀ j : Fin n, c ≠ ThetaWNoteD.Omega j.val) :
    ∀ r : ThetaWNoteD, r < ThetaWNoteD.Omega k → PredCutClaim A k μ r := by
  intro r
  induction r using (wellFounded_lt (α := ThetaWNoteD)).induction with
  | _ r ih =>
    intro hr H α Γ d
    exact predCut_aux hAb hμ hr (fun c hc => ih c hc (lt_trans hc hr)) d

/-- **`CollapseHyps.predCut`, discharged** (the field's statement verbatim): predicative cut
elimination on `(Ω_σ, Ω_{σ+1})`, `σ = s + 1`, for the operator `H_{γ'}[Θ]` of the step (□),
at the height `β' := φ_{s+1}(ρ₀, β)`. -/
theorem collapseHyps_predCut (hAb : FamilyLevelBounded A) :
    ∀ (s : ℕ) {γ' : ThetaWNoteD} {X : Set ThetaWNoteD} {β ρ₀ : ThetaWNoteD}
      {Γ : Sequent (LIinfN n)},
      γ' ∈ ThetaWNoteD.HopS γ' X → ThetaWNoteD.HullHypGe (s + 1) γ' X →
      ThetaWNoteD.omegaPow (Collapsing.muBar (s + 2) + Collapsing.muBar (s + 2)) ≤ γ' →
      β ∈ ThetaWNoteD.HopS γ' X → ρ₀ ∈ ThetaWNoteD.HopS γ' X →
      Collapsing.muBar (s + 1) ≤ ρ₀ → ρ₀ < ThetaWNoteD.Omega (s + 1) →
      β < ThetaWNoteD.Omega (s + 1) →
      IDnDerivable A ρ₀ (Collapsing.Hg γ' X) β Γ →
      ∃ β' : ThetaWNoteD, β' ∈ ThetaWNoteD.HopS γ' X ∧ β' < ThetaWNoteD.Omega (s + 1) ∧
        IDnDerivable A (Collapsing.muBar (s + 1)) (Collapsing.Hg γ' X) β' Γ := by
  intro s γ' X β ρ₀ Γ _ _ hω hβ hρ₀ _ hρ₀Ω hβΩ D
  have hP : ThetaWNoteD.PhiClosed (s + 1) (Collapsing.Hg γ' X) :=
    (ThetaWNoteD.phiClosed_HopS hω).adjoin X
  have hρ₀H : ρ₀ ∈ Collapsing.Hg γ' X ∅ := Collapsing.mem_Hg_empty.mpr hρ₀
  have hβH : β ∈ Collapsing.Hg γ' X ∅ := Collapsing.mem_Hg_empty.mpr hβ
  refine ⟨ThetaWNoteD.phiN (s + 1) ρ₀ β, ?_, ThetaWNoteD.phiN_lt_Omega _ _ _, ?_⟩
  · exact Collapsing.mem_Hg_empty.mp (hP ∅ ρ₀ β hρ₀Ω hβΩ hρ₀H hβH)
  · exact predicative_cut_elim hAb (noOmega_muBar s) ρ₀ hρ₀Ω D (Collapsing.Hg_niceS γ' X) hP
      hρ₀H hβΩ

/-- **`CollapseHyps A` from `positive` and `levelBounded` alone**: `bound`/`negStage` by
`Collapsing.collapseHyps_of` (`IDn/Boundedness.lean`), `predCut` by `collapseHyps_predCut`. -/
theorem collapseHyps_of_levelBounded
    (positive : ∀ k : Fin n, PositiveIn k (A k))
    (levelBounded : ∀ k : Fin n, LevelBounded k (A k)) : Collapsing.CollapseHyps A :=
  Collapsing.collapseHyps_of positive levelBounded (collapseHyps_predCut levelBounded)

end IDn

end OrdinalAnalysis
