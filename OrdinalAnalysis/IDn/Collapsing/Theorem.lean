/-
  **ASSEMBLY FILE — no `sorry`, no `axiom`.**
  Buchholz 1992, Theorem 4.8, for `ID_n` (the statement lives in `Statement.lean`; see that
  file's header for sources and the doubled-`μ` deviation), assembled from the twelve
  proved case lemmas `CaseFix.lean`, `CaseCut.lean`, `CaseStage.lean`, `CaseLiteral.lean`,
  `CaseVerum.lean`, `CaseIdX.lean`, `CaseAnd.lean`, `CaseOrL.lean`, `CaseOrR.lean`,
  `CaseAll.lean`, `CaseExs.lean`, `CaseNstage.lean`.

  This file, not `Statement.lean`, is where `collapse` and its corollaries live: every
  `Case<Rule>.lean` imports `Statement.lean`, so `Statement.lean` cannot import them back
  without a cycle.  `claim_of_cases`/`collapse_of_cases` (main induction on `m`, side
  induction on `α`, dispatch on the last clause of `IDnDerivable`) and the corollary section
  are carried over verbatim from the former `Cases.lean` (deleted at assembly; its twelve
  case-lemma *statements* live on, proved, as the `Case<Rule>.lean` files this module imports).

  Also: `collapseHyps_of` discharges the `bound` and `negStage` fields of `CollapseHyps` from
  the merged `IDn/Boundedness.lean` (`OrdinalAnalysis.IDn.boundedness`, `neg_stage_bound`),
  whose statements were written to match those fields exactly (see the doc comments there);
  only `positive`, `levelBounded`, `predCut` remain as hypotheses to build a `CollapseHyps`.
-/
import OrdinalAnalysis.IDn.Collapsing.CaseFix
import OrdinalAnalysis.IDn.Collapsing.CaseCut
import OrdinalAnalysis.IDn.Collapsing.CaseStage
import OrdinalAnalysis.IDn.Collapsing.CaseLiteral
import OrdinalAnalysis.IDn.Collapsing.CaseVerum
import OrdinalAnalysis.IDn.Collapsing.CaseIdX
import OrdinalAnalysis.IDn.Collapsing.CaseAnd
import OrdinalAnalysis.IDn.Collapsing.CaseOrL
import OrdinalAnalysis.IDn.Collapsing.CaseOrR
import OrdinalAnalysis.IDn.Collapsing.CaseAll
import OrdinalAnalysis.IDn.Collapsing.CaseExs
import OrdinalAnalysis.IDn.Collapsing.CaseNstage
import OrdinalAnalysis.IDn.Boundedness

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

namespace Collapsing

open LO LO.FirstOrder

variable {n : ℕ} {A : Fin n → Semisentence (LXIn n) 1}

/-! ### The assembly (no `sorry` of its own), carried over from `Cases.lean` -/

/-- **Theorem 4.8 from the case lemmas**: main induction on `m`, side induction on `α`,
dispatch on the last clause. -/
theorem claim_of_cases (hyp : CollapseHyps A) :
    ∀ m : ℕ, m ≤ n → ∀ α : ThetaWNoteD, Claim A m α := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m mih₀ =>
  intro hm α
  have mih : ∀ m' < m, ∀ α' : ThetaWNoteD, Claim A m' α' :=
    fun m' h' => mih₀ m' h' (le_trans (le_of_lt h') hm)
  induction α using WellFoundedLT.induction with
  | ind α sih =>
  intro k γ X Γ hΓ hγ hX d
  generalize hH : Hg γ X = H at d
  cases d with
  | literal hα hΓH hφ hmem =>
    subst hH; exact collapse_case_literal hyp hm mih sih hΓ hγ hX hα hΓH hφ hmem
  | verum hα hΓH hmem =>
    subst hH; exact collapse_case_verum hyp hm mih sih hΓ hγ hX hα hΓH hmem
  | idX t hα hΓH h1 h2 =>
    subst hH; exact collapse_case_idX hyp hm mih sih hΓ hγ hX t hα hΓH h1 h2
  | and hα hΓH hmem h0 h1 d0 d1 =>
    subst hH; exact collapse_case_and hyp hm mih sih hΓ hγ hX hα hΓH hmem h0 h1 d0 d1
  | orL hα hΓH hmem h0 d0 =>
    subst hH; exact collapse_case_orL hyp hm mih sih hΓ hγ hX hα hΓH hmem h0 d0
  | orR hα hΓH hmem h1 h0 d0 =>
    subst hH; exact collapse_case_orR hyp hm mih sih hΓ hγ hX hα hΓH hmem h1 h0 d0
  | all f hα hΓH hmem hf d0 =>
    subst hH; exact collapse_case_all hyp hm mih sih hΓ hγ hX f hα hΓH hmem hf d0
  | exs i hα hΓH hmem hi h0 d0 =>
    subst hH; exact collapse_case_exs hyp hm mih sih hΓ hγ hX i hα hΓH hmem hi h0 d0
  | stage g hα hΓH hmem hga hgα hgH h0 d0 =>
    subst hH
    exact collapse_case_stage hyp hm mih sih hΓ hγ hX g hα hΓH hmem hga hgα hgH h0 d0
  | nstage f hα hΓH hmem hf d0 =>
    subst hH; exact collapse_case_nstage hyp hm mih sih hΓ hγ hX f hα hΓH hmem hf d0
  | fix hα hΓH hmem hΩ h0 d0 =>
    subst hH; exact collapse_case_fix hyp hm mih sih hΓ hγ hX hα hΓH hmem hΩ h0 d0
  | cut hα hΓH hr h0 d0 d1 =>
    subst hH; exact collapse_case_cut hyp hm mih sih hΓ hγ hX hα hΓH hr h0 d0 d1

/-- `Statement.collapse`, verbatim, from the case lemmas. -/
theorem collapse_of_cases (hyp : CollapseHyps A) {m : ℕ} (hm : m ≤ n) {k : Fin n}
    {γ α : ThetaWNoteD} {X : Set ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaWNoteD.HopS γ X)
    (hX : ThetaWNoteD.HullHypGe k.val γ X) (d : IDnDerivable A (muBar m) (Hg γ X) α Γ) :
    IDnDerivable A (psi k.val (hat γ (muBar m) α)) (Hg (hat γ (muBar m) α) X)
      (psi k.val (hat γ (muBar m) α)) Γ :=
  claim_of_cases hyp m hm α k γ X Γ hΓ hγ hX d

/-! ### `collapse` itself -/

/-- **Buchholz 1992, Theorem 4.8, for `ID_n`** (collapsing and impredicative cut elimination,
every level; see `Statement.lean`'s header for sources and the doubled-`μ` deviation): for
`μ = Ω̄_m ∈ {0, Ω_1 + 1, …, Ω_n + 1}` (`m ≤ n`), `κ = Ω_{k+1}`, a `Σ(Ω_{k+1})` sequent `Γ`,
`γ ∈ H_γ[Θ]` and the hull hypothesis at every level `≥ k`,

    `H_γ[Θ] ⊢^α_μ Γ  ⇒  H_α̂[Θ] ⊢^{ψ_k α̂}_{ψ_k α̂} Γ`,   `α̂ = γ + ω^{μ+μ+α}`

(Buchholz: `γ + ω^{μ+α}`). Proved by main induction on `m`, side induction on `α`, and one case
lemma per clause of `IDnDerivable` (`collapse_of_cases`). -/
theorem collapse (hyp : CollapseHyps A) {m : ℕ} (hm : m ≤ n) {k : Fin n} {γ α : ThetaWNoteD}
    {X : Set ThetaWNoteD} {Γ : Sequent (LIinfN n)} (hΓ : ∀ φ ∈ Γ, SigmaW k φ)
    (hγ : γ ∈ ThetaWNoteD.HopS γ X) (hX : ThetaWNoteD.HullHypGe k.val γ X)
    (d : IDnDerivable A (muBar m) (Hg γ X) α Γ) :
    IDnDerivable A (psi k.val (hat γ (muBar m) α)) (Hg (hat γ (muBar m) α) X)
      (psi k.val (hat γ (muBar m) α)) Γ :=
  collapse_of_cases hyp hm hΓ hγ hX d

/-! ### The corollary (Buchholz p. 29; Freund Corollary 7.2), per level -/

theorem Hg_zero_empty : Hg ThetaWNoteD.zero ∅ = ThetaWNoteD.HopS ThetaWNoteD.zero := by
  funext Y; simp [Hg, ThetaWNoteD.adjoin]

theorem Hg_empty_eq (a : ThetaWNoteD) : Hg a ∅ = ThetaWNoteD.HopS a := by
  funext Y; simp [Hg, ThetaWNoteD.adjoin]

theorem hat_zero (μ α : ThetaWNoteD) :
    hat ThetaWNoteD.zero μ α = ThetaWNoteD.omegaPow (μ + μ + α) :=
  ThetaWNoteD.zero_add _

/-- **The corollary of Theorem 4.8, at level `k`** (`γ = 0`, `Θ = ∅`; Buchholz p. 29 at
`κ = Ω_1`, `μ = I + 1`; Freund Corollary 7.2 for `ID₁`): for a `Σ(Ω_{k+1})` sequent,

    `H_0 ⊢^α_{Ω̄_m} Γ  ⇒  H_η ⊢^{ψ_k η}_{ψ_k η} Γ`,   `η = ω^{Ω̄_m + Ω̄_m + α}`. -/
theorem collapse_zero (hyp : CollapseHyps A) {m : ℕ} (hm : m ≤ n) (k : Fin n)
    {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)} (hΓ : ∀ φ ∈ Γ, SigmaW k φ)
    (d : IDnDerivable A (muBar m) (ThetaWNoteD.HopS ThetaWNoteD.zero) α Γ) :
    IDnDerivable A (psi k.val (ThetaWNoteD.omegaPow (muBar m + muBar m + α)))
      (ThetaWNoteD.HopS (ThetaWNoteD.omegaPow (muBar m + muBar m + α)))
      (psi k.val (ThetaWNoteD.omegaPow (muBar m + muBar m + α))) Γ := by
  have h := collapse hyp hm (k := k) (γ := ThetaWNoteD.zero) (X := ∅) hΓ
    ((ThetaWNoteD.HopS_nice _).zero_mem) (fun _ _ _ _ _ => Set.empty_subset _)
    (by rw [Hg_zero_empty]; exact d)
  rwa [Hg_empty_eq, hat_zero] at h

/-- **The corollary followed by boundedness at level `k`** (design note §2.7, steps 4–5):
`H_0 ⊢^α_{Ω̄_m} φ`, `φ ∈ Σ(Ω_{k+1})` give `H_η ⊢^β_β φ^β` with `β = ψ_k(ω^{Ω̄_m+Ω̄_m+α}) ≺ Ω_{k+1}`. -/
theorem collapse_zero_bound (hyp : CollapseHyps A) {m : ℕ} (hm : m ≤ n) (k : Fin n)
    {α : ThetaWNoteD} {φ : Proposition (LIinfN n)} (hφ : SigmaW k φ)
    (d : IDnDerivable A (muBar m) (ThetaWNoteD.HopS ThetaWNoteD.zero) α [φ]) :
    ∃ b : StageAt k.val, b.1 = psi k.val (ThetaWNoteD.omegaPow (muBar m + muBar m + α)) ∧
      IDnDerivable A b.1 (ThetaWNoteD.HopS (ThetaWNoteD.omegaPow (muBar m + muBar m + α))) b.1
        (capSeq k b [φ]) := by
  have D := collapse_zero hyp hm k (Γ := [φ])
    (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hφ) d
  let b : StageAt k.val := ⟨psi k.val (ThetaWNoteD.omegaPow (muBar m + muBar m + α)),
    le_of_lt (psi_lt_Omega _ _)⟩
  have hbH : b.1 ∈ ThetaWNoteD.HopS (ThetaWNoteD.omegaPow (muBar m + muBar m + α)) ∅ := by
    have h := psi_hat_mem (k := k.val) (m := m) (γ := ThetaWNoteD.zero) (X := ∅) (α := α)
      (fun _ _ _ _ _ => Set.empty_subset _) ((ThetaWNoteD.HopS_nice _).zero_mem)
      (d.height_mem)
    rwa [hat_zero] at h
  exact ⟨b, rfl, hyp.bound k b (ThetaWNoteD.HopS_isOperator _) hbH le_rfl (psi_lt_Omega _ _) D⟩

/-! ### `CollapseHyps.bound` / `CollapseHyps.negStage` from `IDn/Boundedness.lean`

`Boundedness.lean`'s `boundedness` and `neg_stage_bound` were written (their doc comments say
so explicitly) to match `CollapseHyps.bound` and `CollapseHyps.negStage` verbatim, field for
field, hypothesis for hypothesis — compare `Statement.lean`'s `CollapseHyps` above with
`OrdinalAnalysis.IDn.boundedness` / `OrdinalAnalysis.IDn.neg_stage_bound`. So a `CollapseHyps`
needs only `positive`, `levelBounded` and `predCut` supplied; `bound` and `negStage` are
discharged here for free. -/

/-- Builds `CollapseHyps A` from `positive`, `levelBounded` and `predCut` alone: `bound` and
`negStage` are discharged from the merged `IDn/Boundedness.lean` theorems `boundedness` and
`neg_stage_bound`, which prove exactly those two fields. -/
theorem collapseHyps_of
    (positive : ∀ k : Fin n, PositiveIn k (A k))
    (levelBounded : ∀ k : Fin n, LevelBounded k (A k))
    (predCut : ∀ (s : ℕ) {γ' : ThetaWNoteD} {X : Set ThetaWNoteD} {β ρ₀ : ThetaWNoteD}
      {Γ : Sequent (LIinfN n)},
      γ' ∈ ThetaWNoteD.HopS γ' X → ThetaWNoteD.HullHypGe (s + 1) γ' X →
      ThetaWNoteD.omegaPow (muBar (s + 2) + muBar (s + 2)) ≤ γ' →
      β ∈ ThetaWNoteD.HopS γ' X → ρ₀ ∈ ThetaWNoteD.HopS γ' X →
      muBar (s + 1) ≤ ρ₀ → ρ₀ < ThetaWNoteD.Omega (s + 1) → β < ThetaWNoteD.Omega (s + 1) →
      IDnDerivable A ρ₀ (Hg γ' X) β Γ →
      ∃ β' : ThetaWNoteD, β' ∈ ThetaWNoteD.HopS γ' X ∧ β' < ThetaWNoteD.Omega (s + 1) ∧
        IDnDerivable A (muBar (s + 1)) (Hg γ' X) β' Γ) :
    CollapseHyps A where
  positive := positive
  levelBounded := levelBounded
  bound := fun k {ρ} {H} {α} {ψ} {Γ} b hH hbH hαb hbΩ d =>
    OrdinalAnalysis.IDn.boundedness (k := k) (ρ := ρ) (H := H) (α := α) (ψ := ψ) (Γ := Γ)
      (b := b) hH hbH hαb hbΩ d
  negStage := fun k {ρ} {H} {α} {t} {Γ} δ hH hδ d =>
    OrdinalAnalysis.IDn.neg_stage_bound (k := k) (ρ := ρ) (H := H) (α := α) (t := t) (Γ := Γ)
      (δ := δ) hH hδ d
  predCut := predCut

-- Remaining hypotheses of `collapseHyps_of`, after discharging `bound`/`negStage` from
-- `IDn/Boundedness.lean`: exactly `positive` (the operator forms are positive), `levelBounded`
-- (they mention only lower levels), and `predCut` (predicative cut elimination on every
-- interval `(Ω_σ, Ω_{σ+1})`, `σ ≥ 1`) — owned by `IDn/PredCut.lean`, not yet merged into a
-- single closed theorem the way boundedness is.

end Collapsing

end IDn

end OrdinalAnalysis
