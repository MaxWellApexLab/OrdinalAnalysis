/-
  **ASSEMBLY FILE — no `sorry`, no `axiom`.**
  Buchholz 1992, Theorem 4.8, for `ID_ω` (the statement lives in `Statement.lean`; see that
  file's header for sources, the doubled-`μ` deviation and the changes from `IDn`), assembled
  from the fourteen per-case obligations `CollapseCases A` (`Statement.lean`), taken here as a
  hypothesis: the case files `IDw/Collapsing/Case<Rule>.lean` prove them one by one
  (`collapse_case_<rule> hyp`), and the main line builds `CollapseCases A` from them.

  Transcribed from `IDn/Collapsing/Theorem.lean`.  Changes: the main induction runs over
  `m : WithTop ℕ` (`WellFoundedLT (WithTop ℕ)`), with no bound `m ≤ n`; the dispatch has the two
  new clauses `jlev`, `njlev`; the case lemmas enter through `C : CollapseCases A` instead of
  imports; `collapse_top`/`collapse_zero_top` are the limit instances used by the lower bound
  (design §4: embed, eliminate `Ω_ω + r → Ω_ω`, collapse at `m = ⊤`, `k = 0`, `γ = 0`, `X = ∅`).

  `collapseHyps_of` discharges `bound`/`negStage` from the merged `IDw/Boundedness.lean`
  (`boundedness`, `neg_stage_bound`), exactly as `IDn`; `positive` and `predCut` remain.
-/
import OrdinalAnalysis.IDw.Collapsing.Statement
import OrdinalAnalysis.IDw.Boundedness

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

variable {A : FormJ}

/-! ### The assembly -/

/-- **Theorem 4.8 from the case obligations**: main induction on `m : WithTop ℕ`, side
induction on `α`, dispatch on the last clause. -/
theorem claim_of_cases (C : CollapseCases A) :
    ∀ m : WithTop ℕ, ∀ α : ThetaVNoteD, Claim A m α := by
  intro m
  induction m using WellFoundedLT.induction with
  | ind m mih =>
  intro α
  induction α using WellFoundedLT.induction with
  | ind α sih =>
  intro k γ X Γ hΓ hγ hX d
  generalize hH : Hg γ X = H at d
  cases d with
  | literal hα hΓH hφ hmem =>
    subst hH; exact C.literal mih sih hΓ hγ hX hα hΓH hφ hmem
  | verum hα hΓH hmem =>
    subst hH; exact C.verum mih sih hΓ hγ hX hα hΓH hmem
  | idX t hα hΓH h1 h2 =>
    subst hH; exact C.idX mih sih hΓ hγ hX t hα hΓH h1 h2
  | and hα hΓH hmem h0 h1 d0 d1 =>
    subst hH; exact C.and mih sih hΓ hγ hX hα hΓH hmem h0 h1 d0 d1
  | orL hα hΓH hmem h0 d0 =>
    subst hH; exact C.orL mih sih hΓ hγ hX hα hΓH hmem h0 d0
  | orR hα hΓH hmem h1 h0 d0 =>
    subst hH; exact C.orR mih sih hΓ hγ hX hα hΓH hmem h1 h0 d0
  | all f hα hΓH hmem hf d0 =>
    subst hH; exact C.all mih sih hΓ hγ hX f hα hΓH hmem hf d0
  | exs i hα hΓH hmem hi h0 d0 =>
    subst hH; exact C.exs mih sih hΓ hγ hX i hα hΓH hmem hi h0 d0
  | stage g hα hΓH hmem hga hgα hgH h0 d0 =>
    subst hH; exact C.stage mih sih hΓ hγ hX g hα hΓH hmem hga hgα hgH h0 d0
  | nstage f hα hΓH hmem hf d0 =>
    subst hH; exact C.nstage mih sih hΓ hγ hX f hα hΓH hmem hf d0
  | fix hα hΓH hmem hΩ h0 d0 =>
    subst hH; exact C.fix mih sih hΓ hγ hX hα hΓH hmem hΩ h0 d0
  | jlev hα hΓH hmem hs ht hl h0 d0 =>
    subst hH; exact C.jlev mih sih hΓ hγ hX hα hΓH hmem hs ht hl h0 d0
  | njlev hα hΓH hmem hs ht h0 d0 =>
    subst hH; exact C.njlev mih sih hΓ hγ hX hα hΓH hmem hs ht h0 d0
  | cut hα hΓH hr h0 d0 d1 =>
    subst hH; exact C.cut mih sih hΓ hγ hX hα hΓH hr h0 d0 d1

/-- `IDn`'s name for `collapse` (kept for the transcription map): Theorem 4.8 from the case
obligations. -/
theorem collapse_of_cases (C : CollapseCases A) {m : WithTop ℕ} {k : ℕ} {γ α : ThetaVNoteD}
    {X : Set ThetaVNoteD} {Γ : Sequent LIinfW} (hΓ : ∀ φ ∈ Γ, SigmaW k φ)
    (hγ : γ ∈ ThetaVNoteD.HopS γ X) (hX : ThetaVNoteD.HullHypGe k γ X)
    (d : IDwDerivable A (muBarW m) (Hg γ X) α Γ) :
    IDwDerivable A (psi k (hat γ (muBarW m) α)) (Hg (hat γ (muBarW m) α) X)
      (psi k (hat γ (muBarW m) α)) Γ :=
  claim_of_cases C m α k γ X Γ hΓ hγ hX d

/-! ### `collapse` itself -/

/-- **Buchholz 1992, Theorem 4.8, for `ID_ω`** (collapsing and impredicative cut elimination,
every level `k : ℕ`, every `μ = Ω̄_m ∈ {0, Ω_1 + 1, Ω_2 + 1, …} ∪ {Ω_ω}`): for a `Σ(Ω_{k+1})`
sequent `Γ`, `γ ∈ H_γ[Θ]` and the hull hypothesis at every level `≥ k`,

    `H_γ[Θ] ⊢^α_μ Γ  ⇒  H_α̂[Θ] ⊢^{ψ_k α̂}_{ψ_k α̂} Γ`,   `α̂ = γ + ω^{μ+μ+α}`. -/
theorem collapse (C : CollapseCases A) {m : WithTop ℕ} {k : ℕ} {γ α : ThetaVNoteD}
    {X : Set ThetaVNoteD} {Γ : Sequent LIinfW} (hΓ : ∀ φ ∈ Γ, SigmaW k φ)
    (hγ : γ ∈ ThetaVNoteD.HopS γ X) (hX : ThetaVNoteD.HullHypGe k γ X)
    (d : IDwDerivable A (muBarW m) (Hg γ X) α Γ) :
    IDwDerivable A (psi k (hat γ (muBarW m) α)) (Hg (hat γ (muBarW m) α) X)
      (psi k (hat γ (muBarW m) α)) Γ :=
  claim_of_cases C m α k γ X Γ hΓ hγ hX d

/-- **The limit instance** `μ = Ω_ω` (`m = ⊤`): cut rank `Ω_ω` collapses to `ψ_k α̂`,
`α̂ = γ + ω^{Ω_ω+Ω_ω+α}`. -/
theorem collapse_top (C : CollapseCases A) {k : ℕ} {γ α : ThetaVNoteD}
    {X : Set ThetaVNoteD} {Γ : Sequent LIinfW} (hΓ : ∀ φ ∈ Γ, SigmaW k φ)
    (hγ : γ ∈ ThetaVNoteD.HopS γ X) (hX : ThetaVNoteD.HullHypGe k γ X)
    (d : IDwDerivable A ThetaVNoteD.OmegaW (Hg γ X) α Γ) :
    IDwDerivable A (psi k (hat γ ThetaVNoteD.OmegaW α)) (Hg (hat γ ThetaVNoteD.OmegaW α) X)
      (psi k (hat γ ThetaVNoteD.OmegaW α)) Γ :=
  collapse C (m := ⊤) hΓ hγ hX d

/-! ### The corollary (Buchholz p. 29; Freund Corollary 7.2), per level -/

theorem Hg_zero_empty : Hg ThetaVNoteD.zero ∅ = ThetaVNoteD.HopS ThetaVNoteD.zero := by
  funext Y; simp [Hg, ThetaVNoteD.adjoin]

theorem Hg_empty_eq (a : ThetaVNoteD) : Hg a ∅ = ThetaVNoteD.HopS a := by
  funext Y; simp [Hg, ThetaVNoteD.adjoin]

theorem hat_zero (μ α : ThetaVNoteD) :
    hat ThetaVNoteD.zero μ α = ThetaVNoteD.omegaPow (μ + μ + α) :=
  ThetaVNoteD.zero_add _

/-- **The corollary of Theorem 4.8, at level `k`** (`γ = 0`, `Θ = ∅`): for a `Σ(Ω_{k+1})`
sequent, `H_0 ⊢^α_{Ω̄_m} Γ  ⇒  H_η ⊢^{ψ_k η}_{ψ_k η} Γ`, `η = ω^{Ω̄_m + Ω̄_m + α}`. -/
theorem collapse_zero (C : CollapseCases A) {m : WithTop ℕ} (k : ℕ)
    {α : ThetaVNoteD} {Γ : Sequent LIinfW} (hΓ : ∀ φ ∈ Γ, SigmaW k φ)
    (d : IDwDerivable A (muBarW m) (ThetaVNoteD.HopS ThetaVNoteD.zero) α Γ) :
    IDwDerivable A (psi k (ThetaVNoteD.omegaPow (muBarW m + muBarW m + α)))
      (ThetaVNoteD.HopS (ThetaVNoteD.omegaPow (muBarW m + muBarW m + α)))
      (psi k (ThetaVNoteD.omegaPow (muBarW m + muBarW m + α))) Γ := by
  have h := collapse C (k := k) (γ := ThetaVNoteD.zero) (X := ∅) hΓ
    ((ThetaVNoteD.HopS_nice _).zero_mem) (fun _ _ _ _ _ => Set.empty_subset _)
    (by rw [Hg_zero_empty]; exact d)
  rwa [Hg_empty_eq, hat_zero] at h

/-- **The corollary at the limit** (`m = ⊤`, the lower bound's use, design §4):
`H_0 ⊢^α_{Ω_ω} Γ ⇒ H_η ⊢^{ψ_k η}_{ψ_k η} Γ`, `η = ω^{Ω_ω + Ω_ω + α}`. -/
theorem collapse_zero_top (C : CollapseCases A) (k : ℕ)
    {α : ThetaVNoteD} {Γ : Sequent LIinfW} (hΓ : ∀ φ ∈ Γ, SigmaW k φ)
    (d : IDwDerivable A ThetaVNoteD.OmegaW (ThetaVNoteD.HopS ThetaVNoteD.zero) α Γ) :
    IDwDerivable A
      (psi k (ThetaVNoteD.omegaPow (ThetaVNoteD.OmegaW + ThetaVNoteD.OmegaW + α)))
      (ThetaVNoteD.HopS (ThetaVNoteD.omegaPow (ThetaVNoteD.OmegaW + ThetaVNoteD.OmegaW + α)))
      (psi k (ThetaVNoteD.omegaPow (ThetaVNoteD.OmegaW + ThetaVNoteD.OmegaW + α))) Γ :=
  collapse_zero C (m := ⊤) k hΓ d

/-- **The corollary followed by boundedness at level `k`** (design note §2.7, steps 4–5):
`H_0 ⊢^α_{Ω̄_m} φ`, `φ ∈ Σ(Ω_{k+1})` give `H_η ⊢^β_β φ^β` with `β = ψ_k(ω^{Ω̄_m+Ω̄_m+α}) ≺ Ω_{k+1}`. -/
theorem collapse_zero_bound (hyp : CollapseHyps A) (C : CollapseCases A) {m : WithTop ℕ} (k : ℕ)
    {α : ThetaVNoteD} {φ : Proposition LIinfW} (hφ : SigmaW k φ)
    (d : IDwDerivable A (muBarW m) (ThetaVNoteD.HopS ThetaVNoteD.zero) α [φ]) :
    ∃ b : StageAt k, b.1 = psi k (ThetaVNoteD.omegaPow (muBarW m + muBarW m + α)) ∧
      IDwDerivable A b.1 (ThetaVNoteD.HopS (ThetaVNoteD.omegaPow (muBarW m + muBarW m + α))) b.1
        (capSeq k b [φ]) := by
  have D := collapse_zero C k (Γ := [φ])
    (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact hφ) d
  let b : StageAt k := ⟨psi k (ThetaVNoteD.omegaPow (muBarW m + muBarW m + α)),
    le_of_lt (psi_lt_Omega _ _)⟩
  have hbH : b.1 ∈ ThetaVNoteD.HopS (ThetaVNoteD.omegaPow (muBarW m + muBarW m + α)) ∅ := by
    have h := psi_hat_mem (k := k) (m := m) (γ := ThetaVNoteD.zero) (X := ∅) (α := α)
      (fun _ _ _ _ _ => Set.empty_subset _) ((ThetaVNoteD.HopS_nice _).zero_mem)
      (d.height_mem)
    rwa [hat_zero] at h
  exact ⟨b, rfl, hyp.bound k b (ThetaVNoteD.HopS_isOperator _) hbH le_rfl (psi_lt_Omega _ _) D⟩

/-! ### `CollapseHyps.bound` / `CollapseHyps.negStage` from `IDw/Boundedness.lean` -/

/-- Builds `CollapseHyps A` from `positive` and `predCut` alone: `bound` and `negStage` are the
merged `IDw/Boundedness.lean` theorems `boundedness` and `neg_stage_bound`. -/
theorem collapseHyps_of (positive : PositiveP A)
    (predCut : ∀ (s : ℕ) {γ' : ThetaVNoteD} {X : Set ThetaVNoteD} {β ρ₀ : ThetaVNoteD}
      {Γ : Sequent LIinfW},
      γ' ∈ ThetaVNoteD.HopS γ' X → ThetaVNoteD.HullHypGe (s + 1) γ' X →
      ThetaVNoteD.omegaPow (muBar (s + 2) + muBar (s + 2)) ≤ γ' →
      β ∈ ThetaVNoteD.HopS γ' X → ρ₀ ∈ ThetaVNoteD.HopS γ' X →
      muBar (s + 1) ≤ ρ₀ → ρ₀ < ThetaVNoteD.Omega (s + 1) → β < ThetaVNoteD.Omega (s + 1) →
      IDwDerivable A ρ₀ (Hg γ' X) β Γ →
      ∃ β' : ThetaVNoteD, β' ∈ ThetaVNoteD.HopS γ' X ∧ β' < ThetaVNoteD.Omega (s + 1) ∧
        IDwDerivable A (muBar (s + 1)) (Hg γ' X) β' Γ) :
    CollapseHyps A where
  positive := positive
  bound := fun k {ρ} {H} {α} {ψ} {Γ} b hH hbH hαb hbΩ d =>
    OrdinalAnalysis.IDw.boundedness (k := k) (ρ := ρ) (H := H) (α := α) (ψ := ψ) (Γ := Γ)
      (b := b) hH hbH hαb hbΩ d
  negStage := fun k {ρ} {H} {α} {t} {Γ} δ hH hδ d =>
    OrdinalAnalysis.IDw.neg_stage_bound (k := k) (ρ := ρ) (H := H) (α := α) (t := t) (Γ := Γ)
      (δ := δ) hH hδ d
  predCut := predCut

end Collapsing

end IDw

end OrdinalAnalysis
