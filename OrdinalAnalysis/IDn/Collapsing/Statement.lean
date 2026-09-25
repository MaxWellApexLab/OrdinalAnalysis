/-
  **ASSEMBLED — sorry-free.**  States `CollapseHyps`, `Concl` and `Claim`, the shared
  vocabulary of Theorem 4.8 for `ID_n`.  `collapse` itself, its corollaries and the assembly
  from the twelve proved per-rule case lemmas (`IDn/Collapsing/Case<Rule>.lean`) live in
  `IDn/Collapsing/Theorem.lean` (not here: the twelve case files import this file, so the
  assembly cannot live here too without a cycle).

  The collapsing theorem with impredicative cut elimination for `ID_n^∞`, all levels at once.

  Source: W. Buchholz, *A simplified version of local predicativity*, in: P. Aczel,
  H. Simmons, S. Wainer (eds.), *Proof Theory* (Leeds 1990), CUP 1992,
  p. 26 (Lemma 4.6; `K̄ := {Ω̄_σ : σ ≤ I}`, `Ω̄_σ = Ω_σ + 1` for regular `Ω_σ`, `Ω_σ` otherwise;
  `𝒜(Θ; γ, κ, μ) :⇔ μ ∈ K̄ & γ, κ, μ ∈ H_γ[Θ] & k(Θ) ⊆ ⋂_{τ ≥ κ} C_τ(γ + 1)`; Lemma 4.7
  (𝒜1)–(𝒜4)), p. 27 (**Theorem 4.8** and its cases 1–3), p. 28 (the step (□), cases 4.1–4.3),
  p. 29 (end of 4.3, the Corollary); the design note the design notes; A. Freund,
  arXiv:2204.09321, Theorem 6.7 (the one-level case, `ID1/Collapsing.lean`), Theorem 5.9
  (boundedness), Exercise 6.6, Theorem 7.8 (predicative cut elimination one level up).

  **Theorem 4.8 (Collapsing and impredicative cut elimination), Buchholz p. 27.**

      𝒜(Θ; γ, κ, μ)  &  Γ ⊆ Σ(κ)  &  H_γ[Θ] ⊢^α_μ Γ   ⇒   H_α̂[Θ] ⊢^{ψ_κ α̂}_{ψ_κ α̂} Γ,
                                                           α̂ := γ + ω^{μ+α}.

  **Deviation: here `α̂ := γ + ω^{μ+μ+α}`** (`Basic.hat`).  `HopS` is closed under
  `φ_σ(ρ, β) = ϑ_σ(Ω_{σ+1}·ρ + β)` only when `Ω_{σ+1}·ρ + β ⪯ γ'`, whereas Buchholz's `H_γ` is
  closed under `φ` by definition (Lemma 4.6 b)); the doubled `μ` makes the base `γ'` of the
  step (□) at least `ω^{Ω_{σ+1}·2}`, above every such argument (audit the design notes,
  item 1).  Lemma 4.7 (𝒜4) holds verbatim with `μ + μ` for `μ`.

  Proof by main induction on `μ` and subsidiary induction on `α`.

  **Reading for `ID_n` (`IDn/Calculus.lean`).**
  * `κ = Ω_{k+1}`, `k : Fin n` (Lean `ThetaWNoteD.Omega k`); `Σ(κ)` is `SigmaW k`.
  * `μ ∈ K̄` restricted to the ranks that occur: `μ = muBar m`, `m ≤ n`, i.e. `μ ∈ {0} ∪
    {Ω_j + 1 | 1 ≤ j ≤ n}` (`Ω_0 = 0` is not regular, `Ω̄_0 = 0`).  The main induction is on
    `m : ℕ`.  The embedding (+ Exercise 7.1 (c)) delivers `μ = Ω_n + 1 = muBar n`.
  * `ψ_κ = ϑ_k` of the merged interface (`psi k = (Notn.thetaWLevel k).theta`).
  * `H_γ[Θ] = Hg γ X := adjoin (HopS γ) X`, the level-free Buchholz operator
    (`Ordinal/ThetaW/HullSingle.lean`).  `γ, κ, μ ∈ H_γ[Θ]`: only `γ ∈ HopS γ X` is a hypothesis;
    `κ` and `μ` are in every nice operator.  `k(Θ) ⊆ ⋂_{τ ≥ κ} C_τ(γ+1)` is read as
    `HullHypGe k γ X` (`Ordinal/ThetaW/HullDom.lean`): Freund's `X ⊆ C^ξ(ϑ_τ ξ)` for every
    `ξ ≻ γ` in the domain of `ϑ_τ`, every level `τ ≥ k` (Freund, Theorem 6.7's hypothesis per
    level; the print's `C_τ(γ+1)` needs `γ + 1` in the domain, which `ThetaWNoteD` does not
    guarantee).
  * The rank index `ρ` of `IDnDerivable A ρ H α Γ` is a strict bound (`rk ψ ≺ ρ` for every cut),
    as Buchholz's subscript; `⊢^{ψα̂}_{ψα̂}` is `IDnDerivable A (ψα̂) H' (ψα̂) Γ`.

  **The results of other stages, taken as hypotheses (`CollapseHyps`).**  Transcribed from
  their `ID₁` counterparts per level (never imported):
  * `bound` — Freund Theorem 5.9 / Buchholz Lemma 3.17 at level `k` (`ID1/Boundedness.lean`
    `boundedness`; in flight as `IDn/_draft/Boundedness.lean`);
  * `negStage` — Freund Exercise 6.6 / Buchholz Lemma 3.9 c) at level `k`
    (`ID1/Boundedness.lean` `neg_stage_bound`);
  * `predCut` — Buchholz Theorem 3.16 (predicative cut elimination) with Lemma 4.6 b)
    (`H_γ` closed under `φ`), on an interval `[Ω_σ + 1, ρ₀)`, `σ ≥ 1`, `ρ₀ ≺ Ω_{σ+1}`; only
    the facts the step (□) uses are asserted: some height `β' ∈ H_{γ'}[Θ] ∩ Ω_{σ+1}`
    (Buchholz's `φρ(β+1)`).  Owner: the `IDn/PredCut.lean` stage.
  * `positive`, `levelBounded` — the operator forms (`IDn/Theory.lean`).

  **The corollary** (Buchholz p. 29, Corollary; Freund Corollary 7.2) per level: `collapse_zero`
  (`γ = 0`, `Θ = ∅`) and `collapse_zero_bound` (followed by boundedness at level `k`, the steps
  4–5 of the lower bound, design note §2.7).
-/
import OrdinalAnalysis.IDn.Collapsing.Basic

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

namespace Collapsing

open LO LO.FirstOrder

variable {n : ℕ}

/-- **The results of other stages used by Theorem 4.8, as hypotheses** (see the file header):
the operator forms are positive in their own level and level-bounded; boundedness and
Exercise 6.6 at every level; predicative cut elimination on every interval `(Ω_σ, Ω_{σ+1})`,
`σ ≥ 1` (Lean: `σ = s + 1`, `Ω_σ = Omega s`, `Ω_{σ+1} = Omega (s+1)`). -/
structure CollapseHyps (A : Fin n → Semisentence (LXIn n) 1) : Prop where
  /-- `A_k` is positive in `I_k`. -/
  positive : ∀ k : Fin n, PositiveIn k (A k)
  /-- `A_k` mentions only `I_j`, `j ≤ k`. -/
  levelBounded : ∀ k : Fin n, LevelBounded k (A k)
  /-- **Boundedness at level `k`** (Freund Theorem 5.9, Buchholz Lemma 3.17):
  `H ⊢^α_ρ Γ, ψ`, `α ⪯ b ≺ Ω_{k+1}`, `b ∈ H(∅)` give `H ⊢^α_ρ Γ, ψ^b`. -/
  bound : ∀ (k : Fin n) {ρ : ThetaWNoteD} {H : Set ThetaWNoteD → Set ThetaWNoteD}
    {α : ThetaWNoteD} {ψ : Proposition (LIinfN n)} {Γ : Sequent (LIinfN n)} (b : StageAt k.val),
    ThetaWNoteD.IsOperator H → b.1 ∈ H ∅ → α ≤ b.1 → b.1 < ThetaWNoteD.Omega k.val →
    IDnDerivable A ρ H α (ψ :: Γ) → IDnDerivable A ρ H α (capAt k b ψ :: Γ)
  /-- **Exercise 6.6 at level `k`** (Buchholz Lemma 3.9 c)): `H ⊢^α_ρ Γ, ¬I_k t` and
  `δ ∈ H(∅)` give `H ⊢^α_ρ Γ, ¬I_k^{≺δ} t`. -/
  negStage : ∀ (k : Fin n) {ρ : ThetaWNoteD} {H : Set ThetaWNoteD → Set ThetaWNoteD}
    {α : ThetaWNoteD} {t : SyntacticTerm (LIinfN n)} {Γ : Sequent (LIinfN n)} (δ : StageAt k.val),
    ThetaWNoteD.IsOperator H → δ.1 ∈ H ∅ →
    IDnDerivable A ρ H α (∼(IOmegaAt k t) :: Γ) →
    IDnDerivable A ρ H α (nstageAt (⟨k, δ⟩ : Stage n) t :: Γ)
  /-- **Predicative cut elimination on `(Ω_σ, Ω_{σ+1})`, `σ = s + 1 ≥ 1`** (Buchholz
  Theorem 3.16 with Lemma 4.6 b); Freund Theorem 7.8 one level up): for the operator
  `H_{γ'}[Θ]` of the step (□) — `γ' ∈ H_{γ'}[Θ]`, the hull hypothesis at every level `≥ σ`,
  `ω^{Ω̄_{σ+1}·2} ⪯ γ'` (so `Ω_{σ+1}·ρ₀ + β ⪯ γ'`) — a derivation with cut ranks `≺ ρ₀`, `Ω_σ + 1 ⪯ ρ₀ ≺ Ω_{σ+1}`,
  `ρ₀ ∈ H_{γ'}[Θ]`, of height `β ≺ Ω_{σ+1}`, `β ∈ H_{γ'}[Θ]`, has cut ranks `≺ Ω_σ + 1` at a
  height `β' ∈ H_{γ'}[Θ] ∩ Ω_{σ+1}` (Buchholz's `φρ₀β`). -/
  predCut : ∀ (s : ℕ) {γ' : ThetaWNoteD} {X : Set ThetaWNoteD} {β ρ₀ : ThetaWNoteD}
    {Γ : Sequent (LIinfN n)},
    γ' ∈ ThetaWNoteD.HopS γ' X → ThetaWNoteD.HullHypGe (s + 1) γ' X →
    ThetaWNoteD.omegaPow (muBar (s + 2) + muBar (s + 2)) ≤ γ' →
    β ∈ ThetaWNoteD.HopS γ' X → ρ₀ ∈ ThetaWNoteD.HopS γ' X →
    muBar (s + 1) ≤ ρ₀ → ρ₀ < ThetaWNoteD.Omega (s + 1) → β < ThetaWNoteD.Omega (s + 1) →
    IDnDerivable A ρ₀ (Hg γ' X) β Γ →
    ∃ β' : ThetaWNoteD, β' ∈ ThetaWNoteD.HopS γ' X ∧ β' < ThetaWNoteD.Omega (s + 1) ∧
      IDnDerivable A (muBar (s + 1)) (Hg γ' X) β' Γ

/-- The conclusion of Theorem 4.8 at level `k`: `H_α̂[Θ] ⊢^{ψ_κ α̂}_{ψ_κ α̂} Γ`,
`α̂ = γ + ω^{μ+μ+α}`, `μ = muBar m`. -/
abbrev Concl (A : Fin n → Semisentence (LXIn n) 1) (k : Fin n) (γ : ThetaWNoteD)
    (X : Set ThetaWNoteD) (m : ℕ) (α : ThetaWNoteD) (Γ : Sequent (LIinfN n)) : Prop :=
  IDnDerivable A (psi k.val (hat γ (muBar m) α)) (Hg (hat γ (muBar m) α) X)
    (psi k.val (hat γ (muBar m) α)) Γ

/-- **Theorem 4.8 at `μ = muBar m` and height `α`**, for every `κ = Ω_{k+1}`, `γ`, `Θ`, `Γ`:

    `Γ ⊆ Σ(Ω_{k+1})`, `γ ∈ H_γ[Θ]`, `HullHypGe k γ X`, `H_γ[Θ] ⊢^α_μ Γ`
      ⇒ `H_α̂[Θ] ⊢^{ψ_k α̂}_{ψ_k α̂} Γ`, `α̂ = γ + ω^{μ+μ+α}`.

The main induction hypothesis is `Claim A m' α'` for all `m' < m` and all `α'`; the side
induction hypothesis is `Claim A m α₀` for all `α₀ ≺ α`. -/
def Claim (A : Fin n → Semisentence (LXIn n) 1) (m : ℕ) (α : ThetaWNoteD) : Prop :=
  ∀ (k : Fin n) (γ : ThetaWNoteD) (X : Set ThetaWNoteD) (Γ : Sequent (LIinfN n)),
    (∀ φ ∈ Γ, SigmaW k φ) → γ ∈ ThetaWNoteD.HopS γ X → ThetaWNoteD.HullHypGe k.val γ X →
    IDnDerivable A (muBar m) (Hg γ X) α Γ → Concl A k γ X m α Γ

/-! ### `collapse` itself

Moved to `IDn/Collapsing/Theorem.lean`, together with its corollaries (`collapse_zero`,
`collapse_zero_bound`), the small `Hg`/`hat` facts they use, and the assembly from the twelve
case lemmas (`claim_of_cases`, `collapse_of_cases`): the twelve `Case<Rule>.lean` files import
this file, so the assembly (which needs all twelve) cannot also live here without an import
cycle. `Statement.lean` itself is sorry-free; `CollapseHyps`, `Concl` and `Claim` above are the
shared vocabulary the case lemmas, `CollapseHyps` and `Theorem.lean` all use. -/

end Collapsing

end IDn

end OrdinalAnalysis
