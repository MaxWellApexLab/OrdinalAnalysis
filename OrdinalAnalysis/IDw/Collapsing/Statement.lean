/-
  **STATEMENT FILE — sorry-free.**  States `CollapseHyps`, `Concl`, `Claim` and the fourteen
  per-case obligations `CollapseCases` of Theorem 4.8 for `ID_ω`.  `collapse`, its corollaries
  and the assembly live in `IDw/Collapsing/Theorem.lean`; the case lemmas in
  `IDw/Collapsing/Case<Rule>.lean` (one file per clause of `IDwDerivable`, proved in parallel).
  Transcribed from `IDn/Collapsing/Statement.lean` (see that file's header for the sources and
  the doubled-`μ` deviation `α̂ = γ + ω^{μ+μ+α}`); the changes are listed below.

  Source: W. Buchholz, *A simplified version of local predicativity* (Leeds 1990, CUP 1992),
  p. 26 (Lemma 4.6, `K̄`, `𝒜(Θ; γ, κ, μ)`, Lemma 4.7), p. 27 (Theorem 4.8), p. 28 ((□), cases
  4.1–4.3); A. Freund, arXiv:2204.09321, Theorem 6.7; the design notes

  **Changes from `IDn`.**
  * The main induction index is `m : WithTop ℕ` (well founded), `μ = muBarW m ∈ {0} ∪ {Ω_j + 1 |
    j ≥ 1} ∪ {Ω_ω}`; there is no bound `m ≤ n`. At `m = ⊤`, `μ = Ω_ω` is singular (`Ω̄_ω = Ω_ω`,
    Buchholz p. 26); the embedding delivers ranks `Ω_ω + r`, eliminated to `Ω_ω` (design §4), and
    the corollary is taken at `m = ⊤`.  `ψ_{Ω_ω}` is never used (B92 collapses only at `κ ∈ R`):
    `κ = Ω_{k+1}`, `k : ℕ`, as before.
  * `CollapseHyps`: `levelBounded` is gone (automatic in `ID_ω`: `Q ↦ Jlev j`); `positive` is
    `PositiveP A` (one schema); `bound`, `negStage`, `predCut` are `IDn`'s with `k : ℕ`
    (`IDw/Boundedness.lean`'s `boundedness`/`neg_stage_bound` have exactly the `bound`/`negStage`
    shapes; `predCut` is the `IDw/PredCut` stage's, taken in `IDn`'s shape on finite `σ = s + 1`).
  * **`CollapseCases`**: the fourteen per-case statements (the twelve of `IDn`, `hm` dropped,
    `k : ℕ`, plus `jlev`, `njlev`) as fields, so `Theorem.lean` assembles without importing the
    case files.  The case file `Case<Rule>.lean` proves
    `theorem collapse_case_<rule> (hyp : CollapseHyps A) <field binders> : Concl A k γ X m α Γ`
    with the field's binders verbatim; the main line then fills `<rule> := collapse_case_<rule> hyp`.

  **Reading for `ID_ω` (`IDw/Calculus.lean`).**  As for `IDn`: `κ = Ω_{k+1}` (Lean `Omega k`),
  `Σ(κ)` is `SigmaW k` (`Jlev ℓ` allowed iff `ℓ ≤ k`), `ψ_κ = ϑ_k = psi k`, `H_γ[Θ] = Hg γ X`,
  `k(Θ) ⊆ ⋂_{τ ≥ κ} C_τ(γ+1)` is `HullHypGe k γ X`, the rank index is a strict bound.
-/
import OrdinalAnalysis.IDw.Collapsing.Basic

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

/-- **The results of other stages used by Theorem 4.8, as hypotheses**: the schema is positive
in `P`; boundedness and Exercise 6.6 at every level `k : ℕ`; predicative cut elimination on every
interval `(Ω_σ, Ω_{σ+1})`, `σ = s + 1 ≥ 1` (Lean `Ω_σ = Omega s`, `Ω_{σ+1} = Omega (s+1)`). -/
structure CollapseHyps (A : FormJ) : Prop where
  /-- `A` is positive in `P` (the `Q ↦ Jlev` slot is unrestricted). -/
  positive : PositiveP A
  /-- **Boundedness at level `k`** (Freund Theorem 5.9, Buchholz Lemma 3.17):
  `H ⊢^α_ρ Γ, ψ`, `α ⪯ b ≺ Ω_{k+1}`, `b ∈ H(∅)` give `H ⊢^α_ρ Γ, ψ^b`. -/
  bound : ∀ (k : ℕ) {ρ : ThetaVNoteD} {H : Set ThetaVNoteD → Set ThetaVNoteD}
    {α : ThetaVNoteD} {ψ : Proposition LIinfW} {Γ : Sequent LIinfW} (b : StageAt k),
    ThetaVNoteD.IsOperator H → b.1 ∈ H ∅ → α ≤ b.1 → b.1 < ThetaVNoteD.Omega k →
    IDwDerivable A ρ H α (ψ :: Γ) → IDwDerivable A ρ H α (capAt k b ψ :: Γ)
  /-- **Exercise 6.6 at level `k`** (Buchholz Lemma 3.9 c)): `H ⊢^α_ρ Γ, ¬I_k t` and
  `δ ∈ H(∅)` give `H ⊢^α_ρ Γ, ¬I_k^{≺δ} t`. -/
  negStage : ∀ (k : ℕ) {ρ : ThetaVNoteD} {H : Set ThetaVNoteD → Set ThetaVNoteD}
    {α : ThetaVNoteD} {t : SyntacticTerm LIinfW} {Γ : Sequent LIinfW} (δ : StageAt k),
    ThetaVNoteD.IsOperator H → δ.1 ∈ H ∅ →
    IDwDerivable A ρ H α (∼(IOmegaAt k t) :: Γ) →
    IDwDerivable A ρ H α (nstageAt (⟨k, δ⟩ : Stage) t :: Γ)
  /-- **Predicative cut elimination on `(Ω_σ, Ω_{σ+1})`, `σ = s + 1 ≥ 1`** (Buchholz
  Theorem 3.16 with Lemma 4.6 b); Freund Theorem 7.8 one level up), `IDn`'s shape: for the
  operator `H_{γ'}[Θ]` of the step (□) — `γ' ∈ H_{γ'}[Θ]`, the hull hypothesis at every level
  `≥ σ`, `ω^{Ω̄_{σ+1}·2} ⪯ γ'` — a derivation with cut ranks `≺ ρ₀`, `Ω_σ + 1 ⪯ ρ₀ ≺ Ω_{σ+1}`,
  `ρ₀ ∈ H_{γ'}[Θ]`, of height `β ≺ Ω_{σ+1}`, `β ∈ H_{γ'}[Θ]`, has cut ranks `≺ Ω_σ + 1` at a
  height `β' ∈ H_{γ'}[Θ] ∩ Ω_{σ+1}`. -/
  predCut : ∀ (s : ℕ) {γ' : ThetaVNoteD} {X : Set ThetaVNoteD} {β ρ₀ : ThetaVNoteD}
    {Γ : Sequent LIinfW},
    γ' ∈ ThetaVNoteD.HopS γ' X → ThetaVNoteD.HullHypGe (s + 1) γ' X →
    ThetaVNoteD.omegaPow (muBar (s + 2) + muBar (s + 2)) ≤ γ' →
    β ∈ ThetaVNoteD.HopS γ' X → ρ₀ ∈ ThetaVNoteD.HopS γ' X →
    muBar (s + 1) ≤ ρ₀ → ρ₀ < ThetaVNoteD.Omega (s + 1) → β < ThetaVNoteD.Omega (s + 1) →
    IDwDerivable A ρ₀ (Hg γ' X) β Γ →
    ∃ β' : ThetaVNoteD, β' ∈ ThetaVNoteD.HopS γ' X ∧ β' < ThetaVNoteD.Omega (s + 1) ∧
      IDwDerivable A (muBar (s + 1)) (Hg γ' X) β' Γ

/-- The conclusion of Theorem 4.8 at level `k`: `H_α̂[Θ] ⊢^{ψ_κ α̂}_{ψ_κ α̂} Γ`,
`α̂ = γ + ω^{μ+μ+α}`, `μ = muBarW m`. -/
abbrev Concl (A : FormJ) (k : ℕ) (γ : ThetaVNoteD) (X : Set ThetaVNoteD) (m : WithTop ℕ)
    (α : ThetaVNoteD) (Γ : Sequent LIinfW) : Prop :=
  IDwDerivable A (psi k (hat γ (muBarW m) α)) (Hg (hat γ (muBarW m) α) X)
    (psi k (hat γ (muBarW m) α)) Γ

/-- **Theorem 4.8 at `μ = muBarW m` and height `α`**, for every `κ = Ω_{k+1}`, `γ`, `Θ`, `Γ`:

    `Γ ⊆ Σ(Ω_{k+1})`, `γ ∈ H_γ[Θ]`, `HullHypGe k γ X`, `H_γ[Θ] ⊢^α_μ Γ`
      ⇒ `H_α̂[Θ] ⊢^{ψ_k α̂}_{ψ_k α̂} Γ`, `α̂ = γ + ω^{μ+μ+α}`.

The main induction hypothesis is `Claim A m' α'` for all `m' < m` (in `WithTop ℕ`) and all `α'`;
the side induction hypothesis is `Claim A m α₀` for all `α₀ ≺ α`. -/
def Claim (A : FormJ) (m : WithTop ℕ) (α : ThetaVNoteD) : Prop :=
  ∀ (k : ℕ) (γ : ThetaVNoteD) (X : Set ThetaVNoteD) (Γ : Sequent LIinfW),
    (∀ φ ∈ Γ, SigmaW k φ) → γ ∈ ThetaVNoteD.HopS γ X → ThetaVNoteD.HullHypGe k γ X →
    IDwDerivable A (muBarW m) (Hg γ X) α Γ → Concl A k γ X m α Γ

/-! ### Smoke tests: the limit instance and the finite instances -/

/-- At `m = ⊤` the claim is Theorem 4.8 at `μ = Ω_ω`, definitionally. -/
example (A : FormJ) (α : ThetaVNoteD) :
    Claim A ⊤ α ↔ ∀ (k : ℕ) (γ : ThetaVNoteD) (X : Set ThetaVNoteD) (Γ : Sequent LIinfW),
      (∀ φ ∈ Γ, SigmaW k φ) → γ ∈ ThetaVNoteD.HopS γ X → ThetaVNoteD.HullHypGe k γ X →
      IDwDerivable A ThetaVNoteD.OmegaW (Hg γ X) α Γ →
      IDwDerivable A (psi k (hat γ ThetaVNoteD.OmegaW α))
        (Hg (hat γ ThetaVNoteD.OmegaW α) X) (psi k (hat γ ThetaVNoteD.OmegaW α)) Γ :=
  Iff.rfl

/-- At `m = ↑m₀` the claim is `IDn`'s `Claim` at `muBar m₀`, definitionally. -/
example (A : FormJ) (m₀ : ℕ) (α : ThetaVNoteD) :
    Claim A (m₀ : WithTop ℕ) α ↔
      ∀ (k : ℕ) (γ : ThetaVNoteD) (X : Set ThetaVNoteD) (Γ : Sequent LIinfW),
      (∀ φ ∈ Γ, SigmaW k φ) → γ ∈ ThetaVNoteD.HopS γ X → ThetaVNoteD.HullHypGe k γ X →
      IDwDerivable A (muBar m₀) (Hg γ X) α Γ →
      IDwDerivable A (psi k (hat γ (muBar m₀) α)) (Hg (hat γ (muBar m₀) α) X)
        (psi k (hat γ (muBar m₀) α)) Γ :=
  Iff.rfl

/-- Every `m' < ⊤` is finite: the main induction hypothesis at `⊤` is the family of finite
claims. -/
example (A : FormJ) :
    (∀ m' < (⊤ : WithTop ℕ), ∀ α' : ThetaVNoteD, Claim A m' α') ↔
      ∀ m₀ : ℕ, ∀ α' : ThetaVNoteD, Claim A (m₀ : WithTop ℕ) α' :=
  ⟨fun h m₀ => h m₀ (WithTop.coe_lt_top m₀), fun h m' hm' => by
    lift m' to ℕ using hm'.ne
    exact h m'⟩

/-! ### The per-case obligations

One field per clause of `IDwDerivable`, in constructor order. Each field is the statement of
`Case<Rule>.lean`'s `collapse_case_<rule>` after its first argument `hyp : CollapseHyps A`.
The common prefix (`m`, `α`, `mih`, `sih`, `k`, `γ`, `X`, `Γ`, `hΓ`, `hγ`, `hX`) is `IDn`'s with
`m : WithTop ℕ`, `hm` dropped, `k : ℕ`; the clause-specific binders are the constructor's
premises with `muBar m` read as `muBarW m`. -/
structure CollapseCases (A : FormJ) : Prop where
  /-- (V) for a true literal (`CaseLiteral.lean`). -/
  literal : ∀ {m : WithTop ℕ} {α : ThetaVNoteD}
    (_mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (_sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (_hΓ : ∀ φ ∈ Γ, SigmaW k φ) (_hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (_hX : ThetaVNoteD.HullHypGe k γ X)
    {φ : Proposition LIinfW}
    (_hα : α ∈ Hg γ X ∅) (_hΓH : paramsVal Γ ⊆ Hg γ X ∅) (_hφ : TrueLit φ) (_hmem : φ ∈ Γ),
    Concl A k γ X m α Γ
  /-- (V) for `⊤` (`CaseVerum.lean`). -/
  verum : ∀ {m : WithTop ℕ} {α : ThetaVNoteD}
    (_mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (_sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (_hΓ : ∀ φ ∈ Γ, SigmaW k φ) (_hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (_hX : ThetaVNoteD.HullHypGe k γ X)
    (_hα : α ∈ Hg γ X ∅) (_hΓH : paramsVal Γ ⊆ Hg γ X ∅) (_hmem : ⊤ ∈ Γ),
    Concl A k γ X m α Γ
  /-- The identity axiom of `X` (`CaseIdX.lean`). -/
  idX : ∀ {m : WithTop ℕ} {α : ThetaVNoteD}
    (_mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (_sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (_hΓ : ∀ φ ∈ Γ, SigmaW k φ) (_hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (_hX : ThetaVNoteD.HullHypGe k γ X)
    (t : SyntacticTerm LIinfW)
    (_hα : α ∈ Hg γ X ∅) (_hΓH : paramsVal Γ ⊆ Hg γ X ∅) (_h1 : XinfAt t ∈ Γ)
    (_h2 : ∼(XinfAt t) ∈ Γ),
    Concl A k γ X m α Γ
  /-- (V) for `∧` (`CaseAnd.lean`). -/
  and : ∀ {m : WithTop ℕ} {α : ThetaVNoteD}
    (_mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (_sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (_hΓ : ∀ φ ∈ Γ, SigmaW k φ) (_hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (_hX : ThetaVNoteD.HullHypGe k γ X)
    {φ ψ : Proposition LIinfW} {α₀ α₁ : ThetaVNoteD}
    (_hα : α ∈ Hg γ X ∅) (_hΓH : paramsVal Γ ⊆ Hg γ X ∅) (_hmem : φ ⋏ ψ ∈ Γ)
    (_h0 : α₀ < α) (_h1 : α₁ < α)
    (_d0 : IDwDerivable A (muBarW m) (Hg γ X) α₀ (φ :: Γ))
    (_d1 : IDwDerivable A (muBarW m) (Hg γ X) α₁ (ψ :: Γ)),
    Concl A k γ X m α Γ
  /-- (W) for `∨`, left disjunct (`CaseOrL.lean`). -/
  orL : ∀ {m : WithTop ℕ} {α : ThetaVNoteD}
    (_mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (_sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (_hΓ : ∀ φ ∈ Γ, SigmaW k φ) (_hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (_hX : ThetaVNoteD.HullHypGe k γ X)
    {φ ψ : Proposition LIinfW} {α₀ : ThetaVNoteD}
    (_hα : α ∈ Hg γ X ∅) (_hΓH : paramsVal Γ ⊆ Hg γ X ∅) (_hmem : φ ⋎ ψ ∈ Γ)
    (_h0 : α₀ < α) (_d0 : IDwDerivable A (muBarW m) (Hg γ X) α₀ (φ :: Γ)),
    Concl A k γ X m α Γ
  /-- (W) for `∨`, right disjunct (`CaseOrR.lean`). -/
  orR : ∀ {m : WithTop ℕ} {α : ThetaVNoteD}
    (_mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (_sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (_hΓ : ∀ φ ∈ Γ, SigmaW k φ) (_hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (_hX : ThetaVNoteD.HullHypGe k γ X)
    {φ ψ : Proposition LIinfW} {α₀ : ThetaVNoteD}
    (_hα : α ∈ Hg γ X ∅) (_hΓH : paramsVal Γ ⊆ Hg γ X ∅) (_hmem : φ ⋎ ψ ∈ Γ)
    (_h1 : ThetaVNoteD.one < α) (_h0 : α₀ < α)
    (_d0 : IDwDerivable A (muBarW m) (Hg γ X) α₀ (ψ :: Γ)),
    Concl A k γ X m α Γ
  /-- (V) for `∀`, the ω-rule (`CaseAll.lean`). -/
  all : ∀ {m : WithTop ℕ} {α : ThetaVNoteD}
    (_mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (_sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (_hΓ : ∀ φ ∈ Γ, SigmaW k φ) (_hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (_hX : ThetaVNoteD.HullHypGe k γ X)
    {φ : Semiproposition LIinfW 1} (f : ℕ → ThetaVNoteD)
    (_hα : α ∈ Hg γ X ∅) (_hΓH : paramsVal Γ ⊆ Hg γ X ∅) (_hmem : (∀¹ φ) ∈ Γ)
    (_hf : ∀ i, f i < α)
    (_d0 : ∀ i, IDwDerivable A (muBarW m) (Hg γ X) (f i) (φ/[numI i] :: Γ)),
    Concl A k γ X m α Γ
  /-- (W) for `∃` (`CaseExs.lean`). -/
  exs : ∀ {m : WithTop ℕ} {α : ThetaVNoteD}
    (_mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (_sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (_hΓ : ∀ φ ∈ Γ, SigmaW k φ) (_hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (_hX : ThetaVNoteD.HullHypGe k γ X)
    {φ : Semiproposition LIinfW 1} (i : ℕ) {α₀ : ThetaVNoteD}
    (_hα : α ∈ Hg γ X ∅) (_hΓH : paramsVal Γ ⊆ Hg γ X ∅) (_hmem : (∃¹ φ) ∈ Γ)
    (_hi : ThetaVNoteD.ofNat i < α) (_h0 : α₀ < α)
    (_d0 : IDwDerivable A (muBarW m) (Hg γ X) α₀ (φ/[numI i] :: Γ)),
    Concl A k γ X m α Γ
  /-- (W) for `I_j^{≺a} t` (`CaseStage.lean`). -/
  stage : ∀ {m : WithTop ℕ} {α : ThetaVNoteD}
    (_mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (_sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (_hΓ : ∀ φ ∈ Γ, SigmaW k φ) (_hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (_hX : ThetaVNoteD.HullHypGe k γ X)
    {j : ℕ} {a : StageAt j} {t : SyntacticTerm LIinfW} (g : StageAt j)
    {α₀ : ThetaVNoteD}
    (_hα : α ∈ Hg γ X ∅) (_hΓH : paramsVal Γ ⊆ Hg γ X ∅)
    (_hmem : stageAt (⟨j, a⟩ : Stage) t ∈ Γ) (_hga : g.1 < a.1) (_hgα : g.1 < α)
    (_hgH : g.1 ∈ Hg γ X ∅) (_h0 : α₀ < α)
    (_d0 : IDwDerivable A (muBarW m) (Hg γ X) α₀ (unfoldW A j g t :: Γ)),
    Concl A k γ X m α Γ
  /-- (V) for `¬I_j^{≺a} t` (`CaseNstage.lean`). -/
  nstage : ∀ {m : WithTop ℕ} {α : ThetaVNoteD}
    (_mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (_sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (_hΓ : ∀ φ ∈ Γ, SigmaW k φ) (_hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (_hX : ThetaVNoteD.HullHypGe k γ X)
    {j : ℕ} {a : StageAt j} {t : SyntacticTerm LIinfW}
    (f : StageAt j → ThetaVNoteD)
    (_hα : α ∈ Hg γ X ∅) (_hΓH : paramsVal Γ ⊆ Hg γ X ∅)
    (_hmem : nstageAt (⟨j, a⟩ : Stage) t ∈ Γ)
    (_hf : ∀ g : StageAt j, g.1 < a.1 → f g < α)
    (_d0 : ∀ g : StageAt j, g.1 < a.1 →
      IDwDerivable A (muBarW m) (ThetaVNoteD.adjoin (Hg γ X) {g.1}) (f g)
        (∼(unfoldW A j g t) :: Γ)),
    Concl A k γ X m α Γ
  /-- (Fix) at level `j` (`CaseFix.lean`). -/
  fix : ∀ {m : WithTop ℕ} {α : ThetaVNoteD}
    (_mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (_sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (_hΓ : ∀ φ ∈ Γ, SigmaW k φ) (_hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (_hX : ThetaVNoteD.HullHypGe k γ X)
    {j : ℕ} {t : SyntacticTerm LIinfW} {α₀ : ThetaVNoteD}
    (_hα : α ∈ Hg γ X ∅) (_hΓH : paramsVal Γ ⊆ Hg γ X ∅) (_hmem : IOmegaAt j t ∈ Γ)
    (_hΩ : ThetaVNoteD.Omega j ≤ α) (_h0 : α₀ < α)
    (_d0 : IDwDerivable A (muBarW m) (Hg γ X) α₀
      (unfoldW A j (StageAt.top j) t :: Γ)),
    Concl A k γ X m α Γ
  /-- **(jlev)**, new (`CaseJlev.lean`): (W) for `Jlev ℓ (s,t)`, the one disjunct `I_{val s} t`. -/
  jlev : ∀ {m : WithTop ℕ} {α : ThetaVNoteD}
    (_mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (_sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (_hΓ : ∀ φ ∈ Γ, SigmaW k φ) (_hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (_hX : ThetaVNoteD.HullHypGe k γ X)
    {ℓ : WithTop ℕ} {s t : SyntacticTerm LIinfW} {α₀ : ThetaVNoteD}
    (_hα : α ∈ Hg γ X ∅) (_hΓH : paramsVal Γ ⊆ Hg γ X ∅) (_hmem : jlevAt ℓ s t ∈ Γ)
    (_hs : s.freeVariables = ∅) (_ht : t.freeVariables = ∅)
    (_hl : ((termVal s : ℕ) : WithTop ℕ) < ℓ) (_h0 : α₀ < α)
    (_d0 : IDwDerivable A (muBarW m) (Hg γ X) α₀ (IOmegaAt (termVal s) t :: Γ)),
    Concl A k γ X m α Γ
  /-- **(njlev)**, new (`CaseNJlev.lean`): (V) for `¬Jlev ℓ (s,t)`, at most one conjunct
  `¬I_{val s} t`. -/
  njlev : ∀ {m : WithTop ℕ} {α : ThetaVNoteD}
    (_mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (_sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (_hΓ : ∀ φ ∈ Γ, SigmaW k φ) (_hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (_hX : ThetaVNoteD.HullHypGe k γ X)
    {ℓ : WithTop ℕ} {s t : SyntacticTerm LIinfW} {α₀ : ThetaVNoteD}
    (_hα : α ∈ Hg γ X ∅) (_hΓH : paramsVal Γ ⊆ Hg γ X ∅) (_hmem : njlevAt ℓ s t ∈ Γ)
    (_hs : s.freeVariables = ∅) (_ht : t.freeVariables = ∅)
    (_h0 : ((termVal s : ℕ) : WithTop ℕ) < ℓ → α₀ < α)
    (_d0 : ((termVal s : ℕ) : WithTop ℕ) < ℓ →
      IDwDerivable A (muBarW m) (Hg γ X) α₀ (∼(IOmegaAt (termVal s) t) :: Γ)),
    Concl A k γ X m α Γ
  /-- (Cut) of rank `≺ μ` (`CaseCut.lean`; the limit `m = ⊤` is handled there). -/
  cut : ∀ {m : WithTop ℕ} {α : ThetaVNoteD}
    (_mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (_sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (_hΓ : ∀ φ ∈ Γ, SigmaW k φ) (_hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (_hX : ThetaVNoteD.HullHypGe k γ X)
    {ψ : Proposition LIinfW} {α₀ : ThetaVNoteD}
    (_hα : α ∈ Hg γ X ∅) (_hΓH : paramsVal Γ ⊆ Hg γ X ∅) (_hr : rk ψ < muBarW m)
    (_h0 : α₀ < α) (_d0 : IDwDerivable A (muBarW m) (Hg γ X) α₀ (ψ :: Γ))
    (_d1 : IDwDerivable A (muBarW m) (Hg γ X) α₀ (∼ψ :: Γ)),
    Concl A k γ X m α Γ

end Collapsing

end IDw

end OrdinalAnalysis
