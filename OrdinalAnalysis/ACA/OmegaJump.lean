/-
  The omega-jump as a set, and the two theories built from it.

  Afshari-Rathjen (2009) and Marcone-Montalban (2011) study `ACA_0^+ := ACA_0 +
  "every set has an omega-jump"`, whose proof-theoretic ordinal is `phi_2(0)`.
  The omega-jump of a set `Z` is a set `Y` coding the whole hierarchy of finite
  jumps of `Z`: reading `Y` as an omega-indexed sequence of columns via a
  pairing function, column `0` of `Y` is `Z` itself and column `k+1` of `Y` is
  the (Gentzen) jump of column `k`.

  This file states that hierarchy condition as an arithmetical formula in two
  set variables, `IsOmegaJump(Y, Z)`, packages the axiom `omegaJumpAxiom :=
  forall Z, exists Y, IsOmegaJump(Y, Z)` as a closed second-order proposition,
  and forms the two theories

  * `ACAplus0 := ACA_0 + omegaJumpAxiom` (only the set-induction axiom of
    `ACA_0`, plus the omega-jump);
  * `ACAplus  := ACA   + omegaJumpAxiom` (the full second-order induction
    scheme, plus the omega-jump),

  together with the evident monotonicity facts relating them to `ACA_0`/`ACA`.

  The pairing function reused throughout is Foundation's Cantor pairing
  (`LO.FirstOrder.Arithmetic.pair`/`pairDef`, already `Sigma_0`-definable and
  used by the sequence-coding machinery of `HFS`); `columnAt Y k x` reads
  `x` as belonging to column `k` of `Y` through that pairing graph, and
  `jumpColumnAt k` is Gentzen's jump (`Gentzen/Jump.lean`, instantiated at the
  coded Veblen ordering `Gentzen/CodedVeblenJump.lean`'s `precCode1`) applied
  to "membership in column `k`".  Both are built once, at the level of the
  language `LX` (arithmetic plus one fresh unary predicate standing for an
  arbitrary set, `Gentzen/Setup.lean`), and lifted into the second-order
  syntax by `Translate.lean`'s `toSOAtB`, exactly as the rest of `ACA/` treats
  every use of the jump.
-/
import OrdinalAnalysis.ACA.Toolkit
import OrdinalAnalysis.ACA.Translate
import OrdinalAnalysis.Gentzen.CodedVeblenJump
import OrdinalAnalysis.Gentzen.CodedVeblen

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX XRel Xat toLX paLX)
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁)
open OrdinalAnalysis.Gentzen.CodedVeblenJump (addCode₁ omegaPowCode₁ jumpB₁)

/-! ### Pairing, lifted to `LX` -/

/-- The Cantor pairing graph, lifted to `LX`: `z = ⟪x, y⟫`. -/
def pairCode : FirstOrder.Semiformula LX ℕ 3 :=
  Gentzen.CodedNotation.liftCode FirstOrder.Arithmetic.pairDef

/-- Apply the pairing graph, result first: `z = ⟪x, y⟫`. -/
def pairAt {n : ℕ} (z x y : FirstOrder.Semiterm LX ℕ n) : FirstOrder.Semiformula LX ℕ n :=
  FirstOrder.Rew.subst ![z, x, y] ▹ pairCode

/-! ### Columns and their jump, at the level of `LX` -/

/-- `y` belongs to the `k`-th column of the set represented by the fresh
predicate `X`: `exists p, p = ⟪k, y⟫ and X(p)`. -/
def columnXat {n : ℕ} (k y : FirstOrder.Semiterm LX ℕ n) : FirstOrder.Semiformula LX ℕ n :=
  ∃¹ (pairAt (#0 : FirstOrder.Semiterm LX ℕ (n + 1))
      (FirstOrder.Rew.bShift k) (FirstOrder.Rew.bShift y) ⋏
    Xat (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))

/-- `columnXat`, curried at the free variable `&0` standing for the column
index `k`, as the unary formula Gentzen's jump expects. -/
def columnXatFree : FirstOrder.Semiformula LX ℕ 1 :=
  columnXat (&0 : FirstOrder.Semiterm LX ℕ 1) (#0 : FirstOrder.Semiterm LX ℕ 1)

/-- The jump (Gentzen's, over the coded Veblen ordering `precCode₁`) of the
column indexed by the free variable `&0`: a formula in one bound variable,
with the column index still a free variable. -/
def jumpColumnFree : FirstOrder.Semiformula LX ℕ 1 :=
  Gentzen.jump precCode₁ addCode₁ omegaPowCode₁ columnXatFree

/-- The jump of the `k`-th column, with `k` now the *second* bound variable
(`#1`) and the jump's own argument the first (`#0`) — `fixitr` turns the
lone free variable `&0` of `jumpColumnFree` into that second bound slot. -/
def jumpColumnAt2 : FirstOrder.Semiformula LX ℕ 2 :=
  (FirstOrder.Rew.fixitr 1 1 : FirstOrder.Rew LX ℕ 1 ℕ 2) ▹ jumpColumnFree

/-! ### The hierarchy condition, second-order

Both `Y` and `Z` are presented as *bound* set slots, slot `1` for `Y` and
slot `0` for `Z`, so that `IsOmegaJump : Semiproposition ℒₒᵣ 2 0` closes to
`omegaJumpAxiom := ∀²Z ∃²Y IsOmegaJump(Y, Z)` by two plain applications of
`∀²`/`∃²`. -/

/-- The witness recovering the bound set slot `1` (`Y`), inside a two-slot
ambient formula. -/
def yWit2 : Semiformula ℒₒᵣ ℕ Empty 2 1 :=
  (#0 : FirstOrder.Semiterm ℒₒᵣ Empty 1) ∈# (1 : Fin 2)

theorem arith_yWit2 : Arith yWit2 := trivial

/-- `x` belongs to column `0` of `Y`, at `LX`. -/
def hierBaseColLX : FirstOrder.Semiformula LX ℕ 1 :=
  columnXat ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 1) (#0 : FirstOrder.Semiterm LX ℕ 1)

/-- The base condition: column `0` of `Y` is exactly `Z`. -/
def hierBase : Semiproposition ℒₒᵣ 2 0 :=
  ∀¹ ((toSOAtB yWit2 hierBaseColLX : Semiproposition ℒₒᵣ 2 1) 🡘
    ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 2)))

/-- `x` belongs to column `k + 1` of `Y` iff `x` belongs to the jump of
column `k` of `Y`, for `#0 = x` and `#1 = k`, at `LX`. -/
def hierStepColLX : FirstOrder.Semiformula LX ℕ 2 :=
  (columnXat (‘#1 + 1’ : FirstOrder.Semiterm LX ℕ 2) (#0 : FirstOrder.Semiterm LX ℕ 2)) 🡘
    jumpColumnAt2

/-- The step condition: column `k + 1` of `Y` is exactly the jump of column
`k` of `Y`, for every `k`. -/
def hierStep : Semiproposition ℒₒᵣ 2 0 :=
  ∀¹ ∀¹ (toSOAtB yWit2 hierStepColLX : Semiproposition ℒₒᵣ 2 2)

/-- **`IsOmegaJump(Y, Z)`**: `Y` codes the hierarchy of finite Gentzen jumps
of `Z`. -/
def IsOmegaJump : Semiproposition ℒₒᵣ 2 0 := hierBase ⋏ hierStep

/-- **The omega-jump axiom**: every set has an omega-jump. -/
def omegaJumpAxiom : Proposition ℒₒᵣ := ∀² (∃² IsOmegaJump)

/-! ### The two theories -/

/-- **`ACAplus0`**: `ACA_0` (set induction, arithmetical comprehension) plus
the omega-jump axiom. -/
def ACAplus₀ : Set (Proposition ℒₒᵣ) := ACA₀ ∪ {omegaJumpAxiom}

/-- **`ACAplus`**: `ACA` (the full second-order induction scheme) plus the
omega-jump axiom. -/
def ACAplus : Set (Proposition ℒₒᵣ) := ACA ∪ {omegaJumpAxiom}

theorem omegaJumpAxiom_mem_ACAplus₀ : omegaJumpAxiom ∈ ACAplus₀ := Or.inr rfl

theorem omegaJumpAxiom_mem_ACAplus : omegaJumpAxiom ∈ ACAplus := Or.inr rfl

/-- `ACA₀ ⊆ ACAplus₀`. -/
theorem ACA₀_subset_ACAplus₀ : ACA₀ ⊆ ACAplus₀ := Set.subset_union_left

/-- `ACA ⊆ ACAplus`. -/
theorem ACA_subset_ACAplus : ACA ⊆ ACAplus := Set.subset_union_left

/-- `ACAplus₀ ⊆ ACAplus`. -/
theorem ACAplus₀_subset_ACAplus : ACAplus₀ ⊆ ACAplus := by
  intro χ hχ
  rcases hχ with hχ | hχ
  · exact Or.inl (ACA₀_subset_ACA hχ)
  · exact Or.inr hχ

/-- Everything `ACA₀` proves, `ACAplus₀` proves. -/
theorem acaplus₀_provable_mono {φ : Proposition ℒₒᵣ} (h : Provable ACA₀ φ) :
    Provable ACAplus₀ φ :=
  provable_mono ACA₀_subset_ACAplus₀ h

/-- Everything `ACA` proves, `ACAplus` proves. -/
theorem acaplus_provable_mono {φ : Proposition ℒₒᵣ} (h : Provable ACA φ) :
    Provable ACAplus φ :=
  provable_mono ACA_subset_ACAplus h

/-- Everything `ACAplus₀` proves, `ACAplus` proves. -/
theorem acaplus_of_acaplus₀ {φ : Proposition ℒₒᵣ} (h : Provable ACAplus₀ φ) :
    Provable ACAplus φ :=
  provable_mono ACAplus₀_subset_ACAplus h

end OrdinalAnalysis.ACA
