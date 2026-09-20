/-
  **`|PA + TI(ε₀)| = ε₁`.**

  Avigad 2002, *An ordinal analysis of admissible set theory using recursion on
  ordinal notations*, Thm 9.8; and before that Schütte, *Proof Theory*, §22.
  The proof-theoretic ordinal of Peano arithmetic augmented by transfinite
  induction up to `ε₀` is `ε₁`, the next epsilon number after `ε₀`.  Here `ε₁`
  is `Gamma0Note.epsilonNote 1`, the notation `φ_1(1)`.

  The theory is `Epsilon1UpperBound.paLX₁ = paLX ∪ tiScheme₀`:

  * `paLX` is `PA` in the language `LX = ℒₒᵣ + {X}`, with the induction schema
    for *every* formula of `LX`, including those mentioning the fresh unary
    predicate `X`;
  * `tiScheme₀` is the schema of transfinite induction along the coded Veblen
    ordering `≺₁`, restricted below the code of `ε₀`, asserted for every unary
    formula `φ` of `LX`:

        Prog(≺₁, φ) → ∀ x ≺₁ ε₀̄, φ(x),

    universally closed over the remaining free variables of `φ`.

  The two halves say the following, and the difference between them is the
  whole content of the calibration.

  * **Upper bound** — for *every* unary formula `φ` and *every* notation `a`
    below `ε₁`, the theory proves transfinite induction for `φ` along `≺₁`
    restricted below `a`.  The quantifier over `a` is in the meta-language:
    there is one proof for each `a`, and no single proof of all of them.
  * **Lower bound** — the theory does *not* prove transfinite induction along
    `≺₁'`, the `ε₁`-segment of `≺₁`, for the free predicate `X`.

  Note precisely what the lower bound is *not*.  It is not the negation of the
  upper bound with `a` set to `ε₁`: the upper bound is about the initial
  segments below every notation `< ε₁`, one at a time, while the lower bound is
  about the whole segment at once, and it is stated for the free predicate `X`
  — the weakest instance of the schema, which makes the non-provability the
  strongest statement available.  Together they place the proof-theoretic
  ordinal exactly at `ε₁`.

  The two halves were built over different theories and are joined here.  The
  upper bound (`Epsilon1UpperBound.lean`) needs the schema — with the single
  `X`-instance it is false, by a counter-model — and the lower bound was
  first proved (`Epsilon1LowerBound.lean`) over `insert TI₀ paLX`, the single
  instance.  `Epsilon1Scheme.lean` lifts the lower bound's cut-away step to the
  schema, by substituting an arbitrary unary formula for `X` in the one
  ω-derivation that exists (`SubstX.lean`) and discharging the free variables
  with the ω-rule.
-/
import OrdinalAnalysis.Gentzen.Epsilon1LowerBoundScheme

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gamma0Note

/-- **`|PA + TI(ε₀)| = ε₁`.**

The left conjunct is the upper bound: for every unary formula `φ` of `LX` and
every Veblen notation `a < ε₁`, `PA[X] + TI(≺₁ ↾ ε₀)` proves transfinite
induction for `φ` along `≺₁` below `a`.

The right conjunct is the lower bound: the same theory does not prove
transfinite induction along `≺₁'`, the `ε₁`-segment of `≺₁`, for the free
predicate `X`. -/
theorem epsilon1_theorem :
    (∀ (φ : Semiformula LX ℕ 1) (a : Gamma0Note), a < epsilonNote 1 →
        Epsilon1UpperBound.paLX₁ ⊢ Epsilon1UpperBound.closedTI₁ φ
          (Epsilon1UpperBound.gamma0Term a))
      ∧ Epsilon1UpperBound.paLX₁ ⊬ (TI Epsilon1Order.epsilon1Order.prec).univCl :=
  ⟨fun φ a ha => Epsilon1UpperBound.epsilon1_upper_bound φ a ha,
    Epsilon1LowerBoundScheme.epsilon1_lower_bound_scheme⟩

/-- The theory is consistent — the same chain, with `⊥` in place of `TI`. -/
theorem paLX₁_consistent : Epsilon1UpperBound.paLX₁ ⊬ (⊥ : Sentence LX) :=
  Epsilon1LowerBoundScheme.paLX₁_scheme_consistent

end OrdinalAnalysis.Gentzen
