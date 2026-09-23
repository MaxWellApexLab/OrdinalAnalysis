/-
  The Veblen hierarchy on a notation system, abstractly.

  `ACAOmega/SecondCut.lean` isolated the three facts the second cut-elimination theorem
  uses about `α ↦ ε_α` as `EpsilonStructure`.  Predicative cut elimination
  (`⊢^α_{ρ ⊕ ω^ξ} Γ ⇒ ⊢^{φ_ξ(α)}_ρ Γ`, Pohlers) needs the same package one level up: not a
  single strictly monotone closure operator `ε`, but a *two-argument* Veblen function
  `φ : O → O → O`, strictly increasing in its second argument, merely monotone (not strict)
  in its first — `ξ = 0` gives the ε-numbers, `ξ = 1` the ζ-numbers, and so on, and every
  level `φ_ξ(·)` for `ξ ≥ 1` is, exactly as an ε-number was, closed under `ω ^ ·` and the
  natural sum.  `veblen_veblen_of_lt` is the two-argument analogue of "`ε` absorbs itself":
  raising the level past an existing one leaves the value fixed.

  This file states that package as `VeblenStructure`, derives the same closure lemmas
  (`omegaTower_lt_veblen`, `redOrd_lt_veblen`, `succ_lt_veblen`) that `EpsilonStructure`
  proved for the height bookkeeping of cut elimination, and supplies the compatibility
  bridge `VeblenStructure.toEpsilonStructure`: restricting a Veblen structure to level
  `one` recovers exactly the three facts `EpsilonStructure` packages, so `SecondCut.lean`
  keeps compiling unchanged once `Gamma0Note` also carries a `VeblenStructure`
  (`Ordinal/Veblen/VeblenStructureInstance.lean`).

  As with `EpsilonStructure`, the laws deliberately omit `a < veblen a x` unconditionally at
  fixed `a`; what holds is only the weaker `le_veblen_right` (`x ≤ veblen a x`), because on
  `Gamma0Note` the ε-numbers, ζ-numbers, etc. are honest elements of the notation type, not
  merely a bound the calculus stays under (the pitfall notes: `a < ω ^ a` is false at fixed
  points, and `φ` is not strictly monotone in its first argument).
-/
import OrdinalAnalysis.Ordinal.Notation
import OrdinalAnalysis.ACAOmega.SecondCut

set_option autoImplicit false

namespace OrdinalAnalysis

/-! ### Veblen structures, abstractly -/

/-- A Veblen operation on a notation system: strictly increasing in its second argument,
monotone (not strictly) in its first, inflationary in its second, and with every value
`φ_a(y)` at level `a ≥ 1` closed under `ω ^ ·` and the natural sum, exactly as an ε-number is
closed at level `1`. `veblen_veblen_of_lt` is the two-argument fixed-point law: raising the
level past an existing one changes nothing.

These are the only properties predicative cut elimination
(`⊢^α_{ρ ⊕ ω^ξ} Γ ⇒ ⊢^{φ_ξ(α)}_ρ Γ`) uses of `α ↦ φ_ξ(α)`. -/
structure VeblenStructure (O : Type) [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O] where
  /-- `φ_a(x)`. -/
  veblen : O → O → O
  /-- Strictly increasing in the second argument. -/
  veblen_lt_right : ∀ {a x y : O}, x < y → veblen a x < veblen a y
  /-- Monotone — **not** strictly — in the first argument: at a fixed point `x` of `φ_a`,
  `φ_a x = φ_b x` for every `b ≥ a`. -/
  veblen_mono_left : ∀ {a b : O} (x : O), a ≤ b → veblen a x ≤ veblen b x
  /-- Inflationary in the second argument. -/
  le_veblen_right : ∀ (a x : O), x ≤ veblen a x
  /-- Every `φ_a(y)` at level `a ≥ 1` is closed under `ω ^ ·`. -/
  omegaPow_lt_veblen : ∀ {a x y : O}, OrdinalNotation.one ≤ a → x < veblen a y →
    OrdinalNotation.omegaPow x < veblen a y
  /-- Every `φ_a(y)` at level `a ≥ 1` is closed under the natural sum. -/
  nadd_lt_veblen : ∀ {a x y z : O}, OrdinalNotation.one ≤ a → x < veblen a z → y < veblen a z →
    OrdinalNotation.nadd x y < veblen a z
  /-- Raising the level past an existing one is the identity: `φ_a(φ_b(x)) = φ_b(x)` for
  `a < b`. -/
  veblen_veblen_of_lt : ∀ {a b x : O}, a < b → veblen a (veblen b x) = veblen b x

namespace VeblenStructure

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- The `ω`-tower does not escape `φ_a(y)`, for `a ≥ 1`. -/
theorem omegaTower_lt_veblen (V : VeblenStructure O) {a : O} (h : OrdinalNotation.one ≤ a) :
    ∀ (k : ℕ) (x y : O), x < V.veblen a y → OrdinalNotation.omegaTower k x < V.veblen a y
  | 0, _, _, hx => hx
  | (k + 1), x, y, hx => by
    rw [OrdinalNotation.omegaTower_succ]
    exact V.omegaTower_lt_veblen h k (OrdinalNotation.omegaPow x) y (V.omegaPow_lt_veblen h hx)

/-- The reduction lemma's doubled bound does not escape `φ_a(z)`, for `a ≥ 1`. -/
theorem redOrd_lt_veblen (V : VeblenStructure O) {a x y z : O} (h : OrdinalNotation.one ≤ a)
    (hx : x < V.veblen a z) (hy : y < V.veblen a z) :
    OrdinalNotation.redOrd x y < V.veblen a z := by
  have h₁ : OrdinalNotation.nadd x y < V.veblen a z := V.nadd_lt_veblen h hx hy
  exact V.nadd_lt_veblen h h₁ h₁

/-- Successor does not escape `φ_a(y)`, given that `1` itself does not — which, unlike
`omegaPow_lt_veblen`/`nadd_lt_veblen`, is not automatic from `a ≥ 1` alone (nothing forces
`φ_a(y) > 1` in general, e.g. it could equal `1` for some notation systems at `a = y = 0`),
so it is taken as a side hypothesis, discharged at each use site. -/
theorem succ_lt_veblen (V : VeblenStructure O) {a x y : O} (h : OrdinalNotation.one ≤ a)
    (hone : OrdinalNotation.one < V.veblen a y) (hx : x < V.veblen a y) :
    OrdinalNotation.succ x < V.veblen a y :=
  V.nadd_lt_veblen h hx hone

end VeblenStructure

/-! ### The compatibility bridge: a `VeblenStructure` restricts to an `EpsilonStructure` -/

/-- Every Veblen structure restricts to an `EpsilonStructure` at level `one`, `ε_a := φ_1(a)`.

No side hypothesis is needed to build this, unlike `omegaTower_lt_veblen`/`redOrd_lt_veblen`
above: the side condition `one ≤ a` of `omegaPow_lt_veblen`/`nadd_lt_veblen` is discharged by
`le_rfl` at the fixed level `a = one`. This is the compatibility bridge that lets
`ACAOmega/SecondCut.lean` keep compiling against `EpsilonStructure` once `Gamma0Note` also
carries a `VeblenStructure` (`Ordinal/Veblen/VeblenStructureInstance.lean`). -/
def VeblenStructure.toEpsilonStructure {O : Type} [LinearOrder O] [WellFoundedLT O]
    [OrdinalNotation O] (V : VeblenStructure O) : ACAOmega.EpsilonStructure O where
  epsilon := V.veblen OrdinalNotation.one
  epsilon_lt_epsilon := fun h => V.veblen_lt_right h
  omegaPow_lt_epsilon := fun h => V.omegaPow_lt_veblen le_rfl h
  nadd_lt_epsilon := fun hx hy => V.nadd_lt_veblen le_rfl hx hy

end OrdinalAnalysis
