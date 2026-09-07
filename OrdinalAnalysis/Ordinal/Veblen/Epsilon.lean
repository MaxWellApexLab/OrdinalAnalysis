/-
  The ε-numbers as Veblen notations.

  `ε_a = φ_1(a)`, so on notations `epsilonNote a = veblenNote 1 a` and everything about it
  is inherited from `Gamma0Note.veblenNote`.  What is new here is the *closure* package:
  `ε_a` is a fixed point of `ω ^ ·` and is additively principal, so the two operations the
  infinitary calculus performs on heights — `ω ^ ·` and the natural sum — never leave the
  interval below `ε_a`.

  That is what the second cut-elimination theorem for `ACA` needs (Afshari–Rathjen 2012,
  Thm 4: `⊢^α_ω Γ ⇒ ⊢^{ε_α}_0 Γ`, whose whole content is that `ε_α` absorbs `ω`-towers and
  natural sums of things below it), and it is why `Gamma0Note` rather than `NONote` is the
  height type above `ε₀`: `Γ₀` is closed under `α ↦ ε_α`, so no side condition is ever
  needed.
-/
import OrdinalAnalysis.Ordinal.Veblen.NaturalSum

set_option autoImplicit false

namespace OrdinalAnalysis

open Ordinal

namespace Gamma0Note

/-- The `a`-th ε-number, as a notation: `ε_a = φ_1(a)`.

Note that this is *total* and always in normal form, because `Gamma0Note.veblenNote` is:
when `a` is itself of the form `φ_{a₁}(a₂)` with `1 < a₁` — that is, when `a` is already a
fixed point of `φ_1` — the notation returned is `a` itself. -/
def epsilonNote (a : Gamma0Note) : Gamma0Note :=
  veblenNote 1 a

@[simp]
theorem repr_epsilonNote (a : Gamma0Note) : repr (epsilonNote a) = veblen 1 (repr a) := by
  rw [epsilonNote, repr_veblenNote, repr_one]

/-- The same statement in mathlib's own spelling: `Ordinal.epsilon` is by definition
`veblen 1`. -/
theorem repr_epsilonNote_eq_epsilon (a : Gamma0Note) :
    repr (epsilonNote a) = Ordinal.epsilon (repr a) :=
  repr_epsilonNote a

theorem epsilonNote_zero_repr : repr (epsilonNote 0) = Ordinal.epsilon 0 := by
  rw [repr_epsilonNote_eq_epsilon, repr_zero]

theorem epsilon_lt_epsilon {a b : Gamma0Note} (h : a < b) : epsilonNote a < epsilonNote b :=
  veblenNote_lt_veblenNote_right h

theorem epsilon_le_epsilon {a b : Gamma0Note} (h : a ≤ b) : epsilonNote a ≤ epsilonNote b :=
  veblenNote_le_veblenNote_right h

/-- `a ≤ ε_a`, with equality exactly at the fixed points of `φ_1`. -/
theorem le_epsilon_self (a : Gamma0Note) : a ≤ epsilonNote a :=
  le_veblenNote_right 1 a

theorem epsilon_pos (a : Gamma0Note) : 0 < epsilonNote a :=
  veblenNote_pos 1 a

/-! ### Closure

The two facts the calculus consumes: `ε_a` is a fixed point of `ω ^ ·`, and it is additively
principal.  Both are read off `Ordinal.veblen_veblen_of_lt` and `isPrincipal_add_veblen`. -/

/-- `ω ^ ε_a = ε_a`. -/
theorem omega0_opow_repr_epsilonNote (a : Gamma0Note) :
    ω ^ repr (epsilonNote a) = repr (epsilonNote a) := by
  rw [repr_epsilonNote]
  have h := veblen_veblen_of_lt (o₁ := 0) (o₂ := 1) zero_lt_one (repr a)
  rwa [veblen_zero_apply] at h

/-- `ε_a` is a fixed point of `ω ^ ·` on notations too — and, `omegaPow` being total, on the
nose. -/
@[simp]
theorem omegaPow_epsilonNote (a : Gamma0Note) : omegaPow (epsilonNote a) = epsilonNote a :=
  repr_injective (by rw [repr_omegaPow]; exact omega0_opow_repr_epsilonNote a)

/-- **`ω ^ ·` does not escape `ε_a`.** -/
theorem omegaPow_lt_epsilon {a x : Gamma0Note} (h : x < epsilonNote a) :
    omegaPow x < epsilonNote a := by
  have h' := omegaPow_lt_omegaPow h
  rwa [omegaPow_epsilonNote] at h'

/-- **The natural sum does not escape `ε_a`**: every Veblen value is additively principal,
and `ε_a = φ_1(a)` is one. -/
theorem nadd_lt_epsilon {a x y : Gamma0Note} (hx : x < epsilonNote a)
    (hy : y < epsilonNote a) : nadd x y < epsilonNote a :=
  nadd_lt_veblenNote (a := 1) (b := a) hx hy

end Gamma0Note

end OrdinalAnalysis
