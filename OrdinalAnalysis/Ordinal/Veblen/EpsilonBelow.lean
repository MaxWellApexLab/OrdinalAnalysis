/-
  Every ε-number is a closed bound: the notations below `ε_a` form a
  notation system, `Below (epsilonNote a)`.
-/
import OrdinalAnalysis.Ordinal.Below
import OrdinalAnalysis.Ordinal.Veblen.Instance

set_option autoImplicit false

namespace OrdinalAnalysis.Gamma0Note

open Ordinal

theorem ofNat_lt_epsilon (n : ℕ) (a : Gamma0Note) : ofNat n < epsilonNote a := by
  rw [lt_def, repr_ofNat, repr_epsilonNote_eq_epsilon]
  exact natCast_lt_epsilon n (repr a)

theorem one_lt_epsilon (a : Gamma0Note) : (1 : Gamma0Note) < epsilonNote a := by
  rw [lt_def, repr_one, repr_epsilonNote_eq_epsilon]
  exact_mod_cast natCast_lt_epsilon 1 (repr a)

/-- **`ε_a` is closed.** -/
theorem closed_epsilonNote (a : Gamma0Note) : OrdinalNotation.Closed (epsilonNote a) where
  nadd_lt hx hy := nadd_lt_epsilon hx hy
  omegaPow_lt hx := omegaPow_lt_epsilon hx
  ofNat_lt n := ofNat_lt_epsilon n a
  one_lt := one_lt_epsilon a

/-- The notations below `ε_a`. -/
abbrev EpsilonBelow (a : Gamma0Note) : Type := Below (epsilonNote a)

instance (a : Gamma0Note) : OrdinalNotation (EpsilonBelow a) :=
  Below.ordinalNotation (closed_epsilonNote a)

end OrdinalAnalysis.Gamma0Note
