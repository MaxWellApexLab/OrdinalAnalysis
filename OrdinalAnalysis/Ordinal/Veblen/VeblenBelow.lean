/-
  Every level-`a` Veblen value, for `0 < a`, is a closed bound: the notations
  below `φ_a(b)` form a notation system, `Below (veblenNote a b)`.

  This is the two-argument generalisation of `EpsilonBelow.lean` (where the level is
  fixed at `1`).  The natural-sum closure comes straight from
  `Gamma0Note.nadd_lt_veblenNote` (`NaturalSum.lean`), which needs no hypothesis on `a`
  at all — every Veblen value is additively principal regardless of level.  The `ω ^ ·`
  closure needs `1 ≤ a`, read off `Gamma0Note.omegaPow_veblenNote`
  (`VeblenStructureInstance.lean`) exactly as `Epsilon.lean`'s `omegaPow_lt_epsilon` reads
  off `omegaPow_epsilonNote`.  The numerals go through `epsilonNote b = veblenNote 1 b`
  (definitional) and `EpsilonBelow.lean`'s `ofNat_lt_epsilon`/`one_lt_epsilon`, pushed up
  to level `a` by `veblenNote_le_veblenNote_left` at `1 ≤ a`.  That last hypothesis comes
  from `0 < a` via the ordinal fact `0 < o → 1 ≤ o` (`Order.one_le_iff_ne_zero`),
  transported along `repr`.
-/
import OrdinalAnalysis.Ordinal.Below
import OrdinalAnalysis.Ordinal.Veblen.EpsilonBelow
import OrdinalAnalysis.Ordinal.Veblen.VeblenStructureInstance

set_option autoImplicit false

namespace OrdinalAnalysis.Gamma0Note

open Ordinal

/-! ### `0 < a` gives `1 ≤ a` -/

/-- The immediate case of `0 < o → 1 ≤ o` for ordinals, transported along `repr`. -/
theorem one_le_of_pos {a : Gamma0Note} (ha : 0 < a) : (1 : Gamma0Note) ≤ a := by
  rw [le_def, repr_one]
  rw [lt_def, repr_zero] at ha
  exact Order.one_le_iff_ne_zero.mpr ha.ne'

/-! ### The three closure facts -/

/-- **`ω ^ ·` does not escape `φ_a(b)`, for `a ≥ 1`.** The two-argument generalisation of
`omegaPow_lt_epsilon`. -/
theorem omegaPow_lt_veblenNote {a : Gamma0Note} (ha : (1 : Gamma0Note) ≤ a) {x b : Gamma0Note}
    (hx : x < veblenNote a b) : omegaPow x < veblenNote a b := by
  have h' := omegaPow_lt_omegaPow hx
  rwa [omegaPow_veblenNote ha b] at h'

/-- `ofNat n` stays below `φ_a(b)`, for `a ≥ 1`: `ofNat n < ε_b = φ_1(b) ≤ φ_a(b)`. -/
theorem ofNat_lt_veblenNote (n : ℕ) {a b : Gamma0Note} (ha : (1 : Gamma0Note) ≤ a) :
    ofNat n < veblenNote a b :=
  lt_of_lt_of_le (ofNat_lt_epsilon n b) (veblenNote_le_veblenNote_left ha)

/-- `1` stays below `φ_a(b)`, for `a ≥ 1`: `1 < ε_b = φ_1(b) ≤ φ_a(b)`. -/
theorem one_lt_veblenNote {a b : Gamma0Note} (ha : (1 : Gamma0Note) ≤ a) :
    (1 : Gamma0Note) < veblenNote a b :=
  lt_of_lt_of_le (one_lt_epsilon b) (veblenNote_le_veblenNote_left ha)

/-- **`φ_a(b)` is closed, for `0 < a`.** -/
theorem closed_veblenNote (a b : Gamma0Note) (ha : 0 < a) :
    OrdinalNotation.Closed (veblenNote a b) where
  nadd_lt hx hy := nadd_lt_veblenNote hx hy
  omegaPow_lt hx := omegaPow_lt_veblenNote (one_le_of_pos ha) hx
  ofNat_lt n := ofNat_lt_veblenNote n (one_le_of_pos ha)
  one_lt := one_lt_veblenNote (one_le_of_pos ha)

/-- The notations below `φ_a(b)`. -/
abbrev VeblenBelow (a b : Gamma0Note) : Type := Below (veblenNote a b)

namespace VeblenBelow

/-- **The class instance**, for `0 < a`.  Like `Below.ordinalNotation` itself, this is a
`def` and not a bare `instance`: the side hypothesis `ha` is a proof, not a class, and does
not occur in the return type `OrdinalNotation (VeblenBelow a b)`, so typeclass search cannot
manufacture it — call sites bring it into scope with `haveI`/`letI`. -/
def ordinalNotation (a b : Gamma0Note) (ha : 0 < a) : OrdinalNotation (VeblenBelow a b) :=
  Below.ordinalNotation (closed_veblenNote a b ha)

end VeblenBelow

/-- **`VeblenBelow 1 a` is `EpsilonBelow a`.** `veblenNote 1 a` is *definitionally*
`epsilonNote a` (`Epsilon.lean`), so the two notation systems built below them agree on the
nose. -/
theorem epsilonBelow_eq (a : Gamma0Note) : VeblenBelow 1 a = EpsilonBelow a := rfl

end OrdinalAnalysis.Gamma0Note
