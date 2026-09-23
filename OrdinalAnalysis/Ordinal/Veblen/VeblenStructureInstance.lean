/-
  `Gamma0Note`, as a `VeblenStructure`.

  `Ordinal/VeblenStructure.lean` isolated exactly what predicative cut elimination consumes
  from a two-argument Veblen function; this file discharges those six fields for the Veblen
  notations, the same way `Ordinal/Veblen/Epsilon.lean` discharged the four fields of
  `EpsilonStructure` for `ε_a = φ_1(a)` alone.

  Every field is a definition or lemma already proved in `Veblen/Gamma0Note.lean` and
  `Veblen/NaturalSum.lean`, transported through `repr_veblenNote` to mathlib's own
  `Ordinal.veblen`; nothing is re-proved. The one new piece of arithmetic is
  `omegaPow_veblenNote`: `ω ^ φ_a(y) = φ_a(y)` for `a ≥ 1`, which is
  `Ordinal.veblen_veblen_of_lt` at `o₁ = 0` (`ω ^ · = φ_0(·)`, `Ordinal.veblen_zero_apply`)
  together with monotonicity of `ω ^ ·`; it is exactly `Gamma0Note.omegaPow_epsilonNote`
  from `Epsilon.lean` with the fixed level `1` generalised to any `a ≥ 1`.

  `nadd_lt_veblen` does not even need its `one ≤ a` hypothesis: `Gamma0Note.nadd_lt_veblenNote`
  holds at *every* level `a`, because every value of `veblen` is additively principal
  regardless of level — the hypothesis is carried only so the field matches the
  `VeblenStructure` signature.
-/
import OrdinalAnalysis.Ordinal.VeblenStructure
import OrdinalAnalysis.Ordinal.Veblen.Instance

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Gamma0Note

/-! ### `ω ^ ·` does not escape `φ_a(y)`, for `a ≥ 1` -/

/-- **`ω ^ φ_a(y) = φ_a(y)` for `a ≥ 1`.** The two-argument generalisation of
`omegaPow_epsilonNote` (the `a = 1` case). -/
theorem omegaPow_veblenNote {a : Gamma0Note} (ha : (1 : Gamma0Note) ≤ a) (y : Gamma0Note) :
    omegaPow (veblenNote a y) = veblenNote a y := by
  have hpos0 : (0 : Gamma0Note) < a := lt_of_lt_of_le zero_lt_one ha
  have hpos : (0 : Ordinal) < repr a := by
    have h := lt_def.mp hpos0
    rwa [repr_zero] at h
  refine repr_injective ?_
  rw [repr_omegaPow, repr_veblenNote]
  have h := Ordinal.veblen_veblen_of_lt (o₁ := 0) (o₂ := repr a) hpos (repr y)
  rwa [Ordinal.veblen_zero_apply] at h

/-! ### The two-argument fixed-point law -/

/-- **`φ_a(φ_b(x)) = φ_b(x)` for `a < b`.** The notation-level form of
`Ordinal.veblen_veblen_of_lt`. -/
theorem veblenNote_veblenNote_of_lt {a b x : Gamma0Note} (h : a < b) :
    veblenNote a (veblenNote b x) = veblenNote b x :=
  repr_injective (by
    simp only [repr_veblenNote]
    exact Ordinal.veblen_veblen_of_lt (lt_def.mp h) (repr x))

/-! ### The instance -/

/-- **`Gamma0Note`, as a `VeblenStructure`.** Every law is inherited from
`Ordinal/Veblen/{Gamma0Note,NaturalSum}.lean` and mathlib's `Ordinal.veblen`. -/
def veblenStructure : VeblenStructure Gamma0Note where
  veblen := veblenNote
  veblen_lt_right := fun h => veblenNote_lt_veblenNote_right h
  veblen_mono_left := fun _ h => veblenNote_le_veblenNote_left h
  le_veblen_right := fun a x => le_veblenNote_right a x
  omegaPow_lt_veblen := by
    intro a x y h hxy
    rw [← omegaPow_veblenNote h y]
    exact omegaPow_lt_omegaPow hxy
  nadd_lt_veblen := fun _ hx hy => nadd_lt_veblenNote hx hy
  veblen_veblen_of_lt := fun h => veblenNote_veblenNote_of_lt h

/-! ### Compatibility with the `EpsilonStructure` instance from `SecondCut.lean` -/

/-- Restricting `Gamma0Note.veblenStructure` to level `one` recovers exactly
`ACAOmega.Gamma0Note.epsilonStructure` (the instance `SecondCut.lean` builds from
`Epsilon.lean`): both have `epsilon a = veblenNote 1 a`, and the remaining fields of
`EpsilonStructure` are propositions, hence definitionally irrelevant once the data field
agrees. So this compatibility bridge is `rfl` — `SecondCut.lean` needs no change. -/
theorem epsilonStructure_eq :
    veblenStructure.toEpsilonStructure = ACAOmega.Gamma0Note.epsilonStructure :=
  rfl

end Gamma0Note

end OrdinalAnalysis
