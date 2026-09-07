/-
  `Gamma0Note` as an `OrdinalNotation`.

  `OrdinalAnalysis/Ordinal/Notation.lean` isolated exactly what the infinitary calculus of
  `Omega/` consumes from its type of heights; this file discharges those eleven fields for
  the Veblen notations, so that the calculus — and with it the reduction lemma, the
  elimination lemma and cut elimination — can be run at heights up to `Γ₀` instead of
  stopping at `ε₀`.

  Every field is a definition or lemma proved in `Veblen/NaturalSum.lean` and
  `Veblen/Gamma0Note.lean`; nothing is re-proved.  Note which field is *absent* from the
  class: `a < ω ^ a`.  It is false on `Gamma0Note` — the ε-numbers are fixed points of
  `ω ^ ·` and, unlike `ONote`'s notations, they live inside the type — and the class was
  designed without it for exactly that reason.

  The file closes with `omegaTower_lt_epsilon`, the form in which the closure package of
  `Veblen/Epsilon.lean` is used: the `ω`-tower operator of the class does not escape an
  ε-number.
-/
import OrdinalAnalysis.Ordinal.Notation
import OrdinalAnalysis.Ordinal.Veblen.Epsilon
import OrdinalAnalysis.Ordinal.Veblen.NaturalSumAssoc

set_option autoImplicit false

namespace OrdinalAnalysis

open Ordinal

/-! ### The finite notations

`φ_0(0) = ω ^ 0 = 1`, so `vadd 0 0 n 0` denotes `n`. -/

namespace VNote

/-- The notation for a natural number: `0` for `0`, and the single term `φ_0(0) · (n+1)`
otherwise. -/
def ofNat : ℕ → VNote
  | 0 => 0
  | (n + 1) => VNote.vadd 0 0 ⟨n + 1, Nat.succ_pos n⟩ 0

instance nf_ofNat (n : ℕ) : NF (ofNat n) := by
  cases n with
  | zero => exact NF.zero
  | succ k => exact NF.vadd_zero _ NF.zero NF.zero (by rw [repr_zero]; exact veblen_pos)

@[simp]
theorem repr_ofNat : ∀ n : ℕ, repr (ofNat n) = (n : Ordinal)
  | 0 => by rw [ofNat, repr_zero, Nat.cast_zero]
  | (n + 1) => by
    show veblen (repr (0 : VNote)) (repr (0 : VNote)) * (((n + 1 : ℕ) : ℕ) : Ordinal)
        + repr (0 : VNote) = ((n + 1 : ℕ) : Ordinal)
    rw [repr_zero, veblen_zero_apply, opow_zero, one_mul, add_zero]

end VNote

namespace Gamma0Note

/-- The notation for a natural number. -/
def ofNat (n : ℕ) : Gamma0Note :=
  ⟨VNote.ofNat n, VNote.nf_ofNat n⟩

@[simp] theorem repr_ofNat (n : ℕ) : repr (ofNat n) = (n : Ordinal) :=
  VNote.repr_ofNat n

theorem ofNat_lt_ofNat {m n : ℕ} (h : m < n) : ofNat m < ofNat n := by
  rw [lt_def, repr_ofNat, repr_ofNat]
  exact_mod_cast h

theorem zero_lt_one : (0 : Gamma0Note) < 1 := by
  rw [lt_def, repr_zero, repr_one]
  exact_mod_cast Nat.zero_lt_one

/-- Adding `1` strictly increases; this is the class's `lt_nadd_one`. -/
theorem lt_nadd_one (a : Gamma0Note) : a < nadd a 1 := by
  have h := nadd_lt_nadd_right a zero_lt_one
  rwa [nadd_zero] at h

end Gamma0Note

/-! ### The instance -/

instance : OrdinalNotation Gamma0Note where
  nadd := Gamma0Note.nadd
  nadd_comm := Gamma0Note.nadd_comm
  nadd_assoc := Gamma0Note.nadd_assoc
  le_nadd_left := Gamma0Note.le_nadd_left
  nadd_lt_nadd_left := fun b h => Gamma0Note.nadd_lt_nadd_left b h
  omegaPow := Gamma0Note.omegaPow
  omegaPow_lt_omegaPow := Gamma0Note.omegaPow_lt_omegaPow
  nadd_lt_omegaPow := Gamma0Note.nadd_lt_omegaPow
  one := 1
  lt_nadd_one := Gamma0Note.lt_nadd_one
  one_le_omegaPow := Gamma0Note.one_le_omegaPow
  ofNat := Gamma0Note.ofNat
  ofNat_lt_ofNat := Gamma0Note.ofNat_lt_ofNat

namespace OrdinalNotation

/-! ### The bridge to the `Gamma0Note` spellings

As for `NONote`: every generic operation is *definitionally* the `Gamma0Note` one, but `rw`
and `simp` compare at reducible transparency and will not cross on their own. -/

@[simp] theorem Gamma0Note_nadd (a b : Gamma0Note) :
    OrdinalNotation.nadd a b = Gamma0Note.nadd a b := rfl

@[simp] theorem Gamma0Note_omegaPow (a : Gamma0Note) :
    OrdinalNotation.omegaPow a = Gamma0Note.omegaPow a := rfl

@[simp] theorem Gamma0Note_one : (OrdinalNotation.one : Gamma0Note) = 1 := rfl

@[simp] theorem Gamma0Note_ofNat (n : ℕ) :
    (OrdinalNotation.ofNat n : Gamma0Note) = Gamma0Note.ofNat n := rfl

@[simp] theorem Gamma0Note_sq (a : Gamma0Note) : sq a = Gamma0Note.nadd a a := rfl

@[simp] theorem Gamma0Note_succ (a : Gamma0Note) :
    succ a = Gamma0Note.nadd a 1 := rfl

end OrdinalNotation

namespace Gamma0Note

/-- **The `ω`-tower does not escape an ε-number.**

`ε_a = ω ^ ε_a`, so each level of the tower stays below `ε_a`; this is the height bookkeeping
of the second cut-elimination theorem. -/
theorem omegaTower_lt_epsilon {a : Gamma0Note} :
    ∀ (k : ℕ) (x : Gamma0Note), x < epsilonNote a →
      OrdinalNotation.omegaTower k x < epsilonNote a
  | 0, _, h => h
  | (k + 1), x, h => by
    rw [OrdinalNotation.omegaTower_succ, OrdinalNotation.Gamma0Note_omegaPow]
    exact omegaTower_lt_epsilon k (omegaPow x) (omegaPow_lt_epsilon h)

/-- The reduction lemma's doubled bound also stays below an ε-number. -/
theorem redOrd_lt_epsilon {a x y : Gamma0Note} (hx : x < epsilonNote a)
    (hy : y < epsilonNote a) : OrdinalNotation.redOrd x y < epsilonNote a := by
  have h₁ : Gamma0Note.nadd x y < epsilonNote a := nadd_lt_epsilon hx hy
  show OrdinalNotation.sq (OrdinalNotation.nadd x y) < epsilonNote a
  rw [OrdinalNotation.Gamma0Note_nadd, OrdinalNotation.Gamma0Note_sq]
  exact nadd_lt_epsilon h₁ h₁

end Gamma0Note

end OrdinalAnalysis
