/-
  A notation system cut off below a closed bound.

  The lower-bound chain — replay, cutting away the axioms, cut elimination,
  boundedness — is generic in the notation system `O` that carries both the
  heights and the codes.  To run it for `|PA + TI(ε₀)| ≤ ε₁` the system must
  be exactly the notations below `ε₁`: boundedness reads the derivation's
  `X`-atoms as codes of elements of `O`, and the induction axiom it refutes
  is transfinite induction along *all* of `O`'s coded ordering.  So `O` is
  the subtype `{o // o < ε}` of a larger system, for a bound `ε` closed under
  the operations of the class.  Every ε-number is such a bound, and so is
  every `φ_a(0)` and `Γ₀`; this file is the one construction they all use.
-/
import OrdinalAnalysis.Ordinal.Notation

set_option autoImplicit false

namespace OrdinalAnalysis

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- A bound closed under the natural sum, the ω-power, and the numerals. -/
structure OrdinalNotation.Closed (ε : O) : Prop where
  nadd_lt : ∀ {x y : O}, x < ε → y < ε → OrdinalNotation.nadd x y < ε
  omegaPow_lt : ∀ {x : O}, x < ε → OrdinalNotation.omegaPow x < ε
  ofNat_lt : ∀ n : ℕ, OrdinalNotation.ofNat n < ε
  one_lt : OrdinalNotation.one < ε

/-- The notations below `ε`. -/
def Below (ε : O) : Type := {o : O // o < ε}

namespace Below

variable {ε : O}

instance : LinearOrder (Below ε) := inferInstanceAs (LinearOrder {o : O // o < ε})

instance : WellFoundedLT (Below ε) := inferInstanceAs (WellFoundedLT {o : O // o < ε})

/-- The underlying notation. -/
def val (a : Below ε) : O := a.1

theorem lt_def {a b : Below ε} : a < b ↔ a.1 < b.1 := Iff.rfl

theorem le_def {a b : Below ε} : a ≤ b ↔ a.1 ≤ b.1 := Iff.rfl

theorem val_strictMono : StrictMono (val (ε := ε)) := fun _ _ h => h

@[ext] theorem ext {a b : Below ε} (h : a.1 = b.1) : a = b := Subtype.ext h

/-- **The class instance**, for a closed bound.  Every operation is the
operation of `O`, every law is the law of `O`. -/
def ordinalNotation (h : OrdinalNotation.Closed ε) : OrdinalNotation (Below ε) where
  nadd a b := ⟨OrdinalNotation.nadd a.1 b.1, h.nadd_lt a.2 b.2⟩
  nadd_comm a b := Subtype.ext (OrdinalNotation.nadd_comm a.1 b.1)
  nadd_assoc a b c := Subtype.ext (OrdinalNotation.nadd_assoc a.1 b.1 c.1)
  le_nadd_left a b := OrdinalNotation.le_nadd_left a.1 b.1
  nadd_lt_nadd_left b hab := OrdinalNotation.nadd_lt_nadd_left b.1 hab
  omegaPow a := ⟨OrdinalNotation.omegaPow a.1, h.omegaPow_lt a.2⟩
  omegaPow_lt_omegaPow hab := OrdinalNotation.omegaPow_lt_omegaPow hab
  nadd_lt_omegaPow hx hy := OrdinalNotation.nadd_lt_omegaPow hx hy
  one := ⟨OrdinalNotation.one, h.one_lt⟩
  lt_nadd_one a := OrdinalNotation.lt_nadd_one a.1
  one_le_omegaPow a := OrdinalNotation.one_le_omegaPow a.1
  ofNat n := ⟨OrdinalNotation.ofNat n, h.ofNat_lt n⟩
  ofNat_lt_ofNat hmn := OrdinalNotation.ofNat_lt_ofNat hmn

end Below

end OrdinalAnalysis
