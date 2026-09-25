/-
  The multi-level ϑ-notation, on the domain terms, as an `OrdinalNotation`.

  Mirrors `Ordinal/Theta/Instance.lean`: the class `OrdinalNotation` isolates what the
  infinitary calculus consumes from its type of heights (a natural sum, `ω^·` with strict
  monotonicity and additive indecomposability, `1`, and the numerals), and every field is
  discharged by the syntactic arithmetic of `ThetaW/Arith` — nothing is re-proved.

  Unlike `Theta/Instance.lean`, which leaves the actual instance as a `def` pending the (then
  unfinished) well-foundedness of `ThetaNote`, here `WellFoundedLT ThetaWNoteD` is already a
  global instance (`ThetaW/WellFoundedD.wellFoundedLT`), so the registration is completed in one
  line.
-/
import OrdinalAnalysis.Ordinal.Notation
import OrdinalAnalysis.Ordinal.ThetaW.Arith
import OrdinalAnalysis.Ordinal.ThetaW.WellFoundedD

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWNoteD

/-- The multi-level ϑ-notation on the domain terms is an ordinal notation system. -/
instance ordinalNotation : OrdinalNotation ThetaWNoteD where
  nadd := ThetaWNoteD.nadd
  nadd_comm := ThetaWNoteD.nadd_comm
  nadd_assoc := ThetaWNoteD.nadd_assoc
  le_nadd_left := ThetaWNoteD.le_nadd_left
  nadd_lt_nadd_left := ThetaWNoteD.nadd_lt_nadd_left
  omegaPow := ThetaWNoteD.omegaPow
  omegaPow_lt_omegaPow := ThetaWNoteD.omegaPow_lt_omegaPow
  nadd_lt_omegaPow := ThetaWNoteD.nadd_lt_omegaPow
  one := ThetaWNoteD.one
  lt_nadd_one := ThetaWNoteD.lt_nadd_one
  one_le_omegaPow := ThetaWNoteD.one_le_omegaPow
  ofNat := ThetaWNoteD.ofNat
  ofNat_lt_ofNat := ThetaWNoteD.ofNat_lt_ofNat

/-! ### The generic operations are the ϑ-operations -/

@[simp] theorem ordinalNotation_nadd (a b : ThetaWNoteD) :
    @OrdinalNotation.nadd ThetaWNoteD _ _ ordinalNotation a b = ThetaWNoteD.nadd a b := rfl

@[simp] theorem ordinalNotation_omegaPow (a : ThetaWNoteD) :
    @OrdinalNotation.omegaPow ThetaWNoteD _ _ ordinalNotation a = omegaPow a := rfl

@[simp] theorem ordinalNotation_one :
    @OrdinalNotation.one ThetaWNoteD _ _ ordinalNotation = one := rfl

@[simp] theorem ordinalNotation_ofNat (n : ℕ) :
    @OrdinalNotation.ofNat ThetaWNoteD _ _ ordinalNotation n = ofNat n := rfl

@[simp] theorem ordinalNotation_succ (a : ThetaWNoteD) :
    @OrdinalNotation.succ ThetaWNoteD _ _ ordinalNotation a = succ a := rfl

/-- The generic successor is the ordinal successor `α + 1`. -/
theorem ordinalNotation_succ_eq_add_one (a : ThetaWNoteD) :
    @OrdinalNotation.succ ThetaWNoteD _ _ ordinalNotation a = a + one :=
  (add_one_eq_succ a).symm

/-! ### Principal terms are closed under the operations of the class -/

/-- The `ω`-tower does not escape a principal term. -/
theorem omegaTower_lt_prin {p : ThetaWNoteD} (hp : ThetaWTerm.IsPrin p.1) :
    ∀ (n : ℕ) {a : ThetaWNoteD}, a < p →
      @OrdinalNotation.omegaTower ThetaWNoteD _ _ ordinalNotation n a < p
  | 0, _, h => h
  | n + 1, _, h => omegaTower_lt_prin hp n (omegaPow_lt_prin hp h)

/-- The `ω`-tower does not escape `Ω_{k+1}`. -/
theorem omegaTower_lt_Omega (k : ℕ) (n : ℕ) {a : ThetaWNoteD} (h : a < Omega k) :
    @OrdinalNotation.omegaTower ThetaWNoteD _ _ ordinalNotation n a < Omega k :=
  omegaTower_lt_prin (p := Omega k) trivial n h

/-- The doubled bound of the reduction lemma does not escape a principal term. -/
theorem redOrd_lt_prin {p x y : ThetaWNoteD} (hp : ThetaWTerm.IsPrin p.1) (hx : x < p)
    (hy : y < p) : @OrdinalNotation.redOrd ThetaWNoteD _ _ ordinalNotation x y < p := by
  rw [← omegaPow_eq_self_iff.mpr hp] at hx hy ⊢
  exact @OrdinalNotation.redOrd_lt_omegaPow ThetaWNoteD _ _ ordinalNotation _ _ _ hx hy

end ThetaWNoteD

end OrdinalAnalysis
