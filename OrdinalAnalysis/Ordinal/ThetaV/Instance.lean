/- Source: OrdinalAnalysis\Ordinal\ThetaW\Instance.lean (mechanical rename ThetaW -> ThetaV; residue: the `OmegaW` constructor arm in any exhaustive match on term shape, added by hand). -/
/-
  The multi-level ϑ-notation, on the domain terms, as an `OrdinalNotation`.

  Mirrors `Ordinal/Theta/Instance.lean`: the class `OrdinalNotation` isolates what the
  infinitary calculus consumes from its type of heights (a natural sum, `ω^·` with strict
  monotonicity and additive indecomposability, `1`, and the numerals), and every field is
  discharged by the syntactic arithmetic of `ThetaV/Arith` — nothing is re-proved.

  Unlike `Theta/Instance.lean`, which leaves the actual instance as a `def` pending the (then
  unfinished) well-foundedness of `ThetaNote`, here `WellFoundedLT ThetaVNoteD` is already a
  global instance (`ThetaV/WellFoundedV.wellFoundedLT`), so the registration is completed in one
  line.
-/
import OrdinalAnalysis.Ordinal.Notation
import OrdinalAnalysis.Ordinal.ThetaV.Arith
import OrdinalAnalysis.Ordinal.ThetaV.WellFoundedV

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaVNoteD

/-- The multi-level ϑ-notation on the domain terms is an ordinal notation system. -/
instance ordinalNotation : OrdinalNotation ThetaVNoteD where
  nadd := ThetaVNoteD.nadd
  nadd_comm := ThetaVNoteD.nadd_comm
  nadd_assoc := ThetaVNoteD.nadd_assoc
  le_nadd_left := ThetaVNoteD.le_nadd_left
  nadd_lt_nadd_left := ThetaVNoteD.nadd_lt_nadd_left
  omegaPow := ThetaVNoteD.omegaPow
  omegaPow_lt_omegaPow := ThetaVNoteD.omegaPow_lt_omegaPow
  nadd_lt_omegaPow := ThetaVNoteD.nadd_lt_omegaPow
  one := ThetaVNoteD.one
  lt_nadd_one := ThetaVNoteD.lt_nadd_one
  one_le_omegaPow := ThetaVNoteD.one_le_omegaPow
  ofNat := ThetaVNoteD.ofNat
  ofNat_lt_ofNat := ThetaVNoteD.ofNat_lt_ofNat

/-! ### The generic operations are the ϑ-operations -/

@[simp] theorem ordinalNotation_nadd (a b : ThetaVNoteD) :
    @OrdinalNotation.nadd ThetaVNoteD _ _ ordinalNotation a b = ThetaVNoteD.nadd a b := rfl

@[simp] theorem ordinalNotation_omegaPow (a : ThetaVNoteD) :
    @OrdinalNotation.omegaPow ThetaVNoteD _ _ ordinalNotation a = omegaPow a := rfl

@[simp] theorem ordinalNotation_one :
    @OrdinalNotation.one ThetaVNoteD _ _ ordinalNotation = one := rfl

@[simp] theorem ordinalNotation_ofNat (n : ℕ) :
    @OrdinalNotation.ofNat ThetaVNoteD _ _ ordinalNotation n = ofNat n := rfl

@[simp] theorem ordinalNotation_succ (a : ThetaVNoteD) :
    @OrdinalNotation.succ ThetaVNoteD _ _ ordinalNotation a = succ a := rfl

/-- The generic successor is the ordinal successor `α + 1`. -/
theorem ordinalNotation_succ_eq_add_one (a : ThetaVNoteD) :
    @OrdinalNotation.succ ThetaVNoteD _ _ ordinalNotation a = a + one :=
  (add_one_eq_succ a).symm

/-! ### Principal terms are closed under the operations of the class -/

/-- The `ω`-tower does not escape a principal term. -/
theorem omegaTower_lt_prin {p : ThetaVNoteD} (hp : ThetaVTerm.IsPrin p.1) :
    ∀ (n : ℕ) {a : ThetaVNoteD}, a < p →
      @OrdinalNotation.omegaTower ThetaVNoteD _ _ ordinalNotation n a < p
  | 0, _, h => h
  | n + 1, _, h => omegaTower_lt_prin hp n (omegaPow_lt_prin hp h)

/-- The `ω`-tower does not escape `Ω_{k+1}`. -/
theorem omegaTower_lt_Omega (k : ℕ) (n : ℕ) {a : ThetaVNoteD} (h : a < Omega k) :
    @OrdinalNotation.omegaTower ThetaVNoteD _ _ ordinalNotation n a < Omega k :=
  omegaTower_lt_prin (p := Omega k) trivial n h

/-- The doubled bound of the reduction lemma does not escape a principal term. -/
theorem redOrd_lt_prin {p x y : ThetaVNoteD} (hp : ThetaVTerm.IsPrin p.1) (hx : x < p)
    (hy : y < p) : @OrdinalNotation.redOrd ThetaVNoteD _ _ ordinalNotation x y < p := by
  rw [← omegaPow_eq_self_iff.mpr hp] at hx hy ⊢
  exact @OrdinalNotation.redOrd_lt_omegaPow ThetaVNoteD _ _ ordinalNotation _ _ _ hx hy

end ThetaVNoteD

end OrdinalAnalysis
