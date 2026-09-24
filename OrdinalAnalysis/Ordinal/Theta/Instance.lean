/-
  The ϑ-notation as an `OrdinalNotation`.

  The class `OrdinalNotation` isolates what the infinitary calculus consumes from
  its type of heights: a natural sum, `ω^·` with strict monotonicity and additive
  indecomposability, `1`, and the numerals.  Every field is discharged by the syntactic
  arithmetic of the ϑ-notation (the natural sum merges the Cantor exponent lists, `ω^α`
  is the normal form with the single exponent `α`, `1 = ω^0`, and the numeral `n` is
  `⟨0, …, 0⟩`); nothing is re-proved.

  The class takes the well-foundedness of the order as a parameter (`[WellFoundedLT O]`), not
  as a field, and its projections receive that parameter as an implicit argument determined
  by the instance found.  An instance whose type mentions a well-foundedness hypothesis
  that is itself a variable would leave that argument undetermined; so the structure is given
  here as a definition, `ThetaNote.ordinalNotation`, whose fields use no well-foundedness at
  all.  Once `WellFoundedLT ThetaNote` is an instance (the well-foundedness of the ϑ-order,
  by the distinguished-set argument of Buchholz; cf. Freund, arXiv:2204.09321, §3), the
  instance is the one line `instance : OrdinalNotation ThetaNote := ThetaNote.ordinalNotation`.

  As for `Gamma0Note`, the field `a < ω^a` is absent from the class, and it is false here:
  the principal terms `Ω` and `ϑ β` are fixed points of `ω^·` (`ThetaNote.omegaPow_eq_self_iff`).
  The file closes with the closure of the principal terms under the operations of the class,
  in particular under the `ω`-tower.
-/
import OrdinalAnalysis.Ordinal.Notation
import OrdinalAnalysis.Ordinal.Theta.Arith

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaNote

/-- The ϑ-notation is an ordinal notation system, given the well-foundedness of its order;
no field depends on that hypothesis. -/
@[instance_reducible]
def ordinalNotation [WellFoundedLT ThetaNote] : OrdinalNotation ThetaNote where
  nadd := ThetaNote.nadd
  nadd_comm := ThetaNote.nadd_comm
  nadd_assoc := ThetaNote.nadd_assoc
  le_nadd_left := ThetaNote.le_nadd_left
  nadd_lt_nadd_left := ThetaNote.nadd_lt_nadd_left
  omegaPow := ThetaNote.omegaPow
  omegaPow_lt_omegaPow := ThetaNote.omegaPow_lt_omegaPow
  nadd_lt_omegaPow := ThetaNote.nadd_lt_omegaPow
  one := ThetaNote.one
  lt_nadd_one := ThetaNote.lt_nadd_one
  one_le_omegaPow := ThetaNote.one_le_omegaPow
  ofNat := ThetaNote.ofNat
  ofNat_lt_ofNat := ThetaNote.ofNat_lt_ofNat

variable [WellFoundedLT ThetaNote]

/-! ### The generic operations are the ϑ-operations -/

@[simp] theorem ordinalNotation_nadd (a b : ThetaNote) :
    @OrdinalNotation.nadd ThetaNote _ _ ordinalNotation a b = ThetaNote.nadd a b := rfl

@[simp] theorem ordinalNotation_omegaPow (a : ThetaNote) :
    @OrdinalNotation.omegaPow ThetaNote _ _ ordinalNotation a = omegaPow a := rfl

@[simp] theorem ordinalNotation_one :
    @OrdinalNotation.one ThetaNote _ _ ordinalNotation = one := rfl

@[simp] theorem ordinalNotation_ofNat (n : ℕ) :
    @OrdinalNotation.ofNat ThetaNote _ _ ordinalNotation n = ofNat n := rfl

@[simp] theorem ordinalNotation_succ (a : ThetaNote) :
    @OrdinalNotation.succ ThetaNote _ _ ordinalNotation a = succ a := rfl

/-- The generic successor is the ordinal successor `α + 1`. -/
theorem ordinalNotation_succ_eq_add_one (a : ThetaNote) :
    @OrdinalNotation.succ ThetaNote _ _ ordinalNotation a = a + one :=
  (add_one_eq_succ a).symm

/-! ### Principal terms are closed under the operations of the class -/

/-- The `ω`-tower does not escape a principal term. -/
theorem omegaTower_lt_prin {p : ThetaNote} (hp : ThetaTerm.IsPrin p.1) :
    ∀ (n : ℕ) {a : ThetaNote}, a < p →
      @OrdinalNotation.omegaTower ThetaNote _ _ ordinalNotation n a < p
  | 0, _, h => h
  | n + 1, _, h => omegaTower_lt_prin hp n (omegaPow_lt_prin hp h)

/-- The `ω`-tower does not escape `ϑ β`. -/
theorem omegaTower_lt_theta (b : ThetaNote) (n : ℕ) {a : ThetaNote} (h : a < theta b) :
    @OrdinalNotation.omegaTower ThetaNote _ _ ordinalNotation n a < theta b :=
  omegaTower_lt_prin (p := theta b) trivial n h

/-- The `ω`-tower does not escape `Ω`. -/
theorem omegaTower_lt_Omega (n : ℕ) {a : ThetaNote} (h : a < Omega) :
    @OrdinalNotation.omegaTower ThetaNote _ _ ordinalNotation n a < Omega :=
  omegaTower_lt_prin (p := Omega) trivial n h

/-- The doubled bound of the reduction lemma does not escape a principal term. -/
theorem redOrd_lt_prin {p x y : ThetaNote} (hp : ThetaTerm.IsPrin p.1) (hx : x < p)
    (hy : y < p) : @OrdinalNotation.redOrd ThetaNote _ _ ordinalNotation x y < p := by
  rw [← omegaPow_eq_self_iff.mpr hp] at hx hy ⊢
  exact @OrdinalNotation.redOrd_lt_omegaPow ThetaNote _ _ ordinalNotation _ _ _ hx hy

end ThetaNote

end OrdinalAnalysis
