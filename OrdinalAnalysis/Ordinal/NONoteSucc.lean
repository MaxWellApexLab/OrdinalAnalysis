/-
  `repr` of the project's natural-sum successor.

  `ACAOmega/Axioms₂.lean`'s rank bound needs `repr (NONote.succ a) = repr a + 1`
  (`NONote.succ a := nadd a one`, `Ordinal/Notation.lean`), and
  `Ordinal/NaturalSum.lean` proves only order facts about `nadd` — never its
  `repr`.  This file supplies exactly that one computation, by structural
  recursion on the Cantor normal form of `a`, following `nadd`'s own case
  split against the second argument `1 = oadd 0 1 0`:

  * `a = 0`: `nadd 0 1 = 1` outright (`zero_nadd`).
  * `a = oadd e n r` with `e = 0` (so `r = 0`, since a normal form with a zero
    exponent has a zero tail — `ONote.NF.zero_of_zero`): the coefficient is
    bumped, `ω^0 * (n+1) = n+1`.
  * `a = oadd e n r` with `e ≠ 0` (`e` itself of shape `oadd e' n' a'`): the
    `1` merges into the tail, `nadd (oadd e n r) 1 = oadd e n (nadd r 1)`, and
    `repr` is `ω^(repr e) * n + repr (nadd r 1) = ω^(repr e) * n + (repr r + 1)
    = (ω^(repr e) * n + repr r) + 1` by associativity of ordinal addition.
-/
import OrdinalAnalysis.Ordinal.Notation

set_option autoImplicit false

namespace OrdinalAnalysis

open ONote

/-- **`repr` of the natural sum at `1`**, on raw `ONote`s in normal form.
The pure-ordinal fact `NONote.repr_succ` below is this, transported to the
normal-form subtype. -/
theorem repr_nadd_one : ∀ (x : ONote), ONote.NF x →
    ONote.repr (nadd x 1) = ONote.repr x + 1
  | 0, _ => by simp
  | ONote.oadd e n a, h => by
      rcases e with _ | ⟨e', n', a'⟩
      · -- `e = 0`: normal form forces `a = 0`, so `x` is the natural number `n`.
        obtain rfl : a = 0 := ONote.NF.zero_of_zero h rfl
        rw [nadd.eq_def]
        show ONote.repr (ONote.oadd 0 (n + 1) (nadd (0 : ONote) 0))
            = ONote.repr (ONote.oadd (0 : ONote) n 0) + 1
        simp [Ordinal.opow_zero, PNat.add_coe, Nat.cast_add]
      · -- `e = oadd e' n' a' ≠ 0`: the `1` merges into the tail.
        have ha : ONote.NF a := h.snd
        rw [nadd.eq_def]
        show ONote.repr (ONote.oadd (ONote.oadd e' n' a') n (nadd a 1))
            = ONote.repr (ONote.oadd (ONote.oadd e' n' a') n a) + 1
        simp only [ONote.repr, repr_nadd_one a ha, add_assoc]
  termination_by x => nsize x
  decreasing_by all_goals (simp [nsize]; try omega)

namespace NONote

/-- **The `repr` of `NONote.succ`.**  `NONote.succ` is built from the project's
natural sum rather than ordinal addition (`Ordinal/Notation.lean`), so that the
monotonicity already proved for the natural sum applies to it; this is the fact
that its `repr` nonetheless still computes as the ordinary ordinal successor.
This is exactly the missing lemma flagged by `ACAOmega/Axioms₂.lean`'s "Not
done here" section. -/
theorem repr_succ (a : _root_.NONote) :
    ONote.repr (NONote.succ a).1 = ONote.repr a.1 + 1 :=
  OrdinalAnalysis.repr_nadd_one a.1 a.2

/-- `NONote.succ` is monotone: `succ = nadd · one`, and `nadd` is monotone in
its left argument. -/
theorem succ_le_succ {a a' : _root_.NONote} (h : a ≤ a') :
    NONote.succ a ≤ NONote.succ a' :=
  NONote.nadd_le_nadd_left NONote.one h

end NONote

end OrdinalAnalysis
