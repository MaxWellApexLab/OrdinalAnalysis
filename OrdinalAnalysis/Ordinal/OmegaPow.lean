/-
  `ω ^ α` on normal-form notations, and the one fact about it that the
  elimination lemma turns on: it is additively indecomposable for the *natural*
  sum, not just for ordinary addition.

  The proof is shorter than it looks, and the reason is worth recording.  The
  obvious route is ordinal arithmetic: unfold `repr`, appeal to mathlib's theory
  of principal ordinals, and fight the natural sum's lack of an `Ordinal`-level
  API.  The route taken instead is syntactic.  `ONote.NFBelow o b` already says
  exactly "`o` is a normal form all of whose exponents are below `b`", mathlib
  supplies both halves of `NFBelow o b ↔ repr o < ω ^ b`, and the natural sum
  merges Cantor normal forms without inventing new exponents — which is
  `nadd_nfBelow`, proved when the natural sum was defined.  Sandwiching those
  three facts is the whole argument.
-/
import OrdinalAnalysis.Ordinal.NONatSum

namespace OrdinalAnalysis

namespace NONote

open Ordinal

/-- `ω ^ a`, as a normal-form notation.  In Cantor normal form this is the
single term `ω ^ a · 1 + 0`, and its normal-form proof is immediate: the
exponent inherits `a`'s, and the tail is `0`. -/
def omegaPow (a : _root_.NONote) : _root_.NONote :=
  ⟨ONote.oadd a.1 1 0, ONote.NF.oadd a.2 1 ONote.NFBelow.zero⟩

@[simp] theorem repr_omegaPow (a : _root_.NONote) :
    ONote.repr (omegaPow a).1 = Ordinal.omega0 ^ ONote.repr a.1 := by
  simp [omegaPow]

@[simp] theorem NONote_repr_omegaPow (a : _root_.NONote) :
    _root_.NONote.repr (omegaPow a) = Ordinal.omega0 ^ ONote.repr a.1 :=
  repr_omegaPow a

theorem omegaPow_lt_omegaPow {a b : _root_.NONote} (h : a < b) :
    omegaPow a < omegaPow b := by
  show ONote.repr (omegaPow a).1 < ONote.repr (omegaPow b).1
  rw [repr_omegaPow, repr_omegaPow]
  exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 h

theorem omegaPow_le_omegaPow {a b : _root_.NONote} (h : a ≤ b) :
    omegaPow a ≤ omegaPow b := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (omegaPow_lt_omegaPow h)
  · exact le_rfl

theorem omegaPow_pos (a : _root_.NONote) : (0 : _root_.NONote) < omegaPow a := by
  show ONote.repr (0 : _root_.NONote).1 < ONote.repr (omegaPow a).1
  rw [repr_omegaPow]
  simpa using Ordinal.opow_pos (ONote.repr a.1) Ordinal.omega0_pos


private theorem lt_omegaPow_raw :
    ∀ o : ONote, ONote.NF o → ONote.repr o < Ordinal.omega0 ^ ONote.repr o
  | 0, _ => by simp
  | ONote.oadd e n t, h => by
      have he : ONote.repr e < ONote.repr (ONote.oadd e n t) :=
        lt_of_lt_of_le (lt_omegaPow_raw e h.fst) (ONote.omega0_le_oadd e n t)
      have ho : ONote.oadd e n t < ONote.oadd (ONote.oadd e n t) 1 0 :=
        ONote.oadd_lt_oadd_1 h he
      simpa [ONote.lt_def] using ho

/-- The induction on the exponent. -/
theorem lt_omegaPow_self (a : _root_.NONote) : a < omegaPow a := by
  change ONote.repr a.1 < ONote.repr (ONote.oadd a.1 1 0)
  simpa using lt_omegaPow_raw a.1 a.2

/-- **Additive indecomposability of `ω ^ a` for the natural sum.**

This is what the elimination lemma needs, and it is the reason the reduction
lemma was free to double its ordinal bound: any finite amount of natural-sum
slack below `ω ^ a` stays below `ω ^ a`. -/
theorem nadd_lt_omegaPow {a x y : _root_.NONote}
    (hx : x < omegaPow a) (hy : y < omegaPow a) :
    nadd x y < omegaPow a := by
  have hx' : ONote.repr x.1 < Ordinal.omega0 ^ ONote.repr a.1 := by
    have h : ONote.repr x.1 < ONote.repr (omegaPow a).1 := hx
    rwa [repr_omegaPow] at h
  have hy' : ONote.repr y.1 < Ordinal.omega0 ^ ONote.repr a.1 := by
    have h : ONote.repr y.1 < ONote.repr (omegaPow a).1 := hy
    rwa [repr_omegaPow] at h
  have hbx : ONote.NFBelow x.1 (ONote.repr a.1) := ONote.NF.below_of_lt' hx' x.2
  have hby : ONote.NFBelow y.1 (ONote.repr a.1) := ONote.NF.below_of_lt' hy' y.2
  have h := (OrdinalAnalysis.nadd_nfBelow hbx hby).repr_lt
  show ONote.repr (nadd x y).1 < ONote.repr (omegaPow a).1
  rw [repr_omegaPow]
  simpa using h

/-- The doubled bound the reduction lemma delivers is still below `ω ^ a`. -/
theorem redOrd_lt_omegaPow {a x y : _root_.NONote}
    (hx : x < omegaPow a) (hy : y < omegaPow a) :
    redOrd x y < omegaPow a := by
  have h₁ : nadd x y < omegaPow a := nadd_lt_omegaPow hx hy
  exact nadd_lt_omegaPow h₁ h₁

/-- The `n`-fold tower `ω ^ ω ^ ⋯ ^ α`.

The recursion pushes the new exponentiation *inside*, which is what makes the
cut-elimination induction definitional: peeling one level of rank turns
`α` into `ω ^ α` and leaves `n` levels still to peel. -/
def omegaTower : ℕ → _root_.NONote → _root_.NONote
  | 0, α => α
  | (n + 1), α => omegaTower n (omegaPow α)

@[simp] theorem omegaTower_zero (α : _root_.NONote) : omegaTower 0 α = α := rfl

@[simp] theorem omegaTower_succ (n : ℕ) (α : _root_.NONote) :
    omegaTower (n + 1) α = omegaTower n (omegaPow α) := rfl

end NONote

end OrdinalAnalysis
