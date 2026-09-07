/-
  The natural sum on `NONote`, the subtype of notations that are in normal form.

  `BoundedDerivable` is indexed by these rather than by raw `ONote`.  The order
  on `ONote` is defined through `repr`, and `repr` of a notation that is not in
  normal form is not the ordinal it looks like — so every order fact used for
  the ordinal bookkeeping, monotonicity above all, needs the normal-form
  hypothesis.  Carrying it in the index removes it from every statement
  downstream, and `NONote` additionally comes with `LinearOrder` and
  `WellFoundedLT`, both of which the elimination lemma will want.
-/
import OrdinalAnalysis.Ordinal.NaturalSumMono

namespace OrdinalAnalysis

namespace NONote

open ONote

/-- Natural (Hessenberg) sum of normal-form notations. -/
def nadd (a b : _root_.NONote) : _root_.NONote :=
  ⟨OrdinalAnalysis.nadd a.1 b.1, by
    have := a.2; have := b.2; exact OrdinalAnalysis.nadd_nf a.1 b.1⟩

@[simp] theorem nadd_coe (a b : _root_.NONote) :
    (nadd a b).1 = OrdinalAnalysis.nadd a.1 b.1 := rfl

@[simp] theorem val_zero : (0 : _root_.NONote).1 = (0 : ONote) := rfl

@[simp] theorem nadd_zero (a : _root_.NONote) : nadd a 0 = a := by
  apply Subtype.ext; simp [nadd]

@[simp] theorem zero_nadd (a : _root_.NONote) : nadd 0 a = a := by
  apply Subtype.ext; simp [nadd]

theorem nadd_comm (a b : _root_.NONote) : nadd a b = nadd b a := by
  apply Subtype.ext; simpa using OrdinalAnalysis.nadd_comm a.1 b.1

theorem le_nadd_left (a b : _root_.NONote) : a ≤ nadd a b :=
  OrdinalAnalysis.repr_le_nadd_left a.1 b.1 a.2 b.2

theorem le_nadd_right (a b : _root_.NONote) : b ≤ nadd a b :=
  OrdinalAnalysis.repr_le_nadd_right a.1 b.1 a.2 b.2

theorem nadd_lt_nadd_left {a a' : _root_.NONote} (b : _root_.NONote) (h : a < a') :
    nadd a b < nadd a' b :=
  OrdinalAnalysis.nadd_lt_nadd_left a.1 a'.1 b.1 a.2 a'.2 b.2 h

theorem nadd_lt_nadd_right {b b' : _root_.NONote} (a : _root_.NONote) (h : b < b') :
    nadd a b < nadd a b' :=
  OrdinalAnalysis.nadd_lt_nadd_right a.1 b.1 b'.1 a.2 b.2 b'.2 h

theorem nadd_le_nadd_left {a a' : _root_.NONote} (b : _root_.NONote) (h : a ≤ a') :
    nadd a b ≤ nadd a' b := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (nadd_lt_nadd_left b h)
  · exact le_rfl

theorem nadd_le_nadd_right {b b' : _root_.NONote} (a : _root_.NONote) (h : b ≤ b') :
    nadd a b ≤ nadd a b' := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (nadd_lt_nadd_right a h)
  · exact le_rfl

/-- `x ⊕ x`.  The reduction lemma is proved with the bound `sq (β ⊕ γ)` rather
than the textbook `β ⊕ γ`, and this is the whole reason: the propositional
principal case performs two *nested* cuts, so it needs two strictly increasing
ordinals above everything the induction hypotheses hand back, and `β ⊕ γ`
supplies only one.  Doubling is the cheapest repair that survives the
recursion, and it costs nothing downstream because `ω ^ α` is additively
indecomposable, so the elimination lemma absorbs it. -/
def sq (x : _root_.NONote) : _root_.NONote := nadd x x

theorem sq_lt_sq {x y : _root_.NONote} (h : x < y) : sq x < sq y :=
  lt_trans (nadd_lt_nadd_left x h) (nadd_lt_nadd_right y h)

theorem sq_le_sq {x y : _root_.NONote} (h : x ≤ y) : sq x ≤ sq y :=
  le_trans (nadd_le_nadd_left x h) (nadd_le_nadd_right y h)

/-- The witness for the gap below. -/
def mid (s₀ s₁ s : _root_.NONote) : _root_.NONote := nadd (max s₀ s₁) s

/-- **The room lemma.**  If `s₀` and `s₁` are both below `s`, then `mid s₀ s₁ s`
sits strictly above `sq s₀` and `sq s₁` and strictly below `sq s`.

This is the one arithmetic fact the reduction lemma's principal cases turn on.
Note what it does *not* need: associativity of the natural sum, which is a
genuinely painful induction over Cantor normal forms and which this formulation
sidesteps entirely by keeping every term a two-argument `nadd`. -/
theorem sq_lt_mid_left {s₀ s₁ s : _root_.NONote} (h₀ : s₀ < s) (h₁ : s₁ < s) :
    sq s₀ < mid s₀ s₁ s := by
  have hm : max s₀ s₁ < s := max_lt h₀ h₁
  calc sq s₀ ≤ sq (max s₀ s₁) := sq_le_sq (le_max_left _ _)
    _ < nadd (max s₀ s₁) s := nadd_lt_nadd_right _ hm
    _ = mid s₀ s₁ s := rfl

theorem sq_lt_mid_right {s₀ s₁ s : _root_.NONote} (h₀ : s₀ < s) (h₁ : s₁ < s) :
    sq s₁ < mid s₀ s₁ s := by
  have hm : max s₀ s₁ < s := max_lt h₀ h₁
  calc sq s₁ ≤ sq (max s₀ s₁) := sq_le_sq (le_max_right _ _)
    _ < nadd (max s₀ s₁) s := nadd_lt_nadd_right _ hm
    _ = mid s₀ s₁ s := rfl

theorem mid_lt_sq {s₀ s₁ s : _root_.NONote} (h₀ : s₀ < s) (h₁ : s₁ < s) :
    mid s₀ s₁ s < sq s :=
  nadd_lt_nadd_left s (max_lt h₀ h₁)

/-- The ordinal the reduction lemma delivers. -/
def redOrd (β γ : _root_.NONote) : _root_.NONote := sq (nadd β γ)

theorem redOrd_lt_left {β β' : _root_.NONote} (γ : _root_.NONote) (h : β < β') :
    redOrd β γ < redOrd β' γ :=
  sq_lt_sq (nadd_lt_nadd_left γ h)

theorem redOrd_lt_right {γ γ' : _root_.NONote} (β : _root_.NONote) (h : γ < γ') :
    redOrd β γ < redOrd β γ' :=
  sq_lt_sq (nadd_lt_nadd_right β h)

end NONote

end OrdinalAnalysis
