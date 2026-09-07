/-
  Ordinal notations, abstractly.

  The infinitary calculus of `Omega/` was written with `NONote` — mathlib's
  notations below `ε₀` — hard-wired as the type of heights.  Nothing in it uses
  anything about `NONote` beyond a handful of order-arithmetic facts, and the
  next results need heights above `ε₀`, so this file isolates those facts as a
  class and re-installs `NONote` as an instance.

  Two decisions about the shape.

  * The class is a **mixin** over `LinearOrder` and `WellFoundedLT` rather than
    an extension of them.  `NONote` already carries mathlib's order, and an
    `extends LinearOrder` would put a second one in scope: every downstream
    `<` would then have to be checked for which of the two it means, and the
    instances that mathlib derives from its own order (`max`, `le_of_lt`, the
    lattice lemmas) would not apply to ours.  Mixing in keeps a single order.

  * `WellFoundedLT` is a parameter of the class rather than a field.  It is a
    `Prop`-valued class, so proof irrelevance makes any two routes to it
    definitionally equal, and there is nothing to diverge; only `LinearOrder`
    carries data, and `NONote` has exactly one.

  What the calculus actually needs is short: a natural (commutative,
  strictly monotone) sum, `ω ^ ·` with strict monotonicity and additive
  indecomposability, a `1` strictly above nothing in particular but strictly
  raising the sum, and an embedding of `ℕ` used only for the finite heights of
  the identity sequents.  Everything else — the doubled bound `sq`, the witness
  `mid`, the reduction ordinal `redOrd`, the `ω`-tower, the successor — is
  *defined* from those, once, here, instead of once per notation system.

  This file also holds `NONote.one`, `NONote.succ` and their three order
  lemmas, which used to live in `Proof/Bridge.lean`.  They belong to the
  notation layer, not to the bridge, and keeping them here is what lets
  `Ordinal/` be free of any dependency on `Proof/`.
-/
import OrdinalAnalysis.Ordinal.OmegaPow
import OrdinalAnalysis.Ordinal.NaturalSumAssoc

namespace OrdinalAnalysis

/-! ### `1` and the successor on `NONote`

Moved here from `Proof/Bridge.lean`; the names are unchanged, so the bridge and
the `Gentzen/` files see exactly what they saw before. -/

namespace NONote

/-- `1`, as a normal-form notation. -/
def one : _root_.NONote := ⟨1, by infer_instance⟩

@[simp] theorem repr_one : ONote.repr one.1 = 1 := by simp [one]

/-- Successor, built from the natural sum rather than from ordinal addition,
so that the monotonicity already proved for the natural sum applies to it. -/
def succ (a : _root_.NONote) : _root_.NONote := nadd a one

theorem lt_succ (a : _root_.NONote) : a < succ a := by
  have h : ONote.repr a.1 < ONote.repr (OrdinalAnalysis.nadd one.1 a.1) :=
    OrdinalAnalysis.lt_nadd_of_pos one.1 a.1 one.2 a.2 (by simp)
  show ONote.repr a.1 < ONote.repr (succ a).1
  have e : OrdinalAnalysis.nadd a.1 one.1 = OrdinalAnalysis.nadd one.1 a.1 :=
    OrdinalAnalysis.nadd_comm _ _
  simpa [succ, e] using h

theorem le_succ (a : _root_.NONote) : a ≤ succ a := le_of_lt (lt_succ a)

theorem lt_succ_of_le {a b : _root_.NONote} (h : a ≤ b) : a < succ b :=
  lt_of_le_of_lt h (lt_succ b)

/-- The embedding of `ℕ` is strictly monotone.  `NONote.ofNat` is mathlib's
(`Mathlib/SetTheory/Ordinal/Notation.lean`) and `ONote.repr_ofNat` computes its
`repr`; since the order on `NONote` *is* the order on `repr`, this is one
unfolding away. -/
theorem ofNat_lt_ofNat {m n : ℕ} (h : m < n) :
    _root_.NONote.ofNat m < _root_.NONote.ofNat n := by
  show ONote.repr (ONote.ofNat m) < ONote.repr (ONote.ofNat n)
  rw [ONote.repr_ofNat, ONote.repr_ofNat]
  exact_mod_cast h

/-! ### The two facts the boundedness lemma needs beyond the calculus

Both used to live in `Gentzen/Boundedness.lean`, where they were proved for
`NONote` alone; they are the fields `nadd_assoc` and `one_le_omegaPow` of the
class below, so they belong next to the other instance data.  The names in
`Boundedness.lean` are kept there as `NONote` restatements. -/

/-- Associativity of the natural sum, lifted from `Ordinal/NaturalSumAssoc.lean`
to normal-form notations. -/
theorem nadd_assoc (a b c : _root_.NONote) :
    NONote.nadd (NONote.nadd a b) c = NONote.nadd a (NONote.nadd b c) := by
  apply Subtype.ext
  simp only [NONote.nadd_coe]
  exact _root_.OrdinalAnalysis.nadd_assoc a.1 b.1 c.1 a.2 b.2 c.2

theorem zero_le' (a : _root_.NONote) : (0 : _root_.NONote) ≤ a := by
  refine not_lt.mp (fun h => ?_)
  have h' : ONote.repr a.1 < ONote.repr (0 : _root_.NONote).1 := h
  simp at h'

theorem one_eq_omegaPow_zero : NONote.one = NONote.omegaPow 0 := Subtype.ext rfl

theorem one_le_omegaPow (a : _root_.NONote) : NONote.one ≤ NONote.omegaPow a := by
  rw [one_eq_omegaPow_zero]
  exact NONote.omegaPow_le_omegaPow (zero_le' a)

end NONote

/-! ### The class -/

/-- An **ordinal notation system**, in exactly the strength the infinitary
calculus consumes.

A mixin over an existing linear order that is well founded downwards; see the
module docstring for why it is a mixin and not an extension.

The natural sum is required to be commutative and strictly monotone in its left
argument (monotonicity on the right, and the non-strict forms, are derived), and
`ω ^ ·` is required to be strictly monotone and *additively indecomposable for
the natural sum* — that last is the one non-formal fact, and the whole reason
the reduction lemma may double its bound. -/
class OrdinalNotation (O : Type) [LinearOrder O] [WellFoundedLT O] where
  /-- The natural (Hessenberg) sum. -/
  nadd : O → O → O
  /-- The natural sum is commutative. -/
  nadd_comm : ∀ a b : O, nadd a b = nadd b a
  /-- The natural sum is associative.  Not needed by the calculus itself — the
  reduction lemma is deliberately phrased so as to avoid it — but the
  boundedness lemma's bump does need it: raising the lower bound to
  `succ (γ ⊕ ω^β)` and re-adding `ω^β` has to be rebracketed around `γ`. -/
  nadd_assoc : ∀ a b c : O, nadd (nadd a b) c = nadd a (nadd b c)
  /-- The natural sum is inflationary. -/
  le_nadd_left : ∀ a b : O, a ≤ nadd a b
  /-- The natural sum is strictly monotone in its left argument. -/
  nadd_lt_nadd_left : ∀ {a a' : O} (b : O), a < a' → nadd a b < nadd a' b
  /-- `ω ^ ·`. -/
  omegaPow : O → O
  /-- `ω ^ ·` is strictly monotone. -/
  omegaPow_lt_omegaPow : ∀ {a b : O}, a < b → omegaPow a < omegaPow b
  /-- `ω ^ a` is additively indecomposable for the natural sum. -/
  nadd_lt_omegaPow : ∀ {a x y : O}, x < omegaPow a → y < omegaPow a → nadd x y < omegaPow a
  /-- `1`. -/
  one : O
  /-- Adding `1` strictly increases.  Stated in this form rather than as
  `0 < one` so that the class needs no `Zero`. -/
  lt_nadd_one : ∀ a : O, a < nadd a one
  /-- `1 ≤ ω ^ a`.  Not derivable from the rest: the class has no `0`, so
  nothing forces `ω ^ ·` to land above `one`.  On `NONote` it is
  `one = ω ^ 0 ≤ ω ^ a`. -/
  one_le_omegaPow : ∀ a : O, one ≤ omegaPow a
  /-- The finite notations, used only for the finite heights of the identity
  sequents. -/
  ofNat : ℕ → O
  /-- The finite notations are ordered as the naturals are. -/
  ofNat_lt_ofNat : ∀ {m n : ℕ}, m < n → ofNat m < ofNat n

namespace OrdinalNotation

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-! ### The natural sum, on the other side -/

theorem le_nadd_right (a b : O) : b ≤ OrdinalNotation.nadd a b := by
  rw [OrdinalNotation.nadd_comm]
  exact OrdinalNotation.le_nadd_left b a

theorem nadd_lt_nadd_right {b b' : O} (a : O) (h : b < b') :
    OrdinalNotation.nadd a b < OrdinalNotation.nadd a b' := by
  rw [OrdinalNotation.nadd_comm a b, OrdinalNotation.nadd_comm a b']
  exact OrdinalNotation.nadd_lt_nadd_left a h

theorem nadd_le_nadd_left {a a' : O} (b : O) (h : a ≤ a') :
    OrdinalNotation.nadd a b ≤ OrdinalNotation.nadd a' b := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (OrdinalNotation.nadd_lt_nadd_left b h)
  · exact le_rfl

theorem nadd_le_nadd_right {b b' : O} (a : O) (h : b ≤ b') :
    OrdinalNotation.nadd a b ≤ OrdinalNotation.nadd a b' := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (nadd_lt_nadd_right a h)
  · exact le_rfl

/-! ### Doubling, and the room lemma -/

/-- `x ⊕ x`.  The reduction lemma is proved with the bound `sq (β ⊕ γ)` rather
than the textbook `β ⊕ γ`, and this is the whole reason: the propositional
principal case performs two *nested* cuts, so it needs two strictly increasing
ordinals above everything the induction hypotheses hand back, and `β ⊕ γ`
supplies only one.  Doubling is the cheapest repair that survives the
recursion, and it costs nothing downstream because `ω ^ α` is additively
indecomposable, so the elimination lemma absorbs it. -/
def sq (x : O) : O := OrdinalNotation.nadd x x

theorem sq_lt_sq {x y : O} (h : x < y) : sq x < sq y :=
  lt_trans (OrdinalNotation.nadd_lt_nadd_left x h) (nadd_lt_nadd_right y h)

theorem sq_le_sq {x y : O} (h : x ≤ y) : sq x ≤ sq y :=
  le_trans (nadd_le_nadd_left x h) (nadd_le_nadd_right y h)

/-- The witness for the gap below. -/
def mid (s₀ s₁ s : O) : O := OrdinalNotation.nadd (max s₀ s₁) s

/-- **The room lemma.**  If `s₀` and `s₁` are both below `s`, then `mid s₀ s₁ s`
sits strictly above `sq s₀` and `sq s₁` and strictly below `sq s`.

This is the one arithmetic fact the reduction lemma's principal cases turn on.
Note what it does *not* need: associativity of the natural sum, which is a
genuinely painful induction over Cantor normal forms and which this formulation
sidesteps entirely by keeping every term a two-argument `nadd`. -/
theorem sq_lt_mid_left {s₀ s₁ s : O} (h₀ : s₀ < s) (h₁ : s₁ < s) :
    sq s₀ < mid s₀ s₁ s := by
  have hm : max s₀ s₁ < s := max_lt h₀ h₁
  calc sq s₀ ≤ sq (max s₀ s₁) := sq_le_sq (le_max_left _ _)
    _ < OrdinalNotation.nadd (max s₀ s₁) s := nadd_lt_nadd_right _ hm
    _ = mid s₀ s₁ s := rfl

theorem sq_lt_mid_right {s₀ s₁ s : O} (h₀ : s₀ < s) (h₁ : s₁ < s) :
    sq s₁ < mid s₀ s₁ s := by
  have hm : max s₀ s₁ < s := max_lt h₀ h₁
  calc sq s₁ ≤ sq (max s₀ s₁) := sq_le_sq (le_max_right _ _)
    _ < OrdinalNotation.nadd (max s₀ s₁) s := nadd_lt_nadd_right _ hm
    _ = mid s₀ s₁ s := rfl

theorem mid_lt_sq {s₀ s₁ s : O} (h₀ : s₀ < s) (h₁ : s₁ < s) :
    mid s₀ s₁ s < sq s :=
  OrdinalNotation.nadd_lt_nadd_left s (max_lt h₀ h₁)

/-- The ordinal the reduction lemma delivers. -/
def redOrd (β γ : O) : O := sq (OrdinalNotation.nadd β γ)

theorem redOrd_lt_left {β β' : O} (γ : O) (h : β < β') : redOrd β γ < redOrd β' γ :=
  sq_lt_sq (OrdinalNotation.nadd_lt_nadd_left γ h)

theorem redOrd_lt_right {γ γ' : O} (β : O) (h : γ < γ') : redOrd β γ < redOrd β γ' :=
  sq_lt_sq (nadd_lt_nadd_right β h)

/-- The doubled bound the reduction lemma delivers is still below `ω ^ a`. -/
theorem redOrd_lt_omegaPow {a x y : O}
    (hx : x < OrdinalNotation.omegaPow a) (hy : y < OrdinalNotation.omegaPow a) :
    redOrd x y < OrdinalNotation.omegaPow a := by
  have h₁ : OrdinalNotation.nadd x y < OrdinalNotation.omegaPow a :=
    OrdinalNotation.nadd_lt_omegaPow hx hy
  exact OrdinalNotation.nadd_lt_omegaPow h₁ h₁

/-! ### The tower and the successor -/

/-- The `n`-fold tower `ω ^ ω ^ ⋯ ^ α`.

The recursion pushes the new exponentiation *inside*, which is what makes the
cut-elimination induction definitional: peeling one level of rank turns
`α` into `ω ^ α` and leaves `n` levels still to peel. -/
def omegaTower : ℕ → O → O
  | 0, α => α
  | (n + 1), α => omegaTower n (OrdinalNotation.omegaPow α)

@[simp] theorem omegaTower_zero (α : O) : omegaTower 0 α = α := rfl

@[simp] theorem omegaTower_succ (n : ℕ) (α : O) :
    omegaTower (n + 1) α = omegaTower n (OrdinalNotation.omegaPow α) := rfl

/-- Successor, built from the natural sum rather than from ordinal addition. -/
def succ (a : O) : O := OrdinalNotation.nadd a OrdinalNotation.one

theorem lt_succ (a : O) : a < succ a := OrdinalNotation.lt_nadd_one a

theorem le_succ (a : O) : a ≤ succ a := le_of_lt (lt_succ a)

theorem lt_succ_of_le {a b : O} (h : a ≤ b) : a < succ b := lt_of_le_of_lt h (lt_succ b)

end OrdinalNotation

/-! ### `NONote` as an instance

Every field is the definition or lemma already proved in `Ordinal/NONatSum.lean`
and `Ordinal/OmegaPow.lean`; nothing is re-proved. -/

instance : OrdinalNotation _root_.NONote where
  nadd := NONote.nadd
  nadd_comm := NONote.nadd_comm
  nadd_assoc := NONote.nadd_assoc
  le_nadd_left := NONote.le_nadd_left
  nadd_lt_nadd_left := NONote.nadd_lt_nadd_left
  omegaPow := NONote.omegaPow
  omegaPow_lt_omegaPow := NONote.omegaPow_lt_omegaPow
  nadd_lt_omegaPow := NONote.nadd_lt_omegaPow
  one := NONote.one
  lt_nadd_one := NONote.lt_succ
  one_le_omegaPow := NONote.one_le_omegaPow
  ofNat := _root_.NONote.ofNat
  ofNat_lt_ofNat := NONote.ofNat_lt_ofNat

namespace OrdinalNotation

/-! ### The bridge to the `NONote` spellings

Every generic operation is *definitionally* the `NONote` one it was abstracted
from, but `rw` and `simp` compare at reducible transparency and will not cross
on their own.  These `rfl` lemmas are what keeps the `Gentzen/` files, which
still write `NONote.nadd`, `NONote.redOrd` and friends, working unchanged
against the now-generic calculus. -/

@[simp] theorem NONote_nadd (a b : _root_.NONote) :
    OrdinalNotation.nadd a b = NONote.nadd a b := rfl

@[simp] theorem NONote_omegaPow (a : _root_.NONote) :
    OrdinalNotation.omegaPow a = NONote.omegaPow a := rfl

@[simp] theorem NONote_one : (OrdinalNotation.one : _root_.NONote) = NONote.one := rfl

@[simp] theorem NONote_ofNat (n : ℕ) :
    (OrdinalNotation.ofNat n : _root_.NONote) = _root_.NONote.ofNat n := rfl

@[simp] theorem NONote_sq (a : _root_.NONote) : sq a = NONote.sq a := rfl

@[simp] theorem NONote_mid (a b c : _root_.NONote) : mid a b c = NONote.mid a b c := rfl

@[simp] theorem NONote_redOrd (a b : _root_.NONote) : redOrd a b = NONote.redOrd a b := rfl

@[simp] theorem NONote_succ (a : _root_.NONote) : succ a = NONote.succ a := rfl

@[simp] theorem NONote_omegaTower (n : ℕ) (a : _root_.NONote) :
    omegaTower n a = NONote.omegaTower n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact ih (NONote.omegaPow a)

end OrdinalNotation

end OrdinalAnalysis
