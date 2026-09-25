/-
  Course-of-values tables for the multi-level ϑ-notation: reuses `ID1.Internal`'s generic
  `covVal`/`covTable` machinery verbatim (it is already generic in the position type `V`, not
  specific to the one-level notation), and adds the *tag* combinators needed to fold the extra
  level parameter of the ϑ_k-ϑ_k order clause into a single position space.

  **Why a new combinator is needed at all.**  ID1's comparison table packs `(lt, all, ex)` into
  one value at position `⟪c1, c2⟫`: `all c1 c2 = ∀ g ∈ E(c1), g ≺ c2` and
  `ex c1 c2 = ∃ g ∈ E(c2), c1 ≼ g` recurse structurally on `c1` resp. `c2`, the other coordinate
  fixed, so they fit the same pair-order recursion as `lt`.  Here `E_k` carries an extra level
  `k`, and the ϑ_k-ϑ_k clause needs `all_k`/`ex_k` for the *specific* `k` read off the two codes
  (a tagged-pair alternative was tried and fails: tagging the *whole* pair with an outer
  level coordinate breaks the pairwise-monotonicity lemmas, because `Nat.pair`'s case split
  depends on both coordinates' relative sizes at once).

  The fix tags a *single* coordinate at a time, by parity: `tagP c` (even) is "plain code `c`",
  `tagL i c` (odd) is "code `c` at level `i`".  A combined step function can then dispatch on the
  parity of each coordinate of its position, and every recursive read needed by the ϑ_k-ϑ_k
  clause becomes a one-lemma application of `pair_lt_pair_left`/`pair_lt_pair_right`/
  `le_pair_right`, exactly as in ID1: two *equal* untagged coordinates are unaffected by
  `pair_lt_pair_left/right`, and `tagP c < tagL i c` (`le_pair_right`), `tagL i c < tagP (tcTheta i c)`
  (`le_pair_right` again, chained through the `+1` of `tcTheta`) give the two "leveled reads from
  a plain position" directions.
-/
import OrdinalAnalysis.ID1.Internal.CovTable

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.ID1.Internal (bor band beq covVal covTable covVal_unfold covVal_zero
  covVal_succ covValDef covTableDef)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Parity tags on table positions -/

/-- The "plain code `c`" tag: an even position coordinate. -/
noncomputable def tagP (c : V) : V := c + c

/-- The "code `c` at level `i`" tag: an odd position coordinate. -/
noncomputable def tagL (i c : V) : V := ⟪i, c⟫ + ⟪i, c⟫ + 1

def tagPDef : 𝚺₀.Semisentence 2 := .mkSigma “y c. y = c + c”

def tagLDef : 𝚺₁.Semisentence 3 := .mkSigma “y i c. ∃ p, !pairDef p i c ∧ y = p + p + 1”

instance tagP_defined : 𝚺₀-Function₁ (tagP : V → V) via tagPDef := .mk fun v ↦ by
  simp [tagPDef, tagP]

instance tagL_defined : 𝚺₁-Function₂ (tagL : V → V → V) via tagLDef := .mk fun v ↦ by
  simp [tagLDef, tagL, pair_defined.iff]

instance tagP_definable : 𝚺₀-Function₁ (tagP : V → V) := tagP_defined.to_definable
instance tagL_definable : 𝚺₁-Function₂ (tagL : V → V → V) := tagL_defined.to_definable
instance tagP_definable' (Γ) : Γ-Function₁ (tagP : V → V) := tagP_definable.of_zero
instance tagL_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (tagL : V → V → V) :=
  tagL_definable.of_sigmaOne

/-! ### The basic order facts about the tags -/

@[simp] lemma tagP_lt_tagP {a b : V} (h : a < b) : tagP a < tagP b := by
  unfold tagP; exact add_lt_add h h

@[simp] lemma tagP_le_tagP {a b : V} (h : a ≤ b) : tagP a ≤ tagP b := by
  unfold tagP; exact add_le_add h h

@[simp] lemma tagP_inj {a b : V} : tagP a = tagP b ↔ a = b := by
  unfold tagP
  constructor
  · intro h
    rcases lt_trichotomy a b with hab | hab | hab
    · exact absurd h (ne_of_lt (add_lt_add hab hab))
    · exact hab
    · exact absurd h.symm (ne_of_lt (add_lt_add hab hab))
  · rintro rfl; rfl

@[simp] lemma tagL_lt_tagL_of_lt_right (i : V) {a b : V} (h : a < b) : tagL i a < tagL i b := by
  have hp := pair_lt_pair_right i h
  unfold tagL
  gcongr

lemma tagL_inj {i a : V} {b : V} (h : tagL i a = tagL i b) : a = b := by
  have h1 : (⟪i, a⟫ : V) + ⟪i, a⟫ = ⟪i, b⟫ + ⟪i, b⟫ := add_right_cancel h
  have h2 : (⟪i, a⟫ : V) = ⟪i, b⟫ := by
    rcases lt_trichotomy (⟪i, a⟫ : V) ⟪i, b⟫ with hab | hab | hab
    · exact absurd h1 (ne_of_lt (add_lt_add hab hab))
    · exact hab
    · exact absurd h1.symm (ne_of_lt (add_lt_add hab hab))
  have h3 : π₂ (⟪i, a⟫ : V) = π₂ (⟪i, b⟫ : V) := by rw [h2]
  simpa using h3

/-- **The key crossing lemma, direction 1**: the plain code `c` sits below `c` tagged at any
level `i` — used to read `lt` from an `all_i`/`ex_i` base case. -/
lemma tagP_lt_tagL (i c : V) : tagP c < tagL i c := by
  have h := le_pair_right i c
  unfold tagP tagL
  have h2 : c + c ≤ (⟪i, c⟫ : V) + ⟪i, c⟫ := by gcongr
  exact lt_of_le_of_lt h2 (lt_add_one _)

/-- **The key crossing lemma, direction 2**: `c` tagged at level `i` sits strictly below the
plain code of the `tcTheta`-shaped term built from `⟪1, ⟪i, c⟫⟫ + 1` — used to read `all_i`/
`ex_i` from the ϑ_i-ϑ_i clause of `lt`. -/
lemma tagL_lt_tagP_succ_pair (i c : V) : tagL i c < tagP (⟪1, ⟪i, c⟫⟫ + 1 : V) := by
  have h1 : (⟪i, c⟫ : V) ≤ ⟪1, ⟪i, c⟫⟫ := le_pair_right 1 ⟪i, c⟫
  set A : V := ⟪1, ⟪i, c⟫⟫ with hA
  unfold tagP tagL
  have h2 : (⟪i, c⟫ : V) + ⟪i, c⟫ + 1 ≤ A + A + 1 := by gcongr
  have h3 : A + A + 1 < A + 1 + (A + 1) := by
    have e : A + 1 + (A + 1) = A + A + 1 + 1 := by
      rw [add_assoc A 1 (A + 1), ← add_assoc 1 A 1, add_comm 1 A, add_assoc A A 1,
        add_assoc A (A + 1) 1]
    rw [e]; exact lt_add_one _
  exact lt_of_le_of_lt h2 h3

end OrdinalAnalysis.IDn.Internal
