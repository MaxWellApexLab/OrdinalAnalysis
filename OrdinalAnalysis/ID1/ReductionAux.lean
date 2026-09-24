/-
  Ordinal arithmetic for the reduction and cut elimination lemmas of `ID₁^∞`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Definition 3.1, §5 (the functions `α + β` and
  `ω(α)`), Exercise 7.1 (b) (the height `α + β`) and (c) (the height `ω(α)`, the rank
  `ρ + 1`), and Corollary 7.2 (the towers `ω_n(β)`).

  The facts proved here:

    * `α ≼ α + β` (`le_self_add_red`), used for the heights `α + β` of Exercise 7.1 (b);
    * `α ≺ β + 1` implies `α ≼ β` (`le_of_lt_succ_red`): a cut formula of rank `≺ ρ + 1`
      has rank `≺ ρ` or rank `ρ`, as in Exercise 7.1 (c);
    * `α ≼ ω(α)` (`le_omegaPow_red`), for the side conditions of the clauses at the height
      `ω(α)` of Exercise 7.1 (c);
    * the ordinal sum of two numerals is the numeral of their sum, and the tower laws `ω_{n+1}(α) = ω_n(ω(α))`,
      `ω_m(ω_n(α)) = ω_{m+n}(α)` and the strict monotonicity of `ω_n`, used in
      Corollary 7.2.
-/
import OrdinalAnalysis.ID1.Collapsing
import OrdinalAnalysis.Ordinal.Theta.HullCofinal

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaTerm

/-- If `⟨xs⟩ ≺ ⟨ys, 0⟩` then not `⟨ys⟩ ≺ ⟨xs⟩`: nothing lies strictly between a sum and its
successor. -/
theorem not_lt_of_lt_append_zero_red : ∀ (ys xs : List ThetaTerm),
    sum xs < sum (ys ++ [sum []]) → ¬ sum ys < sum xs
  | [], [], _, h2 => not_nil_lt_nil h2
  | [], x :: xs, h1, _ => by
    rcases (cons_lt_cons_iff x (sum []) xs []).mp h1 with h | ⟨-, h⟩
    · exact not_lt_nil x h
    · exact not_lt_nil _ h
  | _ :: _, [], _, h2 => not_cons_lt_nil _ _ h2
  | y :: ys, x :: xs, h1, h2 => by
    rw [List.cons_append] at h1
    rcases (cons_lt_cons_iff x y xs _).mp h1 with h | ⟨rfl, h⟩
    · rcases (cons_lt_cons_iff y x ys xs).mp h2 with h' | ⟨rfl, -⟩
      · exact lt_asymm' h h'
      · exact lt_irrefl' _ h
    · rcases (cons_lt_cons_iff x x ys xs).mp h2 with h' | ⟨-, h'⟩
      · exact lt_irrefl' _ h'
      · exact not_lt_of_lt_append_zero_red ys xs h h'

end ThetaTerm

namespace ThetaNote

open ThetaTerm

/-- `α ≼ α + β`. -/
theorem le_self_add_red (a b : ThetaNote) : a ≤ a + b := by
  have h := add_le_add_left a (bot_le : (⊥ : ThetaNote) ≤ b)
  rwa [bot_eq_zero, add_zero] at h

/-- `α ≺ β + 1` gives `α ≼ β`. -/
theorem le_of_lt_succ_red {a b : ThetaNote} (h : a < succ b) : a ≤ b := by
  refine le_of_not_gt fun hba => ?_
  rw [lt_iff_entries, succ, entries_nadd_one] at h
  exact not_lt_of_lt_append_zero_red _ _ h (lt_iff_entries.mp hba)

/-- `α ≺ β + 1` gives `α ≼ β`, with `β + 1` the ordinal sum. -/
theorem le_of_lt_add_one_red {a b : ThetaNote} (h : a < b + one) : a ≤ b := by
  rw [add_one_eq_succ] at h
  exact le_of_lt_succ_red h

/-- `α ≼ ω(α)`. -/
theorem le_omegaPow_red (a : ThetaNote) : a ≤ omegaPow a := by
  by_cases hp : IsPrin a.1
  · exact le_of_eq (omegaPow_eq_self_iff.mpr hp).symm
  · refine le_of_lt (lt_omegaPow_iff.mpr ?_)
    obtain ⟨t, ht⟩ := a
    cases t with
    | Omega => exact absurd trivial hp
    | theta _ => exact absurd trivial hp
    | sum xs =>
      intro e he
      cases xs with
      | nil => exact absurd he List.not_mem_nil
      | cons x xs =>
        have hs : SortedDesc (x :: xs) := sorted_entries ⟨sum (x :: xs), ht⟩
        have hex : e ≤ x := by
          rcases List.mem_cons.mp he with rfl | he
          · exact le_refl' _
          · exact List.rel_of_pairwise_cons hs he
        exact lt_of_le_of_lt' hex (lt_sum_cons_self x xs)

/-- `ω(α₀) + ω(α₀) ≺ ω(α)` for `α₀ ≺ α`: the height of a reduced cut in Exercise 7.1 (c). -/
theorem omegaPow_add_omegaPow_lt_red {a b : ThetaNote} (h : a < b) :
    omegaPow a + omegaPow a < omegaPow b :=
  add_lt_omegaPow (omegaPow_lt_omegaPow h) (omegaPow_lt_omegaPow h)

/-- On the numerals the ordinal sum is the sum of natural numbers. -/
theorem ofNat_add_ofNat_red (m : ℕ) : ∀ n : ℕ, ofNat m + ofNat n = ofNat (m + n)
  | 0 => by rw [ofNat_zero, add_zero, Nat.add_zero]
  | n + 1 => by
    rw [ofNat_succ, ← add_one_eq_succ, ← add_assoc, ofNat_add_ofNat_red m n, add_one_eq_succ,
      ← ofNat_succ, Nat.add_assoc]

/-- `ρ + (n + 1) = (ρ + n) + 1`. -/
theorem add_ofNat_succ_red (r : ThetaNote) (n : ℕ) :
    r + ofNat (n + 1) = r + ofNat n + one := by
  rw [add_assoc, ← ofNat_one, ofNat_add_ofNat_red]

/-- `ω_{n+1}(α) = ω_n(ω(α))`. -/
theorem omegaTower_succ_red : ∀ (n : ℕ) (x : ThetaNote),
    omegaTower (n + 1) x = omegaTower n (omegaPow x)
  | 0, _ => rfl
  | n + 1, x => by
    rw [omegaTower_succ, omegaTower_succ_red n x, omegaTower_succ]

/-- `ω_m(ω_n(α)) = ω_{m+n}(α)`. -/
theorem omegaTower_omegaTower_red : ∀ (m n : ℕ) (x : ThetaNote),
    omegaTower m (omegaTower n x) = omegaTower (m + n) x
  | 0, n, x => by rw [omegaTower_zero, Nat.zero_add]
  | m + 1, n, x => by
    rw [omegaTower_succ, omegaTower_omegaTower_red m n x, Nat.add_right_comm, omegaTower_succ]

/-- `ω_n` is strictly increasing. -/
theorem omegaTower_lt_omegaTower_red {x y : ThetaNote} (h : x < y) :
    ∀ n : ℕ, omegaTower n x < omegaTower n y
  | 0 => h
  | n + 1 => omegaPow_lt_omegaPow (omegaTower_lt_omegaTower_red h n)

/-- `ω_n` preserves membership in a nice operator. -/
theorem Nice.omegaTower_mem_red {H : Set ThetaNote → Set ThetaNote} (hH : Nice H)
    {X : Set ThetaNote} {x : ThetaNote} (hx : x ∈ H X) : ∀ n : ℕ, omegaTower n x ∈ H X
  | 0 => hx
  | n + 1 => hH.omegaPow_mem (Nice.omegaTower_mem_red hH hx n)

end ThetaNote

end OrdinalAnalysis
