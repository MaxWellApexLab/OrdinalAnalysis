/-
  The cofinality lemma for the countable part of the ϑ-notation.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Definition 3.1 (clause (ii') of the order) and §5
  (the function `ω(α)` for exponentiation with base `ω`).

  Write `ω₀(α) = α` and `ω_{n+1}(α) = ω(ω_n(α))`.  Every notation lies below some
  `ω_n(Ω + 1)`, and every notation below `Ω` lies below some `ϑ(ω_n(Ω + 1))`.  Both are proved
  by induction on the length.  The terms `ω_n(Ω + 1)` have no coefficients
  (`E(ω_n(Ω + 1)) = ∅`), so that clause (ii') makes `ϑ(ω_n(Ω + 1))` strictly increasing
  in `n`, and in the case `ϑ ξ` of the second induction it suffices that `ξ` lies below
  some `ω_n(Ω + 1)` and that the coefficients of `ξ`, which are shorter than `ϑ ξ`, lie
  below some `ϑ(ω_n(Ω + 1))`.  Hence the terms `ϑ(ω_n(Ω + 1))` are cofinal in the
  notations below `Ω`: the Bachmann–Howard ordinal is their supremum.
-/
import OrdinalAnalysis.Ordinal.Theta.Hull

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaNote

open ThetaTerm

/-- The tower `ω₀(α) = α`, `ω_{n+1}(α) = ω(ω_n(α))`. -/
def omegaTower : ℕ → ThetaNote → ThetaNote
  | 0, x => x
  | n + 1, x => omegaPow (omegaTower n x)

@[simp] theorem omegaTower_zero (x : ThetaNote) : omegaTower 0 x = x := rfl

@[simp] theorem omegaTower_succ (n : ℕ) (x : ThetaNote) :
    omegaTower (n + 1) x = omegaPow (omegaTower n x) := rfl

theorem Omega_lt_Omega_add_one : Omega < Omega + one := by
  have h := add_lt_add_left Omega zero_lt_one
  rwa [add_zero] at h

/-- `E(ω_n(Ω + 1)) = ∅`. -/
theorem Ehull_omegaTower_hull (n : ℕ) : Ehull (omegaTower n (Omega + one)) = ∅ := by
  induction n with
  | zero =>
    apply Set.eq_empty_of_subset_empty
    refine (Ehull_add_subset_hull Omega one).trans ?_
    simp
  | succ n ih => rw [omegaTower_succ, Ehull_omegaPow_hull, ih]

theorem E_omegaTower_hull (n : ℕ) : E (omegaTower n (Omega + one)).1 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro g hg
  have hmem : (⟨g, (omegaTower n (Omega + one)).2.of_mem_E hg⟩ : ThetaNote) ∈
      Ehull (omegaTower n (Omega + one)) := hg
  rw [Ehull_omegaTower_hull] at hmem
  exact hmem

theorem omegaTower_lt_omegaTower_succ (n : ℕ) :
    omegaTower n (Omega + one) < omegaTower (n + 1) (Omega + one) := by
  induction n with
  | zero =>
    rw [omegaTower_succ, omegaTower_zero, lt_omegaPow_iff, entries_add]
    intro e he
    rcases mem_addL he with he | he
    · rw [entries_Omega, List.mem_singleton] at he
      rw [he]
      exact Omega_lt_Omega_add_one
    · rw [entries_one, List.mem_singleton] at he
      rw [he]
      exact lt_trans (nil_lt_Omega) Omega_lt_Omega_add_one
  | succ n ih => exact omegaPow_lt_omegaPow ih

theorem omegaTower_lt_omegaTower {m n : ℕ} (h : m < n) :
    omegaTower m (Omega + one) < omegaTower n (Omega + one) := by
  induction h with
  | refl => exact omegaTower_lt_omegaTower_succ m
  | step _ ih => exact lt_trans ih (omegaTower_lt_omegaTower_succ _)

theorem omegaTower_le_omegaTower {m n : ℕ} (h : m ≤ n) :
    omegaTower m (Omega + one) ≤ omegaTower n (Omega + one) := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (omegaTower_lt_omegaTower h)
  · exact le_rfl

/-- `ϑ(ω_m(Ω + 1)) ≺ ϑ(ω_n(Ω + 1))` for `m < n`, by clause (ii') and `E(ω_m(Ω + 1)) = ∅`. -/
theorem theta_omegaTower_lt_theta_omegaTower {m n : ℕ} (h : m < n) :
    theta (omegaTower m (Omega + one)) < theta (omegaTower n (Omega + one)) :=
  theta_lt_theta_of_lt (omegaTower_lt_omegaTower h) (by simp [E_omegaTower_hull])

theorem theta_omegaTower_le_theta_omegaTower {m n : ℕ} (h : m ≤ n) :
    theta (omegaTower m (Omega + one)) ≤ theta (omegaTower n (Omega + one)) := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (theta_omegaTower_lt_theta_omegaTower h)
  · exact le_rfl

/-- A common bound for finitely many terms, for a property monotone in the bound. -/
theorem exists_bound_hull {p : ThetaTerm → ℕ → Prop}
    (hp : ∀ t m n, m ≤ n → p t m → p t n) :
    ∀ (xs : List ThetaTerm), (∀ x ∈ xs, ∃ n, p x n) → ∃ N, ∀ x ∈ xs, p x N
  | [], _ => ⟨0, by simp⟩
  | y :: ys, h => by
    obtain ⟨n, hn⟩ := h y List.mem_cons_self
    obtain ⟨N, hN⟩ := exists_bound_hull hp ys fun x hx => h x (List.mem_cons_of_mem y hx)
    refine ⟨max n N, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp x n _ (le_max_left n N) hn
    · exact hp x N _ (le_max_right n N) (hN x hx)

/-- Every normal term is below some `ω_n(Ω + 1)`, by induction on the length. -/
theorem exists_lt_omegaTower_aux : ∀ (t : ThetaTerm), NF t →
    ∃ n, t < (omegaTower n (Omega + one)).1
  | ThetaTerm.Omega, _ => ⟨0, Omega_lt_Omega_add_one⟩
  | ThetaTerm.theta s, _ => ⟨0, lt_trans (ThetaTerm.theta_lt_Omega s) Omega_lt_Omega_add_one⟩
  | ThetaTerm.sum xs, ht => by
    obtain ⟨N, hN⟩ := exists_bound_hull
      (p := fun x n => x < (omegaTower n (Omega + one)).1)
      (fun _ _ _ hmn h => lt_of_lt_of_le h (omegaTower_le_omegaTower hmn)) xs
      fun x hx => exists_lt_omegaTower_aux x (ht.of_mem hx)
    refine ⟨N + 1, ?_⟩
    have key : (⟨sum xs, ht⟩ : ThetaNote) < omegaPow (omegaTower N (Omega + one)) :=
      lt_omegaPow_iff.mpr fun e he => hN e he
    exact key
termination_by t => l t
decreasing_by exact l_lt_of_mem hx

/-- Every notation is below some `ω_n(Ω + 1)`. -/
theorem exists_lt_omegaTower (a : ThetaNote) : ∃ n, a < omegaTower n (Omega + one) :=
  exists_lt_omegaTower_aux a.1 a.2

/-- The cofinality lemma on normal terms, by induction on the length. -/
theorem exists_lt_theta_omegaTower_aux : ∀ (t : ThetaTerm), NF t → t < ThetaTerm.Omega →
    ∃ n, t < ThetaTerm.theta (omegaTower n (Omega + one)).1
  | ThetaTerm.Omega, _, h => absurd h not_Omega_lt_Omega
  | ThetaTerm.theta s, ht, _ => by
    have hs : NF s := (nf_theta_iff s).mp ht
    obtain ⟨n₀, hn₀⟩ := exists_lt_omegaTower_aux s hs
    obtain ⟨N, hN⟩ := exists_bound_hull
      (p := fun x n => x < ThetaTerm.theta (omegaTower n (Omega + one)).1)
      (fun _ _ _ hmn h => lt_of_lt_of_le h (theta_omegaTower_le_theta_omegaTower hmn)) (E s)
      fun g hg => exists_lt_theta_omegaTower_aux g (hs.of_mem_E hg) (lt_Omega_of_mem_E hg)
    refine ⟨max n₀ N, theta_lt_theta_of_lt ?_ fun g hg => ?_⟩
    · exact lt_of_lt_of_le hn₀ (omegaTower_le_omegaTower (le_max_left n₀ N))
    · exact lt_of_lt_of_le (hN g hg) (theta_omegaTower_le_theta_omegaTower (le_max_right n₀ N))
  | ThetaTerm.sum [], _, _ => ⟨0, nil_lt_theta _⟩
  | ThetaTerm.sum (x :: xs), ht, h => by
    obtain ⟨n, hn⟩ := exists_lt_theta_omegaTower_aux x (ht.of_mem List.mem_cons_self)
      ((cons_lt_Omega_iff x xs).mp h)
    exact ⟨n, (cons_lt_theta_iff _ _ _).mpr hn⟩
termination_by t => l t
decreasing_by
  · have := l_le_of_mem_E hg; simp; omega
  · simp; omega

/-- The cofinality lemma: every notation below `Ω` is below some `ϑ(ω_n(Ω + 1))`. -/
theorem exists_lt_theta_omegaTower {a : ThetaNote} (ha : a < Omega) :
    ∃ n, a < theta (omegaTower n (Omega + one)) :=
  exists_lt_theta_omegaTower_aux a.1 a.2 ha

end ThetaNote

end OrdinalAnalysis
