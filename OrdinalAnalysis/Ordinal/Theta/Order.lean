/-
  The ϑ-order is a linear order.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Definition 3.1 and Exercise 3.2.  Freund leaves the
  linearity of `≺` as an exercise (Exercise 3.2(b)); the proof given here works on all raw
  terms (the set `ϑ⁰(ε_{Ω+1})` of Freund), so that normal forms are needed only for the
  finer facts of Exercise 3.2(c)–(e).

  * Transitivity (`lt_trans'`) is proved first, by induction on `l α + l β + l γ`.  After
    the observation that a sum `⟨⟩` is below every other term and above none, every term
    is either principal (`Ω` or `ϑ δ`) or a non-empty sum, and the clauses of
    Definition 3.1 reduce each of the eight shape combinations to the induction hypothesis
    for shorter terms.  The only case with content is `ϑ α ≺ ϑ β ≺ ϑ γ`:
    - if `ϑ β ≼ δ` for some `δ ∈ E(γ)`, then `ϑ α ≺ δ` by induction, since `l δ ≤ l γ`;
    - if `β ≺ γ` and `E(β) ≺* ϑ γ`, and `ϑ α ≼ δ` for some `δ ∈ E(β)`, then `ϑ α ≺ ϑ γ`
      by induction applied to `ϑ α ≼ δ ≺ ϑ γ`, since `l δ ≤ l β`;
    - if `β ≺ γ`, `E(β) ≺* ϑ γ`, `α ≺ β` and `E(α) ≺* ϑ β`, then `α ≺ γ` by induction,
      and each `δ ∈ E(α)` satisfies `δ ≺ ϑ β ≺ ϑ γ`, hence `δ ≺ ϑ γ` by induction, since
      `l δ ≤ l α`.
  * `E(α) ≺* ϑ α` (Exercise 3.2(a)) is immediate from the third clause for `ϑ δ ≺ ϑ α`.
  * Irreflexivity (`lt_irrefl'`) follows by induction on `l α`, as Freund's hint suggests:
    `ϑ α ≺ ϑ α` would give `α ≺ α` or `ϑ α ≼ δ` for some `δ ∈ E(α)`; in the second case
    `δ ≺ ϑ α` and transitivity give `δ ≺ δ`, with `δ` shorter than `ϑ α`.
  * Trichotomy (`lt_trichotomy'`) is proved by induction on `l α + l β`; for two ϑ-terms
    with `α ≺ β`, either `E(α) ≺* ϑ β` or some `δ ∈ E(α)` has `ϑ β ≼ δ`, and then
    `ϑ β ≺ ϑ α` by the third clause.

  This yields `LinearOrder ThetaTerm` and, by restriction, `LinearOrder ThetaNote`.  The file
  ends with Exercise 3.2(c)–(e) for normal terms and the basic compatibility lemmas.
-/
import OrdinalAnalysis.Ordinal.Theta.Basic
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.FinRange
import Mathlib.Order.Basic

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaTerm

/-! ### Preliminaries -/

/-- Exercise 3.2(a): `E(α) ≺* ϑ α`. -/
theorem lt_theta_of_mem_E {a g : ThetaTerm} (h : g ∈ E a) : g < theta a := by
  obtain ⟨d, rfl⟩ := exists_eq_theta_of_mem_E h
  exact (theta_lt_theta_iff d a).mpr (Or.inr ⟨theta d, h, le_refl' _⟩)

/-- No term is below `⟨⟩`. -/
theorem not_lt_nil (a : ThetaTerm) : ¬ a < sum [] := by
  cases a with
  | Omega => exact not_Omega_lt_nil
  | theta a => exact not_theta_lt_nil a
  | sum xs =>
    cases xs with
    | nil => exact not_nil_lt_nil
    | cons x xs => exact not_cons_lt_nil x xs

/-- `⟨⟩` is below every other term. -/
theorem nil_lt_of_ne {a : ThetaTerm} (h : a ≠ sum []) : sum [] < a := by
  cases a with
  | Omega => exact nil_lt_Omega
  | theta a => exact nil_lt_theta a
  | sum xs =>
    cases xs with
    | nil => exact absurd rfl h
    | cons x xs => exact nil_lt_cons x xs

theorem nil_le (a : ThetaTerm) : sum [] ≤ a := by
  by_cases h : a = sum []
  · exact Or.inr h.symm
  · exact Or.inl (nil_lt_of_ne h)

/-- Every term is principal, `⟨⟩`, or a non-empty sum. -/
theorem shape (a : ThetaTerm) :
    IsPrin a ∨ a = sum [] ∨ ∃ x xs, a = sum (x :: xs) := by
  cases a with
  | Omega => exact Or.inl trivial
  | theta _ => exact Or.inl trivial
  | sum xs =>
    cases xs with
    | nil => exact Or.inr (Or.inl rfl)
    | cons x xs => exact Or.inr (Or.inr ⟨x, xs, rfl⟩)

theorem not_Omega_lt_prin {p : ThetaTerm} (hp : IsPrin p) : ¬ Omega < p := by
  cases p with
  | Omega => exact not_Omega_lt_Omega
  | theta b => exact not_Omega_lt_theta b
  | sum _ => exact absurd hp id

/-! ### Transitivity -/

/-- Transitivity, by induction on `n ≥ l α + l β + l γ`. -/
theorem lt_trans_aux (n : ℕ) :
    ∀ a b c : ThetaTerm, l a + l b + l c ≤ n → a < b → b < c → a < c := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b c hn hab hbc
  -- the induction hypothesis for shorter triples, and its `≼` variants
  have T : ∀ {x y z : ThetaTerm}, l x + l y + l z < l a + l b + l c →
      x < y → y < z → x < z :=
    fun h h1 h2 => ih _ (by omega) _ _ _ le_rfl h1 h2
  have TL : ∀ {x y z : ThetaTerm}, l x + l y + l z < l a + l b + l c →
      x ≤ y → y < z → x < z := by
    intro x y z h h1 h2
    rcases h1 with h1 | rfl
    · exact T h h1 h2
    · exact h2
  have TR : ∀ {x y z : ThetaTerm}, l x + l y + l z < l a + l b + l c →
      x < y → y ≤ z → x < z := by
    intro x y z h h1 h2
    rcases h2 with h2 | rfl
    · exact T h h1 h2
    · exact h1
  rcases shape a with ha | rfl | ⟨x, xs, rfl⟩ <;>
  rcases shape b with hb | rfl | ⟨y, ys, rfl⟩ <;>
  rcases shape c with hc | rfl | ⟨z, zs, rfl⟩
  -- every case in which some term is `⟨⟩`
  all_goals first
    | exact absurd hab (not_lt_nil _)
    | exact absurd hbc (not_lt_nil _)
    | exact nil_lt_of_ne (fun h => not_lt_nil _ (h ▸ hbc))
    | skip
  -- principal, principal, principal
  · cases a with
    | sum _ => exact absurd ha id
    | Omega => exact absurd hab (not_Omega_lt_prin hb)
    | theta a =>
    cases b with
    | sum _ => exact absurd hb id
    | Omega => exact absurd hbc (not_Omega_lt_prin hc)
    | theta b =>
    cases c with
    | sum _ => exact absurd hc id
    | Omega => exact theta_lt_Omega a
    | theta c =>
    have hlab := hab
    rw [theta_lt_theta_iff] at hab hbc
    rw [theta_lt_theta_iff]
    rcases hbc with ⟨hbc1, hbc2⟩ | ⟨d, hd, hbd⟩
    · rcases hab with ⟨hab1, hab2⟩ | ⟨d, hd, had⟩
      · refine Or.inl ⟨T (by simp; omega) hab1 hbc1, fun g hg => ?_⟩
        have := l_le_of_mem_E hg
        have hbc' : theta b < theta c :=
          (theta_lt_theta_iff b c).mpr (Or.inl ⟨hbc1, hbc2⟩)
        exact T (by simp; omega) (hab2 g hg) hbc'
      · have := l_le_of_mem_E hd
        exact (theta_lt_theta_iff a c).mp (TL (by simp; omega) had (hbc2 d hd))
    · have := l_le_of_mem_E hd
      exact Or.inr ⟨d, hd, Or.inl (TR (by simp; omega) hlab hbd)⟩
  -- principal, principal, sum
  · rw [prin_lt_cons_iff ha]
    rw [prin_lt_cons_iff hb] at hbc
    exact Or.inl (TR (by simp; omega) hab hbc)
  -- principal, sum, principal
  · rw [prin_lt_cons_iff ha] at hab
    rw [cons_lt_prin_iff hc] at hbc
    exact TL (by simp; omega) hab hbc
  -- principal, sum, sum
  · rw [prin_lt_cons_iff ha] at hab
    rw [prin_lt_cons_iff ha]
    rcases (cons_lt_cons_iff y z ys zs).mp hbc with h | ⟨rfl, _⟩
    · exact Or.inl (TL (by simp; omega) hab h)
    · exact hab
  -- sum, principal, principal
  · rw [cons_lt_prin_iff hb] at hab
    rw [cons_lt_prin_iff hc]
    exact T (by simp; omega) hab hbc
  -- sum, principal, sum
  · rw [cons_lt_prin_iff hb] at hab
    rw [prin_lt_cons_iff hb] at hbc
    exact (cons_lt_cons_iff x z xs zs).mpr (Or.inl (TR (by simp; omega) hab hbc))
  -- sum, sum, principal
  · rw [cons_lt_prin_iff hc] at hbc
    rw [cons_lt_prin_iff hc]
    rcases (cons_lt_cons_iff x y xs ys).mp hab with h | ⟨rfl, _⟩
    · exact T (by simp; omega) h hbc
    · exact hbc
  -- sum, sum, sum
  · rw [cons_lt_cons_iff] at hab hbc ⊢
    rcases hab with h1 | ⟨rfl, h1⟩ <;> rcases hbc with h2 | ⟨rfl, h2⟩
    · exact Or.inl (T (by simp; omega) h1 h2)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr ⟨rfl, T (by simp; omega) h1 h2⟩

/-- Transitivity of the ϑ-order (Freund, Exercise 3.2(b)). -/
theorem lt_trans' {a b c : ThetaTerm} (hab : a < b) (hbc : b < c) : a < c :=
  lt_trans_aux _ a b c le_rfl hab hbc

theorem lt_of_le_of_lt' {a b c : ThetaTerm} (hab : a ≤ b) (hbc : b < c) : a < c := by
  rcases hab with hab | rfl
  · exact lt_trans' hab hbc
  · exact hbc

theorem lt_of_lt_of_le' {a b c : ThetaTerm} (hab : a < b) (hbc : b ≤ c) : a < c := by
  rcases hbc with hbc | rfl
  · exact lt_trans' hab hbc
  · exact hab

theorem le_trans' {a b c : ThetaTerm} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rcases hab with hab | rfl
  · exact Or.inl (lt_of_lt_of_le' hab hbc)
  · exact hbc

/-! ### Irreflexivity -/

theorem lt_irrefl_aux (n : ℕ) : ∀ a : ThetaTerm, l a ≤ n → ¬ a < a := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn h
  cases a with
  | Omega => exact not_Omega_lt_Omega h
  | theta a =>
    rcases (theta_lt_theta_iff a a).mp h with ⟨h1, _⟩ | ⟨g, hg, h1⟩
    · simp at hn
      exact ih (l a) (by omega) a le_rfl h1
    · have hl := l_le_of_mem_E hg
      simp at hn
      rcases h1 with h1 | rfl
      · exact ih (l g) (by omega) g le_rfl (lt_trans' (lt_theta_of_mem_E hg) h1)
      · simp at hl; omega
  | sum xs =>
    cases xs with
    | nil => exact not_nil_lt_nil h
    | cons x xs =>
      simp at hn
      rcases (cons_lt_cons_iff x x xs xs).mp h with h1 | ⟨_, h1⟩
      · exact ih (l x) (by omega) x le_rfl h1
      · exact ih (l (sum xs)) (by omega) (sum xs) le_rfl h1

/-- Irreflexivity of the ϑ-order (Freund, Exercise 3.2(b)). -/
theorem lt_irrefl' (a : ThetaTerm) : ¬ a < a := lt_irrefl_aux _ a le_rfl

theorem ne_of_lt' {a b : ThetaTerm} (h : a < b) : a ≠ b := by
  rintro rfl; exact lt_irrefl' a h

/-- Asymmetry of the ϑ-order. -/
theorem lt_asymm' {a b : ThetaTerm} (h : a < b) : ¬ b < a :=
  fun h' => lt_irrefl' a (lt_trans' h h')

theorem not_le_of_lt' {a b : ThetaTerm} (h : a < b) : ¬ b ≤ a := by
  rintro (h' | rfl)
  · exact lt_asymm' h h'
  · exact lt_irrefl' b h

/-- In the ϑ-ϑ clause, `ϑ α ≼ δ ∈ E(α)` is impossible (Freund's hint to Exercise 3.2(b)). -/
theorem not_theta_le_mem_E {a g : ThetaTerm} (hg : g ∈ E a) : ¬ theta a ≤ g :=
  not_le_of_lt' (lt_theta_of_mem_E hg)

/-! ### Trichotomy -/

theorem lt_trichotomy_aux (n : ℕ) :
    ∀ a b : ThetaTerm, l a + l b ≤ n → a < b ∨ a = b ∨ b < a := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn
  have C : ∀ {x y : ThetaTerm}, l x + l y < l a + l b → x < y ∨ x = y ∨ y < x :=
    fun h => ih _ (by omega) _ _ le_rfl
  rcases shape a with ha | rfl | ⟨x, xs, rfl⟩ <;>
  rcases shape b with hb | rfl | ⟨y, ys, rfl⟩
  -- principal, principal
  · cases a with
    | sum _ => exact absurd ha id
    | Omega =>
      cases b with
      | sum _ => exact absurd hb id
      | Omega => exact Or.inr (Or.inl rfl)
      | theta b => exact Or.inr (Or.inr (theta_lt_Omega b))
    | theta a =>
      cases b with
      | sum _ => exact absurd hb id
      | Omega => exact Or.inl (theta_lt_Omega a)
      | theta b =>
        simp only [l_theta] at C
        rcases C (x := a) (y := b) (by omega) with h | rfl | h
        · by_cases hE : ∀ g ∈ E a, g < theta b
          · exact Or.inl ((theta_lt_theta_iff a b).mpr (Or.inl ⟨h, hE⟩))
          · obtain ⟨g, hg, hgb⟩ : ∃ g ∈ E a, ¬ g < theta b := by
              by_contra hc
              exact hE (fun g hg => by_contra fun h' => hc ⟨g, hg, h'⟩)
            have := l_le_of_mem_E hg
            rcases C (x := g) (y := theta b) (by simp; omega) with h' | h' | h'
            · exact absurd h' hgb
            · exact Or.inr (Or.inr ((theta_lt_theta_iff b a).mpr (Or.inr ⟨g, hg, Or.inr h'.symm⟩)))
            · exact Or.inr (Or.inr ((theta_lt_theta_iff b a).mpr (Or.inr ⟨g, hg, Or.inl h'⟩)))
        · exact Or.inr (Or.inl rfl)
        · by_cases hE : ∀ g ∈ E b, g < theta a
          · exact Or.inr (Or.inr ((theta_lt_theta_iff b a).mpr (Or.inl ⟨h, hE⟩)))
          · obtain ⟨g, hg, hga⟩ : ∃ g ∈ E b, ¬ g < theta a := by
              by_contra hc
              exact hE (fun g hg => by_contra fun h' => hc ⟨g, hg, h'⟩)
            have := l_le_of_mem_E hg
            rcases C (x := g) (y := theta a) (by simp; omega) with h' | h' | h'
            · exact absurd h' hga
            · exact Or.inl ((theta_lt_theta_iff a b).mpr (Or.inr ⟨g, hg, Or.inr h'.symm⟩))
            · exact Or.inl ((theta_lt_theta_iff a b).mpr (Or.inr ⟨g, hg, Or.inl h'⟩))
  -- principal, `⟨⟩`
  · exact Or.inr (Or.inr (nil_lt_prin ha))
  -- principal, sum
  · rcases C (x := a) (y := y) (by simp; omega) with h | rfl | h
    · exact Or.inl ((prin_lt_cons_iff ha).mpr (Or.inl h))
    · exact Or.inl ((prin_lt_cons_iff ha).mpr (Or.inr rfl))
    · exact Or.inr (Or.inr ((cons_lt_prin_iff ha).mpr h))
  -- `⟨⟩`, anything
  · exact Or.inl (nil_lt_prin hb)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (nil_lt_cons y ys)
  -- sum, principal
  · rcases C (x := x) (y := b) (by simp; omega) with h | rfl | h
    · exact Or.inl ((cons_lt_prin_iff hb).mpr h)
    · exact Or.inr (Or.inr ((prin_lt_cons_iff hb).mpr (Or.inr rfl)))
    · exact Or.inr (Or.inr ((prin_lt_cons_iff hb).mpr (Or.inl h)))
  -- sum, `⟨⟩`
  · exact Or.inr (Or.inr (nil_lt_cons x xs))
  -- sum, sum
  · rcases C (x := x) (y := y) (by simp; omega) with h | rfl | h
    · exact Or.inl ((cons_lt_cons_iff x y xs ys).mpr (Or.inl h))
    · rcases C (x := sum xs) (y := sum ys) (by simp; omega) with h' | h' | h'
      · exact Or.inl ((cons_lt_cons_iff x x xs ys).mpr (Or.inr ⟨rfl, h'⟩))
      · cases h'; exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ((cons_lt_cons_iff x x ys xs).mpr (Or.inr ⟨rfl, h'⟩)))
    · exact Or.inr (Or.inr ((cons_lt_cons_iff y x ys xs).mpr (Or.inl h)))

/-- Trichotomy of the ϑ-order (Freund, Exercise 3.2(b)). -/
theorem lt_trichotomy' (a b : ThetaTerm) : a < b ∨ a = b ∨ b < a :=
  lt_trichotomy_aux _ a b le_rfl

theorem le_total' (a b : ThetaTerm) : a ≤ b ∨ b ≤ a := by
  rcases lt_trichotomy' a b with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem le_antisymm' {a b : ThetaTerm} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rcases hab with hab | rfl
  · exact absurd hba (not_le_of_lt' hab)
  · rfl

theorem not_lt_iff_le {a b : ThetaTerm} : ¬ a < b ↔ b ≤ a := by
  constructor
  · intro h
    rcases lt_trichotomy' a b with h' | h' | h'
    · exact absurd h' h
    · exact Or.inr h'.symm
    · exact Or.inl h'
  · intro h h'
    exact not_le_of_lt' h' h

/-! ### The comparison function -/

theorem cmp_eq_lt_iff {a b : ThetaTerm} : cmp a b = .lt ↔ a < b := by
  unfold cmp
  split_ifs with h1 h2
  · subst h1; simp [lt_irrefl']
  · simp [h2]
  · simp [h2]

theorem cmp_eq_gt_iff {a b : ThetaTerm} : cmp a b = .gt ↔ b < a := by
  unfold cmp
  split_ifs with h1 h2
  · subst h1; simp [lt_irrefl']
  · simp [lt_asymm' h2]
  · simp only [true_iff]
    rcases lt_trichotomy' a b with h | h | h
    · exact absurd h h2
    · exact absurd h h1
    · exact h

/-- Antisymmetry of the comparison. -/
theorem cmp_swap (a b : ThetaTerm) : (cmp a b).swap = cmp b a := by
  rcases lt_trichotomy' a b with h | rfl | h
  · rw [cmp_eq_lt_iff.mpr h, cmp_eq_gt_iff.mpr h]; rfl
  · simp
  · rw [cmp_eq_gt_iff.mpr h, cmp_eq_lt_iff.mpr h]; rfl

theorem cmp_eq_compareOfLessAndEq (a b : ThetaTerm) : cmp a b = compareOfLessAndEq a b := by
  unfold cmp compareOfLessAndEq
  by_cases h1 : a = b
  · subst h1; simp [lt_irrefl']
  · by_cases h2 : a < b
    · simp [h1, h2]
    · simp [h1, h2]

/-! ### Sums (Exercise 3.2(d)) -/

/-- Exercise 3.2(d), first part (on all raw terms): `α₀ ≺ ⟨α₀, …, α_{n-1}⟩`. -/
theorem lt_sum_cons_self : ∀ (x : ThetaTerm) (xs : List ThetaTerm), x < sum (x :: xs)
  | Omega, xs => (Omega_lt_cons_iff _ xs).mpr (le_refl' _)
  | theta a, xs => (theta_lt_cons_iff a _ xs).mpr (le_refl' _)
  | sum [], xs => nil_lt_cons _ xs
  | sum (y :: ys), xs => (cons_lt_cons_iff _ _ _ xs).mpr (Or.inl (lt_sum_cons_self y ys))
termination_by x => l x
decreasing_by simp; omega

/-- In a non-increasing list every entry is `≼` the first one. -/
theorem Desc.le_head {x : ThetaTerm} {xs : List ThetaTerm} (h : Desc (x :: xs)) :
    ∀ y ∈ x :: xs, y ≤ x := by
  induction xs generalizing x with
  | nil => intro y hy; simp at hy; exact Or.inr hy
  | cons z zs ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_refl' _
    · exact le_trans' (ih h.2 y hy) h.1

/-- The Cantor-sum clause is the lexicographic order on the lists of exponents. -/
theorem sum_lt_sum_iff_lex (as bs : List ThetaTerm) :
    sum as < sum bs ↔ List.Lex (· < ·) as bs := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => exact ⟨fun h => absurd h not_nil_lt_nil, fun h => by cases h⟩
    | cons b bs => exact ⟨fun _ => List.Lex.nil, fun _ => nil_lt_cons b bs⟩
  | cons a as ih =>
    cases bs with
    | nil => exact ⟨fun h => absurd h (not_cons_lt_nil a as), fun h => by cases h⟩
    | cons b bs =>
      rw [cons_lt_cons_iff]
      constructor
      · rintro (h | ⟨rfl, h⟩)
        · exact List.Lex.rel h
        · exact List.Lex.cons ((ih bs).mp h)
      · intro h
        cases h with
        | cons h => exact Or.inr ⟨rfl, (ih bs).mpr h⟩
        | rel h => exact Or.inl h

/-- A proper extension of a sum is larger. -/
theorem sum_lt_sum_append (xs : List ThetaTerm) (y : ThetaTerm) (ys : List ThetaTerm) :
    sum xs < sum (xs ++ y :: ys) := by
  induction xs with
  | nil => exact nil_lt_cons y ys
  | cons x xs ih => exact (cons_lt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, ih⟩)

/-- Exercise 3.2(d), second part, in multiset form: if the entries of `⟨α₀, …, α_{m-1}⟩`
are dominated entrywise by a sub-multiset of the entries of `⟨β₀, …, β_{n-1}⟩`, and the
latter are non-increasing, then `⟨α₀, …, α_{m-1}⟩ ≼ ⟨β₀, …, β_{n-1}⟩`.  The proof follows
Freund's hint: the entry dominating `α₀` is `≼ β₀`; if `α₀ ≺ β₀` we are done, and otherwise
`α₀ = β₀` is itself the dominating entry, which may be removed from both sides. -/
theorem sum_le_sum_of_forall₂ {as cs : List ThetaTerm} (hr : List.Forall₂ (· ≤ ·) as cs) :
    ∀ {bs : List ThetaTerm}, Desc bs → cs.Subperm bs → sum as ≤ sum bs := by
  induction hr with
  | nil => intro bs _ _; exact nil_le _
  | @cons a c as cs hac _ ih =>
    intro bs hd hs
    cases bs with
    | nil => exact absurd (hs.subset List.mem_cons_self) (by simp)
    | cons b bs =>
      have hcb : c ≤ b := hd.le_head c (hs.subset List.mem_cons_self)
      rcases le_trans' hac hcb with hab | rfl
      · exact Or.inl ((cons_lt_cons_iff _ _ _ _).mpr (Or.inl hab))
      · have hc : c = a := le_antisymm' hcb hac
        subst hc
        rcases ih hd.tail ((List.subperm_cons c).mp hs) with h | h
        · exact Or.inl ((cons_lt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, h⟩))
        · cases h; exact le_refl' _

private theorem subperm_map' {α β : Type} (f : α → β) {l₁ l₂ : List α}
    (h : l₁.Subperm l₂) : (l₁.map f).Subperm (l₂.map f) := by
  obtain ⟨l, hp, hs⟩ := h
  exact ⟨l.map f, hp.map f, hs.map f⟩

/-- Exercise 3.2(d), second part: `⟨α₀, …, α_{m-1}⟩ ≼ ⟨β₀, …, β_{n-1}⟩` whenever
`β_{n-1} ≼ ⋯ ≼ β₀` and there is an injection `g : {0, …, m-1} → {0, …, n-1}` with
`α_i ≼ β_{g(i)}` for all `i < m`. -/
theorem sum_le_sum_of_injective {as bs : List ThetaTerm} (hbs : Desc bs)
    (g : Fin as.length → Fin bs.length) (hg : Function.Injective g)
    (h : ∀ i, as.get i ≤ bs.get (g i)) : sum as ≤ sum bs := by
  have h1 : List.Forall₂ (· ≤ ·) as
      ((List.finRange as.length).map (fun i => bs.get (g i))) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp, fun i h₁ h₂ => ?_⟩
    simpa using h ⟨i, h₁⟩
  have h2 : ((List.finRange as.length).map (fun i => bs.get (g i))).Subperm bs := by
    have hn : ((List.finRange as.length).map g).Subperm (List.finRange bs.length) :=
      List.Nodup.subperm ((List.nodup_finRange _).map hg)
        (fun x _ => List.mem_finRange x)
    have := subperm_map' bs.get hn
    rwa [List.map_map, List.map_get_finRange] at this
  exact sum_le_sum_of_forall₂ h1 hbs h2

/-! ### Coefficients below `Ω` (Exercise 3.2(c), (e)) -/

/-- For normal `α`, every `δ ∈ E(α)` satisfies `δ ≼ α` (used in Freund, proof of
Proposition 3.9). -/
theorem le_of_mem_E : ∀ {a g : ThetaTerm}, NF a → g ∈ E a → g ≤ a
  | Omega, _, _, h => by simp at h
  | theta a, g, _, h => by simp at h; exact Or.inr h
  | sum xs, g, ha, h => by
    obtain ⟨y, hy, hg⟩ := mem_E_sum.mp h
    have h1 := le_of_mem_E (ha.of_mem hy) hg
    cases xs with
    | nil => cases hy
    | cons x xs =>
      have h2 := ha.desc.le_head y hy
      exact Or.inl (lt_of_le_of_lt' (le_trans' h1 h2) (lt_sum_cons_self x xs))
termination_by a => l a
decreasing_by exact l_lt_of_mem hy

/-- Exercise 3.2(c): for normal `α ≺ Ω`, `E(α) ≺* ϑ β ↔ α ≺ ϑ β`. -/
theorem forall_E_lt_theta_iff : ∀ {a : ThetaTerm} (b : ThetaTerm), NF a → a < Omega →
    ((∀ g ∈ E a, g < theta b) ↔ a < theta b)
  | Omega, _, _, h => absurd h not_Omega_lt_Omega
  | theta a, b, _, _ => by simp
  | sum [], b, _, _ => by simp [nil_lt_theta]
  | sum (x :: xs), b, ha, h => by
    constructor
    · intro hE
      rw [cons_lt_theta_iff]
      have hx : NF x := ha.of_mem List.mem_cons_self
      exact (forall_E_lt_theta_iff b hx ((cons_lt_Omega_iff x xs).mp h)).mp
        (fun g hg => hE g (by simp [hg]))
    · intro hlt g hg
      exact lt_of_le_of_lt' (le_of_mem_E ha hg) hlt
termination_by a => l a
decreasing_by simp; omega

/-- If `ϑ δ ≼ β ≺ Ω`, then `ϑ δ ≼ γ` for some `γ ∈ E(β)` (on all raw terms). -/
theorem exists_mem_E_of_theta_le : ∀ {b : ThetaTerm} (d : ThetaTerm), b < Omega →
    theta d ≤ b → ∃ g ∈ E b, theta d ≤ g
  | Omega, _, h, _ => absurd h not_Omega_lt_Omega
  | theta b, _, _, h => ⟨theta b, by simp, h⟩
  | sum [], d, _, h => by
    rcases h with h | h
    · exact absurd h (not_theta_lt_nil d)
    · cases h
  | sum (x :: xs), d, hb, h => by
    have hx : theta d ≤ x := by
      rcases h with h | h
      · exact (theta_lt_cons_iff d x xs).mp h
      · cases h
    obtain ⟨g, hg, h'⟩ := exists_mem_E_of_theta_le d ((cons_lt_Omega_iff x xs).mp hb) hx
    exact ⟨g, by simp [hg], h'⟩
termination_by b => l b
decreasing_by simp; omega

/-- Exercise 3.2(e): if `α ≼ β ≺ Ω` with `α` normal, then every `γ ∈ E(α)` has some
`δ ∈ E(β)` with `γ ≼ δ`. -/
theorem exists_mem_E_le_of_le {a b g : ThetaTerm} (ha : NF a) (hab : a ≤ b) (hb : b < Omega)
    (hg : g ∈ E a) : ∃ d ∈ E b, g ≤ d := by
  obtain ⟨d, rfl⟩ := exists_eq_theta_of_mem_E hg
  exact exists_mem_E_of_theta_le d hb (le_trans' (le_of_mem_E ha hg) hab)

/-! ### Compatibility with the constructors -/

/-- `0 = ⟨⟩` is the least term. -/
theorem zero_le' (a : ThetaTerm) : zero ≤ a := nil_le a

/-- `ϑ` is order preserving under the side condition `E(α) ≺* ϑ β` (Definition 3.1 (ii')). -/
theorem theta_lt_theta_of_lt {a b : ThetaTerm} (h : a < b) (hE : ∀ g ∈ E a, g < theta b) :
    theta a < theta b :=
  (theta_lt_theta_iff a b).mpr (Or.inl ⟨h, hE⟩)

/-- `ϑ α ≺ ϑ β` whenever `ϑ α ≼ δ` for some `δ ∈ E(β)` (Definition 3.1 (ii')). -/
theorem theta_lt_theta_of_le_mem_E {a b g : ThetaTerm} (hg : g ∈ E b) (h : theta a ≤ g) :
    theta a < theta b :=
  (theta_lt_theta_iff a b).mpr (Or.inr ⟨g, hg, h⟩)

/-- For normal `α ≺ Ω`: `α ≺ β` and `α ≺ ϑ β` give `ϑ α ≺ ϑ β` (by Exercise 3.2(c)). -/
theorem theta_lt_theta_of_lt_of_lt_theta {a b : ThetaTerm} (ha : NF a) (hΩ : a < Omega)
    (h : a < b) (h' : a < theta b) : theta a < theta b :=
  theta_lt_theta_of_lt h ((forall_E_lt_theta_iff b ha hΩ).mpr h')

/-- `Ω`'s place: `Ω ≺ β` only for sums `⟨β₀, …⟩` with `Ω ≼ β₀`. -/
theorem Omega_lt_iff {b : ThetaTerm} :
    Omega < b ↔ ∃ c cs, b = sum (c :: cs) ∧ Omega ≤ c := by
  constructor
  · intro h
    rcases shape b with hb | rfl | ⟨c, cs, rfl⟩
    · exact absurd h (not_Omega_lt_prin hb)
    · exact absurd h not_Omega_lt_nil
    · exact ⟨c, cs, rfl, (Omega_lt_cons_iff c cs).mp h⟩
  · rintro ⟨c, cs, rfl, h⟩
    exact (Omega_lt_cons_iff c cs).mpr h

/-- Principal terms are closed under `ω^·` from below: `⟨ξ⟩ ≺ P ↔ ξ ≺ P`
(for `P = Ω` or `P = ϑ β`). -/
theorem singleton_lt_prin_iff {p x : ThetaTerm} (hp : IsPrin p) : sum [x] < p ↔ x < p :=
  cons_lt_prin_iff hp

/-- Principal terms are additively principal: a non-increasing sum is below a principal
term iff all its entries are. -/
theorem sum_lt_prin_iff {p : ThetaTerm} (hp : IsPrin p) {xs : List ThetaTerm}
    (hxs : Desc xs) : sum xs < p ↔ ∀ x ∈ xs, x < p := by
  cases xs with
  | nil => simp [nil_lt_prin hp]
  | cons x xs =>
    rw [cons_lt_prin_iff hp]
    exact ⟨fun h y hy => lt_of_le_of_lt' (hxs.le_head y hy) h, fun h => h x List.mem_cons_self⟩

/-! ### The linear orders on terms and on notations -/

instance linearOrder : LinearOrder ThetaTerm where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := le_refl'
  le_trans _ _ _ := le_trans'
  le_antisymm _ _ := le_antisymm'
  lt_iff_le_not_ge _ _ := ⟨fun h => ⟨Or.inl h, not_le_of_lt' h⟩,
    fun ⟨h1, h2⟩ => h1.elim id (fun h => absurd (Or.inr h.symm) h2)⟩
  le_total := le_total'
  toDecidableLE := decidableLE
  toDecidableEq := inferInstance
  toDecidableLT := decidableLT
  compare := cmp
  compare_eq_compareOfLessAndEq := cmp_eq_compareOfLessAndEq

end ThetaTerm

instance ThetaNote.linearOrder : LinearOrder ThetaNote :=
  inferInstanceAs (LinearOrder {t : ThetaTerm // ThetaTerm.NF t})

namespace ThetaNote

theorem lt_iff {a b : ThetaNote} : a < b ↔ a.1 < b.1 := Iff.rfl

theorem le_iff {a b : ThetaNote} : a ≤ b ↔ a.1 ≤ b.1 := Iff.rfl

/-- The notation `0`. -/
def zero : ThetaNote := ⟨ThetaTerm.zero, ThetaTerm.nf_zero⟩

/-- The notation `Ω`. -/
def Omega : ThetaNote := ⟨ThetaTerm.Omega, ThetaTerm.nf_Omega⟩

/-- The notation `ϑ α`. -/
def theta (a : ThetaNote) : ThetaNote :=
  ⟨ThetaTerm.theta a.1, (ThetaTerm.nf_theta_iff _).mpr a.2⟩

/-- `0` is the least notation. -/
instance : OrderBot ThetaNote where
  bot := zero
  bot_le a := ThetaTerm.zero_le' a.1

theorem bot_eq_zero : (⊥ : ThetaNote) = zero := rfl

theorem theta_lt_Omega (a : ThetaNote) : theta a < Omega := ThetaTerm.theta_lt_Omega a.1

end ThetaNote

end OrdinalAnalysis
