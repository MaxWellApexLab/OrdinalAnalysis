/-
  The multi-level ϑ-order is a linear order.

  Sources: A. Freund, arXiv:2204.09321, Definition 3.1 and Exercise 3.2 (the one-level
  system); G. Wilken, arXiv:2410.15953, Proposition 2.3 (the clause at one level of the
  stepwise defined ϑ-functions).  The clauses used are listed in the companion module on
  terms.

  The proofs are those of the one-level system, level by level; they work on all raw terms,
  for all levels `k : ℕ` at once.

  * Principal terms are first compared by their position `key` (`ϑ_k`-terms at `2k`, `Ω_{k+1}`
    at `2k + 1`): a smaller position gives a smaller term, a smaller term never has a larger
    position, and `Ω_{k+1}` is strictly above everything of smaller or equal position.  So
    in a chain `P ≺ Q ≺ R` of principal terms, either the positions of `P` and `R` differ,
    and then `P ≺ R`, or `P`, `Q`, `R` are `ϑ_k`-terms of one level `k`.
  * For three `ϑ_k`-terms, transitivity is Freund's argument with `E_k` in place of `E`, by
    induction on `l α + l β + l γ`; it uses only `l δ ≤ l α` for `δ ∈ E_k(α)`.
  * `E_k(α) ≺* ϑ_k α` (Exercise 3.2(a) per level): a member `ϑ_j δ` with `j < k` is below
    by position, and a member `ϑ_k δ` is below by the second disjunct of the clause.
  * Irreflexivity and trichotomy are then Freund's arguments, by induction on the length.

  For normal terms the file proves the analogues of Exercise 3.2(c)–(e) per level:
  (c) for `α ≺ Ω_{k+1}`, `E_k(α) ≺* ϑ_k β ↔ α ≺ ϑ_k β`;
  (d) `α₀ ≺ ⟨α₀, …⟩`, and sums are compared lexicographically;
  (e) for `α ≼ β ≺ Ω_{k+1}`, every `ϑ_k`-term in `E_k(α)` is `≼` some member of `E_k(β)`.
  In (e) only the members of level exactly `k` are covered: `E_k(α)` also contains the
  members of lower level, and those need not be dominated by a member of `E_k(β)` (for
  `α = ϑ₀ 0 ≺ β = Ω₁ ≺ Ω₂` one has `E₁(α) = {ϑ₀ 0}` and `E₁(β) = ∅`); they lie below `Ω_k`,
  hence below every `ϑ_k`-term, so they never matter in the clause at level `k`.
-/
import OrdinalAnalysis.Ordinal.ThetaW.Basic
import Mathlib.Data.List.Lex
import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

/-! ### Preliminaries -/

/-- No term is below `⟨⟩`. -/
theorem not_lt_nil (a : ThetaWTerm) : ¬ a < sum [] := by
  cases a with
  | Omega i => exact not_Omega_lt_nil i
  | theta i a => exact not_theta_lt_nil i a
  | sum xs =>
    cases xs with
    | nil => exact not_nil_lt_nil
    | cons x xs => exact not_cons_lt_nil x xs

/-- `⟨⟩` is below every other term. -/
theorem nil_lt_of_ne {a : ThetaWTerm} (h : a ≠ sum []) : sum [] < a := by
  cases a with
  | Omega i => exact nil_lt_Omega i
  | theta i a => exact nil_lt_theta i a
  | sum xs =>
    cases xs with
    | nil => exact absurd rfl h
    | cons x xs => exact nil_lt_cons x xs

theorem nil_le (a : ThetaWTerm) : sum [] ≤ a := by
  by_cases h : a = sum []
  · exact Or.inr h.symm
  · exact Or.inl (nil_lt_of_ne h)

/-- Every term is principal, `⟨⟩`, or a non-empty sum. -/
theorem shape (a : ThetaWTerm) :
    IsPrin a ∨ a = sum [] ∨ ∃ x xs, a = sum (x :: xs) := by
  cases a with
  | Omega _ => exact Or.inl trivial
  | theta _ _ => exact Or.inl trivial
  | sum xs =>
    cases xs with
    | nil => exact Or.inr (Or.inl rfl)
    | cons x xs => exact Or.inr (Or.inr ⟨x, xs, rfl⟩)

/-! ### Positions of principal terms -/

/-- A smaller position gives a smaller principal term. -/
theorem prin_lt_of_key_lt {p q : ThetaWTerm} (hp : IsPrin p) (hq : IsPrin q)
    (h : key p < key q) : p < q := by
  cases p with
  | sum _ => exact absurd hp id
  | Omega i =>
    cases q with
    | sum _ => exact absurd hq id
    | Omega j => simp at h; exact (Omega_lt_Omega_iff i j).mpr (by omega)
    | theta j b => simp at h; exact (Omega_lt_theta_iff i j b).mpr (by omega)
  | theta i a =>
    cases q with
    | sum _ => exact absurd hq id
    | Omega j => simp at h; exact (theta_lt_Omega_iff i j a).mpr (by omega)
    | theta j b => simp at h; exact theta_lt_theta_of_lt_level a b (by omega)

/-- A smaller principal term never has a larger position. -/
theorem key_le_of_lt {p q : ThetaWTerm} (hp : IsPrin p) (hq : IsPrin q) (h : p < q) :
    key p ≤ key q := by
  cases p with
  | sum _ => exact absurd hp id
  | Omega i =>
    cases q with
    | sum _ => exact absurd hq id
    | Omega j => have := (Omega_lt_Omega_iff i j).mp h; simp; omega
    | theta j b => have := (Omega_lt_theta_iff i j b).mp h; simp; omega
  | theta i a =>
    cases q with
    | sum _ => exact absurd hq id
    | Omega j => have := (theta_lt_Omega_iff i j a).mp h; simp; omega
    | theta j b =>
      have : ¬ j < i := fun hji => not_theta_lt_theta_of_lt_level a b hji h
      simp; omega

/-- Below `Ω_{j+1}` the position drops strictly. -/
theorem key_lt_of_lt_Omega {p : ThetaWTerm} (hp : IsPrin p) {j : ℕ} (h : p < Omega j) :
    key p < key (Omega j) := by
  cases p with
  | sum _ => exact absurd hp id
  | Omega i => have := (Omega_lt_Omega_iff i j).mp h; simp; omega
  | theta i a => have := (theta_lt_Omega_iff i j a).mp h; simp; omega

/-- Above `Ω_{i+1}` the position rises strictly. -/
theorem key_lt_of_Omega_lt {q : ThetaWTerm} (hq : IsPrin q) {i : ℕ} (h : Omega i < q) :
    key (Omega i) < key q := by
  cases q with
  | sum _ => exact absurd hq id
  | Omega j => have := (Omega_lt_Omega_iff i j).mp h; simp; omega
  | theta j b => have := (Omega_lt_theta_iff i j b).mp h; simp; omega

theorem not_Omega_lt_Omega (k : ℕ) : ¬ Omega k < Omega k := by
  rw [Omega_lt_Omega_iff]; omega

/-! ### Transitivity -/

/-- Transitivity, by induction on `n ≥ l α + l β + l γ`. -/
theorem lt_trans_aux (n : ℕ) :
    ∀ a b c : ThetaWTerm, l a + l b + l c ≤ n → a < b → b < c → a < c := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b c hn hab hbc
  have T : ∀ {x y z : ThetaWTerm}, l x + l y + l z < l a + l b + l c →
      x < y → y < z → x < z :=
    fun h h1 h2 => ih _ (by omega) _ _ _ le_rfl h1 h2
  have TL : ∀ {x y z : ThetaWTerm}, l x + l y + l z < l a + l b + l c →
      x ≤ y → y < z → x < z := by
    intro x y z h h1 h2
    rcases h1 with h1 | rfl
    · exact T h h1 h2
    · exact h2
  have TR : ∀ {x y z : ThetaWTerm}, l x + l y + l z < l a + l b + l c →
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
  · have k1 := key_le_of_lt ha hb hab
    have k2 := key_le_of_lt hb hc hbc
    by_cases hk : key a < key c
    · exact prin_lt_of_key_lt ha hc hk
    cases a with
    | sum _ => exact absurd ha id
    | Omega i => exact absurd (by have := key_lt_of_Omega_lt hb hab; omega) hk
    | theta i a =>
    cases c with
    | sum _ => exact absurd hc id
    | Omega j => exact absurd (by have := key_lt_of_lt_Omega hb hbc; omega) hk
    | theta m c =>
    cases b with
    | sum _ => exact absurd hb id
    | Omega j => exact absurd (by have := key_lt_of_lt_Omega ha hab; omega) hk
    | theta j b =>
    simp only [key_theta] at k1 k2 hk
    have e1 : j = i := by omega
    have e2 : m = i := by omega
    subst e1 e2
    -- three `ϑ_m`-terms: Freund's argument with `E_m`
    have hlab := hab
    rw [theta_lt_theta_iff] at hab hbc
    rw [theta_lt_theta_iff]
    rcases hbc with ⟨hbc1, hbc2⟩ | ⟨d, hd, hbd⟩
    · rcases hab with ⟨hab1, hab2⟩ | ⟨d, hd, had⟩
      · refine Or.inl ⟨T (by simp; omega) hab1 hbc1, fun g hg => ?_⟩
        have := l_le_of_mem_E hg
        have hbc' : theta m b < theta m c :=
          (theta_lt_theta_iff m b c).mpr (Or.inl ⟨hbc1, hbc2⟩)
        exact T (by simp; omega) (hab2 g hg) hbc'
      · have := l_le_of_mem_E hd
        exact (theta_lt_theta_iff m a c).mp (TL (by simp; omega) had (hbc2 d hd))
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

/-- Transitivity of the multi-level ϑ-order. -/
theorem lt_trans' {a b c : ThetaWTerm} (hab : a < b) (hbc : b < c) : a < c :=
  lt_trans_aux _ a b c le_rfl hab hbc

theorem lt_of_le_of_lt' {a b c : ThetaWTerm} (hab : a ≤ b) (hbc : b < c) : a < c := by
  rcases hab with hab | rfl
  · exact lt_trans' hab hbc
  · exact hbc

theorem lt_of_lt_of_le' {a b c : ThetaWTerm} (hab : a < b) (hbc : b ≤ c) : a < c := by
  rcases hbc with hbc | rfl
  · exact lt_trans' hab hbc
  · exact hab

theorem le_trans' {a b c : ThetaWTerm} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rcases hab with hab | rfl
  · exact Or.inl (lt_of_lt_of_le' hab hbc)
  · exact hbc

/-! ### `E_k(α) ≺* ϑ_k α` (Exercise 3.2(a) per level) -/

/-- Exercise 3.2(a) per level: every member of `E_k(α)` is below `ϑ_k α`. -/
theorem lt_theta_of_mem_E {k : ℕ} {a g : ThetaWTerm} (h : g ∈ E k a) : g < theta k a := by
  obtain ⟨j, d, hj, rfl⟩ := exists_eq_theta_of_mem_E h
  rcases Nat.lt_or_ge j k with hjk | hjk
  · exact theta_lt_theta_of_lt_level d a hjk
  · have : j = k := by omega
    subst this
    exact (theta_lt_theta_iff j d a).mpr (Or.inr ⟨theta j d, h, le_refl' _⟩)

/-! ### Irreflexivity -/

theorem lt_irrefl_aux (n : ℕ) : ∀ a : ThetaWTerm, l a ≤ n → ¬ a < a := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn h
  cases a with
  | Omega k => exact not_Omega_lt_Omega k h
  | theta k a =>
    rcases (theta_lt_theta_iff k a a).mp h with ⟨h1, _⟩ | ⟨g, hg, h1⟩
    · simp at hn
      exact ih (l a) (by omega) a le_rfl h1
    · have hl := l_le_of_mem_E hg
      simp at hn
      rcases h1 with h1 | rfl
      · exact ih (l g) (by omega) g le_rfl (lt_trans' (lt_theta_of_mem_E hg) h1)
      · simp only [l_theta] at hl; omega
  | sum xs =>
    cases xs with
    | nil => exact not_nil_lt_nil h
    | cons x xs =>
      simp at hn
      rcases (cons_lt_cons_iff x x xs xs).mp h with h1 | ⟨_, h1⟩
      · exact ih (l x) (by omega) x le_rfl h1
      · exact ih (l (sum xs)) (by omega) (sum xs) le_rfl h1

/-- Irreflexivity of the multi-level ϑ-order. -/
theorem lt_irrefl' (a : ThetaWTerm) : ¬ a < a := lt_irrefl_aux _ a le_rfl

theorem ne_of_lt' {a b : ThetaWTerm} (h : a < b) : a ≠ b := by
  rintro rfl; exact lt_irrefl' a h

/-- Asymmetry of the multi-level ϑ-order. -/
theorem lt_asymm' {a b : ThetaWTerm} (h : a < b) : ¬ b < a :=
  fun h' => lt_irrefl' a (lt_trans' h h')

theorem not_le_of_lt' {a b : ThetaWTerm} (h : a < b) : ¬ b ≤ a := by
  rintro (h' | rfl)
  · exact lt_asymm' h h'
  · exact lt_irrefl' b h

/-- In the clause at level `k`, `ϑ_k α ≼ δ ∈ E_k(α)` is impossible. -/
theorem not_theta_le_mem_E {k : ℕ} {a g : ThetaWTerm} (hg : g ∈ E k a) : ¬ theta k a ≤ g :=
  not_le_of_lt' (lt_theta_of_mem_E hg)

/-! ### Trichotomy -/

theorem lt_trichotomy_aux (n : ℕ) :
    ∀ a b : ThetaWTerm, l a + l b ≤ n → a < b ∨ a = b ∨ b < a := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn
  have C : ∀ {x y : ThetaWTerm}, l x + l y < l a + l b → x < y ∨ x = y ∨ y < x :=
    fun h => ih _ (by omega) _ _ le_rfl
  rcases shape a with ha | rfl | ⟨x, xs, rfl⟩ <;>
  rcases shape b with hb | rfl | ⟨y, ys, rfl⟩
  -- principal, principal
  · rcases Nat.lt_trichotomy (key a) (key b) with hk | hk | hk
    · exact Or.inl (prin_lt_of_key_lt ha hb hk)
    rotate_left
    · exact Or.inr (Or.inr (prin_lt_of_key_lt hb ha hk))
    cases a with
    | sum _ => exact absurd ha id
    | Omega i =>
      cases b with
      | sum _ => exact absurd hb id
      | Omega j =>
        have : i = j := by simp at hk; omega
        subst this; exact Or.inr (Or.inl rfl)
      | theta j b => simp at hk; omega
    | theta i a =>
      cases b with
      | sum _ => exact absurd hb id
      | Omega j => simp at hk; omega
      | theta j b =>
        simp only [key_theta] at hk
        have e : j = i := by omega
        subst e
        simp only [l_theta] at C
        rcases C (x := a) (y := b) (by omega) with h | rfl | h
        · by_cases hE : ∀ g ∈ E j a, g < theta j b
          · exact Or.inl ((theta_lt_theta_iff j a b).mpr (Or.inl ⟨h, hE⟩))
          · obtain ⟨g, hg, hgb⟩ : ∃ g ∈ E j a, ¬ g < theta j b := by
              by_contra hc
              exact hE (fun g hg => by_contra fun h' => hc ⟨g, hg, h'⟩)
            have := l_le_of_mem_E hg
            rcases C (x := g) (y := theta j b) (by simp; omega) with h' | h' | h'
            · exact absurd h' hgb
            · exact Or.inr (Or.inr
                ((theta_lt_theta_iff j b a).mpr (Or.inr ⟨g, hg, Or.inr h'.symm⟩)))
            · exact Or.inr (Or.inr
                ((theta_lt_theta_iff j b a).mpr (Or.inr ⟨g, hg, Or.inl h'⟩)))
        · exact Or.inr (Or.inl rfl)
        · by_cases hE : ∀ g ∈ E j b, g < theta j a
          · exact Or.inr (Or.inr ((theta_lt_theta_iff j b a).mpr (Or.inl ⟨h, hE⟩)))
          · obtain ⟨g, hg, hga⟩ : ∃ g ∈ E j b, ¬ g < theta j a := by
              by_contra hc
              exact hE (fun g hg => by_contra fun h' => hc ⟨g, hg, h'⟩)
            have := l_le_of_mem_E hg
            rcases C (x := g) (y := theta j a) (by simp; omega) with h' | h' | h'
            · exact absurd h' hga
            · exact Or.inl ((theta_lt_theta_iff j a b).mpr (Or.inr ⟨g, hg, Or.inr h'.symm⟩))
            · exact Or.inl ((theta_lt_theta_iff j a b).mpr (Or.inr ⟨g, hg, Or.inl h'⟩))
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

/-- Trichotomy of the multi-level ϑ-order. -/
theorem lt_trichotomy' (a b : ThetaWTerm) : a < b ∨ a = b ∨ b < a :=
  lt_trichotomy_aux _ a b le_rfl

theorem le_total' (a b : ThetaWTerm) : a ≤ b ∨ b ≤ a := by
  rcases lt_trichotomy' a b with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem le_antisymm' {a b : ThetaWTerm} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rcases hab with hab | rfl
  · exact absurd hba (not_le_of_lt' hab)
  · rfl

theorem not_lt_iff_le {a b : ThetaWTerm} : ¬ a < b ↔ b ≤ a := by
  constructor
  · intro h
    rcases lt_trichotomy' a b with h' | h' | h'
    · exact absurd h' h
    · exact Or.inr h'.symm
    · exact Or.inl h'
  · intro h h'
    exact not_le_of_lt' h' h

/-! ### The comparison function -/

theorem cmp_eq_lt_iff {a b : ThetaWTerm} : cmp a b = .lt ↔ a < b := by
  unfold cmp
  split_ifs with h1 h2
  · subst h1; simp [lt_irrefl']
  · simp [h2]
  · simp [h2]

theorem cmp_eq_gt_iff {a b : ThetaWTerm} : cmp a b = .gt ↔ b < a := by
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
theorem cmp_swap (a b : ThetaWTerm) : (cmp a b).swap = cmp b a := by
  rcases lt_trichotomy' a b with h | rfl | h
  · rw [cmp_eq_lt_iff.mpr h, cmp_eq_gt_iff.mpr h]; rfl
  · simp
  · rw [cmp_eq_gt_iff.mpr h, cmp_eq_lt_iff.mpr h]; rfl

theorem cmp_eq_compareOfLessAndEq (a b : ThetaWTerm) : cmp a b = compareOfLessAndEq a b := by
  unfold cmp compareOfLessAndEq
  by_cases h1 : a = b
  · subst h1; simp [lt_irrefl']
  · by_cases h2 : a < b
    · simp [h1, h2]
    · simp [h1, h2]

/-! ### Sums (Exercise 3.2(d)) -/

/-- Exercise 3.2(d), first part: `α₀ ≺ ⟨α₀, …, α_{n-1}⟩`. -/
theorem lt_sum_cons_self : ∀ (x : ThetaWTerm) (xs : List ThetaWTerm), x < sum (x :: xs)
  | Omega k, xs => (Omega_lt_cons_iff k _ xs).mpr (le_refl' _)
  | theta k a, xs => (theta_lt_cons_iff k a _ xs).mpr (le_refl' _)
  | sum [], xs => nil_lt_cons _ xs
  | sum (y :: ys), xs => (cons_lt_cons_iff _ _ _ xs).mpr (Or.inl (lt_sum_cons_self y ys))
termination_by x => l x
decreasing_by simp; omega

/-- In a non-increasing list every entry is `≼` the first one. -/
theorem Desc.le_head {x : ThetaWTerm} {xs : List ThetaWTerm} (h : Desc (x :: xs)) :
    ∀ y ∈ x :: xs, y ≤ x := by
  induction xs generalizing x with
  | nil => intro y hy; simp at hy; exact Or.inr hy
  | cons z zs ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_refl' _
    · exact le_trans' (ih h.2 y hy) h.1

/-- The Cantor-sum clause is the lexicographic order on the lists of exponents. -/
theorem sum_lt_sum_iff_lex (as bs : List ThetaWTerm) :
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

/-- Principal terms are additively principal: a non-increasing sum is below a principal
term iff all its entries are. -/
theorem sum_lt_prin_iff {p : ThetaWTerm} (hp : IsPrin p) {xs : List ThetaWTerm}
    (hxs : Desc xs) : sum xs < p ↔ ∀ x ∈ xs, x < p := by
  cases xs with
  | nil => simp [nil_lt_prin hp]
  | cons x xs =>
    rw [cons_lt_prin_iff hp]
    exact ⟨fun h y hy => lt_of_le_of_lt' (hxs.le_head y hy) h, fun h => h x List.mem_cons_self⟩

/-! ### Coefficients (Exercise 3.2(c), (e) per level) -/

/-- For normal `α`, every `δ ∈ E_k(α)` satisfies `δ ≼ α`. -/
theorem le_of_mem_E {k : ℕ} : ∀ {a g : ThetaWTerm}, NF a → g ∈ E k a → g ≤ a
  | Omega _, _, _, h => by simp at h
  | theta j a, g, ha, h => by
    by_cases hj : j ≤ k
    · rw [E_theta_of_le hj] at h; simp at h; exact Or.inr h
    · have hjk : k < j := Nat.lt_of_not_le hj
      rw [E_theta_of_lt hjk] at h
      obtain ⟨i, d, hi, rfl⟩ := exists_eq_theta_of_mem_E h
      exact Or.inl (theta_lt_theta_of_lt_level d a (by omega))
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

/-- The members of `E_k(α)` lie below `Ω_{k+1}`. -/
theorem lt_Omega_of_mem_E {k : ℕ} {a g : ThetaWTerm} (hg : g ∈ E k a) : g < Omega k := by
  obtain ⟨j, d, hj, rfl⟩ := exists_eq_theta_of_mem_E hg
  exact (theta_lt_Omega_iff j k d).mpr hj

/-- Exercise 3.2(c) at level `k`: for normal `α ≺ Ω_{k+1}`,
`E_k(α) ≺* ϑ_k β ↔ α ≺ ϑ_k β`. -/
theorem forall_E_lt_theta_iff {k : ℕ} : ∀ {a : ThetaWTerm} (b : ThetaWTerm), NF a →
    a < Omega k → ((∀ g ∈ E k a, g < theta k b) ↔ a < theta k b)
  | Omega j, b, _, h => by
    have := (Omega_lt_Omega_iff j k).mp h
    simp only [E_Omega, List.not_mem_nil, false_imp_iff, imp_true_iff, true_iff]
    exact (Omega_lt_theta_iff j k b).mpr this
  | theta j a, b, _, h => by
    have := (theta_lt_Omega_iff j k a).mp h
    rw [E_theta_of_le this]; simp
  | sum [], b, _, _ => by simp [nil_lt_theta]
  | sum (x :: xs), b, ha, h => by
    constructor
    · intro hE
      rw [cons_lt_theta_iff]
      have hx : NF x := ha.of_mem List.mem_cons_self
      exact (forall_E_lt_theta_iff b hx ((cons_lt_Omega_iff k x xs).mp h)).mp
        (fun g hg => hE g (by simp [hg]))
    · intro hlt g hg
      exact lt_of_le_of_lt' (le_of_mem_E ha hg) hlt
termination_by a => l a
decreasing_by simp; omega

/-- If `ϑ_k δ ≼ β ≺ Ω_{k+1}`, then `ϑ_k δ ≼ γ` for some `γ ∈ E_k(β)` (on all raw terms). -/
theorem exists_mem_E_of_theta_le {k : ℕ} : ∀ {b : ThetaWTerm} (d : ThetaWTerm),
    b < Omega k → theta k d ≤ b → ∃ g ∈ E k b, theta k d ≤ g
  | Omega j, d, hb, h => by
    have hjk := (Omega_lt_Omega_iff j k).mp hb
    rcases h with h | h
    · have := (theta_lt_Omega_iff k j d).mp h; omega
    · cases h
  | theta j e, _, hb, h => by
    have := (theta_lt_Omega_iff j k e).mp hb
    exact ⟨theta j e, by rw [E_theta_of_le this]; simp, h⟩
  | sum [], d, _, h => by
    rcases h with h | h
    · exact absurd h (not_theta_lt_nil k d)
    · cases h
  | sum (x :: xs), d, hb, h => by
    have hx : theta k d ≤ x := by
      rcases h with h | h
      · exact (theta_lt_cons_iff k d x xs).mp h
      · cases h
    obtain ⟨g, hg, h'⟩ :=
      exists_mem_E_of_theta_le d ((cons_lt_Omega_iff k x xs).mp hb) hx
    exact ⟨g, by simp [hg], h'⟩
termination_by b => l b
decreasing_by simp; omega

/-- Exercise 3.2(e) at level `k`: if `α ≼ β ≺ Ω_{k+1}` with `α` normal, then every member
`ϑ_k δ` of `E_k(α)` of level `k` has some `γ ∈ E_k(β)` with `ϑ_k δ ≼ γ`. -/
theorem exists_mem_E_le_of_le {k : ℕ} {a b d : ThetaWTerm} (ha : NF a) (hab : a ≤ b)
    (hb : b < Omega k) (hg : theta k d ∈ E k a) : ∃ g ∈ E k b, theta k d ≤ g :=
  exists_mem_E_of_theta_le d hb (le_trans' (le_of_mem_E ha hg) hab)

/-! ### Compatibility with the constructors -/

/-- `0 = ⟨⟩` is the least term. -/
theorem zero_le' (a : ThetaWTerm) : zero ≤ a := nil_le a

/-- `ϑ_k` is order preserving under the side condition `E_k(α) ≺* ϑ_k β`. -/
theorem theta_lt_theta_of_lt {k : ℕ} {a b : ThetaWTerm} (h : a < b)
    (hE : ∀ g ∈ E k a, g < theta k b) : theta k a < theta k b :=
  (theta_lt_theta_iff k a b).mpr (Or.inl ⟨h, hE⟩)

/-- `ϑ_k α ≺ ϑ_k β` whenever `ϑ_k α ≼ δ` for some `δ ∈ E_k(β)`. -/
theorem theta_lt_theta_of_le_mem_E {k : ℕ} {a b g : ThetaWTerm} (hg : g ∈ E k b)
    (h : theta k a ≤ g) : theta k a < theta k b :=
  (theta_lt_theta_iff k a b).mpr (Or.inr ⟨g, hg, h⟩)

/-- For normal `α ≺ Ω_{k+1}`: `α ≺ β` and `α ≺ ϑ_k β` give `ϑ_k α ≺ ϑ_k β`. -/
theorem theta_lt_theta_of_lt_of_lt_theta {k : ℕ} {a b : ThetaWTerm} (ha : NF a)
    (hΩ : a < Omega k) (h : a < b) (h' : a < theta k b) : theta k a < theta k b :=
  theta_lt_theta_of_lt h ((forall_E_lt_theta_iff b ha hΩ).mpr h')

/-- `Ω_k < ϑ_k α < Ω_{k+1}`, in the indexing of the terms: `Ω_{k+1} ≺ ϑ_{k+1} α ≺ Ω_{k+2}`
and `ϑ_k α ≺ Ω_{k+1}`. -/
theorem theta_lt_Omega_self (k : ℕ) (a : ThetaWTerm) : theta k a < Omega k :=
  (theta_lt_Omega_iff k k a).mpr le_rfl

theorem Omega_lt_theta_succ (k : ℕ) (a : ThetaWTerm) : Omega k < theta (k + 1) a :=
  (Omega_lt_theta_iff k (k + 1) a).mpr (Nat.lt_succ_self k)

/-- What lies above `Ω_{k+1}`: the principal terms of larger position, and the sums whose
first entry is `≽ Ω_{k+1}`. -/
theorem Omega_lt_iff {k : ℕ} {b : ThetaWTerm} :
    Omega k < b ↔ (IsPrin b ∧ key (Omega k) < key b) ∨
      ∃ c cs, b = sum (c :: cs) ∧ Omega k ≤ c := by
  constructor
  · intro h
    rcases shape b with hb | rfl | ⟨c, cs, rfl⟩
    · exact Or.inl ⟨hb, key_lt_of_Omega_lt hb h⟩
    · exact absurd h (not_Omega_lt_nil k)
    · exact Or.inr ⟨c, cs, rfl, (Omega_lt_cons_iff k c cs).mp h⟩
  · rintro (⟨hb, hk⟩ | ⟨c, cs, rfl, h⟩)
    · exact prin_lt_of_key_lt (isPrin_Omega k) hb hk
    · exact (Omega_lt_cons_iff k c cs).mpr h

/-! ### The linear order on terms -/

instance linearOrder : LinearOrder ThetaWTerm where
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

end ThetaWTerm

/-- The multi-level ϑ-notation: terms in normal form, all levels. -/
def ThetaWNote : Type := {t : ThetaWTerm // ThetaWTerm.NF t}

instance : DecidableEq ThetaWNote :=
  inferInstanceAs (DecidableEq {t : ThetaWTerm // ThetaWTerm.NF t})

instance ThetaWNote.linearOrder : LinearOrder ThetaWNote :=
  inferInstanceAs (LinearOrder {t : ThetaWTerm // ThetaWTerm.NF t})

namespace ThetaWNote

theorem lt_iff {a b : ThetaWNote} : a < b ↔ a.1 < b.1 := Iff.rfl

theorem le_iff {a b : ThetaWNote} : a ≤ b ↔ a.1 ≤ b.1 := Iff.rfl

/-- The notation `0`. -/
def zero : ThetaWNote := ⟨ThetaWTerm.zero, ThetaWTerm.nf_zero⟩

/-- The notation `Ω_{k+1}`. -/
def Omega (k : ℕ) : ThetaWNote := ⟨ThetaWTerm.Omega k, ThetaWTerm.nf_Omega k⟩

/-- The notation `ϑ_k α`. -/
def theta (k : ℕ) (a : ThetaWNote) : ThetaWNote :=
  ⟨ThetaWTerm.theta k a.1, (ThetaWTerm.nf_theta_iff _ _).mpr a.2⟩

/-- `0` is the least notation. -/
instance : OrderBot ThetaWNote where
  bot := zero
  bot_le a := ThetaWTerm.zero_le' a.1

theorem bot_eq_zero : (⊥ : ThetaWNote) = zero := rfl

theorem theta_lt_Omega (k : ℕ) (a : ThetaWNote) : theta k a < Omega k :=
  ThetaWTerm.theta_lt_Omega_self k a.1

theorem Omega_lt_theta_succ (k : ℕ) (a : ThetaWNote) : Omega k < theta (k + 1) a :=
  ThetaWTerm.Omega_lt_theta_succ k a.1

end ThetaWNote

end OrdinalAnalysis
