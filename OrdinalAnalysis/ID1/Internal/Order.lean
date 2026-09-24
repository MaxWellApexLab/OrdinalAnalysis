/-
  The order of the coded ϑ-notation inside models of `IΣ₁`.

  `Codes` defines the internal order `iltb` by a course-of-values table and proves that it
  computes `ThetaTerm.ltb` on standard codes.  Here the order-theoretic facts are proved for
  *all* codes of an arbitrary model `V` of `IΣ₁`, following the syntactic proofs of
  `Ordinal/Theta/Order.lean` (Freund, arXiv:2204.09321, Exercise 3.2) by `IΣ₁`-induction.

  The induction measure is the sum of the codes rather than the sum of the lengths: every
  immediate constituent of a code is below it, and so is every element of its coefficient set
  `E` (`iinE_bound`), which is all the syntactic proofs use of the length.

  A code is `0`, a cons cell, a `ϑ`-code, or of *top shape* (`kind` `1` or `4`); codes of top
  shape are compared like `Ω`.  Transitivity and irreflexivity hold for all codes,
  trichotomy for codes of terms (in particular for codes of normal forms):

  * `iltb_trans`, `iltb_irrefl`, `iltb_asymm`, `iltb_trichotomy`, `iltb_trichotomy_nf`;
  * the coefficient sets: `iinE_bound` (elements of `E(c)` are `ϑ`-codes `≤ c`),
    `iall_iff`, `iex_iff` (the two quantifier flags of the table mean what they say),
    `lt_theta_of_iinE` (`E(α) ≺ ϑ α`).
-/
import OrdinalAnalysis.ID1.Internal.Codes

set_option autoImplicit false

namespace OrdinalAnalysis.ID1.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.Gentzen.InternalONote

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Definability of the auxiliary flags

The flags `nfA`, `sumK`, `sok` and `descOk` of the normal-form recogniser, at every level
of the hierarchy, as for the other functions of the coding. -/

instance nfA_definable : 𝚺₁-Function₁ (nfA : V → V) := nfA_defined.to_definable
instance nfA_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (nfA : V → V) :=
  nfA_definable.of_sigmaOne
instance sumK_definable : 𝚺₁-Function₁ (sumK : V → V) := sumK_defined.to_definable
instance sumK_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (sumK : V → V) :=
  sumK_definable.of_sigmaOne
instance sok_definable : 𝚺₁-Function₁ (sok : V → V) := sok_defined.to_definable
instance sok_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (sok : V → V) :=
  sok_definable.of_sigmaOne
instance descOk_definable : 𝚺₁-Function₁ (descOk : V → V) := descOk_defined.to_definable
instance descOk_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (descOk : V → V) :=
  descOk_definable.of_sigmaOne

/-! ### Shapes of codes -/

/-- Every code is `0`, a cons cell, a `ϑ`-code, or of top shape. -/
lemma code_cases (c : V) :
    c = 0 ∨ (∃ x s, c = tcCons x s) ∨ (∃ a, c = tcTheta a) ∨ (kind c = 1 ∨ kind c = 4) := by
  rcases kind_cases c with h | h | h | h | h
  · exact Or.inl (kind_eq_zero_iff.mp h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl ⟨_, eq_tcTheta_of_kind h⟩))
  · exact Or.inr (Or.inl ⟨_, _, eq_tcCons_of_kind h⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- A nonzero code is a cons cell or of principal shape (`kind` `1`, `2` or `4`). -/
lemma code_cases_ne_zero {c : V} (hc : c ≠ 0) :
    (∃ x s, c = tcCons x s) ∨ (kind c ≠ 0 ∧ kind c ≠ 3) := by
  by_cases h3 : kind c = 3
  · exact Or.inl ⟨_, _, eq_tcCons_of_kind h3⟩
  · exact Or.inr ⟨fun h => hc (kind_eq_zero_iff.mp h), h3⟩

lemma kind_ne_zero_of_top {c : V} (hc : kind c = 1 ∨ kind c = 4) : kind c ≠ 0 := by
  rcases hc with h | h <;> simp [h]

lemma kind_ne_three_of_top {c : V} (hc : kind c = 1 ∨ kind c = 4) : kind c ≠ 3 := by
  rcases hc with h | h <;> simp [h]

lemma ne_zero_of_kind_ne_zero {c : V} (h : kind c ≠ 0) : c ≠ 0 := by
  rintro rfl; simp at h

/-! ### The clauses of the order at all codes -/

lemma iltb_zero_right (c : V) : iltb c (0 : V) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact iltb_zero_zero
  · exact iltb_pos_zero hc

lemma not_iltb_zero_right (c : V) : iltb c (0 : V) ≠ 1 := by
  rw [iltb_zero_right]; exact zero_ne_one

lemma iltb_cons_prin' (x s : V) {c : V} (h0 : kind c ≠ 0) (h3 : kind c ≠ 3) :
    iltb (tcCons x s) c = iltb x c := by
  obtain ⟨S, h, -, -, hr⟩ := cmp_unfold (tcCons x s) c
  rw [h, ltStep]
  simp only [kind_tcCons]
  simp [h0, h3, ltCP, (hr x c (pair_lt_pair_left (hd_lt_tcCons x s) c)).1]

lemma iltb_prin_cons' {c : V} (h0 : kind c ≠ 0) (h3 : kind c ≠ 3) (y t : V) :
    iltb c (tcCons y t) = bor (iltb c y) (beq c y) := by
  obtain ⟨S, h, -, -, hr⟩ := cmp_unfold c (tcCons y t)
  rw [h, ltStep]
  simp only [kind_tcCons]
  simp [h0, h3, ltPC, (hr c y (pair_lt_pair_right c (hd_lt_tcCons y t))).1]

lemma iltb_theta_top (a : V) {c : V} (hc : kind c = 1 ∨ kind c = 4) :
    iltb (tcTheta a) c = 1 := by
  obtain ⟨S, h, -⟩ := cmp_unfold (tcTheta a) c
  rw [h, ltStep]
  rcases hc with hc | hc <;> simp [hc]

lemma iltb_top_prin {c d : V} (hc : kind c = 1 ∨ kind c = 4) (h0 : kind d ≠ 0)
    (h3 : kind d ≠ 3) : iltb c d = 0 := by
  obtain ⟨S, h, -⟩ := cmp_unfold c d
  rw [h, ltStep]
  rcases hc with hc | hc <;> simp [hc, h0, h3]

lemma iltb_top_theta {c : V} (hc : kind c = 1 ∨ kind c = 4) (a : V) :
    iltb c (tcTheta a) = 0 :=
  iltb_top_prin hc (by simp) (by simp)

lemma iall_top {c : V} (hc : kind c = 1 ∨ kind c = 4) (x : V) : iall c x = 1 := by
  obtain ⟨S, -, h, -⟩ := cmp_unfold c x
  rw [h, alStep]
  rcases hc with hc | hc <;> simp [hc]

lemma iex_top (x : V) {c : V} (hc : kind c = 1 ∨ kind c = 4) : iex x c = 0 := by
  obtain ⟨S, -, -, h, -⟩ := cmp_unfold x c
  rw [h, exStep]
  rcases hc with hc | hc <;> simp [hc]

lemma iinE_top (g : V) {c : V} (hc : kind c = 1 ∨ kind c = 4) : iinE g c = 0 := by
  obtain ⟨S, h, -⟩ := iinE_unfold g c
  rw [h, inEStep]
  rcases hc with hc | hc <;> simp [hc]

@[simp] lemma iinE_zero (g : V) : iinE g (0 : V) = 0 := iinE_of_kind g (Or.inl kind_zero)

@[simp] lemma iall_zero (x : V) : iall (0 : V) x = 1 := iall_of_kind (Or.inl kind_zero) x

@[simp] lemma iex_zero (x : V) : iex x (0 : V) = 0 := iex_of_kind x (Or.inl kind_zero)

@[simp] lemma iltb_zero_tcCons (x s : V) : iltb (0 : V) (tcCons x s) = 1 :=
  iltb_zero_pos (tcCons_ne_zero x s)

@[simp] lemma iltb_zero_tcTheta (a : V) : iltb (0 : V) (tcTheta a) = 1 :=
  iltb_zero_pos (tcTheta_ne_zero a)

lemma iltb_theta_cons (a y t : V) :
    iltb (tcTheta a) (tcCons y t) = bor (iltb (tcTheta a) y) (beq (tcTheta a) y) :=
  iltb_prin_cons' (by simp) (by simp) y t

lemma iltb_cons_theta (x s a : V) : iltb (tcCons x s) (tcTheta a) = iltb x (tcTheta a) :=
  iltb_cons_prin' x s (by simp) (by simp)

/-! ### Coefficient sets -/

/-- Every element of `E(c)` is a `ϑ`-code `≤ c`. -/
lemma iinE_bound (g : V) : ∀ c : V, iinE g c = 1 → g ≤ c ∧ kind g = 2 := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    intro h
    rcases code_cases c with rfl | ⟨x, s, rfl⟩ | ⟨a, rfl⟩ | hk
    · simp at h
    · rw [iinE_tcCons, bor_eq_one] at h
      rcases h with h | h
      · obtain ⟨h1, h2⟩ := ih x (hd_lt_tcCons x s) h
        exact ⟨h1.trans (hd_lt_tcCons x s).le, h2⟩
      · obtain ⟨h1, h2⟩ := ih s (tl_lt_tcCons x s) h
        exact ⟨h1.trans (tl_lt_tcCons x s).le, h2⟩
    · rw [iinE_tcTheta, beq_eq_one] at h
      subst h
      simp
    · rw [iinE_top g hk] at h; simp at h

lemma le_of_iinE {g c : V} (h : iinE g c = 1) : g ≤ c := (iinE_bound g c h).1

lemma kind_of_iinE {g c : V} (h : iinE g c = 1) : kind g = 2 := (iinE_bound g c h).2

lemma eq_tcTheta_of_iinE {g c : V} (h : iinE g c = 1) : g = tcTheta (tcArg g) :=
  eq_tcTheta_of_kind (kind_of_iinE h)

@[simp] lemma iinE_tcTheta_iff (g a : V) : iinE g (tcTheta a) = 1 ↔ g = tcTheta a := by
  rw [iinE_tcTheta, beq_eq_one]

lemma iinE_tcCons_iff (g x s : V) :
    iinE g (tcCons x s) = 1 ↔ iinE g x = 1 ∨ iinE g s = 1 := by
  rw [iinE_tcCons, bor_eq_one]

/-- The `all` flag, bounded form. -/
lemma iall_iff_bdd (x : V) :
    ∀ c : V, iall c x = 1 ↔ ∀ g ≤ c, iinE g c = 1 → iltb g x = 1 := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    rcases code_cases c with rfl | ⟨y, t, rfl⟩ | ⟨a, rfl⟩ | hk
    · simp
    · rw [iall_cons, band_eq_one, ih y (hd_lt_tcCons y t), ih t (tl_lt_tcCons y t)]
      constructor
      · rintro ⟨h1, h2⟩ g _ hg
        rcases (iinE_tcCons_iff g y t).mp hg with hg | hg
        · exact h1 g (le_of_iinE hg) hg
        · exact h2 g (le_of_iinE hg) hg
      · intro h
        refine ⟨fun g _ hg => ?_, fun g _ hg => ?_⟩
        · exact h g ((le_of_iinE hg).trans (hd_lt_tcCons y t).le)
            ((iinE_tcCons_iff g y t).mpr (Or.inl hg))
        · exact h g ((le_of_iinE hg).trans (tl_lt_tcCons y t).le)
            ((iinE_tcCons_iff g y t).mpr (Or.inr hg))
    · rw [iall_theta]
      constructor
      · intro h g _ hg
        rw [(iinE_tcTheta_iff g a).mp hg]; exact h
      · intro h
        exact h _ le_rfl ((iinE_tcTheta_iff _ a).mpr rfl)
    · rw [iall_top hk]
      simp only [true_iff]
      intro g _ hg
      rw [iinE_top g hk] at hg; simp at hg

/-- **The `all` flag**: `iall c x = 1` iff every element of `E(c)` is `≺ x`. -/
lemma iall_iff (c x : V) : iall c x = 1 ↔ ∀ g, iinE g c = 1 → iltb g x = 1 := by
  rw [iall_iff_bdd x c]
  exact ⟨fun h g hg => h g (le_of_iinE hg) hg, fun h g _ hg => h g hg⟩

/-- The `ex` flag, bounded form. -/
lemma iex_iff_bdd (x : V) :
    ∀ c : V, iex x c = 1 ↔ ∃ g ≤ c, iinE g c = 1 ∧ (iltb x g = 1 ∨ x = g) := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    rcases code_cases c with rfl | ⟨y, t, rfl⟩ | ⟨a, rfl⟩ | hk
    · simp
    · rw [iex_cons, bor_eq_one, ih y (hd_lt_tcCons y t), ih t (tl_lt_tcCons y t)]
      constructor
      · rintro (⟨g, _, hg, h⟩ | ⟨g, _, hg, h⟩)
        · exact ⟨g, (le_of_iinE hg).trans (hd_lt_tcCons y t).le,
            (iinE_tcCons_iff g y t).mpr (Or.inl hg), h⟩
        · exact ⟨g, (le_of_iinE hg).trans (tl_lt_tcCons y t).le,
            (iinE_tcCons_iff g y t).mpr (Or.inr hg), h⟩
      · rintro ⟨g, _, hg, h⟩
        rcases (iinE_tcCons_iff g y t).mp hg with hg | hg
        · exact Or.inl ⟨g, le_of_iinE hg, hg, h⟩
        · exact Or.inr ⟨g, le_of_iinE hg, hg, h⟩
    · rw [iex_theta, bor_eq_one, beq_eq_one]
      constructor
      · intro h
        exact ⟨tcTheta a, le_rfl, (iinE_tcTheta_iff _ a).mpr rfl, h⟩
      · rintro ⟨g, _, hg, h⟩
        rwa [(iinE_tcTheta_iff g a).mp hg] at h
    · rw [iex_top x hk]
      simp only [zero_ne_one, false_iff, not_exists, not_and]
      intro g _ hg
      rw [iinE_top g hk] at hg; simp at hg

/-- **The `ex` flag**: `iex x c = 1` iff `x ≼ γ` for some element `γ` of `E(c)`. -/
lemma iex_iff (x c : V) : iex x c = 1 ↔ ∃ g, iinE g c = 1 ∧ (iltb x g = 1 ∨ x = g) := by
  rw [iex_iff_bdd x c]
  exact ⟨fun ⟨g, _, h⟩ => ⟨g, h⟩, fun ⟨g, h⟩ => ⟨g, le_of_iinE h.1, h⟩⟩

/-- The `ϑ`-`ϑ` clause of the order, with the quantifier flags unfolded. -/
lemma iltb_theta_theta_iff (a b : V) :
    iltb (tcTheta a) (tcTheta b) = 1 ↔
      (iltb a b = 1 ∧ ∀ g, iinE g a = 1 → iltb g (tcTheta b) = 1) ∨
        ∃ g, iinE g b = 1 ∧ (iltb (tcTheta a) g = 1 ∨ tcTheta a = g) := by
  rw [iltb_theta_theta, bor_eq_one, band_eq_one, iall_iff, iex_iff]

/-- `E(α) ≺ ϑ α` (Freund, Exercise 3.2(a)). -/
lemma lt_theta_of_iinE {g a : V} (h : iinE g a = 1) : iltb g (tcTheta a) = 1 := by
  rw [eq_tcTheta_of_iinE h, iltb_theta_theta_iff]
  exact Or.inr ⟨g, h, Or.inr (eq_tcTheta_of_iinE h).symm⟩

/-! ### Transitivity -/

private lemma sum3_lt_of {x y z x' y' z' : V} (hx : x' ≤ x) (hy : y' ≤ y) (hz : z' ≤ z)
    (hs : x' < x ∨ y' < y ∨ z' < z) : x' + y' + z' < x + y + z := by
  rcases hs with h | h | h
  · exact add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le h hy) hz
  · exact add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt hx h) hz
  · exact add_lt_add_of_le_of_lt (add_le_add hx hy) h

lemma iltb_trans_aux : ∀ w : V, ∀ a ≤ w, ∀ b ≤ w, ∀ c ≤ w, a + b + c ≤ w →
    iltb a b = 1 → iltb b c = 1 → iltb a c = 1 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro a _ b _ c _ hsum hab hbc
    have T : ∀ {x y z : V}, x + y + z < a + b + c →
        iltb x y = 1 → iltb y z = 1 → iltb x z = 1 :=
      fun {x y z} hlt => ih (x + y + z) (lt_of_lt_of_le hlt hsum)
        x (le_trans le_self_add le_self_add) y (le_trans le_add_self le_self_add)
        z le_add_self le_rfl
    have TL : ∀ {x y z : V}, x + y + z < a + b + c →
        (iltb x y = 1 ∨ x = y) → iltb y z = 1 → iltb x z = 1 := by
      intro x y z h h1 h2
      rcases h1 with h1 | rfl
      · exact T h h1 h2
      · exact h2
    have TR : ∀ {x y z : V}, x + y + z < a + b + c →
        iltb x y = 1 → (iltb y z = 1 ∨ y = z) → iltb x z = 1 := by
      intro x y z h h1 h2
      rcases h2 with h2 | rfl
      · exact T h h1 h2
      · exact h1
    have hb0 : b ≠ 0 := by rintro rfl; exact not_iltb_zero_right a hab
    have hc0 : c ≠ 0 := by rintro rfl; exact not_iltb_zero_right b hbc
    rcases eq_or_ne a 0 with rfl | ha0
    · exact iltb_zero_pos hc0
    rcases code_cases_ne_zero ha0 with ⟨x, xs, rfl⟩ | ⟨ha0', ha3⟩ <;>
    rcases code_cases_ne_zero hb0 with ⟨y, ys, rfl⟩ | ⟨hb0', hb3⟩ <;>
    rcases code_cases_ne_zero hc0 with ⟨z, zs, rfl⟩ | ⟨hc0', hc3⟩
    -- sum, sum, sum
    · rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at hab hbc ⊢
      rcases hab with h1 | ⟨rfl, h1⟩ <;> rcases hbc with h2 | ⟨rfl, h2⟩
      · exact Or.inl (T (sum3_lt_of (hd_lt_tcCons x xs).le (hd_lt_tcCons y ys).le
          (hd_lt_tcCons z zs).le (Or.inl (hd_lt_tcCons x xs))) h1 h2)
      · exact Or.inl h1
      · exact Or.inl h2
      · exact Or.inr ⟨rfl, T (sum3_lt_of (tl_lt_tcCons x xs).le (tl_lt_tcCons x ys).le
          (tl_lt_tcCons x zs).le (Or.inl (tl_lt_tcCons x xs))) h1 h2⟩
    -- sum, sum, principal
    · rw [iltb_cons_prin' _ _ hc0' hc3] at hbc ⊢
      rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at hab
      rcases hab with h | ⟨rfl, _⟩
      · exact T (sum3_lt_of (hd_lt_tcCons x xs).le (hd_lt_tcCons y ys).le le_rfl
          (Or.inl (hd_lt_tcCons x xs))) h hbc
      · exact hbc
    -- sum, principal, sum
    · rw [iltb_cons_prin' _ _ hb0' hb3] at hab
      rw [iltb_prin_cons' hb0' hb3, bor_eq_one, beq_eq_one] at hbc
      rw [iltb_cons_cons, bor_eq_one]
      exact Or.inl (TR (sum3_lt_of (hd_lt_tcCons x xs).le le_rfl (hd_lt_tcCons z zs).le
        (Or.inl (hd_lt_tcCons x xs))) hab hbc)
    -- sum, principal, principal
    · rw [iltb_cons_prin' _ _ hb0' hb3] at hab
      rw [iltb_cons_prin' _ _ hc0' hc3]
      exact T (sum3_lt_of (hd_lt_tcCons x xs).le le_rfl le_rfl
        (Or.inl (hd_lt_tcCons x xs))) hab hbc
    -- principal, sum, sum
    · rw [iltb_prin_cons' ha0' ha3, bor_eq_one, beq_eq_one] at hab ⊢
      rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at hbc
      rcases hbc with h | ⟨rfl, _⟩
      · exact Or.inl (TL (sum3_lt_of le_rfl (hd_lt_tcCons y ys).le (hd_lt_tcCons z zs).le
          (Or.inr (Or.inl (hd_lt_tcCons y ys)))) hab h)
      · exact hab
    -- principal, sum, principal
    · rw [iltb_prin_cons' ha0' ha3, bor_eq_one, beq_eq_one] at hab
      rw [iltb_cons_prin' _ _ hc0' hc3] at hbc
      exact TL (sum3_lt_of le_rfl (hd_lt_tcCons y ys).le le_rfl
        (Or.inr (Or.inl (hd_lt_tcCons y ys)))) hab hbc
    -- principal, principal, sum
    · rw [iltb_prin_cons' hb0' hb3, bor_eq_one, beq_eq_one] at hbc
      rw [iltb_prin_cons' ha0' ha3, bor_eq_one]
      exact Or.inl (TR (sum3_lt_of le_rfl le_rfl (hd_lt_tcCons z zs).le
        (Or.inr (Or.inr (hd_lt_tcCons z zs)))) hab hbc)
    -- principal, principal, principal
    · rcases code_cases a with rfl | ⟨_, _, rfl⟩ | ⟨a, rfl⟩ | hka
      · exact absurd rfl ha0
      · simp at ha3
      · rcases code_cases b with rfl | ⟨_, _, rfl⟩ | ⟨b, rfl⟩ | hkb
        · exact absurd rfl hb0
        · simp at hb3
        · rcases code_cases c with rfl | ⟨_, _, rfl⟩ | ⟨c, rfl⟩ | hkc
          · exact absurd rfl hc0
          · simp at hc3
          · -- the ϑ-ϑ-ϑ case
            have hbc' := hbc
            have hab' := hab
            rw [iltb_theta_theta_iff] at hab hbc ⊢
            rcases hbc with ⟨hbc1, hbc2⟩ | ⟨d, hd, hbd⟩
            · rcases hab with ⟨hab1, hab2⟩ | ⟨d, hd, had⟩
              · refine Or.inl ⟨T (sum3_lt_of (lt_tcTheta a).le (lt_tcTheta b).le
                  (lt_tcTheta c).le (Or.inl (lt_tcTheta a))) hab1 hbc1, fun g hg => ?_⟩
                have hga : g < tcTheta a := lt_of_le_of_lt (le_of_iinE hg) (lt_tcTheta a)
                exact T (sum3_lt_of hga.le le_rfl le_rfl (Or.inl hga)) (hab2 g hg) hbc'
              · have hdb : d < tcTheta b := lt_of_le_of_lt (le_of_iinE hd) (lt_tcTheta b)
                exact (iltb_theta_theta_iff a c).mp
                  (TL (sum3_lt_of le_rfl hdb.le le_rfl (Or.inr (Or.inl hdb))) had (hbc2 d hd))
            · have hdc : d < tcTheta c := lt_of_le_of_lt (le_of_iinE hd) (lt_tcTheta c)
              exact Or.inr ⟨d, hd, Or.inl (TR (sum3_lt_of le_rfl le_rfl hdc.le
                (Or.inr (Or.inr hdc))) hab' hbd)⟩
          · exact iltb_theta_top a hkc
        · rw [iltb_top_prin hkb hc0' hc3] at hbc; simp at hbc
      · rw [iltb_top_prin hka hb0' hb3] at hab; simp at hab

/-- **Transitivity of the internal order**, on all codes. -/
lemma iltb_trans {a b c : V} (hab : iltb a b = 1) (hbc : iltb b c = 1) : iltb a c = 1 :=
  iltb_trans_aux (a + b + c) a (le_trans le_self_add le_self_add)
    b (le_trans le_add_self le_self_add) c le_add_self le_rfl hab hbc

lemma iltb_of_le_of_lt {a b c : V} (hab : iltb a b = 1 ∨ a = b) (hbc : iltb b c = 1) :
    iltb a c = 1 := by
  rcases hab with hab | rfl
  · exact iltb_trans hab hbc
  · exact hbc

lemma iltb_of_lt_of_le {a b c : V} (hab : iltb a b = 1) (hbc : iltb b c = 1 ∨ b = c) :
    iltb a c = 1 := by
  rcases hbc with hbc | rfl
  · exact iltb_trans hab hbc
  · exact hab

lemma ile_trans {a b c : V} (hab : iltb a b = 1 ∨ a = b) (hbc : iltb b c = 1 ∨ b = c) :
    iltb a c = 1 ∨ a = c := by
  rcases hab with hab | rfl
  · exact Or.inl (iltb_of_lt_of_le hab hbc)
  · exact hbc

/-! ### Irreflexivity -/

lemma iltb_irrefl_aux : ∀ a : V, iltb a a ≠ 1 := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a ih =>
    intro h
    rcases code_cases a with rfl | ⟨x, s, rfl⟩ | ⟨a, rfl⟩ | hk
    · exact not_iltb_zero_right 0 h
    · rw [iltb_cons_cons, bor_eq_one, band_eq_one] at h
      rcases h with h | ⟨-, h⟩
      · exact ih x (hd_lt_tcCons x s) h
      · exact ih s (tl_lt_tcCons x s) h
    · rcases (iltb_theta_theta_iff a a).mp h with ⟨h1, -⟩ | ⟨g, hg, h1⟩
      · exact ih a (lt_tcTheta a) h1
      · have hga : g < tcTheta a := lt_of_le_of_lt (le_of_iinE hg) (lt_tcTheta a)
        rcases h1 with h1 | h1
        · exact ih g hga (iltb_trans (lt_theta_of_iinE hg) h1)
        · exact absurd h1.symm (ne_of_lt hga)
    · rw [iltb_top_prin hk (kind_ne_zero_of_top hk) (kind_ne_three_of_top hk)] at h
      simp at h

/-- **Irreflexivity of the internal order**, on all codes. -/
lemma iltb_irrefl (a : V) : iltb a a ≠ 1 := iltb_irrefl_aux a

lemma ne_of_iltb {a b : V} (h : iltb a b = 1) : a ≠ b := by
  rintro rfl; exact iltb_irrefl a h

/-- Asymmetry of the internal order. -/
lemma iltb_asymm {a b : V} (h : iltb a b = 1) : iltb b a ≠ 1 :=
  fun h' => iltb_irrefl a (iltb_trans h h')

lemma not_ile_of_iltb {a b : V} (h : iltb a b = 1) : ¬ (iltb b a = 1 ∨ b = a) := by
  rintro (h' | rfl)
  · exact iltb_asymm h h'
  · exact iltb_irrefl b h

lemma ile_antisymm {a b : V} (hab : iltb a b = 1 ∨ a = b) (hba : iltb b a = 1 ∨ b = a) :
    a = b := by
  rcases hab with hab | rfl
  · exact absurd hba (not_ile_of_iltb hab)
  · rfl

/-- `ϑ α ≼ δ ∈ E(α)` is impossible. -/
lemma not_theta_le_of_iinE {g a : V} (h : iinE g a = 1) :
    ¬ (iltb (tcTheta a) g = 1 ∨ tcTheta a = g) :=
  not_ile_of_iltb (lt_theta_of_iinE h)

/-! ### Codes of terms and of normal forms -/

/-- The shapes of codes of terms. -/
lemma isTerm_cases {c : V} (h : isTerm c) :
    c = 0 ∨ c = 1 ∨ (∃ a, c = tcTheta a ∧ isTerm a) ∨
      (∃ x s, c = tcCons x s ∧ isTerm x ∧ isTerm s ∧ sumK s = 1) := by
  unfold isTerm at h
  rcases kind_cases c with hk | hk | hk | hk | hk
  · exact Or.inl (kind_eq_zero_iff.mp hk)
  · rw [isTermb_kind_one hk, beq_eq_one] at h
    exact Or.inr (Or.inl (eq_one_of_kind hk h))
  · rw [eq_tcTheta_of_kind hk, isTermb_tcTheta] at h
    exact Or.inr (Or.inr (Or.inl ⟨_, eq_tcTheta_of_kind hk, h⟩))
  · rw [eq_tcCons_of_kind hk, isTermb_tcCons, band_eq_one, band_eq_one] at h
    exact Or.inr (Or.inr (Or.inr ⟨_, _, eq_tcCons_of_kind hk, h.1, h.2.1, h.2.2⟩))
  · rw [isTermb_kind_four hk] at h; simp at h

@[simp] lemma isTerm_zero : isTerm (0 : V) := by simp [isTerm]

@[simp] lemma isTerm_one : isTerm (1 : V) := by simp [isTerm]

@[simp] lemma isTerm_tcTheta_iff (a : V) : isTerm (tcTheta a) ↔ isTerm a := by
  simp [isTerm]

lemma isTerm_tcCons_iff (x s : V) :
    isTerm (tcCons x s) ↔ isTerm x ∧ isTerm s ∧ sumK s = 1 := by
  simp [isTerm]

/-- The elements of `E(c)` of a term code are term codes. -/
lemma isTerm_of_iinE (g : V) : ∀ c : V, isTerm c → iinE g c = 1 → isTerm g := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    intro hc h
    rcases isTerm_cases hc with rfl | rfl | ⟨a, rfl, _⟩ | ⟨x, s, rfl, hx, hs, _⟩
    · simp at h
    · rw [iinE_top g (Or.inl kind_one)] at h; simp at h
    · rw [(iinE_tcTheta_iff g a).mp h]; exact hc
    · rcases (iinE_tcCons_iff g x s).mp h with h | h
      · exact ih x (hd_lt_tcCons x s) hx h
      · exact ih s (tl_lt_tcCons x s) hs h

/-- The shapes of codes whose hereditary normality flag is set. -/
lemma nfA_cases {c : V} (h : nfA c = 1) :
    c = 0 ∨ c = 1 ∨ (∃ a, c = tcTheta a ∧ isNF a) ∨
      (∃ x s, c = tcCons x s ∧ isNF x ∧ nfA s = 1 ∧ sumK s = 1 ∧
        descOk (tcCons x s) = 1) := by
  rcases kind_cases c with hk | hk | hk | hk | hk
  · exact Or.inl (kind_eq_zero_iff.mp hk)
  · rw [nfA_kind_one hk, beq_eq_one] at h
    exact Or.inr (Or.inl (eq_one_of_kind hk h))
  · rw [eq_tcTheta_of_kind hk, nfA_tcTheta] at h
    exact Or.inr (Or.inr (Or.inl ⟨_, eq_tcTheta_of_kind hk, h⟩))
  · have e := eq_tcCons_of_kind hk
    rw [e, nfA_tcCons, band_eq_one, band_eq_one, band_eq_one] at h
    exact Or.inr (Or.inr (Or.inr ⟨_, _, e, h.1, h.2.1, h.2.2.1, h.2.2.2⟩))
  · rw [nfA_kind_four hk] at h; simp at h

lemma nfA_of_isNF {c : V} (h : isNF c) : nfA c = 1 := by
  unfold isNF isNFb at h; rw [band_eq_one] at h; exact h.1

lemma sok_of_isNF {c : V} (h : isNF c) : sok c = 1 := by
  unfold isNF isNFb at h; rw [band_eq_one] at h; exact h.2

lemma isTerm_of_nfA_aux : ∀ c : V, nfA c = 1 → isTerm c := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    intro h
    rcases nfA_cases h with rfl | rfl | ⟨a, rfl, ha⟩ | ⟨x, s, rfl, hx, hs, hk, -⟩
    · simp
    · simp
    · exact (isTerm_tcTheta_iff a).mpr (ih a (lt_tcTheta a) (nfA_of_isNF ha))
    · exact (isTerm_tcCons_iff x s).mpr
        ⟨ih x (hd_lt_tcCons x s) (nfA_of_isNF hx), ih s (tl_lt_tcCons x s) hs, hk⟩

/-- Codes of normal forms are codes of terms. -/
lemma isTerm_of_isNF {c : V} (h : isNF c) : isTerm c :=
  isTerm_of_nfA_aux c (nfA_of_isNF h)

@[simp] lemma isNF_zero : isNF (0 : V) := by simp [isNF, isNFb]

@[simp] lemma isNF_one : isNF (1 : V) := by simp [isNF, isNFb]

@[simp] lemma isNF_tcTheta_iff (a : V) : isNF (tcTheta a) ↔ isNF a := by
  simp [isNF, isNFb]

/-! ### Trichotomy -/

private lemma sum2_lt_of {x y x' y' : V} (hx : x' ≤ x) (hy : y' ≤ y)
    (hs : x' < x ∨ y' < y) : x' + y' < x + y := by
  rcases hs with h | h
  · exact add_lt_add_of_lt_of_le h hy
  · exact add_lt_add_of_le_of_lt hx h

private lemma tri_symm {x y : V} (h : iltb x y = 1 ∨ x = y ∨ iltb y x = 1) :
    iltb y x = 1 ∨ y = x ∨ iltb x y = 1 := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inl h

/-- The trichotomy of a principal code against a cons cell, from that against its head. -/
private lemma prin_cons_tri {p y ys : V} (h0 : kind p ≠ 0) (h3 : kind p ≠ 3)
    (C : iltb p y = 1 ∨ p = y ∨ iltb y p = 1) :
    iltb p (tcCons y ys) = 1 ∨ p = tcCons y ys ∨ iltb (tcCons y ys) p = 1 := by
  rw [iltb_prin_cons' h0 h3, bor_eq_one, beq_eq_one, iltb_cons_prin' y ys h0 h3]
  rcases C with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

/-- The trichotomy of two `ϑ`-codes with `α ≺ β`, from the trichotomy of the elements of
`E(α)` against `ϑ β`. -/
private lemma theta_tri_of_lt {a b : V} (h : iltb a b = 1)
    (C : ∀ g, iinE g a = 1 → iltb g (tcTheta b) = 1 ∨ g = tcTheta b ∨
      iltb (tcTheta b) g = 1) :
    iltb (tcTheta a) (tcTheta b) = 1 ∨ iltb (tcTheta b) (tcTheta a) = 1 := by
  by_cases hE : ∀ g, iinE g a = 1 → iltb g (tcTheta b) = 1
  · exact Or.inl ((iltb_theta_theta_iff a b).mpr (Or.inl ⟨h, hE⟩))
  · obtain ⟨g, hg, hgb⟩ : ∃ g, iinE g a = 1 ∧ iltb g (tcTheta b) ≠ 1 := by
      by_contra hc
      exact hE (fun g hg => by_contra fun h' => hc ⟨g, hg, h'⟩)
    rcases C g hg with h' | h' | h'
    · exact absurd h' hgb
    · exact Or.inr ((iltb_theta_theta_iff b a).mpr (Or.inr ⟨g, hg, Or.inr h'.symm⟩))
    · exact Or.inr ((iltb_theta_theta_iff b a).mpr (Or.inr ⟨g, hg, Or.inl h'⟩))

lemma iltb_trichotomy_aux : ∀ w : V, ∀ a ≤ w, ∀ b ≤ w, a + b ≤ w → isTerm a → isTerm b →
    iltb a b = 1 ∨ a = b ∨ iltb b a = 1 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro a _ b _ hsum ha hb
    have C : ∀ {x y : V}, x + y < a + b → isTerm x → isTerm y →
        iltb x y = 1 ∨ x = y ∨ iltb y x = 1 :=
      fun {x y} hlt => ih (x + y) (lt_of_lt_of_le hlt hsum) x le_self_add y le_add_self le_rfl
    have k1 : kind (1 : V) ≠ 0 := by simp
    have k1' : kind (1 : V) ≠ 3 := by simp
    have kt : ∀ a : V, kind (tcTheta a) ≠ 0 := fun a => by simp
    have kt' : ∀ a : V, kind (tcTheta a) ≠ 3 := fun a => by simp
    rcases isTerm_cases ha with rfl | rfl | ⟨a, rfl, ha'⟩ | ⟨x, xs, rfl, hx, hxs, -⟩ <;>
    rcases isTerm_cases hb with rfl | rfl | ⟨b, rfl, hb'⟩ | ⟨y, ys, rfl, hy, hys, -⟩
    -- `0` against anything
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (iltb_zero_pos _root_.one_ne_zero)
    · exact Or.inl (iltb_zero_tcTheta b)
    · exact Or.inl (iltb_zero_tcCons y ys)
    -- `Ω`
    · exact Or.inr (Or.inr (iltb_zero_pos _root_.one_ne_zero))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (iltb_theta_top b (Or.inl kind_one)))
    · exact prin_cons_tri k1 k1' (C (sum2_lt_of le_rfl (hd_lt_tcCons y ys).le
        (Or.inr (hd_lt_tcCons y ys))) isTerm_one hy)
    -- `ϑ`
    · exact Or.inr (Or.inr (iltb_zero_tcTheta a))
    · exact Or.inl (iltb_theta_top a (Or.inl kind_one))
    · rcases C (sum2_lt_of (lt_tcTheta a).le (lt_tcTheta b).le (Or.inl (lt_tcTheta a)))
        ha' hb' with h | rfl | h
      · rcases theta_tri_of_lt h (fun g hg => by
          have hga : g < tcTheta a := lt_of_le_of_lt (le_of_iinE hg) (lt_tcTheta a)
          exact C (sum2_lt_of hga.le le_rfl (Or.inl hga)) (isTerm_of_iinE g a ha' hg) hb)
          with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl rfl)
      · rcases theta_tri_of_lt h (fun g hg => by
          have hgb : g < tcTheta b := lt_of_le_of_lt (le_of_iinE hg) (lt_tcTheta b)
          exact tri_symm (C (sum2_lt_of le_rfl hgb.le (Or.inr hgb)) ha
            (isTerm_of_iinE g b hb' hg)))
          with h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
    · exact prin_cons_tri (kt a) (kt' a) (C (sum2_lt_of le_rfl (hd_lt_tcCons y ys).le
        (Or.inr (hd_lt_tcCons y ys))) ha hy)
    -- sums
    · exact Or.inr (Or.inr (iltb_zero_tcCons x xs))
    · rcases prin_cons_tri k1 k1' (ys := xs) (tri_symm (C (sum2_lt_of (hd_lt_tcCons x xs).le
        le_rfl (Or.inl (hd_lt_tcCons x xs))) hx isTerm_one)) with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
    · rcases prin_cons_tri (kt b) (kt' b) (ys := xs) (tri_symm (C (sum2_lt_of
        (hd_lt_tcCons x xs).le le_rfl (Or.inl (hd_lt_tcCons x xs))) hx hb)) with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
    · rw [iltb_cons_cons, iltb_cons_cons, bor_eq_one, bor_eq_one, band_eq_one, band_eq_one,
        beq_eq_one, beq_eq_one]
      rcases C (sum2_lt_of (hd_lt_tcCons x xs).le (hd_lt_tcCons y ys).le
        (Or.inl (hd_lt_tcCons x xs))) hx hy with h | rfl | h
      · exact Or.inl (Or.inl h)
      · rcases C (sum2_lt_of (tl_lt_tcCons x xs).le (tl_lt_tcCons x ys).le
          (Or.inl (tl_lt_tcCons x xs))) hxs hys with h | rfl | h
        · exact Or.inl (Or.inr ⟨rfl, h⟩)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
      · exact Or.inr (Or.inr (Or.inl h))

/-- **Trichotomy of the internal order** on codes of terms. -/
lemma iltb_trichotomy {a b : V} (ha : isTerm a) (hb : isTerm b) :
    iltb a b = 1 ∨ a = b ∨ iltb b a = 1 :=
  iltb_trichotomy_aux (a + b) a le_self_add b le_add_self le_rfl ha hb

/-- **Totality of the internal order** on codes of normal forms. -/
lemma iltb_trichotomy_nf {a b : V} (ha : isNF a) (hb : isNF b) :
    iltb a b = 1 ∨ a = b ∨ iltb b a = 1 :=
  iltb_trichotomy (isTerm_of_isNF ha) (isTerm_of_isNF hb)

lemma ile_total {a b : V} (ha : isTerm a) (hb : isTerm b) :
    (iltb a b = 1 ∨ a = b) ∨ (iltb b a = 1 ∨ b = a) := by
  rcases iltb_trichotomy ha hb with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)

lemma ile_of_not_iltb {a b : V} (ha : isTerm a) (hb : isTerm b) (h : iltb a b ≠ 1) :
    iltb b a = 1 ∨ b = a := by
  rcases iltb_trichotomy ha hb with h' | h' | h'
  · exact absurd h' h
  · exact Or.inr h'.symm
  · exact Or.inl h'

lemma not_iltb_iff_ile {a b : V} (ha : isTerm a) (hb : isTerm b) :
    iltb a b ≠ 1 ↔ (iltb b a = 1 ∨ b = a) :=
  ⟨ile_of_not_iltb ha hb, fun h h' => not_ile_of_iltb h' h⟩

/-! ### The least code -/

/-- `0` is the least code. -/
lemma iltb_zero_left {c : V} (hc : c ≠ 0) : iltb (0 : V) c = 1 := iltb_zero_pos hc

lemma ile_zero_left (c : V) : iltb (0 : V) c = 1 ∨ (0 : V) = c := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact Or.inr rfl
  · exact Or.inl (iltb_zero_pos hc)

/-- Nothing is below `0`. -/
lemma not_iltb_zero (c : V) : iltb c (0 : V) ≠ 1 := not_iltb_zero_right c

end OrdinalAnalysis.ID1.Internal
