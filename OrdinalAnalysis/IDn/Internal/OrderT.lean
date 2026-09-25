/-
  The order of the coded multi-level ϑ-notation inside models of `IΣ₁`.

  `Order` defines the internal order `iltb` by a course-of-values table and proves that it
  computes `ThetaWTerm.ltb` on standard codes.  Here the order-theoretic facts are proved for
  the codes of terms of an arbitrary model `V` of `IΣ₁`, following the syntactic proofs of
  `Ordinal/ThetaW/Order.lean` by `IΣ₁`-induction (the one-level template is
  `ID1/Internal/Order.lean`).

  The induction measure is the sum of the codes rather than the sum of the lengths: every
  immediate constituent of a code is below it, and so is every element of its coefficient set
  `E_k` (`iinE_bound`).

  A code is `0`, an `Ω`-code, a `ϑ`-code, a cons cell, or of the fifth shape (`kind` `4`, no
  term).  The quantifier flag `iall` of the table is `0` at codes of the fifth shape, so the
  `ϑ_k`-`ϑ_k` clause reads as a statement about `E_k` only for codes of terms
  (`iltb_theta_theta_iff`); all order facts are therefore stated for codes of terms (in
  particular for codes of normal forms, `isTerm_of_isNF`):

  * `iinE_bound` (elements of `E_k(c)` are codes `ϑ_j δ ≤ c` with `j ≤ k`), `iall_iff`,
    `iex_iff` (the two quantifier flags mean what they say), `lt_theta_of_iinE`
    (`E_k(α) ≺ ϑ_k α`), `iltb_theta_theta_iff'` (the clause of two collapses, all levels);
  * `iltb_trans`, `iltb_irrefl`, `iltb_asymm`, `iltb_trichotomy`, `iltb_trichotomy_nf`;
  * `isTerm_cases`, `nfA_cases`, `isTerm_of_isNF`, `isTerm_of_iinE`.
-/
import OrdinalAnalysis.IDn.Internal.Order

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.ID1.Internal (bor band beq bor_eq_one band_eq_one beq_eq_one)

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Definability at every level -/

instance iltb_definable : 𝚺₁-Function₂ (iltb : V → V → V) := iltb_defined.to_definable
instance iltb_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (iltb : V → V → V) :=
  iltb_definable.of_sigmaOne
instance iall_definable : 𝚺₁-Function₃ (iall : V → V → V → V) := iall_defined.to_definable
instance iall_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₃ (iall : V → V → V → V) :=
  iall_definable.of_sigmaOne
instance iex_definable : 𝚺₁-Function₃ (iex : V → V → V → V) := iex_defined.to_definable
instance iex_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₃ (iex : V → V → V → V) :=
  iex_definable.of_sigmaOne
instance sumK_definable : 𝚺₁-Function₁ (sumK : V → V) := sumK_defined.to_definable
instance sumK_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (sumK : V → V) :=
  sumK_definable.of_sigmaOne
instance sok_definable : 𝚺₁-Function₁ (sok : V → V) := sok_defined.to_definable
instance sok_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (sok : V → V) :=
  sok_definable.of_sigmaOne
instance descOk_definable : 𝚺₁-Function₁ (descOk : V → V) := descOk_defined.to_definable
instance descOk_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (descOk : V → V) :=
  descOk_definable.of_sigmaOne
instance nfA_definable : 𝚺₁-Function₁ (nfA : V → V) := nfA_defined.to_definable
instance nfA_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (nfA : V → V) :=
  nfA_definable.of_sigmaOne
instance isNFb_definable : 𝚺₁-Function₁ (isNFb : V → V) := isNFb_defined.to_definable
instance isNFb_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (isNFb : V → V) :=
  isNFb_definable.of_sigmaOne
instance domOk_definable : 𝚺₁-Function₃ (domOk : V → V → V → V) := domOk_defined.to_definable
instance domOk_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₃ (domOk : V → V → V → V) :=
  domOk_definable.of_sigmaOne
instance isDomb_definable : 𝚺₁-Function₁ (isDomb : V → V) := isDomb_defined.to_definable
instance isDomb_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (isDomb : V → V) :=
  isDomb_definable.of_sigmaOne

instance isNF_definable (Γ) (m : ℕ) : Γ-[m + 1]-Predicate (isNF : V → Prop) := by
  unfold isNF; definability

instance isDom_definable (Γ) (m : ℕ) : Γ-[m + 1]-Predicate (isDom : V → Prop) := by
  unfold isDom; definability

/-! ### Shapes of codes -/

/-- Every code is `0`, an `Ω`-code, a `ϑ`-code, a cons cell, or of the fifth shape. -/
lemma code_cases (c : V) :
    c = 0 ∨ (∃ i, c = tcOmega i) ∨ (∃ i a, c = tcTheta i a) ∨ (∃ x s, c = tcCons x s) ∨
      kind c = 4 := by
  rcases kind_cases c with h | h | h | h | h
  · exact Or.inl (kind_eq_zero_iff.mp h)
  · exact Or.inr (Or.inl ⟨_, eq_tcOmega_of_kind h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, eq_tcTheta_of_kind h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, eq_tcCons_of_kind h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

lemma iinE_kind_four (k g : V) {c : V} (hc : kind c = 4) : iinE k g c = 0 := by
  obtain ⟨S, h, -⟩ := iinE_unfold k g c
  rw [h, inEStep]
  simp only [pi₁_pair, pi₂_pair]
  simp [hc]

lemma iinG_kind_four (k x : V) {c : V} (hc : kind c = 4) : iinG k x c = 0 := by
  obtain ⟨S, h, -⟩ := iinG_unfold k x c
  rw [h, inGStep]
  simp only [pi₁_pair, pi₂_pair]
  simp [hc]

lemma iex_kind_four (k x : V) {c : V} (hc : kind c = 4) : iex k x c = 0 := by
  obtain ⟨S, h, -⟩ := iex_unfold k x c
  rw [h]
  simp [exStep, hc]

lemma iinE_cons_iff (k g x s : V) :
    iinE k g (tcCons x s) = 1 ↔ iinE k g x = 1 ∨ iinE k g s = 1 := by
  rw [iinE_tcCons, bor_eq_one]

lemma iinG_cons_iff (k y x s : V) :
    iinG k y (tcCons x s) = 1 ↔ iinG k y x = 1 ∨ iinG k y s = 1 := by
  rw [iinG_tcCons, bor_eq_one]

lemma iinE_theta_le_iff {k j a g : V} (hjk : j ≤ k) :
    iinE k g (tcTheta j a) = 1 ↔ g = tcTheta j a := by
  rw [iinE_tcTheta_of_le hjk, beq_eq_one]

lemma iinG_theta_lt_iff {k j a x : V} (hkj : k < j) :
    iinG k x (tcTheta j a) = 1 ↔ x = a ∨ iinG k x a = 1 := by
  rw [iinG_tcTheta_of_lt hkj, bor_eq_one, beq_eq_one]

@[simp] lemma iinE_at_zero (k g : V) : iinE k g (0 : V) = 0 := iinE_of_kind k g (Or.inl kind_zero)

@[simp] lemma iinG_at_zero (k x : V) : iinG k x (0 : V) = 0 := iinG_of_kind k x (Or.inl kind_zero)

@[simp] lemma iinE_at_tcOmega (k g i : V) : iinE k g (tcOmega i) = 0 :=
  iinE_of_kind k g (Or.inr (kind_tcOmega i))

@[simp] lemma iinG_at_tcOmega (k x i : V) : iinG k x (tcOmega i) = 0 :=
  iinG_of_kind k x (Or.inr (kind_tcOmega i))

/-! ### The clauses of the order between principal codes -/

lemma not_iltb_zero_right (c : V) : iltb c (0 : V) ≠ 1 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [iltb_zero_zero]; simp
  · rw [iltb_pos_zero hc]; simp

lemma iltb_Omega_Omega_iff (i j : V) : iltb (tcOmega i) (tcOmega j) = 1 ↔ i < j := by
  rw [iltb_tcOmega_tcOmega]; split_ifs with h <;> simp [h]

lemma iltb_Omega_theta_iff (i j b : V) : iltb (tcOmega i) (tcTheta j b) = 1 ↔ i < j := by
  rw [iltb_tcOmega_tcTheta]; split_ifs with h <;> simp [h]

lemma iltb_theta_Omega_iff (i a j : V) : iltb (tcTheta i a) (tcOmega j) = 1 ↔ i ≤ j := by
  rw [iltb_tcTheta_tcOmega]; split_ifs with h <;> simp [h]

lemma le_of_iltb_theta_theta {i a j b : V} (h : iltb (tcTheta i a) (tcTheta j b) = 1) :
    i ≤ j := by
  by_contra hji
  rw [iltb_tcTheta_tcTheta_of_gt (not_le.mp hji)] at h
  simp at h

lemma iltb_prin_zero {c : V} (hc : kind c = 1 ∨ kind c = 2) : iltb c (0 : V) = 0 :=
  iltb_pos_zero (by rintro rfl; rcases hc with h | h <;> simp at h)

/-! ### Coefficient sets -/

/-- Every element of `E_k(c)` is a `ϑ`-code `≤ c` of level `≤ k`. -/
lemma iinE_bound (k g : V) : ∀ c : V, iinE k g c = 1 → g ≤ c ∧ kind g = 2 ∧ tcLev g ≤ k := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    intro h
    rcases code_cases c with rfl | ⟨i, rfl⟩ | ⟨j, a, rfl⟩ | ⟨x, s, rfl⟩ | hk
    · simp at h
    · simp at h
    · by_cases hj : j ≤ k
      · rw [iinE_theta_le_iff hj] at h
        subst h
        simp [hj]
      · rw [iinE_tcTheta_of_lt (not_le.mp hj)] at h
        obtain ⟨h1, h2, h3⟩ := ih a (arg_lt_tcTheta j a) h
        exact ⟨h1.trans (arg_lt_tcTheta j a).le, h2, h3⟩
    · rcases (iinE_cons_iff k g x s).mp h with h | h
      · obtain ⟨h1, h2, h3⟩ := ih x (hd_lt_tcCons x s) h
        exact ⟨h1.trans (hd_lt_tcCons x s).le, h2, h3⟩
      · obtain ⟨h1, h2, h3⟩ := ih s (tl_lt_tcCons x s) h
        exact ⟨h1.trans (tl_lt_tcCons x s).le, h2, h3⟩
    · rw [iinE_kind_four k g hk] at h; simp at h

lemma iinE_le {k g c : V} (h : iinE k g c = 1) : g ≤ c := (iinE_bound k g c h).1

/-- An element of `E_k(c)` is a code `ϑ_j δ` with `j ≤ k`. -/
lemma iinE_shape {k g c : V} (h : iinE k g c = 1) :
    ∃ j d, g = tcTheta j d ∧ j ≤ k := by
  obtain ⟨-, h2, h3⟩ := iinE_bound k g c h
  exact ⟨_, _, eq_tcTheta_of_kind h2, h3⟩

/-- Every element of `G_k(c)` is a proper constituent of `c`. -/
lemma iinG_lt (k y : V) : ∀ c : V, iinG k y c = 1 → y < c := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    intro h
    rcases code_cases c with rfl | ⟨i, rfl⟩ | ⟨j, a, rfl⟩ | ⟨x, s, rfl⟩ | hk
    · simp at h
    · simp at h
    · by_cases hj : k < j
      · rcases (iinG_theta_lt_iff hj).mp h with rfl | h
        · exact arg_lt_tcTheta j y
        · exact (ih a (arg_lt_tcTheta j a) h).trans (arg_lt_tcTheta j a)
      · rw [iinG_tcTheta_of_le (not_lt.mp hj)] at h; simp at h
    · rcases (iinG_cons_iff k y x s).mp h with h | h
      · exact (ih x (hd_lt_tcCons x s) h).trans (hd_lt_tcCons x s)
      · exact (ih s (tl_lt_tcCons x s) h).trans (tl_lt_tcCons x s)
    · rw [iinG_kind_four k y hk] at h; simp at h

/-! ### Codes of terms -/

/-- The shapes of codes of terms. -/
lemma isTerm_cases {c : V} (h : isTerm c) :
    c = 0 ∨ (∃ i, c = tcOmega i) ∨ (∃ i a, c = tcTheta i a ∧ isTerm a) ∨
      (∃ x s, c = tcCons x s ∧ isTerm x ∧ isTerm s ∧ sumK s = 1) := by
  unfold isTerm at h
  rcases code_cases c with rfl | ⟨i, rfl⟩ | ⟨i, a, rfl⟩ | ⟨x, s, rfl⟩ | hk
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · rw [isTermb_tcTheta] at h
    exact Or.inr (Or.inr (Or.inl ⟨i, a, rfl, h⟩))
  · rw [isTermb_tcCons, band_eq_one, band_eq_one] at h
    exact Or.inr (Or.inr (Or.inr ⟨x, s, rfl, h.1, h.2.1, h.2.2⟩))
  · rw [isTermb_kind_four hk] at h; simp at h

@[simp] lemma isTerm_at_zero : isTerm (0 : V) := by simp [isTerm]

@[simp] lemma isTerm_tcOmega (i : V) : isTerm (tcOmega i) := by simp [isTerm]

@[simp] lemma isTerm_tcTheta_iff (i a : V) : isTerm (tcTheta i a) ↔ isTerm a := by
  simp [isTerm]

lemma isTerm_tcCons_iff (x s : V) :
    isTerm (tcCons x s) ↔ isTerm x ∧ isTerm s ∧ sumK s = 1 := by
  simp [isTerm]

/-- A nonzero code of a term is a cons cell or principal. -/
lemma isTerm_cases_ne_zero {c : V} (h : isTerm c) (hc : c ≠ 0) :
    (∃ x s, c = tcCons x s ∧ isTerm x ∧ isTerm s ∧ sumK s = 1) ∨
      (kind c = 1 ∨ kind c = 2) := by
  rcases isTerm_cases h with rfl | ⟨i, rfl⟩ | ⟨i, a, rfl, -⟩ | h'
  · exact absurd rfl hc
  · exact Or.inr (Or.inl (kind_tcOmega i))
  · exact Or.inr (Or.inr (kind_tcTheta i a))
  · exact Or.inl h'

/-- The elements of `E_k(c)` of a term code are term codes. -/
lemma isTerm_of_iinE (k g : V) : ∀ c : V, isTerm c → iinE k g c = 1 → isTerm g := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    intro hc h
    rcases isTerm_cases hc with rfl | ⟨i, rfl⟩ | ⟨j, a, rfl, ha⟩ | ⟨x, s, rfl, hx, hs, -⟩
    · simp at h
    · simp at h
    · by_cases hj : j ≤ k
      · rw [iinE_theta_le_iff hj] at h; rw [h]; exact hc
      · rw [iinE_tcTheta_of_lt (not_le.mp hj)] at h
        exact ih a (arg_lt_tcTheta j a) ha h
    · rcases (iinE_cons_iff k g x s).mp h with h | h
      · exact ih x (hd_lt_tcCons x s) hx h
      · exact ih s (tl_lt_tcCons x s) hs h

/-! ### The quantifier flags -/

/-- The `all_k` flag, bounded form. -/
lemma iall_iff_bdd (k x : V) :
    ∀ c : V, isTerm c → (iall k c x = 1 ↔ ∀ g ≤ c, iinE k g c = 1 → iltb g x = 1) := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    intro hc
    rcases isTerm_cases hc with rfl | ⟨i, rfl⟩ | ⟨j, a, rfl, ha⟩ | ⟨y, t, rfl, hy, ht, -⟩
    · rw [iall_of_kind k (Or.inl kind_zero)]
      simp
    · rw [iall_of_kind k (Or.inr (kind_tcOmega i))]
      simp
    · by_cases hj : j ≤ k
      · rw [iall_tcTheta_of_le hj]
        constructor
        · intro h g _ hg
          rw [(iinE_theta_le_iff hj).mp hg]; exact h
        · intro h
          exact h _ le_rfl ((iinE_theta_le_iff hj).mpr rfl)
      · have hkj : k < j := not_le.mp hj
        rw [iall_tcTheta_of_lt hkj, ih a (arg_lt_tcTheta j a) ha]
        constructor
        · intro h g _ hg
          rw [iinE_tcTheta_of_lt hkj] at hg
          exact h g (iinE_le hg) hg
        · intro h g _ hg
          exact h g ((iinE_le hg).trans (arg_lt_tcTheta j a).le)
            (by rw [iinE_tcTheta_of_lt hkj]; exact hg)
    · rw [iall_cons, band_eq_one, ih y (hd_lt_tcCons y t) hy, ih t (tl_lt_tcCons y t) ht]
      constructor
      · rintro ⟨h1, h2⟩ g _ hg
        rcases (iinE_cons_iff k g y t).mp hg with hg | hg
        · exact h1 g (iinE_le hg) hg
        · exact h2 g (iinE_le hg) hg
      · intro h
        refine ⟨fun g _ hg => ?_, fun g _ hg => ?_⟩
        · exact h g ((iinE_le hg).trans (hd_lt_tcCons y t).le)
            ((iinE_cons_iff k g y t).mpr (Or.inl hg))
        · exact h g ((iinE_le hg).trans (tl_lt_tcCons y t).le)
            ((iinE_cons_iff k g y t).mpr (Or.inr hg))

/-- **The `all_k` flag**: at a term code, `iall k c x = 1` iff every element of `E_k(c)` is
`≺ x`. -/
lemma iall_iff {k c : V} (x : V) (hc : isTerm c) :
    iall k c x = 1 ↔ ∀ g, iinE k g c = 1 → iltb g x = 1 := by
  rw [iall_iff_bdd k x c hc]
  exact ⟨fun h g hg => h g (iinE_le hg) hg, fun h g _ hg => h g hg⟩

/-- The `ex_k` flag, bounded form. -/
lemma iex_iff_bdd (k x : V) :
    ∀ c : V, iex k x c = 1 ↔ ∃ g ≤ c, iinE k g c = 1 ∧ (iltb x g = 1 ∨ x = g) := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    rcases code_cases c with rfl | ⟨i, rfl⟩ | ⟨j, a, rfl⟩ | ⟨y, t, rfl⟩ | hk
    · rw [iex_of_kind k x (Or.inl kind_zero)]; simp
    · rw [iex_of_kind k x (Or.inr (kind_tcOmega i))]; simp
    · by_cases hj : j ≤ k
      · rw [iex_tcTheta_of_le hj, bor_eq_one, beq_eq_one]
        constructor
        · intro h
          exact ⟨tcTheta j a, le_rfl, (iinE_theta_le_iff hj).mpr rfl, h⟩
        · rintro ⟨g, _, hg, h⟩
          rwa [(iinE_theta_le_iff hj).mp hg] at h
      · have hkj : k < j := not_le.mp hj
        rw [iex_tcTheta_of_lt hkj, ih a (arg_lt_tcTheta j a)]
        constructor
        · rintro ⟨g, _, hg, h⟩
          exact ⟨g, (iinE_le hg).trans (arg_lt_tcTheta j a).le,
            by rw [iinE_tcTheta_of_lt hkj]; exact hg, h⟩
        · rintro ⟨g, _, hg, h⟩
          rw [iinE_tcTheta_of_lt hkj] at hg
          exact ⟨g, iinE_le hg, hg, h⟩
    · rw [iex_cons, bor_eq_one, ih y (hd_lt_tcCons y t), ih t (tl_lt_tcCons y t)]
      constructor
      · rintro (⟨g, _, hg, h⟩ | ⟨g, _, hg, h⟩)
        · exact ⟨g, (iinE_le hg).trans (hd_lt_tcCons y t).le,
            (iinE_cons_iff k g y t).mpr (Or.inl hg), h⟩
        · exact ⟨g, (iinE_le hg).trans (tl_lt_tcCons y t).le,
            (iinE_cons_iff k g y t).mpr (Or.inr hg), h⟩
      · rintro ⟨g, _, hg, h⟩
        rcases (iinE_cons_iff k g y t).mp hg with hg | hg
        · exact Or.inl ⟨g, iinE_le hg, hg, h⟩
        · exact Or.inr ⟨g, iinE_le hg, hg, h⟩
    · rw [iex_kind_four k x hk]
      simp only [zero_ne_one, false_iff, not_exists, not_and]
      intro g _ hg
      rw [iinE_kind_four k g hk] at hg; simp at hg

/-- **The `ex_k` flag**: `iex k x c = 1` iff `x ≼ γ` for some element `γ` of `E_k(c)`. -/
lemma iex_iff (k x c : V) :
    iex k x c = 1 ↔ ∃ g, iinE k g c = 1 ∧ (iltb x g = 1 ∨ x = g) := by
  rw [iex_iff_bdd k x c]
  exact ⟨fun ⟨g, _, h⟩ => ⟨g, h⟩, fun ⟨g, h⟩ => ⟨g, iinE_le h.1, h⟩⟩

/-- **The clause of two collapses of one level**, at a term code `a`. -/
lemma iltb_theta_theta_iff {i a : V} (b : V) (ha : isTerm a) :
    iltb (tcTheta i a) (tcTheta i b) = 1 ↔
      (iltb a b = 1 ∧ ∀ g, iinE i g a = 1 → iltb g (tcTheta i b) = 1) ∨
        ∃ g, iinE i g b = 1 ∧ (iltb (tcTheta i a) g = 1 ∨ tcTheta i a = g) := by
  rw [iltb_tcTheta_tcTheta_eq, bor_eq_one, band_eq_one, iall_iff _ ha, iex_iff]

/-- **The clause of two collapses**, all levels, at a term code `a`. -/
lemma iltb_theta_theta_iff' {i a j : V} (b : V) (ha : isTerm a) :
    iltb (tcTheta i a) (tcTheta j b) = 1 ↔
      i < j ∨ (i = j ∧ ((iltb a b = 1 ∧ ∀ g, iinE i g a = 1 → iltb g (tcTheta j b) = 1) ∨
        ∃ g, iinE i g b = 1 ∧ (iltb (tcTheta i a) g = 1 ∨ tcTheta i a = g))) := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [iltb_tcTheta_tcTheta_of_lt h]
    simp [h]
  · rw [iltb_theta_theta_iff b ha]
    simp
  · rw [iltb_tcTheta_tcTheta_of_gt h]
    simp [not_lt.mpr h.le, h.ne']

/-- `ϑ_i α ≺ ϑ_i β` whenever `ϑ_i α ≼ δ` for some `δ ∈ E_i(β)` (all codes). -/
lemma iltb_theta_theta_of_le_iinE {i a b g : V} (hg : iinE i g b = 1)
    (h : iltb (tcTheta i a) g = 1 ∨ tcTheta i a = g) :
    iltb (tcTheta i a) (tcTheta i b) = 1 := by
  rw [iltb_tcTheta_tcTheta_eq, bor_eq_one]
  exact Or.inr ((iex_iff i _ b).mpr ⟨g, hg, h⟩)

/-- `ϑ_i α ≺ ϑ_i β` from `α ≺ β` and `E_i(α) ≺ ϑ_i β`, at a term code `α`. -/
lemma iltb_theta_theta_of_lt {i a b : V} (ha : isTerm a) (h : iltb a b = 1)
    (hE : ∀ g, iinE i g a = 1 → iltb g (tcTheta i b) = 1) :
    iltb (tcTheta i a) (tcTheta i b) = 1 :=
  (iltb_theta_theta_iff b ha).mpr (Or.inl ⟨h, hE⟩)

/-- **`E_k(α) ≺ ϑ_k α`** (all codes). -/
lemma lt_theta_of_iinE {k g a : V} (h : iinE k g a = 1) : iltb g (tcTheta k a) = 1 := by
  obtain ⟨j, d, rfl, hjk⟩ := iinE_shape h
  rcases lt_or_eq_of_le hjk with hlt | rfl
  · exact iltb_tcTheta_tcTheta_of_lt hlt d a
  · exact iltb_theta_theta_of_le_iinE h (Or.inr rfl)

/-! ### Transitivity -/

private lemma sum3_lt_of {x y z x' y' z' : V} (hx : x' ≤ x) (hy : y' ≤ y) (hz : z' ≤ z)
    (hs : x' < x ∨ y' < y ∨ z' < z) : x' + y' + z' < x + y + z := by
  rcases hs with h | h | h
  · exact add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le h hy) hz
  · exact add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt hx h) hz
  · exact add_lt_add_of_le_of_lt (add_le_add hx hy) h

/-- Transitivity among principal codes, given the case of three collapses of one level. -/
private lemma iltb_trans_prin {a b c : V} (ha : kind a = 1 ∨ kind a = 2)
    (hb : kind b = 1 ∨ kind b = 2) (hc : kind c = 1 ∨ kind c = 2)
    (hab : iltb a b = 1) (hbc : iltb b c = 1)
    (H : ∀ i a' b' c', a = tcTheta i a' → b = tcTheta i b' → c = tcTheta i c' →
      iltb a c = 1) :
    iltb a c = 1 := by
  rcases ha with ha | ha
  · obtain ⟨i, rfl⟩ : ∃ i, a = tcOmega i := ⟨_, eq_tcOmega_of_kind ha⟩
    rcases hb with hb | hb
    · obtain ⟨j, rfl⟩ : ∃ j, b = tcOmega j := ⟨_, eq_tcOmega_of_kind hb⟩
      rw [iltb_Omega_Omega_iff] at hab
      rcases hc with hc | hc
      · obtain ⟨k, rfl⟩ : ∃ k, c = tcOmega k := ⟨_, eq_tcOmega_of_kind hc⟩
        rw [iltb_Omega_Omega_iff] at hbc ⊢; exact hab.trans hbc
      · obtain ⟨k, c', rfl⟩ : ∃ k c', c = tcTheta k c' := ⟨_, _, eq_tcTheta_of_kind hc⟩
        rw [iltb_Omega_theta_iff] at hbc ⊢; exact hab.trans hbc
    · obtain ⟨j, b', rfl⟩ : ∃ j b', b = tcTheta j b' := ⟨_, _, eq_tcTheta_of_kind hb⟩
      rw [iltb_Omega_theta_iff] at hab
      rcases hc with hc | hc
      · obtain ⟨k, rfl⟩ : ∃ k, c = tcOmega k := ⟨_, eq_tcOmega_of_kind hc⟩
        rw [iltb_theta_Omega_iff] at hbc
        rw [iltb_Omega_Omega_iff]; exact lt_of_lt_of_le hab hbc
      · obtain ⟨k, c', rfl⟩ : ∃ k c', c = tcTheta k c' := ⟨_, _, eq_tcTheta_of_kind hc⟩
        have := le_of_iltb_theta_theta hbc
        rw [iltb_Omega_theta_iff]; exact lt_of_lt_of_le hab this
  · obtain ⟨i, a', rfl⟩ : ∃ i a', a = tcTheta i a' := ⟨_, _, eq_tcTheta_of_kind ha⟩
    rcases hb with hb | hb
    · obtain ⟨j, rfl⟩ : ∃ j, b = tcOmega j := ⟨_, eq_tcOmega_of_kind hb⟩
      rw [iltb_theta_Omega_iff] at hab
      rcases hc with hc | hc
      · obtain ⟨k, rfl⟩ : ∃ k, c = tcOmega k := ⟨_, eq_tcOmega_of_kind hc⟩
        rw [iltb_Omega_Omega_iff] at hbc
        rw [iltb_theta_Omega_iff]; exact (lt_of_le_of_lt hab hbc).le
      · obtain ⟨k, c', rfl⟩ : ∃ k c', c = tcTheta k c' := ⟨_, _, eq_tcTheta_of_kind hc⟩
        rw [iltb_Omega_theta_iff] at hbc
        exact iltb_tcTheta_tcTheta_of_lt (lt_of_le_of_lt hab hbc) a' c'
    · obtain ⟨j, b', rfl⟩ : ∃ j b', b = tcTheta j b' := ⟨_, _, eq_tcTheta_of_kind hb⟩
      have hij := le_of_iltb_theta_theta hab
      rcases hc with hc | hc
      · obtain ⟨k, rfl⟩ : ∃ k, c = tcOmega k := ⟨_, eq_tcOmega_of_kind hc⟩
        rw [iltb_theta_Omega_iff] at hbc
        rw [iltb_theta_Omega_iff]; exact hij.trans hbc
      · obtain ⟨k, c', rfl⟩ : ∃ k c', c = tcTheta k c' := ⟨_, _, eq_tcTheta_of_kind hc⟩
        have hjk := le_of_iltb_theta_theta hbc
        by_cases hik : i < k
        · exact iltb_tcTheta_tcTheta_of_lt hik a' c'
        · have hki : k ≤ i := not_lt.mp hik
          have e1 : i = k := le_antisymm (hij.trans hjk) hki
          subst e1
          have e2 : j = i := le_antisymm hjk hij
          subst e2
          exact H j a' b' c' rfl rfl rfl

lemma iltb_trans_aux : ∀ w : V, ∀ a ≤ w, ∀ b ≤ w, ∀ c ≤ w, a + b + c ≤ w →
    isTerm a → isTerm b → isTerm c → iltb a b = 1 → iltb b c = 1 → iltb a c = 1 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro a _ b _ c _ hsum ha hb hc hab hbc
    have T : ∀ {x y z : V}, x + y + z < a + b + c → isTerm x → isTerm y → isTerm z →
        iltb x y = 1 → iltb y z = 1 → iltb x z = 1 :=
      fun {x y z} hlt => ih (x + y + z) (lt_of_lt_of_le hlt hsum)
        x (le_trans le_self_add le_self_add) y (le_trans le_add_self le_self_add)
        z le_add_self le_rfl
    have TL : ∀ {x y z : V}, x + y + z < a + b + c → isTerm x → isTerm y → isTerm z →
        (iltb x y = 1 ∨ x = y) → iltb y z = 1 → iltb x z = 1 := by
      intro x y z h hx hy hz h1 h2
      rcases h1 with h1 | rfl
      · exact T h hx hy hz h1 h2
      · exact h2
    have TR : ∀ {x y z : V}, x + y + z < a + b + c → isTerm x → isTerm y → isTerm z →
        iltb x y = 1 → (iltb y z = 1 ∨ y = z) → iltb x z = 1 := by
      intro x y z h hx hy hz h1 h2
      rcases h2 with h2 | rfl
      · exact T h hx hy hz h1 h2
      · exact h1
    have hb0 : b ≠ 0 := by rintro rfl; exact not_iltb_zero_right a hab
    have hc0 : c ≠ 0 := by rintro rfl; exact not_iltb_zero_right b hbc
    rcases eq_or_ne a 0 with rfl | ha0
    · exact iltb_zero_pos hc0
    rcases isTerm_cases_ne_zero ha ha0 with ⟨x, xs, rfl, hx, hxs, -⟩ | hpa <;>
    rcases isTerm_cases_ne_zero hb hb0 with ⟨y, ys, rfl, hy, hys, -⟩ | hpb <;>
    rcases isTerm_cases_ne_zero hc hc0 with ⟨z, zs, rfl, hz, hzs, -⟩ | hpc
    -- sum, sum, sum
    · rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at hab hbc ⊢
      rcases hab with h1 | ⟨rfl, h1⟩ <;> rcases hbc with h2 | ⟨rfl, h2⟩
      · exact Or.inl (T (sum3_lt_of (hd_lt_tcCons x xs).le (hd_lt_tcCons y ys).le
          (hd_lt_tcCons z zs).le (Or.inl (hd_lt_tcCons x xs))) hx hy hz h1 h2)
      · exact Or.inl h1
      · exact Or.inl h2
      · exact Or.inr ⟨rfl, T (sum3_lt_of (tl_lt_tcCons x xs).le (tl_lt_tcCons x ys).le
          (tl_lt_tcCons x zs).le (Or.inl (tl_lt_tcCons x xs))) hxs hys hzs h1 h2⟩
    -- sum, sum, principal
    · rw [iltb_cons_prin _ _ hpc] at hbc ⊢
      rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at hab
      rcases hab with h | ⟨rfl, _⟩
      · exact T (sum3_lt_of (hd_lt_tcCons x xs).le (hd_lt_tcCons y ys).le le_rfl
          (Or.inl (hd_lt_tcCons x xs))) hx hy hc h hbc
      · exact hbc
    -- sum, principal, sum
    · rw [iltb_cons_prin _ _ hpb] at hab
      rw [iltb_prin_cons hpb, bor_eq_one, beq_eq_one] at hbc
      rw [iltb_cons_cons, bor_eq_one]
      exact Or.inl (TR (sum3_lt_of (hd_lt_tcCons x xs).le le_rfl (hd_lt_tcCons z zs).le
        (Or.inl (hd_lt_tcCons x xs))) hx hb hz hab hbc)
    -- sum, principal, principal
    · rw [iltb_cons_prin _ _ hpb] at hab
      rw [iltb_cons_prin _ _ hpc]
      exact T (sum3_lt_of (hd_lt_tcCons x xs).le le_rfl le_rfl
        (Or.inl (hd_lt_tcCons x xs))) hx hb hc hab hbc
    -- principal, sum, sum
    · rw [iltb_prin_cons hpa, bor_eq_one, beq_eq_one] at hab ⊢
      rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at hbc
      rcases hbc with h | ⟨rfl, _⟩
      · exact Or.inl (TL (sum3_lt_of le_rfl (hd_lt_tcCons y ys).le (hd_lt_tcCons z zs).le
          (Or.inr (Or.inl (hd_lt_tcCons y ys)))) ha hy hz hab h)
      · exact hab
    -- principal, sum, principal
    · rw [iltb_prin_cons hpa, bor_eq_one, beq_eq_one] at hab
      rw [iltb_cons_prin _ _ hpc] at hbc
      exact TL (sum3_lt_of le_rfl (hd_lt_tcCons y ys).le le_rfl
        (Or.inr (Or.inl (hd_lt_tcCons y ys)))) ha hy hc hab hbc
    -- principal, principal, sum
    · rw [iltb_prin_cons hpb, bor_eq_one, beq_eq_one] at hbc
      rw [iltb_prin_cons hpa, bor_eq_one]
      exact Or.inl (TR (sum3_lt_of le_rfl le_rfl (hd_lt_tcCons z zs).le
        (Or.inr (Or.inr (hd_lt_tcCons z zs)))) ha hb hz hab hbc)
    -- principal, principal, principal
    · refine iltb_trans_prin hpa hpb hpc hab hbc ?_
      rintro i a' b' c' rfl rfl rfl
      have ha' : isTerm a' := (isTerm_tcTheta_iff i a').mp ha
      have hb' : isTerm b' := (isTerm_tcTheta_iff i b').mp hb
      have hc' : isTerm c' := (isTerm_tcTheta_iff i c').mp hc
      have hbc' := hbc
      have hab' := hab
      rw [iltb_theta_theta_iff b' ha'] at hab
      rw [iltb_theta_theta_iff c' hb'] at hbc
      rw [iltb_theta_theta_iff c' ha']
      rcases hbc with ⟨hbc1, hbc2⟩ | ⟨d, hd, hbd⟩
      · rcases hab with ⟨hab1, hab2⟩ | ⟨d, hd, had⟩
        · refine Or.inl ⟨T (sum3_lt_of (arg_lt_tcTheta i a').le (arg_lt_tcTheta i b').le
            (arg_lt_tcTheta i c').le (Or.inl (arg_lt_tcTheta i a'))) ha' hb' hc' hab1 hbc1,
            fun g hg => ?_⟩
          have hga : g < tcTheta i a' := lt_of_le_of_lt (iinE_le hg) (arg_lt_tcTheta i a')
          exact T (sum3_lt_of hga.le le_rfl le_rfl (Or.inl hga)) (isTerm_of_iinE i g a' ha' hg)
            hb hc (hab2 g hg) hbc'
        · have hdb : d < tcTheta i b' := lt_of_le_of_lt (iinE_le hd) (arg_lt_tcTheta i b')
          exact (iltb_theta_theta_iff c' ha').mp
            (TL (sum3_lt_of le_rfl hdb.le le_rfl (Or.inr (Or.inl hdb))) ha
              (isTerm_of_iinE i d b' hb' hd) hc had (hbc2 d hd))
      · have hdc : d < tcTheta i c' := lt_of_le_of_lt (iinE_le hd) (arg_lt_tcTheta i c')
        exact Or.inr ⟨d, hd, Or.inl (TR (sum3_lt_of le_rfl le_rfl hdc.le
          (Or.inr (Or.inr hdc))) ha hb (isTerm_of_iinE i d c' hc' hd) hab' hbd)⟩

/-- **Transitivity of the internal order** on codes of terms. -/
lemma iltb_trans {a b c : V} (ha : isTerm a) (hb : isTerm b) (hc : isTerm c)
    (hab : iltb a b = 1) (hbc : iltb b c = 1) : iltb a c = 1 :=
  iltb_trans_aux (a + b + c) a (le_trans le_self_add le_self_add)
    b (le_trans le_add_self le_self_add) c le_add_self le_rfl ha hb hc hab hbc

lemma iltb_of_le_of_lt {a b c : V} (ha : isTerm a) (hb : isTerm b) (hc : isTerm c)
    (hab : iltb a b = 1 ∨ a = b) (hbc : iltb b c = 1) : iltb a c = 1 := by
  rcases hab with hab | rfl
  · exact iltb_trans ha hb hc hab hbc
  · exact hbc

lemma iltb_of_lt_of_le {a b c : V} (ha : isTerm a) (hb : isTerm b) (hc : isTerm c)
    (hab : iltb a b = 1) (hbc : iltb b c = 1 ∨ b = c) : iltb a c = 1 := by
  rcases hbc with hbc | rfl
  · exact iltb_trans ha hb hc hab hbc
  · exact hab

lemma ile_trans {a b c : V} (ha : isTerm a) (hb : isTerm b) (hc : isTerm c)
    (hab : iltb a b = 1 ∨ a = b) (hbc : iltb b c = 1 ∨ b = c) : iltb a c = 1 ∨ a = c := by
  rcases hab with hab | rfl
  · exact Or.inl (iltb_of_lt_of_le ha hb hc hab hbc)
  · exact hbc

/-! ### Irreflexivity -/

lemma iltb_irrefl_aux : ∀ a : V, isTerm a → iltb a a ≠ 1 := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a ih =>
    intro ha h
    rcases isTerm_cases ha with rfl | ⟨i, rfl⟩ | ⟨i, a', rfl, ha'⟩ | ⟨x, s, rfl, hx, hs, -⟩
    · exact not_iltb_zero_right 0 h
    · rw [iltb_Omega_Omega_iff] at h; exact _root_.lt_irrefl i h
    · rcases (iltb_theta_theta_iff a' ha').mp h with ⟨h1, -⟩ | ⟨g, hg, h1⟩
      · exact ih a' (arg_lt_tcTheta i a') ha' h1
      · have hga : g < tcTheta i a' := lt_of_le_of_lt (iinE_le hg) (arg_lt_tcTheta i a')
        have hgt : isTerm g := isTerm_of_iinE i g a' ha' hg
        rcases h1 with h1 | h1
        · exact ih g hga hgt (iltb_trans hgt ha hgt (lt_theta_of_iinE hg) h1)
        · exact absurd h1.symm (ne_of_lt hga)
    · rw [iltb_cons_cons, bor_eq_one, band_eq_one] at h
      rcases h with h | ⟨-, h⟩
      · exact ih x (hd_lt_tcCons x s) hx h
      · exact ih s (tl_lt_tcCons x s) hs h

/-- **Irreflexivity of the internal order** on codes of terms. -/
lemma iltb_irrefl {a : V} (ha : isTerm a) : iltb a a ≠ 1 := iltb_irrefl_aux a ha

lemma ne_of_iltb {a b : V} (ha : isTerm a) (h : iltb a b = 1) : a ≠ b := by
  rintro rfl; exact iltb_irrefl ha h

/-- Asymmetry of the internal order on codes of terms. -/
lemma iltb_asymm {a b : V} (ha : isTerm a) (hb : isTerm b) (h : iltb a b = 1) :
    iltb b a ≠ 1 :=
  fun h' => iltb_irrefl ha (iltb_trans ha hb ha h h')

lemma not_ile_of_iltb {a b : V} (ha : isTerm a) (hb : isTerm b) (h : iltb a b = 1) :
    ¬ (iltb b a = 1 ∨ b = a) := by
  rintro (h' | rfl)
  · exact iltb_asymm ha hb h h'
  · exact iltb_irrefl ha h

/-- `ϑ_k α ≼ δ ∈ E_k(α)` is impossible (term codes). -/
lemma not_theta_le_of_iinE {k g a : V} (ha : isTerm a) (h : iinE k g a = 1) :
    ¬ (iltb (tcTheta k a) g = 1 ∨ tcTheta k a = g) :=
  not_ile_of_iltb (isTerm_of_iinE k g a ha h) ((isTerm_tcTheta_iff k a).mpr ha)
    (lt_theta_of_iinE h)

/-! ### Codes of normal forms -/

/-- The shapes of codes whose hereditary normality flag is set. -/
lemma nfA_cases {c : V} (h : nfA c = 1) :
    c = 0 ∨ (∃ i, c = tcOmega i) ∨ (∃ i a, c = tcTheta i a ∧ isNF a) ∨
      (∃ x s, c = tcCons x s ∧ isNF x ∧ nfA s = 1 ∧ sumK s = 1 ∧
        descOk (tcCons x s) = 1) := by
  rcases code_cases c with rfl | ⟨i, rfl⟩ | ⟨i, a, rfl⟩ | ⟨x, s, rfl⟩ | hk
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · rw [nfA_tcTheta] at h
    exact Or.inr (Or.inr (Or.inl ⟨i, a, rfl, h⟩))
  · rw [nfA_tcCons, band_eq_one, band_eq_one, band_eq_one] at h
    exact Or.inr (Or.inr (Or.inr ⟨x, s, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2⟩))
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
    rcases nfA_cases h with rfl | ⟨i, rfl⟩ | ⟨i, a, rfl, ha⟩ | ⟨x, s, rfl, hx, hs, hk, -⟩
    · simp
    · simp
    · exact (isTerm_tcTheta_iff i a).mpr (ih a (arg_lt_tcTheta i a) (nfA_of_isNF ha))
    · exact (isTerm_tcCons_iff x s).mpr
        ⟨ih x (hd_lt_tcCons x s) (nfA_of_isNF hx), ih s (tl_lt_tcCons x s) hs, hk⟩

/-- Codes of normal forms are codes of terms. -/
lemma isTerm_of_isNF {c : V} (h : isNF c) : isTerm c :=
  isTerm_of_nfA_aux c (nfA_of_isNF h)

@[simp] lemma isNF_at_zero : isNF (0 : V) := by simp [isNF, isNFb]

@[simp] lemma isNF_tcOmega (i : V) : isNF (tcOmega i) := by simp [isNF, isNFb]

@[simp] lemma isNF_tcTheta_iff (i a : V) : isNF (tcTheta i a) ↔ isNF a := by
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
private lemma prin_cons_tri {p y ys : V} (hp : kind p = 1 ∨ kind p = 2)
    (C : iltb p y = 1 ∨ p = y ∨ iltb y p = 1) :
    iltb p (tcCons y ys) = 1 ∨ p = tcCons y ys ∨ iltb (tcCons y ys) p = 1 := by
  rw [iltb_prin_cons hp, bor_eq_one, beq_eq_one, iltb_cons_prin y ys hp]
  rcases C with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

/-- The trichotomy of two `ϑ_i`-codes with `α ≺ β`, from the trichotomy of the elements of
`E_i(α)` against `ϑ_i β`. -/
private lemma theta_tri_of_lt {i a b : V} (ha : isTerm a) (h : iltb a b = 1)
    (C : ∀ g, iinE i g a = 1 → iltb g (tcTheta i b) = 1 ∨ g = tcTheta i b ∨
      iltb (tcTheta i b) g = 1) :
    iltb (tcTheta i a) (tcTheta i b) = 1 ∨ iltb (tcTheta i b) (tcTheta i a) = 1 := by
  by_cases hE : ∀ g, iinE i g a = 1 → iltb g (tcTheta i b) = 1
  · exact Or.inl (iltb_theta_theta_of_lt ha h hE)
  · obtain ⟨g, hg, hgb⟩ : ∃ g, iinE i g a = 1 ∧ iltb g (tcTheta i b) ≠ 1 := by
      by_contra hc
      exact hE (fun g hg => by_contra fun h' => hc ⟨g, hg, h'⟩)
    rcases C g hg with h' | h' | h'
    · exact absurd h' hgb
    · exact Or.inr (iltb_theta_theta_of_le_iinE hg (Or.inr h'.symm))
    · exact Or.inr (iltb_theta_theta_of_le_iinE hg (Or.inl h'))

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
    rcases isTerm_cases ha with rfl | ⟨i, rfl⟩ | ⟨i, a', rfl, ha'⟩ | ⟨x, xs, rfl, hx, hxs, -⟩ <;>
    rcases isTerm_cases hb with rfl | ⟨j, rfl⟩ | ⟨j, b', rfl, hb'⟩ | ⟨y, ys, rfl, hy, hys, -⟩
    -- `0` against anything
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (iltb_zero_pos (tcOmega_ne_zero j))
    · exact Or.inl (iltb_zero_pos (tcTheta_ne_zero j b'))
    · exact Or.inl (iltb_zero_pos (tcCons_ne_zero y ys))
    -- `Ω_i`
    · exact Or.inr (Or.inr (iltb_zero_pos (tcOmega_ne_zero i)))
    · rw [iltb_Omega_Omega_iff, iltb_Omega_Omega_iff]
      rcases lt_trichotomy i j with h | rfl | h
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h)
    · rw [iltb_Omega_theta_iff, iltb_theta_Omega_iff]
      by_cases h : i < j
      · exact Or.inl h
      · exact Or.inr (Or.inr (not_lt.mp h))
    · exact prin_cons_tri (Or.inl (kind_tcOmega i)) (C (sum2_lt_of le_rfl (hd_lt_tcCons y ys).le
        (Or.inr (hd_lt_tcCons y ys))) ha hy)
    -- `ϑ_i`
    · exact Or.inr (Or.inr (iltb_zero_pos (tcTheta_ne_zero i a')))
    · rw [iltb_theta_Omega_iff, iltb_Omega_theta_iff]
      by_cases h : j < i
      · exact Or.inr (Or.inr h)
      · exact Or.inl (not_lt.mp h)
    · rcases lt_trichotomy i j with hij | rfl | hij
      · exact Or.inl (iltb_tcTheta_tcTheta_of_lt hij a' b')
      · rcases C (sum2_lt_of (arg_lt_tcTheta i a').le (arg_lt_tcTheta i b').le
          (Or.inl (arg_lt_tcTheta i a'))) ha' hb' with h | rfl | h
        · rcases theta_tri_of_lt ha' h (fun g hg => by
            have hga : g < tcTheta i a' := lt_of_le_of_lt (iinE_le hg) (arg_lt_tcTheta i a')
            exact C (sum2_lt_of hga.le le_rfl (Or.inl hga)) (isTerm_of_iinE i g a' ha' hg) hb)
            with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl rfl)
        · rcases theta_tri_of_lt hb' h (fun g hg => by
            have hgb : g < tcTheta i b' := lt_of_le_of_lt (iinE_le hg) (arg_lt_tcTheta i b')
            exact tri_symm (C (sum2_lt_of le_rfl hgb.le (Or.inr hgb)) ha
              (isTerm_of_iinE i g b' hb' hg)))
            with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inl h
      · exact Or.inr (Or.inr (iltb_tcTheta_tcTheta_of_lt hij b' a'))
    · exact prin_cons_tri (Or.inr (kind_tcTheta i a')) (C (sum2_lt_of le_rfl
        (hd_lt_tcCons y ys).le (Or.inr (hd_lt_tcCons y ys))) ha hy)
    -- sums
    · exact Or.inr (Or.inr (iltb_zero_pos (tcCons_ne_zero x xs)))
    · rcases prin_cons_tri (ys := xs) (Or.inl (kind_tcOmega j)) (tri_symm (C (sum2_lt_of
        (hd_lt_tcCons x xs).le le_rfl (Or.inl (hd_lt_tcCons x xs))) hx hb)) with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
    · rcases prin_cons_tri (ys := xs) (Or.inr (kind_tcTheta j b')) (tri_symm (C (sum2_lt_of
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

lemma ile_of_not_iltb {a b : V} (ha : isTerm a) (hb : isTerm b) (h : iltb a b ≠ 1) :
    iltb b a = 1 ∨ b = a := by
  rcases iltb_trichotomy ha hb with h' | h' | h'
  · exact absurd h' h
  · exact Or.inr h'.symm
  · exact Or.inl h'

lemma not_iltb_iff_ile {a b : V} (ha : isTerm a) (hb : isTerm b) :
    iltb a b ≠ 1 ↔ (iltb b a = 1 ∨ b = a) :=
  ⟨ile_of_not_iltb ha hb, fun h h' => not_ile_of_iltb ha hb h' h⟩

end Model

end OrdinalAnalysis.IDn.Internal
