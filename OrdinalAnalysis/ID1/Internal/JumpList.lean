/-
  Exponent lists of the coded ϑ-notation inside models of `IΣ₁`: the facts about appending
  one exponent at the end that Gentzen's jump needs.

  A normal form `α = ω^{α₀} + … + ω^{α_{n-1}}` is read through its exponent list `itoL α`
  (a cons list of codes of normal forms, non-increasing), and the order of normal forms is the
  lexicographic order of their exponent lists (`iltb_itoL_iff`).  Gentzen's jump (Gentzen
  1943; Arai, arXiv:2304.00246, Lemma 1.31) extends a list `η` by one exponent at the end,
  `η ++ ⟨y⟩ = isnoc η y`, and uses:

  * `iapp_isnoc`: `(η ++ ⟨y⟩) ++ w = η ++ (y :: w)`;
  * `iltb_iapp_iapp`: a common prefix does not change the order;
  * `iltb_isnoc_cases`: every list `ζ ≺ η ++ ⟨y⟩` is `≼ η` or of the form `η ++ ρ` with `ρ`
    nonempty and first exponent `≺ y`;
  * `isSL_isnoc_of_isSL_iapp`: the list `η ++ ⟨z⟩` is descending when `η ++ (z :: w)` is;
  * `iinE_iapp_right`: the coefficients of `ρ` are coefficients of `η ++ ρ`;

  together with `isNF_of_iinE` (the elements of `E(α)` of a normal form are normal) and the
  two comparisons used at the start of the tower of jumps: below `ω^β` (`iltb_single_cases`)
  and below `Ω + 1` (`iltb_omega_succ_cases`).
-/
import OrdinalAnalysis.ID1.Internal.ArithLaws

set_option autoImplicit false

namespace OrdinalAnalysis.ID1.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.Gentzen.InternalONote

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `s ++ ⟨y⟩`: the list `s` with the exponent `y` appended at the end. -/
noncomputable def isnoc (s y : V) : V := iapp s (tcCons y 0)

instance isnoc_definable (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (isnoc : V → V → V) := by
  unfold isnoc; definability

@[simp] lemma isnoc_zero (y : V) : isnoc 0 y = tcCons y 0 := by simp [isnoc]

lemma isnoc_cons (a s y : V) : isnoc (tcCons a s) y = tcCons a (isnoc s y) := by
  simp [isnoc, iapp_cons]

/-- `(s ++ ⟨y⟩) ++ w = s ++ (y :: w)`. -/
lemma iapp_isnoc (y w : V) : ∀ s : V, iapp (isnoc s y) w = iapp s (tcCons y w) := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    by_cases hk : kind s = 3
    · rw [eq_tcCons_of_kind hk, isnoc_cons, iapp_cons, iapp_cons,
        ih _ (tcTl_lt (ne_zero_of_kind_ne_zero (by rw [hk]; simp)))]
    · rw [isnoc, iapp_of_kind hk, iapp_of_kind hk, iapp_cons, iapp_zero_left]

/-- A common prefix does not change the order. -/
lemma iltb_iapp_iapp (u v : V) :
    ∀ s : V, iltb (iapp s u) (iapp s v) = 1 ↔ iltb u v = 1 := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    by_cases hk : kind s = 3
    · rw [eq_tcCons_of_kind hk, iapp_cons, iapp_cons, iltb_cons_cons, bor_eq_one, band_eq_one,
        beq_eq_one, ih _ (tcTl_lt (ne_zero_of_kind_ne_zero (by rw [hk]; simp)))]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact absurd h (iltb_irrefl _)
        · exact h
      · intro h; exact Or.inr ⟨rfl, h⟩
    · rw [iapp_of_kind hk, iapp_of_kind hk]

/-- The appended list is at least as large, as a number, as its second part. -/
lemma le_iapp_right (t : V) : ∀ s : V, t ≤ iapp s t := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    by_cases hk : kind s = 3
    · rw [eq_tcCons_of_kind hk, iapp_cons]
      exact le_of_lt (lt_of_le_of_lt (ih _ (tcTl_lt (ne_zero_of_kind_ne_zero (by rw [hk]; simp))))
        (tl_lt_tcCons _ _))
    · rw [iapp_of_kind hk]

/-- The coefficients of `ρ` are coefficients of `s ++ ρ`. -/
lemma iinE_iapp_right (g t : V) : ∀ s : V, iinE g t = 1 → iinE g (iapp s t) = 1 := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro h
    by_cases hk : kind s = 3
    · rw [eq_tcCons_of_kind hk, iapp_cons, iinE_tcCons_iff]
      exact Or.inr (ih _ (tcTl_lt (ne_zero_of_kind_ne_zero (by rw [hk]; simp))) h)
    · rw [iapp_of_kind hk]; exact h

/-- The first entry of `s ++ (z :: w)` does not depend on `w`. -/
lemma tcHd_iapp_cons (s z w w' : V) :
    tcHd (iapp s (tcCons z w)) = tcHd (iapp s (tcCons z w')) := by
  by_cases hk : kind s = 3
  · rw [eq_tcCons_of_kind hk, iapp_cons, iapp_cons, tcHd_tcCons, tcHd_tcCons]
  · rw [iapp_of_kind hk, iapp_of_kind hk, tcHd_tcCons, tcHd_tcCons]

/-- `s ++ ⟨z⟩` is descending when `s ++ (z :: w)` is. -/
lemma isSL_isnoc_of_isSL_iapp (z w : V) :
    ∀ s : V, IsSL (iapp s (tcCons z w)) → IsSL (isnoc s z) := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro h
    by_cases hk : kind s = 3
    · have e := eq_tcCons_of_kind hk
      have hlt : tcTl s < s := tcTl_lt (ne_zero_of_kind_ne_zero (by rw [hk]; simp))
      rw [e, iapp_cons, isSL_cons_iff] at h
      rw [e, isnoc_cons, isSL_cons_iff]
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨h1, ih _ hlt h2, Or.inr ?_⟩
      rcases h3 with h3 | h3
      · exact absurd h3 (iapp_ne_zero_of_ne_zero _ (tcCons_ne_zero z w))
      · rw [isnoc, tcHd_iapp_cons (tcTl s) z 0 w]; exact h3
    · rw [iapp_of_kind hk, isSL_cons_iff] at h
      rw [isnoc, iapp_of_kind hk, isSL_cons_iff]
      exact ⟨h.1, isSL_zero, Or.inl rfl⟩

/-- The second part of a descending list `s ++ ρ` is descending. -/
lemma isSL_of_isSL_iapp_right (r : V) : ∀ s : V, IsSL (iapp s r) → IsSL r := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro h
    by_cases hk : kind s = 3
    · rw [eq_tcCons_of_kind hk, iapp_cons, isSL_cons_iff] at h
      exact ih _ (tcTl_lt (ne_zero_of_kind_ne_zero (by rw [hk]; simp))) h.2.1
    · rwa [iapp_of_kind hk] at h

/-- A cons cell is a normal form iff it is a descending list and not a one-entry list with a
principal entry. -/
lemma isNF_tcCons_iff (x w : V) :
    isNF (tcCons x w) ↔ IsSL (tcCons x w) ∧ ¬ (w = 0 ∧ IsPrinC x) := by
  unfold isNF isNFb IsSL
  rw [band_eq_one, sok_tcCons, sumK_tcCons]
  by_cases h : w = 0 ∧ IsPrinC x
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

/-- **Below `η ++ ⟨y⟩`.**  A descending list `ζ ≺ η ++ ⟨y⟩` is `≼ η` or of the form `η ++ ρ`
with `ρ` nonempty and first exponent `≺ y`. -/
lemma iltb_isnoc_cases (y : V) :
    ∀ s : V, IsSL s → ∀ z, IsSL z → iltb z (isnoc s y) = 1 →
      iltb z s = 1 ∨ z = s ∨ ∃ r ≤ z, z = iapp s r ∧ r ≠ 0 ∧ iltb (tcHd r) y = 1 := by
  intro s
  induction s using ISigma1.pi1_order_induction
  · definability
  case ind s ih =>
    intro hs z hz h
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [isnoc_zero] at h
      rcases eq_or_ne z 0 with rfl | hz0
      · exact Or.inr (Or.inl rfl)
      obtain ⟨c, r', rfl⟩ := eq_cons_of_sumK hz.2 hz0
      rw [iltb_cons_cons, bor_eq_one, band_eq_one] at h
      rcases h with h | ⟨-, h⟩
      · exact Or.inr (Or.inr ⟨tcCons c r', le_rfl, by rw [iapp_zero_left],
          tcCons_ne_zero _ _, by rw [tcHd_tcCons]; exact h⟩)
      · exact absurd h (not_iltb_zero r')
    obtain ⟨a, s', rfl⟩ := eq_cons_of_sumK hs.2 hs0
    have hs' : IsSL s' := ((isSL_cons_iff a s').mp hs).2.1
    rw [isnoc_cons] at h
    rcases eq_or_ne z 0 with rfl | hz0
    · exact Or.inl (iltb_zero_tcCons a s')
    obtain ⟨c, r', rfl⟩ := eq_cons_of_sumK hz.2 hz0
    have hr' : IsSL r' := ((isSL_cons_iff c r').mp hz).2.1
    rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at h
    rcases h with h | ⟨rfl, h⟩
    · refine Or.inl ?_
      rw [iltb_cons_cons, bor_eq_one]
      exact Or.inl h
    · rcases ih s' (tl_lt_tcCons c s') hs' r' hr' h with h' | rfl | ⟨r, hr, rfl, hr0, hry⟩
      · refine Or.inl ?_
        rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
        exact Or.inr ⟨rfl, h'⟩
      · exact Or.inr (Or.inl rfl)
      · refine Or.inr (Or.inr ⟨r, le_trans hr (le_of_lt (tl_lt_tcCons _ _)), ?_, hr0, hry⟩)
        rw [iapp_cons]

/-- The elements of `E(α)` of a code with hereditarily normal entries are normal. -/
lemma isNF_of_iinE (g : V) : ∀ c : V, nfA c = 1 → iinE g c = 1 → isNF g := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    intro hc h
    rcases nfA_cases hc with rfl | rfl | ⟨a, rfl, ha⟩ | ⟨x, s, rfl, hx, hs, -, -⟩
    · simp at h
    · rw [iinE_top g (Or.inl kind_one)] at h; simp at h
    · rw [(iinE_tcTheta_iff g a).mp h, isNF_tcTheta_iff]; exact ha
    · rcases (iinE_tcCons_iff g x s).mp h with h | h
      · exact ih x (hd_lt_tcCons x s) (nfA_of_isNF hx) h
      · exact ih s (tl_lt_tcCons x s) hs h

/-- **The order of normal forms is the lexicographic order of their exponent lists.** -/
lemma iltb_itoL_iff {b c : V} (hb : isNF b) (hc : isNF c) :
    iltb (itoL b) (itoL c) = 1 ↔ iltb b c = 1 := by
  refine ⟨fun h => ?_, iltb_itoL hb hc⟩
  rcases iltb_trichotomy_nf hb hc with h' | rfl | h'
  · exact h'
  · exact absurd h (iltb_irrefl _)
  · exact absurd h (iltb_asymm (iltb_itoL hc hb h'))

/-- The exponent list determines the normal form. -/
lemma eq_of_itoL_eq {b c : V} (hb : isNF b) (hc : isNF c) (h : itoL b = itoL c) : b = c := by
  rw [← iofL_itoL hb, ← iofL_itoL hc, h]

/-- **Below `ω^β`**: a list below the one-entry list `⟨β⟩` is empty or has its first entry
`≺ β`. -/
lemma iltb_single_cases {l β : V} (hl : sumK l = 1) (h : iltb l (tcCons β 0) = 1) :
    l = 0 ∨ ∃ z w, l = tcCons z w ∧ iltb z β = 1 := by
  rcases eq_or_ne l 0 with rfl | hl0
  · exact Or.inl rfl
  obtain ⟨z, w, rfl⟩ := eq_cons_of_sumK hl hl0
  rw [iltb_cons_cons, bor_eq_one, band_eq_one] at h
  rcases h with h | ⟨-, h⟩
  · exact Or.inr ⟨z, w, rfl, h⟩
  · exact absurd h (not_iltb_zero w)

/-- **Below `Ω + 1`**: a normal form below `Ω + 1 = ⟨Ω, 0⟩` is below `Ω` or is `Ω`. -/
lemma iltb_omega_succ_cases {ξ : V} (hξ : isNF ξ) (h : iltb ξ (tcCons 1 (tcCons 0 0)) = 1) :
    iltb ξ 1 = 1 ∨ ξ = 1 := by
  rcases nf_cases hξ with rfl | hp | ⟨z, w, rfl, hzw⟩
  · exact Or.inl (iltb_zero_pos _root_.one_ne_zero)
  · rw [iltb_prinC_cons hp] at h; exact h
  · rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at h
    rcases h with h | ⟨rfl, h⟩
    · rw [iltb_cons_one]; exact Or.inl h
    · exfalso
      refine hzw ⟨?_, isPrinC_one⟩
      rcases eq_or_ne w 0 with hw | hw
      · exact hw
      · obtain ⟨c, w', rfl⟩ := eq_cons_of_sumK (isSL_cons_iff 1 w |>.mp
          (by rw [← itoL_tcCons]; exact isSL_itoL hξ)).2.1.2 hw
        rw [iltb_cons_cons, bor_eq_one, band_eq_one] at h
        rcases h with h | ⟨-, h⟩
        · exact absurd h (not_iltb_zero c)
        · exact absurd h (not_iltb_zero w')

end OrdinalAnalysis.ID1.Internal
