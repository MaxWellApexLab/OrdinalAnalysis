/-
  Order theory of the internal Veblen comparison `icmp₁` on normal codes.

  `InternalVNote` supplies the recursion law, trichotomy and the swap law of `icmp₁`
  on normal codes.  This file adds what Gentzen's jump needs on top of that:

  * the **lead form** of the recursion — on normal codes `x = φ_a(b)·n + c`,
    `icmp₁ x y = thenV (icmp₁ Lx Ly) (thenV (cmpV n n') (icmp₁ c c'))` with
    `Lx = vcVadd a b 1 0` the leading term; this is exactly the Cantor-normal-form
    recursion of `InternalONote.icmp_ocOadd` with the exponent replaced by the leading
    term, and it is what lets the ω-cover argument of `OmegaCover.lean` transfer;
  * reflexivity `icmp₁_self` and the equality reflection `icmp₁_eq_imp_eq`;
  * the two monotonicity facts of the Veblen rule, `snd_lt_of_lead_lt`
    (`φ_a(b) < y → b < y`) and `lt_lead_of_lt_snd` (`x < b' → x < φ_{a'}(b')`), proved by
    a joint induction on the *sum* of the codes;
  * transitivity `icmp₁_trans`, also by induction on the sum of the three codes.  The
    sum (rather than the maximum used in `InternalONote.icmp_trans`) is forced by the
    Veblen rule, which compares an argument `b` against a *whole* term `L'` that is not
    below the other code in the maximum order.

  Everything is proved semantically in an arbitrary model of `IΣ₁`, by `𝚺₁`-order
  induction; nothing about ordinals is used.
-/
import OrdinalAnalysis.Gentzen.InternalVNote

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OrdinalAnalysis.Gentzen.InternalVNoteOrder

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.InternalVNote

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Code-value bounds in constructor form -/

lemma fst_lt_code (a b n c : V) : a < vcVadd a b n c := by
  simpa using vcFst_lt a b n c

lemma snd_lt_code (a b n c : V) : b < vcVadd a b n c := by
  simpa using vcSnd_lt a b n c

lemma tail_lt_code (a b n c : V) : c < vcVadd a b n c := by
  simpa using vcTail_lt a b n c

lemma lead_le_code {a b n c : V} (hn : n ≠ 0) : vcVadd a b 1 0 ≤ vcVadd a b n c :=
  vcVadd_one_zero_le hn

/-- Destructuring a normal positive code: the six clauses of `isNF₁_vcVadd` together with
normality of the leading term. -/
lemma nf_parts {a b n c : V} (h : isNF₁ (vcVadd a b n c)) :
    n ≠ 0 ∧ isNF₁ a ∧ isNF₁ b ∧ isNF₁ c ∧ isNF₁ (vcVadd a b 1 0) ∧
      icmp₁ b (vcVadd a b 1 0) = 0 ∧ icmp₁ c (vcVadd a b 1 0) = 0 := by
  obtain ⟨hn, ha, hb, hc, hfix, htail⟩ := (isNF₁_vcVadd a b n c).1 h
  refine ⟨hn, ha, hb, hc, ?_, hfix, htail⟩
  rw [isNF₁_vcVadd]
  exact ⟨_root_.one_ne_zero, ha, hb, isNF₁_zero, hfix, icmp₁_zero_vcVadd _ _ _ _⟩

lemma isNF₁_lead_of {a b n c : V} (h : isNF₁ (vcVadd a b n c)) :
    isNF₁ (vcVadd a b 1 0) :=
  (nf_parts h).2.2.2.2.1

lemma isNF₁_of_parts {a b : V} (ha : isNF₁ a) (hb : isNF₁ b)
    (hfix : icmp₁ b (vcVadd a b 1 0) = 0) {n c : V} (hn : n ≠ 0) (hc : isNF₁ c)
    (htail : icmp₁ c (vcVadd a b 1 0) = 0) : isNF₁ (vcVadd a b n c) :=
  (isNF₁_vcVadd a b n c).2 ⟨hn, ha, hb, hc, hfix, htail⟩

/-! ### Ordering-code facts -/

lemma icmp₁_right_zero_ne_zero (x : V) : icmp₁ x 0 ≠ 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [icmp₁_zero_zero]; exact _root_.one_ne_zero
  · rw [icmp₁_pos_zero hx]; exact _root_.two_ne_zero

lemma icmp₁_rev_zero {a b : V} (ha : isNF₁ a) (hb : isNF₁ b) (h : icmp₁ a b = 0) :
    icmp₁ b a = 2 := by
  have hs := icmp₁_swap ha hb
  rw [h] at hs
  simpa [oswap] using hs

lemma icmp₁_rev_two {a b : V} (ha : isNF₁ a) (hb : isNF₁ b) (h : icmp₁ a b = 2) :
    icmp₁ b a = 0 := by
  have hs := icmp₁_swap ha hb
  rw [h] at hs
  simpa [oswap] using hs

lemma icmp₁_rev_one {a b : V} (ha : isNF₁ a) (hb : isNF₁ b) (h : icmp₁ a b = 1) :
    icmp₁ b a = 1 := by
  have hs := icmp₁_swap ha hb
  rw [h] at hs
  simpa [oswap] using hs

lemma icmp₁_zero_of_ne {a b : V} (ha : isNF₁ a) (hb : isNF₁ b)
    (h1 : icmp₁ a b ≠ 1) (h2 : icmp₁ a b ≠ 2) : icmp₁ a b = 0 := by
  rcases icmp₁_cases ha hb with h | h | h
  · exact h
  · exact absurd h h1
  · exact absurd h h2

/-! ### Reflexivity -/

lemma icmp₁_self_aux : ∀ w : V, ∀ x ≤ w, isNF₁ x → icmp₁ x x = 1 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro x hxw hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact icmp₁_zero_zero
    · obtain ⟨a, b, n, c, rfl⟩ : ∃ a b n c, x = vcVadd a b n c :=
        ⟨_, _, _, _, (vcVadd_destruct hx0).symm⟩
      obtain ⟨hn, ha, hb, hc, -, -, -⟩ := nf_parts hx
      have haw : a < w := lt_of_lt_of_le (fst_lt_code a b n c) hxw
      have hbw : b < w := lt_of_lt_of_le (snd_lt_code a b n c) hxw
      have hcw : c < w := lt_of_lt_of_le (tail_lt_code a b n c) hxw
      rw [icmp₁_vcVadd_vcVadd hn hn, ih a haw a le_rfl ha, ih b hbw b le_rfl hb,
        ih c hcw c le_rfl hc, leadV_one, cmpV_self, thenV_one_left, thenV_one_left]

/-- Internal Veblen comparison is reflexive on normal codes. -/
lemma icmp₁_self {x : V} (hx : isNF₁ x) : icmp₁ x x = 1 :=
  icmp₁_self_aux x x le_rfl hx

/-! ### The lead form of the recursion -/

/-- Comparison of two single Veblen terms is the three-way Veblen rule. -/
lemma icmp₁_lead_lead (a b a' b' : V) :
    icmp₁ (vcVadd a b 1 0) (vcVadd a' b' 1 0) =
      leadV (icmp₁ a a') (icmp₁ b b') (icmp₁ b (vcVadd a' b' 1 0))
        (icmp₁ (vcVadd a b 1 0) b') := by
  rw [icmp₁_vcVadd_vcVadd _root_.one_ne_zero _root_.one_ne_zero, cmpV_self, icmp₁_zero_zero,
    thenV_one_left, thenV_one_right]

/-- **The lead form.**  Comparison of two codes with positive coefficients is the
lexicographic combination of leading-term comparison, coefficient comparison and tail
comparison. -/
lemma icmp₁_lead_form {a b n c a' b' n' c' : V} (hn : n ≠ 0) (hn' : n' ≠ 0) :
    icmp₁ (vcVadd a b n c) (vcVadd a' b' n' c') =
      thenV (icmp₁ (vcVadd a b 1 0) (vcVadd a' b' 1 0))
        (thenV (cmpV n n') (icmp₁ c c')) := by
  rw [icmp₁_vcVadd_vcVadd hn hn', icmp₁_lead_lead]

/-- `lead x < lead y → x < y`. -/
lemma lt_of_lead_lt {a b n c a' b' n' c' : V} (hn : n ≠ 0) (hn' : n' ≠ 0)
    (h : icmp₁ (vcVadd a b 1 0) (vcVadd a' b' 1 0) = 0) :
    icmp₁ (vcVadd a b n c) (vcVadd a' b' n' c') = 0 := by
  rw [icmp₁_lead_form hn hn']
  exact thenV_eq_zero.mpr (Or.inl h)

/-- `x < lead y → x < y`. -/
lemma lt_of_lt_lead {x a' b' n' c' : V} (hx : isNF₁ x) (hn' : n' ≠ 0)
    (h : icmp₁ x (vcVadd a' b' 1 0) = 0) : icmp₁ x (vcVadd a' b' n' c') = 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact icmp₁_zero_vcVadd _ _ _ _
  · obtain ⟨a, b, n, c, rfl⟩ : ∃ a b n c, x = vcVadd a b n c :=
      ⟨_, _, _, _, (vcVadd_destruct hx0).symm⟩
    obtain ⟨hn, -, -, -, -, -, -⟩ := nf_parts hx
    rw [icmp₁_lead_form hn _root_.one_ne_zero] at h
    rw [icmp₁_lead_form hn hn']
    rcases thenV_eq_zero.mp h with h0 | ⟨-, hrest⟩
    · exact thenV_eq_zero.mpr (Or.inl h0)
    · exfalso
      rcases thenV_eq_zero.mp hrest with hc0 | ⟨-, hc0⟩
      · exact hn (lt_one_iff_eq_zero.mp (cmpV_eq_zero.mp hc0))
      · exact icmp₁_right_zero_ne_zero c hc0

/-- `x < y → lead x < y`. -/
lemma lead_lt_of_lt {a b n c a' b' n' c' : V} (hn : n ≠ 0) (hn' : n' ≠ 0)
    (h : icmp₁ (vcVadd a b n c) (vcVadd a' b' n' c') = 0) :
    icmp₁ (vcVadd a b 1 0) (vcVadd a' b' n' c') = 0 := by
  rw [icmp₁_lead_form hn hn'] at h
  rw [icmp₁_lead_form _root_.one_ne_zero hn']
  rcases thenV_eq_zero.mp h with h0 | ⟨h1, hrest⟩
  · exact thenV_eq_zero.mpr (Or.inl h0)
  · refine thenV_eq_zero.mpr (Or.inr ⟨h1, ?_⟩)
    rcases thenV_eq_zero.mp hrest with hlt | ⟨heq, hcc⟩
    · have h1n : (1 : V) ≤ n := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hn)
      exact thenV_eq_zero.mpr
        (Or.inl (cmpV_eq_zero.mpr (lt_of_le_of_lt h1n (cmpV_eq_zero.mp hlt))))
    · have hc' : c' ≠ 0 := by
        rintro rfl
        exact icmp₁_right_zero_ne_zero c hcc
      rcases eq_or_ne n' 1 with rfl | hn1
      · exact thenV_eq_zero.mpr (Or.inr ⟨cmpV_self 1, icmp₁_zero_pos hc'⟩)
      · have h1n' : (1 : V) < n' :=
          lt_of_le_of_ne (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hn')) (Ne.symm hn1)
        exact thenV_eq_zero.mpr (Or.inl (cmpV_eq_zero.mpr h1n'))

/-! ### Equality reflection -/

private lemma sum2_lt_of {x y x' y' : V} (hx : x' ≤ x) (hy : y' ≤ y)
    (hs : x' < x ∨ y' < y) : x' + y' < x + y := by
  rcases hs with h | h
  · exact add_lt_add_of_lt_of_le h hy
  · exact add_lt_add_of_le_of_lt hx h

lemma icmp₁_eq_imp_eq_aux : ∀ w : V, ∀ x ≤ w, ∀ y ≤ w, x + y ≤ w →
    isNF₁ x → isNF₁ y → icmp₁ x y = 1 → x = y := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro x hxw y hyw hsum hx hy h
    have IH : ∀ {x' y' : V}, x' + y' < w → isNF₁ x' → isNF₁ y' → icmp₁ x' y' = 1 → x' = y' :=
      fun {x' y'} hlt => ih (x' + y') hlt x' le_self_add y' le_add_self le_rfl
    rcases eq_or_ne x 0 with rfl | hx0
    · rcases eq_or_ne y 0 with rfl | hy0
      · rfl
      · rw [icmp₁_zero_pos hy0] at h
        exact absurd h zero_ne_one
    · rcases eq_or_ne y 0 with rfl | hy0
      · rw [icmp₁_pos_zero hx0] at h
        exact absurd h (one_lt_two).ne'
      · obtain ⟨a, b, n, c, rfl⟩ : ∃ a b n c, x = vcVadd a b n c :=
          ⟨_, _, _, _, (vcVadd_destruct hx0).symm⟩
        obtain ⟨a', b', n', c', rfl⟩ : ∃ a b n c, y = vcVadd a b n c :=
          ⟨_, _, _, _, (vcVadd_destruct hy0).symm⟩
        obtain ⟨hn, ha, hb, hc, hL, hfix, -⟩ := nf_parts hx
        obtain ⟨hn', ha', hb', hc', hL', hfix', -⟩ := nf_parts hy
        rw [icmp₁_lead_form hn hn', thenV_eq_one, thenV_eq_one, icmp₁_lead_lead] at h
        obtain ⟨hlead, hcoef, htail⟩ := h
        have hcc : c = c' :=
          IH (lt_of_lt_of_le (sum2_lt_of (tail_lt_code a b n c).le (tail_lt_code a' b' n' c').le
            (Or.inl (tail_lt_code a b n c))) hsum) hc hc' htail
        have hnn : n = n' := cmpV_eq_one.mp hcoef
        rcases icmp₁_cases ha ha' with h0 | h1 | h2
        · rw [h0, leadV_zero] at hlead
          have hbL : b = vcVadd a' b' 1 0 :=
            IH (lt_of_lt_of_le (sum2_lt_of (snd_lt_code a b n c).le (lead_le_code hn')
              (Or.inl (snd_lt_code a b n c))) hsum) hb hL' hlead
          exfalso
          subst hbL
          rw [icmp₁_lead_lead, icmp₁_rev_zero ha ha' h0, leadV_two, icmp₁_self hL'] at hfix
          exact absurd hfix _root_.one_ne_zero
        · rw [h1, leadV_one] at hlead
          have haa : a = a' :=
            IH (lt_of_lt_of_le (sum2_lt_of (fst_lt_code a b n c).le (fst_lt_code a' b' n' c').le
              (Or.inl (fst_lt_code a b n c))) hsum) ha ha' h1
          have hbb : b = b' :=
            IH (lt_of_lt_of_le (sum2_lt_of (snd_lt_code a b n c).le (snd_lt_code a' b' n' c').le
              (Or.inl (snd_lt_code a b n c))) hsum) hb hb' hlead
          rw [haa, hbb, hnn, hcc]
        · rw [h2, leadV_two] at hlead
          have hLb : vcVadd a b 1 0 = b' :=
            IH (lt_of_lt_of_le (sum2_lt_of (lead_le_code hn) (snd_lt_code a' b' n' c').le
              (Or.inr (snd_lt_code a' b' n' c'))) hsum) hL hb' hlead
          exfalso
          subst hLb
          rw [icmp₁_lead_lead, h2, leadV_two, icmp₁_self hL] at hfix'
          exact absurd hfix' _root_.one_ne_zero

/-- On normal codes the equality code reflects equality. -/
lemma icmp₁_eq_imp_eq {x y : V} (hx : isNF₁ x) (hy : isNF₁ y) (h : icmp₁ x y = 1) : x = y :=
  icmp₁_eq_imp_eq_aux (x + y) x le_self_add y le_add_self le_rfl hx hy h

/-! ### The two monotonicity facts of the Veblen rule

(T')  `φ_a(b) < y → b < y`;   (T'')  `x < b' → x < φ_{a'}(b')`.

They are proved together by induction on the sum of the two codes: the Veblen rule
turns each of them into the other at a strictly smaller sum. -/

lemma veblen_mono_aux : ∀ w : V,
    (∀ a ≤ w, ∀ b ≤ w, ∀ y ≤ w, vcVadd a b 1 0 + y ≤ w →
      isNF₁ (vcVadd a b 1 0) → isNF₁ y → icmp₁ (vcVadd a b 1 0) y = 0 → icmp₁ b y = 0) ∧
    (∀ x ≤ w, ∀ a' ≤ w, ∀ b' ≤ w, x + vcVadd a' b' 1 0 ≤ w →
      isNF₁ x → isNF₁ (vcVadd a' b' 1 0) → icmp₁ x b' = 0 →
        icmp₁ x (vcVadd a' b' 1 0) = 0) := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    have IH1 : ∀ {a₁ b₁ y₁ : V}, vcVadd a₁ b₁ 1 0 + y₁ < w →
        isNF₁ (vcVadd a₁ b₁ 1 0) → isNF₁ y₁ → icmp₁ (vcVadd a₁ b₁ 1 0) y₁ = 0 →
          icmp₁ b₁ y₁ = 0 :=
      fun {a₁ b₁ y₁} hlt => (ih _ hlt).1 a₁ ((fst_lt_code a₁ b₁ 1 0).le.trans le_self_add)
        b₁ ((snd_lt_code a₁ b₁ 1 0).le.trans le_self_add) y₁ le_add_self le_rfl
    have IH2 : ∀ {x₁ a₁ b₁ : V}, x₁ + vcVadd a₁ b₁ 1 0 < w →
        isNF₁ x₁ → isNF₁ (vcVadd a₁ b₁ 1 0) → icmp₁ x₁ b₁ = 0 →
          icmp₁ x₁ (vcVadd a₁ b₁ 1 0) = 0 :=
      fun {x₁ a₁ b₁} hlt => (ih _ hlt).2 x₁ le_self_add
        a₁ ((fst_lt_code a₁ b₁ 1 0).le.trans le_add_self)
        b₁ ((snd_lt_code a₁ b₁ 1 0).le.trans le_add_self) le_rfl
    constructor
    · intro a _ b _ y _ hsum hL hy h
      rcases eq_or_ne y 0 with rfl | hy0
      · rw [icmp₁_pos_zero (vcVadd_ne_zero a b 1 0)] at h
        exact absurd h _root_.two_ne_zero
      · obtain ⟨a', b', n', c', rfl⟩ : ∃ a b n c, y = vcVadd a b n c :=
          ⟨_, _, _, _, (vcVadd_destruct hy0).symm⟩
        obtain ⟨hn', ha', hb', -, hL', -, -⟩ := nf_parts hy
        obtain ⟨-, ha, hb, -, -, hfix, -⟩ := nf_parts hL
        have hbL' : vcVadd a b 1 0 + vcVadd a' b' n' c' ≤ w := hsum
        rw [icmp₁_lead_form _root_.one_ne_zero hn'] at h
        rcases thenV_eq_zero.mp h with h0 | ⟨h1, -⟩
        · rw [icmp₁_lead_lead] at h0
          rcases icmp₁_cases ha ha' with hA0 | hA1 | hA2
          · rw [hA0, leadV_zero] at h0
            exact lt_of_lt_lead hb hn' h0
          · rw [hA1, leadV_one] at h0
            have hbL : icmp₁ b (vcVadd a' b' 1 0) = 0 :=
              IH2 (lt_of_lt_of_le (sum2_lt_of (snd_lt_code a b 1 0).le (lead_le_code hn')
                (Or.inl (snd_lt_code a b 1 0))) hbL') hb hL' h0
            exact lt_of_lt_lead hb hn' hbL
          · rw [hA2, leadV_two] at h0
            have hbb : icmp₁ b b' = 0 :=
              IH1 (lt_of_lt_of_le (sum2_lt_of le_rfl (snd_lt_code a' b' n' c').le
                (Or.inr (snd_lt_code a' b' n' c'))) hbL') hL hb' h0
            have hbL : icmp₁ b (vcVadd a' b' 1 0) = 0 :=
              IH2 (lt_of_lt_of_le (sum2_lt_of (snd_lt_code a b 1 0).le (lead_le_code hn')
                (Or.inl (snd_lt_code a b 1 0))) hbL') hb hL' hbb
            exact lt_of_lt_lead hb hn' hbL
        · have hLL : vcVadd a b 1 0 = vcVadd a' b' 1 0 := icmp₁_eq_imp_eq hL hL' h1
          rw [hLL] at hfix
          exact lt_of_lt_lead hb hn' hfix
    · intro x _ a' _ b' _ hsum hx hL' h
      rcases eq_or_ne x 0 with rfl | hx0
      · exact icmp₁_zero_vcVadd _ _ _ _
      · obtain ⟨a, b, n, c, rfl⟩ : ∃ a b n c, x = vcVadd a b n c :=
          ⟨_, _, _, _, (vcVadd_destruct hx0).symm⟩
        obtain ⟨hn, ha, hb, -, hL, -, -⟩ := nf_parts hx
        obtain ⟨-, ha', hb', -, -, -, -⟩ := nf_parts hL'
        have hxL' : vcVadd a b n c + vcVadd a' b' 1 0 ≤ w := hsum
        -- step 1: the leading term of `x` is below `b'`
        have hLb' : icmp₁ (vcVadd a b 1 0) b' = 0 := by
          rcases eq_or_ne b' 0 with rfl | hb'0
          · exact absurd h (icmp₁_right_zero_ne_zero _)
          · obtain ⟨p, q, m, d, rfl⟩ : ∃ p q m d, b' = vcVadd p q m d :=
              ⟨_, _, _, _, (vcVadd_destruct hb'0).symm⟩
            obtain ⟨hm, -, -, -, -, -, -⟩ := nf_parts hb'
            exact lead_lt_of_lt hn hm h
        -- step 2: the leading terms compare
        have hLL' : icmp₁ (vcVadd a b 1 0) (vcVadd a' b' 1 0) = 0 := by
          rw [icmp₁_lead_lead]
          have hbb' : icmp₁ b b' = 0 :=
            IH1 (lt_of_lt_of_le (sum2_lt_of (lead_le_code hn) (snd_lt_code a' b' 1 0).le
              (Or.inr (snd_lt_code a' b' 1 0))) hxL') hL hb' hLb'
          rcases icmp₁_cases ha ha' with hA0 | hA1 | hA2
          · rw [hA0, leadV_zero]
            exact IH2 (lt_of_lt_of_le (sum2_lt_of (snd_lt_code a b n c).le le_rfl
              (Or.inl (snd_lt_code a b n c))) hxL') hb hL' hbb'
          · rw [hA1, leadV_one]
            exact hbb'
          · rw [hA2, leadV_two]
            exact hLb'
        exact lt_of_lead_lt hn _root_.one_ne_zero hLL'

/-- (T') `φ_a(b) < y → b < y` on normal codes. -/
lemma snd_lt_of_lead_lt {a b y : V} (hL : isNF₁ (vcVadd a b 1 0)) (hy : isNF₁ y)
    (h : icmp₁ (vcVadd a b 1 0) y = 0) : icmp₁ b y = 0 :=
  (veblen_mono_aux (vcVadd a b 1 0 + y)).1 a ((fst_lt_code a b 1 0).le.trans le_self_add)
    b ((snd_lt_code a b 1 0).le.trans le_self_add) y le_add_self le_rfl hL hy h

/-- (T'') `x < b' → x < φ_{a'}(b')` on normal codes. -/
lemma lt_lead_of_lt_snd {x a' b' : V} (hx : isNF₁ x) (hL' : isNF₁ (vcVadd a' b' 1 0))
    (h : icmp₁ x b' = 0) : icmp₁ x (vcVadd a' b' 1 0) = 0 :=
  (veblen_mono_aux (x + vcVadd a' b' 1 0)).2 x le_self_add
    a' ((fst_lt_code a' b' 1 0).le.trans le_add_self)
    b' ((snd_lt_code a' b' 1 0).le.trans le_add_self) le_rfl hx hL' h

/-! ### Transitivity -/

private lemma sum3_lt_of {x y z x' y' z' : V} (hx : x' ≤ x) (hy : y' ≤ y) (hz : z' ≤ z)
    (hs : x' < x ∨ y' < y ∨ z' < z) : x' + y' + z' < x + y + z := by
  rcases hs with h | h | h
  · exact add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le h hy) hz
  · exact add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt hx h) hz
  · exact add_lt_add_of_le_of_lt (add_le_add hx hy) h

lemma icmp₁_trans_aux : ∀ w : V, ∀ x ≤ w, ∀ y ≤ w, ∀ z ≤ w, x + y + z ≤ w →
    isNF₁ x → isNF₁ y → isNF₁ z → icmp₁ x y = 0 → icmp₁ y z = 0 → icmp₁ x z = 0 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro x hxw y hyw z hzw hsum hx hy hz hxy hyz
    have IH : ∀ {x' y' z' : V}, x' + y' + z' < w → isNF₁ x' → isNF₁ y' → isNF₁ z' →
        icmp₁ x' y' = 0 → icmp₁ y' z' = 0 → icmp₁ x' z' = 0 :=
      fun {x' y' z'} hlt => ih (x' + y' + z') hlt
        x' (le_trans le_self_add le_self_add) y' (le_trans le_add_self le_self_add)
        z' le_add_self le_rfl
    rcases eq_or_ne x 0 with rfl | hx0
    · have hz0 : z ≠ 0 := by
        rintro rfl
        exact icmp₁_right_zero_ne_zero y hyz
      exact icmp₁_zero_pos hz0
    · have hy0 : y ≠ 0 := by
        rintro rfl
        exact icmp₁_right_zero_ne_zero x hxy
      have hz0 : z ≠ 0 := by
        rintro rfl
        exact icmp₁_right_zero_ne_zero y hyz
      obtain ⟨a, b, n, c, rfl⟩ : ∃ a b n c, x = vcVadd a b n c :=
        ⟨_, _, _, _, (vcVadd_destruct hx0).symm⟩
      obtain ⟨a', b', n', c', rfl⟩ : ∃ a b n c, y = vcVadd a b n c :=
        ⟨_, _, _, _, (vcVadd_destruct hy0).symm⟩
      obtain ⟨a'', b'', n'', c'', rfl⟩ : ∃ a b n c, z = vcVadd a b n c :=
        ⟨_, _, _, _, (vcVadd_destruct hz0).symm⟩
      obtain ⟨hn, ha, hb, hc, hL, -, -⟩ := nf_parts hx
      obtain ⟨hn', ha', hb', hc', hL', -, -⟩ := nf_parts hy
      obtain ⟨hn'', ha'', hb'', hc'', hL'', -, -⟩ := nf_parts hz
      have hS : vcVadd a b n c + vcVadd a' b' n' c' + vcVadd a'' b'' n'' c'' ≤ w := hsum
      -- bounds of the pieces
      have hLx := lead_le_code (a := a) (b := b) (c := c) hn
      have hLy := lead_le_code (a := a') (b := b') (c := c') hn'
      have hLz := lead_le_code (a := a'') (b := b'') (c := c'') hn''
      have hax := fst_lt_code a b n c
      have hay := fst_lt_code a' b' n' c'
      have haz := fst_lt_code a'' b'' n'' c''
      have hbx := snd_lt_code a b n c
      have hby := snd_lt_code a' b' n' c'
      have hbz := snd_lt_code a'' b'' n'' c''
      have hcx := tail_lt_code a b n c
      have hcy := tail_lt_code a' b' n' c'
      have hcz := tail_lt_code a'' b'' n'' c''
      -- transitivity of the leading terms
      have TT : icmp₁ (vcVadd a b 1 0) (vcVadd a' b' 1 0) = 0 →
          icmp₁ (vcVadd a' b' 1 0) (vcVadd a'' b'' 1 0) = 0 →
          icmp₁ (vcVadd a b 1 0) (vcVadd a'' b'' 1 0) = 0 := by
        intro h1 h2
        have h1' := h1
        have h2' := h2
        rw [icmp₁_lead_lead] at h1 h2
        rcases icmp₁_cases ha ha' with hA0 | hA1 | hA2 <;>
          rcases icmp₁_cases ha' ha'' with hB0 | hB1 | hB2
        · -- a < a', a' < a''
          rw [hA0, leadV_zero] at h1
          rw [hB0, leadV_zero] at h2
          have hAC : icmp₁ a a'' = 0 :=
            IH (lt_of_lt_of_le (sum3_lt_of hax.le hay.le haz.le (Or.inl hax)) hS)
              ha ha' ha'' hA0 hB0
          rw [icmp₁_lead_lead, hAC, leadV_zero]
          exact IH (lt_of_lt_of_le (sum3_lt_of hbx.le hLy hLz (Or.inl hbx)) hS)
            hb hL' hL'' h1 h2'
        · -- a < a', a' = a''
          have e := icmp₁_eq_imp_eq ha' ha'' hB1
          subst e
          rw [hA0, leadV_zero] at h1
          rw [icmp₁_lead_lead, hA0, leadV_zero]
          exact IH (lt_of_lt_of_le (sum3_lt_of hbx.le hLy hLz (Or.inl hbx)) hS)
            hb hL' hL'' h1 h2'
        · -- a < a', a' > a''
          rw [hA0, leadV_zero] at h1
          rw [hB2, leadV_two] at h2
          have hbb'' : icmp₁ b b'' = 0 :=
            IH (lt_of_lt_of_le (sum3_lt_of hbx.le hLy hbz.le (Or.inl hbx)) hS)
              hb hL' hb'' h1 h2
          rw [icmp₁_lead_lead]
          rcases icmp₁_cases ha ha'' with hC0 | hC1 | hC2
          · rw [hC0, leadV_zero]
            exact lt_lead_of_lt_snd hb hL'' hbb''
          · rw [hC1, leadV_one]
            exact hbb''
          · rw [hC2, leadV_two]
            exact IH (lt_of_lt_of_le (sum3_lt_of hLx hLy hbz.le (Or.inr (Or.inr hbz))) hS)
              hL hL' hb'' h1' h2
        · -- a = a', a' < a''
          have e := icmp₁_eq_imp_eq ha ha' hA1
          subst e
          rw [hA1, leadV_one] at h1
          rw [hB0, leadV_zero] at h2
          rw [icmp₁_lead_lead, hB0, leadV_zero]
          exact IH (lt_of_lt_of_le (sum3_lt_of hbx.le hby.le hLz (Or.inl hbx)) hS)
            hb hb' hL'' h1 h2
        · -- a = a' = a''
          have e := icmp₁_eq_imp_eq ha ha' hA1
          subst e
          have e := icmp₁_eq_imp_eq ha' ha'' hB1
          subst e
          rw [hA1, leadV_one] at h1
          rw [hB1, leadV_one] at h2
          rw [icmp₁_lead_lead, icmp₁_self ha, leadV_one]
          exact IH (lt_of_lt_of_le (sum3_lt_of hbx.le hby.le hbz.le (Or.inl hbx)) hS)
            hb hb' hb'' h1 h2
        · -- a = a', a' > a''
          have e := icmp₁_eq_imp_eq ha ha' hA1
          subst e
          rw [hB2, leadV_two] at h2
          rw [icmp₁_lead_lead, hB2, leadV_two]
          exact IH (lt_of_lt_of_le (sum3_lt_of hLx hLy hbz.le (Or.inr (Or.inr hbz))) hS)
            hL hL' hb'' h1' h2
        · -- a > a', a' < a''
          rw [hA2, leadV_two] at h1
          rw [hB0, leadV_zero] at h2
          exact IH (lt_of_lt_of_le (sum3_lt_of hLx hby.le hLz (Or.inr (Or.inl hby))) hS)
            hL hb' hL'' h1 h2
        · -- a > a', a' = a''
          have e := icmp₁_eq_imp_eq ha' ha'' hB1
          subst e
          rw [hA2, leadV_two] at h1
          rw [hB1, leadV_one] at h2
          rw [icmp₁_lead_lead, hA2, leadV_two]
          exact IH (lt_of_lt_of_le (sum3_lt_of hLx hby.le hbz.le (Or.inr (Or.inl hby))) hS)
            hL hb' hb'' h1 h2
        · -- a > a', a' > a''
          rw [hA2, leadV_two] at h1
          rw [hB2, leadV_two] at h2
          have hAC : icmp₁ a a'' = 2 := by
            have h1a : icmp₁ a'' a' = 0 := icmp₁_rev_two ha' ha'' hB2
            have h2a : icmp₁ a' a = 0 := icmp₁_rev_two ha ha' hA2
            have hlt : a'' + a' + a < w := by
              have e : a'' + a' + a = a + a' + a'' := by
                rw [add_comm (a'' + a') a, add_comm a'' a', ← add_assoc]
              rw [e]
              exact lt_of_lt_of_le (sum3_lt_of hax.le hay.le haz.le (Or.inl hax)) hS
            exact icmp₁_rev_zero ha'' ha (IH hlt ha'' ha' ha h1a h2a)
          rw [icmp₁_lead_lead, hAC, leadV_two]
          exact IH (lt_of_lt_of_le (sum3_lt_of hLx hLy hbz.le (Or.inr (Or.inr hbz))) hS)
            hL hL' hb'' h1' h2
      -- the main combination
      rw [icmp₁_lead_form hn hn'] at hxy
      rw [icmp₁_lead_form hn' hn''] at hyz
      rw [icmp₁_lead_form hn hn'']
      rcases thenV_eq_zero.mp hxy with h1 | ⟨h1, r1⟩ <;>
        rcases thenV_eq_zero.mp hyz with h2 | ⟨h2, r2⟩
      · exact thenV_eq_zero.mpr (Or.inl (TT h1 h2))
      · have e := icmp₁_eq_imp_eq hL' hL'' h2
        rw [← e]
        exact thenV_eq_zero.mpr (Or.inl h1)
      · have e := icmp₁_eq_imp_eq hL hL' h1
        rw [e]
        exact thenV_eq_zero.mpr (Or.inl h2)
      · have e1 := icmp₁_eq_imp_eq hL hL' h1
        have e2 := icmp₁_eq_imp_eq hL' hL'' h2
        rw [e1, e2, icmp₁_self hL'', thenV_one_left]
        rcases thenV_eq_zero.mp r1 with q1 | ⟨q1, s1⟩ <;>
          rcases thenV_eq_zero.mp r2 with q2 | ⟨q2, s2⟩
        · exact thenV_eq_zero.mpr
            (Or.inl (cmpV_eq_zero.mpr (lt_trans (cmpV_eq_zero.mp q1) (cmpV_eq_zero.mp q2))))
        · rw [← cmpV_eq_one.mp q2]
          exact thenV_eq_zero.mpr (Or.inl q1)
        · rw [cmpV_eq_one.mp q1]
          exact thenV_eq_zero.mpr (Or.inl q2)
        · rw [cmpV_eq_one.mp q1, cmpV_eq_one.mp q2, cmpV_self]
          refine thenV_eq_zero.mpr (Or.inr ⟨rfl, ?_⟩)
          exact IH (lt_of_lt_of_le (sum3_lt_of hcx.le hcy.le hcz.le (Or.inl hcx)) hS)
            hc hc' hc'' s1 s2

/-- **Transitivity of the internal Veblen order on normal codes.** -/
lemma icmp₁_trans {x y z : V} (hx : isNF₁ x) (hy : isNF₁ y) (hz : isNF₁ z)
    (hxy : icmp₁ x y = 0) (hyz : icmp₁ y z = 0) : icmp₁ x z = 0 :=
  icmp₁_trans_aux (x + y + z) x (le_trans le_self_add le_self_add)
    y (le_trans le_add_self le_self_add) z le_add_self le_rfl hx hy hz hxy hyz

/-! ### Two small facts about the code of `1` -/

/-- Below the code of `1 = φ_0(0)` there is only `0`. -/
lemma eq_zero_of_lt_one {t : V} (ht : isNF₁ t) (h : icmp₁ t (vcVadd 0 0 1 0) = 0) : t = 0 := by
  by_contra ht0
  obtain ⟨p, q, m, d, rfl⟩ : ∃ p q m d, t = vcVadd p q m d :=
    ⟨_, _, _, _, (vcVadd_destruct ht0).symm⟩
  obtain ⟨hm, -, -, -, -, -, -⟩ := nf_parts ht
  rw [icmp₁_lead_form hm _root_.one_ne_zero] at h
  rcases thenV_eq_zero.mp h with h0 | ⟨-, hrest⟩
  · rw [icmp₁_lead_lead] at h0
    rcases eq_or_ne p 0 with rfl | hp
    · rw [icmp₁_zero_zero, leadV_one] at h0
      exact icmp₁_right_zero_ne_zero q h0
    · rw [icmp₁_pos_zero hp, leadV_two] at h0
      exact icmp₁_right_zero_ne_zero _ h0
  · rcases thenV_eq_zero.mp hrest with h0 | ⟨-, h0⟩
    · exact hm (lt_one_iff_eq_zero.mp (cmpV_eq_zero.mp h0))
    · exact icmp₁_right_zero_ne_zero d h0

/-- Below the successor `L + 1` of a normal single term `L = φ_p(q)` a normal code is
either below `L` or equal to `L`. -/
lemma lt_or_eq_of_lt_term_succ {y p q : V} (hy : isNF₁ y) (hL : isNF₁ (vcVadd p q 1 0))
    (h : icmp₁ y (vcVadd p q 1 (vcVadd 0 0 1 0)) = 0) :
    icmp₁ y (vcVadd p q 1 0) = 0 ∨ y = vcVadd p q 1 0 := by
  rcases eq_or_ne y 0 with rfl | hy0
  · exact Or.inl (icmp₁_zero_vcVadd _ _ _ _)
  · obtain ⟨a, b, n, c, rfl⟩ : ∃ a b n c, y = vcVadd a b n c :=
      ⟨_, _, _, _, (vcVadd_destruct hy0).symm⟩
    obtain ⟨hn, -, -, hc, hLy, -, -⟩ := nf_parts hy
    rw [icmp₁_lead_form hn _root_.one_ne_zero] at h
    rcases thenV_eq_zero.mp h with h0 | ⟨h1, hrest⟩
    · exact Or.inl (lt_of_lead_lt hn _root_.one_ne_zero h0)
    · rcases thenV_eq_zero.mp hrest with h0 | ⟨hn1, hc1⟩
      · exact absurd (lt_one_iff_eq_zero.mp (cmpV_eq_zero.mp h0)) hn
      · have hn1' : n = 1 := cmpV_eq_one.mp hn1
        have hc0 : c = 0 := eq_zero_of_lt_one hc hc1
        have e := icmp₁_eq_imp_eq hLy hL h1
        right
        rw [hn1', hc0]
        exact e

end OrdinalAnalysis.Gentzen.InternalVNoteOrder
