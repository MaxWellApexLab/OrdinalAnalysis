/-
  Order-free facts about the internal codes of the multi-level ϑ-notation, inside every model
  of `IΣ₁`, used by the well-ordering proof of `IDn/WellOrdering.lean`.

  Everything here is about the constructors, the coefficient sets `iinE k` (`E_k`) and the
  argument sets `iinG k` (`G_k`) of `IDn/Internal/Codes.lean`; nothing uses the order.

  * `itoL`: the exponent list of a code (`⟨c⟩` for a principal code, `c` itself otherwise), as
    in `ID1/Internal/Arith.lean`, with `iinE_itoL`, `iinG_itoL`.
  * `iinE`/`iinG` vanish on codes that are neither collapses nor sums.
  * `le_of_iinE`: a coefficient is a smaller number; `iinE_kind`: a coefficient of `E_k` is a
    code `ϑ_j δ` with `j ≤ k`;
  * `iinE_trans`: `E_j(g) ⊆ E_j(c)` for `g ∈ E_k(c)`, `j ≤ k`
    (`ThetaWTerm.mem_E_of_mem_E`);
  * `iinG_mono`: `G_k(c) ⊆ G_i(c)` for `i ≤ k`; `iinG_trans`: `G_i` is transitive;
    `iinG_of_iinE`: the argument `d` of a level-`k` coefficient `ϑ_k d ∈ E_k(c)` is in
    `G_i(c)` for every `i < k`.
-/
import OrdinalAnalysis.IDn.Internal.Codes

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.IDn.Internal
open OrdinalAnalysis.ID1.Internal (bor beq bor_eq_one beq_eq_one)

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The exponent list of a code -/

/-- The exponent list of a code: `⟨c⟩` for the principal codes, `c` itself otherwise. -/
noncomputable def itoL (c : V) : V := if kind c = 1 ∨ kind c = 2 then tcCons c 0 else c

def itoLDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ k, !kindDef k c ∧ (((k = 1 ∨ k = 2) ∧ !tcConsDef y c 0) ∨ (k ≠ 1 ∧ k ≠ 2 ∧ y = c))”

instance itoL_defined : 𝚺₁-Function₁ (itoL : V → V) via itoLDef := .mk fun v ↦ by
  simp [itoLDef, itoL, kind_defined.iff, tcCons_defined.iff]
  by_cases h : kind (v 1) = 1 ∨ kind (v 1) = 2
  · rw [if_pos h]; tauto
  · rw [if_neg h]; rw [not_or] at h; tauto

instance itoL_definable : 𝚺₁-Function₁ (itoL : V → V) := itoL_defined.to_definable
instance itoL_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (itoL : V → V) :=
  itoL_definable.of_sigmaOne

@[simp] lemma itoL_zero : itoL (0 : V) = 0 := by simp [itoL]

@[simp] lemma itoL_tcOmega (i : V) : itoL (tcOmega i) = tcCons (tcOmega i) 0 := by simp [itoL]

@[simp] lemma itoL_tcTheta (i a : V) : itoL (tcTheta i a) = tcCons (tcTheta i a) 0 := by
  simp [itoL]

@[simp] lemma itoL_tcCons (x s : V) : itoL (tcCons x s) = tcCons x s := by simp [itoL]

lemma itoL_of_prin {c : V} (h : kind c = 1 ∨ kind c = 2) : itoL c = tcCons c 0 := by
  simp [itoL, h]

lemma itoL_of_not_prin {c : V} (h : ¬ (kind c = 1 ∨ kind c = 2)) : itoL c = c := by
  simp [itoL, h]

lemma itoL_ne_zero {c : V} (hc0 : c ≠ 0) : itoL c ≠ 0 := by
  unfold itoL; split_ifs
  · exact tcCons_ne_zero _ _
  · exact hc0

/-! ### `E_k` and `G_k` on codes that are neither collapses nor sums -/

lemma iinE_eq_zero_of_kind (k g : V) {c : V} (h2 : kind c ≠ 2) (h3 : kind c ≠ 3) :
    iinE k g c = 0 := by
  obtain ⟨S, h, -⟩ := iinE_unfold k g c
  rw [h, inEStep]
  simp only [pi₁_pair, pi₂_pair]
  simp [h2, h3]

lemma iinG_eq_zero_of_kind (k x : V) {c : V} (h2 : kind c ≠ 2) (h3 : kind c ≠ 3) :
    iinG k x c = 0 := by
  obtain ⟨S, h, -⟩ := iinG_unfold k x c
  rw [h, inGStep]
  simp only [pi₁_pair, pi₂_pair]
  simp [h2, h3]

@[simp] lemma iinE_zero (k g : V) : iinE k g (0 : V) = 0 :=
  iinE_eq_zero_of_kind k g (by simp) (by simp)

@[simp] lemma iinG_zero (k x : V) : iinG k x (0 : V) = 0 :=
  iinG_eq_zero_of_kind k x (by simp) (by simp)

@[simp] lemma iinE_tcOmega (k g i : V) : iinE k g (tcOmega i) = 0 :=
  iinE_eq_zero_of_kind k g (by simp) (by simp)

@[simp] lemma iinG_tcOmega (k x i : V) : iinG k x (tcOmega i) = 0 :=
  iinG_eq_zero_of_kind k x (by simp) (by simp)

lemma iinE_tcCons_iff (k g x s : V) :
    iinE k g (tcCons x s) = 1 ↔ iinE k g x = 1 ∨ iinE k g s = 1 := by
  rw [iinE_tcCons, bor_eq_one]

lemma iinG_tcCons_iff (k y x s : V) :
    iinG k y (tcCons x s) = 1 ↔ iinG k y x = 1 ∨ iinG k y s = 1 := by
  rw [iinG_tcCons, bor_eq_one]

lemma iinE_tcTheta_self {k j a : V} (hjk : j ≤ k) : iinE k (tcTheta j a) (tcTheta j a) = 1 := by
  rw [iinE_tcTheta_of_le hjk, beq_eq_one]

lemma iinE_tcTheta_le_iff {k j a g : V} (hjk : j ≤ k) :
    iinE k g (tcTheta j a) = 1 ↔ g = tcTheta j a := by
  rw [iinE_tcTheta_of_le hjk, beq_eq_one]

lemma iinG_tcTheta_lt_iff {k j a x : V} (hkj : k < j) :
    iinG k x (tcTheta j a) = 1 ↔ x = a ∨ iinG k x a = 1 := by
  rw [iinG_tcTheta_of_lt hkj, bor_eq_one, beq_eq_one]

@[simp] lemma iinE_itoL (k g x : V) : iinE k g (itoL x) = 1 ↔ iinE k g x = 1 := by
  unfold itoL; split_ifs
  · rw [iinE_tcCons_iff, iinE_zero]; simp
  · rfl

@[simp] lemma iinG_itoL (k y x : V) : iinG k y (itoL x) = 1 ↔ iinG k y x = 1 := by
  unfold itoL; split_ifs
  · rw [iinG_tcCons_iff, iinG_zero]; simp
  · rfl

/-! ### The shape and size of coefficients -/

/-- A coefficient of `E_k(c)` is a code `ϑ_j δ` with `j ≤ k`, and no larger than `c`. -/
lemma iinE_kind (k : V) : ∀ c : V, ∀ g, iinE k g c = 1 → kind g = 2 ∧ tcLev g ≤ k ∧ g ≤ c := by
  intro c
  induction c using ISigma1.pi1_order_induction
  · definability
  case ind c ih =>
    intro g hg
    rcases kind_cases c with h | h | h | h | h
    · rw [iinE_eq_zero_of_kind k g (by simp [h]) (by simp [h])] at hg; simp at hg
    · rw [iinE_eq_zero_of_kind k g (by simp [h]) (by simp [h])] at hg; simp at hg
    · rw [eq_tcTheta_of_kind h] at hg ⊢
      by_cases hj : tcLev c ≤ k
      · rw [iinE_tcTheta_le_iff hj] at hg
        subst hg
        simp [hj]
      · rw [iinE_tcTheta_of_lt (not_le.mp hj)] at hg
        have hlt : tcThetaArg c < c := tcThetaArg_lt (by rintro rfl; simp at h)
        obtain ⟨h1, h2, h3⟩ := ih _ hlt g hg
        refine ⟨h1, h2, le_trans h3 (le_of_lt ?_)⟩
        rw [← eq_tcTheta_of_kind h]; exact hlt
    · have hc0 : c ≠ 0 := by rintro rfl; simp at h
      rw [eq_tcCons_of_kind h, iinE_tcCons_iff] at hg
      rcases hg with hg | hg
      · obtain ⟨h1, h2, h3⟩ := ih _ (tcHd_lt hc0) g hg
        exact ⟨h1, h2, le_trans h3 (le_of_lt (tcHd_lt hc0))⟩
      · obtain ⟨h1, h2, h3⟩ := ih _ (tcTl_lt hc0) g hg
        exact ⟨h1, h2, le_trans h3 (le_of_lt (tcTl_lt hc0))⟩
    · rw [iinE_eq_zero_of_kind k g (by simp [h]) (by simp [h])] at hg; simp at hg

lemma le_of_iinE {k g c : V} (h : iinE k g c = 1) : g ≤ c := (iinE_kind k c g h).2.2

lemma eq_tcTheta_of_iinE {k g c : V} (h : iinE k g c = 1) :
    g = tcTheta (tcLev g) (tcThetaArg g) ∧ tcLev g ≤ k :=
  ⟨eq_tcTheta_of_kind (iinE_kind k c g h).1, (iinE_kind k c g h).2.1⟩

/-- **`E_j(g) ⊆ E_j(c)` for `g ∈ E_k(c)`, `j ≤ k`.** -/
lemma iinE_trans {j k : V} (hjk : j ≤ k) :
    ∀ c : V, ∀ g h, iinE k g c = 1 → iinE j h g = 1 → iinE j h c = 1 := by
  intro c
  induction c using ISigma1.pi1_order_induction
  · definability
  case ind c ih =>
    intro g h hg hh
    rcases kind_cases c with hc | hc | hc | hc | hc
    · rw [iinE_eq_zero_of_kind k g (by simp [hc]) (by simp [hc])] at hg; simp at hg
    · rw [iinE_eq_zero_of_kind k g (by simp [hc]) (by simp [hc])] at hg; simp at hg
    · have hc0 : c ≠ 0 := by rintro rfl; simp at hc
      rw [eq_tcTheta_of_kind hc] at hg ⊢
      by_cases hi : tcLev c ≤ k
      · rw [iinE_tcTheta_le_iff hi] at hg
        rw [← hg]; exact hh
      · have hki : k < tcLev c := not_le.mp hi
        rw [iinE_tcTheta_of_lt hki] at hg
        rw [iinE_tcTheta_of_lt (lt_of_le_of_lt hjk hki)]
        exact ih _ (tcThetaArg_lt hc0) g h hg hh
    · have hc0 : c ≠ 0 := by rintro rfl; simp at hc
      rw [eq_tcCons_of_kind hc, iinE_tcCons_iff] at hg ⊢
      rcases hg with hg | hg
      · exact Or.inl (ih _ (tcHd_lt hc0) g h hg hh)
      · exact Or.inr (ih _ (tcTl_lt hc0) g h hg hh)
    · rw [iinE_eq_zero_of_kind k g (by simp [hc]) (by simp [hc])] at hg; simp at hg

/-- **`G_k(c) ⊆ G_i(c)` for `i ≤ k`.** -/
lemma iinG_mono {i k : V} (hik : i ≤ k) :
    ∀ c : V, ∀ y, iinG k y c = 1 → iinG i y c = 1 := by
  intro c
  induction c using ISigma1.pi1_order_induction
  · definability
  case ind c ih =>
    intro y hy
    rcases kind_cases c with hc | hc | hc | hc | hc
    · rw [iinG_eq_zero_of_kind k y (by simp [hc]) (by simp [hc])] at hy; simp at hy
    · rw [iinG_eq_zero_of_kind k y (by simp [hc]) (by simp [hc])] at hy; simp at hy
    · have hc0 : c ≠ 0 := by rintro rfl; simp at hc
      rw [eq_tcTheta_of_kind hc] at hy ⊢
      by_cases hj : k < tcLev c
      · rw [iinG_tcTheta_lt_iff hj] at hy
        rw [iinG_tcTheta_lt_iff (lt_of_le_of_lt hik hj)]
        rcases hy with hy | hy
        · exact Or.inl hy
        · exact Or.inr (ih _ (tcThetaArg_lt hc0) y hy)
      · rw [iinG_tcTheta_of_le (not_lt.mp hj)] at hy; simp at hy
    · have hc0 : c ≠ 0 := by rintro rfl; simp at hc
      rw [eq_tcCons_of_kind hc, iinG_tcCons_iff] at hy ⊢
      rcases hy with hy | hy
      · exact Or.inl (ih _ (tcHd_lt hc0) y hy)
      · exact Or.inr (ih _ (tcTl_lt hc0) y hy)
    · rw [iinG_eq_zero_of_kind k y (by simp [hc]) (by simp [hc])] at hy; simp at hy

/-- **`G_i` is transitive.** -/
lemma iinG_trans (i : V) : ∀ c : V, ∀ d y, iinG i d c = 1 → iinG i y d = 1 → iinG i y c = 1 := by
  intro c
  induction c using ISigma1.pi1_order_induction
  · definability
  case ind c ih =>
    intro d y hd hy
    rcases kind_cases c with hc | hc | hc | hc | hc
    · rw [iinG_eq_zero_of_kind i d (by simp [hc]) (by simp [hc])] at hd; simp at hd
    · rw [iinG_eq_zero_of_kind i d (by simp [hc]) (by simp [hc])] at hd; simp at hd
    · have hc0 : c ≠ 0 := by rintro rfl; simp at hc
      rw [eq_tcTheta_of_kind hc] at hd ⊢
      by_cases hj : i < tcLev c
      · rw [iinG_tcTheta_lt_iff hj] at hd ⊢
        rcases hd with rfl | hd
        · exact Or.inr hy
        · exact Or.inr (ih _ (tcThetaArg_lt hc0) d y hd hy)
      · rw [iinG_tcTheta_of_le (not_lt.mp hj)] at hd; simp at hd
    · have hc0 : c ≠ 0 := by rintro rfl; simp at hc
      rw [eq_tcCons_of_kind hc, iinG_tcCons_iff] at hd ⊢
      rcases hd with hd | hd
      · exact Or.inl (ih _ (tcHd_lt hc0) d y hd hy)
      · exact Or.inr (ih _ (tcTl_lt hc0) d y hd hy)
    · rw [iinG_eq_zero_of_kind i d (by simp [hc]) (by simp [hc])] at hd; simp at hd

/-- **The argument of a level-`k` coefficient `ϑ_k d ∈ E_k(c)` is in `G_i(c)`, `i < k`.** -/
lemma iinG_of_iinE {i k : V} (hik : i < k) :
    ∀ c : V, ∀ d, iinE k (tcTheta k d) c = 1 → iinG i d c = 1 := by
  intro c
  induction c using ISigma1.pi1_order_induction
  · definability
  case ind c ih =>
    intro d hd
    rcases kind_cases c with hc | hc | hc | hc | hc
    · rw [iinE_eq_zero_of_kind k _ (by simp [hc]) (by simp [hc])] at hd; simp at hd
    · rw [iinE_eq_zero_of_kind k _ (by simp [hc]) (by simp [hc])] at hd; simp at hd
    · have hc0 : c ≠ 0 := by rintro rfl; simp at hc
      rw [eq_tcTheta_of_kind hc] at hd ⊢
      by_cases hj : tcLev c ≤ k
      · rw [iinE_tcTheta_le_iff hj] at hd
        have e := hd
        have hl : k = tcLev c := by
          have := congrArg tcLev e; simpa using this
        have ha : d = tcThetaArg c := by
          have := congrArg tcThetaArg e; simpa using this
        rw [iinG_tcTheta_lt_iff (by rw [← hl]; exact hik)]
        exact Or.inl ha
      · have hkj : k < tcLev c := not_le.mp hj
        rw [iinE_tcTheta_of_lt hkj] at hd
        rw [iinG_tcTheta_lt_iff (lt_trans hik hkj)]
        exact Or.inr (ih _ (tcThetaArg_lt hc0) d hd)
    · have hc0 : c ≠ 0 := by rintro rfl; simp at hc
      rw [eq_tcCons_of_kind hc, iinE_tcCons_iff] at hd
      rw [eq_tcCons_of_kind hc, iinG_tcCons_iff]
      rcases hd with hd | hd
      · exact Or.inl (ih _ (tcHd_lt hc0) d hd)
      · exact Or.inr (ih _ (tcTl_lt hc0) d hd)
    · rw [iinE_eq_zero_of_kind k _ (by simp [hc]) (by simp [hc])] at hd; simp at hd

end Model

end OrdinalAnalysis.IDn.Upper
