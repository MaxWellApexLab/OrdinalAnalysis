/-
  Coefficient sets of the internal arithmetic, and the Cantor decomposition of codes, in
  every model of `IΣ₁`.

  The elements of `E` of a sum, of a power of `ω` and of `ω · α` come from the arguments:

  * `iinE_iomegaPow`: `E(ω^α) = E(α)`;
  * `iinE_of_iinE_iadd`, `iinE_of_iinE_inadd`: `E(α + β), E(α ⊕ β) ⊆ E(α) ∪ E(β)`,
    and `iinE_iadd_of_iinE_right`: `E(β) ⊆ E(α + β)`;
  * `iinE_of_iinE_ionePlus`, `iinE_of_iinE_iomegaMul`, `iinE_of_iinE_isucc`,
    `not_iinE_inum`: `E(1 + α), E(ω · α), E(α + 1) ⊆ E(α)`, `E(n) = ∅`.

  `iadd_iomegaPow_tail` writes a normal sum `⟨α₀, α₁, …⟩` as `ω^α₀ + ⟨α₁, …⟩`.
-/
import OrdinalAnalysis.ID1.Internal.ArithLaws

set_option autoImplicit false

namespace OrdinalAnalysis.ID1.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.Gentzen.InternalONote

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Exponent lists -/

lemma iinE_single_iff (g x : V) : iinE g (tcCons x 0) = 1 ↔ iinE g x = 1 := by
  rw [iinE_tcCons_iff]; simp

lemma iinE_itoL (g x : V) : iinE g (itoL x) = 1 ↔ iinE g x = 1 := by
  by_cases hp : IsPrinC x
  · rw [itoL_of_prinC hp, iinE_single_iff]
  · rw [itoL_of_not_prinC hp]

lemma iinE_iofL (g s : V) : iinE g (iofL s) = 1 ↔ iinE g s = 1 := by
  rw [iofL_eq]
  split_ifs with h
  · have e := eq_tcCons_of_kind h.1
    rw [h.2.1] at e
    conv_rhs => rw [e]
    rw [iinE_single_iff]
  · rfl

/-! ### `ω^·` -/

/-- `E(ω^α) = E(α)`. -/
theorem iinE_iomegaPow (g a : V) : iinE g (iomegaPow a) = 1 ↔ iinE g a = 1 := by
  rw [iomegaPow, iinE_iofL, iinE_single_iff]

/-! ### The sums -/

lemma iinE_iaddL_aux (g y w : V) : ∀ s : V, iinE g (iaddL s (tcCons y w)) = 1 →
    iinE g s = 1 ∨ iinE g (tcCons y w) = 1 := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro h
    by_cases hk : kind s = 3
    · obtain e := eq_tcCons_of_kind hk
      have hs0 : s ≠ 0 := ne_zero_of_kind_ne_zero (by simp [hk])
      rw [e, iaddL_cons_cons] at h
      rw [e, iinE_tcCons_iff]
      split_ifs at h
      · rcases (iinE_tcCons_iff _ _ _).mp h with h | h
        · exact Or.inl (Or.inl h)
        · rcases ih _ (tcTl_lt hs0) h with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
      · rcases ih _ (tcTl_lt hs0) h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    · rw [iaddL_cons, ifilt_of_kind hk, iapp_zero_left] at h
      exact Or.inr h

lemma iinE_of_iinE_iaddL {g s t : V} (h : iinE g (iaddL s t) = 1) :
    iinE g s = 1 ∨ iinE g t = 1 := by
  by_cases hk : kind t = 3
  · rw [eq_tcCons_of_kind hk] at h ⊢
    exact iinE_iaddL_aux g _ _ s h
  · rw [iaddL_of_kind s hk] at h; exact Or.inl h

/-- `E(α + β) ⊆ E(α) ∪ E(β)`. -/
theorem iinE_of_iinE_iadd {g a b : V} (h : iinE g (iadd a b) = 1) :
    iinE g a = 1 ∨ iinE g b = 1 := by
  rw [iadd, iinE_iofL] at h
  rcases iinE_of_iinE_iaddL h with h | h
  · exact Or.inl ((iinE_itoL g a).mp h)
  · exact Or.inr ((iinE_itoL g b).mp h)

lemma iinE_iaddL_right_aux (g y w : V) (hg : iinE g (tcCons y w) = 1) :
    ∀ s : V, iinE g (iaddL s (tcCons y w)) = 1 := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    by_cases hk : kind s = 3
    · obtain e := eq_tcCons_of_kind hk
      have hs0 : s ≠ 0 := ne_zero_of_kind_ne_zero (by simp [hk])
      rw [e, iaddL_cons_cons]
      split_ifs
      · rw [iinE_tcCons_iff]; exact Or.inr (ih _ (tcTl_lt hs0))
      · exact ih _ (tcTl_lt hs0)
    · rw [iaddL_cons, ifilt_of_kind hk, iapp_zero_left]; exact hg

/-- `E(β) ⊆ E(α + β)`. -/
theorem iinE_iadd_of_iinE_right {g b : V} (a : V) (h : iinE g b = 1) :
    iinE g (iadd a b) = 1 := by
  rw [iadd, iinE_iofL]
  have h' := (iinE_itoL g b).mpr h
  by_cases hk : kind (itoL b) = 3
  · rw [eq_tcCons_of_kind hk] at h' ⊢
    exact iinE_iaddL_right_aux g _ _ h' _
  · have hp : ¬ IsPrinC b := fun hp => hk (by rw [itoL_of_prinC hp]; simp)
    rw [itoL_of_not_prinC hp] at hk
    exfalso
    rcases code_cases b with rfl | ⟨x, s, rfl⟩ | ⟨c, rfl⟩ | hk'
    · simp at h
    · simp at hk
    · exact hp (isPrinC_tcTheta c)
    · rw [iinE_top g hk'] at h; simp at h

lemma iinE_imerge_aux (g : V) : ∀ w : V, ∀ s ≤ w, ∀ t ≤ w, s + t ≤ w →
    iinE g (imerge s t) = 1 → iinE g s = 1 ∨ iinE g t = 1 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro s _ t _ hsum h
    have IH : ∀ {s₁ t₁ : V}, s₁ + t₁ < s + t → iinE g (imerge s₁ t₁) = 1 →
        iinE g s₁ = 1 ∨ iinE g t₁ = 1 :=
      fun {s₁ t₁} hlt => ih (s₁ + t₁) (lt_of_lt_of_le hlt hsum) s₁ le_self_add t₁ le_add_self
        le_rfl
    by_cases hs : kind s = 3
    · by_cases ht : kind t = 3
      · obtain es := eq_tcCons_of_kind hs
        obtain et := eq_tcCons_of_kind ht
        have hs0 : s ≠ 0 := ne_zero_of_kind_ne_zero (by simp [hs])
        have ht0 : t ≠ 0 := ne_zero_of_kind_ne_zero (by simp [ht])
        rw [es, et, imerge_cons_cons] at h
        split_ifs at h
        · rcases (iinE_tcCons_iff _ _ _).mp h with h | h
          · left; rw [es, iinE_tcCons_iff]; exact Or.inl h
          · rw [← et] at h
            rcases IH (add_lt_add_of_lt_of_le (tcTl_lt hs0) le_rfl) h with h | h
            · left; rw [es, iinE_tcCons_iff]; exact Or.inr h
            · exact Or.inr h
        · rcases (iinE_tcCons_iff _ _ _).mp h with h | h
          · right; rw [et, iinE_tcCons_iff]; exact Or.inl h
          · rw [← es] at h
            rcases IH (add_lt_add_of_le_of_lt le_rfl (tcTl_lt ht0)) h with h | h
            · exact Or.inl h
            · right; rw [et, iinE_tcCons_iff]; exact Or.inr h
      · rw [eq_tcCons_of_kind hs, imerge_right_of_kind _ _ ht, ← eq_tcCons_of_kind hs] at h
        exact Or.inl h
    · rw [imerge_left_of_kind hs] at h; exact Or.inr h

/-- `E(α ⊕ β) ⊆ E(α) ∪ E(β)`. -/
theorem iinE_of_iinE_inadd {g a b : V} (h : iinE g (inadd a b) = 1) :
    iinE g a = 1 ∨ iinE g b = 1 := by
  rw [inadd, iinE_iofL] at h
  rcases iinE_imerge_aux g _ _ le_self_add _ le_add_self le_rfl h with h | h
  · exact Or.inl ((iinE_itoL g a).mp h)
  · exact Or.inr ((iinE_itoL g b).mp h)

/-! ### `1 + ·`, `ω · ·`, the successor and the numerals -/

@[simp] lemma iinE_ione (g : V) : iinE g ione = 0 := by
  rw [ione_eq, iinE_tcCons]; simp [bor]

/-- `E(1 + α) ⊆ E(α)`. -/
theorem iinE_of_iinE_ionePlus {g e : V} (h : iinE g (ionePlus e) = 1) : iinE g e = 1 := by
  rw [ionePlus_eq_iadd] at h
  rcases iinE_of_iinE_iadd h with h | h
  · rw [iinE_ione] at h; simp at h
  · exact h

lemma iinE_imapOP_aux (g : V) : ∀ s : V, iinE g (imapOP s) = 1 → iinE g s = 1 := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro h
    by_cases hk : kind s = 3
    · obtain e := eq_tcCons_of_kind hk
      have hs0 : s ≠ 0 := ne_zero_of_kind_ne_zero (by simp [hk])
      rw [e, imapOP_cons, iinE_tcCons_iff] at h
      rw [e, iinE_tcCons_iff]
      rcases h with h | h
      · exact Or.inl (iinE_of_iinE_ionePlus h)
      · exact Or.inr (ih _ (tcTl_lt hs0) h)
    · rw [imapOP_of_kind hk] at h; simp at h

/-- `E(ω · α) ⊆ E(α)`. -/
theorem iinE_of_iinE_iomegaMul {g a : V} (h : iinE g (iomegaMul a) = 1) : iinE g a = 1 := by
  rw [iomegaMul, iinE_iofL] at h
  exact (iinE_itoL g a).mp (iinE_imapOP_aux g _ h)

/-- `E(α + 1) ⊆ E(α)`. -/
theorem iinE_of_iinE_isucc {g a : V} (h : iinE g (isucc a) = 1) : iinE g a = 1 := by
  rcases iinE_of_iinE_inadd h with h | h
  · exact h
  · rw [iinE_ione] at h; simp at h

/-- The numerals have empty coefficient sets. -/
theorem not_iinE_inum (g : V) : ∀ n : V, iinE g (inum n) ≠ 1 := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [inum_succ, ne_eq, iinE_tcCons_iff]
    simpa using ih

/-! ### The Cantor decomposition -/

lemma itoL_iofL {s : V} (hs : sumK s = 1) : itoL (iofL s) = s := by
  rw [iofL_eq]
  split_ifs with h
  · rw [itoL_of_prinC h.2.2]
    have e := eq_tcCons_of_kind h.1
    rw [h.2.1] at e
    exact e.symm
  · rcases eq_or_ne s 0 with rfl | hs0
    · simp
    · rw [itoL_of_not_prinC]
      rw [eq_tcCons_of_kind (kind_eq_three_of_sumK hs hs0)]
      exact not_isPrinC_tcCons _ _

/-- **The Cantor decomposition**: a normal sum `⟨α₀, α₁, …⟩` is `ω^α₀ + ⟨α₁, …⟩`. -/
theorem iadd_iomegaPow_tail {y s : V} (h : isNF (tcCons y s)) :
    iadd (iomegaPow y) (iofL s) = tcCons y s := by
  have hsl := isSL_itoL h
  rw [itoL_tcCons] at hsl
  obtain ⟨-, hs, hds⟩ := (isSL_cons_iff y s).mp hsl
  have htoL : itoL (iomegaPow y) = tcCons y 0 := by
    by_cases hp : IsPrinC y
    · rw [iomegaPow_of_prin hp, itoL_of_prinC hp]
    · rw [iomegaPow_of_not_prin hp, itoL_tcCons]
  rw [iadd, htoL, itoL_iofL hs.2]
  have hl : iaddL (tcCons y 0) s = tcCons y s := by
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [iaddL_zero_right]
    · obtain ⟨z, w, rfl⟩ := eq_cons_of_sumK hs.2 hs0
      have hyz : ige y z = 1 := by simpa using hds.resolve_left hs0
      rw [iaddL_cons_cons, if_pos hyz, iaddL_cons, ifilt_zero, iapp_zero_left]
  rw [hl, iofL_cons, if_neg]
  intro h'
  have := sok_of_isNF h
  rw [sok_tcCons, if_pos ⟨h'.1, h'.2⟩] at this
  simp at this

end OrdinalAnalysis.ID1.Internal
