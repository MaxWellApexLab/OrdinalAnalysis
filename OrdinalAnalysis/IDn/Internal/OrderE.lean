/-
  The coefficient sets `E_k` and the argument sets `G_k` of the coded multi-level ϑ-notation
  inside models of `IΣ₁` (the one-level template is `ID1/Internal/OrderE.lean`).

  * `iltb_self_cons`: `α₀ ≺ ⟨α₀, …⟩` (all codes);
  * `iltb_tail_cons`: a descending sum is below any sum obtained by prefixing an entry that
    is `≽` its first entry;
  * `ile_of_iinE`: `δ ∈ E_k(α) → δ ≼ α` for normal `α` (the internal `ThetaWTerm.le_of_mem_E`);
  * `iltb_Omega_of_iinE`: `δ ∈ E_k(α) → δ ≺ Ω_{k+1}` (the coefficient bound, the internal
    `ThetaWTerm.lt_Omega_of_mem_E`);
  * `domOk_iff`, `isDom_tcTheta_iff`: the domain condition at a collapse, `G_k(α) ≺* α`;
  * normality and the domain condition pass to the members of `E_k` and of `G_k`
    (`isNF_of_iinE`, `isDom_of_iinE`, `isNF_of_iinG`, `isDom_of_iinG`).
-/
import OrdinalAnalysis.IDn.Internal.OrderT

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.ID1.Internal (bor band beq bor_eq_one band_eq_one beq_eq_one)

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Principal codes against cons cells, all principal shapes -/

/-- `P ≺ ⟨y, …⟩ ↔ P ≼ y` for every code `P` that is neither `0` nor a cons cell. -/
lemma iltb_prin_cons' {c : V} (h0 : kind c ≠ 0) (h3 : kind c ≠ 3) (y t : V) :
    iltb c (tcCons y t) = bor (iltb c y) (beq c y) := by
  obtain ⟨S, h, hr⟩ := iltb_unfold c (tcCons y t)
  rw [h, ltStep]
  simp only [kind_tcCons]
  have e1 : rdLt S c y = iltb c y := by
    unfold rdLt iltb
    exact hr _ (pair_lt_pair_right _ (posP_lt_posP (hd_lt_tcCons y t)))
  simp [h0, h3, ltPC, tcHd_tcCons, e1]

/-! ### Sums against their entries -/

/-- `α₀ ≺ ⟨α₀, …⟩`, for every code `α₀`. -/
lemma iltb_self_cons : ∀ x : V, ∀ s : V, iltb x (tcCons x s) = 1 := by
  intro x
  induction x using ISigma1.pi1_order_induction
  · definability
  case ind x ih =>
    intro s
    rcases eq_or_ne x 0 with rfl | hx0
    · exact iltb_zero_pos (tcCons_ne_zero 0 s)
    by_cases h3 : kind x = 3
    · rw [eq_tcCons_of_kind h3, iltb_cons_cons, bor_eq_one]
      exact Or.inl (ih _ (tcHd_lt hx0) _)
    · rw [iltb_prin_cons' (fun h => hx0 (kind_eq_zero_iff.mp h)) h3, bor_eq_one, beq_eq_one]
      exact Or.inr rfl

lemma eq_cons_of_sumK_one {s : V} (hs : sumK s = 1) (hs0 : s ≠ 0) :
    ∃ x w, s = tcCons x w := by
  have hk : kind s = 3 := by
    unfold sumK at hs
    split_ifs at hs with h
    · rcases h with h | h
      · exact absurd (kind_eq_zero_iff.mp h) hs0
      · exact h
    · simp at hs
  exact ⟨_, _, eq_tcCons_of_kind hk⟩

/-- The descent condition of a normal cons cell. -/
lemma descOk_tcCons_iff (x s : V) (hs : sumK s = 1) :
    descOk (tcCons x s) = 1 ↔ s = 0 ∨ (iltb (tcHd s) x = 1 ∨ tcHd s = x) := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  · obtain ⟨y, t, rfl⟩ := eq_cons_of_sumK_one hs hs0
    rw [descOk_tcCons_tcCons, bor_eq_one, beq_eq_one]
    simp

/-- A descending sum `s` is below `⟨ξ⟩ ⁀ s` whenever `ξ` is `≽` the first entry of `s`. -/
lemma iltb_tail_cons : ∀ s : V, ∀ x : V, nfA s = 1 → sumK s = 1 →
    (s = 0 ∨ (iltb (tcHd s) x = 1 ∨ tcHd s = x)) → iltb s (tcCons x s) = 1 := by
  intro s
  induction s using ISigma1.pi1_order_induction
  · definability
  case ind s ih =>
    intro x hs hk hd
    rcases nfA_cases hs with rfl | ⟨i, rfl⟩ | ⟨i, a, rfl, -⟩ | ⟨y, t, rfl, -, ht, htk, hdesc⟩
    · exact iltb_zero_pos (tcCons_ne_zero x 0)
    · simp at hk
    · simp at hk
    · simp only [tcCons_ne_zero, tcHd_tcCons, false_or] at hd
      rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
      rcases hd with hd | rfl
      · exact Or.inl hd
      · exact Or.inr ⟨rfl, ih t (tl_lt_tcCons y t) y ht htk
          ((descOk_tcCons_iff y t htk).mp hdesc)⟩

/-! ### Normality of the members of `E_k` and `G_k` -/

/-- The elements of `E_k(c)` of a code with hereditarily normal entries are normal. -/
lemma isNF_of_iinE (k g : V) : ∀ c : V, nfA c = 1 → iinE k g c = 1 → isNF g := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    intro hc h
    rcases nfA_cases hc with rfl | ⟨i, rfl⟩ | ⟨j, a, rfl, ha⟩ | ⟨x, s, rfl, hx, hs, -, -⟩
    · simp at h
    · simp at h
    · by_cases hj : j ≤ k
      · rw [(iinE_theta_le_iff hj).mp h, isNF_tcTheta_iff]; exact ha
      · rw [iinE_tcTheta_of_lt (not_le.mp hj)] at h
        exact ih a (arg_lt_tcTheta j a) (nfA_of_isNF ha) h
    · rcases (iinE_cons_iff k g x s).mp h with h | h
      · exact ih x (hd_lt_tcCons x s) (nfA_of_isNF hx) h
      · exact ih s (tl_lt_tcCons x s) hs h

/-- The members of `G_k(c)` of a code with hereditarily normal entries are normal. -/
lemma isNF_of_iinG (k y : V) : ∀ c : V, nfA c = 1 → iinG k y c = 1 → isNF y := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    intro hc h
    rcases nfA_cases hc with rfl | ⟨i, rfl⟩ | ⟨j, a, rfl, ha⟩ | ⟨x, s, rfl, hx, hs, -, -⟩
    · simp at h
    · simp at h
    · by_cases hj : k < j
      · rcases (iinG_theta_lt_iff hj).mp h with rfl | h
        · exact ha
        · exact ih a (arg_lt_tcTheta j a) (nfA_of_isNF ha) h
      · rw [iinG_tcTheta_of_le (not_lt.mp hj)] at h; simp at h
    · rcases (iinG_cons_iff k y x s).mp h with h | h
      · exact ih x (hd_lt_tcCons x s) (nfA_of_isNF hx) h
      · exact ih s (tl_lt_tcCons x s) hs h

/-! ### The domain condition -/

lemma domOk_kind_four (bd k : V) {c : V} (hc : kind c = 4) : domOk bd k c = 1 := by
  obtain ⟨S, h, -⟩ := domOk_unfold bd k c
  rw [h, domOkStep]
  simp only [pi₁_pair, pi₂_pair]
  simp [hc]

lemma isDomb_kind_four {c : V} (hc : kind c = 4) : isDomb c = 0 := by
  obtain ⟨S, h, -⟩ := isDomb_unfold c
  simp [h, domStep, hc]

/-- **The `G_k` flag**: `domOk b k c = 1` iff every member of `G_k(c)` is `≺ b` (all codes). -/
lemma domOk_iff_bdd (bd k : V) :
    ∀ c : V, domOk bd k c = 1 ↔ ∀ y < c, iinG k y c = 1 → iltb y bd = 1 := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    rcases code_cases c with rfl | ⟨i, rfl⟩ | ⟨j, a, rfl⟩ | ⟨x, s, rfl⟩ | hk
    · rw [domOk_of_kind bd k (Or.inl kind_zero)]; simp
    · rw [domOk_of_kind bd k (Or.inr (kind_tcOmega i))]; simp
    · by_cases hj : k < j
      · rw [domOk_tcTheta_of_lt hj, band_eq_one, ih a (arg_lt_tcTheta j a)]
        constructor
        · rintro ⟨h1, h2⟩ y _ hy
          rcases (iinG_theta_lt_iff hj).mp hy with rfl | hy
          · exact h1
          · exact h2 y (iinG_lt k y a hy) hy
        · intro h
          refine ⟨h a (arg_lt_tcTheta j a) ((iinG_theta_lt_iff hj).mpr (Or.inl rfl)),
            fun y _ hy => ?_⟩
          exact h y ((iinG_lt k y a hy).trans (arg_lt_tcTheta j a))
            ((iinG_theta_lt_iff hj).mpr (Or.inr hy))
      · rw [domOk_tcTheta_of_le (not_lt.mp hj)]
        simp only [true_iff]
        intro y _ hy
        rw [iinG_tcTheta_of_le (not_lt.mp hj)] at hy; simp at hy
    · rw [domOk_tcCons, band_eq_one, ih x (hd_lt_tcCons x s), ih s (tl_lt_tcCons x s)]
      constructor
      · rintro ⟨h1, h2⟩ y _ hy
        rcases (iinG_cons_iff k y x s).mp hy with hy | hy
        · exact h1 y (iinG_lt k y x hy) hy
        · exact h2 y (iinG_lt k y s hy) hy
      · intro h
        refine ⟨fun y _ hy => ?_, fun y _ hy => ?_⟩
        · exact h y ((iinG_lt k y x hy).trans (hd_lt_tcCons x s))
            ((iinG_cons_iff k y x s).mpr (Or.inl hy))
        · exact h y ((iinG_lt k y s hy).trans (tl_lt_tcCons x s))
            ((iinG_cons_iff k y x s).mpr (Or.inr hy))
    · rw [domOk_kind_four bd k hk]
      simp only [true_iff]
      intro y _ hy
      rw [iinG_kind_four k y hk] at hy; simp at hy

lemma domOk_iff (bd k c : V) : domOk bd k c = 1 ↔ ∀ y, iinG k y c = 1 → iltb y bd = 1 := by
  rw [domOk_iff_bdd]
  exact ⟨fun h y hy => h y (iinG_lt k y c hy) hy, fun h y _ hy => h y hy⟩

@[simp] lemma isDom_at_zero : isDom (0 : V) := by simp [isDom]

@[simp] lemma isDom_tcOmega (i : V) : isDom (tcOmega i) := by simp [isDom]

/-- **Wilken's domain condition at a collapse**: `ϑ_k α` is a domain code iff `α` is and
`G_k(α) ≺* α`. -/
lemma isDom_tcTheta_iff (k a : V) :
    isDom (tcTheta k a) ↔ isDom a ∧ ∀ y, iinG k y a = 1 → iltb y a = 1 := by
  rw [isDom, isDomb_tcTheta, band_eq_one, domOk_iff]
  rfl

lemma isDom_tcCons_iff (x s : V) : isDom (tcCons x s) ↔ isDom x ∧ isDom s := by
  rw [isDom, isDomb_tcCons, band_eq_one]
  rfl

/-- The shapes of domain codes. -/
lemma isDom_cases {c : V} (h : isDom c) :
    c = 0 ∨ (∃ i, c = tcOmega i) ∨ (∃ i a, c = tcTheta i a ∧ isDom a) ∨
      (∃ x s, c = tcCons x s ∧ isDom x ∧ isDom s) := by
  rcases code_cases c with rfl | ⟨i, rfl⟩ | ⟨i, a, rfl⟩ | ⟨x, s, rfl⟩ | hk
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, a, rfl, ((isDom_tcTheta_iff i a).mp h).1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, s, rfl, (isDom_tcCons_iff x s).mp h⟩))
  · unfold isDom at h; rw [isDomb_kind_four hk] at h; simp at h

/-- The elements of `E_k(c)` of a domain code are domain codes. -/
lemma isDom_of_iinE (k g : V) : ∀ c : V, isDom c → iinE k g c = 1 → isDom g := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    intro hc h
    rcases isDom_cases hc with rfl | ⟨i, rfl⟩ | ⟨j, a, rfl, ha⟩ | ⟨x, s, rfl, hx, hs⟩
    · simp at h
    · simp at h
    · by_cases hj : j ≤ k
      · rw [(iinE_theta_le_iff hj).mp h]; exact hc
      · rw [iinE_tcTheta_of_lt (not_le.mp hj)] at h
        exact ih a (arg_lt_tcTheta j a) ha h
    · rcases (iinE_cons_iff k g x s).mp h with h | h
      · exact ih x (hd_lt_tcCons x s) hx h
      · exact ih s (tl_lt_tcCons x s) hs h

/-- The members of `G_k(c)` of a domain code are domain codes. -/
lemma isDom_of_iinG (k y : V) : ∀ c : V, isDom c → iinG k y c = 1 → isDom y := by
  intro c
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    intro hc h
    rcases isDom_cases hc with rfl | ⟨i, rfl⟩ | ⟨j, a, rfl, ha⟩ | ⟨x, s, rfl, hx, hs⟩
    · simp at h
    · simp at h
    · by_cases hj : k < j
      · rcases (iinG_theta_lt_iff hj).mp h with rfl | h
        · exact ha
        · exact ih a (arg_lt_tcTheta j a) ha h
      · rw [iinG_tcTheta_of_le (not_lt.mp hj)] at h; simp at h
    · rcases (iinG_cons_iff k y x s).mp h with h | h
      · exact ih x (hd_lt_tcCons x s) hx h
      · exact ih s (tl_lt_tcCons x s) hs h

/-! ### Elements of `E_k` of a normal form -/

/-- The coefficient bound: every `δ ∈ E_k(α)` lies below `Ω_{k+1}` (all codes). -/
lemma iltb_Omega_of_iinE {k g a : V} (h : iinE k g a = 1) : iltb g (tcOmega k) = 1 := by
  obtain ⟨j, d, rfl, hjk⟩ := iinE_shape h
  exact (iltb_theta_Omega_iff j d k).mpr hjk

lemma ile_of_iinE_aux (k g : V) :
    ∀ a : V, nfA a = 1 → iinE k g a = 1 → (iltb g a = 1 ∨ g = a) := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a ih =>
    intro ha h
    rcases nfA_cases ha with rfl | ⟨i, rfl⟩ | ⟨j, b, rfl, hb⟩ | ⟨x, s, rfl, hx, hs, hk, hdesc⟩
    · simp at h
    · simp at h
    · by_cases hj : j ≤ k
      · exact Or.inr ((iinE_theta_le_iff hj).mp h)
      · have hkj : k < j := not_le.mp hj
        rw [iinE_tcTheta_of_lt hkj] at h
        obtain ⟨j', d, rfl, hj'⟩ := iinE_shape h
        exact Or.inl (iltb_tcTheta_tcTheta_of_lt (lt_of_le_of_lt hj' hkj) d b)
    · refine Or.inl ?_
      have hxs : isTerm (tcCons x s) := isTerm_of_nfA_aux _ ha
      have hsT : isTerm s := ((isTerm_tcCons_iff x s).mp hxs).2.1
      have hxT : isTerm x := ((isTerm_tcCons_iff x s).mp hxs).1
      rcases (iinE_cons_iff k g x s).mp h with h | h
      · have hgT : isTerm g := isTerm_of_iinE k g x hxT h
        exact iltb_of_le_of_lt hgT hxT hxs (ih x (hd_lt_tcCons x s) (nfA_of_isNF hx) h)
          (iltb_self_cons x s)
      · have hgT : isTerm g := isTerm_of_iinE k g s hsT h
        exact iltb_of_le_of_lt hgT hsT hxs (ih s (tl_lt_tcCons x s) hs h)
          (iltb_tail_cons s x hs hk ((descOk_tcCons_iff x s hk).mp hdesc))

/-- For normal `α`, every `δ ∈ E_k(α)` satisfies `δ ≼ α`. -/
lemma ile_of_iinE {k g a : V} (ha : isNF a) (h : iinE k g a = 1) : iltb g a = 1 ∨ g = a :=
  ile_of_iinE_aux k g a (nfA_of_isNF ha) h

/-! ### Finiteness of the coefficient sets -/

/-- **`E_k(c)` is finite**: it is (the extension of) a unique finite set of the model; its
elements are bounded by `c`. -/
lemma iinE_finite (k c : V) : ∃! s : V, ∀ g, g ∈ s ↔ iinE k g c = 1 := by
  have hP : 𝚺-[1]-Predicate (fun g : V => iinE k g c = 1) := by definability
  exact finite_comprehension₁! hP ⟨c + 1, fun g hg => lt_succ_iff_le.mpr (iinE_le hg)⟩

end Model

end OrdinalAnalysis.IDn.Internal
