/-
  The coefficient sets of the coded ϑ-notation inside models of `IΣ₁`: the clauses of
  Freund, arXiv:2204.09321, Exercise 3.2 (c), (e) for internal codes of normal forms,
  following `Ordinal/Theta/Order.lean`.

  * `iltb_self_cons`: `α₀ ≺ ⟨α₀, …⟩` (all codes);
  * `iltb_tail_cons`: a descending sum is below any sum obtained by prefixing an entry that
    is `≽` its first entry;
  * `ile_of_iinE`: `δ ∈ E(α) → δ ≼ α` for normal `α`;
  * `forall_iinE_lt_theta_iff`: `E(α) ≺ ϑ β ↔ α ≺ ϑ β` for normal `α ≺ Ω`;
  * `iex_of_theta_le`, `exists_iinE_of_theta_le`: `ϑ δ ≼ β ≺ Ω` gives `ϑ δ ≼ γ` for some
    `γ ∈ E(β)`;
  * `exists_iinE_le_of_le`: `α ≼ β ≺ Ω`, `α` normal, `γ ∈ E(α)` give `γ ≼ δ` for some
    `δ ∈ E(β)`;
  * `iinE_finite`: `E(c)` is a finite set of the model, bounded by `c`.
-/
import OrdinalAnalysis.ID1.Internal.Order

set_option autoImplicit false

namespace OrdinalAnalysis.ID1.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.Gentzen.InternalONote

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The top code `1` -/

lemma iltb_cons_one (x s : V) : iltb (tcCons x s) 1 = iltb x 1 :=
  iltb_cons_prin' x s (by simp) (by simp)

lemma iltb_one_cons (y t : V) : iltb (1 : V) (tcCons y t) = bor (iltb 1 y) (beq 1 y) :=
  iltb_prin_cons' (by simp) (by simp) y t

lemma iltb_theta_one' (a : V) : iltb (tcTheta a) 1 = 1 := iltb_theta_top a (Or.inl kind_one)

lemma not_iltb_one_one : iltb (1 : V) 1 ≠ 1 := iltb_irrefl 1

lemma iltb_one_theta (a : V) : iltb (1 : V) (tcTheta a) = 0 :=
  iltb_top_theta (Or.inl kind_one) a

/-- Codes below `Ω`: `0`, the `ϑ`-codes, and sums whose first entry is below `Ω`. -/
lemma iltb_one_iff (c : V) :
    iltb c 1 = 1 ↔ c = 0 ∨ kind c = 2 ∨ ∃ x s, c = tcCons x s ∧ iltb x 1 = 1 := by
  rcases code_cases c with rfl | ⟨x, s, rfl⟩ | ⟨a, rfl⟩ | hk
  · simp [iltb_zero_pos]
  · rw [iltb_cons_one]
    constructor
    · intro h; exact Or.inr (Or.inr ⟨x, s, rfl, h⟩)
    · rintro (h | h | ⟨x', s', e, h⟩)
      · simp at h
      · simp at h
      · obtain ⟨rfl, rfl⟩ : x' = x ∧ s' = s := by
          have e1 := congrArg tcHd e
          have e2 := congrArg tcTl e
          simp at e1 e2
          exact ⟨e1.symm, e2.symm⟩
        exact h
  · simp [iltb_theta_one']
  · rw [iltb_top_prin hk (by simp) (by simp)]
    have h0 := kind_ne_zero_of_top hk
    simp only [zero_ne_one, false_iff, not_or, not_exists, not_and]
    refine ⟨ne_zero_of_kind_ne_zero h0, ?_, ?_⟩
    · rcases hk with hk | hk <;> simp [hk]
    · rintro x s rfl
      simp at hk

/-! ### Sums against their entries -/

/-- `α₀ ≺ ⟨α₀, …⟩`, for every code `α₀` (Freund, Exercise 3.2(d), first part). -/
lemma iltb_self_cons : ∀ x : V, ∀ s : V, iltb x (tcCons x s) = 1 := by
  intro x
  induction x using ISigma1.pi1_order_induction
  · definability
  case ind x ih =>
    intro s
    rcases eq_or_ne x 0 with rfl | hx0
    · exact iltb_zero_tcCons 0 s
    rcases code_cases_ne_zero hx0 with ⟨y, ys, rfl⟩ | ⟨h0, h3⟩
    · rw [iltb_cons_cons, bor_eq_one]
      exact Or.inl (ih y (hd_lt_tcCons y ys) ys)
    · rw [iltb_prin_cons' h0 h3, bor_eq_one, beq_eq_one]
      exact Or.inr rfl

/-- The descent condition of a normal cons cell. -/
lemma descOk_tcCons_iff (x s : V) (hs : sumK s = 1) :
    descOk (tcCons x s) = 1 ↔ s = 0 ∨ (iltb (tcHd s) x = 1 ∨ tcHd s = x) := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  · have hk : kind s = 3 := by
      unfold sumK at hs
      split_ifs at hs with h
      · rcases h with h | h
        · exact absurd (kind_eq_zero_iff.mp h) hs0
        · exact h
      · simp at hs
    rw [eq_tcCons_of_kind hk, descOk_tcCons_tcCons, bor_eq_one, beq_eq_one]
    simp

/-- A descending sum `s` is below `⟨ξ⟩ ⁀ s` whenever `ξ` is `≽` the first entry of `s`. -/
lemma iltb_tail_cons : ∀ s : V, ∀ x : V, nfA s = 1 → sumK s = 1 →
    (s = 0 ∨ (iltb (tcHd s) x = 1 ∨ tcHd s = x)) → iltb s (tcCons x s) = 1 := by
  intro s
  induction s using ISigma1.pi1_order_induction
  · definability
  case ind s ih =>
    intro x hs hk hd
    rcases nfA_cases hs with rfl | rfl | ⟨a, rfl, -⟩ | ⟨y, t, rfl, -, ht, htk, hdesc⟩
    · exact iltb_zero_tcCons x 0
    · simp at hk
    · simp at hk
    · simp only [tcCons_ne_zero, tcHd_tcCons, false_or] at hd
      rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
      rcases hd with hd | rfl
      · exact Or.inl hd
      · refine Or.inr ⟨rfl, ih t (tl_lt_tcCons y t) y ht htk ?_⟩
        exact (descOk_tcCons_iff y t htk).mp hdesc

/-! ### Elements of `E` of a normal form -/

lemma ile_of_iinE_aux (g : V) : ∀ a : V, nfA a = 1 → iinE g a = 1 → (iltb g a = 1 ∨ g = a) := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a ih =>
    intro ha h
    rcases nfA_cases ha with rfl | rfl | ⟨b, rfl, -⟩ | ⟨x, s, rfl, hx, hs, hk, hdesc⟩
    · simp at h
    · rw [iinE_top g (Or.inl kind_one)] at h; simp at h
    · exact Or.inr ((iinE_tcTheta_iff g b).mp h)
    · refine Or.inl ?_
      rcases (iinE_tcCons_iff g x s).mp h with h | h
      · exact iltb_of_le_of_lt (ih x (hd_lt_tcCons x s) (nfA_of_isNF hx) h)
          (iltb_self_cons x s)
      · exact iltb_of_le_of_lt (ih s (tl_lt_tcCons x s) hs h)
          (iltb_tail_cons s x hs hk ((descOk_tcCons_iff x s hk).mp hdesc))

/-- For normal `α`, every `δ ∈ E(α)` satisfies `δ ≼ α`. -/
lemma ile_of_iinE {g a : V} (ha : isNF a) (h : iinE g a = 1) : iltb g a = 1 ∨ g = a :=
  ile_of_iinE_aux g a (nfA_of_isNF ha) h

/-- The elements of `E(α)` of a normal `α ≺ Ω` are `≺ Ω`. -/
lemma iltb_one_of_iinE {g a : V} (ha : isNF a) (hΩ : iltb a 1 = 1) (h : iinE g a = 1) :
    iltb g 1 = 1 :=
  iltb_of_le_of_lt (ile_of_iinE ha h) hΩ

lemma iltb_theta_of_iall_aux (b : V) : ∀ a : V, nfA a = 1 → iltb a 1 = 1 →
    iall a (tcTheta b) = 1 → iltb a (tcTheta b) = 1 := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a ih =>
    intro ha hΩ hE
    rcases nfA_cases ha with rfl | rfl | ⟨a', rfl, -⟩ | ⟨x, s, rfl, hx, -, -, -⟩
    · exact iltb_zero_tcTheta b
    · exact absurd hΩ not_iltb_one_one
    · rwa [iall_theta] at hE
    · rw [iltb_cons_theta]
      rw [iltb_cons_one] at hΩ
      rw [iall_cons, band_eq_one] at hE
      exact ih x (hd_lt_tcCons x s) (nfA_of_isNF hx) hΩ hE.1

/-- **Freund, Exercise 3.2(c)**, internally: for normal `α ≺ Ω`,
`E(α) ≺ ϑ β ↔ α ≺ ϑ β`. -/
lemma forall_iinE_lt_theta_iff {a : V} (b : V) (ha : isNF a) (hΩ : iltb a 1 = 1) :
    (∀ g, iinE g a = 1 → iltb g (tcTheta b) = 1) ↔ iltb a (tcTheta b) = 1 := by
  constructor
  · intro h
    exact iltb_theta_of_iall_aux b a (nfA_of_isNF ha) hΩ ((iall_iff a _).mpr h)
  · intro h g hg
    exact iltb_of_le_of_lt (ile_of_iinE ha hg) h

/-- The quantifier flag form of `forall_iinE_lt_theta_iff`. -/
lemma iall_theta_iff {a : V} (b : V) (ha : isNF a) (hΩ : iltb a 1 = 1) :
    iall a (tcTheta b) = 1 ↔ iltb a (tcTheta b) = 1 := by
  rw [iall_iff]; exact forall_iinE_lt_theta_iff b ha hΩ

/-- For normal `α ≺ Ω`: `α ≺ β` and `α ≺ ϑ β` give `ϑ α ≺ ϑ β`. -/
lemma iltb_theta_theta_of_lt_of_lt_theta {a b : V} (ha : isNF a) (hΩ : iltb a 1 = 1)
    (h : iltb a b = 1) (h' : iltb a (tcTheta b) = 1) :
    iltb (tcTheta a) (tcTheta b) = 1 :=
  (iltb_theta_theta_iff a b).mpr (Or.inl ⟨h, (forall_iinE_lt_theta_iff b ha hΩ).mpr h'⟩)

/-- `ϑ α ≺ ϑ β` whenever `ϑ α ≼ δ` for some `δ ∈ E(β)`. -/
lemma iltb_theta_theta_of_le_iinE {a b g : V} (hg : iinE g b = 1)
    (h : iltb (tcTheta a) g = 1 ∨ tcTheta a = g) : iltb (tcTheta a) (tcTheta b) = 1 :=
  (iltb_theta_theta_iff a b).mpr (Or.inr ⟨g, hg, h⟩)

/-- `ϑ` is order preserving under the side condition `E(α) ≺ ϑ β`. -/
lemma iltb_theta_theta_of_lt {a b : V} (h : iltb a b = 1)
    (hE : ∀ g, iinE g a = 1 → iltb g (tcTheta b) = 1) :
    iltb (tcTheta a) (tcTheta b) = 1 :=
  (iltb_theta_theta_iff a b).mpr (Or.inl ⟨h, hE⟩)

/-! ### Witnesses in `E` -/

lemma iex_of_theta_le_aux (d : V) : ∀ b : V, iltb b 1 = 1 →
    (iltb (tcTheta d) b = 1 ∨ tcTheta d = b) → iex (tcTheta d) b = 1 := by
  intro b
  induction b using ISigma1.sigma1_order_induction
  · definability
  case ind b ih =>
    intro hb h
    rcases code_cases b with rfl | ⟨x, s, rfl⟩ | ⟨b', rfl⟩ | hk
    · rcases h with h | h
      · exact absurd h (not_iltb_zero _)
      · exact absurd h (tcTheta_ne_zero d)
    · rw [iltb_cons_one] at hb
      have hx : iltb (tcTheta d) x = 1 ∨ tcTheta d = x := by
        rcases h with h | h
        · rw [iltb_theta_cons, bor_eq_one, beq_eq_one] at h; exact h
        · have := congrArg kind h; simp at this
      rw [iex_cons, bor_eq_one]
      exact Or.inl (ih x (hd_lt_tcCons x s) hb hx)
    · rw [iex_theta, bor_eq_one, beq_eq_one]; exact h
    · rw [iltb_top_prin hk (by simp) (by simp)] at hb; simp at hb

/-- If `ϑ δ ≼ β ≺ Ω`, then `ϑ δ ≼ γ` for some `γ ∈ E(β)` (all codes). -/
lemma iex_of_theta_le {d b : V} (hb : iltb b 1 = 1) (h : iltb (tcTheta d) b = 1 ∨ tcTheta d = b) :
    iex (tcTheta d) b = 1 :=
  iex_of_theta_le_aux d b hb h

lemma exists_iinE_of_theta_le {d b : V} (hb : iltb b 1 = 1)
    (h : iltb (tcTheta d) b = 1 ∨ tcTheta d = b) :
    ∃ g, iinE g b = 1 ∧ (iltb (tcTheta d) g = 1 ∨ tcTheta d = g) :=
  (iex_iff _ b).mp (iex_of_theta_le hb h)

/-- **Freund, Exercise 3.2(e)**, internally: if `α ≼ β ≺ Ω` with `α` normal, then every
`γ ∈ E(α)` has some `δ ∈ E(β)` with `γ ≼ δ`. -/
lemma exists_iinE_le_of_le {a b g : V} (ha : isNF a) (hab : iltb a b = 1 ∨ a = b)
    (hb : iltb b 1 = 1) (hg : iinE g a = 1) :
    ∃ d, iinE d b = 1 ∧ (iltb g d = 1 ∨ g = d) := by
  have e := eq_tcTheta_of_iinE hg
  have hgb : iltb (tcTheta (tcArg g)) b = 1 ∨ tcTheta (tcArg g) = b := by
    rw [← e]; exact ile_trans (ile_of_iinE ha hg) hab
  obtain ⟨d, hd, h⟩ := exists_iinE_of_theta_le hb hgb
  rw [← e] at h
  exact ⟨d, hd, h⟩

/-! ### Finiteness of the coefficient sets -/

/-- **`E(c)` is finite**: it is (the extension of) a unique finite set of the model; its
elements are bounded by `c`. -/
lemma iinE_finite (c : V) : ∃! s : V, ∀ g, g ∈ s ↔ iinE g c = 1 := by
  have hP : 𝚺-[1]-Predicate (fun g : V => iinE g c = 1) := by definability
  exact finite_comprehension₁! hP ⟨c + 1, fun g hg => lt_succ_iff_le.mpr (le_of_iinE hg)⟩

end OrdinalAnalysis.ID1.Internal
