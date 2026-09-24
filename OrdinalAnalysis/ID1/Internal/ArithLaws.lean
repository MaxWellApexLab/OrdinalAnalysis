/-
  Laws of the internal arithmetic of the coded ϑ-notation, in every model of `IΣ₁`.

  Following `Ordinal/Theta/Arith.lean`, the operations are read on exponent lists
  (`itoL`, `iofL`).  The *first exponent* `ilead x` of a nonzero term code `x` decides the
  comparison with a power of `ω`:

  * `iltb_iomegaPow_iff_ilead`: `x ≺ ω^α ↔ ilead x ≺ α`;
  * `iltb_iomegaPow_iff`, `iomegaPow_injective`: `ω^·` is strictly monotone and injective;
  * `iltb_iomegaPow_of_lt_prin`: the principal codes (`Ω`, `ϑ β`) are closed under `ω^·`
    from below, and `ω^P = P` (`iomegaPow_of_prin`);
  * normal forms are preserved by `ω^·`; `0` is neutral for both sums.
-/
import OrdinalAnalysis.ID1.Internal.Arith

set_option autoImplicit false

namespace OrdinalAnalysis.ID1.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.Gentzen.InternalONote

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Principal shapes -/

/-- `c` has the shape of `Ω` or of a `ϑ`-term. -/
abbrev IsPrinC (c : V) : Prop := kind c = 1 ∨ kind c = 2

instance IsPrinC_definable (Γ) (m : ℕ) : Γ-[m + 1]-Predicate (IsPrinC : V → Prop) := by
  unfold IsPrinC; definability

lemma IsPrinC.kind_ne_zero {p : V} (hp : IsPrinC p) : kind p ≠ 0 := by
  rcases hp with h | h <;> simp [h]

lemma IsPrinC.kind_ne_three {p : V} (hp : IsPrinC p) : kind p ≠ 3 := by
  rcases hp with h | h <;> simp [h]

lemma IsPrinC.ne_zero {p : V} (hp : IsPrinC p) : p ≠ 0 :=
  ne_zero_of_kind_ne_zero hp.kind_ne_zero

@[simp] lemma isPrinC_one : IsPrinC (1 : V) := Or.inl kind_one

@[simp] lemma isPrinC_tcTheta (a : V) : IsPrinC (tcTheta a) := Or.inr (kind_tcTheta a)

@[simp] lemma not_isPrinC_zero : ¬ IsPrinC (0 : V) := fun h => h.ne_zero rfl

@[simp] lemma not_isPrinC_tcCons (x s : V) : ¬ IsPrinC (tcCons x s) := by
  simp [IsPrinC]

lemma ne_of_isPrinC_of_not {p c : V} (hp : IsPrinC p) (hc : ¬ IsPrinC c) : p ≠ c := by
  rintro rfl; exact hc hp

/-- A principal code against a cons cell. -/
lemma iltb_prinC_cons {p : V} (hp : IsPrinC p) (y t : V) :
    iltb p (tcCons y t) = 1 ↔ iltb p y = 1 ∨ p = y := by
  rw [iltb_prin_cons' hp.kind_ne_zero hp.kind_ne_three, bor_eq_one, beq_eq_one]

/-- A cons cell against a principal code. -/
lemma iltb_cons_prinC (x s : V) {p : V} (hp : IsPrinC p) : iltb (tcCons x s) p = iltb x p :=
  iltb_cons_prin' x s hp.kind_ne_zero hp.kind_ne_three

/-- Two one-entry lists. -/
lemma iltb_single_single (x y : V) : iltb (tcCons x 0) (tcCons y 0) = 1 ↔ iltb x y = 1 := by
  rw [iltb_cons_cons, bor_eq_one, band_eq_one, iltb_zero_zero]
  simp

/-! ### Exponent lists of term codes -/

/-- The first exponent of a code. -/
noncomputable def ilead (c : V) : V := tcHd (itoL c)

def ileadDef : 𝚺₁.Semisentence 2 := .mkSigma “y c. ∃ s, !itoLDef s c ∧ !tcHdDef y s”

instance ilead_defined : 𝚺₁-Function₁ (ilead : V → V) via ileadDef := .mk fun v ↦ by
  simp [ileadDef, ilead, itoL_defined.iff, tcHd_defined.iff]

instance ilead_definable : 𝚺₁-Function₁ (ilead : V → V) := ilead_defined.to_definable
instance ilead_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (ilead : V → V) :=
  ilead_definable.of_sigmaOne

lemma itoL_of_prinC {p : V} (hp : IsPrinC p) : itoL p = tcCons p 0 := if_pos hp

lemma itoL_of_not_prinC {c : V} (hc : ¬ IsPrinC c) : itoL c = c := if_neg hc

lemma ilead_of_prinC {p : V} (hp : IsPrinC p) : ilead p = p := by
  simp [ilead, itoL_of_prinC hp]

@[simp] lemma ilead_tcCons (x s : V) : ilead (tcCons x s) = x := by simp [ilead]

lemma iofL_eq (s : V) :
    iofL s = if kind s = 3 ∧ tcTl s = 0 ∧ IsPrinC (tcHd s) then tcHd s else s := rfl

lemma iofL_cons (z w : V) :
    iofL (tcCons z w) = if w = 0 ∧ IsPrinC z then z else tcCons z w := by
  simp [iofL_eq]

/-- `iofL` keeps the first entry of a nonempty list. -/
@[simp] lemma ilead_iofL_cons (z w : V) : ilead (iofL (tcCons z w)) = z := by
  rw [iofL_cons]
  split_ifs with h
  · exact ilead_of_prinC h.2
  · simp

lemma sumK_itoL {x : V} (hx : isTerm x) : sumK (itoL x) = 1 := by
  rcases isTerm_cases hx with rfl | rfl | ⟨a, rfl, -⟩ | ⟨y, s, rfl, -⟩ <;> simp

lemma kind_itoL {x : V} (hx : isTerm x) (hx0 : x ≠ 0) : kind (itoL x) = 3 := by
  rcases isTerm_cases hx with rfl | rfl | ⟨a, rfl, -⟩ | ⟨y, s, rfl, -⟩
  · exact absurd rfl hx0
  all_goals simp

lemma itoL_eq_cons {x : V} (hx : isTerm x) (hx0 : x ≠ 0) :
    itoL x = tcCons (ilead x) (tcTl (itoL x)) :=
  eq_tcCons_of_kind (kind_itoL hx hx0)

/-- On codes of normal forms, `iofL` inverts `itoL`. -/
lemma iofL_itoL {x : V} (hx : isNF x) : iofL (itoL x) = x := by
  have hs := sok_of_isNF hx
  rcases nfA_cases (nfA_of_isNF hx) with rfl | rfl | ⟨a, rfl, -⟩ | ⟨y, s, rfl, -⟩
  · simp
  · simp [iofL_single_prin (Or.inl kind_one)]
  · simp [iofL_single_prin (Or.inr (kind_tcTheta a))]
  · rw [itoL_tcCons, iofL_cons, if_neg]
    rw [sok_tcCons] at hs
    intro h
    rw [if_pos ⟨h.1, h.2⟩] at hs
    simp at hs

/-- Codes of normal forms with a set hereditary flag and a proper sum shape. -/
lemma isNF_iofL {s : V} (hs : nfA s = 1) (hk : sumK s = 1) : isNF (iofL s) := by
  rcases nfA_cases hs with rfl | rfl | ⟨a, rfl, -⟩ | ⟨y, t, rfl, hy, ht, -, -⟩
  · simp
  · simp at hk
  · simp at hk
  · rw [iofL_cons]
    split_ifs with h
    · exact hy
    · unfold isNF isNFb
      rw [hs, band_eq_one, sok_tcCons, if_neg (fun h' => h ⟨h'.1, h'.2⟩)]
      exact ⟨rfl, rfl⟩

/-- The exponent list of a normal form is a descending list of normal forms. -/
lemma nfA_itoL {x : V} (hx : isNF x) : nfA (itoL x) = 1 := by
  rcases nfA_cases (nfA_of_isNF hx) with rfl | rfl | ⟨a, rfl, ha⟩ | ⟨y, s, rfl, -⟩
  · simp
  · simp [isNFb, isNF] at hx ⊢
  · have : isNFb (tcTheta a) = 1 := (isNF_tcTheta_iff a).mpr ha
    simp [this]
  · simpa using nfA_of_isNF hx

/-! ### `ω^·` -/

lemma iomegaPow_of_prin {p : V} (hp : IsPrinC p) : iomegaPow p = p := iofL_single_prin hp

lemma iomegaPow_of_not_prin {a : V} (ha : ¬ IsPrinC a) : iomegaPow a = tcCons a 0 :=
  iofL_single_of_not_prin ha 0

@[simp] lemma iomegaPow_one : iomegaPow (1 : V) = 1 := iomegaPow_of_prin isPrinC_one

@[simp] lemma iomegaPow_tcTheta (a : V) : iomegaPow (tcTheta a) = tcTheta a :=
  iomegaPow_of_prin (isPrinC_tcTheta a)

@[simp] lemma iomegaPow_zero : iomegaPow (0 : V) = ione := by
  rw [iomegaPow_of_not_prin not_isPrinC_zero, ione]

@[simp] lemma ilead_iomegaPow (a : V) : ilead (iomegaPow a) = a := ilead_iofL_cons a 0

lemma iomegaPow_ne_zero (a : V) : iomegaPow a ≠ 0 := by
  by_cases ha : IsPrinC a
  · rw [iomegaPow_of_prin ha]; exact ha.ne_zero
  · rw [iomegaPow_of_not_prin ha]; exact tcCons_ne_zero _ _

/-- **`ω^·` is strictly monotone and order reflecting**, on all codes. -/
theorem iltb_iomegaPow_iff (a b : V) :
    iltb (iomegaPow a) (iomegaPow b) = 1 ↔ iltb a b = 1 := by
  by_cases ha : IsPrinC a <;> by_cases hb : IsPrinC b
  · rw [iomegaPow_of_prin ha, iomegaPow_of_prin hb]
  · rw [iomegaPow_of_prin ha, iomegaPow_of_not_prin hb, iltb_prinC_cons ha]
    exact ⟨fun h => h.resolve_right (ne_of_isPrinC_of_not ha hb), Or.inl⟩
  · rw [iomegaPow_of_not_prin ha, iomegaPow_of_prin hb, iltb_cons_prinC _ _ hb]
  · rw [iomegaPow_of_not_prin ha, iomegaPow_of_not_prin hb, iltb_single_single]

/-- `ω^·` is injective, on all codes. -/
theorem iomegaPow_injective {a b : V} (h : iomegaPow a = iomegaPow b) : a = b := by
  have := congrArg ilead h
  simpa using this

/-- `ω^·` preserves normal forms. -/
theorem isNF_iomegaPow {a : V} (ha : isNF a) : isNF (iomegaPow a) := by
  by_cases hp : IsPrinC a
  · rw [iomegaPow_of_prin hp]; exact ha
  · rw [iomegaPow_of_not_prin hp]
    unfold isNF isNFb
    rw [nfA_tcCons, sok_tcCons, if_neg (fun h => hp h.2)]
    have : isNFb a = 1 := ha
    simp [this]

/-- **Comparison with a power of `ω`**: a nonzero term code is below `ω^α` iff its first
exponent is below `α`. -/
theorem iltb_iomegaPow_iff_ilead {x : V} (hx : isTerm x) (hx0 : x ≠ 0) (a : V) :
    iltb x (iomegaPow a) = 1 ↔ iltb (ilead x) a = 1 := by
  have key : ∀ {p : V}, IsPrinC p →
      (iltb p (iomegaPow a) = 1 ↔ iltb p a = 1) := by
    intro p hp
    by_cases ha : IsPrinC a
    · rw [iomegaPow_of_prin ha]
    · rw [iomegaPow_of_not_prin ha, iltb_prinC_cons hp]
      exact ⟨fun h => h.resolve_right (ne_of_isPrinC_of_not hp ha), Or.inl⟩
  rcases isTerm_cases hx with rfl | rfl | ⟨b, rfl, -⟩ | ⟨y, s, rfl, -⟩
  · exact absurd rfl hx0
  · rw [ilead_of_prinC isPrinC_one]; exact key isPrinC_one
  · rw [ilead_of_prinC (isPrinC_tcTheta b)]; exact key (isPrinC_tcTheta b)
  · rw [ilead_tcCons]
    by_cases ha : IsPrinC a
    · rw [iomegaPow_of_prin ha, iltb_cons_prinC _ _ ha]
    · rw [iomegaPow_of_not_prin ha, iltb_cons_cons, bor_eq_one, band_eq_one,
        iltb_zero_right]
      simp

/-- A list read back by `iofL` is below `ω^α` when its first entry is below `α`. -/
theorem iltb_iofL_cons_iomegaPow {z a : V} (w : V) (h : iltb z a = 1) :
    iltb (iofL (tcCons z w)) (iomegaPow a) = 1 := by
  have hz : ∀ {p : V}, IsPrinC p → iltb p a = 1 → iltb p (iomegaPow a) = 1 := by
    intro p hp hpa
    by_cases ha : IsPrinC a
    · rw [iomegaPow_of_prin ha]; exact hpa
    · rw [iomegaPow_of_not_prin ha, iltb_prinC_cons hp]; exact Or.inl hpa
  rw [iofL_cons]
  split_ifs with hw
  · exact hz hw.2 h
  · by_cases ha : IsPrinC a
    · rw [iomegaPow_of_prin ha, iltb_cons_prinC _ _ ha]; exact h
    · rw [iomegaPow_of_not_prin ha, iltb_cons_cons, bor_eq_one]; exact Or.inl h

/-- **The principal codes are closed under `ω^·` from below.** -/
theorem iltb_iomegaPow_of_lt_prin {x p : V} (hp : IsPrinC p) (h : iltb x p = 1) :
    iltb (iomegaPow x) p = 1 := by
  by_cases hx : IsPrinC x
  · rw [iomegaPow_of_prin hx]; exact h
  · rw [iomegaPow_of_not_prin hx, iltb_cons_prinC _ _ hp]; exact h

/-! ### `0` and `1` -/

lemma ione_eq : (ione : V) = tcCons 0 0 := rfl

lemma isNF_ione : isNF (ione : V) := by
  rw [← iomegaPow_zero]; exact isNF_iomegaPow isNF_zero

lemma iltb_zero_ione : iltb (0 : V) ione = 1 := iltb_zero_tcCons 0 0

/-- `1` is below every principal code. -/
lemma iltb_ione_prin {p : V} (hp : IsPrinC p) : iltb (ione : V) p = 1 := by
  rw [ione_eq, iltb_cons_prinC _ _ hp]; exact iltb_zero_pos hp.ne_zero

lemma iaddL_zero_left {t : V} (ht : sumK t = 1) : iaddL 0 t = t := by
  by_cases h : kind t = 3
  · rw [eq_tcCons_of_kind h, iaddL_cons, ifilt_zero, iapp_zero_left]
  · rw [iaddL_of_kind 0 h]
    unfold sumK at ht
    split_ifs at ht with h'
    · rcases h' with h' | h'
      · exact (kind_eq_zero_iff.mp h').symm
      · exact absurd h' h
    · simp at ht

/-- `α + 0 = α` for normal `α`. -/
theorem iadd_zero_right {x : V} (hx : isNF x) : iadd x 0 = x := by
  rw [iadd, itoL_zero, iaddL_zero_right, iofL_itoL hx]

/-- `0 + α = α` for normal `α`. -/
theorem iadd_zero_left {x : V} (hx : isNF x) : iadd 0 x = x := by
  rw [iadd, itoL_zero, iaddL_zero_left (sumK_itoL (isTerm_of_isNF hx)), iofL_itoL hx]

/-- `α ⊕ 0 = α` for normal `α`. -/
theorem inadd_zero_right {x : V} (hx : isNF x) : inadd x 0 = x := by
  rw [inadd, itoL_zero, imerge_zero_right (sumK_itoL (isTerm_of_isNF hx)), iofL_itoL hx]

/-- `0 ⊕ α = α` for normal `α`. -/
theorem inadd_zero_left {x : V} (hx : isNF x) : inadd 0 x = x := by
  rw [inadd, itoL_zero, imerge_zero_left, iofL_itoL hx]

/-! ### The comparison flag `ige` -/

lemma ige_of_iltb {x y : V} (h : iltb y x = 1) : ige x y = 1 := ige_eq_one.mpr (Or.inl h)

@[simp] lemma ige_self (x : V) : ige x x = 1 := ige_eq_one.mpr (Or.inr rfl)

lemma ige_zero_right (x : V) : ige x 0 = 1 := ige_eq_one.mpr (ile_zero_left x)

lemma not_ige_of_iltb {x y : V} (h : iltb x y = 1) : ige x y ≠ 1 := by
  rw [ne_eq, ige_eq_one]; exact not_ile_of_iltb h

lemma iltb_of_not_ige {x y : V} (hx : isTerm x) (hy : isTerm y) (h : ige x y ≠ 1) :
    iltb x y = 1 := by
  rw [ne_eq, ige_eq_one] at h
  rcases iltb_trichotomy hx hy with h' | h' | h'
  · exact h'
  · exact absurd (Or.inr h'.symm) h
  · exact absurd (Or.inl h') h

/-! ### Descending lists -/

/-- `s` is a descending list of normal forms: the exponent list of a normal form. -/
abbrev IsSL (s : V) : Prop := nfA s = 1 ∧ sumK s = 1

lemma kind_eq_three_of_sumK {s : V} (hs : sumK s = 1) (hs0 : s ≠ 0) : kind s = 3 := by
  unfold sumK at hs
  split_ifs at hs with h
  · rcases h with h | h
    · exact absurd (kind_eq_zero_iff.mp h) hs0
    · exact h
  · simp at hs

lemma eq_cons_of_sumK {s : V} (hs : sumK s = 1) (hs0 : s ≠ 0) :
    ∃ x w, s = tcCons x w := ⟨_, _, eq_tcCons_of_kind (kind_eq_three_of_sumK hs hs0)⟩

lemma isSL_zero : IsSL (0 : V) := ⟨nfA_zero, sumK_zero⟩

lemma isSL_cons_iff (x w : V) :
    IsSL (tcCons x w) ↔ isNF x ∧ IsSL w ∧ (w = 0 ∨ ige x (tcHd w) = 1) := by
  constructor
  · rintro ⟨h, -⟩
    rw [nfA_tcCons, band_eq_one, band_eq_one, band_eq_one] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, ⟨h2, h3⟩, ?_⟩
    rcases (descOk_tcCons_iff x w h3).mp h4 with h | h
    · exact Or.inl h
    · exact Or.inr (ige_eq_one.mpr h)
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
    refine ⟨?_, sumK_tcCons x w⟩
    rw [nfA_tcCons, band_eq_one, band_eq_one, band_eq_one]
    refine ⟨h1, h2, h3, (descOk_tcCons_iff x w h3).mpr ?_⟩
    rcases h4 with h | h
    · exact Or.inl h
    · exact Or.inr (ige_eq_one.mp h)

lemma isSL_itoL {x : V} (hx : isNF x) : IsSL (itoL x) :=
  ⟨nfA_itoL hx, sumK_itoL (isTerm_of_isNF hx)⟩

/-- The first exponent of a nonzero normal form is normal. -/
lemma isNF_ilead {x : V} (hx : isNF x) (hx0 : x ≠ 0) : isNF (ilead x) := by
  have h := isSL_itoL hx
  rw [itoL_eq_cons (isTerm_of_isNF hx) hx0] at h
  exact ((isSL_cons_iff _ _).mp h).1

/-! ### The merge of descending lists -/

/-- The first entry of a merge is the first entry of one of the two lists. -/
lemma imerge_cases (s t : V) (hs : sumK s = 1) (ht : sumK t = 1) :
    imerge s t = 0 ∨ (∃ w, imerge s t = tcCons (tcHd s) w ∧ s ≠ 0) ∨
      (∃ w, imerge s t = tcCons (tcHd t) w ∧ t ≠ 0) := by
  rcases eq_or_ne s 0 with rfl | hs0
  · rw [imerge_zero_left]
    rcases eq_or_ne t 0 with rfl | ht0
    · exact Or.inl rfl
    · obtain ⟨y, t', rfl⟩ := eq_cons_of_sumK ht ht0
      exact Or.inr (Or.inr ⟨t', by simp, ht0⟩)
  rcases eq_or_ne t 0 with rfl | ht0
  · obtain ⟨x, s', rfl⟩ := eq_cons_of_sumK hs hs0
    rw [imerge_zero_right hs]
    exact Or.inr (Or.inl ⟨s', by simp, hs0⟩)
  obtain ⟨x, s', rfl⟩ := eq_cons_of_sumK hs hs0
  obtain ⟨y, t', rfl⟩ := eq_cons_of_sumK ht ht0
  rw [imerge_cons_cons]
  split_ifs
  · exact Or.inr (Or.inl ⟨imerge s' (tcCons y t'), by simp, hs0⟩)
  · exact Or.inr (Or.inr ⟨imerge (tcCons x s') t', by simp, ht0⟩)

lemma isSL_imerge_aux : ∀ w : V, ∀ s ≤ w, ∀ t ≤ w, s + t ≤ w →
    IsSL s → IsSL t → IsSL (imerge s t) := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro s _ t _ hsum hs ht
    have IH : ∀ {s' t' : V}, s' + t' < s + t → IsSL s' → IsSL t' → IsSL (imerge s' t') :=
      fun {s' t'} hlt => ih (s' + t') (lt_of_lt_of_le hlt hsum) s' le_self_add t' le_add_self
        le_rfl
    rcases eq_or_ne s 0 with rfl | hs0
    · simpa using ht
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [imerge_zero_right hs.2]; exact hs
    obtain ⟨x, s', rfl⟩ := eq_cons_of_sumK hs.2 hs0
    obtain ⟨y, t', rfl⟩ := eq_cons_of_sumK ht.2 ht0
    obtain ⟨hx, hs', hds⟩ := (isSL_cons_iff x s').mp hs
    obtain ⟨hy, ht', hdt⟩ := (isSL_cons_iff y t').mp ht
    rw [imerge_cons_cons]
    split_ifs with hxy
    · have hm := IH (add_lt_add_of_lt_of_le (tl_lt_tcCons x s') le_rfl) hs' ht
      refine (isSL_cons_iff _ _).mpr ⟨hx, hm, ?_⟩
      rcases imerge_cases s' (tcCons y t') hs'.2 (sumK_tcCons y t') with
        h | ⟨u, h, hne⟩ | ⟨u, h, -⟩
      · exact Or.inl h
      · rw [h, tcHd_tcCons]; exact Or.inr (hds.resolve_left hne)
      · rw [h, tcHd_tcCons, tcHd_tcCons]; exact Or.inr hxy
    · have hlt : iltb x y = 1 :=
        iltb_of_not_ige (isTerm_of_isNF hx) (isTerm_of_isNF hy) hxy
      have hm := IH (add_lt_add_of_le_of_lt le_rfl (tl_lt_tcCons y t')) hs ht'
      refine (isSL_cons_iff _ _).mpr ⟨hy, hm, ?_⟩
      rcases imerge_cases (tcCons x s') t' (sumK_tcCons x s') ht'.2 with
        h | ⟨u, h, -⟩ | ⟨u, h, hne⟩
      · exact Or.inl h
      · rw [h, tcHd_tcCons, tcHd_tcCons]; exact Or.inr (ige_of_iltb hlt)
      · rw [h, tcHd_tcCons]; exact Or.inr (hdt.resolve_left hne)

/-- The merge of two descending lists is descending. -/
lemma isSL_imerge {s t : V} (hs : IsSL s) (ht : IsSL t) : IsSL (imerge s t) :=
  isSL_imerge_aux (s + t) s le_self_add t le_add_self le_rfl hs ht

/-- **The natural sum preserves normal forms.** -/
theorem isNF_inadd {x y : V} (hx : isNF x) (hy : isNF y) : isNF (inadd x y) := by
  have h := isSL_imerge (isSL_itoL hx) (isSL_itoL hy)
  exact isNF_iofL h.1 h.2

/-! ### The filter of a descending list -/

lemma ifilt_eq_zero_aux (y : V) : ∀ s : V, IsSL s → (s = 0 ∨ iltb (tcHd s) y = 1) →
    ifilt s y = 0 := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro hs h
    rcases eq_or_ne s 0 with rfl | hs0
    · simp
    obtain ⟨x, s', rfl⟩ := eq_cons_of_sumK hs.2 hs0
    have hxy : iltb x y = 1 := by simpa using h.resolve_left (tcCons_ne_zero x s')
    obtain ⟨-, hs', hds⟩ := (isSL_cons_iff x s').mp hs
    rw [ifilt_cons, if_neg (not_ige_of_iltb hxy)]
    refine ih s' (tl_lt_tcCons x s') hs' ?_
    rcases hds with h | h
    · exact Or.inl h
    · exact Or.inr (iltb_of_le_of_lt (ige_eq_one.mp h) hxy)

/-- The filter of a descending list is empty or keeps the first entry: it is a prefix. -/
lemma ifilt_cases {s y : V} (hs : IsSL s) (hy : isTerm y) :
    ifilt s y = 0 ∨
      (s ≠ 0 ∧ ige (tcHd s) y = 1 ∧ ifilt s y = tcCons (tcHd s) (ifilt (tcTl s) y)) := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  obtain ⟨x, s', rfl⟩ := eq_cons_of_sumK hs.2 hs0
  rw [ifilt_cons]
  split_ifs with h
  · exact Or.inr ⟨tcCons_ne_zero _ _, by simpa using h, by simp⟩
  · left
    have hx : isTerm x := isTerm_of_isNF ((isSL_cons_iff x s').mp hs).1
    have hlt := iltb_of_not_ige hx hy h
    have := ifilt_eq_zero_aux y (tcCons x s') hs (Or.inr (by simpa using hlt))
    rwa [ifilt_cons, if_neg h] at this

lemma isSL_iapp_ifilt_aux (y t' : V) (ht : IsSL (tcCons y t')) :
    ∀ s : V, IsSL s → IsSL (iapp (ifilt s y) (tcCons y t')) := by
  have hy : isTerm y := isTerm_of_isNF ((isSL_cons_iff y t').mp ht).1
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro hs
    rcases eq_or_ne s 0 with rfl | hs0
    · simpa using ht
    obtain ⟨x, s', rfl⟩ := eq_cons_of_sumK hs.2 hs0
    obtain ⟨hx, hs', hds⟩ := (isSL_cons_iff x s').mp hs
    have IH := ih s' (tl_lt_tcCons x s') hs'
    rw [ifilt_cons]
    split_ifs with h
    · rw [iapp_cons]
      refine (isSL_cons_iff _ _).mpr ⟨hx, IH, ?_⟩
      rcases ifilt_cases hs' hy with e | ⟨hne, -, e⟩
      · rw [e, iapp_zero_left, tcHd_tcCons]; exact Or.inr h
      · rw [e, iapp_cons, tcHd_tcCons]; exact Or.inr (hds.resolve_left hne)
    · exact IH

/-- The exponent list of an ordinal sum of descending lists is descending. -/
lemma isSL_iaddL {s t : V} (hs : IsSL s) (ht : IsSL t) : IsSL (iaddL s t) := by
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [iaddL_zero_right]; exact hs
  obtain ⟨y, t', rfl⟩ := eq_cons_of_sumK ht.2 ht0
  rw [iaddL_cons]
  exact isSL_iapp_ifilt_aux y t' ht s hs

/-- **The ordinal sum preserves normal forms.** -/
theorem isNF_iadd {x y : V} (hx : isNF x) (hy : isNF y) : isNF (iadd x y) := by
  have h := isSL_iaddL (isSL_itoL hx) (isSL_itoL hy)
  exact isNF_iofL h.1 h.2

/-- The first entry of the exponent list of an ordinal sum. -/
lemma iaddL_cases {s y : V} (hs : IsSL s) (hy : isTerm y) (t' : V) :
    (∃ w, iaddL s (tcCons y t') = tcCons (tcHd s) w ∧ s ≠ 0) ∨
      (∃ w, iaddL s (tcCons y t') = tcCons y w) := by
  rw [iaddL_cons]
  rcases ifilt_cases hs hy with e | ⟨hne, -, e⟩
  · right; rw [e, iapp_zero_left]; exact ⟨t', rfl⟩
  · left; rw [e, iapp_cons]; exact ⟨_, rfl, hne⟩

/-! ### Additive principality -/

/-- **`ω^α` is additively indecomposable for the natural sum.** -/
theorem inadd_lt_iomegaPow {x y a : V} (hx : isNF x) (hy : isNF y)
    (hxa : iltb x (iomegaPow a) = 1) (hya : iltb y (iomegaPow a) = 1) :
    iltb (inadd x y) (iomegaPow a) = 1 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rwa [inadd_zero_left hy]
  rcases eq_or_ne y 0 with rfl | hy0
  · rwa [inadd_zero_right hx]
  have hxt := isTerm_of_isNF hx
  have hyt := isTerm_of_isNF hy
  have h1 := (iltb_iomegaPow_iff_ilead hxt hx0 a).mp hxa
  have h2 := (iltb_iomegaPow_iff_ilead hyt hy0 a).mp hya
  rw [inadd, itoL_eq_cons hxt hx0, itoL_eq_cons hyt hy0, imerge_cons_cons]
  split_ifs
  · exact iltb_iofL_cons_iomegaPow _ h1
  · exact iltb_iofL_cons_iomegaPow _ h2

/-- **`ω^α` is additively indecomposable for the ordinal sum.** -/
theorem iadd_lt_iomegaPow {x y a : V} (hx : isNF x) (hy : isNF y)
    (hxa : iltb x (iomegaPow a) = 1) (hya : iltb y (iomegaPow a) = 1) :
    iltb (iadd x y) (iomegaPow a) = 1 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rwa [iadd_zero_left hy]
  rcases eq_or_ne y 0 with rfl | hy0
  · rwa [iadd_zero_right hx]
  have hxt := isTerm_of_isNF hx
  have hyt := isTerm_of_isNF hy
  have h1 := (iltb_iomegaPow_iff_ilead hxt hx0 a).mp hxa
  have h2 := (iltb_iomegaPow_iff_ilead hyt hy0 a).mp hya
  have hyl : isTerm (ilead y) := isTerm_of_isNF (isNF_ilead hy hy0)
  rw [iadd, itoL_eq_cons hyt hy0]
  rcases iaddL_cases (isSL_itoL hx) hyl (tcTl (itoL y)) with ⟨w, e, -⟩ | ⟨w, e⟩
  · rw [e]; exact iltb_iofL_cons_iomegaPow _ h1
  · rw [e]; exact iltb_iofL_cons_iomegaPow _ h2

/-- The principal codes are additively principal for the natural sum. -/
theorem inadd_lt_prin {x y p : V} (hp : IsPrinC p) (hx : isNF x) (hy : isNF y)
    (hxp : iltb x p = 1) (hyp : iltb y p = 1) : iltb (inadd x y) p = 1 := by
  rw [← iomegaPow_of_prin hp] at hxp hyp ⊢
  exact inadd_lt_iomegaPow hx hy hxp hyp

/-- The principal codes are additively principal for the ordinal sum. -/
theorem iadd_lt_prin {x y p : V} (hp : IsPrinC p) (hx : isNF x) (hy : isNF y)
    (hxp : iltb x p = 1) (hyp : iltb y p = 1) : iltb (iadd x y) p = 1 := by
  rw [← iomegaPow_of_prin hp] at hxp hyp ⊢
  exact iadd_lt_iomegaPow hx hy hxp hyp

/-- `ϑ β` is additively principal (Freund §5). -/
theorem iadd_lt_theta {x y b : V} (hx : isNF x) (hy : isNF y)
    (hxb : iltb x (tcTheta b) = 1) (hyb : iltb y (tcTheta b) = 1) :
    iltb (iadd x y) (tcTheta b) = 1 :=
  iadd_lt_prin (isPrinC_tcTheta b) hx hy hxb hyb

/-- `ϑ β` is closed under `ω^·` from below. -/
theorem iomegaPow_lt_theta {x b : V} (h : iltb x (tcTheta b) = 1) :
    iltb (iomegaPow x) (tcTheta b) = 1 :=
  iltb_iomegaPow_of_lt_prin (isPrinC_tcTheta b) h

/-- The codes below `Ω` are closed under the ordinal sum. -/
theorem iadd_lt_one {x y : V} (hx : isNF x) (hy : isNF y)
    (hx1 : iltb x 1 = 1) (hy1 : iltb y 1 = 1) : iltb (iadd x y) 1 = 1 :=
  iadd_lt_prin isPrinC_one hx hy hx1 hy1

/-- The codes below `Ω` are closed under the natural sum. -/
theorem inadd_lt_one {x y : V} (hx : isNF x) (hy : isNF y)
    (hx1 : iltb x 1 = 1) (hy1 : iltb y 1 = 1) : iltb (inadd x y) 1 = 1 :=
  inadd_lt_prin isPrinC_one hx hy hx1 hy1

/-- The codes below `Ω` are closed under `ω^·`. -/
theorem iomegaPow_lt_one {x : V} (h : iltb x 1 = 1) : iltb (iomegaPow x) 1 = 1 :=
  iltb_iomegaPow_of_lt_prin isPrinC_one h

/-- **`ω^x ≺ ϑ α ↔ x ≺ ϑ α`** (the `ε`-number property of `ϑ α`). -/
theorem iomegaPow_lt_prin_iff {x p : V} (hp : IsPrinC p) :
    iltb (iomegaPow x) p = 1 ↔ iltb x p = 1 := by
  conv_lhs => rw [← iomegaPow_of_prin hp]
  exact iltb_iomegaPow_iff x p

/-! ### The successor -/

@[simp] lemma itoL_ione : itoL (ione : V) = ione := by rw [ione_eq, itoL_tcCons]

lemma imerge_ione_aux : ∀ s : V, imerge s ione = iapp s ione := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    by_cases hk : kind s = 3
    · obtain e := eq_tcCons_of_kind hk
      rw [e, ione_eq, imerge_cons_cons, if_pos (ige_zero_right _), ← ione_eq,
        ih _ (tcTl_lt (ne_zero_of_kind_ne_zero (by simp [hk]))), iapp_cons]
    · rw [imerge_left_of_kind hk, iapp_of_kind hk]

/-- `α ⊕ 1` appends the exponent `0`. -/
lemma imerge_ione (s : V) : imerge s ione = iapp s ione := imerge_ione_aux s

lemma iapp_ne_zero_of_ne_zero (s : V) {u : V} (hu : u ≠ 0) : iapp s u ≠ 0 := by
  by_cases hk : kind s = 3
  · rw [eq_tcCons_of_kind hk, iapp_cons]; exact tcCons_ne_zero _ _
  · rw [iapp_of_kind hk]; exact hu

lemma iofL_iapp_ione (s : V) : iofL (iapp s ione) = iapp s ione := by
  by_cases hk : kind s = 3
  · rw [eq_tcCons_of_kind hk, iapp_cons, iofL_cons,
      if_neg (fun h => iapp_ne_zero_of_ne_zero _ (tcCons_ne_zero 0 0) h.1)]
  · rw [iapp_of_kind hk, ione_eq, iofL_cons, if_neg (fun h => not_isPrinC_zero h.2)]

lemma isucc_eq (x : V) : isucc x = iapp (itoL x) ione := by
  rw [isucc, inadd, itoL_ione, imerge_ione, iofL_iapp_ione]

lemma iltb_iapp_self_aux (u : V) (hu : u ≠ 0) :
    ∀ s : V, isTerm s → sumK s = 1 → iltb s (iapp s u) = 1 := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro hs hk
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [iapp_zero_left]; exact iltb_zero_pos hu
    obtain ⟨x, s', rfl⟩ := eq_cons_of_sumK hk hs0
    obtain ⟨-, hs', hk'⟩ := (isTerm_tcCons_iff x s').mp hs
    rw [iapp_cons, iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
    exact Or.inr ⟨rfl, ih s' (tl_lt_tcCons x s') hs' hk'⟩

/-- **`α ≺ α + 1`.** -/
theorem iltb_isucc {x : V} (hx : isNF x) : iltb x (isucc x) = 1 := by
  rw [isucc_eq]
  have hxt := isTerm_of_isNF hx
  rcases isTerm_cases hxt with rfl | rfl | ⟨a, rfl, -⟩ | ⟨y, s, rfl, -⟩
  · rw [itoL_zero, iapp_zero_left]; exact iltb_zero_ione
  · rw [itoL_one, iapp_cons]; exact iltb_self_cons 1 _
  · rw [itoL_tcTheta, iapp_cons]; exact iltb_self_cons _ _
  · rw [itoL_tcCons]
    exact iltb_iapp_self_aux ione (tcCons_ne_zero 0 0) _ hxt (sumK_tcCons y s)

theorem isNF_isucc {x : V} (hx : isNF x) : isNF (isucc x) := isNF_inadd hx isNF_ione

/-- The principal codes are closed under the successor. -/
theorem isucc_lt_prin {x p : V} (hp : IsPrinC p) (hx : isNF x) (h : iltb x p = 1) :
    iltb (isucc x) p = 1 :=
  inadd_lt_prin hp hx isNF_ione h (iltb_ione_prin hp)

/-! ### Numerals -/

lemma inum_facts : ∀ n : V, IsSL (inum n) ∧ (inum n = 0 ∨ tcHd (inum n) = 0) := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [inum_zero]; exact ⟨isSL_zero, Or.inl rfl⟩
  case succ n ih =>
    rw [inum_succ]
    refine ⟨(isSL_cons_iff _ _).mpr ⟨isNF_zero, ih.1, ?_⟩, Or.inr (tcHd_tcCons 0 _)⟩
    rcases ih.2 with h | h
    · exact Or.inl h
    · rw [h]; exact Or.inr (ige_self 0)

lemma inum_eq_cons {n : V} (hn : inum n ≠ 0) : inum n = tcCons 0 (tcTl (inum n)) := by
  have h := eq_tcCons_of_kind (kind_eq_three_of_sumK (inum_facts n).1.2 hn)
  rw [(inum_facts n).2.resolve_left hn] at h
  exact h

/-- The numerals are normal forms. -/
theorem isNF_inum (n : V) : isNF (inum n) := by
  have h := isNF_iofL (inum_facts n).1.1 (inum_facts n).1.2
  rcases eq_or_ne (inum n) 0 with h0 | h0
  · rw [h0]; exact isNF_zero
  · rw [inum_eq_cons h0, iofL_cons, if_neg (fun h' => not_isPrinC_zero h'.2),
      ← inum_eq_cons h0] at h
    exact h

/-- The numerals are below every principal code. -/
theorem inum_lt_prin {p : V} (hp : IsPrinC p) (n : V) : iltb (inum n) p = 1 := by
  rcases eq_or_ne (inum n) 0 with h0 | h0
  · rw [h0]; exact iltb_zero_pos hp.ne_zero
  · rw [inum_eq_cons h0, iltb_cons_prinC _ _ hp]; exact iltb_zero_pos hp.ne_zero

lemma iapp_inum_ione : ∀ n : V, iapp (inum n) ione = inum (n + 1) := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [inum_one]
  case succ n ih => rw [inum_succ, iapp_cons, ih, inum_succ (n + 1)]

/-- **`n + 1` is the successor of `n`.** -/
theorem isucc_inum (n : V) : isucc (inum n) = inum (n + 1) := by
  rw [isucc_eq, itoL_of_not_prinC, iapp_inum_ione]
  intro h
  rcases eq_or_ne (inum n) 0 with h0 | h0
  · rw [h0] at h; exact not_isPrinC_zero h
  · rw [inum_eq_cons h0] at h; exact not_isPrinC_tcCons _ _ h

lemma iltb_inum_aux : ∀ m : V, ∀ k : V, iltb (inum m) (inum (m + k + 1)) = 1 := by
  intro m
  induction m using ISigma1.pi1_succ_induction
  · definability
  case zero =>
    intro k
    rw [zero_add, inum_succ, inum_zero]; exact iltb_zero_tcCons _ _
  case succ m ih =>
    intro k
    rw [show m + 1 + k + 1 = (m + k + 1) + 1 by rw [add_right_comm m 1 k], inum_succ,
      inum_succ, iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
    exact Or.inr ⟨rfl, ih k⟩

/-- **The numerals are strictly increasing.** -/
theorem iltb_inum_inum {m n : V} (h : m < n) : iltb (inum m) (inum n) = 1 := by
  have h1 : m + 1 ≤ n := lt_iff_succ_le.mp h
  have e : n - (m + 1) + (m + 1) = n := sub_add_self_of_le h1
  have := iltb_inum_aux m (n - (m + 1))
  rwa [show m + (n - (m + 1)) + 1 = n - (m + 1) + (m + 1) by
    rw [add_comm m, add_assoc], e] at this

/-! ### `1 + α` -/

lemma ionePlus_eq_iadd (e : V) : ionePlus e = iadd ione e := by
  rw [ionePlus, iadd, itoL_ione]

theorem isNF_ionePlus {e : V} (he : isNF e) : isNF (ionePlus e) := by
  rw [ionePlus_eq_iadd]; exact isNF_iadd isNF_ione he

/-! ### Exponent lists and the order

The order of normal forms is the order of their exponent lists (`iltb_itoL`), and a list
read back by `iofL` keeps its place (`iltb_iofL`): the internal form of
`ThetaNote.lt_iff_entries` and `ThetaTerm.ofList_lt_ofList`. -/

/-- The shapes of codes of normal forms. -/
lemma nf_cases {b : V} (hb : isNF b) :
    b = 0 ∨ IsPrinC b ∨ ∃ z w, b = tcCons z w ∧ ¬ (w = 0 ∧ IsPrinC z) := by
  have hs := sok_of_isNF hb
  rcases nfA_cases (nfA_of_isNF hb) with rfl | rfl | ⟨a, rfl, -⟩ | ⟨z, w, rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl isPrinC_one)
  · exact Or.inr (Or.inl (isPrinC_tcTheta a))
  · refine Or.inr (Or.inr ⟨z, w, rfl, fun h => ?_⟩)
    rw [sok_tcCons, if_pos ⟨h.1, h.2⟩] at hs
    simp at hs

lemma itoL_ne_zero {c : V} (hc : isTerm c) (hc0 : c ≠ 0) : itoL c ≠ 0 := by
  rw [itoL_eq_cons hc hc0]; exact tcCons_ne_zero _ _

lemma iofL_cons_ne_zero (z w : V) : iofL (tcCons z w) ≠ 0 := by
  rw [iofL_cons]
  split_ifs with h
  · exact h.2.ne_zero
  · exact tcCons_ne_zero _ _

/-- The order of normal forms is the order of their exponent lists. -/
lemma iltb_itoL {b c : V} (hb : isNF b) (hc : isNF c) (h : iltb b c = 1) :
    iltb (itoL b) (itoL c) = 1 := by
  have hc0 : c ≠ 0 := by rintro rfl; exact not_iltb_zero b h
  rcases nf_cases hb with rfl | hbp | ⟨z, w, rfl, -⟩
  · rw [itoL_zero]; exact iltb_zero_pos (itoL_ne_zero (isTerm_of_isNF hc) hc0)
  · rw [itoL_of_prinC hbp]
    rcases nf_cases hc with rfl | hcp | ⟨z', w', rfl, hzw⟩
    · exact absurd rfl hc0
    · rw [itoL_of_prinC hcp, iltb_single_single]; exact h
    · rw [itoL_tcCons, iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
      rcases (iltb_prinC_cons hbp z' w').mp h with h' | rfl
      · exact Or.inl h'
      · exact Or.inr ⟨rfl, iltb_zero_pos (fun hw => hzw ⟨hw, hbp⟩)⟩
  · rw [itoL_tcCons]
    rcases nf_cases hc with rfl | hcp | ⟨z', w', rfl, -⟩
    · exact absurd rfl hc0
    · rw [itoL_of_prinC hcp, iltb_cons_cons, bor_eq_one]
      rw [iltb_cons_prinC _ _ hcp] at h
      exact Or.inl h
    · rw [itoL_tcCons]; exact h

/-- A list read back by `iofL` keeps its place in the order. -/
lemma iltb_iofL {u v : V} (hu : sumK u = 1) (hv : sumK v = 1) (h : iltb u v = 1) :
    iltb (iofL u) (iofL v) = 1 := by
  have hv0 : v ≠ 0 := by rintro rfl; exact not_iltb_zero u h
  obtain ⟨z', w', rfl⟩ := eq_cons_of_sumK hv hv0
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [iofL_zero]; exact iltb_zero_pos (iofL_cons_ne_zero z' w')
  obtain ⟨z, w, rfl⟩ := eq_cons_of_sumK hu hu0
  rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at h
  rw [iofL_cons, iofL_cons]
  by_cases h1 : w = 0 ∧ IsPrinC z <;> by_cases h2 : w' = 0 ∧ IsPrinC z'
  · rw [if_pos h1, if_pos h2]
    rcases h with h | ⟨-, h⟩
    · exact h
    · rw [h1.1, h2.1] at h; exact absurd h (not_iltb_zero 0)
  · rw [if_pos h1, if_neg h2, iltb_prinC_cons h1.2]
    rcases h with h | ⟨e, -⟩
    · exact Or.inl h
    · exact Or.inr e
  · rw [if_neg h1, if_pos h2, iltb_cons_prinC _ _ h2.2]
    rcases h with h | ⟨-, h⟩
    · exact h
    · rw [h2.1] at h; exact absurd h (not_iltb_zero w)
  · rw [if_neg h1, if_neg h2, iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]; exact h

lemma ile_iofL {u v : V} (hu : sumK u = 1) (hv : sumK v = 1) (h : iltb u v = 1 ∨ u = v) :
    iltb (iofL u) (iofL v) = 1 ∨ iofL u = iofL v := by
  rcases h with h | rfl
  · exact Or.inl (iltb_iofL hu hv h)
  · exact Or.inr rfl

/-! ### Monotonicity of the ordinal sum -/

lemma iaddL_cons_cons (x s y w : V) :
    iaddL (tcCons x s) (tcCons y w) =
      if ige x y = 1 then tcCons x (iaddL s (tcCons y w)) else iaddL s (tcCons y w) := by
  rw [iaddL_cons, ifilt_cons]
  split_ifs
  · rw [iapp_cons, iaddL_cons]
  · rw [iaddL_cons]

lemma iaddL_eq_of_lt_head {s y w : V} (hs : IsSL s) (h : s = 0 ∨ iltb (tcHd s) y = 1) :
    iaddL s (tcCons y w) = tcCons y w := by
  rw [iaddL_cons, ifilt_eq_zero_aux y s hs h, iapp_zero_left]

/-- `α ≺ α + β` for `β ≠ 0`, on descending exponent lists. -/
lemma iltb_self_iaddL (y w : V) (hy : isTerm y) :
    ∀ s : V, IsSL s → iltb s (iaddL s (tcCons y w)) = 1 := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro hs
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [iaddL_zero_left (sumK_tcCons y w)]; exact iltb_zero_tcCons y w
    obtain ⟨x, s', rfl⟩ := eq_cons_of_sumK hs.2 hs0
    obtain ⟨hx, hs', hds⟩ := (isSL_cons_iff x s').mp hs
    rw [iaddL_cons_cons]
    split_ifs with hxy
    · rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
      exact Or.inr ⟨rfl, ih s' (tl_lt_tcCons x s') hs'⟩
    · have hlt := iltb_of_not_ige (isTerm_of_isNF hx) hy hxy
      rw [iaddL_eq_of_lt_head hs' (hds.imp id (fun h => iltb_of_le_of_lt (ige_eq_one.mp h) hlt)),
        iltb_cons_cons, bor_eq_one]
      exact Or.inl hlt

/-- The ordinal sum is strictly monotone in its right argument, on descending exponent
lists. -/
lemma iltb_iaddL_iaddL {y w y' w' : V} (hy' : isTerm y')
    (h : iltb (tcCons y w) (tcCons y' w') = 1) :
    ∀ s : V, IsSL s → iltb (iaddL s (tcCons y w)) (iaddL s (tcCons y' w')) = 1 := by
  have hyy : iltb y y' = 1 ∨ y = y' := by
    rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at h
    rcases h with h | ⟨e, -⟩
    · exact Or.inl h
    · exact Or.inr e
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro hs
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [iaddL_zero_left (sumK_tcCons y w), iaddL_zero_left (sumK_tcCons y' w')]; exact h
    obtain ⟨x, s', rfl⟩ := eq_cons_of_sumK hs.2 hs0
    obtain ⟨hx, hs', hds⟩ := (isSL_cons_iff x s').mp hs
    have hxt := isTerm_of_isNF hx
    have IH := ih s' (tl_lt_tcCons x s') hs'
    rw [iaddL_cons_cons, iaddL_cons_cons]
    by_cases h1 : ige x y = 1 <;> by_cases h2 : ige x y' = 1
    · rw [if_pos h1, if_pos h2, iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
      exact Or.inr ⟨rfl, IH⟩
    · rw [if_pos h1, if_neg h2]
      have hlt := iltb_of_not_ige hxt hy' h2
      rw [iaddL_eq_of_lt_head hs' (hds.imp id (fun h => iltb_of_le_of_lt (ige_eq_one.mp h) hlt)),
        iltb_cons_cons, bor_eq_one]
      exact Or.inl hlt
    · exfalso
      exact h1 (ige_eq_one.mpr (ile_trans hyy (ige_eq_one.mp h2)))
    · rw [if_neg h1, if_neg h2]; exact IH

/-- **The ordinal sum is strictly monotone in its right argument.** -/
theorem iadd_lt_iadd_right {a b c : V} (ha : isNF a) (hb : isNF b) (hc : isNF c)
    (h : iltb b c = 1) : iltb (iadd a b) (iadd a c) = 1 := by
  have hc0 : c ≠ 0 := by rintro rfl; exact not_iltb_zero b h
  have hs := isSL_itoL ha
  have ht := iltb_itoL hb hc h
  unfold iadd
  refine iltb_iofL (isSL_iaddL hs (isSL_itoL hb)).2 (isSL_iaddL hs (isSL_itoL hc)).2 ?_
  rw [itoL_eq_cons (isTerm_of_isNF hc) hc0] at ht ⊢
  have hy' : isTerm (ilead c) := isTerm_of_isNF (isNF_ilead hc hc0)
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [itoL_zero, iaddL_zero_right]
    exact iltb_self_iaddL _ _ hy' _ hs
  · rw [itoL_eq_cons (isTerm_of_isNF hb) hb0] at ht ⊢
    exact iltb_iaddL_iaddL hy' ht _ hs

/-- `α ≺ α + β` for normal `α` and normal `β ≠ 0`. -/
theorem iltb_self_iadd {a c : V} (ha : isNF a) (hc : isNF c) (hc0 : c ≠ 0) :
    iltb a (iadd a c) = 1 := by
  have := iadd_lt_iadd_right ha isNF_zero hc (iltb_zero_pos hc0)
  rwa [iadd_zero_right ha] at this

/-- `β ≼ α + β`, on descending exponent lists. -/
lemma ile_iaddL (y w : V) (ht : IsSL (tcCons y w)) :
    ∀ s : V, IsSL s → iltb (tcCons y w) (iaddL s (tcCons y w)) = 1 ∨
      tcCons y w = iaddL s (tcCons y w) := by
  obtain ⟨hy, hw, hdw⟩ := (isSL_cons_iff y w).mp ht
  have hwt : iltb w (tcCons y w) = 1 :=
    iltb_tail_cons w y hw.1 hw.2 (hdw.imp id ige_eq_one.mp)
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro hs
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [iaddL_zero_left (sumK_tcCons y w)]; exact Or.inr rfl
    obtain ⟨x, s', rfl⟩ := eq_cons_of_sumK hs.2 hs0
    obtain ⟨-, hs', -⟩ := (isSL_cons_iff x s').mp hs
    have IH := ih s' (tl_lt_tcCons x s') hs'
    rw [iaddL_cons_cons]
    split_ifs with hxy
    · refine Or.inl ?_
      rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
      rcases ige_eq_one.mp hxy with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨rfl, iltb_of_lt_of_le hwt IH⟩
    · exact IH

/-- `β ≼ α + β` for normal `α`, `β`. -/
theorem ile_iadd_right {a b : V} (ha : isNF a) (hb : isNF b) :
    iltb b (iadd a b) = 1 ∨ b = iadd a b := by
  rcases eq_or_ne b 0 with rfl | hb0
  · exact ile_zero_left _
  have hs := isSL_itoL ha
  have ht := isSL_itoL hb
  rw [itoL_eq_cons (isTerm_of_isNF hb) hb0] at ht
  have h := ile_iaddL _ _ ht _ hs
  rw [← itoL_eq_cons (isTerm_of_isNF hb) hb0] at h
  have h' := ile_iofL (sumK_itoL (isTerm_of_isNF hb))
    (isSL_iaddL hs (isSL_itoL hb)).2 h
  rwa [iofL_itoL hb] at h'

/-- `α ≼ α + β` for normal `α`, `β`. -/
theorem ile_iadd_left {a b : V} (ha : isNF a) (hb : isNF b) :
    iltb a (iadd a b) = 1 ∨ a = iadd a b := by
  rcases eq_or_ne b 0 with rfl | hb0
  · exact Or.inr (iadd_zero_right ha).symm
  · exact Or.inl (iltb_self_iadd ha hb hb0)

/-! ### Monotonicity and commutativity of the natural sum -/


/-- Moving a common first entry across a merge. -/
lemma imerge_cons_left_eq (x t : V) (hxt : IsSL (tcCons x t)) :
    ∀ s : V, IsSL (tcCons x s) → imerge s (tcCons x t) = imerge (tcCons x s) t := by
  obtain ⟨-, ht, hdt⟩ := (isSL_cons_iff x t).mp hxt
  have rhs : ∀ u : V, sumK u = 1 → imerge (tcCons x u) t = tcCons x (imerge u t) := by
    intro u hu
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [imerge_zero_right (sumK_tcCons x u), imerge_zero_right hu]
    · obtain ⟨b, t', rfl⟩ := eq_cons_of_sumK ht.2 ht0
      rw [imerge_cons_cons, if_pos (by simpa using hdt.resolve_left ht0)]
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro hs
    obtain ⟨-, hs', hds⟩ := (isSL_cons_iff x s).mp hs
    rw [rhs s hs'.2]
    rcases eq_or_ne s 0 with rfl | hs0
    · simp
    obtain ⟨a, s', rfl⟩ := eq_cons_of_sumK hs'.2 hs0
    have hxa : ige x a = 1 := by simpa using hds.resolve_left hs0
    rw [imerge_cons_cons]
    split_ifs with hax
    · have e : a = x := ile_antisymm (ige_eq_one.mp hxa) (ige_eq_one.mp hax)
      subst e
      rw [ih s' (tl_lt_tcCons a s') ((isSL_cons_iff a s').mpr ?_), rhs s' ?_]
      · exact ((isSL_cons_iff a s').mp hs').2.1.2
      · exact (isSL_cons_iff a s').mp hs'
    · rfl

private lemma sum3_lt' {x y z x' y' z' : V} (hx : x' ≤ x) (hy : y' ≤ y) (hz : z' ≤ z)
    (hs : x' < x ∨ y' < y ∨ z' < z) : x' + y' + z' < x + y + z := by
  rcases hs with h | h | h
  · exact add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le h hy) hz
  · exact add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt hx h) hz
  · exact add_lt_add_of_le_of_lt (add_le_add hx hy) h

lemma imerge_comm_aux : ∀ w : V, ∀ s ≤ w, ∀ t ≤ w, s + t ≤ w →
    IsSL s → IsSL t → imerge s t = imerge t s := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro s _ t _ hsum hs ht
    have IH : ∀ {s₁ t₁ : V}, s₁ + t₁ < s + t → IsSL s₁ → IsSL t₁ →
        imerge s₁ t₁ = imerge t₁ s₁ :=
      fun {s₁ t₁} hlt => ih (s₁ + t₁) (lt_of_lt_of_le hlt hsum) s₁ le_self_add t₁ le_add_self
        le_rfl
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [imerge_zero_left, imerge_zero_right ht.2]
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [imerge_zero_left, imerge_zero_right hs.2]
    obtain ⟨x, s', rfl⟩ := eq_cons_of_sumK hs.2 hs0
    obtain ⟨y, t', rfl⟩ := eq_cons_of_sumK ht.2 ht0
    obtain ⟨hx, hs', -⟩ := (isSL_cons_iff x s').mp hs
    obtain ⟨hy, ht', -⟩ := (isSL_cons_iff y t').mp ht
    rw [imerge_cons_cons, imerge_cons_cons]
    by_cases h1 : ige x y = 1 <;> by_cases h2 : ige y x = 1
    · have e : x = y := ile_antisymm (ige_eq_one.mp h2) (ige_eq_one.mp h1)
      subst e
      rw [if_pos h1, if_pos h2, imerge_cons_left_eq x t' ht s' hs,
        IH (add_lt_add_of_le_of_lt le_rfl (tl_lt_tcCons x t')) hs ht']
    · rw [if_pos h1, if_neg h2,
        IH (add_lt_add_of_lt_of_le (tl_lt_tcCons x s') le_rfl) hs' ht]
    · rw [if_neg h1, if_pos h2,
        IH (add_lt_add_of_le_of_lt le_rfl (tl_lt_tcCons y t')) hs ht']
    · exfalso
      have := iltb_of_not_ige (isTerm_of_isNF hx) (isTerm_of_isNF hy) h1
      exact h2 (ige_of_iltb this)

/-- The merge of descending lists is commutative. -/
lemma imerge_comm {s t : V} (hs : IsSL s) (ht : IsSL t) : imerge s t = imerge t s :=
  imerge_comm_aux (s + t) s le_self_add t le_add_self le_rfl hs ht

/-- A descending list is below its merge with a nonempty descending list. -/
lemma iltb_imerge_right (s : V) (hs : IsSL s) (hs0 : s ≠ 0) :
    ∀ t : V, IsSL t → iltb t (imerge s t) = 1 := by
  obtain ⟨z, s', rfl⟩ := eq_cons_of_sumK hs.2 hs0
  intro t
  induction t using ISigma1.sigma1_order_induction
  · definability
  case ind t ih =>
    intro ht
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [imerge_zero_right hs.2]; exact iltb_zero_tcCons z s'
    obtain ⟨y, t', rfl⟩ := eq_cons_of_sumK ht.2 ht0
    obtain ⟨-, ht', -⟩ := (isSL_cons_iff y t').mp ht
    have IH := ih t' (tl_lt_tcCons y t') ht'
    rw [imerge_cons_cons]
    split_ifs with hzy
    · rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
      rcases ige_eq_one.mp hzy with h | rfl
      · exact Or.inl h
      · refine Or.inr ⟨rfl, ?_⟩
        rw [imerge_cons_left_eq y t' ht s' hs]
        exact IH
    · rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
      exact Or.inr ⟨rfl, IH⟩

lemma iltb_imerge_left_aux : ∀ w : V, ∀ s ≤ w, ∀ s' ≤ w, ∀ t ≤ w, s + s' + t ≤ w →
    IsSL s → IsSL s' → IsSL t → iltb s s' = 1 → iltb (imerge s t) (imerge s' t) = 1 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro s _ s' _ t _ hsum hs hs' ht h
    have IH : ∀ {a b c : V}, a + b + c < s + s' + t → IsSL a → IsSL b → IsSL c →
        iltb a b = 1 → iltb (imerge a c) (imerge b c) = 1 :=
      fun {a b c} hlt => ih (a + b + c) (lt_of_lt_of_le hlt hsum)
        a (le_trans le_self_add le_self_add) b (le_trans le_add_self le_self_add)
        c le_add_self le_rfl
    have hs'0 : s' ≠ 0 := by rintro rfl; exact not_iltb_zero s h
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [imerge_zero_right hs.2, imerge_zero_right hs'.2]; exact h
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [imerge_zero_left]; exact iltb_imerge_right s' hs' hs'0 t ht
    obtain ⟨a1, l1, rfl⟩ := eq_cons_of_sumK hs.2 hs0
    obtain ⟨a2, l2, rfl⟩ := eq_cons_of_sumK hs'.2 hs'0
    obtain ⟨y, ys, rfl⟩ := eq_cons_of_sumK ht.2 ht0
    obtain ⟨ha1, hl1, -⟩ := (isSL_cons_iff a1 l1).mp hs
    obtain ⟨-, hl2, -⟩ := (isSL_cons_iff a2 l2).mp hs'
    obtain ⟨hy, hys, -⟩ := (isSL_cons_iff y ys).mp ht
    have hb3 : tcCons a1 l1 + tcCons a2 l2 + ys < tcCons a1 l1 + tcCons a2 l2 + tcCons y ys :=
      sum3_lt' le_rfl le_rfl (tl_lt_tcCons y ys).le (Or.inr (Or.inr (tl_lt_tcCons y ys)))
    have h' := h
    rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at h'
    rw [imerge_cons_cons, imerge_cons_cons]
    rcases h' with h12 | ⟨rfl, hl⟩
    · by_cases h1 : ige a1 y = 1
      · have h2 : ige a2 y = 1 := ige_of_iltb (iltb_of_le_of_lt (ige_eq_one.mp h1) h12)
        rw [if_pos h1, if_pos h2, iltb_cons_cons, bor_eq_one]
        exact Or.inl h12
      · rw [if_neg h1]
        by_cases h2 : ige a2 y = 1
        · rw [if_pos h2]
          rcases ige_eq_one.mp h2 with h2' | e
          · rw [iltb_cons_cons, bor_eq_one]; exact Or.inl h2'
          · subst e
            rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
            refine Or.inr ⟨rfl, ?_⟩
            rw [imerge_cons_left_eq y ys ht l2 hs']
            exact IH hb3 hs hs' hys h
        · rw [if_neg h2, iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
          exact Or.inr ⟨rfl, IH hb3 hs hs' hys h⟩
    · by_cases h1 : ige a1 y = 1
      · rw [if_pos h1, if_pos h1, iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
        refine Or.inr ⟨rfl, IH ?_ hl1 hl2 ht hl⟩
        exact sum3_lt' (tl_lt_tcCons a1 l1).le (tl_lt_tcCons a1 l2).le le_rfl
          (Or.inl (tl_lt_tcCons a1 l1))
      · rw [if_neg h1, if_neg h1, iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]
        exact Or.inr ⟨rfl, IH hb3 hs hs' hys h⟩

/-- The merge of descending lists is strictly monotone in its left argument. -/
lemma iltb_imerge_left {s s' t : V} (hs : IsSL s) (hs' : IsSL s') (ht : IsSL t)
    (h : iltb s s' = 1) : iltb (imerge s t) (imerge s' t) = 1 :=
  iltb_imerge_left_aux (s + s' + t) s (le_trans le_self_add le_self_add)
    s' (le_trans le_add_self le_self_add) t le_add_self le_rfl hs hs' ht h

/-- **The natural sum is commutative** on normal forms. -/
theorem inadd_comm {a b : V} (ha : isNF a) (hb : isNF b) : inadd a b = inadd b a := by
  unfold inadd; rw [imerge_comm (isSL_itoL ha) (isSL_itoL hb)]

/-- **The natural sum is strictly monotone in its left argument.** -/
theorem inadd_lt_inadd_left {a a' b : V} (ha : isNF a) (ha' : isNF a') (hb : isNF b)
    (h : iltb a a' = 1) : iltb (inadd a b) (inadd a' b) = 1 := by
  unfold inadd
  exact iltb_iofL (isSL_imerge (isSL_itoL ha) (isSL_itoL hb)).2
    (isSL_imerge (isSL_itoL ha') (isSL_itoL hb)).2
    (iltb_imerge_left (isSL_itoL ha) (isSL_itoL ha') (isSL_itoL hb) (iltb_itoL ha ha' h))

/-- **The natural sum is strictly monotone in its right argument.** -/
theorem inadd_lt_inadd_right {a b b' : V} (ha : isNF a) (hb : isNF b) (hb' : isNF b')
    (h : iltb b b' = 1) : iltb (inadd a b) (inadd a b') = 1 := by
  rw [inadd_comm ha hb, inadd_comm ha hb']
  exact inadd_lt_inadd_left hb hb' ha h

/-- `α ≺ α ⊕ β` for `β ≠ 0`. -/
theorem iltb_self_inadd {a b : V} (ha : isNF a) (hb : isNF b) (hb0 : b ≠ 0) :
    iltb a (inadd a b) = 1 := by
  have := inadd_lt_inadd_right ha isNF_zero hb (iltb_zero_pos hb0)
  rwa [inadd_zero_right ha] at this

/-- `α ≼ α ⊕ β`. -/
theorem ile_inadd_left {a b : V} (ha : isNF a) (hb : isNF b) :
    iltb a (inadd a b) = 1 ∨ a = inadd a b := by
  rcases eq_or_ne b 0 with rfl | hb0
  · exact Or.inr (inadd_zero_right ha).symm
  · exact Or.inl (iltb_self_inadd ha hb hb0)

/-- `β ≼ α ⊕ β`. -/
theorem ile_inadd_right {a b : V} (ha : isNF a) (hb : isNF b) :
    iltb b (inadd a b) = 1 ∨ b = inadd a b := by
  rw [inadd_comm ha hb]; exact ile_inadd_left hb ha

end OrdinalAnalysis.ID1.Internal
