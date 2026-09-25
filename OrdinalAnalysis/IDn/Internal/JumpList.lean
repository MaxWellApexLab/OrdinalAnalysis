/-
  Exponent lists of the coded multi-level ϑ-notation inside models of `IΣ₁`: concatenation
  and the facts about appending one exponent at the end that Gentzen's jump needs (the
  one-level template is `ID1/Internal/JumpList.lean`, with `iapp` from `ID1/Internal/Arith.lean`).

  A normal form `α = ω^{α₀} + ⋯ + ω^{α_{m-1}}` is read through its exponent list `expList α`
  (`⟨α⟩` for principal `α`, `α` itself otherwise), and the order of normal forms is the
  lexicographic order of their exponent lists (`iltb_expList_iff`).  A *descending list*
  (`isSL`) is a sum code whose entries are normal domain codes, non-increasing; it is the
  normal-form flag `nfA` of a sum code without the one-entry condition, together with the domain
  flag.  Gentzen's jump extends a list `η` by one exponent at the end, `η ++ ⟨y⟩ = isnocL η y`,
  and uses:

  * `iapp_isnocL`: `(η ++ ⟨y⟩) ++ w = η ++ (y :: w)`;
  * `iltb_isnocL_cases`: every descending list `ζ ≺ η ++ ⟨y⟩` is `≼ η` or of the form `η ++ ρ`
    with `ρ` nonempty and first exponent `≺ y`;
  * `isSL_isnocL_of_isSL_iapp`: `η ++ ⟨z⟩` is descending when `η ++ (z :: w)` is;
  * `isSL_of_isSL_iapp_right`, `iinE_iapp_right`, `iltb_iapp_iapp`;
  * `isNF_isDom_tcCons_iff`: a sum code is a normal domain code iff it is a descending list and
    not a one-entry list with a principal entry.
-/
import OrdinalAnalysis.IDn.Internal.OrderE

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.ID1.Internal (bor band beq bor_eq_one band_eq_one beq_eq_one covVal
  covVal_unfold covValDef covVal_defined)

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Concatenation of list codes -/

/-- The value stored in a table `S` at `⟪x, y⟫`. -/
noncomputable def rdPair (S x y : V) : V := znth S ⟪x, y⟫

def rdPairDef : 𝚺₁.Semisentence 4 := .mkSigma
  “r S x y. ∃ i, !pairDef i x y ∧ !znthDef r S i”

instance rdPair_defined : 𝚺₁-Function₃ (rdPair : V → V → V → V) via rdPairDef := .mk fun v ↦ by
  simp [rdPairDef, rdPair, pair_defined.iff, znth_defined.iff]

/-- The concatenation of two lists, one step. -/
noncomputable def appF (s t S : V) : V :=
  if kind s = 3 then tcCons (tcHd s) (rdPair S (tcTl s) t) else t

def appFDef : 𝚺₁.Semisentence 4 := .mkSigma
  “r s t S. ∃ ks, !kindDef ks s ∧
    ( (ks ≠ 3 ∧ r = t)
    ∨ (ks = 3 ∧ ∃ x, !tcHdDef x s ∧ ∃ u, !tcTlDef u s ∧ ∃ w, !rdPairDef w S u t ∧
        !tcConsDef r x w))”

instance appF_defined : 𝚺₁-Function₃ (appF : V → V → V → V) via appFDef := .mk fun v ↦ by
  simp [appFDef, appF, kind_defined.iff, tcHd_defined.iff, tcTl_defined.iff,
    rdPair_defined.iff, tcCons_defined.iff]
  by_cases h1 : kind (v 1) = 3 <;> simp [h1]

/-- The step of the concatenation table at position `⟪s, t⟫`. -/
noncomputable def appStep (i S : V) : V := appF (π₁ i) (π₂ i) S

def appStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r i S. ∃ s, !pi₁Def s i ∧ ∃ t, !pi₂Def t i ∧ !appFDef r s t S”

instance appStep_defined : 𝚺₁-Function₂ (appStep : V → V → V) via appStepDef :=
  .mk fun v ↦ by simp [appStepDef, appStep, pi₁_defined.iff, pi₂_defined.iff,
    appF_defined.iff]

/-- **The concatenation** `s ++ t` of two list codes (a code that is not a cons cell is read
as the empty list). -/
noncomputable def iapp (s t : V) : V := covVal appStep appStepDef ⟪s, t⟫

def iappDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r s t. ∃ i, !pairDef i s t ∧ !(covValDef appStepDef) r i”

instance iapp_defined : 𝚺₁-Function₂ (iapp : V → V → V) via iappDef := .mk fun v ↦ by
  simp [iappDef, iapp, pair_defined.iff, (covVal_defined appStep appStepDef).iff]

instance iapp_definable : 𝚺₁-Function₂ (iapp : V → V → V) := iapp_defined.to_definable
instance iapp_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (iapp : V → V → V) :=
  iapp_definable.of_sigmaOne

lemma iapp_unfold (s t : V) :
    ∃ S : V, iapp s t = appF s t S ∧
      ∀ x z : V, ⟪x, z⟫ < ⟪s, t⟫ → rdPair S x z = iapp x z := by
  obtain ⟨S, h, hr⟩ := covVal_unfold appStep appStepDef (⟪s, t⟫ : V)
  exact ⟨S, by rw [iapp, h, appStep, pi₁_pair, pi₂_pair], fun x z hxz => hr _ hxz⟩

lemma iapp_of_kind {s : V} (hs : kind s ≠ 3) (t : V) : iapp s t = t := by
  obtain ⟨S, h, -⟩ := iapp_unfold s t
  simp [h, appF, hs]

@[simp] lemma iapp_zero_left (t : V) : iapp 0 t = t := iapp_of_kind (by simp) t

lemma iapp_cons (x s t : V) : iapp (tcCons x s) t = tcCons x (iapp s t) := by
  obtain ⟨S, h, hr⟩ := iapp_unfold (tcCons x s) t
  rw [h, appF]
  simp only [kind_tcCons, tcHd_tcCons, tcTl_tcCons, if_true]
  rw [hr s t (pair_lt_pair_left (tl_lt_tcCons x s) _)]

lemma iapp_ne_zero {t : V} (s : V) (ht : t ≠ 0) : iapp s t ≠ 0 := by
  by_cases hk : kind s = 3
  · rw [eq_tcCons_of_kind hk, iapp_cons]; exact tcCons_ne_zero _ _
  · rw [iapp_of_kind hk]; exact ht

/-- `s ++ ⟨y⟩`: the list `s` with the exponent `y` appended at the end. -/
noncomputable def isnocL (s y : V) : V := iapp s (tcCons y 0)

instance isnocL_definable (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (isnocL : V → V → V) := by
  unfold isnocL; definability

@[simp] lemma isnocL_zero (y : V) : isnocL 0 y = tcCons y 0 := by simp [isnocL]

lemma isnocL_cons (a s y : V) : isnocL (tcCons a s) y = tcCons a (isnocL s y) := by
  simp [isnocL, iapp_cons]

/-- `(s ++ ⟨y⟩) ++ w = s ++ (y :: w)`. -/
lemma iapp_isnocL (y w : V) : ∀ s : V, iapp (isnocL s y) w = iapp s (tcCons y w) := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    by_cases hk : kind s = 3
    · rw [eq_tcCons_of_kind hk, isnocL_cons, iapp_cons, iapp_cons,
        ih _ (tcTl_lt (fun h => by rw [h] at hk; simp at hk))]
    · rw [isnocL, iapp_of_kind hk, iapp_of_kind hk, iapp_cons, iapp_zero_left]

/-- The appended list is at least as large, as a number, as its second part. -/
lemma le_iapp_right (t : V) : ∀ s : V, t ≤ iapp s t := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    by_cases hk : kind s = 3
    · rw [eq_tcCons_of_kind hk, iapp_cons]
      exact le_of_lt (lt_of_le_of_lt (ih _ (tcTl_lt (fun h => by rw [h] at hk; simp at hk)))
        (tl_lt_tcCons _ _))
    · rw [iapp_of_kind hk]

/-- The coefficients of `ρ` are coefficients of `s ++ ρ`. -/
lemma iinE_iapp_right (k g t : V) : ∀ s : V, iinE k g t = 1 → iinE k g (iapp s t) = 1 := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro h
    by_cases hk : kind s = 3
    · rw [eq_tcCons_of_kind hk, iapp_cons, iinE_cons_iff]
      exact Or.inr (ih _ (tcTl_lt (fun h => by rw [h] at hk; simp at hk)) h)
    · rw [iapp_of_kind hk]; exact h

/-- The first entry of `s ++ (z :: w)` does not depend on `w`. -/
lemma tcHd_iapp_cons (s z w w' : V) :
    tcHd (iapp s (tcCons z w)) = tcHd (iapp s (tcCons z w')) := by
  by_cases hk : kind s = 3
  · rw [eq_tcCons_of_kind hk, iapp_cons, iapp_cons, tcHd_tcCons, tcHd_tcCons]
  · rw [iapp_of_kind hk, iapp_of_kind hk, tcHd_tcCons, tcHd_tcCons]

/-! ### Descending lists -/

/-- `s` is a descending list: a sum code whose entries are normal domain codes, each `≼` the
one before. -/
def isSL (s : V) : Prop := sumK s = 1 ∧ nfA s = 1 ∧ isDom s

def isSLDef : 𝚺₁.Semisentence 1 := .mkSigma
  “s. !sumKDef 1 s ∧ !nfADef 1 s ∧ !isDombDef 1 s”

instance isSL_defined : 𝚺₁-Predicate (isSL : V → Prop) via isSLDef := .mk fun v ↦ by
  simp [isSLDef, isSL, isDom, sumK_defined.iff, nfA_defined.iff, isDomb_defined.iff, eq_comm]

instance isSL_definable (Γ) (m : ℕ) : Γ-[m + 1]-Predicate (isSL : V → Prop) := by
  unfold isSL; definability

lemma isSL_zero : isSL (0 : V) := ⟨sumK_zero, nfA_zero, isDom_at_zero⟩

lemma isSL_cons_iff (x w : V) :
    isSL (tcCons x w) ↔
      (isNF x ∧ isDom x) ∧ isSL w ∧ (w = 0 ∨ iltb (tcHd w) x = 1 ∨ tcHd w = x) := by
  unfold isSL
  rw [nfA_tcCons, band_eq_one, band_eq_one, band_eq_one, isDom_tcCons_iff]
  simp only [sumK_tcCons, true_and]
  constructor
  · rintro ⟨⟨hx, hw, hk, hd⟩, hdx, hdw⟩
    exact ⟨⟨hx, hdx⟩, ⟨hk, hw, hdw⟩, (descOk_tcCons_iff x w hk).mp hd⟩
  · rintro ⟨⟨hx, hdx⟩, ⟨hk, hw, hdw⟩, hd⟩
    exact ⟨⟨hx, hw, hk, (descOk_tcCons_iff x w hk).mpr hd⟩, hdx, hdw⟩

lemma isSL_shape {s : V} (hs : isSL s) : s = 0 ∨ kind s = 3 := by
  have h := hs.1
  unfold sumK at h
  split_ifs at h with hk
  · rcases hk with hk | hk
    · exact Or.inl (kind_eq_zero_iff.mp hk)
    · exact Or.inr hk
  · simp at h

lemma isSL_eq_cons {s : V} (hs : isSL s) (hs0 : s ≠ 0) : ∃ x w, s = tcCons x w :=
  eq_cons_of_sumK_one hs.1 hs0

/-- **A sum code is a normal domain code iff it is a descending list and not a one-entry list
with a principal entry.** -/
lemma isNF_isDom_tcCons_iff (x w : V) :
    (isNF (tcCons x w) ∧ isDom (tcCons x w)) ↔
      isSL (tcCons x w) ∧ ¬ (w = 0 ∧ (kind x = 1 ∨ kind x = 2)) := by
  unfold isNF isNFb isSL
  rw [band_eq_one, sok_tcCons]
  simp only [sumK_tcCons, true_and]
  by_cases h : w = 0 ∧ (kind x = 1 ∨ kind x = 2)
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

/-- `s ++ ⟨z⟩` is descending when `s ++ (z :: w)` is. -/
lemma isSL_isnocL_of_isSL_iapp (z w : V) :
    ∀ s : V, isSL (iapp s (tcCons z w)) → isSL (isnocL s z) := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro h
    by_cases hk : kind s = 3
    · have e := eq_tcCons_of_kind hk
      have hlt : tcTl s < s := tcTl_lt (fun h => by rw [h] at hk; simp at hk)
      rw [e, iapp_cons, isSL_cons_iff] at h
      rw [e, isnocL_cons, isSL_cons_iff]
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨h1, ih _ hlt h2, Or.inr ?_⟩
      rcases h3 with h3 | h3
      · exact absurd h3 (iapp_ne_zero _ (tcCons_ne_zero z w))
      · rw [isnocL, tcHd_iapp_cons (tcTl s) z 0 w]; exact h3
    · rw [iapp_of_kind hk, isSL_cons_iff] at h
      rw [isnocL, iapp_of_kind hk, isSL_cons_iff]
      exact ⟨h.1, isSL_zero, Or.inl rfl⟩

/-- The second part of a descending list `s ++ ρ` is descending. -/
lemma isSL_of_isSL_iapp_right (r : V) : ∀ s : V, isSL (iapp s r) → isSL r := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro h
    by_cases hk : kind s = 3
    · rw [eq_tcCons_of_kind hk, iapp_cons, isSL_cons_iff] at h
      exact ih _ (tcTl_lt (fun h => by rw [h] at hk; simp at hk)) h.2.1
    · rwa [iapp_of_kind hk] at h

/-- A common prefix does not change the order (descending prefix). -/
lemma iltb_iapp_iapp (u v : V) :
    ∀ s : V, isSL s → (iltb (iapp s u) (iapp s v) = 1 ↔ iltb u v = 1) := by
  intro s
  induction s using ISigma1.sigma1_order_induction
  · definability
  case ind s ih =>
    intro hs
    rcases isSL_shape hs with rfl | hk
    · simp
    · have e := eq_tcCons_of_kind hk
      have hlt : tcTl s < s := tcTl_lt (fun h => by rw [h] at hk; simp at hk)
      rw [e, isSL_cons_iff] at hs
      rw [e, iapp_cons, iapp_cons, iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one,
        ih _ hlt hs.2.1]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact absurd h (iltb_irrefl (isTerm_of_isNF hs.1.1))
        · exact h
      · intro h; exact Or.inr ⟨rfl, h⟩

/-- **Below `η ++ ⟨y⟩`**, bounded form. -/
lemma iltb_isnocL_cases_bdd (y : V) :
    ∀ s : V, isSL s → ∀ z, isSL z → iltb z (isnocL s y) = 1 →
      iltb z s = 1 ∨ z = s ∨ ∃ r ≤ z, z = iapp s r ∧ r ≠ 0 ∧ iltb (tcHd r) y = 1 := by
  intro s
  induction s using ISigma1.pi1_order_induction
  · definability
  case ind s ih =>
    intro hs z hz h
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [isnocL_zero] at h
      rcases eq_or_ne z 0 with rfl | hz0
      · exact Or.inr (Or.inl rfl)
      obtain ⟨c, r', rfl⟩ := isSL_eq_cons hz hz0
      rw [iltb_cons_cons, bor_eq_one, band_eq_one] at h
      rcases h with h | ⟨-, h⟩
      · exact Or.inr (Or.inr ⟨tcCons c r', le_rfl, by rw [iapp_zero_left],
          tcCons_ne_zero _ _, by rw [tcHd_tcCons]; exact h⟩)
      · exact absurd h (not_iltb_zero_right r')
    obtain ⟨a, s', rfl⟩ := isSL_eq_cons hs hs0
    have hs' : isSL s' := ((isSL_cons_iff a s').mp hs).2.1
    rw [isnocL_cons] at h
    rcases eq_or_ne z 0 with rfl | hz0
    · exact Or.inl (iltb_zero_pos (tcCons_ne_zero a s'))
    obtain ⟨c, r', rfl⟩ := isSL_eq_cons hz hz0
    have hr' : isSL r' := ((isSL_cons_iff c r').mp hz).2.1
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

/-- **Below `η ++ ⟨y⟩`.**  A descending list `ζ ≺ η ++ ⟨y⟩` is `≼ η` or of the form `η ++ ρ`
with `ρ` nonempty and first exponent `≺ y`. -/
lemma iltb_isnocL_cases {s y z : V} (hs : isSL s) (hz : isSL z)
    (h : iltb z (isnocL s y) = 1) :
    iltb z s = 1 ∨ z = s ∨ ∃ r, z = iapp s r ∧ r ≠ 0 ∧ iltb (tcHd r) y = 1 := by
  rcases iltb_isnocL_cases_bdd y s hs z hz h with h | h | ⟨r, -, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨r, h⟩)

/-! ### Exponent lists -/

/-- The exponent list of a code: `⟨c⟩` for the principal codes, `c` itself otherwise. -/
noncomputable def expList (c : V) : V := if kind c = 1 ∨ kind c = 2 then tcCons c 0 else c

def expListDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ k, !kindDef k c ∧ (((k = 1 ∨ k = 2) ∧ !tcConsDef y c 0) ∨ (k ≠ 1 ∧ k ≠ 2 ∧ y = c))”

instance expList_defined : 𝚺₁-Function₁ (expList : V → V) via expListDef := .mk fun v ↦ by
  simp [expListDef, expList, kind_defined.iff, tcCons_defined.iff]
  by_cases h : kind (v 1) = 1 ∨ kind (v 1) = 2
  · rw [if_pos h]; tauto
  · rw [if_neg h]; rw [not_or] at h; tauto

instance expList_definable : 𝚺₁-Function₁ (expList : V → V) := expList_defined.to_definable
instance expList_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (expList : V → V) :=
  expList_definable.of_sigmaOne

lemma expList_of_prin {c : V} (h : kind c = 1 ∨ kind c = 2) : expList c = tcCons c 0 := by
  simp [expList, h]

@[simp] lemma expList_zero : expList (0 : V) = 0 := by simp [expList]

@[simp] lemma expList_tcCons (x s : V) : expList (tcCons x s) = tcCons x s := by simp [expList]

/-- The shapes of codes of normal forms. -/
lemma isNF_shape {b : V} (hb : isNF b) :
    b = 0 ∨ (kind b = 1 ∨ kind b = 2) ∨ ∃ x s, b = tcCons x s := by
  rcases isTerm_cases (isTerm_of_isNF hb) with rfl | ⟨i, rfl⟩ | ⟨i, a, rfl, -⟩ | ⟨x, s, rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (Or.inl (kind_tcOmega i)))
  · exact Or.inr (Or.inl (Or.inr (kind_tcTheta i a)))
  · exact Or.inr (Or.inr ⟨x, s, rfl⟩)

/-- **The exponent list of a normal domain code is a descending list.** -/
lemma isSL_expList {x : V} (hx : isNF x) (hdx : isDom x) : isSL (expList x) := by
  rcases isNF_shape hx with rfl | hp | ⟨y, t, rfl⟩
  · rw [expList_zero]; exact isSL_zero
  · rw [expList_of_prin hp]
    exact (isSL_cons_iff x 0).mpr ⟨⟨hx, hdx⟩, isSL_zero, Or.inl rfl⟩
  · rw [expList_tcCons]
    exact ((isNF_isDom_tcCons_iff y t).mp ⟨hx, hdx⟩).1

private lemma prin_ne_zero {c : V} (h : kind c = 1 ∨ kind c = 2) : c ≠ 0 := by
  rintro rfl; rcases h with h | h <;> simp at h

/-- **The order of normal forms is the order of their exponent lists.** -/
lemma iltb_expList_iff {b c : V} (hb : isNF b) (hc : isNF c) :
    iltb (expList b) (expList c) = 1 ↔ iltb b c = 1 := by
  have h00 : iltb (0 : V) 0 ≠ 1 := not_iltb_zero_right 0
  rcases isNF_shape hb with rfl | hpb | ⟨x, s, rfl⟩ <;>
  rcases isNF_shape hc with rfl | hpc | ⟨y, t, rfl⟩
  · simp
  · rw [expList_zero, expList_of_prin hpc, iltb_zero_pos (tcCons_ne_zero _ _),
      iltb_zero_pos (prin_ne_zero hpc)]
  · simp
  · rw [expList_zero, expList_of_prin hpb, iltb_pos_zero (tcCons_ne_zero _ _),
      iltb_pos_zero (prin_ne_zero hpb)]
  · rw [expList_of_prin hpb, expList_of_prin hpc, iltb_cons_cons, bor_eq_one, band_eq_one]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact h
      · exact absurd h h00
    · intro h; exact Or.inl h
  · rw [expList_of_prin hpb, expList_tcCons, iltb_cons_cons, bor_eq_one, band_eq_one,
      beq_eq_one, iltb_prin_cons hpb, bor_eq_one, beq_eq_one]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | rfl)
      · exact Or.inl h
      · refine Or.inr ⟨rfl, iltb_zero_pos ?_⟩
        rintro rfl
        have := sok_of_isNF hc
        rw [sok_tcCons, if_pos ⟨rfl, hpb⟩] at this
        simp at this
  · simp
  · rw [expList_tcCons, expList_of_prin hpc, iltb_cons_cons, bor_eq_one, band_eq_one,
      iltb_cons_prin _ _ hpc]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact h
      · exact absurd h (not_iltb_zero_right s)
    · intro h; exact Or.inl h
  · rw [expList_tcCons, expList_tcCons]

end Model

end OrdinalAnalysis.IDn.Internal
