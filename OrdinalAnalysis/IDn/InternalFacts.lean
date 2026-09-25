/-
  `InternalOrderFacts` from the internal order of `IDn/Internal/Order.lean`, up to one field.

  The concrete formulas are `iltDef` (`iltb x y = 1`), `thNFDef` (`isNF`) and `thDomDef`
  (`isDom`) (`orderFormulas`); the descending lists are `IsSLW s :≡ nfA s = 1 ∧ sumK s = 1 ∧
  isDom s`, and list concatenation is `ID1/Internal/Arith.iapp` (the cons codes of `ID₁` and of
  the multi-level notation are the same numbers, `⟪2, ⟪x, s⟫⟫ + 1`).  Every field of
  `OrderAxioms` is proved from the recursion equations of `IDn/Internal/{Codes,Order}.lean`
  (by `IΣ₁`-induction where needed), **except transitivity of `iltb` on normal forms**, which is
  the one remaining hypothesis (`OrderTrans`).

  Headlines with the concrete theories and sentences (no `hJ` in the statements):

  * `idn_upper_bound_of_trans hT n hn : ∀ a ≺ c_n, IDn n (WForms orderFormulas n) ⊢ TI_a(≺, X)`;
  * `idlt_upper_bound_of_trans hT : ∀ a ≺ Ω₁, IDlt (WFormsOmega orderFormulas) ⊢ TI_a(≺, X)`.
-/
import OrdinalAnalysis.IDn.Theorem
import OrdinalAnalysis.IDn.Internal.Order
import OrdinalAnalysis.ID1.Internal.JumpList

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.IDn.Internal
open OrdinalAnalysis.ID1.Internal (bor band beq bor_eq_one band_eq_one beq_eq_one)

/-! ### The concrete formulas -/

/-- `iltb x y = 1`, slot `0` the smaller element. -/
def iltDef : 𝚺₁.Semisentence 2 := .mkSigma “x y. !iltbDef 1 x y”

/-- Descending lists of normal domain codes. -/
def slWDef : 𝚺₁.Semisentence 1 := .mkSigma “s. !nfADef 1 s ∧ !sumKDef 1 s ∧ !isDombDef 1 s”

/-- **The formulas of the internal order of `IDn/Internal/Order.lean`.** -/
def orderFormulas : OrderFormulas := ⟨iltDef, thNFDef, thDomDef⟩

section Model

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Definability of the tables of `IDn/Internal/Order.lean` -/

instance sumK_definable : 𝚺₁-Function₁ (sumK : V → V) := sumK_defined.to_definable
instance sumK_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (sumK : V → V) :=
  sumK_definable.of_sigmaOne
instance iltb_definable : 𝚺₁-Function₂ (iltb : V → V → V) := iltb_defined.to_definable
instance iltb_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (iltb : V → V → V) :=
  iltb_definable.of_sigmaOne
instance iall_definable : 𝚺₁-Function₃ (iall : V → V → V → V) := iall_defined.to_definable
instance iall_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₃ (iall : V → V → V → V) :=
  iall_definable.of_sigmaOne
instance iex_definable : 𝚺₁-Function₃ (iex : V → V → V → V) := iex_defined.to_definable
instance iex_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₃ (iex : V → V → V → V) :=
  iex_definable.of_sigmaOne
instance nfA_definable : 𝚺₁-Function₁ (nfA : V → V) := nfA_defined.to_definable
instance nfA_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (nfA : V → V) :=
  nfA_definable.of_sigmaOne
instance isNFb_definable : 𝚺₁-Function₁ (isNFb : V → V) := isNFb_defined.to_definable
instance isNFb_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (isNFb : V → V) :=
  isNFb_definable.of_sigmaOne
instance isDomb_definable : 𝚺₁-Function₁ (isDomb : V → V) := isDomb_defined.to_definable
instance isDomb_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (isDomb : V → V) :=
  isDomb_definable.of_sigmaOne
instance domOk_definable : 𝚺₁-Function₃ (domOk : V → V → V → V) := domOk_defined.to_definable
instance domOk_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₃ (domOk : V → V → V → V) :=
  domOk_definable.of_sigmaOne
instance isNF_definable (Γ) (m : ℕ) : Γ-[m + 1]-Predicate (isNF : V → Prop) := by
  unfold isNF; definability
instance isDom_definable (Γ) (m : ℕ) : Γ-[m + 1]-Predicate (isDom : V → Prop) := by
  unfold isDom; definability

/-- A descending list (sum code) of normal domain codes. -/
def IsSLW (s : V) : Prop := nfA s = 1 ∧ sumK s = 1 ∧ isDom s

instance isSLW_definable (Γ) (m : ℕ) : Γ-[m + 1]-Predicate (IsSLW : V → Prop) := by
  unfold IsSLW; definability

theorem eval_iltDef (x y : V) : iltDef.val.Evalb ![x, y] ↔ iltb x y = 1 := by
  simp [iltDef, iltb_defined.iff, eq_comm]

theorem eval_slWDef (s : V) : slWDef.val.Evalb ![s] ↔ IsSLW s := by
  simp [slWDef, IsSLW, nfA_defined.iff, sumK_defined.iff, isDom, isDomb_defined.iff, eq_comm]

/-! ### The order clauses -/

theorem not_iltb_zero' (x : V) : ¬ iltb x 0 = 1 := by
  rcases eq_or_ne x 0 with rfl | h
  · rw [iltb_zero_zero]; simp
  · rw [iltb_pos_zero h]; simp

theorem iltb_Omega_Omega_iff (i j : V) : iltb (tcOmega i) (tcOmega j) = 1 ↔ i < j := by
  rw [iltb_tcOmega_tcOmega]; split_ifs with h <;> simp [h]

theorem iltb_Omega_theta_iff (i j b : V) : iltb (tcOmega i) (tcTheta j b) = 1 ↔ i < j := by
  rw [iltb_tcOmega_tcTheta]; split_ifs with h <;> simp [h]

theorem iltb_theta_Omega_iff (i a j : V) : iltb (tcTheta i a) (tcOmega j) = 1 ↔ i ≤ j := by
  rw [iltb_tcTheta_tcOmega]; split_ifs with h <;> simp [h]

theorem iltb_cons_cons_iff (x s y t : V) :
    iltb (tcCons x s) (tcCons y t) = 1 ↔ iltb x y = 1 ∨ (x = y ∧ iltb s t = 1) := by
  rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one]

theorem iltb_cons_prin_iff (x s : V) {c : V} (hc : kind c = 1 ∨ kind c = 2) :
    iltb (tcCons x s) c = 1 ↔ iltb x c = 1 := by
  rw [iltb_cons_prin x s hc]

theorem iltb_prin_cons_iff {c : V} (hc : kind c = 1 ∨ kind c = 2) (y t : V) :
    iltb c (tcCons y t) = 1 ↔ iltb c y = 1 ∨ c = y := by
  rw [iltb_prin_cons hc, bor_eq_one, beq_eq_one]

/-- `iall k a x = 1` says that every member of `E_k(a)` is `≺ x`, for term codes `a`. -/
theorem iall_iff (k x : V) :
    ∀ a : V, isTermb a = 1 → (iall k a x = 1 ↔ ∀ g ≤ a, iinE k g a = 1 → iltb g x = 1) := by
  intro a
  induction a using ISigma1.pi1_order_induction
  · definability
  case ind a ih =>
    intro ht
    rcases kind_cases a with h | h | h | h | h
    · rw [iall_of_kind k (Or.inl h)]
      simp [fun g => iinE_eq_zero_of_kind (c := a) k g (by simp [h]) (by simp [h])]
    · rw [iall_of_kind k (Or.inr h)]
      simp [fun g => iinE_eq_zero_of_kind (c := a) k g (by simp [h]) (by simp [h])]
    · have ha0 : a ≠ 0 := by rintro rfl; simp at h
      have hlt := tcThetaArg_lt ha0
      rw [eq_tcTheta_of_kind h] at ht ⊢
      set j := tcLev a
      set a' := tcThetaArg a
      rw [isTermb_tcTheta] at ht
      by_cases hj : j ≤ k
      · rw [iall_tcTheta_of_le hj]
        constructor
        · intro h1 g _ hg
          rw [iinE_tcTheta_le_iff hj] at hg
          rw [hg]; exact h1
        · intro h1
          exact h1 _ le_rfl (iinE_tcTheta_self hj)
      · have hkj : k < j := not_le.mp hj
        rw [iall_tcTheta_of_lt hkj, ih a' hlt ht]
        constructor
        · intro h1 g _ hg
          rw [iinE_tcTheta_of_lt hkj] at hg
          exact h1 g (le_of_iinE hg) hg
        · intro h1 g _ hg
          exact h1 g (le_trans (le_of_iinE hg) (le_of_lt (arg_lt_tcTheta j a')))
            (by rw [iinE_tcTheta_of_lt hkj]; exact hg)
    · have ha0 : a ≠ 0 := by rintro rfl; simp at h
      rw [eq_tcCons_of_kind h] at ht ⊢
      rw [isTermb_tcCons, band_eq_one, band_eq_one] at ht
      rw [iall_cons, band_eq_one, ih _ (tcHd_lt ha0) ht.1, ih _ (tcTl_lt ha0) ht.2.1]
      constructor
      · rintro ⟨h1, h2⟩ g _ hg
        rcases (iinE_tcCons_iff _ _ _ _).mp hg with hg | hg
        · exact h1 g (le_of_iinE hg) hg
        · exact h2 g (le_of_iinE hg) hg
      · intro h1
        constructor
        · intro g _ hg
          have hg' : iinE k g (tcCons (tcHd a) (tcTl a)) = 1 :=
            (iinE_tcCons_iff _ _ _ _).mpr (Or.inl hg)
          exact h1 g (le_of_iinE hg') hg'
        · intro g _ hg
          have hg' : iinE k g (tcCons (tcHd a) (tcTl a)) = 1 :=
            (iinE_tcCons_iff _ _ _ _).mpr (Or.inr hg)
          exact h1 g (le_of_iinE hg') hg'
    · rw [isTermb_kind_four h] at ht; simp at ht

/-- `iex k x b = 1` says that `x ≼` some member of `E_k(b)`, for term codes `b`. -/
theorem iex_iff (k x : V) :
    ∀ b : V, isTermb b = 1 →
      (iex k x b = 1 ↔ ∃ g ≤ b, iinE k g b = 1 ∧ (iltb x g = 1 ∨ x = g)) := by
  intro b
  induction b using ISigma1.pi1_order_induction
  · definability
  case ind b ih =>
    intro ht
    rcases kind_cases b with h | h | h | h | h
    · rw [iex_of_kind k x (Or.inl h)]
      simp [fun g => iinE_eq_zero_of_kind (c := b) k g (by simp [h]) (by simp [h])]
    · rw [iex_of_kind k x (Or.inr h)]
      simp [fun g => iinE_eq_zero_of_kind (c := b) k g (by simp [h]) (by simp [h])]
    · have hb0 : b ≠ 0 := by rintro rfl; simp at h
      have hlt := tcThetaArg_lt hb0
      rw [eq_tcTheta_of_kind h] at ht ⊢
      set j := tcLev b
      set b' := tcThetaArg b
      rw [isTermb_tcTheta] at ht
      by_cases hj : j ≤ k
      · rw [iex_tcTheta_of_le hj, bor_eq_one, beq_eq_one]
        constructor
        · intro h1
          exact ⟨_, le_rfl, iinE_tcTheta_self hj, h1⟩
        · rintro ⟨g, -, hg, h1⟩
          rw [iinE_tcTheta_le_iff hj] at hg
          rwa [hg] at h1
      · have hkj : k < j := not_le.mp hj
        rw [iex_tcTheta_of_lt hkj, ih b' hlt ht]
        constructor
        · rintro ⟨g, _, hg, h1⟩
          exact ⟨g, le_trans (le_of_iinE hg) (le_of_lt (arg_lt_tcTheta j b')),
            by rw [iinE_tcTheta_of_lt hkj]; exact hg, h1⟩
        · rintro ⟨g, _, hg, h1⟩
          rw [iinE_tcTheta_of_lt hkj] at hg
          exact ⟨g, le_of_iinE hg, hg, h1⟩
    · have hb0 : b ≠ 0 := by rintro rfl; simp at h
      rw [eq_tcCons_of_kind h] at ht ⊢
      rw [isTermb_tcCons, band_eq_one, band_eq_one] at ht
      rw [iex_cons, bor_eq_one, ih _ (tcHd_lt hb0) ht.1, ih _ (tcTl_lt hb0) ht.2.1]
      constructor
      · rintro (⟨g, _, hg, h1⟩ | ⟨g, _, hg, h1⟩)
        · exact ⟨g, le_of_iinE ((iinE_tcCons_iff _ _ _ _).mpr (Or.inl hg)),
            (iinE_tcCons_iff _ _ _ _).mpr (Or.inl hg), h1⟩
        · exact ⟨g, le_of_iinE ((iinE_tcCons_iff _ _ _ _).mpr (Or.inr hg)),
            (iinE_tcCons_iff _ _ _ _).mpr (Or.inr hg), h1⟩
      · rintro ⟨g, _, hg, h1⟩
        rcases (iinE_tcCons_iff _ _ _ _).mp hg with hg | hg
        · exact Or.inl ⟨g, le_of_iinE hg, hg, h1⟩
        · exact Or.inr ⟨g, le_of_iinE hg, hg, h1⟩
    · rw [isTermb_kind_four h] at ht; simp at ht

/-! ### Normal forms and the domain condition -/

theorem isTermb_of_nfA : ∀ c : V, nfA c = 1 → isTermb c = 1 := by
  intro c
  induction c using ISigma1.pi1_order_induction
  · definability
  case ind c ih =>
    intro hc
    rcases kind_cases c with h | h | h | h | h
    · rw [kind_eq_zero_iff.mp h]; exact isTermb_zero
    · exact isTermb_kind_one h
    · have hc0 : c ≠ 0 := by rintro rfl; simp at h
      have hlt := tcThetaArg_lt hc0
      rw [eq_tcTheta_of_kind h] at hc ⊢
      rw [nfA_tcTheta, isNFb, band_eq_one] at hc
      rw [isTermb_tcTheta]
      exact ih _ hlt hc.1
    · have hc0 : c ≠ 0 := by rintro rfl; simp at h
      rw [eq_tcCons_of_kind h] at hc ⊢
      rw [nfA_tcCons, band_eq_one, band_eq_one, band_eq_one, isNFb, band_eq_one] at hc
      rw [isTermb_tcCons, band_eq_one, band_eq_one]
      exact ⟨ih _ (tcHd_lt hc0) hc.1.1, ih _ (tcTl_lt hc0) hc.2.1, hc.2.2.1⟩
    · rw [nfA_kind_four h] at hc; simp at hc

theorem nfA_of_isNF {c : V} (h : isNF c) : nfA c = 1 := (band_eq_one.mp h).1

theorem isNF_isTerm {c : V} (h : isNF c) : isTerm c := isTermb_of_nfA c (nfA_of_isNF h)

theorem isNF_tcTheta_iff (k a : V) : isNF (tcTheta k a) ↔ isNF a := by
  unfold isNF isNFb
  rw [nfA_tcTheta, sok_tcTheta, band_eq_one]
  exact and_iff_left rfl

theorem lt_of_iinG (k : V) : ∀ c : V, ∀ y, iinG k y c = 1 → y < c := by
  intro c
  induction c using ISigma1.pi1_order_induction
  · definability
  case ind c ih =>
    intro y hy
    rcases kind_cases c with h | h | h | h | h
    · rw [iinG_eq_zero_of_kind k y (by simp [h]) (by simp [h])] at hy; simp at hy
    · rw [iinG_eq_zero_of_kind k y (by simp [h]) (by simp [h])] at hy; simp at hy
    · have hc0 : c ≠ 0 := by rintro rfl; simp at h
      have hlt := tcThetaArg_lt hc0
      rw [eq_tcTheta_of_kind h] at hy
      by_cases hj : k < tcLev c
      · rcases (iinG_tcTheta_lt_iff hj).mp hy with rfl | hy
        · exact hlt
        · exact lt_trans (ih _ hlt y hy) hlt
      · rw [iinG_tcTheta_of_le (not_lt.mp hj)] at hy; simp at hy
    · have hc0 : c ≠ 0 := by rintro rfl; simp at h
      rw [eq_tcCons_of_kind h, iinG_tcCons_iff] at hy
      rcases hy with hy | hy
      · exact lt_trans (ih _ (tcHd_lt hc0) y hy) (tcHd_lt hc0)
      · exact lt_trans (ih _ (tcTl_lt hc0) y hy) (tcTl_lt hc0)
    · rw [iinG_eq_zero_of_kind k y (by simp [h]) (by simp [h])] at hy; simp at hy

theorem domOk_iff (bound k : V) :
    ∀ c : V, domOk bound k c = 1 ↔ ∀ y < c, iinG k y c = 1 → iltb y bound = 1 := by
  intro c
  induction c using ISigma1.pi1_order_induction
  · definability
  case ind c ih =>
    rcases kind_cases c with h | h | h | h | h
    · rw [domOk_of_kind bound k (Or.inl h)]
      simp [fun y => iinG_eq_zero_of_kind (c := c) k y (by simp [h]) (by simp [h])]
    · rw [domOk_of_kind bound k (Or.inr h)]
      simp [fun y => iinG_eq_zero_of_kind (c := c) k y (by simp [h]) (by simp [h])]
    · have hc0 : c ≠ 0 := by rintro rfl; simp at h
      have hlt := tcThetaArg_lt hc0
      rw [eq_tcTheta_of_kind h]
      rw [eq_tcTheta_of_kind h] at hlt
      set j := tcLev c
      set a := tcThetaArg c
      by_cases hj : k < j
      · rw [domOk_tcTheta_of_lt hj, band_eq_one, ih a (tcThetaArg_lt hc0)]
        constructor
        · rintro ⟨h1, h2⟩ y _ hy
          rcases (iinG_tcTheta_lt_iff hj).mp hy with rfl | hy
          · exact h1
          · exact h2 y (lt_of_iinG k a y hy) hy
        · intro h1
          refine ⟨h1 a (arg_lt_tcTheta j a) ((iinG_tcTheta_lt_iff hj).mpr (Or.inl rfl)),
            fun y _ hy => ?_⟩
          exact h1 y (lt_trans (lt_of_iinG k a y hy) (arg_lt_tcTheta j a))
            ((iinG_tcTheta_lt_iff hj).mpr (Or.inr hy))
      · rw [domOk_tcTheta_of_le (not_lt.mp hj)]
        simp [iinG_tcTheta_of_le (not_lt.mp hj)]
    · have hc0 : c ≠ 0 := by rintro rfl; simp at h
      rw [eq_tcCons_of_kind h, domOk_tcCons, band_eq_one, ih _ (tcHd_lt hc0),
        ih _ (tcTl_lt hc0)]
      constructor
      · rintro ⟨h1, h2⟩ y _ hy
        rcases (iinG_tcCons_iff _ _ _ _).mp hy with hy | hy
        · exact h1 y (lt_of_iinG k _ y hy) hy
        · exact h2 y (lt_of_iinG k _ y hy) hy
      · intro h1
        refine ⟨fun y _ hy => h1 y ?_ ?_, fun y _ hy => h1 y ?_ ?_⟩
        · exact lt_of_iinG k _ y ((iinG_tcCons_iff _ _ _ _).mpr (Or.inl hy))
        · exact (iinG_tcCons_iff _ _ _ _).mpr (Or.inl hy)
        · exact lt_of_iinG k _ y ((iinG_tcCons_iff _ _ _ _).mpr (Or.inr hy))
        · exact (iinG_tcCons_iff _ _ _ _).mpr (Or.inr hy)
    · have hc0 : c ≠ 0 := by rintro rfl; simp at h
      have hd : domOk bound k c = 1 := by
        obtain ⟨S, h', -⟩ := domOk_unfold bound k c
        rw [h', domOkStep]
        simp only [pi₁_pair, pi₂_pair]
        simp [h]
      simp [hd, fun y => iinG_eq_zero_of_kind (c := c) k y (by simp [h]) (by simp [h])]

theorem isDom_tcTheta_iff (k a : V) :
    isDom (tcTheta k a) ↔ isDom a ∧ ∀ y, iinG k y a = 1 → iltb y a = 1 := by
  unfold isDom
  rw [isDomb_tcTheta, band_eq_one, domOk_iff]
  exact and_congr Iff.rfl ⟨fun h y hy => h y (lt_of_iinG k a y hy) hy, fun h y _ hy => h y hy⟩

/-- **The clause for two collapses**, for normal arguments. -/
theorem iltb_theta_theta_iff' (i a j b : V) (ha : isNF a) (hb : isNF b) :
    iltb (tcTheta i a) (tcTheta j b) = 1 ↔
      i < j ∨ (i = j ∧ ((iltb a b = 1 ∧ ∀ g, iinE i g a = 1 → iltb g (tcTheta j b) = 1) ∨
        ∃ g, iinE i g b = 1 ∧ (iltb (tcTheta i a) g = 1 ∨ tcTheta i a = g))) := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [iltb_tcTheta_tcTheta_of_lt h]; simp [h]
  · rw [iltb_tcTheta_tcTheta_eq, bor_eq_one, band_eq_one, iall_iff i _ a (isNF_isTerm ha),
      iex_iff i _ b (isNF_isTerm hb)]
    simp only [_root_.lt_irrefl, false_or, true_and]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨g, _, hg, h3⟩)
      · exact Or.inl ⟨h1, fun g hg => h2 g (le_of_iinE hg) hg⟩
      · exact Or.inr ⟨g, hg, h3⟩
    · rintro (⟨h1, h2⟩ | ⟨g, hg, h3⟩)
      · exact Or.inl ⟨h1, fun g _ hg => h2 g hg⟩
      · exact Or.inr ⟨g, le_of_iinE hg, hg, h3⟩
  · rw [iltb_tcTheta_tcTheta_of_gt h]
    simp [not_lt.mpr (le_of_lt h), ne_of_gt h]

/-- The coefficients of a normal domain code are normal domain codes. -/
theorem fld_of_iinE' (k : V) :
    ∀ c : V, nfA c = 1 → isDom c → ∀ g ≤ c, iinE k g c = 1 → isNF g ∧ isDom g := by
  intro c
  induction c using ISigma1.pi1_order_induction
  · definability
  case ind c ih =>
    intro hn hd g _ hg
    rcases kind_cases c with h | h | h | h | h
    · rw [iinE_eq_zero_of_kind k g (by simp [h]) (by simp [h])] at hg; simp at hg
    · rw [iinE_eq_zero_of_kind k g (by simp [h]) (by simp [h])] at hg; simp at hg
    · have hc0 : c ≠ 0 := by rintro rfl; simp at h
      have hlt := tcThetaArg_lt hc0
      have e := eq_tcTheta_of_kind h
      by_cases hj : tcLev c ≤ k
      · rw [e, iinE_tcTheta_le_iff hj] at hg
        rw [hg, ← e]
        refine ⟨?_, hd⟩
        unfold isNF isNFb
        rw [hn, band_eq_one, e, sok_tcTheta]
        exact ⟨rfl, rfl⟩
      · rw [e, iinE_tcTheta_of_lt (not_le.mp hj)] at hg
        rw [e, nfA_tcTheta, isNFb, band_eq_one] at hn
        rw [e, isDom, isDomb_tcTheta, band_eq_one] at hd
        exact ih _ hlt hn.1 hd.1 g (le_of_iinE hg) hg
    · have hc0 : c ≠ 0 := by rintro rfl; simp at h
      rw [eq_tcCons_of_kind h] at hn hd hg
      rw [nfA_tcCons, band_eq_one, band_eq_one, isNFb, band_eq_one] at hn
      rw [isDom, isDomb_tcCons, band_eq_one] at hd
      rcases (iinE_tcCons_iff _ _ _ _).mp hg with hg | hg
      · exact ih _ (tcHd_lt hc0) hn.1.1 hd.1 g (le_of_iinE hg) hg
      · exact ih _ (tcTl_lt hc0) hn.2.1 hd.2 g (le_of_iinE hg) hg
    · rw [nfA_kind_four h] at hn; simp at hn

/-- The collapse arguments of a normal domain code are normal domain codes. -/
theorem fld_of_iinG' (k : V) :
    ∀ c : V, nfA c = 1 → isDom c → ∀ y < c, iinG k y c = 1 → isNF y ∧ isDom y := by
  intro c
  induction c using ISigma1.pi1_order_induction
  · definability
  case ind c ih =>
    intro hn hd y _ hy
    rcases kind_cases c with h | h | h | h | h
    · rw [iinG_eq_zero_of_kind k y (by simp [h]) (by simp [h])] at hy; simp at hy
    · rw [iinG_eq_zero_of_kind k y (by simp [h]) (by simp [h])] at hy; simp at hy
    · have hc0 : c ≠ 0 := by rintro rfl; simp at h
      have hlt := tcThetaArg_lt hc0
      have e := eq_tcTheta_of_kind h
      rw [e] at hy hn hd
      rw [nfA_tcTheta] at hn
      rw [isDom, isDomb_tcTheta, band_eq_one] at hd
      by_cases hj : k < tcLev c
      · rcases (iinG_tcTheta_lt_iff hj).mp hy with rfl | hy
        · exact ⟨hn, hd.1⟩
        · exact ih _ hlt (band_eq_one.mp hn).1 hd.1 y (lt_of_iinG k _ y hy) hy
      · rw [iinG_tcTheta_of_le (not_lt.mp hj)] at hy; simp at hy
    · have hc0 : c ≠ 0 := by rintro rfl; simp at h
      rw [eq_tcCons_of_kind h] at hn hd hy
      rw [nfA_tcCons, band_eq_one, band_eq_one, isNFb, band_eq_one] at hn
      rw [isDom, isDomb_tcCons, band_eq_one] at hd
      rcases (iinG_tcCons_iff _ _ _ _).mp hy with hy | hy
      · exact ih _ (tcHd_lt hc0) hn.1.1 hd.1 y (lt_of_iinG k _ y hy) hy
      · exact ih _ (tcTl_lt hc0) hn.2.1 hd.2 y (lt_of_iinG k _ y hy) hy
    · rw [nfA_kind_four h] at hn; simp at hn

/-! ### Descending lists -/

theorem isSLW_zero : IsSLW (0 : V) := ⟨nfA_zero, sumK_zero, isDomb_zero⟩

theorem isSLW_shape {s : V} (h : IsSLW s) : s = 0 ∨ kind s = 3 := by
  have := h.2.1
  unfold sumK at this
  split_ifs at this with h'
  · rcases h' with h' | h'
    · exact Or.inl (kind_eq_zero_iff.mp h')
    · exact Or.inr h'
  · simp at this

theorem isSLW_cons_iff (x w : V) :
    IsSLW (tcCons x w) ↔
      (isNF x ∧ isDom x) ∧ IsSLW w ∧ (w = 0 ∨ iltb (tcHd w) x = 1 ∨ tcHd w = x) := by
  simp only [IsSLW, isNF, isDom, nfA_tcCons, sumK_tcCons, isDomb_tcCons, band_eq_one]
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · by_cases hs : sumK w = 1
    · have hk : kind w = 3 := by
        unfold sumK at hs
        split_ifs at hs with h'
        · rcases h' with h' | h'
          · exact absurd (kind_eq_zero_iff.mp h') hw
          · exact h'
        · simp at hs
      obtain ⟨y, t, rfl⟩ : ∃ y t, w = tcCons y t := ⟨_, _, eq_tcCons_of_kind hk⟩
      simp only [descOk_tcCons_tcCons, bor_eq_one, beq_eq_one, tcHd_tcCons]
      have hne := tcCons_ne_zero y t
      tauto
    · constructor
      · intro h; exact absurd h.1.2.2.1 hs
      · intro h; exact absurd h.2.1.2.1 hs

theorem fld_cons_iff' (x w : V) :
    (isNF (tcCons x w) ∧ isDom (tcCons x w)) ↔
      IsSLW (tcCons x w) ∧ ¬ (w = 0 ∧ (kind x = 1 ∨ kind x = 2)) := by
  unfold IsSLW isNF isNFb
  rw [sok_tcCons, sumK_tcCons, band_eq_one]
  by_cases h : w = 0 ∧ (kind x = 1 ∨ kind x = 2)
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

/-! ### Concatenation (`ID1/Internal/Arith.iapp`) -/

/-- Concatenation of sum codes. -/
noncomputable abbrev appW (s t : V) : V := ID1.Internal.iapp s t

theorem appW_of_kind {s : V} (hs : kind s ≠ 3) (t : V) : appW s t = t :=
  ID1.Internal.iapp_of_kind hs t

theorem appW_cons (x s t : V) : appW (tcCons x s) t = tcCons x (appW s t) :=
  ID1.Internal.iapp_cons x s t

theorem appW_zero (t : V) : appW 0 t = t := ID1.Internal.iapp_zero_left t

theorem appW_isnoc (s y w : V) : appW (appW s (tcCons y 0)) w = appW s (tcCons y w) :=
  ID1.Internal.iapp_isnoc y w s

theorem le_appW_right (s t : V) : t ≤ appW s t := ID1.Internal.le_iapp_right t s

theorem tcHd_appW_cons (s z w w' : V) :
    tcHd (appW s (tcCons z w)) = tcHd (appW s (tcCons z w')) :=
  ID1.Internal.tcHd_iapp_cons s z w w'

theorem iinE_appW_right (k g r : V) : ∀ s : V, iinE k g r = 1 → iinE k g (appW s r) = 1 := by
  intro s
  induction s using ISigma1.pi1_order_induction
  · definability
  case ind s ih =>
    intro hg
    by_cases hk : kind s = 3
    · have hs0 : s ≠ 0 := by rintro rfl; simp at hk
      rw [eq_tcCons_of_kind hk, appW_cons, iinE_tcCons_iff]
      exact Or.inr (ih _ (tcTl_lt hs0) hg)
    · rw [appW_of_kind hk]; exact hg

theorem isSLW_of_appW_right (r : V) : ∀ s : V, IsSLW (appW s r) → IsSLW r := by
  intro s
  induction s using ISigma1.pi1_order_induction
  · definability
  case ind s ih =>
    intro h
    by_cases hk : kind s = 3
    · have hs0 : s ≠ 0 := by rintro rfl; simp at hk
      rw [eq_tcCons_of_kind hk, appW_cons, isSLW_cons_iff] at h
      exact ih _ (tcTl_lt hs0) h.2.1
    · rwa [appW_of_kind hk] at h

theorem isSLW_isnoc_of_appW (z w : V) :
    ∀ s : V, IsSLW (appW s (tcCons z w)) → IsSLW (appW s (tcCons z 0)) := by
  intro s
  induction s using ISigma1.pi1_order_induction
  · definability
  case ind s ih =>
    intro h
    by_cases hk : kind s = 3
    · have hs0 : s ≠ 0 := by rintro rfl; simp at hk
      rw [eq_tcCons_of_kind hk, appW_cons, isSLW_cons_iff] at h ⊢
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨h1, ih _ (tcTl_lt hs0) h2, Or.inr ?_⟩
      have hne : appW (tcTl s) (tcCons z w) ≠ 0 := fun e =>
        tcCons_ne_zero z w (nonpos_iff_eq_zero.mp (e ▸ le_appW_right (tcTl s) (tcCons z w)))
      rw [tcHd_appW_cons (tcTl s) z 0 w]
      exact h3.resolve_left hne
    · rw [appW_of_kind hk] at h ⊢
      exact (isSLW_cons_iff z 0).mpr ⟨((isSLW_cons_iff z w).mp h).1, isSLW_zero, Or.inl rfl⟩

/-- **Below `η ++ ⟨y⟩`** (`ID1/Internal/JumpList.iltb_isnoc_cases`). -/
theorem iltb_isnoc_cases' (y : V) :
    ∀ s : V, IsSLW s → ∀ z, IsSLW z → iltb z (appW s (tcCons y 0)) = 1 →
      iltb z s = 1 ∨ z = s ∨ ∃ r ≤ z, z = appW s r ∧ r ≠ 0 ∧ iltb (tcHd r) y = 1 := by
  intro s
  induction s using ISigma1.pi1_order_induction
  · definability
  case ind s ih =>
    intro hs z hz h
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [appW_zero] at h
      rcases eq_or_ne z 0 with rfl | hz0
      · exact Or.inr (Or.inl rfl)
      obtain ⟨c, r', rfl⟩ : ∃ c r', z = tcCons c r' :=
        ⟨_, _, eq_tcCons_of_kind ((isSLW_shape hz).resolve_left hz0)⟩
      rw [iltb_cons_cons_iff] at h
      rcases h with h | ⟨-, h⟩
      · exact Or.inr (Or.inr ⟨tcCons c r', le_rfl, by rw [appW_zero], tcCons_ne_zero _ _,
          by rw [tcHd_tcCons]; exact h⟩)
      · exact absurd h (not_iltb_zero' r')
    obtain ⟨a, s', rfl⟩ : ∃ a s', s = tcCons a s' :=
      ⟨_, _, eq_tcCons_of_kind ((isSLW_shape hs).resolve_left hs0)⟩
    have hs' : IsSLW s' := ((isSLW_cons_iff a s').mp hs).2.1
    rw [appW_cons] at h
    rcases eq_or_ne z 0 with rfl | hz0
    · exact Or.inl (iltb_zero_pos (tcCons_ne_zero a s'))
    obtain ⟨c, r', rfl⟩ : ∃ c r', z = tcCons c r' :=
      ⟨_, _, eq_tcCons_of_kind ((isSLW_shape hz).resolve_left hz0)⟩
    have hr' : IsSLW r' := ((isSLW_cons_iff c r').mp hz).2.1
    rw [iltb_cons_cons_iff] at h
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl ((iltb_cons_cons_iff _ _ _ _).mpr (Or.inl h))
    · rcases ih s' (tl_lt_tcCons c s') hs' r' hr' h with h' | rfl | ⟨r, hr, rfl, hr0, hry⟩
      · exact Or.inl ((iltb_cons_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, h'⟩))
      · exact Or.inr (Or.inl rfl)
      · refine Or.inr (Or.inr ⟨r, le_trans hr (le_of_lt (tl_lt_tcCons _ _)), ?_, hr0, hry⟩)
        rw [appW_cons]

/-- **The order of normal codes is the order of their exponent lists.** -/
theorem iltb_itoL_iff' {b c : V} (hb : isNF b) (hc : isNF c) :
    iltb (Upper.itoL b) (Upper.itoL c) = 1 ↔ iltb b c = 1 := by
  have hbt := isNF_isTerm hb
  have hct := isNF_isTerm hc
  have shape : ∀ {x : V}, isNF x → x = 0 ∨ (kind x = 1 ∨ kind x = 2) ∨ kind x = 3 := by
    intro x hx
    rcases kind_cases x with h | h | h | h | h
    · exact Or.inl (kind_eq_zero_iff.mp h)
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inr h)
    · have := isNF_isTerm hx
      unfold isTerm at this
      rw [isTermb_kind_four h] at this; simp at this
  rcases shape hb with rfl | hbp | hbc <;> rcases shape hc with rfl | hcp | hcc
  · simp [not_iltb_zero']
  · rw [itoL_zero, itoL_of_prin hcp]
    have hc0 : c ≠ 0 := by rintro rfl; simp at hcp
    rw [iltb_zero_pos (tcCons_ne_zero _ _), iltb_zero_pos hc0]
  · rw [itoL_zero, itoL_of_not_prin (by rw [hcc]; simp)]
  · rw [itoL_zero]; simp [not_iltb_zero']
  · rw [itoL_of_prin hbp, itoL_of_prin hcp, iltb_cons_cons_iff]
    simp [not_iltb_zero']
  · have hcn : ¬ (kind c = 1 ∨ kind c = 2) := by rw [hcc]; simp
    rw [itoL_of_prin hbp, itoL_of_not_prin hcn]
    obtain ⟨z', w', rfl⟩ : ∃ z' w', c = tcCons z' w' := ⟨_, _, eq_tcCons_of_kind hcc⟩
    rw [iltb_cons_cons_iff, iltb_prin_cons_iff hbp]
    have hsok : ¬ (w' = 0 ∧ (kind z' = 1 ∨ kind z' = 2)) := by
      intro h
      have := hc
      unfold isNF isNFb at this
      rw [sok_tcCons, if_pos h, band_eq_one] at this
      simp at this
    constructor
    · rintro (h | ⟨rfl, _⟩)
      · exact Or.inl h
      · exact Or.inr rfl
    · rintro (h | rfl)
      · exact Or.inl h
      · refine Or.inr ⟨rfl, iltb_zero_pos fun hw => hsok ⟨hw, hbp⟩⟩
  · rw [itoL_zero]; simp [not_iltb_zero']
  · have hbn : ¬ (kind b = 1 ∨ kind b = 2) := by rw [hbc]; simp
    rw [itoL_of_not_prin hbn, itoL_of_prin hcp]
    obtain ⟨z, w, rfl⟩ : ∃ z w, b = tcCons z w := ⟨_, _, eq_tcCons_of_kind hbc⟩
    rw [iltb_cons_cons_iff, iltb_cons_prin_iff z w hcp]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact h
      · exact absurd h (not_iltb_zero' w)
    · intro h; exact Or.inl h
  · rw [itoL_of_not_prin (by rw [hbc]; simp), itoL_of_not_prin (by rw [hcc]; simp)]

end Model

/-! ### The remaining hypothesis, and the instance -/

/-- **The one field not yet discharged**: transitivity of the internal order on normal
forms, in every model of `IΣ₁`. -/
def OrderTrans : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a b c : V),
    isNF a → isNF b → isNF c → iltb a b = 1 → iltb b c = 1 → iltb a c = 1

/-- **`InternalOrderFacts` from `IDn/Internal/Order.lean` and transitivity.** -/
noncomputable def InternalOrderFacts.ofTrans (hT : OrderTrans) : InternalOrderFacts where
  toOrderFormulas := orderFormulas
  slDef := slWDef
  app := fun {V} _ _ => appW (V := V)
  appDef := ID1.Internal.iappDef
  app_defined := ID1.Internal.iapp_defined
  axioms := fun V _ _ => by
    have elt : ∀ x y : V, iltDef.val.Evalb ![x, y] ↔ iltb x y = 1 := eval_iltDef
    have enf : ∀ x : V, thNFDef.val.Evalb ![x] ↔ isNF x := eval_thNFDef
    have edom : ∀ x : V, thDomDef.val.Evalb ![x] ↔ isDom x := eval_thDomDef
    have esl : ∀ x : V, slWDef.val.Evalb ![x] ↔ IsSLW x := eval_slWDef
    show OrderAxioms V (fun x y => iltDef.val.Evalb ![x, y]) (fun x => thNFDef.val.Evalb ![x])
      (fun x => thDomDef.val.Evalb ![x]) (fun x => slWDef.val.Evalb ![x]) appW
    simp only [elt, enf, edom, esl]
    exact {
      lt_mc := iltb_mc
      nf_mc := isNF_mc
      dom_mc := isDom_mc
      lt_trans := fun ha hb hc hab hbc => hT V _ _ _ ha hb hc hab hbc
      not_lt_zero := not_iltb_zero'
      lt_Omega_Omega := iltb_Omega_Omega_iff
      lt_Omega_theta := iltb_Omega_theta_iff
      lt_theta_Omega := iltb_theta_Omega_iff
      lt_theta_theta := fun i a j b ha hb => iltb_theta_theta_iff' i a j b ha hb
      lt_cons_Omega := fun x s j => iltb_cons_prin_iff x s (by simp)
      lt_cons_theta := fun x s j b => iltb_cons_prin_iff x s (by simp)
      lt_Omega_cons := fun i y t => iltb_prin_cons_iff (by simp) y t
      lt_theta_cons := fun i a y t => iltb_prin_cons_iff (by simp) y t
      lt_cons_cons := iltb_cons_cons_iff
      nf_isTerm := fun _ h => isNF_isTerm h
      nf_theta := isNF_tcTheta_iff
      dom_theta := fun k a _ => isDom_tcTheta_iff k a
      fld_cons := fld_cons_iff'
      fld_of_iinE := fun k g c hn hd hg =>
        fld_of_iinE' k c (nfA_of_isNF hn) hd g (le_of_iinE hg) hg
      fld_of_iinG := fun k y c hn hd hy =>
        fld_of_iinG' k c (nfA_of_isNF hn) hd y (lt_of_iinG k c y hy) hy
      sl_zero := isSLW_zero
      sl_cons := isSLW_cons_iff
      sl_shape := fun _ h => isSLW_shape h
      app_zero := appW_zero
      app_isnoc := fun s y w _ => appW_isnoc s y w
      sl_isnoc_of_app := fun s z w h => isSLW_isnoc_of_appW z w s h
      sl_app_right := fun s r h => isSLW_of_appW_right r s h
      iinE_app_right := fun k g s r _ h => iinE_appW_right k g r s h
      lt_isnoc_cases := fun s y z hs hz h => by
        rcases iltb_isnoc_cases' y s hs z hz h with h | h | ⟨r, -, h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨r, h⟩)
      lt_itoL_iff := fun b c hb _ hc _ => iltb_itoL_iff' hb hc }

/-! ### Slot check: the order of the sentences is the notation order -/

/-- **Slot check**: in `ℕ`, the order `≺` of the forms and of `TI_a(≺, X)` holds between the
codes of two terms exactly when both are normal domain terms and the first is below the second
in `ThetaWTerm`'s order (slot `0` the smaller element). -/
theorem slotCheck_precW (a b : ThetaWTerm) :
    Semiformula.Evalb (M := ℕ) ![code a, code b] (OrderFormulas.precW orderFormulas) ↔
      (ThetaWTerm.NF a ∧ ThetaWTerm.Dom a) ∧ (ThetaWTerm.NF b ∧ ThetaWTerm.Dom b) ∧ a < b := by
  show orderFormulas.precWDef.val.Evalb ![code a, code b] ↔ _
  rw [OrderFormulas.eval_precWDef]
  show (thNFDef.val.Evalb ![code a] ∧ thDomDef.val.Evalb ![code a]) ∧
    (thNFDef.val.Evalb ![code b] ∧ thDomDef.val.Evalb ![code b]) ∧
      iltDef.val.Evalb ![code a, code b] ↔ _
  rw [eval_thNFDef, eval_thNFDef, eval_thDomDef, eval_thDomDef, eval_iltDef, standard_nf_iff,
    standard_nf_iff, standard_dom_iff, standard_dom_iff, standard_lt_iff]

/-! ### The headlines for the concrete order -/

/-- **The upper bound of `ID_n`** for the internal order of `IDn/Internal/Order.lean`, given
transitivity of that order. -/
theorem idn_upper_bound_of_trans (hT : OrderTrans) (n : ℕ) (hn : 0 < n) :
    ∀ a : ThetaWNoteD, a < ThetaWNoteD.c n →
      IDn n (WForms orderFormulas n) ⊢ tiUptoSentence orderFormulas (Fin n) a :=
  idn_upper_bound (InternalOrderFacts.ofTrans hT) n hn

/-- **The upper bound of `ID_{<ω}`** for the internal order of `IDn/Internal/Order.lean`, given
transitivity of that order. -/
theorem idlt_upper_bound_of_trans (hT : OrderTrans) :
    ∀ a : ThetaWNoteD, a.1 < ThetaWTerm.Omega 0 →
      IDlt (WFormsOmega orderFormulas) ⊢ tiUptoSentence orderFormulas ℕ a :=
  idlt_upper_bound (InternalOrderFacts.ofTrans hT)

/-- The theories of the headlines are consistent (no hypothesis). -/
theorem idn_orderFormulas_consistent (n : ℕ) :
    IDn n (WForms orderFormulas n) ⊬ (⊥ : Sentence (LXIn n)) :=
  idn_wForms_consistent orderFormulas n

theorem idlt_orderFormulas_consistent :
    IDlt (WFormsOmega orderFormulas) ⊬ (⊥ : Sentence LXIomega) :=
  idlt_wForms_consistent orderFormulas

end OrdinalAnalysis.IDn.Upper
