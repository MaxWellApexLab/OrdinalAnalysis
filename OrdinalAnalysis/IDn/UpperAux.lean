/-
  The internal order of the multi-level ϑ-notation as a hypothesis: `InternalOrderFacts`.

  The upper bound of `IDn/UpperBound.lean` needs, inside every model of `IΣ₁`, the internal
  order `≺` of the codes of `IDn/Internal/Codes.lean`, the normal-form and domain predicates
  (`NF`, Wilken's `Dom`), the descending exponent lists and their concatenation, together with
  the handful of internal facts about them that the well-ordering proof uses (the list is that
  of `ID1/WellOrdering.lean`'s uses of `ID1/Internal/{Order,OrderE,Arith*,JumpList}`, with
  levels).  These are not built yet (`IDn/Internal/Order*.lean` is in progress); here they are
  a hypothesis.

  * `OrderAxioms V lt nf dom sl app`: the facts, for given predicates on a model `V` of `IΣ₁`.
    Every field is the internal form of a statement proved about `ThetaWTerm` in
    `Ordinal/ThetaW/*` (order clauses of `ltb`, `NF`, `Dom`, `E_k`, `G_k`), or of an
    `ID1/Internal` lemma (lists, concatenation) with levels added.
  * `InternalOrderFacts`: `Σ₁` formulas for `≺`, `NF`, `Dom`, the descending lists, a `Σ₁`
    concatenation function, and `OrderAxioms` in every model of `IΣ₁` for the predicates they
    define.  The standard-model agreement is part of `OrderAxioms` (`lt_mc`, `nf_mc`, `dom_mc`:
    on standard codes, in every model, in particular in `ℕ`).

  Derived here: the definability instances, the field `fld = nf ∧ dom`, the shapes of normal
  codes (`nf_cases`), exponent lists of normal codes (`sl_itoL`), and the two small order
  lemmas below `⟨β⟩` and below `Ω_{i+1} + 1` (`lt_single_cases`, `lt_Omega_succ_cases`).
-/
import OrdinalAnalysis.IDn.UpperAuxCodes
import OrdinalAnalysis.Ordinal.ThetaW.Dom

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.IDn.Internal

/-- **The internal facts about the order used by the well-ordering proof**, for predicates
`lt` (`x ≺ y`), `nf` (normal form), `dom` (Wilken's domain condition), `sl` (a descending
list, coded as a sum, of normal domain codes) and a concatenation `app` of sum codes, on a
model `V` of `IΣ₁`. -/
structure OrderAxioms (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (lt : V → V → Prop) (nf dom sl : V → Prop) (app : V → V → V) : Prop where
  /-- On standard codes `≺` is the order of `ThetaWTerm`. -/
  lt_mc : ∀ a b : ThetaWTerm, lt (mc a) (mc b) ↔ a < b
  /-- On standard codes `nf` is `NF`. -/
  nf_mc : ∀ a : ThetaWTerm, nf (mc a) ↔ ThetaWTerm.NF a
  /-- On standard codes `dom` is `Dom`. -/
  dom_mc : ∀ a : ThetaWTerm, dom (mc a) ↔ ThetaWTerm.Dom a
  /-- Transitivity on normal codes. -/
  lt_trans : ∀ {a b c : V}, nf a → nf b → nf c → lt a b → lt b c → lt a c
  not_lt_zero : ∀ x : V, ¬ lt x 0
  lt_Omega_Omega : ∀ i j : V, lt (tcOmega i) (tcOmega j) ↔ i < j
  lt_Omega_theta : ∀ i j b : V, lt (tcOmega i) (tcTheta j b) ↔ i < j
  lt_theta_Omega : ∀ i a j : V, lt (tcTheta i a) (tcOmega j) ↔ i ≤ j
  /-- The clause of `ThetaWTerm.ltb` for two collapses (of normal arguments). -/
  lt_theta_theta : ∀ i a j b : V, nf a → nf b → (lt (tcTheta i a) (tcTheta j b) ↔
    i < j ∨ (i = j ∧ ((lt a b ∧ ∀ g, iinE i g a = 1 → lt g (tcTheta j b)) ∨
      ∃ g, iinE i g b = 1 ∧ (lt (tcTheta i a) g ∨ tcTheta i a = g))))
  lt_cons_Omega : ∀ x s j : V, lt (tcCons x s) (tcOmega j) ↔ lt x (tcOmega j)
  lt_cons_theta : ∀ x s j b : V, lt (tcCons x s) (tcTheta j b) ↔ lt x (tcTheta j b)
  lt_Omega_cons : ∀ i y t : V, lt (tcOmega i) (tcCons y t) ↔ lt (tcOmega i) y ∨ tcOmega i = y
  lt_theta_cons : ∀ i a y t : V,
    lt (tcTheta i a) (tcCons y t) ↔ lt (tcTheta i a) y ∨ tcTheta i a = y
  lt_cons_cons : ∀ x s y t : V, lt (tcCons x s) (tcCons y t) ↔ lt x y ∨ (x = y ∧ lt s t)
  nf_isTerm : ∀ x : V, nf x → isTerm x
  nf_theta : ∀ k a : V, nf (tcTheta k a) ↔ nf a
  /-- Wilken's domain condition at a collapse of a normal argument: `G_k(α) ≺* α`. -/
  dom_theta : ∀ k a : V, nf a → (dom (tcTheta k a) ↔ dom a ∧ ∀ y, iinG k y a = 1 → lt y a)
  /-- A sum is a normal domain code iff it is a descending list that is not a one-entry list
  with a principal entry. -/
  fld_cons : ∀ x w : V,
    (nf (tcCons x w) ∧ dom (tcCons x w)) ↔ sl (tcCons x w) ∧ ¬ (w = 0 ∧ (kind x = 1 ∨ kind x = 2))
  fld_of_iinE : ∀ k g c : V, nf c → dom c → iinE k g c = 1 → nf g ∧ dom g
  fld_of_iinG : ∀ k y c : V, nf c → dom c → iinG k y c = 1 → nf y ∧ dom y
  sl_zero : sl 0
  sl_cons : ∀ x w : V,
    sl (tcCons x w) ↔ (nf x ∧ dom x) ∧ sl w ∧ (w = 0 ∨ lt (tcHd w) x ∨ tcHd w = x)
  sl_shape : ∀ s : V, sl s → s = 0 ∨ kind s = 3
  app_zero : ∀ t : V, app 0 t = t
  /-- `(s ++ ⟨y⟩) ++ w = s ++ (y :: w)`. -/
  app_isnoc : ∀ s y w : V, sl s → app (app s (tcCons y 0)) w = app s (tcCons y w)
  sl_isnoc_of_app : ∀ s z w : V, sl (app s (tcCons z w)) → sl (app s (tcCons z 0))
  sl_app_right : ∀ s r : V, sl (app s r) → sl r
  iinE_app_right : ∀ k g s r : V, sl s → iinE k g r = 1 → iinE k g (app s r) = 1
  /-- **Below `η ++ ⟨y⟩`** (`ID1/Internal/JumpList.iltb_isnoc_cases`). -/
  lt_isnoc_cases : ∀ s y z : V, sl s → sl z → lt z (app s (tcCons y 0)) →
    lt z s ∨ z = s ∨ ∃ r, z = app s r ∧ r ≠ 0 ∧ lt (tcHd r) y
  /-- **The order of normal codes is the order of their exponent lists.** -/
  lt_itoL_iff : ∀ b c : V, nf b → dom b → nf c → dom c → (lt (itoL b) (itoL c) ↔ lt b c)

/-- The three formulas the theories and sentences are written with: the internal order `≺`,
`NF` and `Dom`. -/
structure OrderFormulas where
  /-- `x ≺ y`, slot `0` the smaller element. -/
  ltDef : 𝚺₁.Semisentence 2
  nfDef : 𝚺₁.Semisentence 1
  domDef : 𝚺₁.Semisentence 1

/-- **The hypothesis structure**: `Σ₁` definitions of the internal order `≺`, of `NF`, `Dom`,
of the descending lists and of list concatenation, satisfying `OrderAxioms` in every model of
`IΣ₁`. -/
structure InternalOrderFacts extends OrderFormulas where
  /-- Descending lists of normal domain codes. -/
  slDef : 𝚺₁.Semisentence 1
  /-- Concatenation of sum codes. -/
  app : ∀ {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V → V → V
  appDef : 𝚺₁.Semisentence 3
  app_defined : ∀ {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    𝚺₁-Function₂ (app : V → V → V) via appDef
  axioms : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    OrderAxioms V (fun x y => ltDef.val.Evalb ![x, y]) (fun x => nfDef.val.Evalb ![x])
      (fun x => domDef.val.Evalb ![x]) (fun x => slDef.val.Evalb ![x]) app

namespace OrderFormulas

variable (F : OrderFormulas) {V : Type} [ORingStructure V]

/-- `x ≺ y` in `V`. -/
def lt (x y : V) : Prop := F.ltDef.val.Evalb ![x, y]

/-- `x` is a normal code. -/
def nf (x : V) : Prop := F.nfDef.val.Evalb ![x]

/-- `x` satisfies the domain condition. -/
def dom (x : V) : Prop := F.domDef.val.Evalb ![x]

/-- The field of the order: normal domain codes. -/
def fld (x : V) : Prop := F.nf x ∧ F.dom x

/-- `x ≼ y`. -/
def le (x y : V) : Prop := F.lt x y ∨ x = y

instance lt_defined : 𝚺₁-Relation (F.lt : V → V → Prop) via F.ltDef :=
  .mk fun v => by simp only [lt]; rw [← Matrix.fun_eq_vec_two]

instance nf_defined : 𝚺₁-Predicate (F.nf : V → Prop) via F.nfDef :=
  .mk fun v => by simp only [nf]; rw [← Matrix.fun_eq_vec_one]

instance dom_defined : 𝚺₁-Predicate (F.dom : V → Prop) via F.domDef :=
  .mk fun v => by simp only [dom]; rw [← Matrix.fun_eq_vec_one]

instance lt_definable : 𝚺₁-Relation (F.lt : V → V → Prop) := (lt_defined F).to_definable
instance nf_definable : 𝚺₁-Predicate (F.nf : V → Prop) := (nf_defined F).to_definable
instance dom_definable : 𝚺₁-Predicate (F.dom : V → Prop) := (dom_defined F).to_definable

instance fld_definable : 𝚺₁-Predicate (F.fld : V → Prop) := by
  unfold fld; definability

instance le_definable : 𝚺₁-Relation (F.le : V → V → Prop) := by
  unfold le; definability

end OrderFormulas

namespace InternalOrderFacts

open OrderFormulas

variable (hJ : InternalOrderFacts) {V : Type} [ORingStructure V]

/-- `x` is a descending list of normal domain codes. -/
def sl (x : V) : Prop := hJ.slDef.val.Evalb ![x]

instance sl_defined : 𝚺₁-Predicate (hJ.sl : V → Prop) via hJ.slDef :=
  .mk fun v => by simp only [sl]; rw [← Matrix.fun_eq_vec_one]

instance sl_definable : 𝚺₁-Predicate (hJ.sl : V → Prop) := (sl_defined hJ).to_definable

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance app_defined' : 𝚺₁-Function₂ (hJ.app : V → V → V) via hJ.appDef := hJ.app_defined

instance app_definable : 𝚺₁-Function₂ (hJ.app : V → V → V) := (app_defined' hJ).to_definable
instance app_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (hJ.app : V → V → V) :=
  (app_definable hJ).of_sigmaOne

/-- The axioms in `V`, for the predicates defined by the formulas. -/
theorem ax : OrderAxioms V hJ.lt hJ.nf hJ.dom hJ.sl hJ.app := hJ.axioms V

/-! ### Derived facts -/

variable {hJ}

theorem fld_mc (a : ThetaWTerm) : hJ.fld (mc a : V) ↔ ThetaWTerm.NF a ∧ ThetaWTerm.Dom a := by
  rw [OrderFormulas.fld, hJ.ax.nf_mc, hJ.ax.dom_mc]

theorem fld_zero : hJ.fld (0 : V) := by
  have := (fld_mc (hJ := hJ) (V := V) (ThetaWTerm.sum [])).mpr
    ⟨ThetaWTerm.nf_zero, ThetaWTerm.dom_zero⟩
  rwa [mc_nil] at this

theorem fld_Omega (k : ℕ) : hJ.fld (tcOmega (k : V)) := by
  have := (fld_mc (hJ := hJ) (V := V) (ThetaWTerm.Omega k)).mpr
    ⟨ThetaWTerm.nf_Omega k, by simp [ThetaWTerm.Dom]⟩
  rwa [mc_Omega] at this

theorem zero_lt_Omega (k : ℕ) : hJ.lt (0 : V) (tcOmega (k : V)) := by
  have := (hJ.ax.lt_mc (V := V) (ThetaWTerm.sum []) (ThetaWTerm.Omega k)).mpr
    (ThetaWTerm.nil_lt_Omega k)
  rwa [mc_nil, mc_Omega] at this

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem fld_nf {x : V} (h : hJ.fld x) : hJ.nf x := h.1

theorem fld_theta_iff (k a : V) :
    hJ.fld (tcTheta k a) ↔ hJ.fld a ∧ ∀ y, iinG k y a = 1 → hJ.lt y a := by
  constructor
  · rintro ⟨hn, hd⟩
    have ha := (hJ.ax.nf_theta k a).mp hn
    obtain ⟨h1, h2⟩ := (hJ.ax.dom_theta k a ha).mp hd
    exact ⟨⟨ha, h1⟩, h2⟩
  · rintro ⟨⟨ha, hd⟩, h⟩
    exact ⟨(hJ.ax.nf_theta k a).mpr ha, (hJ.ax.dom_theta k a ha).mpr ⟨hd, h⟩⟩

theorem fld_of_iinE {k g c : V} (hc : hJ.fld c) (h : iinE k g c = 1) : hJ.fld g :=
  hJ.ax.fld_of_iinE k g c hc.1 hc.2 h

theorem fld_of_iinG {k y c : V} (hc : hJ.fld c) (h : iinG k y c = 1) : hJ.fld y :=
  hJ.ax.fld_of_iinG k y c hc.1 hc.2 h

theorem sl_cons_iff (x w : V) :
    hJ.sl (tcCons x w) ↔ hJ.fld x ∧ hJ.sl w ∧ (w = 0 ∨ hJ.le (tcHd w) x) :=
  hJ.ax.sl_cons x w

theorem fld_cons_iff (x w : V) :
    hJ.fld (tcCons x w) ↔ hJ.sl (tcCons x w) ∧ ¬ (w = 0 ∧ (kind x = 1 ∨ kind x = 2)) :=
  hJ.ax.fld_cons x w

theorem fld_hd {x w : V} (h : hJ.fld (tcCons x w)) : hJ.fld x :=
  ((sl_cons_iff x w).mp ((fld_cons_iff x w).mp h).1).1

theorem lt_trans {a b c : V} (ha : hJ.fld a) (hb : hJ.fld b) (hc : hJ.fld c)
    (hab : hJ.lt a b) (hbc : hJ.lt b c) : hJ.lt a c :=
  hJ.ax.lt_trans ha.1 hb.1 hc.1 hab hbc

theorem lt_of_le_of_lt {a b c : V} (ha : hJ.fld a) (hb : hJ.fld b) (hc : hJ.fld c)
    (hab : hJ.le a b) (hbc : hJ.lt b c) : hJ.lt a c := by
  rcases hab with h | rfl
  · exact lt_trans ha hb hc h hbc
  · exact hbc

theorem lt_of_lt_of_le {a b c : V} (ha : hJ.fld a) (hb : hJ.fld b) (hc : hJ.fld c)
    (hab : hJ.lt a b) (hbc : hJ.le b c) : hJ.lt a c := by
  rcases hbc with h | rfl
  · exact lt_trans ha hb hc hab h
  · exact hab

theorem le_trans {a b c : V} (ha : hJ.fld a) (hb : hJ.fld b) (hc : hJ.fld c)
    (hab : hJ.le a b) (hbc : hJ.le b c) : hJ.le a c := by
  rcases hbc with h | rfl
  · exact Or.inl (lt_of_le_of_lt ha hb hc hab h)
  · exact hab

/-- The shapes of normal codes. -/
theorem nf_cases {b : V} (hb : hJ.nf b) : b = 0 ∨ kind b = 1 ∨ kind b = 2 ∨ kind b = 3 := by
  have ht := hJ.ax.nf_isTerm b hb
  rcases kind_cases b with h | h | h | h | h
  · exact Or.inl (kind_eq_zero_iff.mp h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exfalso
    have := isTermb_kind_four h
    unfold isTerm at ht
    rw [this] at ht; simp at ht

/-- **The exponent list of a normal domain code is a descending list.** -/
theorem sl_itoL {x : V} (hx : hJ.fld x) : hJ.sl (itoL x) := by
  rcases nf_cases hx.1 with rfl | h | h | h
  · rw [itoL_zero]; exact hJ.ax.sl_zero
  · rw [itoL_of_prin (Or.inl h)]
    exact (sl_cons_iff x 0).mpr ⟨hx, hJ.ax.sl_zero, Or.inl rfl⟩
  · rw [itoL_of_prin (Or.inr h)]
    exact (sl_cons_iff x 0).mpr ⟨hx, hJ.ax.sl_zero, Or.inl rfl⟩
  · rw [eq_tcCons_of_kind h] at hx ⊢
    rw [itoL_tcCons]
    exact ((fld_cons_iff _ _).mp hx).1

theorem sl_eq_cons {s : V} (hs : hJ.sl s) (hs0 : s ≠ 0) : ∃ x w, s = tcCons x w := by
  rcases hJ.ax.sl_shape s hs with h | h
  · exact absurd h hs0
  · exact ⟨_, _, eq_tcCons_of_kind h⟩

/-- **Below `ω^β`**: a list below `⟨β⟩` is empty or has its first entry `≺ β`. -/
theorem lt_single_cases {l β : V} (hl : hJ.sl l) (h : hJ.lt l (tcCons β 0)) :
    l = 0 ∨ ∃ z w, l = tcCons z w ∧ hJ.lt z β := by
  rcases eq_or_ne l 0 with rfl | hl0
  · exact Or.inl rfl
  obtain ⟨z, w, rfl⟩ := sl_eq_cons hl hl0
  rw [hJ.ax.lt_cons_cons] at h
  rcases h with h | ⟨-, h⟩
  · exact Or.inr ⟨z, w, rfl, h⟩
  · exact absurd h (hJ.ax.not_lt_zero w)

/-- **Below `Ω_{k+1} + 1`**: a normal domain code below `⟨Ω_{k+1}, 0⟩` is below `Ω_{k+1}` or is
`Ω_{k+1}`. -/
theorem lt_Omega_succ_cases {ξ : V} {k : ℕ} (hξ : hJ.fld ξ)
    (h : hJ.lt ξ (tcCons (tcOmega (k : V)) (tcCons 0 0))) :
    hJ.lt ξ (tcOmega (k : V)) ∨ ξ = tcOmega (k : V) := by
  rcases nf_cases hξ.1 with rfl | hk | hk | hk
  · exact Or.inl (zero_lt_Omega k)
  · rw [eq_tcOmega_of_kind hk] at h ⊢
    exact (hJ.ax.lt_Omega_cons _ _ _).mp h
  · rw [eq_tcTheta_of_kind hk] at h ⊢
    exact (hJ.ax.lt_theta_cons _ _ _ _).mp h
  · rw [eq_tcCons_of_kind hk] at h hξ ⊢
    rw [hJ.ax.lt_cons_cons] at h
    rcases h with h | ⟨hz, h⟩
    · exact Or.inl ((hJ.ax.lt_cons_Omega _ _ _).mpr h)
    · exfalso
      have hsl := ((sl_cons_iff _ _).mp ((fld_cons_iff _ _).mp hξ).1).2.1
      rcases lt_single_cases hsl h with hw | ⟨z', w', -, hz'⟩
      · refine ((fld_cons_iff _ _).mp hξ).2 ⟨hw, Or.inl ?_⟩
        rw [hz]; simp
      · exact hJ.ax.not_lt_zero z' hz'

end InternalOrderFacts

end OrdinalAnalysis.IDn.Upper
