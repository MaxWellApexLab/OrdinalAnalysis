/-
  Arithmetic on the coded ϑ-notation inside models of `IΣ₁`: the definitions.

  `Ordinal/Theta/Arith.lean` computes the arithmetic of normal forms on their lists of Cantor
  exponents (`toList`, `ofList`): the natural sum merges the lists, the ordinal sum keeps the
  exponents of the left summand that are `≽` the first exponent of the right summand and
  appends the right summand, `ω^α` has the single exponent `α`, and `ω · α` replaces every
  exponent `αᵢ` by `1 + αᵢ`.  The same definitions are made here on codes.  The code of a sum
  is a cons list of codes, so a *list code* is `0` or a cons cell; every code that is not a
  cons cell is read as the empty list.

  * `itoL`, `iofL`: the exponent list of a code, and the code with a given exponent list;
  * `imerge`, `ifilt`, `iapp`, `imapOP`, `irep`: merge, filter, append, the map of `1 + ·`,
    and the list `⟨0, …, 0⟩`, each a course-of-values table (`CovTable`) with a `Σ₁` graph;
  * `iaddL`, `iadd`, `inadd`, `iomegaPow`, `ionePlus`, `iomegaMul`, `inum`, `ione`, `isucc`.

  Each function comes with its recursion equations and with `Σ₁` graphs and definability
  instances at every level of the hierarchy.
-/
import OrdinalAnalysis.ID1.Internal.OrderE

set_option autoImplicit false

namespace OrdinalAnalysis.ID1.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.Gentzen.InternalONote

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The comparison `≽` as a flag -/

/-- `ige x y = 1` iff `y ≼ x`: the comparison of the merge and of the filter. -/
noncomputable def ige (x y : V) : V := bor (iltb y x) (beq y x)

def igeDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r x y. ∃ l, !iltbDef l y x ∧ ∃ e, !beqDef e y x ∧ !borDef r l e”

instance ige_defined : 𝚺₁-Function₂ (ige : V → V → V) via igeDef := .mk fun v ↦ by
  simp [igeDef, ige, iltb_defined.iff, beq_defined.iff, bor_defined.iff]

instance ige_definable : 𝚺₁-Function₂ (ige : V → V → V) := ige_defined.to_definable
instance ige_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (ige : V → V → V) :=
  ige_definable.of_sigmaOne

lemma ige_eq_one {x y : V} : ige x y = 1 ↔ iltb y x = 1 ∨ y = x := by
  simp [ige]

/-! ### Exponent lists -/

/-- `1` iff `c` has principal shape `Ω` or `ϑ α` (`kind` `1` or `2`). -/
noncomputable def isPrinb (c : V) : V := if kind c = 1 ∨ kind c = 2 then 1 else 0

def isPrinbDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ k, !kindDef k c ∧ (((k = 1 ∨ k = 2) ∧ y = 1) ∨ (k ≠ 1 ∧ k ≠ 2 ∧ y = 0))”

instance isPrinb_defined : 𝚺₁-Function₁ (isPrinb : V → V) via isPrinbDef := .mk fun v ↦ by
  simp only [isPrinbDef, isPrinb]
  rcases kind_cases (v 1) with h | h | h | h | h <;> simp [h, kind_defined.iff]

instance isPrinb_definable : 𝚺₁-Function₁ (isPrinb : V → V) := isPrinb_defined.to_definable
instance isPrinb_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (isPrinb : V → V) :=
  isPrinb_definable.of_sigmaOne

@[simp] lemma isPrinb_eq_one {c : V} : isPrinb c = 1 ↔ kind c = 1 ∨ kind c = 2 := by
  unfold isPrinb; split_ifs with h <;> simp [h]

/-- The exponent list of a code: `⟨c⟩` for the principal shapes, `c` itself otherwise. -/
noncomputable def itoL (c : V) : V := if kind c = 1 ∨ kind c = 2 then tcCons c 0 else c

/-- The code with exponent list `s`: a one-entry list with a principal entry `P` gives `P`,
every other list gives itself. -/
noncomputable def iofL (s : V) : V :=
  if kind s = 3 ∧ tcTl s = 0 ∧ (kind (tcHd s) = 1 ∨ kind (tcHd s) = 2) then tcHd s else s

def itoLDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ p, !isPrinbDef p c ∧ ((p = 1 ∧ !tcConsDef y c 0) ∨ (p ≠ 1 ∧ y = c))”

def iofLDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y s. ∃ k, !kindDef k s ∧ ∃ t, !tcTlDef t s ∧ ∃ h, !tcHdDef h s ∧ ∃ p, !isPrinbDef p h ∧
    ((k = 3 ∧ t = 0 ∧ p = 1 ∧ y = h) ∨ ((k ≠ 3 ∨ t ≠ 0 ∨ p ≠ 1) ∧ y = s))”

instance itoL_defined : 𝚺₁-Function₁ (itoL : V → V) via itoLDef := .mk fun v ↦ by
  simp only [itoLDef, itoL]
  by_cases h : kind (v 1) = 1 ∨ kind (v 1) = 2
  · simp [h, isPrinb_defined.iff, tcCons_defined.iff]
  · simp [h, isPrinb_defined.iff, tcCons_defined.iff]

instance iofL_defined : 𝚺₁-Function₁ (iofL : V → V) via iofLDef := .mk fun v ↦ by
  simp [iofLDef, iofL, kind_defined.iff, tcTl_defined.iff, tcHd_defined.iff,
    isPrinb_defined.iff]
  by_cases h1 : kind (v 1) = 3 <;> by_cases h2 : tcTl (v 1) = 0 <;>
    rcases kind_cases (tcHd (v 1)) with h3 | h3 | h3 | h3 | h3 <;> simp [h1, h2, h3]

instance itoL_definable : 𝚺₁-Function₁ (itoL : V → V) := itoL_defined.to_definable
instance itoL_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (itoL : V → V) :=
  itoL_definable.of_sigmaOne
instance iofL_definable : 𝚺₁-Function₁ (iofL : V → V) := iofL_defined.to_definable
instance iofL_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (iofL : V → V) :=
  iofL_definable.of_sigmaOne

@[simp] lemma itoL_zero : itoL (0 : V) = 0 := by simp [itoL]

@[simp] lemma itoL_one : itoL (1 : V) = tcCons 1 0 := by simp [itoL]

@[simp] lemma itoL_tcTheta (a : V) : itoL (tcTheta a) = tcCons (tcTheta a) 0 := by simp [itoL]

@[simp] lemma itoL_tcCons (x s : V) : itoL (tcCons x s) = tcCons x s := by simp [itoL]

@[simp] lemma iofL_zero : iofL (0 : V) = 0 := by simp [iofL]

lemma iofL_single_prin {p : V} (hp : kind p = 1 ∨ kind p = 2) : iofL (tcCons p 0) = p := by
  simp [iofL, hp]

lemma iofL_single_of_not_prin {x : V} (hx : ¬ (kind x = 1 ∨ kind x = 2)) (s : V) :
    iofL (tcCons x s) = tcCons x s := by
  simp [iofL, hx]

lemma iofL_of_tl_ne_zero (x : V) {s : V} (hs : s ≠ 0) : iofL (tcCons x s) = tcCons x s := by
  simp [iofL, hs]

@[simp] lemma iofL_tcTheta (a : V) : iofL (tcTheta a) = tcTheta a := by simp [iofL]

@[simp] lemma iofL_one : iofL (1 : V) = 1 := by simp [iofL]

/-! ### Pair-indexed tables

Each of the three list operations of two arguments is a table over pair positions
`⟪s, t⟫`, reading the table only at `⟪tail s, t⟫` or `⟪s, tail t⟫`. -/

/-- The value stored in a table `S` at `⟪x, y⟫`. -/
noncomputable def rd2 (S x y : V) : V := znth S ⟪x, y⟫

def rd2Def : 𝚺₁.Semisentence 4 := .mkSigma
  “r S x y. ∃ i, !pairDef i x y ∧ !znthDef r S i”

instance rd2_defined : 𝚺₁-Function₃ (rd2 : V → V → V → V) via rd2Def := .mk fun v ↦ by
  simp [rd2Def, rd2, pair_defined.iff, znth_defined.iff]

/-! #### Merge -/

/-- The merge of two lists, one step: `s = ⟨x, …⟩`, `t = ⟨y, …⟩`; `x` goes first when
`y ≼ x`. -/
noncomputable def mergeF (s t S : V) : V :=
  if kind s = 3 then
    if kind t = 3 then
      if ige (tcHd s) (tcHd t) = 1 then tcCons (tcHd s) (rd2 S (tcTl s) t)
      else tcCons (tcHd t) (rd2 S s (tcTl t))
    else s
  else t

def mergeFDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y s t S. ∃ ks, !kindDef ks s ∧ ∃ kt, !kindDef kt t ∧
    ( (ks ≠ 3 ∧ y = t)
    ∨ (ks = 3 ∧ kt ≠ 3 ∧ y = s)
    ∨ (ks = 3 ∧ kt = 3 ∧ ∃ x, !tcHdDef x s ∧ ∃ z, !tcHdDef z t ∧ ∃ g, !igeDef g x z ∧
        ( (g = 1 ∧ ∃ s', !tcTlDef s' s ∧ ∃ r, !rd2Def r S s' t ∧ !tcConsDef y x r)
        ∨ (g ≠ 1 ∧ ∃ t', !tcTlDef t' t ∧ ∃ r, !rd2Def r S s t' ∧ !tcConsDef y z r))))”

instance mergeF_defined : 𝚺₁-Function₃ (mergeF : V → V → V → V) via mergeFDef :=
  .mk fun v ↦ by
  simp only [mergeFDef, mergeF]
  by_cases h1 : kind (v 1) = 3 <;> by_cases h2 : kind (v 2) = 3
  · by_cases h3 : ige (tcHd (v 1)) (tcHd (v 2)) = 1
    · simp [h1, h2, h3, kind_defined.iff, tcHd_defined.iff, tcTl_defined.iff, ige_defined.iff,
        rd2_defined.iff, tcCons_defined.iff]
    · simp [h1, h2, h3, kind_defined.iff, tcHd_defined.iff, tcTl_defined.iff, ige_defined.iff,
        rd2_defined.iff, tcCons_defined.iff]
  · simp [h1, h2, kind_defined.iff]
  · simp [h1, h2, kind_defined.iff]
  · simp [h1, h2, kind_defined.iff]

/-- The step of the merge table at position `⟪s, t⟫`. -/
noncomputable def mergeStep (i S : V) : V := mergeF (π₁ i) (π₂ i) S

def mergeStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y i S. ∃ s, !pi₁Def s i ∧ ∃ t, !pi₂Def t i ∧ !mergeFDef y s t S”

instance mergeStep_defined : 𝚺₁-Function₂ (mergeStep : V → V → V) via mergeStepDef :=
  .mk fun v ↦ by simp [mergeStepDef, mergeStep, pi₁_defined.iff, pi₂_defined.iff,
    mergeF_defined.iff]

/-- **The merge** of two list codes. -/
noncomputable def imerge (s t : V) : V := covVal mergeStep mergeStepDef ⟪s, t⟫

def imergeDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y s t. ∃ i, !pairDef i s t ∧ !(covValDef mergeStepDef) y i”

instance imerge_defined : 𝚺₁-Function₂ (imerge : V → V → V) via imergeDef := .mk fun v ↦ by
  simp [imergeDef, imerge, pair_defined.iff, (covVal_defined mergeStep mergeStepDef).iff]

instance imerge_definable : 𝚺₁-Function₂ (imerge : V → V → V) := imerge_defined.to_definable
instance imerge_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (imerge : V → V → V) :=
  imerge_definable.of_sigmaOne

lemma imerge_unfold (s t : V) :
    ∃ S : V, imerge s t = mergeF s t S ∧
      ∀ x y : V, ⟪x, y⟫ < ⟪s, t⟫ → rd2 S x y = imerge x y := by
  obtain ⟨S, h, hr⟩ := covVal_unfold mergeStep mergeStepDef (⟪s, t⟫ : V)
  exact ⟨S, by rw [imerge, h, mergeStep, pi₁_pair, pi₂_pair], fun x y hxy => hr _ hxy⟩

lemma imerge_left_of_kind {s : V} (hs : kind s ≠ 3) (t : V) : imerge s t = t := by
  obtain ⟨S, h, -⟩ := imerge_unfold s t
  simp [h, mergeF, hs]

lemma imerge_right_of_kind (x s' : V) {t : V} (ht : kind t ≠ 3) :
    imerge (tcCons x s') t = tcCons x s' := by
  obtain ⟨S, h, -⟩ := imerge_unfold (tcCons x s') t
  simp [h, mergeF, ht]

@[simp] lemma imerge_zero_left (t : V) : imerge 0 t = t := imerge_left_of_kind (by simp) t

lemma imerge_zero_right {s : V} (hs : sumK s = 1) : imerge s 0 = s := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  · have hk : kind s = 3 := by
      unfold sumK at hs
      split_ifs at hs with h
      · rcases h with h | h
        · exact absurd (kind_eq_zero_iff.mp h) hs0
        · exact h
      · simp at hs
    rw [eq_tcCons_of_kind hk]; exact imerge_right_of_kind _ _ (by simp)

lemma imerge_cons_cons (x s y t : V) :
    imerge (tcCons x s) (tcCons y t) =
      if ige x y = 1 then tcCons x (imerge s (tcCons y t))
      else tcCons y (imerge (tcCons x s) t) := by
  obtain ⟨S, h, hr⟩ := imerge_unfold (tcCons x s) (tcCons y t)
  rw [h, mergeF]
  simp only [kind_tcCons, tcHd_tcCons, tcTl_tcCons, if_true]
  rw [hr s (tcCons y t) (pair_lt_pair_left (tl_lt_tcCons x s) _),
    hr (tcCons x s) t (pair_lt_pair_right _ (tl_lt_tcCons y t))]

/-! #### Filter -/

/-- The filter of a list, one step: the entries `x` with `y ≼ x` are kept. -/
noncomputable def filtF (s y S : V) : V :=
  if kind s = 3 then
    if ige (tcHd s) y = 1 then tcCons (tcHd s) (rd2 S (tcTl s) y) else rd2 S (tcTl s) y
  else 0

def filtFDef : 𝚺₁.Semisentence 4 := .mkSigma
  “r s y S. ∃ ks, !kindDef ks s ∧
    ( (ks ≠ 3 ∧ r = 0)
    ∨ (ks = 3 ∧ ∃ x, !tcHdDef x s ∧ ∃ u, !tcTlDef u s ∧ ∃ g, !igeDef g x y ∧
        ∃ w, !rd2Def w S u y ∧ ((g = 1 ∧ !tcConsDef r x w) ∨ (g ≠ 1 ∧ r = w))))”

instance filtF_defined : 𝚺₁-Function₃ (filtF : V → V → V → V) via filtFDef := .mk fun v ↦ by
  simp [filtFDef, filtF, kind_defined.iff, tcHd_defined.iff, tcTl_defined.iff,
    ige_defined.iff, rd2_defined.iff, tcCons_defined.iff]
  by_cases h1 : kind (v 1) = 3 <;> by_cases h2 : ige (tcHd (v 1)) (v 2) = 1 <;> simp [h1, h2]

noncomputable def filtStep (i S : V) : V := filtF (π₁ i) (π₂ i) S

def filtStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r i S. ∃ s, !pi₁Def s i ∧ ∃ y, !pi₂Def y i ∧ !filtFDef r s y S”

instance filtStep_defined : 𝚺₁-Function₂ (filtStep : V → V → V) via filtStepDef :=
  .mk fun v ↦ by simp [filtStepDef, filtStep, pi₁_defined.iff, pi₂_defined.iff,
    filtF_defined.iff]

/-- **The filter** `s ↦ ⟨x ∈ s | y ≼ x⟩` on list codes. -/
noncomputable def ifilt (s y : V) : V := covVal filtStep filtStepDef ⟪s, y⟫

def ifiltDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r s y. ∃ i, !pairDef i s y ∧ !(covValDef filtStepDef) r i”

instance ifilt_defined : 𝚺₁-Function₂ (ifilt : V → V → V) via ifiltDef := .mk fun v ↦ by
  simp [ifiltDef, ifilt, pair_defined.iff, (covVal_defined filtStep filtStepDef).iff]

instance ifilt_definable : 𝚺₁-Function₂ (ifilt : V → V → V) := ifilt_defined.to_definable
instance ifilt_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (ifilt : V → V → V) :=
  ifilt_definable.of_sigmaOne

lemma ifilt_unfold (s y : V) :
    ∃ S : V, ifilt s y = filtF s y S ∧
      ∀ x z : V, ⟪x, z⟫ < ⟪s, y⟫ → rd2 S x z = ifilt x z := by
  obtain ⟨S, h, hr⟩ := covVal_unfold filtStep filtStepDef (⟪s, y⟫ : V)
  exact ⟨S, by rw [ifilt, h, filtStep, pi₁_pair, pi₂_pair], fun x z hxz => hr _ hxz⟩

lemma ifilt_of_kind {s : V} (hs : kind s ≠ 3) (y : V) : ifilt s y = 0 := by
  obtain ⟨S, h, -⟩ := ifilt_unfold s y
  simp [h, filtF, hs]

@[simp] lemma ifilt_zero (y : V) : ifilt 0 y = 0 := ifilt_of_kind (by simp) y

lemma ifilt_cons (x s y : V) :
    ifilt (tcCons x s) y = if ige x y = 1 then tcCons x (ifilt s y) else ifilt s y := by
  obtain ⟨S, h, hr⟩ := ifilt_unfold (tcCons x s) y
  rw [h, filtF]
  simp only [kind_tcCons, tcHd_tcCons, tcTl_tcCons, if_true]
  rw [hr s y (pair_lt_pair_left (tl_lt_tcCons x s) _)]

/-! #### Append -/

/-- The concatenation of two lists, one step. -/
noncomputable def appF (s t S : V) : V :=
  if kind s = 3 then tcCons (tcHd s) (rd2 S (tcTl s) t) else t

def appFDef : 𝚺₁.Semisentence 4 := .mkSigma
  “r s t S. ∃ ks, !kindDef ks s ∧
    ( (ks ≠ 3 ∧ r = t)
    ∨ (ks = 3 ∧ ∃ x, !tcHdDef x s ∧ ∃ u, !tcTlDef u s ∧ ∃ w, !rd2Def w S u t ∧
        !tcConsDef r x w))”

instance appF_defined : 𝚺₁-Function₃ (appF : V → V → V → V) via appFDef := .mk fun v ↦ by
  simp [appFDef, appF, kind_defined.iff, tcHd_defined.iff, tcTl_defined.iff,
    rd2_defined.iff, tcCons_defined.iff]
  by_cases h1 : kind (v 1) = 3 <;> simp [h1]

noncomputable def appStep (i S : V) : V := appF (π₁ i) (π₂ i) S

def appStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r i S. ∃ s, !pi₁Def s i ∧ ∃ t, !pi₂Def t i ∧ !appFDef r s t S”

instance appStep_defined : 𝚺₁-Function₂ (appStep : V → V → V) via appStepDef :=
  .mk fun v ↦ by simp [appStepDef, appStep, pi₁_defined.iff, pi₂_defined.iff,
    appF_defined.iff]

/-- **The concatenation** of two list codes. -/
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
      ∀ x z : V, ⟪x, z⟫ < ⟪s, t⟫ → rd2 S x z = iapp x z := by
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

/-! ### Numerals -/

/-- The list `⟨0, …, 0⟩` of length `n`, one step. -/
noncomputable def repStep (n S : V) : V := if n = 0 then 0 else tcCons 0 (znth S (n - 1))

def repStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r n S. (n = 0 ∧ r = 0) ∨ (n ≠ 0 ∧ ∃ m, !subDef m n 1 ∧ ∃ w, !znthDef w S m ∧
    !tcConsDef r 0 w)”

instance repStep_defined : 𝚺₁-Function₂ (repStep : V → V → V) via repStepDef := .mk fun v ↦ by
  by_cases h : v 1 = 0
  · simp [repStepDef, repStep, h]
  · simp [repStepDef, repStep, h, sub_defined.iff, znth_defined.iff, tcCons_defined.iff]

/-- **The numeral** `n` as the code of `⟨0, …, 0⟩` (`n` entries). -/
noncomputable def inum (n : V) : V := covVal repStep repStepDef n

def inumDef : 𝚺₁.Semisentence 2 := covValDef repStepDef

instance inum_defined : 𝚺₁-Function₁ (inum : V → V) via inumDef :=
  covVal_defined repStep repStepDef

instance inum_definable : 𝚺₁-Function₁ (inum : V → V) := inum_defined.to_definable
instance inum_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (inum : V → V) :=
  inum_definable.of_sigmaOne

@[simp] lemma inum_zero : inum (0 : V) = 0 := by
  simp [inum, covVal_zero, repStep]

lemma inum_succ (n : V) : inum (n + 1) = tcCons 0 (inum n) := by
  obtain ⟨S, h, hr⟩ := covVal_unfold repStep repStepDef (n + 1)
  rw [inum, h, repStep, if_neg (by simp), add_tsub_cancel_right,
    hr n (lt_add_one n)]
  rfl

/-! ### The operations -/

/-- The code of `1 = ⟨0⟩`. -/
noncomputable def ione : V := tcCons 0 0

lemma inum_one : inum (1 : V) = ione := by
  have := inum_succ (0 : V)
  rw [zero_add] at this
  rw [this, inum_zero, ione]

/-- The exponent list of `α + β`: the exponents of `α` that are `≽` the first exponent of
`β`, followed by the exponents of `β`. -/
noncomputable def iaddL (s t : V) : V := if kind t = 3 then iapp (ifilt s (tcHd t)) t else s

/-- **The ordinal sum** on codes. -/
noncomputable def iadd (a b : V) : V := iofL (iaddL (itoL a) (itoL b))

/-- **The natural sum** on codes. -/
noncomputable def inadd (a b : V) : V := iofL (imerge (itoL a) (itoL b))

/-- **`ω^α`** on codes. -/
noncomputable def iomegaPow (a : V) : V := iofL (tcCons a 0)

/-- `1 + α` on codes. -/
noncomputable def ionePlus (e : V) : V := iofL (iaddL ione (itoL e))

/-- **The successor** `α + 1 = α ⊕ 1` on codes. -/
noncomputable def isucc (a : V) : V := inadd a ione

def ioneDef : 𝚺₁.Semisentence 1 := .mkSigma “y. !tcConsDef y 0 0”

def iaddLDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r s t. ∃ k, !kindDef k t ∧ ((k = 3 ∧ ∃ h, !tcHdDef h t ∧ ∃ f, !ifiltDef f s h ∧
    !iappDef r f t) ∨ (k ≠ 3 ∧ r = s))”

def iaddDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r a b. ∃ s, !itoLDef s a ∧ ∃ t, !itoLDef t b ∧ ∃ u, !iaddLDef u s t ∧ !iofLDef r u”

def inaddDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r a b. ∃ s, !itoLDef s a ∧ ∃ t, !itoLDef t b ∧ ∃ u, !imergeDef u s t ∧ !iofLDef r u”

def iomegaPowDef : 𝚺₁.Semisentence 2 := .mkSigma
  “r a. ∃ s, !tcConsDef s a 0 ∧ !iofLDef r s”

def ionePlusDef : 𝚺₁.Semisentence 2 := .mkSigma
  “r e. ∃ o, !ioneDef o ∧ ∃ t, !itoLDef t e ∧ ∃ u, !iaddLDef u o t ∧ !iofLDef r u”

def isuccDef : 𝚺₁.Semisentence 2 := .mkSigma
  “r a. ∃ o, !ioneDef o ∧ !inaddDef r a o”

instance iaddL_defined : 𝚺₁-Function₂ (iaddL : V → V → V) via iaddLDef := .mk fun v ↦ by
  simp [iaddLDef, iaddL, kind_defined.iff, tcHd_defined.iff, ifilt_defined.iff,
    iapp_defined.iff]
  by_cases h : kind (v 2) = 3 <;> simp [h]

instance iadd_defined : 𝚺₁-Function₂ (iadd : V → V → V) via iaddDef := .mk fun v ↦ by
  simp [iaddDef, iadd, itoL_defined.iff, iaddL_defined.iff, iofL_defined.iff]

instance inadd_defined : 𝚺₁-Function₂ (inadd : V → V → V) via inaddDef := .mk fun v ↦ by
  simp [inaddDef, inadd, itoL_defined.iff, imerge_defined.iff, iofL_defined.iff]

instance iomegaPow_defined : 𝚺₁-Function₁ (iomegaPow : V → V) via iomegaPowDef :=
  .mk fun v ↦ by simp [iomegaPowDef, iomegaPow, tcCons_defined.iff, iofL_defined.iff]

instance ionePlus_defined : 𝚺₁-Function₁ (ionePlus : V → V) via ionePlusDef :=
  .mk fun v ↦ by
  simp [ionePlusDef, ionePlus, ione, ioneDef, tcCons_defined.iff, itoL_defined.iff,
    iaddL_defined.iff, iofL_defined.iff]

instance isucc_defined : 𝚺₁-Function₁ (isucc : V → V) via isuccDef := .mk fun v ↦ by
  simp [isuccDef, isucc, ione, ioneDef, tcCons_defined.iff, inadd_defined.iff]

instance iaddL_definable : 𝚺₁-Function₂ (iaddL : V → V → V) := iaddL_defined.to_definable
instance iaddL_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (iaddL : V → V → V) :=
  iaddL_definable.of_sigmaOne
instance iadd_definable : 𝚺₁-Function₂ (iadd : V → V → V) := iadd_defined.to_definable
instance iadd_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (iadd : V → V → V) :=
  iadd_definable.of_sigmaOne
instance inadd_definable : 𝚺₁-Function₂ (inadd : V → V → V) := inadd_defined.to_definable
instance inadd_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (inadd : V → V → V) :=
  inadd_definable.of_sigmaOne
instance iomegaPow_definable : 𝚺₁-Function₁ (iomegaPow : V → V) :=
  iomegaPow_defined.to_definable
instance iomegaPow_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (iomegaPow : V → V) :=
  iomegaPow_definable.of_sigmaOne
instance ionePlus_definable : 𝚺₁-Function₁ (ionePlus : V → V) :=
  ionePlus_defined.to_definable
instance ionePlus_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (ionePlus : V → V) :=
  ionePlus_definable.of_sigmaOne
instance isucc_definable : 𝚺₁-Function₁ (isucc : V → V) := isucc_defined.to_definable
instance isucc_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (isucc : V → V) :=
  isucc_definable.of_sigmaOne

lemma iaddL_of_kind (s : V) {t : V} (ht : kind t ≠ 3) : iaddL s t = s := by
  simp [iaddL, ht]

@[simp] lemma iaddL_zero_right (s : V) : iaddL s 0 = s := iaddL_of_kind s (by simp)

lemma iaddL_cons (s y t : V) : iaddL s (tcCons y t) = iapp (ifilt s y) (tcCons y t) := by
  simp [iaddL]

/-! #### `ω · α` -/

/-- The map of `1 + ·` over a list, one step. -/
noncomputable def mapStep (s S : V) : V :=
  if kind s = 3 then tcCons (ionePlus (tcHd s)) (znth S (tcTl s)) else 0

def mapStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r s S. ∃ ks, !kindDef ks s ∧
    ( (ks ≠ 3 ∧ r = 0)
    ∨ (ks = 3 ∧ ∃ x, !tcHdDef x s ∧ ∃ o, !ionePlusDef o x ∧ ∃ u, !tcTlDef u s ∧
        ∃ w, !znthDef w S u ∧ !tcConsDef r o w))”

instance mapStep_defined : 𝚺₁-Function₂ (mapStep : V → V → V) via mapStepDef :=
  .mk fun v ↦ by
  simp [mapStepDef, mapStep, kind_defined.iff, tcHd_defined.iff, ionePlus_defined.iff,
    tcTl_defined.iff, znth_defined.iff, tcCons_defined.iff]
  by_cases h1 : kind (v 1) = 3 <;> simp [h1]

/-- The list of the `1 + αᵢ` for the entries `αᵢ` of a list code. -/
noncomputable def imapOP (s : V) : V := covVal mapStep mapStepDef s

def imapOPDef : 𝚺₁.Semisentence 2 := covValDef mapStepDef

instance imapOP_defined : 𝚺₁-Function₁ (imapOP : V → V) via imapOPDef :=
  covVal_defined mapStep mapStepDef

instance imapOP_definable : 𝚺₁-Function₁ (imapOP : V → V) := imapOP_defined.to_definable
instance imapOP_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (imapOP : V → V) :=
  imapOP_definable.of_sigmaOne

lemma imapOP_of_kind {s : V} (hs : kind s ≠ 3) : imapOP s = 0 := by
  obtain ⟨S, h, -⟩ := covVal_unfold mapStep mapStepDef s
  rw [imapOP, h, mapStep, if_neg hs]

@[simp] lemma imapOP_zero : imapOP (0 : V) = 0 := imapOP_of_kind (by simp)

lemma imapOP_cons (x s : V) : imapOP (tcCons x s) = tcCons (ionePlus x) (imapOP s) := by
  obtain ⟨S, h, hr⟩ := covVal_unfold mapStep mapStepDef (tcCons x s)
  rw [imapOP, h, mapStep]
  simp only [kind_tcCons, tcHd_tcCons, tcTl_tcCons, if_true]
  rw [hr s (tl_lt_tcCons x s)]
  rfl

/-- **`ω · α`** on codes. -/
noncomputable def iomegaMul (a : V) : V := iofL (imapOP (itoL a))

def iomegaMulDef : 𝚺₁.Semisentence 2 := .mkSigma
  “r a. ∃ s, !itoLDef s a ∧ ∃ u, !imapOPDef u s ∧ !iofLDef r u”

instance iomegaMul_defined : 𝚺₁-Function₁ (iomegaMul : V → V) via iomegaMulDef :=
  .mk fun v ↦ by simp [iomegaMulDef, iomegaMul, itoL_defined.iff, imapOP_defined.iff,
    iofL_defined.iff]

instance iomegaMul_definable : 𝚺₁-Function₁ (iomegaMul : V → V) :=
  iomegaMul_defined.to_definable
instance iomegaMul_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (iomegaMul : V → V) :=
  iomegaMul_definable.of_sigmaOne

end OrdinalAnalysis.ID1.Internal
