/-
  Helper infrastructure for `OrdinalAnalysis.IDn.Calculus`, generalising the small standalone
  pieces of `OrdinalAnalysis.ID1.Calculus` (the parameters of a sequent, the true literals of
  arithmetic, and the head-symbol lemmas used by inversion and boundedness) from one level to
  `n` levels.

  **Why a separate file.**  `IDn/Language.lean`'s `params`/`paramsList` return a set of
  `Stage n` (a level *and* a bound), because a sequent of `LIinfN n` can mention every level at
  once.  The operator `H : Set ThetaWNoteD → Set ThetaWNoteD` of `IDn/Calculus.lean` (as in
  `ID1/Calculus.lean`, one level-free operator, now phrased against `ThetaWNoteD.HopS`/
  `ThetaWNoteD.NiceS`/`ThetaWNoteD.HullHypGe` per the operator adjudication in
  `Ordinal/ThetaW/HullSingle.lean`/`HullDom.lean`) acts on sets of *bare* `ThetaWNoteD` values.
  `paramsVal` bridges the two: it is `paramsList` composed with `Stage.val`, so that the control
  condition of Definition 5.6 reads `paramsVal Γ ⊆ H ∅`, exactly `ID1.paramsList Γ ⊆ H ∅` with
  the level tag erased.

  Contents.

    `paramsList_nil/cons/append/mono`, `params_subset_paramsList`   generic sequent-parameter
                                                                     lemmas, not yet in
                                                                     `IDn/Language.lean`
    `paramsVal`, `paramsVal_nil/cons/append/mono`,
    `mem_paramsVal_of_mem_params`                                   the `Set ThetaWNoteD` view
    `numI`                                                          the numerals
    `iinfFalseN`, `stdInfN`, `TrueN`, `IsArithLit`, `TrueLit`        the true literals of
                                                                     arithmetic (Definition 5.1)
    `negHeadStage`, `nstageAt_inj`, `stageAt_inj`                   head-symbol lemmas
    `ThetaWNoteD.NiceS.rk_mem`, `rk_mem_params`                     Exercise 5.5 (e), formula half
-/
import OrdinalAnalysis.IDn.Rank
import OrdinalAnalysis.Ordinal.ThetaW.HullDom

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder

variable {n : ℕ}

/-! ### The parameters of a sequent (not yet in `IDn/Language.lean`) -/

section ParamsList

variable {ξ : Type*} {m : ℕ}

@[simp] theorem paramsList_nil : paramsList ([] : List (Semiformula (LIinfN n) ξ m)) = ∅ := by
  ext; simp [paramsList]

@[simp] theorem paramsList_cons (φ : Semiformula (LIinfN n) ξ m)
    (Γ : List (Semiformula (LIinfN n) ξ m)) :
    paramsList (φ :: Γ) = params φ ∪ paramsList Γ := by
  ext; simp [paramsList]

@[simp] theorem paramsList_append (Γ Δ : List (Semiformula (LIinfN n) ξ m)) :
    paramsList (Γ ++ Δ) = paramsList Γ ∪ paramsList Δ := by
  ext; simp only [paramsList, List.mem_append, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨φ, (h | h), ha⟩
    · exact Or.inl ⟨φ, h, ha⟩
    · exact Or.inr ⟨φ, h, ha⟩
  · rintro (⟨φ, h, ha⟩ | ⟨φ, h, ha⟩)
    · exact ⟨φ, Or.inl h, ha⟩
    · exact ⟨φ, Or.inr h, ha⟩

theorem paramsList_mono {Γ Δ : List (Semiformula (LIinfN n) ξ m)} (h : Γ ⊆ Δ) :
    paramsList Γ ⊆ paramsList Δ :=
  fun _ ⟨φ, hφ, ha⟩ => ⟨φ, h hφ, ha⟩

theorem params_subset_paramsList {φ : Semiformula (LIinfN n) ξ m}
    {Γ : List (Semiformula (LIinfN n) ξ m)} (h : φ ∈ Γ) : params φ ⊆ paramsList Γ :=
  fun _ ha => ⟨φ, h, ha⟩

end ParamsList

/-! ### The `Set ThetaWNoteD` view of a sequent's parameters -/

section ParamsVal

variable {ξ : Type*} {m : ℕ}

/-- **`k(Γ)` with the level tag erased.**  The operator `H : Set ThetaWNoteD → Set ThetaWNoteD`
of the calculus is level-free, so its control conditions are phrased against this set, not
against `paramsList Γ : Set (Stage n)` directly. -/
def paramsVal (Γ : List (Semiformula (LIinfN n) ξ m)) : Set ThetaWNoteD :=
  Stage.val '' paramsList Γ

@[simp] theorem paramsVal_nil : paramsVal ([] : List (Semiformula (LIinfN n) ξ m)) = ∅ := by
  simp [paramsVal]

theorem paramsVal_cons (φ : Semiformula (LIinfN n) ξ m) (Γ : List (Semiformula (LIinfN n) ξ m)) :
    paramsVal (φ :: Γ) = Stage.val '' params φ ∪ paramsVal Γ := by
  rw [paramsVal, paramsList_cons, Set.image_union, paramsVal]

theorem paramsVal_append (Γ Δ : List (Semiformula (LIinfN n) ξ m)) :
    paramsVal (Γ ++ Δ) = paramsVal Γ ∪ paramsVal Δ := by
  rw [paramsVal, paramsList_append, Set.image_union, paramsVal, paramsVal]

theorem paramsVal_mono {Γ Δ : List (Semiformula (LIinfN n) ξ m)} (h : Γ ⊆ Δ) :
    paramsVal Γ ⊆ paramsVal Δ :=
  fun _ ⟨s, hs, hx⟩ => ⟨s, paramsList_mono h hs, hx⟩

theorem mem_paramsVal_of_mem_params {s : Stage n} {φ : Semiformula (LIinfN n) ξ m}
    {Γ : List (Semiformula (LIinfN n) ξ m)} (hφ : φ ∈ Γ) (hs : s ∈ params φ) :
    s.val ∈ paramsVal Γ :=
  ⟨s, params_subset_paramsList hφ hs, rfl⟩

theorem params_val_subset_paramsVal {φ : Semiformula (LIinfN n) ξ m}
    {Γ : List (Semiformula (LIinfN n) ξ m)} (h : φ ∈ Γ) :
    Stage.val '' params φ ⊆ paramsVal Γ :=
  fun _ ⟨s, hs, hx⟩ => ⟨s, params_subset_paramsList h hs, hx⟩

theorem paramsVal_map_capAt (k : Fin n) (b : StageAt k.val) (Θ : Sequent (LIinfN n)) :
    paramsVal (Θ.map (capAt k b)) ⊆ paramsVal Θ ∪ {b.1} := by
  rintro x ⟨s, ⟨φ, hφ, hs⟩, rfl⟩
  obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hφ
  rcases params_capAt k b χ hs with h | h
  · exact Or.inl (mem_paramsVal_of_mem_params hχ h)
  · right
    rw [Set.mem_singleton_iff] at h
    subst h
    rfl

end ParamsVal

/-! ### The numerals -/

/-- The numeral `n̄`. -/
abbrev numI (t : ℕ) : SyntacticTerm (LIinfN n) := Semiterm.numeral t

/-! ### The true literals of arithmetic -/

/-- The fresh symbols read as empty; only the arithmetic part matters for the literals below. -/
@[instance_reducible]
def iinfFalseN : Structure (IInfLangN n) ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ _ _ => False

/-- The standard structure: arithmetic standard, `X` and every level's every stage empty. -/
@[instance_reducible]
def stdInfN : Structure (LIinfN n) ℕ := Structure.add ℒₒᵣ (IInfLangN n) ℕ (str₂ := iinfFalseN)

/-- Truth of a formula in `stdInfN` under the zero assignment; for closed formulas of arithmetic
this is truth in `ℕ`. -/
def TrueN (φ : Proposition (LIinfN n)) : Prop :=
  Semiformula.Eval (s := stdInfN) ![] (fun _ => 0) φ

@[simp] theorem trueN_neg (φ : Proposition (LIinfN n)) : TrueN (∼φ) ↔ ¬TrueN φ := by
  simp [TrueN]

/-- A literal of arithmetic with closed arguments. -/
def IsArithLit (φ : Proposition (LIinfN n)) : Prop :=
  ∃ (j : ℕ) (r : Language.Rel ℒₒᵣ j) (v : Fin j → SyntacticTerm (LIinfN n)),
    (φ = Semiformula.rel (Sum.inl r : (LIinfN n).Rel j) v ∨
      φ = Semiformula.nrel (Sum.inl r : (LIinfN n).Rel j) v) ∧
    ∀ i, (v i).freeVariables = ∅

/-- **A true literal of arithmetic**: the empty conjunctions of Definition 5.1 (the false ones
are the empty disjunctions). -/
def TrueLit (φ : Proposition (LIinfN n)) : Prop := IsArithLit φ ∧ TrueN φ

theorem IsArithLit.neg {φ : Proposition (LIinfN n)} (h : IsArithLit φ) : IsArithLit (∼φ) := by
  obtain ⟨j, r, v, (rfl | rfl), hv⟩ := h
  · exact ⟨j, r, v, Or.inr (Semiformula.neg_rel _ _), hv⟩
  · exact ⟨j, r, v, Or.inl (Semiformula.neg_nrel _ _), hv⟩

/-- No literal is true together with its negation. -/
theorem TrueLit.not_neg {φ : Proposition (LIinfN n)} (h : TrueLit φ) : ¬TrueLit (∼φ) :=
  fun h' => (trueN_neg φ).mp h'.2 h.2

theorem IsArithLit.params_eq {φ : Proposition (LIinfN n)} (h : IsArithLit φ) : params φ = ∅ := by
  obtain ⟨j, r, v, (rfl | rfl), -⟩ := h <;> rfl

theorem IsArithLit.capAt_eq {k : Fin n} (b : StageAt k.val) {φ : Proposition (LIinfN n)}
    (h : IsArithLit φ) : capAt k b φ = φ := by
  obtain ⟨j, r, v, (rfl | rfl), -⟩ := h <;> rfl

/-! ### Head symbols -/

/-- The stage of a negated stage atom `¬I_k^{≺α} t`, and `none` for every other formula. -/
def negHeadStage {ξ : Type*} {m : ℕ} : Semiformula (LIinfN n) ξ m → Option (Stage n)
  | .nrel r _ => relStage r
  | _ => none

@[simp] theorem negHeadStage_nstageAt {ξ : Type*} {m : ℕ} (s : Stage n)
    (t : Semiterm (LIinfN n) ξ m) : negHeadStage (nstageAt s t) = some s := rfl

theorem IsArithLit.negHeadStage {φ : Proposition (LIinfN n)} (h : IsArithLit φ) :
    negHeadStage φ = none := by
  obtain ⟨j, r, v, (rfl | rfl), -⟩ := h <;> rfl

theorem nstageAt_inj {ξ : Type*} {m : ℕ} {s s' : Stage n} {t t' : Semiterm (LIinfN n) ξ m}
    (h : nstageAt s t = nstageAt s' t') : s = s' ∧ t = t' := by
  obtain ⟨-, h1, h2⟩ := Semiformula.nrel.inj h
  exact ⟨IInfRelN.stage.inj (Sum.inr_injective (eq_of_heq h1)), congrFun (eq_of_heq h2) 0⟩

theorem stageAt_inj {ξ : Type*} {m : ℕ} {s s' : Stage n} {t t' : Semiterm (LIinfN n) ξ m}
    (h : stageAt s t = stageAt s' t') : s = s' ∧ t = t' := by
  obtain ⟨-, h1, h2⟩ := Semiformula.rel.inj h
  exact ⟨IInfRelN.stage.inj (Sum.inr_injective (eq_of_heq h1)), congrFun (eq_of_heq h2) 0⟩

/-! ### Exercise 5.5 (e), formula half -/

section RankMem

variable {ξ : Type*} {m : ℕ}

theorem _root_.OrdinalAnalysis.ThetaWNoteD.NiceS.omegaBelow_mem
    {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H) (X : Set ThetaWNoteD)
    (j : ℕ) : ThetaWNoteD.OmegaBelow j ∈ H X := by
  cases j with
  | zero => exact hH.zero_mem
  | succ j => exact hH.Omega_mem j

theorem _root_.OrdinalAnalysis.ThetaWNoteD.NiceS.atomRkStage_mem
    {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H) {X : Set ThetaWNoteD}
    {s : Stage n} (hs : s.val ∈ H X) : atomRkStage s ∈ H X :=
  hH.add_mem (hH.omegaBelow_mem X s.lvl.val) (hH.omegaMul_mem hs)

/-- **Freund, Exercise 5.5 (e)**: for a nice operator, `k(ψ)`'s values in `H(X)` give
`rk(ψ) ∈ H(X)`. -/
theorem _root_.OrdinalAnalysis.ThetaWNoteD.NiceS.rk_mem
    {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H) {X : Set ThetaWNoteD}
    {φ : Semiformula (LIinfN n) ξ m} (h : ∀ s ∈ params φ, s.val ∈ H X) : rk φ ∈ H X :=
  rk_mem_of_closed hH.zero_mem (fun _ hx => hH.succ_mem hx)
    (fun s hs => hH.atomRkStage_mem (h s hs))

/-- **Freund, Exercise 5.5 (e)**: `rk(ψ) ∈ H(k(ψ))` for a nice operator. -/
theorem _root_.OrdinalAnalysis.ThetaWNoteD.NiceS.rk_mem_params
    {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    (φ : Semiformula (LIinfN n) ξ m) : rk φ ∈ H (Stage.val '' params φ) :=
  hH.rk_mem (fun s hs => hH.1.subset _ ⟨s, hs, rfl⟩)

end RankMem

end IDn

end OrdinalAnalysis
