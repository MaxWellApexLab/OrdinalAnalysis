/-
  Helper infrastructure for `OrdinalAnalysis.IDw.Calculus`, the `IDw` (`k : ℕ`, ID_ω)
  counterpart of `OrdinalAnalysis.IDn.CalculusAux`.

  Source: the design notes §3.1–§3.2; drafted mechanically from
  `IDn/CalculusAux.lean` by mechanical translation (level `k : Fin n` generalised to `k : ℕ`), then
  hand-completed here: the script cannot produce anything mentioning `Jlev`, so every piece this
  file adds beyond the mechanical rename is new, hand-written content, listed below.

  **Why a separate file** (unchanged from `IDn`).  `IDw/Language.lean`'s `params`/`paramsList`
  return a set of `Stage` (a level *and* a bound), because a sequent of `LIinfW` can mention
  every level at once.  The operator `H : Set ThetaVNoteD → Set ThetaVNoteD` of `IDw/Calculus.lean`
  (one level-free operator, phrased against `ThetaVNoteD.IsOperator`/`NiceS`, `Ordinal/ThetaV/
  HullSingle.lean`/`HullDom.lean`) acts on sets of *bare* `ThetaVNoteD` values.  `paramsVal`
  bridges the two.

  **New beyond the mechanical port** (design §3.2, hand-written).

    * `stdW`, `termVal`         the standard-model value of a *closed* term of `LIinfW`, read
                                 through the same `stdInfN`/`TrueN` pattern this file already uses
                                 for closed *formulas* of arithmetic — needed because the (jlev)/
                                 (njlev) rules' side condition "`val s < ℓ`" (design §3.2) is a
                                 genuine semantic evaluation of the closed term `s`, not a
                                 syntactic numeral check (`s` may be any closed arithmetic term,
                                 e.g. a code for `Ω_y`, design §3.2's third smoke test).
    * `relStage`                 the stage of a stage-relation symbol, `none` for `X`/`Jlev` —
                                 needed for `negHeadStage`, ported unchanged in *shape* from
                                 `IDn.Language` (which had this as a plain top-level `def`, not
                                 carried over by the mechanical Pass-0 stub list since `IDw/
                                 Language.lean` chose not to define it; added here, where it is
                                 actually consumed).
    * `jlevAt_inj`, `njlevAt_inj` head-symbol injectivity for the two new atom formers, the
                                 `Jlev` analogues of `stageAt_inj`/`nstageAt_inj`, needed by the
                                 new inversion lemma `IDwDerivable.inv_njlev` (`Calculus.lean`).
    * `relParams_capRelAt`, `params_capAt`   `capAt`'s effect on parameters, ported from
                                 `IDn.Language`'s `Cap` section (not carried over automatically:
                                 `IDw/Language.lean`'s own `Cap` section stopped at the rank-facing
                                 lemmas needed by stage `L`, design §3.1's own note deferring the
                                 "companion fact for `∼(unfoldW A k g t)`" to `C1`). The `Jlev`
                                 case is immediate: `capRelAt` fixes every `Jlev` symbol
                                 (`capRelAt`'s `jlev` clause, design "`capAt k` is the identity on
                                 `Jlev`"), so `relParams (capRelAt k b (jlev ℓ)) = ∅ ⊆ _` outright.

  Contents.

    `paramsList_nil/cons/append/mono`, `params_subset_paramsList`   generic sequent-parameter
                                                                     lemmas
    `paramsVal`, `paramsVal_nil/cons/append/mono`,
    `mem_paramsVal_of_mem_params`, `paramsVal_map_capAt`            the `Set ThetaVNoteD` view
    `numI`                                                          the numerals
    `iinfFalseW`, `stdW`, `TrueN`, `IsArithLit`, `TrueLit`          the true literals of
                                                                     arithmetic (Definition 5.1)
    `termVal`                                                       the semantic value of a
                                                                     closed term (new, for jlev)
    `relStage`, `negHeadStage`, `nstageAt_inj`, `stageAt_inj`,
    `jlevAt_inj`, `njlevAt_inj`                                      head-symbol lemmas
    `relParams_capRelAt`, `params_capAt`                             `capAt` and parameters
    `rk_IOmegaAt_lt_jlevAt`, `rk_nIOmegaAt_lt_njlevAt`                rank discipline of jlev/njlev
    `ThetaVNoteD.NiceS.omegaBelow_mem`, `atomRkStage_mem`,
    `ThetaVNoteD.adjoin_eq_self`                                     Exercise 5.5 (c), (e)
-/
import OrdinalAnalysis.IDw.Rank
import OrdinalAnalysis.Ordinal.ThetaV.HullDom

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder

/-! ### The parameters of a sequent (not yet in `IDw/Language.lean`) -/

section ParamsList

variable {ξ : Type*} {m : ℕ}

/-- `k(Γ)`, the parameters of a list of formulas (`IDn.paramsList`; `IDw/Language.lean` only
defines `params` of a single formula). -/
def paramsList (Γ : List (Semiformula LIinfW ξ m)) : Set Stage :=
  {s | ∃ φ ∈ Γ, s ∈ params φ}

@[simp] theorem paramsList_nil : paramsList ([] : List (Semiformula LIinfW ξ m)) = ∅ := by
  ext; simp [paramsList]

@[simp] theorem paramsList_cons (φ : Semiformula LIinfW ξ m)
    (Γ : List (Semiformula LIinfW ξ m)) :
    paramsList (φ :: Γ) = params φ ∪ paramsList Γ := by
  ext; simp [paramsList]

@[simp] theorem paramsList_append (Γ Δ : List (Semiformula LIinfW ξ m)) :
    paramsList (Γ ++ Δ) = paramsList Γ ∪ paramsList Δ := by
  ext; simp only [paramsList, List.mem_append, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨φ, (h | h), ha⟩
    · exact Or.inl ⟨φ, h, ha⟩
    · exact Or.inr ⟨φ, h, ha⟩
  · rintro (⟨φ, h, ha⟩ | ⟨φ, h, ha⟩)
    · exact ⟨φ, Or.inl h, ha⟩
    · exact ⟨φ, Or.inr h, ha⟩

theorem paramsList_mono {Γ Δ : List (Semiformula LIinfW ξ m)} (h : Γ ⊆ Δ) :
    paramsList Γ ⊆ paramsList Δ :=
  fun _ ⟨φ, hφ, ha⟩ => ⟨φ, h hφ, ha⟩

theorem params_subset_paramsList {φ : Semiformula LIinfW ξ m}
    {Γ : List (Semiformula LIinfW ξ m)} (h : φ ∈ Γ) : params φ ⊆ paramsList Γ :=
  fun _ ha => ⟨φ, h, ha⟩

/-- `k(φ/[t]) = k(φ)`: single substitution does not see the parameters (`params_subst2`'s unary
companion, for the `∀`-rule's `φ/[m̄]`). -/
theorem params_subst1 (φ : Semiformula LIinfW ξ 1) (t : Semiterm LIinfW ξ m) :
    params (φ/[t]) = params φ := params_rew _ φ

end ParamsList

/-! ### The `Set ThetaVNoteD` view of a sequent's parameters -/

section ParamsVal

variable {ξ : Type*} {m : ℕ}

/-- **`k(Γ)` with the level tag erased.** -/
def paramsVal (Γ : List (Semiformula LIinfW ξ m)) : Set ThetaVNoteD :=
  Stage.val '' paramsList Γ

@[simp] theorem paramsVal_nil : paramsVal ([] : List (Semiformula LIinfW ξ m)) = ∅ := by
  simp [paramsVal]

theorem paramsVal_cons (φ : Semiformula LIinfW ξ m) (Γ : List (Semiformula LIinfW ξ m)) :
    paramsVal (φ :: Γ) = Stage.val '' params φ ∪ paramsVal Γ := by
  rw [paramsVal, paramsList_cons, Set.image_union, paramsVal]

theorem paramsVal_append (Γ Δ : List (Semiformula LIinfW ξ m)) :
    paramsVal (Γ ++ Δ) = paramsVal Γ ∪ paramsVal Δ := by
  rw [paramsVal, paramsList_append, Set.image_union, paramsVal, paramsVal]

theorem paramsVal_mono {Γ Δ : List (Semiformula LIinfW ξ m)} (h : Γ ⊆ Δ) :
    paramsVal Γ ⊆ paramsVal Δ :=
  fun _ ⟨s, hs, hx⟩ => ⟨s, paramsList_mono h hs, hx⟩

theorem mem_paramsVal_of_mem_params {s : Stage} {φ : Semiformula LIinfW ξ m}
    {Γ : List (Semiformula LIinfW ξ m)} (hφ : φ ∈ Γ) (hs : s ∈ params φ) :
    s.val ∈ paramsVal Γ :=
  ⟨s, params_subset_paramsList hφ hs, rfl⟩

theorem params_val_subset_paramsVal {φ : Semiformula LIinfW ξ m}
    {Γ : List (Semiformula LIinfW ξ m)} (h : φ ∈ Γ) :
    Stage.val '' params φ ⊆ paramsVal Γ :=
  fun _ ⟨s, hs, hx⟩ => ⟨s, params_subset_paramsList h hs, hx⟩

end ParamsVal

/-! ### The numerals -/

/-- The numeral `n̄`. -/
abbrev numI (t : ℕ) : SyntacticTerm LIinfW := Semiterm.numeral t

/-! ### The true literals of arithmetic, and the standard-model value of a closed term -/

/-- The fresh symbols read as empty; only the arithmetic part matters for the literals below and
for `termVal`. -/
@[instance_reducible]
def iinfFalseW : Structure IInfLangW ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ _ _ => False

/-- The standard structure: arithmetic standard, `X`, every stage and every `Jlev` empty. -/
@[instance_reducible]
def stdW : Structure LIinfW ℕ := Structure.add ℒₒᵣ IInfLangW ℕ (str₂ := iinfFalseW)

/-- Truth of a formula in `stdW` under the zero assignment; for closed formulas of arithmetic
this is truth in `ℕ`. -/
def TrueN (φ : Proposition LIinfW) : Prop :=
  Semiformula.Eval (s := stdW) ![] (fun _ => 0) φ

@[simp] theorem trueN_neg (φ : Proposition LIinfW) : TrueN (∼φ) ↔ ¬TrueN φ := by
  simp [TrueN]

/-- **The standard-model value of a closed term of `LIinfW`** — `IInfLangW` contributes no
function symbols (`Func := fun _ => PEmpty`), so `termVal` only ever evaluates the arithmetic
part of `t`, exactly as `TrueN` only ever evaluates the arithmetic part of a literal. Needed for
the (jlev)/(njlev) rules' side condition "`val s < ℓ`" (design §3.2): `s` ranges over an
arbitrary closed term of `LIinfW`, not necessarily a numeral (design's third smoke test uses a
"code of `Ω_y`" term), so the level it denotes must be read off semantically. -/
def termVal (t : SyntacticTerm LIinfW) : ℕ := Semiterm.val (s := stdW) ![] (fun _ => 0) t

/-! ### Numerals denote their values, and are closed
(the `IDw` copy of the `Numeral`/`NumeralFreeVariables` sections of `IDn/Evaluate.lean`; the C2
port of `Evaluate` must skip them) -/

section Numeral

variable {ξ : Type*} {m : ℕ}

private lemma lMapNumW_zero :
    Semiterm.lMap toLIinfW ((0 : ℕ) : Semiterm ℒₒᵣ ξ m) = ((0 : ℕ) : Semiterm LIinfW ξ m) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, toLIinfW]

private lemma lMapNumW_one :
    Semiterm.lMap toLIinfW ((1 : ℕ) : Semiterm ℒₒᵣ ξ m) = ((1 : ℕ) : Semiterm LIinfW ξ m) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, toLIinfW]

private lemma lMapNumW_add (v : Fin 2 → Semiterm ℒₒᵣ ξ m) :
    Semiterm.lMap toLIinfW (Semiterm.Operator.Add.add.operator v) =
      Semiterm.Operator.Add.add.operator (Semiterm.lMap toLIinfW ∘ v) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, toLIinfW]
  funext i
  simp

private lemma numeralW_succ_succ (L : Language) [L.Zero] [L.One] [L.Add] (t : ℕ) :
    ((t + 1 + 1 : ℕ) : Semiterm L ξ m) =
      Semiterm.Operator.Add.add.operator
        ![((t + 1 : ℕ) : Semiterm L ξ m), ((1 : ℕ) : Semiterm L ξ m)] := by
  have h : t + 1 ≠ 0 := Nat.succ_ne_zero t
  simp only [Semiterm.numeral, Semiterm.Operator.const,
    Semiterm.Operator.numeral_succ h, Semiterm.Operator.operator_comp]
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- The numerals of `LIinfW` are the numerals of arithmetic. -/
theorem lMap_toLIinfW_numeral (t : ℕ) :
    Semiterm.lMap toLIinfW ((t : ℕ) : Semiterm ℒₒᵣ ξ m) = ((t : ℕ) : Semiterm LIinfW ξ m) := by
  induction t with
  | zero => exact lMapNumW_zero
  | succ t ih =>
    cases t with
    | zero => exact lMapNumW_one
    | succ t =>
      rw [numeralW_succ_succ ℒₒᵣ t, numeralW_succ_succ LIinfW t, lMapNumW_add]
      congr 1
      funext i
      match i with
      | ⟨0, _⟩ => exact ih
      | ⟨1, _⟩ => exact lMapNumW_one

/-- **A numeral denotes its value** in the standard structure. -/
@[simp] theorem val_numeral_stdW (p : ℕ) (e : Fin m → ℕ) (ε : ξ → ℕ) :
    Semiterm.val (s := stdW) e ε ((p : ℕ) : Semiterm LIinfW ξ m) = p := by
  rw [← lMap_toLIinfW_numeral p]
  show Semiterm.val (s := Structure.add ℒₒᵣ IInfLangW ℕ (str₂ := iinfFalseW)) e ε
    (Semiterm.lMap (Language.Hom.add₁ ℒₒᵣ IInfLangW) ((p : ℕ) : Semiterm ℒₒᵣ ξ m)) = p
  rw [Structure.val_lMap_add₁ (str₂ := iinfFalseW)]
  simp

/-- A numeral at any level has no free variable. -/
theorem numeral_freeVariables (p : ℕ) {m : ℕ} :
    ((p : ℕ) : Semiterm LIinfW ℕ m).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hx' : ((Rew.subst ![]) (Rew.emb (Semiterm.Operator.numeral LIinfW p).term) :
      Semiterm LIinfW ℕ m).FVar? x := hx
  rcases Semiterm.fvar?_rew hx' with ⟨i, -⟩ | ⟨z, hz, -⟩
  · exact i.elim0
  · have hz' : z ∈ (Rew.emb (Semiterm.Operator.numeral LIinfW p).term :
        Semiterm LIinfW ℕ 0).freeVariables := hz
    simp at hz'

end Numeral

/-- A literal of arithmetic with closed arguments. -/
def IsArithLit (φ : Proposition LIinfW) : Prop :=
  ∃ (j : ℕ) (r : Language.Rel ℒₒᵣ j) (v : Fin j → SyntacticTerm LIinfW),
    (φ = Semiformula.rel (Sum.inl r : LIinfW.Rel j) v ∨
      φ = Semiformula.nrel (Sum.inl r : LIinfW.Rel j) v) ∧
    ∀ i, (v i).freeVariables = ∅

/-- **A true literal of arithmetic**: the empty conjunctions of Definition 5.1 (the false ones
are the empty disjunctions). -/
def TrueLit (φ : Proposition LIinfW) : Prop := IsArithLit φ ∧ TrueN φ

theorem IsArithLit.neg {φ : Proposition LIinfW} (h : IsArithLit φ) : IsArithLit (∼φ) := by
  obtain ⟨j, r, v, (rfl | rfl), hv⟩ := h
  · exact ⟨j, r, v, Or.inr (Semiformula.neg_rel _ _), hv⟩
  · exact ⟨j, r, v, Or.inl (Semiformula.neg_nrel _ _), hv⟩

/-- No literal is true together with its negation. -/
theorem TrueLit.not_neg {φ : Proposition LIinfW} (h : TrueLit φ) : ¬TrueLit (∼φ) :=
  fun h' => (trueN_neg φ).mp h'.2 h.2

theorem IsArithLit.params_eq {φ : Proposition LIinfW} (h : IsArithLit φ) : params φ = ∅ := by
  obtain ⟨j, r, v, (rfl | rfl), -⟩ := h <;> rfl

theorem IsArithLit.capAt_eq {k : ℕ} (b : StageAt k) {φ : Proposition LIinfW}
    (h : IsArithLit φ) : capAt k b φ = φ := by
  obtain ⟨j, r, v, (rfl | rfl), -⟩ := h <;> rfl

/-! ### Head symbols -/

theorem numI_freeVariables (p : ℕ) : (numI p).freeVariables = ∅ := numeral_freeVariables p

@[simp] theorem val_numI (p : ℕ) (e : Fin 0 → ℕ) (ε : ℕ → ℕ) :
    Semiterm.val (s := stdW) e ε (numI p) = p := val_numeral_stdW p e ε

@[simp] theorem termVal_numI (p : ℕ) : termVal (numI p) = p := val_numI p _ _

/-- The stage of a stage-relation symbol, `none` for `X` and every `Jlev`. -/
def relStage : {k : ℕ} → LIinfW.Rel k → Option Stage
  | _, Sum.inl _ => none
  | _, Sum.inr IInfRelW.X => none
  | _, Sum.inr (IInfRelW.stage s) => some s
  | _, Sum.inr (IInfRelW.jlev _) => none

/-- The stage of a negated stage atom `¬I_k^{≺α} t`, and `none` for every other formula
(including `¬Jlev ℓ (s,t)`, design: `Jlev` "is not a stage-family index"). -/
def negHeadStage {ξ : Type*} {m : ℕ} : Semiformula LIinfW ξ m → Option Stage
  | .nrel r _ => relStage r
  | _ => none

@[simp] theorem negHeadStage_nstageAt {ξ : Type*} {m : ℕ} (s : Stage)
    (t : Semiterm LIinfW ξ m) : negHeadStage (nstageAt s t) = some s := rfl

@[simp] theorem negHeadStage_njlevAt {ξ : Type*} {m : ℕ} (ℓ : WithTop ℕ)
    (s t : Semiterm LIinfW ξ m) : negHeadStage (njlevAt ℓ s t) = none := rfl

theorem IsArithLit.negHeadStage {φ : Proposition LIinfW} (h : IsArithLit φ) :
    negHeadStage φ = none := by
  obtain ⟨j, r, v, (rfl | rfl), -⟩ := h <;> rfl

theorem nstageAt_inj {ξ : Type*} {m : ℕ} {s s' : Stage} {t t' : Semiterm LIinfW ξ m}
    (h : nstageAt s t = nstageAt s' t') : s = s' ∧ t = t' := by
  obtain ⟨-, h1, h2⟩ := Semiformula.nrel.inj h
  exact ⟨IInfRelW.stage.inj (Sum.inr_injective (eq_of_heq h1)), congrFun (eq_of_heq h2) 0⟩

theorem stageAt_inj {ξ : Type*} {m : ℕ} {s s' : Stage} {t t' : Semiterm LIinfW ξ m}
    (h : stageAt s t = stageAt s' t') : s = s' ∧ t = t' := by
  obtain ⟨-, h1, h2⟩ := Semiformula.rel.inj h
  exact ⟨IInfRelW.stage.inj (Sum.inr_injective (eq_of_heq h1)), congrFun (eq_of_heq h2) 0⟩

/-- **Head-symbol injectivity for `Jlev`** (new, needed by `inv_njlev`): `Jlev ℓ (s,t) = Jlev ℓ'
(s',t')` gives `ℓ = ℓ'`, `s = s'`, `t = t'`. -/
theorem jlevAt_inj {ξ : Type*} {m : ℕ} {ℓ ℓ' : WithTop ℕ} {s s' t t' : Semiterm LIinfW ξ m}
    (h : jlevAt ℓ s t = jlevAt ℓ' s' t') : ℓ = ℓ' ∧ s = s' ∧ t = t' := by
  obtain ⟨-, h1, h2⟩ := Semiformula.rel.inj h
  refine ⟨IInfRelW.jlev.inj (Sum.inr_injective (eq_of_heq h1)), ?_, ?_⟩
  · exact congrFun (eq_of_heq h2) 0
  · exact congrFun (eq_of_heq h2) 1

theorem njlevAt_inj {ξ : Type*} {m : ℕ} {ℓ ℓ' : WithTop ℕ} {s s' t t' : Semiterm LIinfW ξ m}
    (h : njlevAt ℓ s t = njlevAt ℓ' s' t') : ℓ = ℓ' ∧ s = s' ∧ t = t' := by
  obtain ⟨-, h1, h2⟩ := Semiformula.nrel.inj h
  refine ⟨IInfRelW.jlev.inj (Sum.inr_injective (eq_of_heq h1)), ?_, ?_⟩
  · exact congrFun (eq_of_heq h2) 0
  · exact congrFun (eq_of_heq h2) 1

/-- **A coarse shape tag for the head relation of a `rel`/`nrel` atom** (new, for `inv_njlev`).
Comparing two atoms that are both `rel` or both `nrel` but come from *different* fresh-relation
families (e.g. `¬Jlev ℓ (s,t)` against `¬X(t)`, or against `¬I_k^{≺a} t`) cannot be settled by
`nomatch` alone (both sides use the same `Semiformula` constructor), and going through
`Semiformula.rel.inj`/`nrel.inj` directly would additionally have to equate the two symbols'
*arities* first (`Jlev` is binary, `X`/a stage atom unary) before any `HEq` becomes a plain `Eq` —
comparing this simple, arity-blind tag instead (via `decide`) sidesteps both issues at once. -/
inductive AtomShape
  | arith | freeX | freeStage | freeJlev | other
  deriving DecidableEq

def relShape : {k : ℕ} → LIinfW.Rel k → AtomShape
  | _, Sum.inl _ => .arith
  | _, Sum.inr IInfRelW.X => .freeX
  | _, Sum.inr (IInfRelW.stage _) => .freeStage
  | _, Sum.inr (IInfRelW.jlev _) => .freeJlev

/-- The shape tag of a formula's head relation, for `rel`/`nrel`; `.other` for everything else
(`⊤`, `⊥`, `∧`, `∨`, `∀`, `∃`). -/
def atomShape {ξ : Type*} {m : ℕ} : Semiformula LIinfW ξ m → AtomShape
  | .rel r _ => relShape r
  | .nrel r _ => relShape r
  | _ => .other

@[simp] theorem atomShape_jlevAt {ξ : Type*} {m : ℕ} (ℓ : WithTop ℕ) (s t : Semiterm LIinfW ξ m) :
    atomShape (jlevAt ℓ s t) = .freeJlev := rfl

@[simp] theorem atomShape_njlevAt {ξ : Type*} {m : ℕ} (ℓ : WithTop ℕ)
    (s t : Semiterm LIinfW ξ m) : atomShape (njlevAt ℓ s t) = .freeJlev := rfl

@[simp] theorem atomShape_Xat {ξ : Type*} {m : ℕ} (t : Semiterm LIinfW ξ m) :
    atomShape (XinfAt t) = .freeX := rfl

@[simp] theorem atomShape_nXat {ξ : Type*} {m : ℕ} (t : Semiterm LIinfW ξ m) :
    atomShape (∼(XinfAt t)) = .freeX := rfl

@[simp] theorem atomShape_stageAt {ξ : Type*} {m : ℕ} (s : Stage) (t : Semiterm LIinfW ξ m) :
    atomShape (stageAt s t) = .freeStage := rfl

@[simp] theorem atomShape_nstageAt {ξ : Type*} {m : ℕ} (s : Stage) (t : Semiterm LIinfW ξ m) :
    atomShape (nstageAt s t) = .freeStage := rfl

theorem IsArithLit.atomShape_eq {φ : Proposition LIinfW} (h : IsArithLit φ) :
    atomShape φ = .arith := by
  obtain ⟨j, r, v, (rfl | rfl), -⟩ := h <;> rfl

/-- `Jlev`/`¬Jlev` atoms are never true literals of arithmetic. -/
theorem not_trueLit_jlevAt (ℓ : WithTop ℕ) (s t : SyntacticTerm LIinfW) :
    ¬ TrueLit (jlevAt ℓ s t) :=
  fun h => absurd h.1.atomShape_eq (by simp)

theorem not_trueLit_njlevAt (ℓ : WithTop ℕ) (s t : SyntacticTerm LIinfW) :
    ¬ TrueLit (njlevAt ℓ s t) :=
  fun h => absurd h.1.atomShape_eq (by simp)

/-! ### `capAt` and the parameters -/

section Cap

variable (k : ℕ) (b : StageAt k)

/-- `k(r^β) ⊆ k(r) ∪ {(k,β)}`, at the level of a single relation symbol. The `Jlev` case is
immediate: `capRelAt` fixes every `Jlev` symbol (design: "`capAt k` is the identity on `Jlev`"),
so `relParams (capRelAt k b (jlev ℓ)) = ∅` regardless. -/
theorem relParams_capRelAt : ∀ {j : ℕ} (r : LIinfW.Rel j),
    relParams (capRelAt k b r) ⊆ relParams r ∪ {(⟨k, b⟩ : Stage)}
  | _, Sum.inl _ => Set.empty_subset _
  | _, Sum.inr IInfRelW.X => Set.empty_subset _
  | _, Sum.inr (IInfRelW.stage s) => by
    rw [capRelAt_stage]
    split_ifs with h
    · exact fun x hx => Or.inr hx
    · exact fun x hx => Or.inl hx
  | _, Sum.inr (IInfRelW.jlev _) => Set.empty_subset _

/-- `k(φ^β) ⊆ k(φ) ∪ {(k,β)}`, at level `k` (design §3.1; the "companion fact for `∼(unfoldW A k
g t)`" deferred there to this stage). -/
theorem params_capAt {ξ : Type*} {m : ℕ} (φ : Semiformula LIinfW ξ m) :
    params (capAt k b φ) ⊆ params φ ∪ {(⟨k, b⟩ : Stage)} := by
  induction φ using Semiformula.rec' with
  | hverum => exact Set.empty_subset _
  | hfalsum => exact Set.empty_subset _
  | hrel r v => exact relParams_capRelAt k b r
  | hnrel r v => exact relParams_capRelAt k b r
  | hand φ ψ ihφ ihψ =>
    rw [capAt_and, params_and, params_and]
    exact Set.union_subset (ihφ.trans (Set.union_subset_union_left _ Set.subset_union_left))
      (ihψ.trans (Set.union_subset_union_left _ Set.subset_union_right))
  | hor φ ψ ihφ ihψ =>
    rw [capAt_or, params_or, params_or]
    exact Set.union_subset (ihφ.trans (Set.union_subset_union_left _ Set.subset_union_left))
      (ihψ.trans (Set.union_subset_union_left _ Set.subset_union_right))
  | hall φ ih => exact ih
  | hexs φ ih => exact ih

theorem paramsVal_map_capAt (Θ : Sequent LIinfW) :
    paramsVal (Θ.map (capAt k b)) ⊆ paramsVal Θ ∪ {b.1} := by
  rintro x ⟨s, ⟨φ, hφ, hs⟩, rfl⟩
  obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hφ
  rcases params_capAt k b χ hs with h | h
  · exact Or.inl (mem_paramsVal_of_mem_params hχ h)
  · right
    rw [Set.mem_singleton_iff] at h
    subst h
    rfl

end Cap

/-! ### Exercise 5.5 (e), formula half — `atomRkStage` only; `rk_mem`/`rk_mem_params` NOT ported

**Deviation from `IDn.CalculusAux`, flagged, not silently ported.** `IDn.rk_mem_of_closed`
(hence `NiceS.rk_mem`/`rk_mem_params`) concludes `rk φ ∈ S` from membership of *only* `atomRkStage
s` for `s ∈ params φ`. That hypothesis says nothing about any `Jlev` atom `φ` may contain
(`params (Jlev …) = ∅`, `IDw.Language`), so the naive port is **false** here: a bare `Jlev ⊤`
atom has `rk = OmegaW`, not bounded by any `S` closed only under the stage atoms' ranks and `+1`.
This is exactly the honesty issue `IDw/Rank.lean` already flagged for `rk_lt_Omega_iff`/
`rk_le_add_ofNat` (see that file's header); the fix needs an extra hypothesis about every `Jlev`
atom of `φ`, which is not needed by anything in this stage (`C1`: `Calculus`/`CalculusAux`/
`CalculusSmoke` never call `rk_mem`/`rk_mem_params`) and is deferred to whichever later stage
first needs it (`C2`/`C3`, boundedness or cut elimination), to be designed against the concrete
shape those proofs actually require. `omegaBelow_mem`/`atomRkStage_mem` below have no such issue
(they never go through `rk`) and are kept. -/

section RankMem

theorem _root_.OrdinalAnalysis.ThetaVNoteD.NiceS.omegaBelow_mem
    {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H) (X : Set ThetaVNoteD)
    (j : ℕ) : ThetaVNoteD.OmegaBelow j ∈ H X := by
  cases j with
  | zero => exact hH.zero_mem
  | succ j => exact hH.Omega_mem j

theorem _root_.OrdinalAnalysis.ThetaVNoteD.NiceS.atomRkStage_mem
    {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H) {X : Set ThetaVNoteD}
    {s : Stage} (hs : s.val ∈ H X) : atomRkStage s ∈ H X :=
  hH.add_mem (hH.omegaBelow_mem X s.lvl) (hH.omegaMul_mem hs)

/-- **Freund, Exercise 5.5 (e), formula half, for `LIinfW`**: `rk φ ∈ H(X)` for a nice `H` once
the values of `φ`'s stage parameters are in `H(X)`. The `Jlev ℓ` atoms (no parameters) have rank
`Ω_ω` or `Ω_k + 1`, in every nice `H(X)` (`NiceS.OmegaW_mem`, `NiceS.omegaBelow_mem`,
`NiceS.succ_mem`) — so, unlike the bare-`S` form `IDn.rk_mem_of_closed` (not ported, see above),
the `NiceS` form holds verbatim.  **The single copy**: `NiceS.rk_memL` (`IDw/AxiomsLogic.lean`),
`NiceS.rk_mem_of_noJlevTop` (`IDw/PredCutAux.lean`), `rk_mem_pa` (`IDw/AxiomsPA.lean`) and
`rk_mem` (`IDw/TransferAux.lean`) are one-line consequences of it. -/
theorem _root_.OrdinalAnalysis.ThetaVNoteD.NiceS.rk_mem' {ξ : Type*} {m : ℕ}
    {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H) {X : Set ThetaVNoteD}
    {φ : Semiformula LIinfW ξ m} (h : ∀ s ∈ params φ, s.val ∈ H X) : rk φ ∈ H X := by
  have hmax : ∀ x y : ThetaVNoteD, x ∈ H X → y ∈ H X → max x y ∈ H X := fun x y hx hy => by
    rcases le_total x y with hxy | hxy
    · rw [max_eq_right hxy]; exact hy
    · rw [max_eq_left hxy]; exact hx
  have hJ : ∀ ℓ : WithTop ℕ, atomRkJlev ℓ ∈ H X := fun ℓ => by
    induction ℓ using WithTop.recTopCoe with
    | top => exact hH.OmegaW_mem
    | coe k => exact hH.succ_mem (hH.omegaBelow_mem X k)
  induction φ using Semiformula.rec' with
  | hverum => rw [rk_verum]; exact hH.zero_mem
  | hfalsum => rw [rk_falsum]; exact hH.zero_mem
  | hrel r v =>
    rw [rk_rel]
    rcases r with r | r
    · exact hH.zero_mem
    · cases r with
      | X => exact hH.zero_mem
      | stage s => exact hH.atomRkStage_mem (h s rfl)
      | jlev ℓ => exact hJ ℓ
  | hnrel r v =>
    rw [rk_nrel]
    rcases r with r | r
    · exact hH.zero_mem
    · cases r with
      | X => exact hH.zero_mem
      | stage s => exact hH.atomRkStage_mem (h s rfl)
      | jlev ℓ => exact hJ ℓ
  | hand φ ψ ihφ ihψ =>
    rw [rk_and]
    exact hH.succ_mem (hmax _ _ (ihφ fun s hs => h s (Or.inl hs)) (ihψ fun s hs => h s (Or.inr hs)))
  | hor φ ψ ihφ ihψ =>
    rw [rk_or]
    exact hH.succ_mem (hmax _ _ (ihφ fun s hs => h s (Or.inl hs)) (ihψ fun s hs => h s (Or.inr hs)))
  | hall φ ih => rw [rk_all]; exact hH.succ_mem (ih h)
  | hexs φ ih => rw [rk_exs]; exact hH.succ_mem (ih h)

end RankMem

/-! ### The rank discipline of `jlev`/`njlev` (design §8.4 kill criterion)

The premise of `(jlev)`/`(njlev)` at a level `j < ℓ` has strictly smaller rank than the principal
atom: `rk (I_j t) = Ω_{j+1}` against `rk (Jlev ℓ (s,t)) = Ω_ℓ + 1` (`ℓ : ℕ`, `Ω_ℓ = OmegaBelow ℓ`)
or `Ω_ω` (`ℓ = ⊤`). -/

section RankDiscipline

variable {ξ : Type*} {m : ℕ}

theorem rk_IOmegaAt_lt_jlevAt {ℓ : WithTop ℕ} {j : ℕ} (h : (j : WithTop ℕ) < ℓ)
    (t : Semiterm LIinfW ξ m) (s' t' : Semiterm LIinfW ξ m) :
    rk (IOmegaAt j t) < rk (jlevAt ℓ s' t') := by
  rw [rk_IOmegaAt, rk_jlevAt]
  induction ℓ using WithTop.recTopCoe with
  | top => exact ThetaVNoteD.Omega_lt_OmegaW j
  | coe k =>
    exact lt_of_le_of_lt (ThetaVNoteD.Omega_le_OmegaBelow_of_lt (WithTop.coe_lt_coe.mp h))
      (ThetaVNoteD.lt_succ _)

theorem rk_nIOmegaAt_lt_njlevAt {ℓ : WithTop ℕ} {j : ℕ} (h : (j : WithTop ℕ) < ℓ)
    (t : Semiterm LIinfW ξ m) (s' t' : Semiterm LIinfW ξ m) :
    rk (∼(IOmegaAt j t)) < rk (njlevAt ℓ s' t') := by
  rw [rk_neg, rk_njlevAt, ← rk_jlevAt ℓ s' t']
  exact rk_IOmegaAt_lt_jlevAt h t s' t'

end RankDiscipline

/-! ### Exercise 5.5 (c) for the level-free operator (`ThetaW/Hull.lean` has it; `ThetaV/HullSingle`
does not yet, so it lives here) -/

/-- Exercise 5.5 (c): `H[Z] = H` when `Z ⊆ H(∅)`. -/
theorem _root_.OrdinalAnalysis.ThetaVNoteD.adjoin_eq_self
    {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.IsOperator H)
    {Z : Set ThetaVNoteD} (hZ : Z ⊆ H ∅) : ThetaVNoteD.adjoin H Z = H := by
  funext X
  exact le_antisymm
    (hH.2 _ _ (Set.union_subset (hZ.trans (hH.mono (Set.empty_subset X))) (hH.1 X)))
    (hH.mono Set.subset_union_right)

end IDw

end OrdinalAnalysis
