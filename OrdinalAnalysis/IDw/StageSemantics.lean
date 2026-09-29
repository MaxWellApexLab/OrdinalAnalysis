/- Source: OrdinalAnalysis/IDn/StageSemantics.lean (ID_n -> ID_omega: levels `k : ℕ`, one uniform form
`A : FormJ`, new atoms `Jlev ℓ`; the design notes "Stage semantics"). -/

/-
  The stage semantics of `ID_ω^∞`, and soundness below `Ω₁`.

  This is the `ID_ω` analogue of `OrdinalAnalysis.IDn.StageSemantics` (and of
  `OrdinalAnalysis.ID1.StageSemantics`). Source for the one-level construction:
  A. Freund, *Impredicativity and trees with gap condition: a second course on ordinal
  analysis*, arXiv:2204.09321, §5; Buchholz, *A simplified version of local predicativity*
  (1992), §3–4 (Thm 4.9 (6)–(8): the level-0 collapse ends in the stage model, with cuts).

  **The stages, iterated over the levels `k : ℕ`.**  There is one uniform form `A : FormJ`
  (`A(x, y)`, with the two schema predicates `P` and `Q` of `LForm`); level `k`'s stages are

      S^k_a  :=  ⋃_{γ≺a} Γ_k(S^k_γ),      Γ_k(T)  =  { x | A(x, k)  with  P := T,  Q := J^{≺k} },

  where `J^{≺k}(j, t) :⇔ j < k ∧ t ∈ S^j_{Ω_{j+1}}` (the *full* stage set of the lower level `j`).
  Level `k`'s stages are built by well-founded recursion on the notations *within* the level
  (`stageWithin`, the direct analogue of `ID1.stageSet`), reading the lower levels' full sets
  from a table; the table itself is built by a second, outer recursion on `k : ℕ`
  (`stageFamily`, plain strong recursion, **no level `ω`**: `Q` only ever reads levels `j < k`,
  a fact built into `J^{≺k}`, so there is no boundedness side condition to state or discharge
  — the `IDn` hypothesis `FamilyLevelBounded` is gone). No positivity of `A` is needed for this
  recursion, and none for soundness: the stage rules are sound because the stages satisfy their
  defining equation.

  **The stage model** `stageModelN P A` is the `LIinfW`-structure on `ℕ` with standard
  arithmetic, `X` read by `P`, every stage predicate `I_k^{≺a}` (`a ⪯ Ω_{k+1}`) read by
  `stageSetN A ⟨k,a⟩`, and

      Jlev ℓ (s, t)   read as   val s < ℓ  ∧  val t ∈ stageSetN A (Stage.top (val s))

  (`ℓ : WithTop ℕ`; `Jlev ⊤` is the full `J`, `Jlev k` is `J^{≺k}`): "`val s < ℓ` and `t ∈ I_{val s}`",
  with `I_j` the full stage set of level `j`, as the design and the two rules (jlev)/(njlev) have
  it. The reduct of the stage model along `formHomAt k a` (`P ↦ I_k^{≺a}`, `Q ↦ Jlev k`) is exactly
  the structure `Γ_k` is defined in (`lMap_formHomAt_stageStrucN`), so the (stage)/(nstage) rules
  are sound by the defining equation `mem_stageSetN_iff`. At `a = Ω_{k+1}` the set
  `⋃_{γ≺Ω_{k+1}} Γ_k(S^k_γ)` is in general not closed under `Γ_k`; this is why (Fix_k) is not
  sound at any level, and why soundness is only claimed for heights `α ≺ Ω₁` — which excludes
  every level's (Fix), since (Fix_k) needs `Ω_{k+1} ⪯ α` and `Ω_{k+1} ⪰ Ω₁` for every `k`.

  **Soundness** (`sound`): if `H ⊢^α_ρ Γ` (`IDwDerivable A ρ H α Γ`) and `α ≺ Ω₁`, then some
  formula of `Γ` is true in the stage model, for every `ρ`, `H` and `P` (free variables read as
  `0`). Cuts are sound whatever their rank. The two new rules are sound by the reading of `Jlev`:
  (jlev) from `I_{val s} t ⇒ Jlev ℓ (s,t)` (given `val s < ℓ`), (njlev) from the reading being
  `false` at `val s ≥ ℓ` and equal to `I_{val s} t` at `val s < ℓ`.

  Contents.

    `iinfStrucN`, `stageStrucN`                          `X ↦ P`, `I_k^{≺a} ↦ S ⟨k,a⟩`, `Jlev ℓ ↦ …`
    `val_stageStrucN_congr`, `val_numeral_stageStrucN`    term values
    `eval_stageAt`, `eval_XinfAt`, `eval_jlevAt`          the fresh atoms
    `pqStruc`, `formStruc`, `opA`                         the operator `Γ_k` of level `k`
    `lMap_formHomAt_stageStrucN`, `eval_unfold`           `A(t, k̄; I_k^{≺a}, Jlev k)`
    `stageWithin`, `stageFamily`, `stageSetN`             **the iterated stages**
    `stageWithin_eq`, `mem_stageWithin_iff`, `stageFamily_eq`, `mem_stageSetN_iff`
    `stageModelN`, `TrueSN`                               the stage model and truth in it
    `omega_zero_le`                                       `Ω₁ ⪯ Ω_{k+1}` for every level `k`
    `sound`                                                **the truth lemma**
-/
import OrdinalAnalysis.IDw.Calculus
import OrdinalAnalysis.IDw.Sound
import OrdinalAnalysis.Ordinal.ThetaV.WellFoundedV

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace StageSem

open LO LO.FirstOrder

/-! ### Structures reading the stages by a given family of sets -/

/-- The fresh symbols of `LIinfW`: `X` read by `P`, the stage `I_k^{≺a}` by `S ⟨k,a⟩`, and
`Jlev ℓ (s, t)` as "`val s < ℓ` and `val t ∈ S (top (val s))`" (the full stage set of level
`val s`). -/
@[instance_reducible]
def iinfStrucN (P : ℕ → Prop) (S : Stage → Set ℕ) : Structure IInfLangW ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ r v => match r with
    | IInfRelW.X => P (v 0)
    | IInfRelW.stage s => v 0 ∈ S s
    | IInfRelW.jlev ℓ => ((v 0 : ℕ) : WithTop ℕ) < ℓ ∧ v 1 ∈ S (Stage.top (v 0))

/-- The `LIinfW`-structure on `ℕ`: arithmetic standard, `X` read by `P`, `I_k^{≺a}` by
`S ⟨k,a⟩`, `Jlev ℓ` through the full stage sets `S (top j)`. -/
@[instance_reducible]
def stageStrucN (P : ℕ → Prop) (S : Stage → Set ℕ) : Structure LIinfW ℕ :=
  Structure.add ℒₒᵣ IInfLangW ℕ (str₂ := iinfStrucN P S)

section Struc

variable (P : ℕ → Prop) (S : Stage → Set ℕ)

/-- Term values do not depend on the readings of the fresh predicates. -/
theorem val_stageStrucN_congr {ξ : Type*} {m : ℕ} (e : Fin m → ℕ) (f : ξ → ℕ)
    (t : Semiterm LIinfW ξ m) :
    Semiterm.val (s := stageStrucN P S) e f t = Semiterm.val (s := stdW) e f t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func fn v ih =>
      simp only [Semiterm.val_func, Function.comp_def, ih]
      rcases fn with fn | fn
      · rfl
      · exact PEmpty.elim fn

/-- The numerals of `LIinfW` are the images of the numerals of arithmetic
(`IDw.CalculusAux.lMap_toLIinfW_numeral`). -/
theorem numeral_lMap_toLIinfN {ξ : Type*} {m : ℕ} (t : ℕ) :
    Semiterm.lMap toLIinfW ((t : ℕ) : Semiterm ℒₒᵣ ξ m) = ((t : ℕ) : Semiterm LIinfW ξ m) :=
  lMap_toLIinfW_numeral t

/-- **A numeral denotes its value.** -/
@[simp] theorem val_numeral_stageStrucN {ξ : Type*} {m : ℕ} (t : ℕ) (e : Fin m → ℕ)
    (f : ξ → ℕ) :
    Semiterm.val (s := stageStrucN P S) e f ((t : ℕ) : Semiterm LIinfW ξ m) = t := by
  rw [← numeral_lMap_toLIinfN t]
  show Semiterm.val (s := Structure.add ℒₒᵣ IInfLangW ℕ (str₂ := iinfStrucN P S)) e f
    (Semiterm.lMap (Language.Hom.add₁ ℒₒᵣ IInfLangW) ((t : ℕ) : Semiterm ℒₒᵣ ξ m)) = t
  rw [Structure.val_lMap_add₁ (str₂ := iinfStrucN P S)]
  simp

/-- `I_k^{≺a} t` holds when the value of `t` lies in `S ⟨k,a⟩`. -/
theorem eval_stageAt {ξ : Type*} {m : ℕ} (s : Stage) (t : Semiterm LIinfW ξ m)
    (e : Fin m → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stageStrucN P S) e f (stageAt s t) ↔
      Semiterm.val (s := stageStrucN P S) e f t ∈ S s := by
  have h : (Semiterm.val (s := stageStrucN P S) e f ∘ ![t] : Fin 1 → ℕ)
      = ![Semiterm.val (s := stageStrucN P S) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg ((stageStrucN P S).rel (Sum.inr (IInfRelW.stage s))) h)

/-- `X t` holds when `P` holds at the value of `t`. -/
theorem eval_XinfAt {ξ : Type*} {m : ℕ} (t : Semiterm LIinfW ξ m) (e : Fin m → ℕ)
    (f : ξ → ℕ) :
    Semiformula.Eval (s := stageStrucN P S) e f (XinfAt t) ↔
      P (Semiterm.val (s := stageStrucN P S) e f t) := by
  have h : (Semiterm.val (s := stageStrucN P S) e f ∘ ![t] : Fin 1 → ℕ)
      = ![Semiterm.val (s := stageStrucN P S) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg ((stageStrucN P S).rel (Sum.inr IInfRelW.X)) h)

/-- **`Jlev ℓ (s, t)` holds when `val s < ℓ` and the value of `t` lies in the full stage set of
level `val s`.** -/
theorem eval_jlevAt {ξ : Type*} {m : ℕ} (ℓ : WithTop ℕ) (s t : Semiterm LIinfW ξ m)
    (e : Fin m → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stageStrucN P S) e f (jlevAt ℓ s t) ↔
      ((Semiterm.val (s := stageStrucN P S) e f s : ℕ) : WithTop ℕ) < ℓ ∧
        Semiterm.val (s := stageStrucN P S) e f t ∈
          S (Stage.top (Semiterm.val (s := stageStrucN P S) e f s)) := by
  have h : (Semiterm.val (s := stageStrucN P S) e f ∘ ![s, t] : Fin 2 → ℕ)
      = ![Semiterm.val (s := stageStrucN P S) e f s, Semiterm.val (s := stageStrucN P S) e f t] :=
    Matrix.comp₂ s t
  exact Iff.of_eq (congrArg ((stageStrucN P S).rel (Sum.inr (IInfRelW.jlev ℓ))) h)

/-- A closed literal of arithmetic has the truth value it has in `ℕ`. -/
theorem eval_of_trueLit {φ : Proposition LIinfW} (h : TrueLit φ) :
    Semiformula.Eval (s := stageStrucN P S) ![] (fun _ => 0) φ := by
  obtain ⟨⟨j, r, v, hφ, -⟩, ht⟩ := h
  unfold TrueN at ht
  have e : (fun i => Semiterm.val (s := stageStrucN P S) ![] (fun _ => 0) (v i)) =
      (fun i => Semiterm.val (s := stdW) ![] (fun _ => 0) (v i)) := by
    funext i
    exact val_stageStrucN_congr P S _ _ (v i)
  rcases hφ with rfl | rfl
  · have ht' : Structure.rel (L := ℒₒᵣ) (M := ℕ) r
        (fun i => Semiterm.val (s := stdW) ![] (fun _ => 0) (v i)) := ht
    show Structure.rel (L := ℒₒᵣ) (M := ℕ) r
      (fun i => Semiterm.val (s := stageStrucN P S) ![] (fun _ => 0) (v i))
    rw [e]
    exact ht'
  · have ht' : ¬Structure.rel (L := ℒₒᵣ) (M := ℕ) r
        (fun i => Semiterm.val (s := stdW) ![] (fun _ => 0) (v i)) := ht
    show ¬Structure.rel (L := ℒₒᵣ) (M := ℕ) r
      (fun i => Semiterm.val (s := stageStrucN P S) ![] (fun _ => 0) (v i))
    rw [e]
    exact ht'

end Struc

/-! ### The operator of level `k`, and the unfolding under the stage structure -/

section Operator

/-- The fresh symbols of `LForm`: `P` read by the set `T`, `Q` by the binary relation `Qr`. -/
@[instance_reducible]
def pqStruc (T : Set ℕ) (Qr : ℕ → ℕ → Prop) : Structure PQLang ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ r v => match r with
    | PQRel.P => v 0 ∈ T
    | PQRel.Q => Qr (v 0) (v 1)

/-- The `LForm`-structure on `ℕ`: arithmetic standard, `P` read by `T`, `Q` by `Qr`. -/
@[instance_reducible]
def formStruc (T : Set ℕ) (Qr : ℕ → ℕ → Prop) : Structure LForm ℕ :=
  Structure.add ℒₒᵣ PQLang ℕ (str₂ := pqStruc T Qr)

/-- **The operator of level `k`** `Γ_k(T)`, with the lower levels read from the table `L`:
`x ∈ Γ_k(T)` iff `A(x, k)` holds with `P := T` and `Q(j, t) := j < k ∧ t ∈ L j` (`J^{≺k}`, only
the lower levels `j < k` of `L` are ever read). -/
def opA (A : FormJ) (k : ℕ) (T : Set ℕ) (L : ℕ → Set ℕ) : Set ℕ :=
  {x | Semiformula.Eval (s := formStruc T (fun j t => j < k ∧ t ∈ L j)) ![x, k] Empty.elim A}

/-- **`opA` reads only the lower levels of the table**: two tables agreeing below `k` give the
same operator. -/
theorem opA_congr (A : FormJ) (k : ℕ) (T : Set ℕ) {L L' : ℕ → Set ℕ}
    (h : ∀ j, j < k → L j = L' j) : opA A k T L = opA A k T L' := by
  have hQ : (fun (j : ℕ) (t : ℕ) => j < k ∧ t ∈ L j) = (fun j t => j < k ∧ t ∈ L' j) := by
    funext j t
    apply propext
    constructor
    · rintro ⟨hj, ht⟩
      exact ⟨hj, by rw [← h j hj]; exact ht⟩
    · rintro ⟨hj, ht⟩
      exact ⟨hj, by rw [h j hj]; exact ht⟩
  unfold opA
  rw [hQ]

variable (P : ℕ → Prop) (S : Stage → Set ℕ)

/-- **The reduct of the stage structure along `formHomAt k a`** (`P ↦ I_k^{≺a}`, `Q ↦ Jlev k`):
the `LForm`-structure with `P` read by `S ⟨k,a⟩` and `Q` by `J^{≺k}` through the full sets
`S (top j)`. -/
theorem lMap_formHomAt_stageStrucN (k : ℕ) (a : StageAt k) :
    (stageStrucN P S).lMap (formHomAt k a) =
      formStruc (S (⟨k, a⟩ : Stage)) (fun j t => j < k ∧ t ∈ S (Stage.top j)) := by
  have hf : ((stageStrucN P S).lMap (formHomAt k a)).func =
      (formStruc (S (⟨k, a⟩ : Stage)) (fun j t => j < k ∧ t ∈ S (Stage.top j))).func := by
    funext m fn v
    rcases fn with fn | fn
    · rfl
    · exact PEmpty.elim fn
  have hr : ((stageStrucN P S).lMap (formHomAt k a)).rel =
      (formStruc (S (⟨k, a⟩ : Stage)) (fun j t => j < k ∧ t ∈ S (Stage.top j))).rel := by
    funext m r v
    rcases r with r | r
    · rfl
    · cases r with
      | P => rfl
      | Q =>
        show (((v 0 : ℕ) : WithTop ℕ) < ((k : ℕ) : WithTop ℕ) ∧ v 1 ∈ S (Stage.top (v 0))) =
          (v 0 < k ∧ v 1 ∈ S (Stage.top (v 0)))
        exact propext (and_congr WithTop.coe_lt_coe Iff.rfl)
  cases h : (stageStrucN P S).lMap (formHomAt k a)
  cases h' : formStruc (S (⟨k, a⟩ : Stage)) (fun j t => j < k ∧ t ∈ S (Stage.top j))
  rw [h] at hf hr
  rw [h'] at hf hr
  cases hf
  cases hr
  rfl

/-- **`A(t, k̄; I_k^{≺a}, Jlev k)` holds exactly when the value of `t` is in the operator of
level `k` applied to `S ⟨k,a⟩`, the lower levels read through the full sets `S (top j)`.** -/
theorem eval_unfold (A : FormJ) (k : ℕ) (a : StageAt k)
    {ξ : Type*} {m : ℕ} (t : Semiterm LIinfW ξ m) (e : Fin m → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stageStrucN P S) e f (unfoldW A k a t) ↔
      Semiterm.val (s := stageStrucN P S) e f t ∈
        opA A k (S (⟨k, a⟩ : Stage)) (fun j => S (Stage.top j)) := by
  rw [unfoldW]
  show Semiformula.Eval (s := stageStrucN P S) e f
      ((Rewriting.emb (formAtW A k a) : Semiformula LIinfW ξ 2) ⇜ ![t, (Semiterm.numeral k : Semiterm LIinfW ξ m)]) ↔ _
  rw [Semiformula.eval_substs, Semiformula.eval_emb, formAtW, Semiformula.eval_lMap,
    lMap_formHomAt_stageStrucN]
  have hv : (Semiterm.val (s := stageStrucN P S) e f ∘
      ![t, (Semiterm.numeral k : Semiterm LIinfW ξ m)] : Fin 2 → ℕ) =
      ![Semiterm.val (s := stageStrucN P S) e f t, k] := by
    funext i
    fin_cases i
    · rfl
    · exact val_numeral_stageStrucN P S k e f
  rw [hv]
  rfl

end Operator

/-! ### The stages, iterated over the levels -/

section Stages

variable (A : FormJ)

/-- **The within-level stages of level `k`**, given the table `L` of the lower levels' full
stage sets (only `L j`, `j < k`, is ever read): `S^k_a := ⋃_{γ≺a} Γ_k(S^k_γ)`, by well-founded
recursion on the notations `a ⪯ Ω_{k+1}`. The direct analogue of `ID1.stageSet`. -/
noncomputable def stageWithin (k : ℕ) (L : ℕ → Set ℕ) : StageAt k → Set ℕ :=
  WellFounded.fix (wellFounded_lt (α := StageAt k))
    (fun a rec => ⋃ g : StageAt k, ⋃ (h : g < a), opA A k (rec g h) L)

/-- The defining equation of the within-level stages. -/
theorem stageWithin_eq (k : ℕ) (L : ℕ → Set ℕ) (a : StageAt k) :
    stageWithin A k L a = ⋃ g : StageAt k, ⋃ (_ : g < a), opA A k (stageWithin A k L g) L :=
  WellFounded.fix_eq _ _ a

theorem mem_stageWithin_iff (k : ℕ) (L : ℕ → Set ℕ) (a : StageAt k) (x : ℕ) :
    x ∈ stageWithin A k L a ↔ ∃ g : StageAt k, g < a ∧ x ∈ opA A k (stageWithin A k L g) L := by
  rw [stageWithin_eq]
  simp only [Set.mem_iUnion, exists_prop]

/-- **The iterated stage family**, level by level: level `k`'s within-level recursion is fed the
table of the strictly lower levels' *full* stage sets, themselves built the same way — plain
strong recursion on `k : ℕ` (no level `ω`), the analogue of `IDw.lfpChain`, generalised from
"the least fixed point of level `k`" to "the whole stage family of level `k`". -/
noncomputable def stageFamily : ∀ k : ℕ, StageAt k → Set ℕ :=
  WellFounded.fix (wellFounded_lt (α := ℕ))
    (fun k rec => stageWithin A k (fun j => if hj : j < k then rec j hj (StageAt.top j) else ∅))

theorem stageFamily_eq (k : ℕ) :
    stageFamily A k =
      stageWithin A k (fun j => if _hj : j < k then stageFamily A j (StageAt.top j) else ∅) :=
  WellFounded.fix_eq _ _ k

/-- **The stages `S_{k,a}` of `ID_ω`**, combined into one family over `Stage`, for the stage
model. -/
noncomputable def stageSetN (s : Stage) : Set ℕ := stageFamily A s.1 s.2

@[simp] theorem stageSetN_top (k : ℕ) :
    stageSetN A (Stage.top k) = stageFamily A k (StageAt.top k) := rfl

/-- **The defining equation of the combined stages**: `I_k^{≺a}`'s stage is the union, over
`γ ≺ a`, of the operator of level `k` applied to `I_k^{≺γ}`'s stage, the lower levels read
through their own full stage sets. -/
theorem mem_stageSetN_iff {k : ℕ} (a : StageAt k) (x : ℕ) :
    x ∈ stageSetN A (⟨k, a⟩ : Stage) ↔ ∃ g : StageAt k, g.1 < a.1 ∧
      x ∈ opA A k (stageSetN A (⟨k, g⟩ : Stage)) (fun j => stageSetN A (Stage.top j)) := by
  show x ∈ stageFamily A k a ↔ _
  rw [stageFamily_eq, mem_stageWithin_iff]
  have hcongr : ∀ g : StageAt k,
      stageWithin A k (fun j => if _hj : j < k then stageFamily A j (StageAt.top j) else ∅) g =
        stageFamily A k g :=
    fun g => (congrFun (stageFamily_eq A k).symm g)
  have hL : ∀ (T : Set ℕ), opA A k T
      (fun j => if _hj : j < k then stageFamily A j (StageAt.top j) else ∅) =
      opA A k T (fun j => stageSetN A (Stage.top j)) := fun T =>
    opA_congr A k T (fun j hj => by simp only [dif_pos hj]; rfl)
  constructor
  · rintro ⟨g, hg, hx⟩
    refine ⟨g, hg, ?_⟩
    rw [hcongr g, hL] at hx
    exact hx
  · rintro ⟨g, hg, hx⟩
    refine ⟨g, hg, ?_⟩
    rw [hcongr g, hL]
    exact hx

end Stages

/-! ### The stage model -/

section Model

variable (P : ℕ → Prop) (A : FormJ)

/-- **The stage model**: arithmetic standard, `X` read by `P`, `I_k^{≺a}` read by the stage
`stageSetN A ⟨k,a⟩` for every level `k` and every `a ⪯ Ω_{k+1}`, and `Jlev ℓ (s,t)` by
"`val s < ℓ` and `t ∈ stageSetN A (top (val s))`". -/
@[instance_reducible]
noncomputable def stageModelN : Structure LIinfW ℕ := stageStrucN P (stageSetN A)

/-- Truth in the stage model, free variables read as `0`. -/
def TrueSN (φ : Proposition LIinfW) : Prop :=
  Semiformula.Eval (s := stageModelN P A) ![] (fun _ => 0) φ

theorem trueSN_stageAt (s : Stage) (t : SyntacticTerm LIinfW) :
    TrueSN P A (stageAt s t) ↔
      Semiterm.val (s := stageModelN P A) ![] (fun _ => 0) t ∈ stageSetN A s :=
  eval_stageAt P _ s t _ _

/-- **`Jlev ℓ (s,t)` in the stage model**: `val s < ℓ` and `val t` in the full stage set of level
`val s`. -/
theorem trueSN_jlevAt (ℓ : WithTop ℕ) (s t : SyntacticTerm LIinfW) :
    TrueSN P A (jlevAt ℓ s t) ↔
      ((Semiterm.val (s := stageModelN P A) ![] (fun _ => 0) s : ℕ) : WithTop ℕ) < ℓ ∧
        Semiterm.val (s := stageModelN P A) ![] (fun _ => 0) t ∈
          stageSetN A (Stage.top (Semiterm.val (s := stageModelN P A) ![] (fun _ => 0) s)) :=
  eval_jlevAt P _ ℓ s t _ _

theorem trueSN_unfold (k : ℕ) (g : StageAt k) (t : SyntacticTerm LIinfW) :
    TrueSN P A (unfoldW A k g t) ↔
      Semiterm.val (s := stageModelN P A) ![] (fun _ => 0) t ∈
        opA A k (stageSetN A (⟨k, g⟩ : Stage)) (fun j => stageSetN A (Stage.top j)) :=
  eval_unfold P _ A k g t _ _

theorem trueSN_neg (φ : Proposition LIinfW) : TrueSN P A (∼φ) ↔ ¬TrueSN P A φ := by
  simp [TrueSN]

theorem trueSN_subst_numeral (φ : Semiproposition LIinfW 1) (m : ℕ) :
    TrueSN P A (φ/[numI m]) ↔
      Semiformula.Eval (s := stageModelN P A) ![m] (fun _ => 0) φ := by
  unfold TrueSN
  rw [Semiformula.eval_substs, Matrix.comp₁]
  have h : Semiterm.val (s := stageModelN P A) ![] (fun _ => 0) (numI m) = m :=
    val_numeral_stageStrucN P _ m _ _
  rw [h]

end Model

/-! ### Soundness below `Ω₁` -/

section Soundness

/-- `Ω₁ ⪯ Ω_{k+1}` for every level `k` (the level-0 top is the least of all the tops), so a
height `α ≺ Ω₁` is below every level's `Fix`-threshold. -/
theorem omega_zero_le (k : ℕ) : ThetaVNoteD.Omega 0 ≤ ThetaVNoteD.Omega k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact le_refl _
  · exact le_of_lt (ThetaVNoteD.Omega_lt_Omega_iff.mpr hk)

variable (P : ℕ → Prop) (A : FormJ)

/-- **The truth lemma (Proposition 5.8, at every level)**: a sequent derived at a height
`α ≺ Ω₁` contains a formula true in the stage model, for every cut rank, every operator and
every reading of `X`; in particular for both `Jlev` rules. -/
theorem sound {ρ : ThetaVNoteD} {H : Set ThetaVNoteD → Set ThetaVNoteD}
    {α : ThetaVNoteD} {Γ : Sequent LIinfW} (d : IDwDerivable A ρ H α Γ) :
    α < ThetaVNoteD.Omega 0 → ∃ φ ∈ Γ, TrueSN P A φ := by
  induction d with
  | literal _ _ hφ hm => exact fun _ => ⟨_, hm, eval_of_trueLit P _ hφ⟩
  | verum _ _ hm =>
    intro _
    refine ⟨⊤, hm, ?_⟩
    simp [TrueSN]
  | idX t _ _ h1 h2 =>
    intro _
    by_cases h : TrueSN P A (XinfAt t)
    · exact ⟨_, h1, h⟩
    · exact ⟨_, h2, (trueSN_neg P A _).mpr h⟩
  | @and H α Γ φ ψ α₀ α₁ _ _ hm h0 h1 _ _ ih0 ih1 =>
    intro hα
    obtain ⟨χ₀, hχ₀, t₀⟩ := ih0 (lt_trans h0 hα)
    obtain ⟨χ₁, hχ₁, t₁⟩ := ih1 (lt_trans h1 hα)
    rcases List.mem_cons.mp hχ₀ with rfl | hχ₀
    · rcases List.mem_cons.mp hχ₁ with rfl | hχ₁
      · refine ⟨_, hm, ?_⟩
        unfold TrueSN at t₀ t₁ ⊢
        rw [LogicalConnective.HomClass.map_and]
        exact ⟨t₀, t₁⟩
      · exact ⟨χ₁, hχ₁, t₁⟩
    · exact ⟨χ₀, hχ₀, t₀⟩
  | @orL H α Γ φ ψ α₀ _ _ hm h0 _ ih0 =>
    intro hα
    obtain ⟨χ, hχ, t⟩ := ih0 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ with rfl | hχ
    · refine ⟨_, hm, ?_⟩
      unfold TrueSN at t ⊢
      rw [LogicalConnective.HomClass.map_or]
      exact Or.inl t
    · exact ⟨χ, hχ, t⟩
  | @orR H α Γ φ ψ α₀ _ _ hm _ h0 _ ih0 =>
    intro hα
    obtain ⟨χ, hχ, t⟩ := ih0 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ with rfl | hχ
    · refine ⟨_, hm, ?_⟩
      unfold TrueSN at t ⊢
      rw [LogicalConnective.HomClass.map_or]
      exact Or.inr t
    · exact ⟨χ, hχ, t⟩
  | @all H α Γ φ f _ _ hm hf _ ih =>
    intro hα
    by_cases hΓ : ∃ χ ∈ Γ, TrueSN P A χ
    · exact hΓ
    · refine ⟨_, hm, ?_⟩
      unfold TrueSN
      rw [Semiformula.eval_all]
      intro m
      obtain ⟨χ, hχ, t⟩ := ih m (lt_trans (hf m) hα)
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact (trueSN_subst_numeral P A φ m).mp t
      · exact absurd ⟨χ, hχ, t⟩ hΓ
  | @exs H α Γ φ m α₀ _ _ hm _ h0 _ ih0 =>
    intro hα
    obtain ⟨χ, hχ, t⟩ := ih0 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ with rfl | hχ
    · refine ⟨_, hm, ?_⟩
      unfold TrueSN
      rw [Semiformula.eval_ex]
      exact ⟨m, (trueSN_subst_numeral P A φ m).mp t⟩
    · exact ⟨χ, hχ, t⟩
  | @stage H α Γ k a t g α₀ _ _ hm hga _ _ h0 _ ih0 =>
    intro hα
    obtain ⟨χ, hχ, tr⟩ := ih0 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ with rfl | hχ
    · refine ⟨_, hm, ?_⟩
      rw [trueSN_stageAt, mem_stageSetN_iff A]
      exact ⟨g, hga, (trueSN_unfold P A k g t).mp tr⟩
    · exact ⟨χ, hχ, tr⟩
  | @nstage H α Γ k a t f _ _ hm hf _ ih =>
    intro hα
    by_cases hΓ : ∃ χ ∈ Γ, TrueSN P A χ
    · exact hΓ
    · refine ⟨_, hm, ?_⟩
      rw [← neg_stageAt, trueSN_neg, trueSN_stageAt, mem_stageSetN_iff A]
      rintro ⟨g, hga, hg⟩
      obtain ⟨χ, hχ, tr⟩ := ih g hga (lt_trans (hf g hga) hα)
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact (trueSN_neg P A _).mp tr ((trueSN_unfold P A k g t).mpr hg)
      · exact hΓ ⟨χ, hχ, tr⟩
  | @fix H α Γ k t α₀ _ _ hm hΩ _ _ =>
    intro hα
    exact absurd (lt_of_le_of_lt (le_trans (omega_zero_le k) hΩ) hα) (lt_irrefl _)
  | @jlev H α Γ ℓ s t α₀ _ _ hm _ _ hl h0 _ ih0 =>
    intro hα
    obtain ⟨χ, hχ, tr⟩ := ih0 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ with rfl | hχ
    · refine ⟨_, hm, ?_⟩
      have hv : Semiterm.val (s := stageModelN P A) ![] (fun _ => 0) s = termVal s :=
        val_stageStrucN_congr P _ _ _ s
      rw [trueSN_jlevAt, hv]
      exact ⟨hl, (trueSN_stageAt P A (Stage.top (termVal s)) t).mp tr⟩
    · exact ⟨χ, hχ, tr⟩
  | @njlev H α Γ ℓ s t α₀ _ _ hm _ _ h0 _ ih0 =>
    intro hα
    have hv : Semiterm.val (s := stageModelN P A) ![] (fun _ => 0) s = termVal s :=
      val_stageStrucN_congr P _ _ _ s
    by_cases hl : ((termVal s : ℕ) : WithTop ℕ) < ℓ
    · obtain ⟨χ, hχ, tr⟩ := ih0 hl (lt_trans (h0 hl) hα)
      rcases List.mem_cons.mp hχ with rfl | hχ
      · refine ⟨_, hm, ?_⟩
        rw [← neg_jlevAt, trueSN_neg, trueSN_jlevAt, hv]
        rintro ⟨-, hj⟩
        exact (trueSN_neg P A _).mp tr ((trueSN_stageAt P A (Stage.top (termVal s)) t).mpr hj)
      · exact ⟨χ, hχ, tr⟩
    · refine ⟨_, hm, ?_⟩
      rw [← neg_jlevAt, trueSN_neg, trueSN_jlevAt, hv]
      exact fun h => hl h.1
  | @cut H α Γ ψ α₀ _ _ _ h0 _ _ ih0 ih1 =>
    intro hα
    obtain ⟨χ₀, hχ₀, t₀⟩ := ih0 (lt_trans h0 hα)
    obtain ⟨χ₁, hχ₁, t₁⟩ := ih1 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ₀ with rfl | hχ₀
    · rcases List.mem_cons.mp hχ₁ with rfl | hχ₁
      · exact absurd t₀ ((trueSN_neg P A _).mp t₁)
      · exact ⟨χ₁, hχ₁, t₁⟩
    · exact ⟨χ₀, hχ₀, t₀⟩

end Soundness

end StageSem

end IDw

end OrdinalAnalysis
