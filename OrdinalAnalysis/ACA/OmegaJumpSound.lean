/-
  The omega-jump axiom is true in the full ω-model, and `ACA^+` is consistent.

  `ACA/Standard.lean` proves the calculus of `LK.lean` sound for the full ω-model
  `stdSO` (the standard model of arithmetic with every set of naturals available)
  and checks every axiom of `ACA` true there.  This file adds the one remaining
  axiom of `ACAplus`, `omegaJumpAxiom = ∀Z ∃Y IsOmegaJump(Y, Z)`.

  * **The lifting, evaluated** (`eval_toSOAtB_of`): the second-order formula
    `toSOAtB ψ χ` is true exactly when the first-order `LX`-formula `χ` is true in
    the standard model of `LX` (`Gentzen/StandardLX.lean`'s `stdLX P`) whose fresh
    predicate `X` is read as the set `P` defined by the witness `ψ`.
  * **The jump is extensional** (`eval_jump_std`): in `stdLX P`, Gentzen's jump of a
    formula `φ` depends on `φ` only through the predicate it defines, namely it is
    `JumpRel (fun y => φ(y))`, Gentzen's jump computed in the standard model.
  * **The omega-jump** of `Z` is the set
    `omegaJumpSet Z := {Nat.pair k x | x ∈ hierSet Z k}`, where `hierSet Z 0 = Z` and
    `hierSet Z (k + 1) = {x | JumpRel (· ∈ hierSet Z k) x}`.  Foundation's pairing `pair` is
    Cantor's `Nat.pair` on `ℕ` (`pair_eq_natPair`), so column `k` of `omegaJumpSet Z`
    is `hierSet Z k`; both conjuncts of `IsOmegaJump` follow.

  With `Standard.soundness_of`, every `ACAplus`-theorem is true in `stdSO`, and `⊥`
  is not (`ACAplus_consistent`).  The order of the two set quantifiers matters here:
  the axiom is evaluated as `∀Z ∃Y`, the inner `∃²` binding the slot `0` read by
  `yWit2`.
-/
import OrdinalAnalysis.ACA.OmegaJumpInduction
import OrdinalAnalysis.ACA.Standard
import OrdinalAnalysis.Gentzen.StandardLX

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX XRel Xat toLX paLX)
open OrdinalAnalysis.Gentzen.StandardLX (stdLX)
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁)
open OrdinalAnalysis.Gentzen.CodedVeblenJump (addCode₁ omegaPowCode₁)

/-! ### The lifting, evaluated in the full model -/

/-- **Erasing `X` from a term does not change its value** in any standard model of
`LX`. -/
theorem val_unTerm (P : ℕ → Prop) {n : ℕ} (e : Fin n → ℕ) (f : ℕ → ℕ) :
    ∀ t : FirstOrder.Semiterm LX ℕ n,
      (unTerm t).val e f = FirstOrder.Semiterm.val (s := stdLX P) e f t
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .func (Sum.inl fn) v => by
      have ih : (fun i => (unTerm (v i)).val e f) =
          (fun i => FirstOrder.Semiterm.val (s := stdLX P) e f (v i)) :=
        funext fun i => val_unTerm P e f (v i)
      show FirstOrder.Structure.func (M := ℕ) fn (fun i => (unTerm (v i)).val e f) = _
      rw [ih]
      rfl
  | .func (Sum.inr fn) _ => fn.elim

section EvalToSOAtB

variable {N : ℕ} (ψ : Semiformula ℒₒᵣ ℕ Empty N 1) (F : ℕ → Set ℕ) (E : Fin N → Set ℕ)
  (f : ℕ → ℕ) (P : ℕ → Prop)
  (hP : ∀ x, (FirstOrder.Rewriting.emb ψ : Semiformula ℒₒᵣ ℕ ℕ N 1).Eval
    (Set.univ : Set (Set ℕ)) F f E ![x] ↔ P x)

include hP in
/-- **The lifting at `ψ` is truth in `stdLX P`**, for `P` the set defined by `ψ`. -/
theorem eval_toSOAtB_of : ∀ {n : ℕ} (e : Fin n → ℕ) (χ : FirstOrder.Semiformula LX ℕ n),
    (toSOAtB ψ χ).Eval (Set.univ : Set (Set ℕ)) F f E e ↔
      FirstOrder.Semiformula.Eval (s := stdLX P) e f χ
  | _, _, .verum => Iff.rfl
  | _, _, .falsum => Iff.rfl
  | _, e, .rel (Sum.inl r) v => by
      show (Semiformula.rel r (fun i => unTerm (v i)) : Semiformula ℒₒᵣ ℕ ℕ N _).Eval
        _ F f E e ↔ _
      have hv : (fun i => (unTerm (v i)).val e f) =
          (fun i => FirstOrder.Semiterm.val (s := stdLX P) e f (v i)) :=
        funext fun i => val_unTerm P e f (v i)
      simp only [Semiformula.eval_rel, Function.comp_def, hv]
      rfl
  | _, e, .nrel (Sum.inl r) v => by
      show (Semiformula.nrel r (fun i => unTerm (v i)) : Semiformula ℒₒᵣ ℕ ℕ N _).Eval
        _ F f E e ↔ _
      have hv : (fun i => (unTerm (v i)).val e f) =
          (fun i => FirstOrder.Semiterm.val (s := stdLX P) e f (v i)) :=
        funext fun i => val_unTerm P e f (v i)
      simp only [Semiformula.eval_nrel, Function.comp_def, hv]
      rfl
  | _, e, .rel (Sum.inr XRel.X) v => by
      show ((FirstOrder.Rewriting.emb ψ : Semiformula ℒₒᵣ ℕ ℕ N 1)/[unTerm (v 0)]).Eval
        _ F f E e ↔ _
      rw [eval_subst₁, hP, val_unTerm P e f (v 0)]
      exact Iff.rfl
  | _, e, .nrel (Sum.inr XRel.X) v => by
      show (∼((FirstOrder.Rewriting.emb ψ : Semiformula ℒₒᵣ ℕ ℕ N 1)/[unTerm (v 0)])).Eval
        _ F f E e ↔ _
      rw [LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, eval_subst₁, hP,
        val_unTerm P e f (v 0)]
      exact Iff.of_eq rfl
  | _, e, .and φ χ => by
      show (toSOAtB ψ φ ⋏ toSOAtB ψ χ).Eval _ F f E e ↔
        FirstOrder.Semiformula.Eval (s := stdLX P) e f (φ ⋏ χ)
      simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
        eval_toSOAtB_of e φ, eval_toSOAtB_of e χ]
  | _, e, .or φ χ => by
      show (toSOAtB ψ φ ⋎ toSOAtB ψ χ).Eval _ F f E e ↔
        FirstOrder.Semiformula.Eval (s := stdLX P) e f (φ ⋎ χ)
      simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
        eval_toSOAtB_of e φ, eval_toSOAtB_of e χ]
  | _, e, .all φ => by
      show (∀¹ (toSOAtB ψ φ)).Eval _ F f E e ↔
        FirstOrder.Semiformula.Eval (s := stdLX P) e f (∀¹ φ)
      simp only [Semiformula.eval_fal₀, FirstOrder.Semiformula.eval_all,
        fun x => eval_toSOAtB_of (x :> e) φ]
  | _, e, .exs φ => by
      show (∃¹ (toSOAtB ψ φ)).Eval _ F f E e ↔
        FirstOrder.Semiformula.Eval (s := stdLX P) e f (∃¹ φ)
      simp only [Semiformula.eval_exs₀, FirstOrder.Semiformula.eval_ex,
        fun x => eval_toSOAtB_of (x :> e) φ]

end EvalToSOAtB

/-! ### Codes, numerals and pairing in the standard models of `LX` -/

section Codes

/-- A reference standard model of `LX`; the codes do not mention `X`, so their
reading is the same in every `stdLX P`. -/
abbrev refLX : FirstOrder.Structure LX ℕ := stdLX (fun _ => False)

/-- A coded formula (a `liftCode`) reads the same in every standard model of `LX`, under
every assignment. -/
theorem eval_liftCode_std {n : ℕ} (σ : FirstOrder.Semisentence ℒₒᵣ n)
    (P : ℕ → Prop) (v : Fin n → ℕ) (f : ℕ → ℕ) :
    FirstOrder.Semiformula.Eval (s := stdLX P) v f (Gentzen.CodedNotation.liftCode σ) ↔
      FirstOrder.Semiformula.Eval (s := refLX) v (fun _ => 0)
        (Gentzen.CodedNotation.liftCode σ) := by
  simp only [Gentzen.CodedNotation.liftCode, Gentzen.StandardLX.eval_lMap_toLX,
    FirstOrder.Semiformula.eval_emb]

/-- `y ≺₁ x`, in the standard model. -/
def precN (y x : ℕ) : Prop :=
  FirstOrder.Semiformula.Eval (s := refLX) ![y, x] (fun _ => 0) precCode₁

/-- `z = b ⊕ u`, in the standard model. -/
def addN (z b u : ℕ) : Prop :=
  FirstOrder.Semiformula.Eval (s := refLX) ![z, b, u] (fun _ => 0) addCode₁

/-- `u = ω^a`, in the standard model. -/
def omegaPowN (u a : ℕ) : Prop :=
  FirstOrder.Semiformula.Eval (s := refLX) ![u, a] (fun _ => 0) omegaPowCode₁

/-- **Gentzen's jump of a predicate `Q`, in the standard model**:
`x ∈ Jump(Q)` iff every initial segment below `b` inside `Q` extends to `b ⊕ ω^x`. -/
def JumpRel (Q : ℕ → Prop) (x : ℕ) : Prop :=
  ∀ b u z, omegaPowN u x → addN z b u → (∀ y, precN y b → Q y) → ∀ y, precN y z → Q y

theorem JumpRel_congr {Q Q' : ℕ → Prop} (h : ∀ y, Q y ↔ Q' y) (x : ℕ) :
    JumpRel Q x ↔ JumpRel Q' x := by
  simp only [JumpRel, h]

/-- **The jump is extensional**: in `stdLX P`, the jump of `φ` is the jump of the
predicate `φ` defines. -/
theorem eval_jump_std (P : ℕ → Prop) (φ : FirstOrder.Semiformula LX ℕ 1) (f : ℕ → ℕ)
    (x : ℕ) :
    FirstOrder.Semiformula.Eval (s := stdLX P) ![x] f
        (Gentzen.jump precCode₁ addCode₁ omegaPowCode₁ φ) ↔
      JumpRel (fun y => FirstOrder.Semiformula.Eval (s := stdLX P) ![y] f φ) x := by
  let _ : FirstOrder.Structure LX ℕ := stdLX P
  have hp : ∀ y x' : ℕ, FirstOrder.Semiformula.Eval ![y, x'] f precCode₁ ↔ precN y x' :=
    fun y x' => eval_liftCode_std _ P _ f
  have ha : ∀ z b u : ℕ, FirstOrder.Semiformula.Eval ![z, b, u] f addCode₁ ↔ addN z b u :=
    fun z b u => eval_liftCode_std _ P _ f
  have ho : ∀ u a : ℕ, FirstOrder.Semiformula.Eval ![u, a] f omegaPowCode₁ ↔ omegaPowN u a :=
    fun u a => eval_liftCode_std _ P _ f
  simp only [Gentzen.jump, Gentzen.jumpAt, FirstOrder.Semiformula.eval_all,
    LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq,
    Gentzen.eval_omegaPowAt, Gentzen.eval_addAt, Gentzen.eval_belowAt,
    FirstOrder.Semiterm.val_bvar, FirstOrder.Semiterm.val_bShift, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_fin_one, hp, ha, ho, JumpRel]
  constructor
  · intro h b u z hom hadd hb
    rcases h b u z with h | h | h | h
    · exact absurd hom h
    · exact absurd hadd h
    · exact absurd hb h
    · exact h
  · intro h b u z
    by_cases hom : omegaPowN u x
    · by_cases hadd : addN z b u
      · by_cases hb : ∀ y, precN y b → FirstOrder.Semiformula.Eval ![y] f φ
        · exact Or.inr (Or.inr (Or.inr (h b u z hom hadd hb)))
        · exact Or.inr (Or.inr (Or.inl hb))
      · exact Or.inr (Or.inl hadd)
    · exact Or.inl hom

/-- Foundation's pairing on `ℕ` is Cantor's `Nat.pair`. -/
theorem pair_eq_natPair (k x : ℕ) : (FirstOrder.Arithmetic.pair k x : ℕ) = Nat.pair k x := by
  simp [FirstOrder.Arithmetic.pair, Nat.pair]

theorem eval_pairCode_std (P : ℕ → Prop) (p k x : ℕ) (f : ℕ → ℕ) :
    FirstOrder.Semiformula.Eval (s := stdLX P) ![p, k, x] f pairCode ↔ p = Nat.pair k x := by
  simp only [pairCode, Gentzen.CodedNotation.liftCode, Gentzen.StandardLX.eval_lMap_toLX,
    FirstOrder.Semiformula.eval_emb]
  rw [← pair_eq_natPair]
  exact (FirstOrder.Arithmetic.pair_defined (V := ℕ)).df ![p, k, x]

theorem val_zero_std (P : ℕ → Prop) {n : ℕ} (e : Fin n → ℕ) (f : ℕ → ℕ) :
    FirstOrder.Semiterm.val (s := stdLX P) e f ((0 : ℕ) : FirstOrder.Semiterm LX ℕ n) = 0 := by
  rw [← Gentzen.OmegaTower.lMap_numeral, Gentzen.StandardLX.val_lMap_toLX]
  simp

theorem lMap_succ_one :
    FirstOrder.Semiterm.lMap toLX (‘(#0 + 1)’ : FirstOrder.Semiterm ℒₒᵣ ℕ 1) =
      (‘(#0 + 1)’ : FirstOrder.Semiterm LX ℕ 1) := by
  simp [FirstOrder.Semiterm.Operator.operator, FirstOrder.Semiterm.Operator.numeral,
    FirstOrder.Semiterm.Operator.One.term_eq, FirstOrder.Semiterm.Operator.Add.term_eq, toLX]
  apply funext
  rw [Fin.forall_fin_two]
  constructor
  · simp [Function.comp_def]
  · simp [Function.comp_def]
    exact Matrix.empty_eq _

theorem val_succ_std (P : ℕ → Prop) (k : ℕ) (f : ℕ → ℕ) :
    FirstOrder.Semiterm.val (s := stdLX P) ![k] f (‘(#0 + 1)’ : FirstOrder.Semiterm LX ℕ 1) =
      k + 1 := by
  rw [← lMap_succ_one, Gentzen.StandardLX.val_lMap_toLX]
  simp

end Codes

/-! ### The omega-jump of a set -/

section OmegaJumpSet

/-- The finite jump hierarchy of `Z`: `hierSet Z 0 = Z`, `hierSet Z (k + 1)` the jump of
`hierSet Z k`. -/
def hierSet (Z : Set ℕ) : ℕ → Set ℕ
  | 0 => Z
  | k + 1 => {x | JumpRel (· ∈ hierSet Z k) x}

/-- **The omega-jump of `Z`**: column `k` is `hierSet Z k`. -/
def omegaJumpSet (Z : Set ℕ) : Set ℕ := {p | ∃ k x, p = Nat.pair k x ∧ x ∈ hierSet Z k}

theorem natPair_mem_omegaJumpSet (Z : Set ℕ) (k x : ℕ) :
    Nat.pair k x ∈ omegaJumpSet Z ↔ x ∈ hierSet Z k := by
  constructor
  · rintro ⟨k', x', h, hx⟩
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp h
    exact hx
  · exact fun hx => ⟨k, x, rfl, hx⟩

/-- Column `k` of `omegaJumpSet Z`, read by `columnXat` in `stdLX`, is `hierSet Z k`. -/
theorem colE_omegaJumpSet (Z : Set ℕ) (f : ℕ → ℕ) (k x : ℕ) :
    @ColumnTower.colE ℕ (stdLX (· ∈ omegaJumpSet Z)) f k x ↔ x ∈ hierSet Z k := by
  unfold ColumnTower.colE
  constructor
  · rintro ⟨p, hp, hY⟩
    rw [eval_pairCode_std] at hp
    subst hp
    exact (natPair_mem_omegaJumpSet Z k x).mp hY
  · intro hx
    exact ⟨Nat.pair k x, (eval_pairCode_std _ _ _ _ f).mpr rfl,
      (natPair_mem_omegaJumpSet Z k x).mpr hx⟩

end OmegaJumpSet

/-! ### The omega-jump axiom is true -/

/-- **Every set has an omega-jump**, in the full ω-model. -/
theorem eval_omegaJumpAxiom : SOTrue omegaJumpAxiom := by
  intro F f
  show (∀² (∃² IsOmegaJump) : Proposition ℒₒᵣ).Eval (Set.univ : Set (Set ℕ)) F f ![] ![]
  simp only [Semiformula.eval_fal₁, Semiformula.eval_exs₁]
  intro Z _
  refine ⟨omegaJumpSet Z, Set.mem_univ _, ?_⟩
  have hP : ∀ x, (FirstOrder.Rewriting.emb yWit2 : Semiformula ℒₒᵣ ℕ ℕ 2 1).Eval
      (Set.univ : Set (Set ℕ)) F f (omegaJumpSet Z :> Z :> ![]) ![x] ↔
        x ∈ omegaJumpSet Z := by
    intro x
    simp [yWit2]
  show (hierBase ⋏ hierStep).Eval _ F f _ _
  rw [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  constructor
  · show (∀¹ ((toSOAtB yWit2 hierBaseColLX : Semiproposition ℒₒᵣ 2 1) 🡘
      ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (1 : Fin 2)))).Eval _ F f _ _
    simp only [Semiformula.eval_fal₀, LogicalConnective.HomClass.map_iff,
      LogicalConnective.Prop.iff_eq]
    intro x
    rw [eval_toSOAtB_of yWit2 F _ f (· ∈ omegaJumpSet Z) hP]
    let _ : FirstOrder.Structure LX ℕ := stdLX (· ∈ omegaJumpSet Z)
    rw [hierBaseColLX, ColumnTower.eval_columnXat, val_zero_std]
    simp only [FirstOrder.Semiterm.val_bvar, Matrix.cons_val_fin_one]
    rw [colE_omegaJumpSet]
    simp [hierSet]
  · show (toSOAtB yWit2 ColumnTower.stepHypLX : Semiproposition ℒₒᵣ 2 0).Eval _ F f _ _
    rw [eval_toSOAtB_of yWit2 F _ f (· ∈ omegaJumpSet Z) hP]
    let _ : FirstOrder.Structure LX ℕ := stdLX (· ∈ omegaJumpSet Z)
    rw [ColumnTower.eval_stepHypLX]
    intro k x
    rw [ColumnTower.succE, val_succ_std, colE_omegaJumpSet, jumpColumnFree, eval_jump_std]
    show JumpRel (· ∈ hierSet Z k) x ↔ _
    refine JumpRel_congr (fun y => ?_) x
    rw [columnXatFree, ColumnTower.eval_columnXat]
    simp only [FirstOrder.Semiterm.val_fvar, FirstOrder.Semiterm.val_bvar,
      Matrix.cons_val_fin_one]
    rw [colE_omegaJumpSet]
    rfl

/-! ### Soundness and consistency of `ACA^+` -/

/-- **Every axiom of `ACAplus` is true in the full ω-model.** -/
theorem eval_ACAplus {χ : Proposition ℒₒᵣ} (h : χ ∈ ACAplus) : SOTrue χ := by
  rcases h with h | h
  · exact eval_ACA h
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact eval_omegaJumpAxiom

/-- **`ACA^+ ⊢ φ ⇒ ℕ ⊧ φ`.** -/
theorem soundness_ACAplus {φ : Proposition ℒₒᵣ} (h : Provable ACAplus φ) : SOTrue φ :=
  soundness_of (fun _ hχ => eval_ACAplus hχ) h

/-- **`ACA^+` is consistent.** -/
theorem ACAplus_consistent : ¬Provable ACAplus ⊥ := by
  intro h
  have := soundness_ACAplus h (fun _ => ∅) (fun _ => 0)
  simp at this

/-- **`ACA_0^+` is consistent.** -/
theorem ACAplus₀_consistent : ¬Provable ACAplus₀ ⊥ := fun h =>
  ACAplus_consistent (acaplus_of_acaplus₀ h)

end OrdinalAnalysis.ACA
