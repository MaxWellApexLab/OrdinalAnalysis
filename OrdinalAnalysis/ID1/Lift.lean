/-
  Models of `ID₁` with standard arithmetic, and the passage from truth in all of them to
  provability.

  **Arithmetically standard structures.**  An `LXI`-structure on a type `N` carrying an
  `ORingStructure` is *arithmetically standard* (`ArithStd`) when its reduct to `ℒₒᵣ` is the
  structure of the arithmetic operations of `N`.  Every `LXI`-structure whose equality is true
  equality is of this form, for the operations it defines itself (`arithStd_of`), so
  by Foundation's completeness theorem:

  * a sentence true in every arithmetically standard model of `ID1Acc prec` is a theorem of
    `ID1Acc prec` (`provable_of_models`).

  **Inside such a model** `N` (the model-theoretic route of `Ramified.provable_of_eqModels`):
  write `I x` and `X x` for the two predicates and `x ≺ y` for `prec`.

  * `N` is a model of `PA`, in particular of `IΣ₁` (`models_peano`, `models_iSigma₁`): the
    arithmetic axioms and the arithmetic instances of induction are axioms of `ID1Acc prec`;
  * `I` is closed: `(∀y ≺ x, I y) → I x` (`imem_of_forall`);
  * the induction scheme of `I` holds for every predicate definable in `LXI` with parameters
    (`ind_definable`): if `Q` is progressive along `≺` then `I ⊆ Q`;
  * induction along the numbers holds for every such predicate (`succ_induction_definable`,
    `order_induction_definable`).

  A predicate is definable when it is defined by a formula whose free variables are indexed by
  `N` itself (Foundation's `Language.Definable`); such a formula becomes an instance of the
  axiom schemes by numbering its finitely many free variables (`exists_nat_formula`).
-/
import OrdinalAnalysis.ID1.Theory
import OrdinalAnalysis.ID1.Internal.Codes
import Foundation.FirstOrder.Completeness

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

namespace Lift

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### Arithmetically standard structures -/

/-- The `ℒₒᵣ`-reduct of the `LXI`-structure is the arithmetic of `N`. -/
class ArithStd (N : Type*) [ORingStructure N] [s : Structure LXI N] : Prop where
  lMap_eq : s.lMap toLXI = Arithmetic.standardModel N

section Std

variable {N : Type*} [ORingStructure N] [s : Structure LXI N] [ArithStd N]

/-- Arithmetic terms have their arithmetic values. -/
theorem val_lMap_toLXI {ξ : Type*} {n : ℕ} (t : Semiterm ℒₒᵣ ξ n) (e : Fin n → N) (f : ξ → N) :
    Semiterm.val (s := s) e f (Semiterm.lMap toLXI t) = Semiterm.val (s := standardModel N) e f t := by
  rw [Semiterm.val_lMap, ArithStd.lMap_eq]

/-- Arithmetic formulas say what they say in the arithmetic of `N`. -/
theorem eval_lMap_toLXI {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) (e : Fin n → N)
    (f : ξ → N) :
    Semiformula.Eval (s := s) e f (Semiformula.lMap toLXI φ) ↔
      Semiformula.Eval (s := standardModel N) e f φ := by
  rw [Semiformula.eval_lMap, ArithStd.lMap_eq]

/-- The predicate read by `I`. -/
def Imem (x : N) : Prop := s.rel (Sum.inr IXRel.I) ![x]

/-- The predicate read by `X`. -/
def Xmem (x : N) : Prop := s.rel (Sum.inr IXRel.X) ![x]

omit [ORingStructure N] [ArithStd N] in
theorem eval_Iat {ξ : Type*} {n : ℕ} (t : Semiterm LXI ξ n) (e : Fin n → N) (f : ξ → N) :
    Semiformula.Eval (s := s) e f (Iat t) ↔ Imem (Semiterm.val (s := s) e f t) := by
  have h : (Semiterm.val (s := s) e f ∘ ![t] : Fin 1 → N)
      = ![Semiterm.val (s := s) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg (s.rel (Sum.inr IXRel.I)) h)

omit [ORingStructure N] [ArithStd N] in
theorem eval_Xat {ξ : Type*} {n : ℕ} (t : Semiterm LXI ξ n) (e : Fin n → N) (f : ξ → N) :
    Semiformula.Eval (s := s) e f (Xat t) ↔ Xmem (Semiterm.val (s := s) e f t) := by
  have h : (Semiterm.val (s := s) e f ∘ ![t] : Fin 1 → N)
      = ![Semiterm.val (s := s) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg (s.rel (Sum.inr IXRel.X)) h)

end Std

/-! ### From truth in the arithmetically standard models to provability -/

section Complete

variable {M : Type*} (s : Structure LXI M)

set_option warn.classDefReducibility false in
/-- The arithmetic operations of an `LXI`-structure. -/
@[reducible] def oringOf : ORingStructure M where
  zero := s.func (Language.Zero.zero : LXI.Func 0) ![]
  one := s.func (Language.One.one : LXI.Func 0) ![]
  add a b := s.func (Language.Add.add : LXI.Func 2) ![a, b]
  mul a b := s.func (Language.Mul.mul : LXI.Func 2) ![a, b]
  lt a b := s.rel (Language.LT.lt : LXI.Rel 2) ![a, b]

/-- An `LXI`-structure with true equality is arithmetically standard for its own
operations. -/
theorem arithStd_of (hEq : ∀ a b : M, s.rel (Language.Eq.eq : LXI.Rel 2) ![a, b] ↔ a = b) :
    letI := oringOf s; ArithStd M := by
  let _ := oringOf s
  refine ⟨Structure.ext (funext₃ fun k f v => ?_) (funext₃ fun k r v => ?_)⟩
  · match k, f with
    | _, Language.ORing.Func.zero =>
      show s.func (Language.Zero.zero : LXI.Func 0) v = s.func (Language.Zero.zero : LXI.Func 0) ![]
      rw [Matrix.empty_eq v]
    | _, Language.ORing.Func.one =>
      show s.func (Language.One.one : LXI.Func 0) v = s.func (Language.One.one : LXI.Func 0) ![]
      rw [Matrix.empty_eq v]
    | _, Language.ORing.Func.add =>
      show s.func (Language.Add.add : LXI.Func 2) v = s.func (Language.Add.add : LXI.Func 2) ![v 0, v 1]
      rw [← Matrix.fun_eq_vec_two]
    | _, Language.ORing.Func.mul =>
      show s.func (Language.Mul.mul : LXI.Func 2) v = s.func (Language.Mul.mul : LXI.Func 2) ![v 0, v 1]
      rw [← Matrix.fun_eq_vec_two]
  · match k, r with
    | _, Language.ORing.Rel.eq =>
      show s.rel (Language.Eq.eq : LXI.Rel 2) v = (v 0 = v 1)
      rw [Matrix.fun_eq_vec_two v]
      exact propext (hEq _ _)
    | _, Language.ORing.Rel.lt =>
      show s.rel (Language.LT.lt : LXI.Rel 2) v = s.rel (Language.LT.lt : LXI.Rel 2) ![v 0, v 1]
      rw [← Matrix.fun_eq_vec_two]

/-- **Provability from truth in the arithmetically standard models.**  A sentence true in
every arithmetically standard model of `ID1Acc prec` is a theorem of `ID1Acc prec`. -/
theorem provable_of_models (prec : Semisentence ℒₒᵣ 2) {σ : Sentence LXI}
    (H : ∀ (N : Type) [ORingStructure N] [Structure LXI N] [ArithStd N],
      N↓[LXI] ⊧* ID1Acc prec → N↓[LXI] ⊧ σ) :
    ID1Acc prec ⊢ σ := by
  have _ : 𝗘𝗤 LXI ⪯ ID1Acc prec := eq_weakerThan_ID1 (accForm prec)
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq]
  intro N _ s hEq hN
  let _ := oringOf s
  have _ := arithStd_of s (fun a b => hEq.eq a b)
  exact H N hN

end Complete

/-! ### Reading `I` as a predicate -/

section WithI

variable {N : Type*} [s : Structure LXI N]

set_option warn.classDefReducibility false in
/-- The structure `N` with `I` read as `T`. -/
def withI (T : N → Prop) : Structure LXI N where
  func := fun {_} f v => s.func f v
  rel := fun {k} r v => match k, r with
    | _, Sum.inl r => s.rel (Sum.inl r) v
    | _, Sum.inr IXRel.X => s.rel (Sum.inr IXRel.X) v
    | _, Sum.inr IXRel.I => T (v 0)

theorem val_withI (T : N → Prop) {ξ : Type*} {n : ℕ} (e : Fin n → N) (f : ξ → N)
    (t : Semiterm LXI ξ n) :
    Semiterm.val (s := withI T) e f t = Semiterm.val (s := s) e f t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func F v ih =>
    simp only [Semiterm.val_func]
    exact congrArg _ (funext fun i => ih i)

theorem lMap_withI (T : N → Prop) : (withI T).lMap toLXI = s.lMap toLXI := rfl

/-- **`substI F φ` reads `I` as the set defined by `F`**, under the same assignment of the
free variables. -/
theorem eval_substI {ξ : Type*} (F : Semiformula LXI ξ 1) (f : ξ → N) {n : ℕ}
    (φ : Semiformula LXI ξ n) (e : Fin n → N) :
    Semiformula.Eval (s := s) e f (substI F φ) ↔
      Semiformula.Eval (s := withI fun x => Semiformula.Eval (s := s) ![x] f F) e f φ := by
  set T : N → Prop := fun x => Semiformula.Eval (s := s) ![x] f F with hT
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v =>
    rcases r with r | r
    · show s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e f (v i)) ↔
        s.rel (Sum.inl r) (fun i => Semiterm.val (s := withI T) e f (v i))
      simp only [val_withI]
    · cases r with
      | X =>
        show s.rel (Sum.inr IXRel.X) (fun i => Semiterm.val (s := s) e f (v i)) ↔
          s.rel (Sum.inr IXRel.X) (fun i => Semiterm.val (s := withI T) e f (v i))
        simp only [val_withI]
      | I =>
        show Semiformula.Eval (s := s) e f (F/[v 0]) ↔ T (Semiterm.val (s := withI T) e f (v 0))
        rw [Semiformula.eval_substs, Matrix.comp₁, val_withI]
  | hnrel r v =>
    rcases r with r | r
    · show ¬s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e f (v i)) ↔
        ¬s.rel (Sum.inl r) (fun i => Semiterm.val (s := withI T) e f (v i))
      simp only [val_withI]
    · cases r with
      | X =>
        show ¬s.rel (Sum.inr IXRel.X) (fun i => Semiterm.val (s := s) e f (v i)) ↔
          ¬s.rel (Sum.inr IXRel.X) (fun i => Semiterm.val (s := withI T) e f (v i))
        simp only [val_withI]
      | I =>
        show Semiformula.Eval (s := s) e f (∼(F/[v 0])) ↔
          ¬T (Semiterm.val (s := withI T) e f (v 0))
        rw [LogicalConnective.HomClass.map_neg, Semiformula.eval_substs, Matrix.comp₁, val_withI]
        rfl
  | hand φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := s) e f (substI F φ ⋏ substI F ψ) ↔ _
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact and_congr (ihφ e) (ihψ e)
  | hor φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := s) e f (substI F φ ⋎ substI F ψ) ↔ _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact or_congr (ihφ e) (ihψ e)
  | hall φ ih =>
    show Semiformula.Eval (s := s) e f (∀¹ substI F φ) ↔ _
    rw [Semiformula.eval_all, Semiformula.eval_all]
    exact forall_congr' fun x => ih (x :> e)
  | hexs φ ih =>
    show Semiformula.Eval (s := s) e f (∃¹ substI F φ) ↔ _
    rw [Semiformula.eval_ex, Semiformula.eval_ex]
    exact exists_congr fun x => ih (x :> e)

end WithI

/-! ### Inside an arithmetically standard model of `ID1Acc prec` -/

section Model

variable {N : Type*} [ORingStructure N] [s : Structure LXI N] [ArithStd N]
variable (prec : Semisentence ℒₒᵣ 2)

/-- `y ≺ x` in `N` (slot `#0` the smaller element, as in `accForm`). -/
def precM (y x : N) : Prop := Semiformula.Evalb (M := N) ![y, x] prec

omit [ArithStd N] in
theorem eval_accForm_withI (T : N → Prop) [ArithStd N] (x : N) :
    Semiformula.Eval (s := withI T) ![x] Empty.elim (accForm prec) ↔
      ∀ y, precM prec y x → T y := by
  unfold accForm
  rw [Semiformula.eval_all]
  refine forall_congr' fun y => ?_
  rw [LogicalConnective.HomClass.map_imply, Semiformula.eval_lMap, lMap_withI,
    ArithStd.lMap_eq]
  have e : (y :> ![x] : Fin 2 → N) = ![y, x] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    rfl
  rw [e]
  rfl

theorem eval_accForm (x : N) :
    Semiformula.Eval (s := s) ![x] Empty.elim (accForm prec) ↔ ∀ y, precM prec y x → Imem y := by
  unfold accForm
  rw [Semiformula.eval_all]
  refine forall_congr' fun y => ?_
  rw [LogicalConnective.HomClass.map_imply, eval_lMap_toLXI, eval_Iat]
  have e : (y :> ![x] : Fin 2 → N) = ![y, x] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    rfl
  rw [e]
  rfl

/-- `A(F, x)` for the accessibility form. -/
theorem eval_opAt_accForm (F : Semiformula LXI ℕ 1) (f : ℕ → N) (x : N) :
    Semiformula.Eval (s := s) ![x] f (opAt (accForm prec) F) ↔
      ∀ y, precM prec y x → Semiformula.Eval (s := s) ![y] f F := by
  rw [opAt, eval_substI, Semiformula.eval_emb, eval_accForm_withI]

variable [hM : N↓[LXI] ⊧* ID1Acc prec]

omit [ArithStd N] in
include hM in
theorem eval_of_mem_ID1Acc {σ : Sentence LXI} (h : σ ∈ ID1Acc prec) :
    Semiformula.Eval (s := s) ![] Empty.elim σ :=
  models_iff.mp (Semantics.modelsSet_iff.mp hM h)

include hM in
/-- **Closure**: `(∀y ≺ x, I y) → I x`. -/
theorem imem_of_forall (x : N) (h : ∀ y, precM prec y x → Imem y) : Imem x := by
  have hc := eval_of_mem_ID1Acc (N := N) prec (closureAx_mem_ID1 (accForm prec))
  rw [closureAx, Semiformula.eval_all] at hc
  have := hc x
  rw [LogicalConnective.HomClass.map_imply, eval_Iat] at this
  exact this ((eval_accForm prec x).mpr h)

include hM in
/-- **The induction scheme of `I`** at a formula `F` with an assignment `f`. -/
theorem ind_formula (F : Semiformula LXI ℕ 1) (f : ℕ → N)
    (hprog : ∀ x, (∀ y, precM prec y x → Semiformula.Eval (s := s) ![y] f F) →
      Semiformula.Eval (s := s) ![x] f F) :
    ∀ x, Imem x → Semiformula.Eval (s := s) ![x] f F := by
  have hi := eval_of_mem_ID1Acc (N := N) prec (indAx_mem_ID1 (accForm prec) F)
  have : Nonempty N := ⟨0⟩
  rw [indAx] at hi
  have hf := (Semiformula.eval_univCl (s := s) _).mp hi f
  simp only [Semiformula.Evalf, LogicalConnective.HomClass.map_imply, Semiformula.eval_all] at hf
  intro x hx
  have h2 := hf (fun y hy => hprog y ((eval_opAt_accForm prec F f y).mp hy)) x
  exact h2 ((eval_Iat (#0 : Semiterm LXI ℕ 1) ![x] f).mpr hx)

omit [ArithStd N] hM in
theorem lMap_zero_term :
    Semiterm.lMap toLXI ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 0) = ((0 : ℕ) : Semiterm LXI ℕ 0) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral, Semiterm.Operator.Zero.term_eq]

omit [ArithStd N] hM in
theorem lMap_succ_term :
    Semiterm.lMap toLXI (‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1) = (‘(#0 + 1)’ : Semiterm LXI ℕ 1) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, Semiterm.Operator.Add.term_eq]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => k.elim0) j
    simp [Function.comp_def, Matrix.empty_eq]

omit hM in
theorem val_zero_term (f : ℕ → N) :
    Semiterm.val (s := s) ![] f ((0 : ℕ) : Semiterm LXI ℕ 0) = 0 := by
  rw [← lMap_zero_term, val_lMap_toLXI]
  simp [Semiterm.val_operator]

omit hM in
theorem val_succ_term (f : ℕ → N) (x : N) :
    Semiterm.val (s := s) ![x] f (‘(#0 + 1)’ : Semiterm LXI ℕ 1) = x + 1 := by
  rw [← lMap_succ_term, val_lMap_toLXI]
  simp [Semiterm.val_operator]

/-- The instance of `succInd` at `φ`, unfolded. -/
theorem eval_succInd_iff {L : Language} [L.ORing] {M : Type*} [Structure L M]
    (φ : Semiformula L ℕ 1) (f : ℕ → M) :
    Semiformula.Eval ![] f (succInd φ) ↔
      (Semiformula.Eval ![Semiterm.val ![] f ((0 : ℕ) : Semiterm L ℕ 0)] f φ →
        (∀ x, Semiformula.Eval ![x] f φ →
          Semiformula.Eval ![Semiterm.val ![x] f (‘(#0 + 1)’ : Semiterm L ℕ 1)] f φ) →
        ∀ x, Semiformula.Eval ![x] f φ) := by
  show Semiformula.Eval ![] f ((φ/[((0 : ℕ) : Semiterm L ℕ 0)]) 🡒
      (∀¹ (φ/[(#0 : Semiterm L ℕ 1)] 🡒 φ/[(‘(#0 + 1)’ : Semiterm L ℕ 1)])) 🡒
      ∀¹ (φ/[(#0 : Semiterm L ℕ 1)])) ↔ _
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_all, Semiformula.eval_substs]
  simp [Matrix.empty_eq]

include hM in
/-- **Induction along the numbers** at a formula `φ` of `LXI` with an assignment `f`. -/
theorem succ_induction_formula (φ : Semiformula LXI ℕ 1) (f : ℕ → N)
    (h0 : Semiformula.Eval (s := s) ![0] f φ)
    (hs : ∀ x, Semiformula.Eval (s := s) ![x] f φ → Semiformula.Eval (s := s) ![x + 1] f φ) :
    ∀ x, Semiformula.Eval (s := s) ![x] f φ := by
  have hi := eval_of_mem_ID1Acc (N := N) prec (succInd_mem_ID1 (accForm prec) φ)
  have : Nonempty N := ⟨0⟩
  have hf := (Semiformula.eval_univCl (s := s) _).mp hi f
  simp only [Semiformula.Evalf] at hf
  rw [eval_succInd_iff, val_zero_term] at hf
  simp only [val_succ_term] at hf
  exact hf h0 hs

include hM in
/-- **The arithmetic reduct is a model of `PA`.** -/
theorem models_peano : N↓[ℒₒᵣ] ⊧* 𝗣𝗔 := by
  refine Semantics.modelsSet_iff.mpr fun σ hσ => models_iff.mpr ?_
  rcases hσ with hσ | ⟨ψ, -, rfl⟩
  · have h := eval_of_mem_ID1Acc (N := N) prec (mem_ID1_of_paMinus (accForm prec) hσ)
    rw [eval_lMap_toLXI] at h
    exact h
  · have : Nonempty N := ⟨0⟩
    refine (Semiformula.eval_univCl (s := standardModel N) _).mpr fun f => ?_
    simp only [Semiformula.Evalf]
    rw [eval_succInd_iff]
    intro h0 hs
    have e0 : Semiterm.val (s := standardModel N) ![] f ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 0) = 0 := by
      simp [Semiterm.val_operator]
    have e1 : ∀ x : N,
        Semiterm.val (s := standardModel N) ![x] f (‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1) = x + 1 := by
      intro x; simp [Semiterm.val_operator]
    rw [e0] at h0
    simp only [e1] at hs
    have key := succ_induction_formula prec (Semiformula.lMap toLXI ψ) f
      ((eval_lMap_toLXI ψ ![0] f).mpr h0)
      (fun x hx => (eval_lMap_toLXI ψ ![x + 1] f).mpr (hs x ((eval_lMap_toLXI ψ ![x] f).mp hx)))
    exact fun x => (eval_lMap_toLXI ψ ![x] f).mp (key x)

include hM in
/-- **The arithmetic reduct is a model of `IΣ₁`.** -/
theorem models_iSigma₁ : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
  Semantics.ModelsSet.of_subset (models_peano (N := N) prec)
    (Set.union_subset_union_right _ (InductionScheme_subset fun _ => trivial))

/-! ### Definable predicates -/

omit [ORingStructure N] [ArithStd N] hM in
/-- A formula with parameters from `N` is a formula with free variables numbered by `ℕ`,
under a suitable assignment. -/
theorem exists_nat_formula [Inhabited N] {k : ℕ} (φ : Semiformula LXI N k) :
    ∃ (ψ : Semiformula LXI ℕ k) (f : ℕ → N),
      ∀ e, Semiformula.Eval (s := s) e f ψ ↔ Semiformula.Eval (s := s) e id φ := by
  classical
  refine ⟨Rew.rewriteMap φ.idxOfFVar ▹ φ, φ.enumerateFVar, fun e => ?_⟩
  rw [Semiformula.eval_rewriteMap]
  exact Semiformula.eval_enumerateFVar_idxOfFVar_eq_id φ e

omit [ArithStd N] hM in
theorem exists_nat_formula_pred {Q : N → Prop} (hQ : LXI.DefinablePred Q) :
    ∃ (ψ : Semiformula LXI ℕ 1) (f : ℕ → N), ∀ x, Semiformula.Eval (s := s) ![x] f ψ ↔ Q x := by
  have : Inhabited N := ⟨0⟩
  obtain ⟨φ, hφ⟩ := hQ.definable
  obtain ⟨ψ, f, hψ⟩ := exists_nat_formula φ
  exact ⟨ψ, f, fun x => (hψ ![x]).trans (hφ ![x])⟩

include hM in
/-- **The induction scheme of `I` for definable predicates**: a definable predicate that is
progressive along `≺` holds on `I`. -/
theorem ind_definable {Q : N → Prop} (hQ : LXI.DefinablePred Q)
    (hprog : ∀ x, (∀ y, precM prec y x → Q y) → Q x) : ∀ x, Imem x → Q x := by
  obtain ⟨ψ, f, hψ⟩ := exists_nat_formula_pred hQ
  intro x hx
  exact (hψ x).mp (ind_formula prec ψ f
    (fun x h => (hψ x).mpr (hprog x fun y hy => (hψ y).mp (h y hy))) x hx)

include hM in
/-- **Induction along the numbers for definable predicates.** -/
theorem succ_induction_definable {Q : N → Prop} (hQ : LXI.DefinablePred Q)
    (h0 : Q 0) (hs : ∀ x, Q x → Q (x + 1)) : ∀ x, Q x := by
  obtain ⟨ψ, f, hψ⟩ := exists_nat_formula_pred hQ
  intro x
  exact (hψ x).mp (succ_induction_formula prec ψ f ((hψ 0).mpr h0)
    (fun x h => (hψ (x + 1)).mpr (hs x ((hψ x).mp h))) x)

omit hM in
/-- An arithmetic predicate with parameters is definable in `LXI`. -/
theorem definable_of_arith {k : ℕ} {R : (Fin k → N) → Prop} {ℌ : HierarchySymbol}
    (h : ℌ.Definable R) : LXI.Definable R := by
  obtain ⟨φ, hφ⟩ := h.definable
  refine ⟨Semiformula.lMap toLXI φ.val, fun v => ?_⟩
  rw [eval_lMap_toLXI]
  exact HierarchySymbol.IsDefinedByWithParam.df hφ v

omit [ORingStructure N] [ArithStd N] hM in
theorem definable_imem : LXI.DefinablePred (Imem (N := N)) :=
  ⟨Iat #0, fun v => by rw [eval_Iat]; rfl⟩

omit [ORingStructure N] [ArithStd N] hM in
theorem definable_xmem : LXI.DefinablePred (Xmem (N := N)) :=
  ⟨Xat #0, fun v => by rw [eval_Xat]; rfl⟩

include hM in
/-- **Order induction along the numbers for definable predicates.** -/
theorem order_induction_definable {Q : N → Prop} (hQ : LXI.DefinablePred Q)
    (h : ∀ x, (∀ y < x, Q y) → Q x) : ∀ x, Q x := by
  have : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_iSigma₁ prec
  have hQ' : LXI.DefinablePred fun x : N => ∀ y < x, Q y := by
    refine Language.Definable.all ?_
    refine Language.Definable.imp ?_ ?_
    · exact definable_of_arith (ℌ := 𝚺₀) (by definability)
    · exact hQ.retraction ![0]
  have key := succ_induction_definable prec hQ' (fun y hy => absurd hy (by simp))
    (fun x hx y hy => by
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hy) with hy | rfl
      · exact hx y hy
      · exact h y hx)
  exact fun x => key (x + 1) x (lt_succ_iff_le.mpr le_rfl)

end Model

end Lift

end InductiveDef

end OrdinalAnalysis
