/-
  Models of `ID A` (finitely or infinitely many levels) with standard arithmetic, and the
  passage from truth in all of them to provability.

  The multi-level version of `ID1/Lift.lean`, for the theories `ID A` of
  `IDn/Theory.lean` over the language `LXIN ι = ℒₒᵣ + {X} + {I_k | k : ι}` (any index type
  `ι` with decidable equality: `Fin n` for `IDn n`, `ℕ` for `IDlt`).

  **Arithmetically standard structures.**  An `LXIN ι`-structure on a type `N` carrying an
  `ORingStructure` is *arithmetically standard* (`ArithStd`) when its reduct to `ℒₒᵣ` is the
  structure of the arithmetic operations of `N`.  Every `LXIN ι`-structure whose equality is
  true equality is of this form for the operations it defines itself (`arithStd_of`), so by
  Foundation's completeness theorem a sentence true in every arithmetically standard model of
  `ID A` is a theorem of `ID A` (`provable_of_models`).

  **Inside such a model** `N` (write `I_k x`, `X x`):

  * `N` is a model of `PA`, in particular of `IΣ₁` (`models_peano`, `models_iSigma₁`);
  * reading `I_k` as a predicate `T` (`withIAt k T`, the other predicates unchanged),
    `substIAt k F` is evaluation with `I_k` read as the set defined by `F` (`eval_substIAt`);
  * **closure** of level `k`: if `A_k(I_k, x)` then `I_k x` (`imem_of_form`);
  * **the induction scheme** of level `k` for every predicate definable in `LXIN ι` with
    parameters (`ind_definable`): if `A_k(Q, x) → Q x` for all `x`, then `I_k ⊆ Q`;
  * induction along the numbers for every such predicate (`succ_induction_definable`,
    `order_induction_definable`).
-/
import OrdinalAnalysis.IDn.Theory
import Foundation.FirstOrder.Completeness

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

namespace Lift

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {ι : Type}

/-! ### Arithmetically standard structures -/

/-- The `ℒₒᵣ`-reduct of the `LXIN ι`-structure is the arithmetic of `N`. -/
class ArithStd (ι : Type) (N : Type*) [ORingStructure N] [s : Structure (LXIN ι) N] : Prop where
  lMap_eq : s.lMap (toLXIN ι) = Arithmetic.standardModel N

section Std

variable {N : Type*} [ORingStructure N] [s : Structure (LXIN ι) N] [ArithStd ι N]

/-- Arithmetic terms have their arithmetic values. -/
theorem val_lMap {ξ : Type*} {n : ℕ} (t : Semiterm ℒₒᵣ ξ n) (e : Fin n → N) (f : ξ → N) :
    Semiterm.val (s := s) e f (Semiterm.lMap (toLXIN ι) t) =
      Semiterm.val (s := standardModel N) e f t := by
  rw [Semiterm.val_lMap, ArithStd.lMap_eq]

/-- Arithmetic formulas say what they say in the arithmetic of `N`. -/
theorem eval_lMap {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) (e : Fin n → N) (f : ξ → N) :
    Semiformula.Eval (s := s) e f (Semiformula.lMap (toLXIN ι) φ) ↔
      Semiformula.Eval (s := standardModel N) e f φ := by
  rw [Semiformula.eval_lMap, ArithStd.lMap_eq]

end Std

section Preds

variable {N : Type*} [s : Structure (LXIN ι) N]

/-- The predicate read by `I_k`. -/
def Imem (k : ι) (x : N) : Prop := s.rel (Sum.inr (IXRelN.I k)) ![x]

/-- The predicate read by `X`. -/
def Xmem (x : N) : Prop := s.rel (Sum.inr IXRelN.X) ![x]

theorem eval_IatN {ξ : Type*} {n : ℕ} (k : ι) (t : Semiterm (LXIN ι) ξ n) (e : Fin n → N)
    (f : ξ → N) :
    Semiformula.Eval (s := s) e f (Iat k t) ↔ Imem k (Semiterm.val (s := s) e f t) := by
  have h : (Semiterm.val (s := s) e f ∘ ![t] : Fin 1 → N)
      = ![Semiterm.val (s := s) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg (s.rel (Sum.inr (IXRelN.I k))) h)

theorem eval_XatN {ξ : Type*} {n : ℕ} (t : Semiterm (LXIN ι) ξ n) (e : Fin n → N)
    (f : ξ → N) :
    Semiformula.Eval (s := s) e f (Xat t) ↔ Xmem (s := s) (Semiterm.val (s := s) e f t) := by
  have h : (Semiterm.val (s := s) e f ∘ ![t] : Fin 1 → N)
      = ![Semiterm.val (s := s) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg (s.rel (Sum.inr IXRelN.X)) h)

end Preds

/-! ### From truth in the arithmetically standard models to provability -/

section Complete

variable {M : Type*} (s : Structure (LXIN ι) M)

set_option warn.classDefReducibility false in
/-- The arithmetic operations of an `LXIN ι`-structure. -/
@[reducible] def oringOf : ORingStructure M where
  zero := s.func (Language.Zero.zero : (LXIN ι).Func 0) ![]
  one := s.func (Language.One.one : (LXIN ι).Func 0) ![]
  add a b := s.func (Language.Add.add : (LXIN ι).Func 2) ![a, b]
  mul a b := s.func (Language.Mul.mul : (LXIN ι).Func 2) ![a, b]
  lt a b := s.rel (Language.LT.lt : (LXIN ι).Rel 2) ![a, b]

/-- An `LXIN ι`-structure with true equality is arithmetically standard for its own
operations. -/
theorem arithStd_of
    (hEq : ∀ a b : M, s.rel (Language.Eq.eq : (LXIN ι).Rel 2) ![a, b] ↔ a = b) :
    letI := oringOf s; ArithStd ι M := by
  let _ := oringOf s
  refine ⟨Structure.ext (funext₃ fun k f v => ?_) (funext₃ fun k r v => ?_)⟩
  · match k, f with
    | _, Language.ORing.Func.zero =>
      show s.func (Language.Zero.zero : (LXIN ι).Func 0) v =
        s.func (Language.Zero.zero : (LXIN ι).Func 0) ![]
      rw [Matrix.empty_eq v]
    | _, Language.ORing.Func.one =>
      show s.func (Language.One.one : (LXIN ι).Func 0) v =
        s.func (Language.One.one : (LXIN ι).Func 0) ![]
      rw [Matrix.empty_eq v]
    | _, Language.ORing.Func.add =>
      show s.func (Language.Add.add : (LXIN ι).Func 2) v =
        s.func (Language.Add.add : (LXIN ι).Func 2) ![v 0, v 1]
      rw [← Matrix.fun_eq_vec_two]
    | _, Language.ORing.Func.mul =>
      show s.func (Language.Mul.mul : (LXIN ι).Func 2) v =
        s.func (Language.Mul.mul : (LXIN ι).Func 2) ![v 0, v 1]
      rw [← Matrix.fun_eq_vec_two]
  · match k, r with
    | _, Language.ORing.Rel.eq =>
      show s.rel (Language.Eq.eq : (LXIN ι).Rel 2) v = (v 0 = v 1)
      rw [Matrix.fun_eq_vec_two v]
      exact propext (hEq _ _)
    | _, Language.ORing.Rel.lt =>
      show s.rel (Language.LT.lt : (LXIN ι).Rel 2) v =
        s.rel (Language.LT.lt : (LXIN ι).Rel 2) ![v 0, v 1]
      rw [← Matrix.fun_eq_vec_two]

variable [DecidableEq ι]

/-- **Provability from truth in the arithmetically standard models.**  A sentence true in
every arithmetically standard model of `ID A` is a theorem of `ID A`. -/
theorem provable_of_models (A : ι → Semisentence (LXIN ι) 1) {σ : Sentence (LXIN ι)}
    (H : ∀ (N : Type) [ORingStructure N] [Structure (LXIN ι) N] [ArithStd ι N],
      N↓[LXIN ι] ⊧* ID A → N↓[LXIN ι] ⊧ σ) :
    ID A ⊢ σ := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq]
  intro N _ s hEq hN
  let _ := oringOf s
  have _ := arithStd_of s (fun a b => hEq.eq a b)
  exact H N hN

end Complete

/-! ### Reading `I_k` as a predicate -/

section WithI

variable [DecidableEq ι] {N : Type*} [s : Structure (LXIN ι) N]

set_option warn.classDefReducibility false in
/-- The structure `N` with `I_k` read as `T`, every other symbol unchanged. -/
def withIAt (k : ι) (T : N → Prop) : Structure (LXIN ι) N where
  func := fun {_} f v => s.func f v
  rel := fun {m} r v => match m, r with
    | _, Sum.inl r => s.rel (Sum.inl r) v
    | _, Sum.inr IXRelN.X => s.rel (Sum.inr IXRelN.X) v
    | _, Sum.inr (IXRelN.I j) => if j = k then T (v 0) else s.rel (Sum.inr (IXRelN.I j)) v

theorem val_withIAt (k : ι) (T : N → Prop) {ξ : Type*} {n : ℕ} (e : Fin n → N) (f : ξ → N)
    (t : Semiterm (LXIN ι) ξ n) :
    Semiterm.val (s := withIAt k T) e f t = Semiterm.val (s := s) e f t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func F v ih =>
    simp only [Semiterm.val_func]
    exact congrArg _ (funext fun i => ih i)

theorem lMap_withIAt (k : ι) (T : N → Prop) :
    (withIAt k T).lMap (toLXIN ι) = s.lMap (toLXIN ι) := rfl

theorem withIAt_rel_I_self (k : ι) (T : N → Prop) (x : N) :
    (withIAt k T).rel (Sum.inr (IXRelN.I k)) ![x] ↔ T x := by
  show (if k = k then T x else _) ↔ T x
  rw [if_pos rfl]

theorem withIAt_rel_I_ne {k j : ι} (h : j ≠ k) (T : N → Prop) (x : N) :
    (withIAt k T).rel (Sum.inr (IXRelN.I j)) ![x] ↔ Imem j x := by
  show (if j = k then T x else _) ↔ _
  rw [if_neg h]; rfl

theorem withIAt_rel_X (k : ι) (T : N → Prop) (x : N) :
    (withIAt k T).rel (Sum.inr IXRelN.X) ![x] ↔ Xmem (s := s) x := Iff.rfl

/-- Reading `I_k` as itself changes nothing. -/
theorem withIAt_self (k : ι) : withIAt k (Imem (s := s) k) = s := by
  refine Structure.ext (funext₃ fun _ _ _ => rfl) (funext₃ fun m r v => ?_)
  match m, r with
  | _, Sum.inl r => rfl
  | _, Sum.inr IXRelN.X => rfl
  | _, Sum.inr (IXRelN.I j) =>
    show (if j = k then Imem k (v 0) else s.rel (Sum.inr (IXRelN.I j)) v) = _
    split_ifs with h
    · subst h
      show s.rel (Sum.inr (IXRelN.I j)) ![v 0] = s.rel (Sum.inr (IXRelN.I j)) v
      rw [← Matrix.fun_eq_vec_one]
    · rfl

/-- **`substIAt k F φ` reads `I_k` as the set defined by `F`**, under the same assignment of
the free variables, the other predicates unchanged. -/
theorem eval_substIAt (k : ι) {ξ : Type*} (F : Semiformula (LXIN ι) ξ 1) (f : ξ → N) {n : ℕ}
    (φ : Semiformula (LXIN ι) ξ n) (e : Fin n → N) :
    Semiformula.Eval (s := s) e f (substIAt k F φ) ↔
      Semiformula.Eval (s := withIAt k fun x => Semiformula.Eval (s := s) ![x] f F) e f φ := by
  set T : N → Prop := fun x => Semiformula.Eval (s := s) ![x] f F with hT
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v =>
    rcases r with r | r
    · show s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e f (v i)) ↔
        s.rel (Sum.inl r) (fun i => Semiterm.val (s := withIAt k T) e f (v i))
      simp only [val_withIAt]
    · cases r with
      | X =>
        show s.rel (Sum.inr IXRelN.X) (fun i => Semiterm.val (s := s) e f (v i)) ↔
          s.rel (Sum.inr IXRelN.X) (fun i => Semiterm.val (s := withIAt k T) e f (v i))
        simp only [val_withIAt]
      | I j =>
        show Semiformula.Eval (s := s) e f
            (if _ : j = k then F/[v 0] else Semiformula.rel (Sum.inr (IXRelN.I j)) v) ↔
          (if j = k then T (Semiterm.val (s := withIAt k T) e f (v 0))
            else s.rel (Sum.inr (IXRelN.I j)) (fun i => Semiterm.val (s := withIAt k T) e f (v i)))
        by_cases h : j = k
        · rw [dif_pos h, if_pos h, Semiformula.eval_substs, Matrix.comp₁, val_withIAt]
        · rw [dif_neg h, if_neg h]
          show s.rel (Sum.inr (IXRelN.I j)) (fun i => Semiterm.val (s := s) e f (v i)) ↔ _
          simp only [val_withIAt]
  | hnrel r v =>
    rcases r with r | r
    · show ¬s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e f (v i)) ↔
        ¬s.rel (Sum.inl r) (fun i => Semiterm.val (s := withIAt k T) e f (v i))
      simp only [val_withIAt]
    · cases r with
      | X =>
        show ¬s.rel (Sum.inr IXRelN.X) (fun i => Semiterm.val (s := s) e f (v i)) ↔
          ¬s.rel (Sum.inr IXRelN.X) (fun i => Semiterm.val (s := withIAt k T) e f (v i))
        simp only [val_withIAt]
      | I j =>
        show Semiformula.Eval (s := s) e f
            (if _ : j = k then ∼(F/[v 0]) else Semiformula.nrel (Sum.inr (IXRelN.I j)) v) ↔
          ¬(if j = k then T (Semiterm.val (s := withIAt k T) e f (v 0))
            else s.rel (Sum.inr (IXRelN.I j)) (fun i => Semiterm.val (s := withIAt k T) e f (v i)))
        by_cases h : j = k
        · rw [dif_pos h, if_pos h, LogicalConnective.HomClass.map_neg, Semiformula.eval_substs,
            Matrix.comp₁, val_withIAt]
          rfl
        · rw [dif_neg h, if_neg h]
          show ¬s.rel (Sum.inr (IXRelN.I j)) (fun i => Semiterm.val (s := s) e f (v i)) ↔ _
          simp only [val_withIAt]
  | hand φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := s) e f (substIAt k F φ ⋏ substIAt k F ψ) ↔ _
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact and_congr (ihφ e) (ihψ e)
  | hor φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := s) e f (substIAt k F φ ⋎ substIAt k F ψ) ↔ _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact or_congr (ihφ e) (ihψ e)
  | hall φ ih =>
    show Semiformula.Eval (s := s) e f (∀¹ substIAt k F φ) ↔ _
    rw [Semiformula.eval_all, Semiformula.eval_all]
    exact forall_congr' fun x => ih (x :> e)
  | hexs φ ih =>
    show Semiformula.Eval (s := s) e f (∃¹ substIAt k F φ) ↔ _
    rw [Semiformula.eval_ex, Semiformula.eval_ex]
    exact exists_congr fun x => ih (x :> e)

/-- `A_k(F, x)` is `A_k` evaluated with `I_k` read as the set defined by `F`. -/
theorem eval_opAt (k : ι) (A : Semisentence (LXIN ι) 1) (F : Semiformula (LXIN ι) ℕ 1)
    (f : ℕ → N) (x : N) :
    Semiformula.Eval (s := s) ![x] f (opAt k A F) ↔
      Semiformula.Eval (s := withIAt k fun y => Semiformula.Eval (s := s) ![y] f F)
        ![x] Empty.elim A := by
  rw [opAt, eval_substIAt, Semiformula.eval_emb]

end WithI

/-! ### Inside an arithmetically standard model of `ID A` -/

section Model

variable [DecidableEq ι] {N : Type*} [ORingStructure N] [s : Structure (LXIN ι) N] [ArithStd ι N]
variable (A : ι → Semisentence (LXIN ι) 1)

variable [hM : N↓[LXIN ι] ⊧* ID A]

omit [ArithStd ι N] in
include hM in
theorem eval_of_mem_ID {σ : Sentence (LXIN ι)} (h : σ ∈ ID A) :
    Semiformula.Eval (s := s) ![] Empty.elim σ :=
  models_iff.mp (Semantics.modelsSet_iff.mp hM h)

omit [ArithStd ι N] in
include hM in
/-- **Closure** of level `k`: `A_k(I_k, x) → I_k x`. -/
theorem imem_of_form (k : ι) (x : N) (h : Semiformula.Eval (s := s) ![x] Empty.elim (A k)) :
    Imem k x := by
  have hc := eval_of_mem_ID (N := N) A (closureAxAt_mem_ID A k)
  rw [closureAxAt, Semiformula.eval_all] at hc
  have := hc x
  rw [LogicalConnective.HomClass.map_imply, eval_IatN] at this
  exact this h

omit [ArithStd ι N] in
include hM in
/-- Closure of level `k`, with the form read in `withIAt k (I_k)`. -/
theorem imem_of_form' (k : ι) (x : N)
    (h : Semiformula.Eval (s := withIAt k (Imem (s := s) k)) ![x] Empty.elim (A k)) :
    Imem k x := by
  rw [withIAt_self] at h
  exact imem_of_form A k x h

omit [ArithStd ι N] in
include hM in
/-- **The induction scheme of `I_k`** at a formula `F` with an assignment `f`. -/
theorem ind_formula (k : ι) (F : Semiformula (LXIN ι) ℕ 1) (f : ℕ → N)
    (hprog : ∀ x, Semiformula.Eval (s := withIAt k fun y => Semiformula.Eval (s := s) ![y] f F)
      ![x] Empty.elim (A k) → Semiformula.Eval (s := s) ![x] f F) :
    ∀ x, Imem k x → Semiformula.Eval (s := s) ![x] f F := by
  have hi := eval_of_mem_ID (N := N) A (indAxAt_mem_ID A k F)
  have : Nonempty N := ⟨0⟩
  rw [indAxAt] at hi
  have hf := (Semiformula.eval_univCl (s := s) _).mp hi f
  simp only [Semiformula.Evalf, LogicalConnective.HomClass.map_imply, Semiformula.eval_all] at hf
  intro x hx
  have h2 := hf (fun y hy => hprog y ((eval_opAt k (A k) F f y).mp hy)) x
  exact h2 ((eval_IatN k (#0 : Semiterm (LXIN ι) ℕ 1) ![x] f).mpr hx)

omit [DecidableEq ι] [ArithStd ι N] hM in
theorem lMap_zero_term :
    Semiterm.lMap (toLXIN ι) ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 0) =
      ((0 : ℕ) : Semiterm (LXIN ι) ℕ 0) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral, Semiterm.Operator.Zero.term_eq]

omit [DecidableEq ι] [ArithStd ι N] hM in
theorem lMap_succ_term :
    Semiterm.lMap (toLXIN ι) (‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1) =
      (‘(#0 + 1)’ : Semiterm (LXIN ι) ℕ 1) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, Semiterm.Operator.Add.term_eq]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => k.elim0) j
    simp [Function.comp_def, Matrix.empty_eq]

omit [DecidableEq ι] hM in
theorem val_zero_term (f : ℕ → N) :
    Semiterm.val (s := s) ![] f ((0 : ℕ) : Semiterm (LXIN ι) ℕ 0) = 0 := by
  rw [← lMap_zero_term, val_lMap]
  simp [Semiterm.val_operator]

omit [DecidableEq ι] hM in
theorem val_succ_term (f : ℕ → N) (x : N) :
    Semiterm.val (s := s) ![x] f (‘(#0 + 1)’ : Semiterm (LXIN ι) ℕ 1) = x + 1 := by
  rw [← lMap_succ_term, val_lMap]
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
/-- **Induction along the numbers** at a formula `φ` of `LXIN ι` with an assignment `f`. -/
theorem succ_induction_formula (φ : Semiformula (LXIN ι) ℕ 1) (f : ℕ → N)
    (h0 : Semiformula.Eval (s := s) ![0] f φ)
    (hs : ∀ x, Semiformula.Eval (s := s) ![x] f φ → Semiformula.Eval (s := s) ![x + 1] f φ) :
    ∀ x, Semiformula.Eval (s := s) ![x] f φ := by
  have hi := eval_of_mem_ID (N := N) A (succInd_mem_ID A φ)
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
  · have h := eval_of_mem_ID (N := N) A (mem_ID_of_paMinus A hσ)
    rw [eval_lMap] at h
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
    have key := succ_induction_formula A (Semiformula.lMap (toLXIN ι) ψ) f
      ((eval_lMap ψ ![0] f).mpr h0)
      (fun x hx => (eval_lMap ψ ![x + 1] f).mpr (hs x ((eval_lMap ψ ![x] f).mp hx)))
    exact fun x => (eval_lMap ψ ![x] f).mp (key x)

include hM in
/-- **The arithmetic reduct is a model of `IΣ₁`.** -/
theorem models_iSigma₁ : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
  Semantics.ModelsSet.of_subset (models_peano (N := N) A)
    (Set.union_subset_union_right _ (InductionScheme_subset fun _ => trivial))

/-! ### Definable predicates -/

omit [DecidableEq ι] [ORingStructure N] [ArithStd ι N] hM in
/-- A formula with parameters from `N` is a formula with free variables numbered by `ℕ`,
under a suitable assignment. -/
theorem exists_nat_formula [Inhabited N] {k : ℕ} (φ : Semiformula (LXIN ι) N k) :
    ∃ (ψ : Semiformula (LXIN ι) ℕ k) (f : ℕ → N),
      ∀ e, Semiformula.Eval (s := s) e f ψ ↔ Semiformula.Eval (s := s) e id φ := by
  classical
  refine ⟨Rew.rewriteMap φ.idxOfFVar ▹ φ, φ.enumerateFVar, fun e => ?_⟩
  rw [Semiformula.eval_rewriteMap]
  exact Semiformula.eval_enumerateFVar_idxOfFVar_eq_id φ e

omit [DecidableEq ι] [ArithStd ι N] hM in
theorem exists_nat_formula_pred {Q : N → Prop} (hQ : (LXIN ι).DefinablePred Q) :
    ∃ (ψ : Semiformula (LXIN ι) ℕ 1) (f : ℕ → N),
      ∀ x, Semiformula.Eval (s := s) ![x] f ψ ↔ Q x := by
  have : Inhabited N := ⟨0⟩
  obtain ⟨φ, hφ⟩ := hQ.definable
  obtain ⟨ψ, f, hψ⟩ := exists_nat_formula φ
  exact ⟨ψ, f, fun x => (hψ ![x]).trans (hφ ![x])⟩

omit [ArithStd ι N] in
include hM in
/-- **The induction scheme of `I_k` for definable predicates**: if `A_k(Q, x) → Q x` for
every `x` (the form read with `I_k` as `Q`), then `Q` holds on `I_k`. -/
theorem ind_definable (k : ι) {Q : N → Prop} (hQ : (LXIN ι).DefinablePred Q)
    (hprog : ∀ x, Semiformula.Eval (s := withIAt k Q) ![x] Empty.elim (A k) → Q x) :
    ∀ x, Imem k x → Q x := by
  obtain ⟨ψ, f, hψ⟩ := exists_nat_formula_pred hQ
  have e : (fun y => Semiformula.Eval (s := s) ![y] f ψ) = Q := funext fun y => propext (hψ y)
  intro x hx
  refine (hψ x).mp (ind_formula A k ψ f (fun y hy => (hψ y).mpr (hprog y ?_)) x hx)
  rwa [e] at hy

include hM in
/-- **Induction along the numbers for definable predicates.** -/
theorem succ_induction_definable {Q : N → Prop} (hQ : (LXIN ι).DefinablePred Q)
    (h0 : Q 0) (hs : ∀ x, Q x → Q (x + 1)) : ∀ x, Q x := by
  obtain ⟨ψ, f, hψ⟩ := exists_nat_formula_pred hQ
  intro x
  exact (hψ x).mp (succ_induction_formula A ψ f ((hψ 0).mpr h0)
    (fun x h => (hψ (x + 1)).mpr (hs x ((hψ x).mp h))) x)

omit [DecidableEq ι] hM in
/-- An arithmetic predicate with parameters is definable in `LXIN ι`. -/
theorem definable_of_arith {k : ℕ} {R : (Fin k → N) → Prop} {ℌ : HierarchySymbol}
    (h : ℌ.Definable R) : (LXIN ι).Definable R := by
  obtain ⟨φ, hφ⟩ := h.definable
  refine ⟨Semiformula.lMap (toLXIN ι) φ.val, fun v => ?_⟩
  rw [eval_lMap]
  exact HierarchySymbol.IsDefinedByWithParam.df hφ v

omit [DecidableEq ι] [ORingStructure N] [ArithStd ι N] hM in
theorem definable_imem (k : ι) : (LXIN ι).DefinablePred (Imem (s := s) k) :=
  ⟨Iat k #0, fun v => by rw [eval_IatN]; rfl⟩

omit [DecidableEq ι] [ORingStructure N] [ArithStd ι N] hM in
theorem definable_xmem : (LXIN ι).DefinablePred (Xmem (s := s)) :=
  ⟨Xat #0, fun v => by rw [eval_XatN]; rfl⟩

include hM in
/-- **Order induction along the numbers for definable predicates.** -/
theorem order_induction_definable {Q : N → Prop} (hQ : (LXIN ι).DefinablePred Q)
    (h : ∀ x, (∀ y < x, Q y) → Q x) : ∀ x, Q x := by
  have : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_iSigma₁ A
  have hQ' : (LXIN ι).DefinablePred fun x : N => ∀ y < x, Q y := by
    refine Language.Definable.all ?_
    refine Language.Definable.imp ?_ ?_
    · exact definable_of_arith (ℌ := 𝚺₀) (by definability)
    · exact hQ.retraction ![0]
  have key := succ_induction_definable A hQ' (fun y hy => absurd hy (by simp))
    (fun x hx y hy => by
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hy) with hy | rfl
      · exact hx y hy
      · exact h y hx)
  exact fun x => key (x + 1) x (lt_succ_iff_le.mpr le_rfl)

end Model

end Lift

end IDn

end OrdinalAnalysis
