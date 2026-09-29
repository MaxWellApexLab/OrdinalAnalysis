/- Source: OrdinalAnalysis\IDn\Lift.lean (ID_n -> ID_omega: the level-family API is replaced by the binary J with an internal level; hand port). -/

/-
  Models of `IDw A` with standard arithmetic, and the passage from truth in all of them to
  provability.

  The ID_ω version of `IDn/Lift.lean`, for the theory `IDw A` of `IDw/Theory.lean` over the
  language `LXJ = ℒₒᵣ + {X} + {J}` with ONE binary inductively defined predicate `J(y, x)`
  ("`x` is in the `y`-th inductive set") governed by ONE operator form `A : FormJ` used at
  every level `y`.  Where `IDn/Lift.lean` reads a single unary `I_k` and states its closure
  and induction for a Lean-side level `k`, here the level is an object of the model: `y : N`,
  possibly nonstandard.

  **Arithmetically standard structures.**  An `LXJ`-structure on a type `N` carrying an
  `ORingStructure` is *arithmetically standard* (`ArithStd`) when its reduct to `ℒₒᵣ` is the
  structure of the arithmetic operations of `N`.  Every `LXJ`-structure whose equality is
  true equality is of this form for the operations it defines itself (`arithStd_of`), so by
  Foundation's completeness theorem a sentence true in every arithmetically standard model of
  `IDw A` is a theorem of `IDw A` (`provable_of_models`).

  **Inside such a model** `N` (write `J y x`, `X x`):

  * `N` is a model of `PA`, in particular of `IΣ₁` (`models_peano`, `models_iSigma₁`);
  * reading the `y`-th column of `J` as a predicate `T` (`withJAt y T`, every other column
    and `X` unchanged), `A_y(F, x)` -- the form compiled at level `y` with the own place
    read by the formula `F` -- is the form compiled with `J`'s `y`-th column read as the set
    defined by `F` (`eval_AAt_subst`);
  * **closure** of level `y`: if `A_y(J(y,·), x)` then `J y x` (`jmem_of_form`);
  * **the induction scheme** of level `y` for every predicate definable in `LXJ` with
    parameters (`ind_definable`): if `A_y(Q, x) → Q x` for all `x`, then `J y ⊆ Q`;
  * induction along the numbers for every such predicate (`succ_induction_definable`,
    `order_induction_definable`).
-/
import OrdinalAnalysis.IDw.Theory
import OrdinalAnalysis.IDw.Sound
import Foundation.FirstOrder.Completeness

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Lift

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

open scoped Classical

/-! ### Arithmetically standard structures -/

/-- The `ℒₒᵣ`-reduct of the `LXJ`-structure is the arithmetic of `N`. -/
class ArithStd (N : Type*) [ORingStructure N] [s : Structure LXJ N] : Prop where
  lMap_eq : s.lMap toLXJ = Arithmetic.standardModel N

section Std

variable {N : Type*} [ORingStructure N] [s : Structure LXJ N] [ArithStd N]

/-- Arithmetic terms have their arithmetic values. -/
theorem val_lMap {ξ : Type*} {n : ℕ} (t : Semiterm ℒₒᵣ ξ n) (e : Fin n → N) (f : ξ → N) :
    Semiterm.val (s := s) e f (Semiterm.lMap toLXJ t) =
      Semiterm.val (s := standardModel N) e f t := by
  rw [Semiterm.val_lMap, ArithStd.lMap_eq]

/-- Arithmetic formulas say what they say in the arithmetic of `N`. -/
theorem eval_lMap {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) (e : Fin n → N) (f : ξ → N) :
    Semiformula.Eval (s := s) e f (Semiformula.lMap toLXJ φ) ↔
      Semiformula.Eval (s := standardModel N) e f φ := by
  rw [Semiformula.eval_lMap, ArithStd.lMap_eq]

end Std

section Preds

variable {N : Type*} [s : Structure LXJ N]

/-- The binary relation read by `J`: `J y x` says `x` is in the `y`-th inductive set. -/
def Jmem (y x : N) : Prop := s.rel (Sum.inr XJRel.J) ![y, x]

/-- The predicate read by `X`. -/
def Xmem (x : N) : Prop := s.rel (Sum.inr XJRel.X) ![x]

theorem eval_JatN {ξ : Type*} {n : ℕ} (a b : Semiterm LXJ ξ n) (e : Fin n → N)
    (f : ξ → N) :
    Semiformula.Eval (s := s) e f (Jat a b) ↔
      Jmem (s := s) (Semiterm.val (s := s) e f a) (Semiterm.val (s := s) e f b) := by
  have h : (Semiterm.val (s := s) e f ∘ ![a, b] : Fin 2 → N)
      = ![Semiterm.val (s := s) e f a, Semiterm.val (s := s) e f b] := Matrix.comp₂ a b
  exact Iff.of_eq (congrArg (s.rel (Sum.inr XJRel.J)) h)

theorem eval_XatN {ξ : Type*} {n : ℕ} (t : Semiterm LXJ ξ n) (e : Fin n → N)
    (f : ξ → N) :
    Semiformula.Eval (s := s) e f (Xat t) ↔ Xmem (s := s) (Semiterm.val (s := s) e f t) := by
  have h : (Semiterm.val (s := s) e f ∘ ![t] : Fin 1 → N)
      = ![Semiterm.val (s := s) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg (s.rel (Sum.inr XJRel.X)) h)

end Preds

/-! ### Membership of the axioms of `IDw A` -/

section Membership

variable (A : FormJ)

theorem mem_IDw_of_eq {σ : Sentence LXJ} (h : σ ∈ 𝗘𝗤 LXJ) : σ ∈ IDw A :=
  paLXJ_subset_IDw A (Or.inl h)

theorem mem_IDw_of_paMinus {σ : Sentence ℒₒᵣ} (h : σ ∈ 𝗣𝗔⁻) :
    Semiformula.lMap toLXJ σ ∈ IDw A :=
  paLXJ_subset_IDw A (Or.inr (Or.inl ⟨σ, h, rfl⟩))

theorem succInd_mem_IDw (φ : Semiformula LXJ ℕ 1) :
    Semiformula.univCl (succInd φ) ∈ IDw A :=
  paLXJ_subset_IDw A (Or.inr (Or.inr ⟨φ, trivial, rfl⟩))

instance eq_weakerThan_IDw : 𝗘𝗤 LXJ ⪯ IDw A :=
  Entailment.WeakerThan.ofSubset fun _ h => mem_IDw_of_eq A h

end Membership

/-! ### From truth in the arithmetically standard models to provability -/

section Complete

variable {M : Type*} (s : Structure LXJ M)

set_option warn.classDefReducibility false in
/-- The arithmetic operations of an `LXJ`-structure. -/
@[reducible] def oringOf : ORingStructure M where
  zero := s.func (Language.Zero.zero : LXJ.Func 0) ![]
  one := s.func (Language.One.one : LXJ.Func 0) ![]
  add a b := s.func (Language.Add.add : LXJ.Func 2) ![a, b]
  mul a b := s.func (Language.Mul.mul : LXJ.Func 2) ![a, b]
  lt a b := s.rel (Language.LT.lt : LXJ.Rel 2) ![a, b]

/-- An `LXJ`-structure with true equality is arithmetically standard for its own
operations. -/
theorem arithStd_of
    (hEq : ∀ a b : M, s.rel (Language.Eq.eq : LXJ.Rel 2) ![a, b] ↔ a = b) :
    letI := oringOf s; ArithStd M := by
  let _ := oringOf s
  refine ⟨Structure.ext (funext₃ fun k f v => ?_) (funext₃ fun k r v => ?_)⟩
  · match k, f with
    | _, Language.ORing.Func.zero =>
      show s.func (Language.Zero.zero : LXJ.Func 0) v =
        s.func (Language.Zero.zero : LXJ.Func 0) ![]
      rw [Matrix.empty_eq v]
    | _, Language.ORing.Func.one =>
      show s.func (Language.One.one : LXJ.Func 0) v =
        s.func (Language.One.one : LXJ.Func 0) ![]
      rw [Matrix.empty_eq v]
    | _, Language.ORing.Func.add =>
      show s.func (Language.Add.add : LXJ.Func 2) v =
        s.func (Language.Add.add : LXJ.Func 2) ![v 0, v 1]
      rw [← Matrix.fun_eq_vec_two]
    | _, Language.ORing.Func.mul =>
      show s.func (Language.Mul.mul : LXJ.Func 2) v =
        s.func (Language.Mul.mul : LXJ.Func 2) ![v 0, v 1]
      rw [← Matrix.fun_eq_vec_two]
  · match k, r with
    | _, Language.ORing.Rel.eq =>
      show s.rel (Language.Eq.eq : LXJ.Rel 2) v = (v 0 = v 1)
      rw [Matrix.fun_eq_vec_two v]
      exact propext (hEq _ _)
    | _, Language.ORing.Rel.lt =>
      show s.rel (Language.LT.lt : LXJ.Rel 2) v =
        s.rel (Language.LT.lt : LXJ.Rel 2) ![v 0, v 1]
      rw [← Matrix.fun_eq_vec_two]

/-- **Provability from truth in the arithmetically standard models.**  A sentence true in
every arithmetically standard model of `IDw A` is a theorem of `IDw A`. -/
theorem provable_of_models (A : FormJ) {σ : Sentence LXJ}
    (H : ∀ (N : Type) [ORingStructure N] [Structure LXJ N] [ArithStd N],
      N↓[LXJ] ⊧* IDw A → N↓[LXJ] ⊧ σ) :
    IDw A ⊢ σ := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq]
  intro N _ s hEq hN
  let _ := oringOf s
  have _ := arithStd_of s (fun a b => hEq.eq a b)
  exact H N hN

end Complete

/-! ### Reading one column of `J` as a predicate -/

section WithJ

variable {N : Type*} [s : Structure LXJ N]

set_option warn.classDefReducibility false in
/-- The structure `N` with the `y`-th column of `J` read as `T`, every other symbol and
column unchanged. -/
def withJAt (y : N) (T : N → Prop) : Structure LXJ N where
  func := fun {_} f v => s.func f v
  rel := fun {m} r v => match m, r with
    | _, Sum.inl r => s.rel (Sum.inl r) v
    | _, Sum.inr XJRel.X => s.rel (Sum.inr XJRel.X) v
    | _, Sum.inr XJRel.J => if v 0 = y then T (v 1) else s.rel (Sum.inr XJRel.J) v

theorem val_withJAt (y : N) (T : N → Prop) {ξ : Type*} {n : ℕ} (e : Fin n → N) (f : ξ → N)
    (t : Semiterm LXJ ξ n) :
    Semiterm.val (s := withJAt y T) e f t = Semiterm.val (s := s) e f t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func F v ih =>
    simp only [Semiterm.val_func]
    exact congrArg _ (funext fun i => ih i)

theorem lMap_withJAt (y : N) (T : N → Prop) :
    (withJAt y T).lMap toLXJ = s.lMap toLXJ := rfl

theorem withJAt_rel_J_self (y : N) (T : N → Prop) (x : N) :
    (withJAt y T).rel (Sum.inr XJRel.J) ![y, x] ↔ T x := by
  show (if y = y then T x else _) ↔ T x
  rw [if_pos rfl]

theorem withJAt_rel_J_ne {y z : N} (h : z ≠ y) (T : N → Prop) (x : N) :
    (withJAt y T).rel (Sum.inr XJRel.J) ![z, x] ↔ Jmem (s := s) z x := by
  show (if z = y then T x else _) ↔ _
  rw [if_neg h]; rfl

theorem withJAt_rel_X (y : N) (T : N → Prop) (x : N) :
    (withJAt y T).rel (Sum.inr XJRel.X) ![x] ↔ Xmem (s := s) x := Iff.rfl

/-- Reading the `y`-th column of `J` as itself changes nothing. -/
theorem withJAt_self (y : N) : withJAt y (Jmem (s := s) y) = s := by
  refine Structure.ext (funext₃ fun _ _ _ => rfl) (funext₃ fun m r v => ?_)
  match m, r with
  | _, Sum.inl r => rfl
  | _, Sum.inr XJRel.X => rfl
  | _, Sum.inr XJRel.J =>
    show (if v 0 = y then Jmem (s := s) y (v 1) else s.rel (Sum.inr XJRel.J) v) = _
    split_ifs with h
    · subst h
      show s.rel (Sum.inr XJRel.J) ![v 0, v 1] = s.rel (Sum.inr XJRel.J) v
      rw [← Matrix.fun_eq_vec_two]
    · rfl

theorem eval_JatN_withJAt_of_eq {y : N} (T : N → Prop) {ξ : Type*} {n : ℕ}
    (a b : Semiterm LXJ ξ n) (e : Fin n → N) (f : ξ → N)
    (h : Semiterm.val (s := s) e f a = y) :
    Semiformula.Eval (s := withJAt y T) e f (Jat a b) ↔ T (Semiterm.val (s := s) e f b) := by
  have hc : (Semiterm.val (s := withJAt y T) e f ∘ ![a, b] : Fin 2 → N)
      = ![Semiterm.val (s := s) e f a, Semiterm.val (s := s) e f b] := by
    rw [Matrix.comp₂, val_withJAt, val_withJAt]
  refine (Iff.of_eq (congrArg ((withJAt y T).rel (Sum.inr XJRel.J)) hc)).trans ?_
  rw [h]
  exact withJAt_rel_J_self y T _

theorem eval_JatN_withJAt_of_ne {y : N} (T : N → Prop) {ξ : Type*} {n : ℕ}
    (a b : Semiterm LXJ ξ n) (e : Fin n → N) (f : ξ → N)
    (h : Semiterm.val (s := s) e f a ≠ y) :
    Semiformula.Eval (s := withJAt y T) e f (Jat a b) ↔
      Jmem (s := s) (Semiterm.val (s := s) e f a) (Semiterm.val (s := s) e f b) := by
  have hc : (Semiterm.val (s := withJAt y T) e f ∘ ![a, b] : Fin 2 → N)
      = ![Semiterm.val (s := s) e f a, Semiterm.val (s := s) e f b] := by
    rw [Matrix.comp₂, val_withJAt, val_withJAt]
  refine (Iff.of_eq (congrArg ((withJAt y T).rel (Sum.inr XJRel.J)) hc)).trans ?_
  exact withJAt_rel_J_ne h T _

theorem eval_ltAt_withJAt (y : N) (T : N → Prop) {ξ : Type*} {n : ℕ} (a b : Semiterm LXJ ξ n)
    (e : Fin n → N) (f : ξ → N) :
    Semiformula.Eval (s := withJAt y T) e f (ltAt a b) ↔
      Semiformula.Eval (s := s) e f (ltAt a b) := by
  show s.rel (Sum.inl Language.LT.lt) _ ↔ s.rel (Sum.inl Language.LT.lt) _
  simp only [val_withJAt]

section ArithStdLt

variable [ORingStructure N] [ArithStd N]

theorem eval_ltAt_iff {ξ : Type*} {n : ℕ} (a b : Semiterm LXJ ξ n) (e : Fin n → N) (f : ξ → N) :
    Semiformula.Eval (s := s) e f (ltAt a b) ↔
      Semiterm.val (s := s) e f a < Semiterm.val (s := s) e f b := by
  have h : (fun i => Semiterm.val (s := s) e f (![a, b] i))
      = ![Semiterm.val (s := s) e f a, Semiterm.val (s := s) e f b] := Matrix.comp₂ a b
  have key : ∀ v : Fin 2 → N, s.rel (Sum.inl Language.LT.lt) v ↔ v 0 < v 1 := by
    intro v
    have h1 : s.rel (Sum.inl Language.LT.lt) v =
        (s.lMap toLXJ).rel (Language.LT.lt : (ℒₒᵣ).Rel 2) v := rfl
    rw [h1, ArithStd.lMap_eq]
    exact Structure.lt_lang
  show s.rel (Sum.inl Language.LT.lt) _ ↔ _
  rw [h, key]
  rfl

/-- **`A_y(F, x)` reads `J`'s `y`-th column as the set defined by `F`**, the other columns
and `X` unchanged.  The generalisation of `Sound.eval_AAt_subst` to an arbitrary
arithmetically standard structure. -/
theorem eval_AAt_substN (hirr : ∀ z : N, ¬ z < z) (y : N) {ξ : Type*}
    (F : Semiformula LXJ ξ 2) {n : ℕ} (φ : Semiformula LForm ξ n) (f : ξ → N)
    (Y : Semiterm LXJ ξ n) (e : Fin n → N) (hYe : Semiterm.val (s := s) e f Y = y) :
    Semiformula.Eval (s := s) e f (AAt F Y φ) ↔
      Semiformula.Eval (s := withJAt y fun x => Semiformula.Eval (s := s) ![x, y] f F) e f
        (AAt (Jat #1 #0) Y φ) := by
  set T : N → Prop := fun x => Semiformula.Eval (s := s) ![x, y] f F with hT
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v =>
    rcases r with r | r
    · show s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e f (termCast (v i))) ↔
        s.rel (Sum.inl r) (fun i => Semiterm.val (s := withJAt y T) e f (termCast (v i)))
      simp only [val_withJAt]
    · cases r with
      | P =>
        simp only [AAt, Semiformula.eval_substs]
        have hc : (Semiterm.val (s := s) e f ∘ ![termCast (v 0), Y] : Fin 2 → N)
            = ![Semiterm.val (s := s) e f (termCast (v 0)), y] := by
          rw [Matrix.comp₂, hYe]
        have hc' : (Semiterm.val (s := withJAt y T) e f ∘ ![termCast (v 0), Y] : Fin 2 → N)
            = ![Semiterm.val (s := s) e f (termCast (v 0)), y] := by
          rw [Matrix.comp₂, val_withJAt, val_withJAt, hYe]
        rw [hc, hc', eval_JatN_withJAt_of_eq T _ _ _ _ (by simp)]
        exact Iff.rfl
      | Q =>
        have hne : ∀ a : N, a < y → a ≠ y := fun a h e => hirr y (e ▸ h)
        simp only [AAt, LogicalConnective.HomClass.map_and, eval_ltAt_withJAt, eval_ltAt_iff,
          eval_JatN (s := s), hYe]
        constructor
        · rintro ⟨hlt, hmem⟩
          refine ⟨hlt, ?_⟩
          rw [eval_JatN_withJAt_of_ne T _ _ _ _ (hne _ hlt)]
          exact hmem
        · rintro ⟨hlt, hmem⟩
          rw [eval_JatN_withJAt_of_ne T _ _ _ _ (hne _ hlt)] at hmem
          exact ⟨hlt, hmem⟩
  | hnrel r v =>
    rcases r with r | r
    · show ¬s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e f (termCast (v i))) ↔
        ¬s.rel (Sum.inl r) (fun i => Semiterm.val (s := withJAt y T) e f (termCast (v i)))
      simp only [val_withJAt]
    · cases r with
      | P =>
        simp only [AAt, LogicalConnective.HomClass.map_neg, Semiformula.eval_substs]
        have hc : (Semiterm.val (s := s) e f ∘ ![termCast (v 0), Y] : Fin 2 → N)
            = ![Semiterm.val (s := s) e f (termCast (v 0)), y] := by
          rw [Matrix.comp₂, hYe]
        have hc' : (Semiterm.val (s := withJAt y T) e f ∘ ![termCast (v 0), Y] : Fin 2 → N)
            = ![Semiterm.val (s := s) e f (termCast (v 0)), y] := by
          rw [Matrix.comp₂, val_withJAt, val_withJAt, hYe]
        rw [hc, hc', eval_JatN_withJAt_of_eq T _ _ _ _ (by simp)]
        exact not_congr Iff.rfl
      | Q =>
        have hne : ∀ a : N, a < y → a ≠ y := fun a h e => hirr y (e ▸ h)
        simp only [AAt, LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_and,
          eval_ltAt_withJAt, eval_ltAt_iff, eval_JatN (s := s), hYe]
        apply not_congr
        constructor
        · rintro ⟨hlt, hmem⟩
          refine ⟨hlt, ?_⟩
          rw [eval_JatN_withJAt_of_ne T _ _ _ _ (hne _ hlt)]
          exact hmem
        · rintro ⟨hlt, hmem⟩
          rw [eval_JatN_withJAt_of_ne T _ _ _ _ (hne _ hlt)] at hmem
          exact ⟨hlt, hmem⟩
  | hand φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := s) e f (AAt F Y φ ⋏ AAt F Y ψ) ↔
      Semiformula.Eval (s := withJAt y T) e f (AAt (Jat #1 #0) Y φ ⋏ AAt (Jat #1 #0) Y ψ)
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact and_congr (ihφ Y e hYe) (ihψ Y e hYe)
  | hor φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := s) e f (AAt F Y φ ⋎ AAt F Y ψ) ↔
      Semiformula.Eval (s := withJAt y T) e f (AAt (Jat #1 #0) Y φ ⋎ AAt (Jat #1 #0) Y ψ)
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact or_congr (ihφ Y e hYe) (ihψ Y e hYe)
  | hall φ ih =>
    show Semiformula.Eval (s := s) e f (∀¹ AAt F (Rew.bShift Y) φ) ↔
      Semiformula.Eval (s := withJAt y T) e f (∀¹ AAt (Jat #1 #0) (Rew.bShift Y) φ)
    rw [Semiformula.eval_all, Semiformula.eval_all]
    exact forall_congr' fun x =>
      ih (Rew.bShift Y) (x :> e) (by rw [Semiterm.val_bShift]; exact hYe)
  | hexs φ ih =>
    show Semiformula.Eval (s := s) e f (∃¹ AAt F (Rew.bShift Y) φ) ↔
      Semiformula.Eval (s := withJAt y T) e f (∃¹ AAt (Jat #1 #0) (Rew.bShift Y) φ)
    rw [Semiformula.eval_ex, Semiformula.eval_ex]
    exact exists_congr fun x =>
      ih (Rew.bShift Y) (x :> e) (by rw [Semiterm.val_bShift]; exact hYe)

end ArithStdLt

end WithJ

/-! ### Inside an arithmetically standard model of `IDw A` -/

section Model

variable {N : Type*} [ORingStructure N] [s : Structure LXJ N] [ArithStd N]
variable (A : FormJ)

variable [hM : N↓[LXJ] ⊧* IDw A]

omit [ArithStd N] in
include hM in
theorem eval_of_mem_IDwN {σ : Sentence LXJ} (h : σ ∈ IDw A) :
    Semiformula.Eval (s := s) ![] Empty.elim σ :=
  models_iff.mp (Semantics.modelsSet_iff.mp hM h)

omit [ORingStructure N] [ArithStd N] s hM in
/-- **`AAt` with the `ξ = Empty` and `ξ = ℕ` copies of `A` agree** in every structure. -/
theorem eval_AAt_embN (t : Structure LXJ N) (φ : Semiformula LForm Empty 2) (e : Fin 2 → N)
    (f : ℕ → N) :
    Semiformula.Eval (s := t) e f
        (AAt (Jat #1 #0) (Rew.emb (#1 : Semiterm LXJ Empty 2)) (Rewriting.emb φ)) ↔
      Semiformula.Eval (s := t) e Empty.elim
        (AAt (Jat #1 #0) (#1 : Semiterm LXJ Empty 2) φ) := by
  rw [AAt_emb, Semiformula.eval_emb]

omit [ArithStd N] in
include hM in
/-- **Closure** of level `y`: `A_y(J(y,·), x) → J y x`. -/
theorem jmem_of_form (y x : N)
    (h : Semiformula.Eval (s := s) ![x, y] Empty.elim (AAt (Jat #1 #0) #1 A)) :
    Jmem (s := s) y x := by
  have hc := eval_of_mem_IDwN (N := N) A (closureAxJ_mem_IDw A)
  rw [closureAxJ, Semiformula.eval_all] at hc
  have h1 := hc y
  rw [Semiformula.eval_all] at h1
  have h2 := h1 x
  rw [LogicalConnective.HomClass.map_imply] at h2
  exact (eval_JatN (s := s) _ _ _ _).mp (h2 h)

omit [ArithStd N] in
include hM in
/-- Closure of level `y`, with the form read in `withJAt y (J y)`. -/
theorem jmem_of_form' (y x : N)
    (h : Semiformula.Eval (s := withJAt y (Jmem (s := s) y)) ![x, y] Empty.elim
      (AAt (Jat #1 #0) #1 A)) :
    Jmem (s := s) y x := by
  rw [withJAt_self] at h
  exact jmem_of_form A y x h

include hM in
/-- **The arithmetic reduct is a model of `PA⁻`.** -/
theorem models_paMinus : N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  Semantics.modelsSet_iff.mpr fun σ hσ => models_iff.mpr <| by
    have h := eval_of_mem_IDwN (N := N) A (mem_IDw_of_paMinus A hσ)
    rw [eval_lMap] at h
    exact h

include hM in
/-- The order of a model is irreflexive. -/
theorem lt_irrefl_model : ∀ z : N, ¬z < z := by
  have := models_paMinus (N := N) A
  exact Arithmetic.lt_irrefl

include hM in
/-- **The induction scheme of `J`** at level `y`, for a formula `F` in the two variables
`(x, y)` with an assignment `f` for its parameters. -/
theorem ind_formula (y : N) (F : Semiformula LXJ ℕ 2) (f : ℕ → N)
    (hprog : ∀ x, Semiformula.Eval (s := withJAt y fun z => Semiformula.Eval (s := s) ![z, y] f F)
      ![x, y] Empty.elim (AAt (Jat #1 #0) #1 A) → Semiformula.Eval (s := s) ![x, y] f F) :
    ∀ x, Jmem (s := s) y x → Semiformula.Eval (s := s) ![x, y] f F := by
  have hi := eval_of_mem_IDwN (N := N) A (indAxJ_mem_IDw A F)
  have : Nonempty N := ⟨0⟩
  rw [indAxJ] at hi
  have hf := (Semiformula.eval_univCl (s := s) _).mp hi f
  simp only [Semiformula.Evalf, LogicalConnective.HomClass.map_imply,
    Semiformula.eval_all] at hf
  have hirr := lt_irrefl_model (N := N) A
  intro x hx
  refine hf y (fun z hz => hprog z ?_) x ((eval_JatN (s := s) (#1 : Semiterm LXJ ℕ 2) #0
    ![x, y] f).mpr hx)
  have h1 := (eval_AAt_substN (N := N) hirr y F (Rewriting.emb A) f (#1 : Semiterm LXJ ℕ 2)
    ![z, y] rfl).mp hz
  exact (eval_AAt_embN (withJAt y fun z => Semiformula.Eval (s := s) ![z, y] f F) A ![z, y]
    f).mp h1

omit [ArithStd N] hM in
theorem lMap_zero_term :
    Semiterm.lMap toLXJ ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 0) =
      ((0 : ℕ) : Semiterm LXJ ℕ 0) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral, Semiterm.Operator.Zero.term_eq]

omit [ArithStd N] hM in
theorem lMap_succ_term :
    Semiterm.lMap toLXJ (‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1) =
      (‘(#0 + 1)’ : Semiterm LXJ ℕ 1) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, Semiterm.Operator.Add.term_eq]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => k.elim0) j
    simp [Function.comp_def, Matrix.empty_eq]

omit hM in
theorem val_zero_term (f : ℕ → N) :
    Semiterm.val (s := s) ![] f ((0 : ℕ) : Semiterm LXJ ℕ 0) = 0 := by
  rw [← lMap_zero_term, val_lMap]
  simp [Semiterm.val_operator]

omit hM in
theorem val_succ_term (f : ℕ → N) (x : N) :
    Semiterm.val (s := s) ![x] f (‘(#0 + 1)’ : Semiterm LXJ ℕ 1) = x + 1 := by
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
/-- **Induction along the numbers** at a formula `φ` of `LXJ` with an assignment `f`. -/
theorem succ_induction_formula (φ : Semiformula LXJ ℕ 1) (f : ℕ → N)
    (h0 : Semiformula.Eval (s := s) ![0] f φ)
    (hs : ∀ x, Semiformula.Eval (s := s) ![x] f φ → Semiformula.Eval (s := s) ![x + 1] f φ) :
    ∀ x, Semiformula.Eval (s := s) ![x] f φ := by
  have hi := eval_of_mem_IDwN (N := N) A (succInd_mem_IDw A φ)
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
  · have h := eval_of_mem_IDwN (N := N) A (mem_IDw_of_paMinus A hσ)
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
    have key := succ_induction_formula A (Semiformula.lMap toLXJ ψ) f
      ((eval_lMap ψ ![0] f).mpr h0)
      (fun x hx => (eval_lMap ψ ![x + 1] f).mpr (hs x ((eval_lMap ψ ![x] f).mp hx)))
    exact fun x => (eval_lMap ψ ![x] f).mp (key x)

include hM in
/-- **The arithmetic reduct is a model of `IΣ₁`.** -/
theorem models_iSigma₁ : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
  Semantics.ModelsSet.of_subset (models_peano (N := N) A)
    (Set.union_subset_union_right _ (InductionScheme_subset fun _ => trivial))

/-! ### Definable predicates -/

omit [ORingStructure N] [ArithStd N] hM in
/-- A formula with parameters from `N` is a formula with free variables numbered by `ℕ`,
under a suitable assignment. -/
theorem exists_nat_formula [Inhabited N] {k : ℕ} (φ : Semiformula LXJ N k) :
    ∃ (ψ : Semiformula LXJ ℕ k) (f : ℕ → N),
      ∀ e, Semiformula.Eval (s := s) e f ψ ↔ Semiformula.Eval (s := s) e id φ := by
  classical
  refine ⟨Rew.rewriteMap φ.idxOfFVar ▹ φ, φ.enumerateFVar, fun e => ?_⟩
  rw [Semiformula.eval_rewriteMap]
  exact Semiformula.eval_enumerateFVar_idxOfFVar_eq_id φ e

omit [ArithStd N] hM in
theorem exists_nat_formula_pred {Q : N → Prop} (hQ : LXJ.DefinablePred Q) :
    ∃ (ψ : Semiformula LXJ ℕ 1) (f : ℕ → N),
      ∀ x, Semiformula.Eval (s := s) ![x] f ψ ↔ Q x := by
  have : Inhabited N := ⟨0⟩
  obtain ⟨φ, hφ⟩ := hQ.definable
  obtain ⟨ψ, f, hψ⟩ := exists_nat_formula φ
  exact ⟨ψ, f, fun x => (hψ ![x]).trans (hφ ![x])⟩

include hM in
/-- **The induction scheme of `J` at level `y` for definable predicates**: if
`A_y(Q, x) → Q x` for every `x` (the form read with the `y`-th column of `J` as `Q`), then
`Q` holds on `J y`. -/
theorem ind_definable (y : N) {Q : N → Prop} (hQ : LXJ.DefinablePred Q)
    (hprog : ∀ x, Semiformula.Eval (s := withJAt y Q) ![x, y] Empty.elim
      (AAt (Jat #1 #0) #1 A) → Q x) :
    ∀ x, Jmem (s := s) y x → Q x := by
  obtain ⟨ψ, f, hψ⟩ := exists_nat_formula_pred (s := s) hQ
  let F : Semiformula LXJ ℕ 2 := ψ/[(#0 : Semiterm LXJ ℕ 2)]
  have hF : ∀ x z : N, Semiformula.Eval (s := s) ![x, z] f F ↔ Q x := by
    intro x z
    show Semiformula.Eval (s := s) ![x, z] f (ψ/[(#0 : Semiterm LXJ ℕ 2)]) ↔ _
    rw [Semiformula.eval_substs, Matrix.comp₁]
    exact hψ x
  have e : (fun z => Semiformula.Eval (s := s) ![z, y] f F) = Q :=
    funext fun z => propext (hF z y)
  intro x hx
  refine (hF x y).mp (ind_formula A y F f (fun z hz => (hF z y).mpr (hprog z ?_)) x hx)
  rwa [e] at hz

include hM in
/-- **Induction along the numbers for definable predicates.** -/
theorem succ_induction_definable {Q : N → Prop} (hQ : LXJ.DefinablePred Q)
    (h0 : Q 0) (hs : ∀ x, Q x → Q (x + 1)) : ∀ x, Q x := by
  obtain ⟨ψ, f, hψ⟩ := exists_nat_formula_pred (s := s) hQ
  intro x
  exact (hψ x).mp (succ_induction_formula A ψ f ((hψ 0).mpr h0)
    (fun x h => (hψ (x + 1)).mpr (hs x ((hψ x).mp h))) x)

omit [ORingStructure N] [ArithStd N] hM in
/-- An arithmetic predicate with parameters is definable in `LXJ`. -/
theorem definable_of_arith [ORingStructure N] [ArithStd N] {k : ℕ} {R : (Fin k → N) → Prop}
    {ℌ : HierarchySymbol} (h : ℌ.Definable R) : LXJ.Definable R := by
  obtain ⟨φ, hφ⟩ := h.definable
  refine ⟨Semiformula.lMap toLXJ φ.val, fun v => ?_⟩
  rw [eval_lMap]
  exact HierarchySymbol.IsDefinedByWithParam.df hφ v

omit [ORingStructure N] [ArithStd N] hM in
/-- Each column of `J` is definable, with the level as a parameter. -/
theorem definable_jmem (y : N) : LXJ.DefinablePred (Jmem (s := s) y) :=
  ⟨Jat &y #0, fun v => by rw [eval_JatN]; rfl⟩

omit [ORingStructure N] [ArithStd N] hM in
/-- `J` itself is a definable binary relation. -/
theorem definable_jmem₂ : LXJ.DefinableRel (fun y x : N => Jmem (s := s) y x) :=
  ⟨Jat #0 #1, fun v => by rw [eval_JatN]; rfl⟩

omit [ORingStructure N] [ArithStd N] hM in
theorem definable_xmem : LXJ.DefinablePred (Xmem (s := s)) :=
  ⟨Xat #0, fun v => by rw [eval_XatN]; rfl⟩

include hM in
/-- **Order induction along the numbers for definable predicates.** -/
theorem order_induction_definable {Q : N → Prop} (hQ : LXJ.DefinablePred Q)
    (h : ∀ x, (∀ y < x, Q y) → Q x) : ∀ x, Q x := by
  have : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_iSigma₁ A
  have hQ' : LXJ.DefinablePred fun x : N => ∀ y < x, Q y := by
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

end IDw

end OrdinalAnalysis
