/- Source: OrdinalAnalysis/IDn/LowerBoundAux.lean (X-free reinterpretation of the free predicate; hand port: in `LXJ` the predicate `X` (arity 1) cannot be renamed to `J` (arity 2), so the reinterpretation is a structure `xStruc s θ` reading `X` by a closed formula `θ`, and `substX θ` is its syntactic dual). -/

/-
  Helpers for the lower bound of `ID_ω` (`IDw/LowerBound.lean`): **reading the free predicate `X`
  as a formula `θ`**.

  In `IDn`, `X ↦ I_{k₀}` is a language homomorphism (`swapXIN`) and every axiom of `IDn n A` is
  stable under it (`eval_swap_of_mem_IDn`).  In `IDw` the free predicate `X` is unary and the
  inductively defined predicate `J` binary, so no homomorphism `LXJ →ᵥ LXJ` sends `X` to a column
  of `J`.  What replaces it is the reinterpretation of the *structure*:

      `xStruc s θ`   :=   `s`, with `X(t)` read as `θ(t)` (a closed formula `θ : Semisentence LXJ 1`,
                          evaluated in `s`); arithmetic and `J` unchanged,

  together with its syntactic dual `substX θ` (replace every `X(t)` by `θ(t)`), related by
  `eval_substX : s ⊧ substX θ φ ↔ xStruc s θ ⊧ φ`.  Every axiom of `IDw A` remains true in
  `xStruc s θ`, for `A` any form (`A` mentions no `X`): the closure axiom does not see `X`, and the
  induction axioms `indAxJ A F`, `succInd φ` for `F`, `φ` in `xStruc s θ` are the same axioms for
  `substX θ F`, `substX θ φ` in `s` (`eval_indAxJ_xStruc`, `eval_succInd_xStruc`).  Consequently
  (`provable_reread`) a theorem `σ` of `IDw A` is true in `xStruc s θ` for every arithmetically
  standard model `s` of `IDw A`.

  Contents.

    `substX`, `xStruc`                                the syntactic and the semantic reading
    `val_xStruc`, `eval_substX`                       they agree
    `xStruc_arithStd`                                 `xStruc s θ` is arithmetically standard
    `eval_AAt_congr`                                  `AAt` only sees the own place through its truth
    `eval_closureAxJ_xStruc`, `eval_indAxJ_xStruc`, `eval_succInd_xStruc`
    `eval_of_mem_IDw_xStruc`                          **every axiom of `IDw A` holds in `xStruc s θ`**
    `eval_of_provable_xStruc`                         **and hence every theorem**
-/
import OrdinalAnalysis.IDw.Lift
import OrdinalAnalysis.IDw.UpperAuxForms
import OrdinalAnalysis.IDw.Evaluate
import Foundation.FirstOrder.Completeness

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.IDw.Lift

/-! ### `X ↦ θ`, syntactically -/

section Subst

variable {ξ : Type*}

/-- **`φ` with every `X(t)` replaced by `θ(t)`** (`θ` a closed formula in one free slot). -/
def substX (θ : Semisentence LXJ 1) : {n : ℕ} → Semiformula LXJ ξ n → Semiformula LXJ ξ n
  | _, .verum => ⊤
  | _, .falsum => ⊥
  | _, .rel (Sum.inl r) v => .rel (Sum.inl r) v
  | _, .rel (Sum.inr XJRel.X) v => (Rewriting.emb θ : Semiformula LXJ ξ 1)/[v 0]
  | _, .rel (Sum.inr XJRel.J) v => .rel (Sum.inr XJRel.J) v
  | _, .nrel (Sum.inl r) v => .nrel (Sum.inl r) v
  | _, .nrel (Sum.inr XJRel.X) v => ∼((Rewriting.emb θ : Semiformula LXJ ξ 1)/[v 0])
  | _, .nrel (Sum.inr XJRel.J) v => .nrel (Sum.inr XJRel.J) v
  | _, .and φ ψ => substX θ φ ⋏ substX θ ψ
  | _, .or φ ψ => substX θ φ ⋎ substX θ ψ
  | _, .all φ => ∀¹ substX θ φ
  | _, .exs φ => ∃¹ substX θ φ

end Subst

/-! ### `X ↦ θ`, semantically -/

section Struc

variable {N : Type*}

set_option warn.classDefReducibility false in
/-- **The structure `s` with `X(t)` read as `θ(t)`**; arithmetic and `J` unchanged. -/
def xStruc (s : Structure LXJ N) (θ : Semisentence LXJ 1) : Structure LXJ N where
  func := fun {_} f v => s.func f v
  rel := fun {m} r v => match m, r with
    | _, Sum.inl r => s.rel (Sum.inl r) v
    | _, Sum.inr XJRel.X => Semiformula.Eval (s := s) ![v 0] Empty.elim θ
    | _, Sum.inr XJRel.J => s.rel (Sum.inr XJRel.J) v

variable (s : Structure LXJ N) (θ : Semisentence LXJ 1)

/-- Term values do not see `X`. -/
theorem val_xStruc {ξ : Type*} {n : ℕ} (e : Fin n → N) (f : ξ → N) (t : Semiterm LXJ ξ n) :
    Semiterm.val (s := xStruc s θ) e f t = Semiterm.val (s := s) e f t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func fn v ih =>
    simp only [Semiterm.val_func, Function.comp_def, ih]
    rfl

/-- **`substX` and `xStruc` agree.** -/
theorem eval_substX {ξ : Type*} : ∀ {n : ℕ} (φ : Semiformula LXJ ξ n) (e : Fin n → N) (f : ξ → N),
    Semiformula.Eval (s := s) e f (substX θ φ) ↔ Semiformula.Eval (s := xStruc s θ) e f φ := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro e f; simp [substX]
  | hfalsum => intro e f; simp [substX]
  | hrel r v =>
    intro e f
    rcases r with r | r
    · show s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e f (v i)) ↔
        s.rel (Sum.inl r) (fun i => Semiterm.val (s := xStruc s θ) e f (v i))
      simp only [val_xStruc]
    · cases r with
      | X =>
        show Semiformula.Eval (s := s) e f ((Rewriting.emb θ : Semiformula LXJ ξ 1)/[v 0]) ↔
          Semiformula.Eval (s := s) ![Semiterm.val (s := xStruc s θ) e f (v 0)] Empty.elim θ
        rw [Semiformula.eval_substs, Semiformula.eval_emb, val_xStruc,
          show (Semiterm.val (s := s) e f ∘ ![v 0] : Fin 1 → N) =
            ![Semiterm.val (s := s) e f (v 0)] from Matrix.comp₁ (v 0)]
      | J =>
        show s.rel (Sum.inr XJRel.J) (fun i => Semiterm.val (s := s) e f (v i)) ↔
          s.rel (Sum.inr XJRel.J) (fun i => Semiterm.val (s := xStruc s θ) e f (v i))
        simp only [val_xStruc]
  | hnrel r v =>
    intro e f
    rcases r with r | r
    · show ¬ s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e f (v i)) ↔
        ¬ s.rel (Sum.inl r) (fun i => Semiterm.val (s := xStruc s θ) e f (v i))
      simp only [val_xStruc]
    · cases r with
      | X =>
        show Semiformula.Eval (s := s) e f (∼((Rewriting.emb θ : Semiformula LXJ ξ 1)/[v 0])) ↔
          ¬ Semiformula.Eval (s := s) ![Semiterm.val (s := xStruc s θ) e f (v 0)] Empty.elim θ
        rw [LogicalConnective.HomClass.map_neg, Semiformula.eval_substs, Semiformula.eval_emb,
          val_xStruc,
          show (Semiterm.val (s := s) e f ∘ ![v 0] : Fin 1 → N) =
            ![Semiterm.val (s := s) e f (v 0)] from Matrix.comp₁ (v 0)]
        exact Iff.rfl
      | J =>
        show ¬ s.rel (Sum.inr XJRel.J) (fun i => Semiterm.val (s := s) e f (v i)) ↔
          ¬ s.rel (Sum.inr XJRel.J) (fun i => Semiterm.val (s := xStruc s θ) e f (v i))
        simp only [val_xStruc]
  | hand φ ψ ihφ ihψ =>
    intro e f
    simp only [substX, LogicalConnective.HomClass.map_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
    intro e f
    simp only [substX, LogicalConnective.HomClass.map_or, ihφ, ihψ]
  | hall φ ih =>
    intro e f
    simp only [substX, Semiformula.eval_all, ih]
  | hexs φ ih =>
    intro e f
    simp only [substX, Semiformula.eval_ex, ih]

end Struc

/-! ### Every axiom of `IDw A` holds in `xStruc s θ` -/

section Models

variable {N : Type} [ORingStructure N] (s : Structure LXJ N) (θ : Semisentence LXJ 1)

/-- The arithmetic reduct of `xStruc s θ` is that of `s`. -/
theorem xStruc_lMap : (xStruc s θ).lMap toLXJ = s.lMap toLXJ := rfl

/-- `J` is unchanged. -/
theorem jmem_xStruc (a b : N) :
    Jmem (s := xStruc s θ) a b ↔ Jmem (s := s) a b := Iff.rfl

/-- `xStruc s θ` is arithmetically standard when `s` is. -/
theorem xStruc_arithStd (hS : s.lMap toLXJ = Arithmetic.standardModel N) :
    (xStruc s θ).lMap toLXJ = Arithmetic.standardModel N := hS

/-- **`AAt` sees the own place only through its truth**: two structures with the same `J` and
standard arithmetic, and two formulas `F₁`, `F₂` with the same truth at level `y`, compile the
form `φ` to formulas of the same truth. -/
theorem eval_AAt_congr (s₁ s₂ : Structure LXJ N)
    (h₁ : s₁.lMap toLXJ = Arithmetic.standardModel N)
    (h₂ : s₂.lMap toLXJ = Arithmetic.standardModel N)
    (hJ : ∀ a b : N, Jmem (s := s₁) a b ↔ Jmem (s := s₂) a b)
    {ξ : Type*} (F₁ F₂ : Semiformula LXJ ξ 2) (f : ξ → N) (y : N)
    (hF : ∀ t, Semiformula.Eval (s := s₁) ![t, y] f F₁ ↔ Semiformula.Eval (s := s₂) ![t, y] f F₂)
    {n : ℕ} (φ : Semiformula LForm ξ n) (Y : Semiterm LXJ ξ n) (e : Fin n → N)
    (hY₁ : Semiterm.val (s := s₁) e f Y = y) (hY₂ : Semiterm.val (s := s₂) e f Y = y) :
    Semiformula.Eval (s := s₁) e f (AAt F₁ Y φ) ↔ Semiformula.Eval (s := s₂) e f (AAt F₂ Y φ) := by
  rw [Upper.eval_AAt (s := s₁) h₁ F₁ f y φ Y e hY₁, Upper.eval_AAt (s := s₂) h₂ F₂ f y φ Y e hY₂]
  have hP : (fun t => Semiformula.Eval (s := s₁) ![t, y] f F₁) =
      fun t => Semiformula.Eval (s := s₂) ![t, y] f F₂ := funext fun t => propext (hF t)
  have hQ : (fun a b => a < y ∧ Upper.Jm (s := s₁) a b) =
      fun a b => a < y ∧ Upper.Jm (s := s₂) a b :=
    funext fun a => funext fun b => propext (and_congr Iff.rfl (hJ a b))
  rw [hP, hQ]

variable (A : FormJ) (hS : s.lMap toLXJ = Arithmetic.standardModel N)
include hS

/-- **The closure axiom does not see `X`.** -/
theorem eval_closureAxJ_xStruc :
    Semiformula.Eval (s := xStruc s θ) ![] Empty.elim (closureAxJ A) ↔
      Semiformula.Eval (s := s) ![] Empty.elim (closureAxJ A) := by
  unfold closureAxJ
  simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply]
  refine forall_congr' fun y => forall_congr' fun x => ?_
  refine imp_congr ?_ ?_
  · refine eval_AAt_congr (xStruc s θ) s hS hS (fun a b => Iff.rfl) (Jat #1 #0) (Jat #1 #0)
      Empty.elim y (fun t => ?_) A #1 _ rfl rfl
    rw [eval_JatN (s := xStruc s θ), eval_JatN (s := s)]
    exact Iff.rfl
  · rw [eval_JatN (s := xStruc s θ), eval_JatN (s := s)]
    exact Iff.rfl

/-- **The induction axiom at `F` in `xStruc s θ` is the induction axiom at `substX θ F` in `s`.** -/
theorem eval_indAxJ_xStruc (F : Semiformula LXJ ℕ 2) :
    Semiformula.Eval (s := xStruc s θ) ![] Empty.elim (indAxJ A F) ↔
      Semiformula.Eval (s := s) ![] Empty.elim (indAxJ A (substX θ F)) := by
  have : Nonempty N := ⟨0⟩
  unfold indAxJ
  refine (Semiformula.eval_univCl (s := xStruc s θ) _).trans
    (Iff.trans (forall_congr' fun f => ?_) (Semiformula.eval_univCl (s := s) _).symm)
  simp only [Semiformula.Evalf, LogicalConnective.HomClass.map_imply, Semiformula.eval_all]
  refine forall_congr' fun y => imp_congr (forall_congr' fun x => imp_congr ?_ ?_)
    (forall_congr' fun x => imp_congr ?_ ?_)
  · refine eval_AAt_congr (xStruc s θ) s hS hS (fun a b => Iff.rfl) F (substX θ F) f y
      (fun t => (eval_substX s θ F _ f).symm) (Rewriting.emb A) #1 _ rfl rfl
  · exact (eval_substX s θ F _ f).symm
  · rw [eval_JatN (s := xStruc s θ), eval_JatN (s := s)]
    exact Iff.rfl
  · exact (eval_substX s θ F _ f).symm

/-- **The successor induction axiom at `φ` in `xStruc s θ` is that at `substX θ φ` in `s`.** -/
theorem eval_succInd_xStruc (φ : Semiformula LXJ ℕ 1) (f : ℕ → N) :
    Semiformula.Eval (s := xStruc s θ) ![] f (succInd φ) ↔
      Semiformula.Eval (s := s) ![] f (succInd (substX θ φ)) := by
  rw [@eval_succInd_iff LXJ _ N (xStruc s θ) φ f, @eval_succInd_iff LXJ _ N s (substX θ φ) f]
  simp only [val_xStruc, eval_substX]

/-- Equality is true equality in an arithmetically standard structure. -/
theorem eq_of_arithStd (a b : N) : s.rel (Language.Eq.eq : LXJ.Rel 2) ![a, b] ↔ a = b := by
  show s.rel (Sum.inl Language.Eq.eq) ![a, b] ↔ _
  rw [Upper.rel_inl_iff hS]
  exact Structure.eq_lang

/-- **Every axiom of `IDw A` is true in `xStruc s θ`**, if every axiom is true in `s`
(`s` arithmetically standard; `A` mentions no `X`). -/
theorem eval_of_mem_IDw_xStruc
    (hM : ∀ σ ∈ IDw A, Semiformula.Eval (s := s) ![] Empty.elim σ)
    {σ : Sentence LXJ} (hσ : σ ∈ IDw A) :
    Semiformula.Eval (s := xStruc s θ) ![] Empty.elim σ := by
  rcases (mem_IDw A).mp hσ with rfl | h | ⟨F, rfl⟩
  · exact (eval_closureAxJ_xStruc s θ A hS).mpr (hM _ (closureAxJ_mem_IDw A))
  · rcases h with h | h | h
    · let _ : Structure LXJ N := xStruc s θ
      have _ : Structure.Eq LXJ N := ⟨fun a b => eq_of_arithStd s hS a b⟩
      have _ : N↓[LXJ] ⊧* 𝗘𝗤 LXJ := Structure.Eq.models_eq LXJ N
      exact Theory.models N (𝗘𝗤 LXJ) h
    · obtain ⟨τ, hτ, rfl⟩ := h
      have h1 := hM _ (mem_IDw_of_paMinus A hτ)
      rw [Semiformula.eval_lMap] at h1 ⊢
      exact h1
    · obtain ⟨φ, -, rfl⟩ := h
      have : Nonempty N := ⟨0⟩
      refine (Semiformula.eval_univCl (s := xStruc s θ) _).mpr fun f => ?_
      have h1 := (Semiformula.eval_univCl (s := s) _).mp
        (hM _ (succInd_mem_IDw A (substX θ φ))) f
      exact (eval_succInd_xStruc s θ hS φ f).mpr h1
  · exact (eval_indAxJ_xStruc s θ A hS F).mpr (hM _ (indAxJ_mem_IDw A _))

/-- **Every theorem of `IDw A` is true in `xStruc s θ`**, for `s` an arithmetically standard
model of `IDw A`: the free predicate `X` may be read by any closed formula. -/
theorem eval_of_provable_xStruc
    (hM : ∀ σ ∈ IDw A, Semiformula.Eval (s := s) ![] Empty.elim σ)
    {σ : Sentence LXJ} (h : IDw A ⊢ σ) :
    Semiformula.Eval (s := xStruc s θ) ![] Empty.elim σ := by
  let _ : Structure LXJ N := xStruc s θ
  have : Nonempty N := ⟨0⟩
  have hT : N↓[LXJ] ⊧* IDw A :=
    Semantics.modelsSet_iff.mpr fun τ hτ => models_iff.mpr (eval_of_mem_IDw_xStruc s θ A hS hM hτ)
  exact models_iff.mp (models_of_provable hT h)

end Models

end IDw

end OrdinalAnalysis
