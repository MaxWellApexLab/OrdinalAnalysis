/-
  The Foundation idiom for proving `paLX ⊢ σ` by semantics.

  Foundation is semantic-first: a derivation `T ⊢ σ` for a concrete sentence is
  obtained by fixing an arbitrary model `M` of `T`, doing ordinary mathematics
  inside `M`, and appealing to completeness.  This file isolates that idiom for
  the theory `paLX` of `Setup.lean` and demonstrates it end to end:

  (a) `paLX_proves_of_models` / `paLX_proves_of_models_eq` — completeness in
      the exact instance shape Foundation needs;
  (b) `paLX_refl` — a trivial arithmetic sentence, `∀ x, x = x`;
  (c) `paLX_induction` / `paLX_indX` — the induction axiom for a formula that
      mentions the fresh predicate `X`, first invoked inside a model and then
      turned into a derivation of a sentence that is *not* literally an axiom;
  (d) `paLX_proves_univCl_of_forall` and the evaluation lemmas for `Xat`,
      `below`, `Prog`, `TI`, `TIupto` — the bridge from Lean-level statements
      `∀ x : M, P x` to object-language sentences.
-/
import OrdinalAnalysis.Gentzen.Setup
import Foundation.FirstOrder.Completeness

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.Idiom

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### (a) Completeness for `paLX`

`Theory.Proof.complete : T ⊨[Struc.{max u w} L] φ → T ⊢ φ`
(Foundation/FirstOrder/Completeness/CounterModel.lean:241) is the general
completeness theorem.  `LX : Language.{0}`, so the models range over `Type 0`
and the universe instantiation is `.{0, 0}`.  The hypothesis is unpacked by

  `consequence_iff'   : T ⊨[Struc.{v,u} L] φ ↔
      ∀ (M : Type v) [Nonempty M] [Structure L M] [M↓[L] ⊧* T], M↓[L] ⊧ φ`
      (Foundation/FirstOrder/Basic/Semantics/Semantics.lean:550)
  `consequence_iff_eq' : … ↔ ∀ (M : Type v) [Nonempty M] [Structure L M]
      [Structure.Eq L M] [M↓[L] ⊧* T], M↓[L] ⊧ φ`   (needs `[𝗘𝗤 L ⪯ T]`)
      (Foundation/FirstOrder/Basic/Eq.lean:276)

The second form is the one to use: `paLX` contains `𝗘𝗤 LX` (instance
`paLX_eqTheory` in `Setup.lean`), and `Structure.Eq LX M` makes the object
equality `“x = y”` evaluate to Lean's `x = y` under `simp`. -/

/-- Completeness for `paLX`, plain form. -/
theorem paLX_proves_of_models {σ : Sentence LX}
    (h : ∀ (M : Type) [Nonempty M] [Structure LX M] [M↓[LX] ⊧* paLX],
      M↓[LX] ⊧ σ) :
    paLX ⊢ σ := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff']
  intro M _ _ _
  exact h M

/-- Completeness for `paLX`, with equality interpreted as Lean equality.
This is the form to use in practice. -/
theorem paLX_proves_of_models_eq {σ : Sentence LX}
    (h : ∀ (M : Type) [Nonempty M] [Structure LX M] [Structure.Eq LX M]
      [M↓[LX] ⊧* paLX], M↓[LX] ⊧ σ) :
    paLX ⊢ σ := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ _
  exact h M

/-- Soundness in the matching shape: a `paLX`-derivation holds in every model.
(`Theory.Proof.sound` at Foundation/FirstOrder/Basic/Soundness.lean, composed
with `consequence_iff'`.)  This is how previously proved sentences are reused
inside a model. -/
theorem models_of_paLX_proof {σ : Sentence LX} (h : paLX ⊢ σ)
    (M : Type) [Nonempty M] [Structure LX M] [M↓[LX] ⊧* paLX] :
    M↓[LX] ⊧ σ :=
  consequence_iff'.mp (Theory.Proof.sound h) M

/-! ### (b) A trivial arithmetic sentence -/

/-- `∀ x, x = x` as a sentence of `LX`. -/
def reflStatement : Sentence LX := “∀ x, x = x”

theorem paLX_refl : paLX ⊢ reflStatement := by
  apply paLX_proves_of_models_eq
  intro M _ _ _ _
  simp [reflStatement, models_iff]

/-! ### Evaluating the predicate `X` -/

/-- The interpretation of the fresh predicate in a structure for `LX`.

A `def`, not an `abbrev`, on purpose: `XLang` in `Setup.lean` is a `def`, so the
symbol `Sum.inr XRel.X : LX.Rel 1` is only well typed after unfolding
`XLang.Rel 1 = XRel 1` at default transparency.  `rw` and `simp` match at
reducible/instances transparency and therefore refuse to rewrite *any* term
containing that symbol ("target expression is not type-correct under the
`implicit` transparency level").  Keeping the symbol hidden behind an opaque
`Xrel` means `simp` only ever sees `Xrel M x`. -/
def Xrel (M : Type*) [Structure LX M] (x : M) : Prop :=
  Structure.rel (L := LX) (Sum.inr XRel.X) ![x]

/-- `X(t)` evaluates to `Xrel` at the value of `t`.  Proved by definitional
unfolding (`Semiformula.eval_rel` is `of_eq rfl`) plus one `funext`; see the
note on `Xrel` for why neither `rw` nor `simp` can do this step. -/
@[simp] theorem eval_Xat {M : Type*} [Structure LX M] {n : ℕ}
    (t : Semiterm LX ℕ n) (e : Fin n → M) (f : ℕ → M) :
    (Xat t).Eval e f ↔ Xrel M (t.val e f) := by
  have h : (Semiterm.val e f ∘ ![t] : Fin 1 → M) = ![t.val e f] :=
    Matrix.comp₁ t
  exact Iff.of_eq (congrArg (Structure.rel (L := LX) (Sum.inr XRel.X)) h)

/-! ### (c) Induction over a formula mentioning `X`

`InductionScheme LX Set.univ = { ψ | ∃ φ, True ∧ ψ = (succInd φ).univCl }`
(Foundation/FirstOrder/Arithmetic/Schemata.lean:26), and
`succInd φ = “!φ 0 → (∀ x, !φ x → !φ (x + 1)) → ∀ x, !φ x”` (ibid.:18).
Membership of an instance in `paLX` is therefore the raw witness
`⟨ψ, trivial, rfl⟩` pushed through the two set unions; `Theory.models`
(Semantics.lean:539) turns membership into truth in `M`. -/

/-- The induction axiom for `ψ` is an axiom of `paLX`. -/
theorem succInd_mem_paLX (ψ : Semiformula LX ℕ 1) :
    (succInd ψ).univCl ∈ paLX := by
  change (succInd ψ).univCl ∈
    𝗘𝗤 LX ∪ (Theory.lMap toLX 𝗣𝗔⁻ ∪ InductionScheme LX Set.univ)
  exact Set.mem_union_right _ (Set.mem_union_right _
    (show (succInd ψ).univCl ∈ InductionScheme LX Set.univ from
      ⟨ψ, trivial, rfl⟩))

/-- Induction for an arbitrary `LX`-formula `ψ` (which may mention `X`),
invoked inside a model of `paLX`.  The numerals stay as term values because
an arbitrary `Structure LX M` carries no `Zero M`/`Add M` to reduce them to. -/
theorem paLX_induction {M : Type*} [Nonempty M] [Structure LX M]
    [M↓[LX] ⊧* paLX] (ψ : Semiformula LX ℕ 1) (f : ℕ → M) :
    ψ.Eval ![((0 : ℕ) : Semiterm LX ℕ 0).val ![] f] f →
    (∀ x : M,
      ψ.Eval ![x] f →
      ψ.Eval ![(‘(#0 + 1)’ : Semiterm LX ℕ 1).val ![x] f] f) →
    ∀ x : M, ψ.Eval ![x] f := by
  have hInd : M↓[LX] ⊧ (succInd ψ).univCl :=
    Theory.models (T := paLX) M (succInd_mem_paLX ψ)
  revert f
  simpa [models_iff, Semiformula.eval_univCl, succInd,
    Semiformula.eval_substs, Matrix.constant_eq_singleton] using hInd

/-- Induction specialised to the predicate `X` itself. -/
theorem paLX_X_induction {M : Type*} [Nonempty M] [Structure LX M]
    [M↓[LX] ⊧* paLX] (f : ℕ → M)
    (h0 : Xrel M (((0 : ℕ) : Semiterm LX ℕ 0).val ![] f))
    (hs : ∀ x : M, Xrel M x →
      Xrel M ((‘(#0 + 1)’ : Semiterm LX ℕ 1).val ![x] f)) :
    ∀ x : M, Xrel M x := by
  have := paLX_induction (M := M) (Xat #0) f
  simp only [eval_Xat, Semiterm.val_bvar, Matrix.cons_val_zero] at this
  exact this h0 hs

/-- `(X 0 ∧ ∀ x (X x → X (x + 1))) → ∀ x, X x`, written with the primitive
connectives so that it is *not* syntactically the axiom
`(succInd (Xat #0)).univCl`; proving it therefore has to go through the
model. -/
def indXStatement : Sentence LX :=
  (∼(Xat ((0 : ℕ) : Semiterm LX ℕ 0) ⋏
      (∀¹ (∼(Xat (#0 : Semiterm LX ℕ 1)) ⋎
        Xat (‘(#0 + 1)’ : Semiterm LX ℕ 1)))) ⋎
    (∀¹ (Xat (#0 : Semiterm LX ℕ 1)))).univCl

theorem paLX_indX : paLX ⊢ indXStatement := by
  apply paLX_proves_of_models_eq
  intro M _ _ _ _
  rw [models_iff]
  simp only [indXStatement, Semiformula.eval_univCl]
  intro f
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.HomClass.map_and, LogicalConnective.Prop.or_eq,
    LogicalConnective.Prop.neg_eq, LogicalConnective.Prop.and_eq,
    Semiformula.eval_all, eval_Xat, Semiterm.val_bvar, Matrix.cons_val_zero]
  by_cases h : Xrel M (((0 : ℕ) : Semiterm LX ℕ 0).val ![] f) ∧
      ∀ x : M, ¬Xrel M x ∨ Xrel M ((‘(#0 + 1)’ : Semiterm LX ℕ 1).val ![x] f)
  · right
    apply paLX_X_induction f h.1
    intro x hx
    rcases h.2 x with hnot | hsucc
    · exact (hnot hx).elim
    · exact hsucc
  · left
    exact h

/-- The same sentence obtained syntactically: the induction axiom for `X` is
literally a member of `paLX`. -/
theorem paLX_succInd_X : paLX ⊢ (succInd (Xat (#0 : Semiterm LX ℕ 1))).univCl :=
  Entailment.by_axm (succInd_mem_paLX _)

/-! ### (d) The bridge from Lean-level statements to sentences

A universally quantified sentence is written as `(∀¹ φ).univCl` with
`φ : Semiformula LX ℕ 1`; `Semiformula.eval_univCl` (Semantics.lean:451) and
`Semiformula.eval_all` (ibid.:263) unfold it to
`∀ (f : ℕ → M) (x : M), φ.Eval ![x] f`. -/

/-- From a Lean proof in every model to a derivation of the universal closure. -/
theorem paLX_proves_univCl_of_forall (φ : Semiformula LX ℕ 1)
    (h : ∀ (M : Type) [Nonempty M] [Structure LX M] [Structure.Eq LX M]
      [M↓[LX] ⊧* paLX], ∀ (f : ℕ → M) (x : M), φ.Eval ![x] f) :
    paLX ⊢ (∀¹ φ).univCl := by
  apply paLX_proves_of_models_eq
  intro M _ _ _ _
  rw [models_iff]
  simp only [Semiformula.eval_univCl, Semiformula.eval_all]
  intro f x
  exact h M f x

/-- Conversely, a derivation of `(∀¹ φ).univCl` yields the Lean statement in
every model. -/
theorem forall_of_paLX_proves_univCl (φ : Semiformula LX ℕ 1)
    (h : paLX ⊢ (∀¹ φ).univCl)
    (M : Type) [Nonempty M] [Structure LX M] [M↓[LX] ⊧* paLX]
    (f : ℕ → M) (x : M) : φ.Eval ![x] f := by
  have := models_of_paLX_proof h M
  rw [models_iff] at this
  simp only [Semiformula.eval_univCl, Semiformula.eval_all] at this
  exact this f x

/-! Evaluation of the `Setup.lean` formulas.  `prec.Eval ![y, x] f` is the
meaning of `y ≺ x`. -/

@[simp] theorem eval_precAt {M : Type*} [Structure LX M]
    (prec : Semiformula LX ℕ 2) {n : ℕ} (y x : Semiterm LX ℕ n)
    (e : Fin n → M) (f : ℕ → M) :
    (precAt prec y x).Eval e f ↔ prec.Eval ![y.val e f, x.val e f] f := by
  simp [precAt]

@[simp] theorem eval_below {M : Type*} [Structure LX M]
    (prec : Semiformula LX ℕ 2) (x : M) (f : ℕ → M) :
    (below prec).Eval ![x] f ↔
      ∀ y : M, prec.Eval ![y, x] f → Xrel M y := by
  simp [below]
  constructor
  · intro h y hy
    rcases h y with hnot | hX
    · exact (hnot hy).elim
    · exact hX
  · intro h y
    by_cases hy : prec.Eval ![y, x] f
    · exact Or.inr (h y hy)
    · exact Or.inl hy

@[simp] theorem eval_Prog {M : Type*} [Structure LX M]
    (prec : Semiformula LX ℕ 2) (f : ℕ → M) :
    (Prog prec).Eval ![] f ↔
      ∀ x : M, (∀ y : M, prec.Eval ![y, x] f → Xrel M y) → Xrel M x := by
  classical
  simp only [Prog, Semiformula.eval_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq, eval_Xat, Semiterm.val_bvar,
    Matrix.cons_val_zero]
  constructor
  · intro h x hx
    rcases h x with hnot | hX
    · exact (hnot ((eval_below prec x f).mpr hx)).elim
    · exact hX
  · intro h x
    by_cases hx : ∀ y : M, prec.Eval ![y, x] f → Xrel M y
    · exact Or.inr (h x hx)
    · exact Or.inl (fun hb => hx ((eval_below prec x f).mp hb))

@[simp] theorem eval_TI {M : Type*} [Structure LX M]
    (prec : Semiformula LX ℕ 2) (f : ℕ → M) :
    (TI prec).Eval ![] f ↔
      ((∀ x : M, (∀ y : M, prec.Eval ![y, x] f → Xrel M y) → Xrel M x) →
        ∀ x : M, Xrel M x) := by
  classical
  simp only [TI, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq,
    Semiformula.eval_all, eval_Xat, Semiterm.val_bvar, Matrix.cons_val_zero,
    eval_Prog]
  constructor
  · intro h hprog
    rcases h with hnot | hall
    · exact (hnot hprog).elim
    · exact hall
  · intro h
    by_cases hprog : ∀ x : M, (∀ y : M, prec.Eval ![y, x] f → Xrel M y) → Xrel M x
    · exact Or.inr (h hprog)
    · exact Or.inl hprog

@[simp] theorem eval_TIupto {M : Type*} [Structure LX M]
    (prec : Semiformula LX ℕ 2) (t : Semiterm LX ℕ 0) (f : ℕ → M) :
    (TIupto prec t).Eval ![] f ↔
      ((∀ x : M, (∀ y : M, prec.Eval ![y, x] f → Xrel M y) → Xrel M x) →
        ∀ x : M, prec.Eval ![x, t.val ![] f] f → Xrel M x) := by
  classical
  simp only [TIupto, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq,
    Semiformula.eval_all, eval_Xat, eval_precAt, Semiterm.val_bvar,
    Semiterm.val_bShift, Matrix.cons_val_zero, eval_Prog]
  constructor
  · intro h hprog x hx
    rcases h with hnot | hall
    · exact (hnot hprog).elim
    · rcases hall x with hnp | hX
      · exact (hnp hx).elim
      · exact hX
  · intro h
    by_cases hprog : ∀ x : M, (∀ y : M, prec.Eval ![y, x] f → Xrel M y) → Xrel M x
    · right
      intro x
      by_cases hx : prec.Eval ![x, t.val ![] f] f
      · exact Or.inr (h hprog x hx)
      · exact Or.inl hx
    · exact Or.inl hprog

/-- The shape of the upper bound, semantically: to prove `paLX ⊢ TIupto prec t`
it suffices to prove, in every model, that progressiveness of `X` forces `X`
below `t`. -/
theorem paLX_proves_TIupto_of_models (prec : Semiformula LX ℕ 2)
    (t : Semiterm LX ℕ 0)
    (h : ∀ (M : Type) [Nonempty M] [Structure LX M] [Structure.Eq LX M]
      [M↓[LX] ⊧* paLX], ∀ f : ℕ → M,
        (∀ x : M, (∀ y : M, prec.Eval ![y, x] f → Xrel M y) → Xrel M x) →
        ∀ x : M, prec.Eval ![x, t.val ![] f] f → Xrel M x) :
    paLX ⊢ (TIupto prec t).univCl := by
  apply paLX_proves_of_models_eq
  intro M _ _ _ _
  rw [models_iff]
  simp only [Semiformula.eval_univCl]
  intro f
  exact (eval_TIupto prec t f).mpr (h M f)

end OrdinalAnalysis.Gentzen.Idiom
