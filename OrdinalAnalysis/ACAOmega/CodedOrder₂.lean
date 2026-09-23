/-
  Coded orderings for the second-order calculus `ACA_∞`.

  This is `Gentzen/CodedOrder.lean` transposed to Foundation's monadic
  second-order syntax, in the shape the boundedness lemma of
  `ACAOmega/Boundedness₂.lean` consumes.  Three things change and nothing else.

  * **The fresh predicate becomes a free set variable.**  Where the first-order
    files write `Xat t` — an atom of the enlarged language `LX` — the
    second-order files write `t ∈& 0`, the atom "`t` is in the free set variable
    `0`".  Its negation is `t ∉& 0`, and unlike `∼(Xat t)` that is a *normal
    form*: `Semiformula.neg_fvar` is a `simp` lemma, so `∼(t ∈& 0)` is always
    displayed as `t ∉& 0` and every statement below is written that way.

  * **`XFree` becomes `SetFree`.**  A formula is set-free when no set atom of
    any of the four kinds occurs in it, and — this is an extra clause with no
    first-order counterpart — no set *quantifier* either.  So a set-free formula
    is in particular `ACA.Arith`, and the class of `LowerClass₂.lean` contains
    no set quantifier at all, which is what makes the `all₂` and `exs₂` cases of
    the boundedness induction vacuous.

  * **Closedness is not carried.**  The first-order class asks its arithmetic
    members to be closed (`φ.freeVariables = ∅`) because `Gentzen/OmegaTruth.lean`
    reads them in a structure where free variables would matter.  Foundation's
    second-order syntax has no `freeVariables`, and none is needed: `TrueN₂`
    (`ACAOmega/Evaluate.lean`) fixes *one* assignment of the free number
    variables, the same one at every step, and the four truth laws the induction
    uses — `or`, `and`, `all`, `exs` — hold at that fixed assignment whether or
    not the formula is closed.  `SetFree` alone separates the arithmetic members
    of the class from the named ones.

  What the structure carries is exactly the four facts of `CodedOrder`: the
  ordering as a *lifted first-order* formula (which is how every syntactic fact
  about it is obtained in one line), a coding of the notations, the reading of
  the ordering in `ℕ`, and the two bridges.

  Foundation has no substitution lemma for the second-order `Eval` (see the
  header of `ACA/Standard.lean`); `ACA/Standard.lean` supplies them, but that
  file is not importable from here, so the three that are needed — `eval_rew`,
  `eval_subst₁`, `eval_lift` — are reproved at the head of this file under the
  names `evalSO_*`.
-/
import OrdinalAnalysis.ACAOmega.Evaluate
import OrdinalAnalysis.Gentzen.EpsilonSegmentOrder

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA

/-! ### The missing substitution lemmas for the second-order `Eval`

Reproved here rather than imported: `ACA/Standard.lean` has them, but importing
it would drag in the whole `ACA` axiom layer. -/

section EvalSO

variable {M : Type*} [s : FirstOrder.Structure ℒₒᵣ M]

/-- **First-order rewriting under the second-order `Eval`.** -/
theorem evalSO_rew {N : ℕ} {n₁ n₂ : ℕ} {𝕊 : Set (Set M)} {F : ℕ → Set M}
    {E : Fin N → Set M} {e₂ : Fin n₂ → M} {f₂ : ℕ → M}
    (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂) (φ : Semiformula ℒₒᵣ ℕ ℕ N n₁) :
    (ω ▹ φ).Eval 𝕊 F f₂ E e₂ ↔
      φ.Eval 𝕊 F (FirstOrder.Semiterm.val (s := s) e₂ f₂ ∘ ω ∘ FirstOrder.Semiterm.fvar) E
        (FirstOrder.Semiterm.val (s := s) e₂ f₂ ∘ ω ∘ FirstOrder.Semiterm.bvar) := by
  match φ with
  | .rel r v =>
      simp only [Semiformula.rew_rel, Semiformula.eval_rel, Function.comp_def]
      exact Iff.of_eq (congrArg (FirstOrder.Structure.rel (M := M) r)
        (funext fun i => FirstOrder.Semiterm.val_rew ω (v i)))
  | .nrel r v =>
      simp only [Semiformula.rew_nrel, Semiformula.eval_nrel, Function.comp_def]
      exact not_congr (Iff.of_eq (congrArg (FirstOrder.Structure.rel (M := M) r)
        (funext fun i => FirstOrder.Semiterm.val_rew ω (v i))))
  | t ∈# X => simp [FirstOrder.Semiterm.val_rew]
  | t ∉# X => simp [FirstOrder.Semiterm.val_rew]
  | t ∈& X => simp [FirstOrder.Semiterm.val_rew]
  | t ∉& X => simp [FirstOrder.Semiterm.val_rew]
  | ⊤ => simp
  | ⊥ => simp
  | φ ⋏ ψ => simp [evalSO_rew ω φ, evalSO_rew ω ψ]
  | φ ⋎ ψ => simp [evalSO_rew ω φ, evalSO_rew ω ψ]
  | ∀¹ φ =>
      simpa [Function.comp_def, evalSO_rew ω.q φ] using
        iff_of_eq <| forall_congr fun x ↦ by congr; funext i; cases i using Fin.cases <;> simp
  | ∃¹ φ =>
      simpa [Function.comp_def, evalSO_rew ω.q φ] using
        exists_congr fun x ↦ iff_of_eq <| by
          congr; funext i; cases i using Fin.cases <;> simp
  | ∀² φ => simp [evalSO_rew ω φ]
  | ∃² φ => simp [evalSO_rew ω φ]

/-- **The `∃¹`/`ω`-rule substitution lemma.** -/
theorem evalSO_subst₁ {N n : ℕ} {𝕊 : Set (Set M)} {F : ℕ → Set M} {E : Fin N → Set M}
    {f : ℕ → M} {e : Fin n → M} (φ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    (φ/[t]).Eval 𝕊 F f E e ↔
      φ.Eval 𝕊 F f E ![FirstOrder.Semiterm.val (s := s) e f t] := by
  have h1 : (FirstOrder.Semiterm.val (s := s) e f ∘ (FirstOrder.Rew.subst ![t]) ∘
      FirstOrder.Semiterm.fvar) = f := by funext y; simp
  have h2 : (FirstOrder.Semiterm.val (s := s) e f ∘ (FirstOrder.Rew.subst ![t]) ∘
      FirstOrder.Semiterm.bvar) = ![FirstOrder.Semiterm.val (s := s) e f t] := by
    funext i; simp
  rw [show (φ/[t]) = FirstOrder.Rew.subst ![t] ▹ φ from rfl, evalSO_rew, h1, h2]

/-- **Lifted first-order formulas evaluate as they do first-order.** -/
theorem evalSO_lift {N n : ℕ} {𝕊 : Set (Set M)} {F : ℕ → Set M} {E : Fin N → Set M}
    {f : ℕ → M} {e : Fin n → M} (φ : FirstOrder.Semiformula ℒₒᵣ ℕ n) :
    (lift φ : Semiformula ℒₒᵣ ℕ ℕ N n).Eval 𝕊 F f E e ↔
      FirstOrder.Semiformula.Eval e f φ := by
  induction φ using FirstOrder.Semiformula.rec' <;> simp [*]

end EvalSO

/-! ### Set-freeness

The second-order twin of `LowerClass.XFree`.  Unlike the first-order predicate
this one also forbids set *quantifiers*, so `SetFree φ → Arith φ`. -/

/-- **`φ` mentions no set variable at all** — neither in an atom nor in a
quantifier. -/
def SetFree {N n : ℕ} : Semiformula ℒₒᵣ ℕ ℕ N n → Prop
  |  .rel _ _ => True
  | .nrel _ _ => True
  |    _ ∈# _ => False
  |    _ ∉# _ => False
  |    _ ∈& _ => False
  |    _ ∉& _ => False
  |         ⊤ => True
  |         ⊥ => True
  |     φ ⋏ ψ => SetFree φ ∧ SetFree ψ
  |     φ ⋎ ψ => SetFree φ ∧ SetFree ψ
  |      ∀¹ φ => SetFree φ
  |      ∃¹ φ => SetFree φ
  |      ∀² _ => False
  |      ∃² _ => False

section SetFreeSimp

variable {N n : ℕ}

@[simp] theorem setFree_rel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    SetFree (.rel r v : Semiformula ℒₒᵣ ℕ ℕ N n) := trivial

@[simp] theorem setFree_nrel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    SetFree (.nrel r v : Semiformula ℒₒᵣ ℕ ℕ N n) := trivial

@[simp] theorem not_setFree_bvar (X : Fin N) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ¬ SetFree (t ∈# X : Semiformula ℒₒᵣ ℕ ℕ N n) := id

@[simp] theorem not_setFree_nbvar (X : Fin N) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ¬ SetFree (t ∉# X : Semiformula ℒₒᵣ ℕ ℕ N n) := id

@[simp] theorem not_setFree_fvar (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ¬ SetFree (t ∈& X : Semiformula ℒₒᵣ ℕ ℕ N n) := id

@[simp] theorem not_setFree_nfvar (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ¬ SetFree (t ∉& X : Semiformula ℒₒᵣ ℕ ℕ N n) := id

@[simp] theorem setFree_verum : SetFree (⊤ : Semiformula ℒₒᵣ ℕ ℕ N n) := trivial

@[simp] theorem setFree_falsum : SetFree (⊥ : Semiformula ℒₒᵣ ℕ ℕ N n) := trivial

@[simp] theorem setFree_and (φ ψ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    SetFree (φ ⋏ ψ) ↔ SetFree φ ∧ SetFree ψ := Iff.rfl

@[simp] theorem setFree_or (φ ψ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    SetFree (φ ⋎ ψ) ↔ SetFree φ ∧ SetFree ψ := Iff.rfl

@[simp] theorem setFree_all₁ (φ : Semiformula ℒₒᵣ ℕ ℕ N (n + 1)) :
    SetFree (∀¹ φ) ↔ SetFree φ := Iff.rfl

@[simp] theorem setFree_exs₁ (φ : Semiformula ℒₒᵣ ℕ ℕ N (n + 1)) :
    SetFree (∃¹ φ) ↔ SetFree φ := Iff.rfl

@[simp] theorem not_setFree_all₂ (φ : Semiformula ℒₒᵣ ℕ ℕ (N + 1) n) :
    ¬ SetFree (∀² φ) := id

@[simp] theorem not_setFree_exs₂ (φ : Semiformula ℒₒᵣ ℕ ℕ (N + 1) n) :
    ¬ SetFree (∃² φ) := id

end SetFreeSimp

/-- Set-freeness is invariant under negation. -/
@[simp] theorem setFree_neg {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    SetFree (∼φ) ↔ SetFree φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- Set-freeness is invariant under every first-order rewriting: a rewriting
moves terms, never set variables. -/
@[simp] theorem setFree_rew {N n₁ n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    (φ : Semiformula ℒₒᵣ ℕ ℕ N n₁) : SetFree (ω ▹ φ) ↔ SetFree φ := by
  induction φ using Semiformula.rec' generalizing n₂ <;>
    simp [Semiformula.rew_rel, Semiformula.rew_nrel, *]

/-- The evaluator rewrites inside atoms only, so it neither creates nor destroys
set atoms. -/
@[simp] theorem setFree_ev₂ {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    SetFree (ev₂ φ) ↔ SetFree φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **Everything lifted from the first order is set-free.** -/
@[simp] theorem setFree_lift {N n : ℕ} (φ : FirstOrder.Semiformula ℒₒᵣ ℕ n) :
    SetFree (lift φ : Semiformula ℒₒᵣ ℕ ℕ N n) := by
  induction φ using FirstOrder.Semiformula.rec' <;> simp [*]

/-- A set-free formula is arithmetical. -/
theorem arith_of_setFree {N n : ℕ} {φ : Semiformula ℒₒᵣ ℕ ℕ N n} (h : SetFree φ) :
    Arith φ := by
  induction φ using Semiformula.rec' with
  | hRel r v => simp
  | hNrel r v => simp
  | hBvar X t => exact absurd h (by simp)
  | hNbvar X t => exact absurd h (by simp)
  | hFvar X t => exact absurd h (by simp)
  | hNfvar X t => exact absurd h (by simp)
  | hVerum => simp
  | hFalsum => simp
  | hAnd φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | hOr φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | hAll₁ φ ih => exact ih h
  | hExs₁ φ ih => exact ih h
  | hAll₂ φ _ => exact absurd h (by simp)
  | hExs₂ φ _ => exact absurd h (by simp)

/-- The atomic axioms are set-free: they carry a relation symbol of `ℒₒᵣ`. -/
theorem setFree_of_isArithLit₂ {φ : Proposition ℒₒᵣ} (h : IsArithLit₂ φ) : SetFree φ := by
  obtain ⟨k, r, v, (rfl | rfl), -⟩ := h <;> simp

/-! ### Numerals are injective

Cheaply, through their value in the standard model. -/

theorem numAt_injective {n : ℕ} :
    Function.Injective (numAt : ℕ → FirstOrder.Semiterm ℒₒᵣ ℕ n) := by
  intro a b h
  have := congrArg (evTerm (n := n)) h
  rwa [evTerm_numAt, evTerm_numAt] at this

@[simp] theorem numAt_inj {n a b : ℕ} :
    (numAt a : FirstOrder.Semiterm ℒₒᵣ ℕ n) = numAt b ↔ a = b :=
  ⟨fun h => numAt_injective h, fun h => by rw [h]⟩

/-- The value of a numeral, in the assignment `TrueN₂` fixes. -/
@[simp] theorem val_numAt {n : ℕ} (m : ℕ) (e : Fin n → ℕ) (f : ℕ → ℕ) :
    FirstOrder.Semiterm.val (M := ℕ) e f (numAt m : FirstOrder.Semiterm ℒₒᵣ ℕ n) = m := by
  rw [val_ground (ground_numAt m)]
  exact evTerm_numAt m

/-! ### The shapes

`Gentzen/Setup.lean`, symbol for symbol, with `t ∈& 0` in place of `Xat t`. -/

section Shapes

variable (prec : Semiformula ℒₒᵣ ℕ ℕ 0 2)

/-- `y ≺ x`, with `y` the innermost bound variable. -/
def precAt₂ {n : ℕ} (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ ℕ 0 n :=
  FirstOrder.Rew.subst ![y, x] ▹ prec

/-- `∀ y ≺ x, y ∈ X` — the hypothesis of progressiveness at `x`. -/
def below₂ : Semiformula ℒₒᵣ ℕ ℕ 0 1 :=
  ∀¹ (∼(precAt₂ prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) #1) ⋎
    ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) ∈& 0))

/-- `Prog(≺, X) :≡ ∀ x ((∀ y ≺ x, y ∈ X) → x ∈ X)`. -/
def Prog₂ : Proposition ℒₒᵣ :=
  ∀¹ (∼(below₂ prec) ⋎ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0))

/-- `TI(≺, X) :≡ Prog(≺, X) → ∀ x, x ∈ X`. -/
def TI₂ : Proposition ℒₒᵣ :=
  ∼(Prog₂ prec) ⋎ (∀¹ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0))

end Shapes

/-- `∀ x, x ∈ X` — the conclusion of transfinite induction.  It does not mention
the ordering. -/
def allXat₂ : Proposition ℒₒᵣ := ∀¹ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0)

theorem allXat₂_eq : allXat₂ = ∀¹ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0) := rfl

section ShapeLemmas

variable (prec : Semiformula ℒₒᵣ ℕ ℕ 0 2)

theorem TI₂_eq : TI₂ prec = ∼(Prog₂ prec) ⋎ allXat₂ := rfl

/-- Rewriting commutes with `precAt₂`, for any rewriting that fixes the free
variables. -/
theorem rew_precAt₂ {n₁ n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    (hω : ∀ z : ℕ, ω &z = &z) (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n₁) :
    ω ▹ (precAt₂ prec y x) = precAt₂ prec (ω y) (ω x) := by
  have h : ω.comp (FirstOrder.Rew.subst ![y, x]) = FirstOrder.Rew.subst ![ω y, ω x] := by
    ext i
    case hb =>
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> simp [FirstOrder.Rew.comp_app]
    case hf => simp [FirstOrder.Rew.comp_app, hω]
  show (FirstOrder.Rew.subst ![y, x] ▹ prec |> (FirstOrder.Rewriting.app ω)) =
    FirstOrder.Rew.subst ![ω y, ω x] ▹ prec
  rw [← FirstOrder.TransitiveRewriting.comp_app, h]

/-- The instance used throughout: substitution commutes with `precAt₂`. -/
@[simp] theorem subst_precAt₂ {n₁ n₂ : ℕ} (w : Fin n₁ → FirstOrder.Semiterm ℒₒᵣ ℕ n₂)
    (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n₁) :
    (FirstOrder.Rew.subst w) ▹ (precAt₂ prec y x)
      = precAt₂ prec (FirstOrder.Rew.subst w y) (FirstOrder.Rew.subst w x) :=
  rew_precAt₂ prec _ (fun z => by simp) y x

/-- One substitution into `below₂`. -/
theorem subst_below₂ (t : FirstOrder.SyntacticTerm ℒₒᵣ) :
    (below₂ prec)/[t] =
      ∀¹ (∼(precAt₂ prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) (FirstOrder.Rew.bShift t)) ⋎
        ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0)) := by
  simp [below₂, FirstOrder.Rew.q_subst]

/-- The same at a numeral: `bShift` fixes numerals. -/
@[simp] theorem subst_below₂_numeral (k : ℕ) :
    (below₂ prec)/[(numAt k : FirstOrder.SyntacticTerm ℒₒᵣ)] =
      ∀¹ (∼(precAt₂ prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) (numAt k)) ⋎
        ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0)) := by
  rw [subst_below₂]
  simp

/-- The second substitution: the body of `(below₂ prec)/[k̄]`, at a numeral. -/
@[simp] theorem subst_belowBody₂_numeral (k m : ℕ) :
    (∼(precAt₂ prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) (numAt k)) ⋎
      ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0))/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)] =
      ∼(precAt₂ prec (numAt m) (numAt k)) ⋎ ((numAt m : FirstOrder.SyntacticTerm ℒₒᵣ) ∈& 0) := by
  simp

/-- `∼Prog(≺, X) = ∃ x ((∀ y ≺ x, y ∈ X) ⋏ x ∉ X)`. -/
theorem neg_Prog₂ :
    ∼(Prog₂ prec) =
      ∃¹ ((below₂ prec) ⋏ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∉& 0)) := by
  simp [Prog₂]

end ShapeLemmas

/-- The `omegaRule`-premises of `∀ x, x ∈ X` are the atoms `m̄ ∈ X`. -/
@[simp] theorem subst_allXat₂_body (m : ℕ) :
    (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0 : Semiformula ℒₒᵣ ℕ ℕ 0 1))
        /[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)] =
      (((numAt m : FirstOrder.SyntacticTerm ℒₒᵣ) ∈& 0) : Proposition ℒₒᵣ) := by
  simp

/-! ### Set-freeness of the shapes -/

section ShapeSetFree

variable (prec : Semiformula ℒₒᵣ ℕ ℕ 0 2)

@[simp] theorem setFree_precAt₂ (h : SetFree prec) {n : ℕ}
    (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) : SetFree (precAt₂ prec y x) := by
  simp only [precAt₂, setFree_rew]
  exact h

@[simp] theorem not_setFree_below₂ : ¬ SetFree (below₂ prec) := by
  simp [below₂]

@[simp] theorem not_setFree_Prog₂ : ¬ SetFree (Prog₂ prec) := by
  simp [Prog₂]

@[simp] theorem not_setFree_TI₂ : ¬ SetFree (TI₂ prec) := by
  simp [TI₂]

end ShapeSetFree

@[simp] theorem not_setFree_allXat₂ : ¬ SetFree allXat₂ := by
  simp [allXat₂]

/-! ### Truth in `ℕ`, in the shapes the rules produce

`TrueN₂` reads every set variable as `∅` and every free number variable as `0`.
Both choices are fixed once and for all, and the four laws below hold at that
fixed reading whatever the formula. -/

theorem trueN₂_or (φ ψ : Proposition ℒₒᵣ) : TrueN₂ (φ ⋎ ψ) ↔ TrueN₂ φ ∨ TrueN₂ ψ := by
  simp [TrueN₂]

theorem trueN₂_and (φ ψ : Proposition ℒₒᵣ) : TrueN₂ (φ ⋏ ψ) ↔ TrueN₂ φ ∧ TrueN₂ ψ := by
  simp [TrueN₂]

theorem trueN₂_verum : TrueN₂ (⊤ : Proposition ℒₒᵣ) := by simp [TrueN₂]

theorem trueN₂_subst_numeral (φ : Semiproposition ℒₒᵣ 0 1) (m : ℕ) :
    TrueN₂ (φ/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)]) ↔
      φ.Eval (Set.univ : Set (Set ℕ)) (fun _ => (∅ : Set ℕ)) (fun _ => 0) ![] ![m] := by
  rw [TrueN₂, evalSO_subst₁, val_numAt]

theorem trueN₂_all (φ : Semiproposition ℒₒᵣ 0 1) :
    TrueN₂ (∀¹ φ) ↔ ∀ m : ℕ, TrueN₂ (φ/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)]) := by
  simp only [TrueN₂, Semiformula.eval_fal₀]
  exact forall_congr' fun m => (trueN₂_subst_numeral φ m).symm

theorem trueN₂_exs (φ : Semiproposition ℒₒᵣ 0 1) :
    TrueN₂ (∃¹ φ) ↔ ∃ m : ℕ, TrueN₂ (φ/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)]) := by
  simp only [TrueN₂, Semiformula.eval_exs₀]
  exact exists_congr fun m => (trueN₂_subst_numeral φ m).symm

/-- The instance the evaluating calculus produces has the truth of the plain
numeral instance. -/
theorem trueN₂_inst (φ : Semiproposition ℒₒᵣ 0 1) (m : ℕ) :
    TrueN₂ (evInst₂.inst φ m) ↔
      TrueN₂ (φ/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)]) := by
  rw [evInst₂_inst]
  exact trueN₂_ev₂ _

/-! ### The structure -/

/-- A **coded ordering** for the second-order calculus: a first-order formula of
two variables with no free variables, *lifted* into the second-order syntax; a
coding of the notations by numbers; the reading of the formula in `ℕ`; and the
two bridges between them.

The field `prec_eq` is what makes every syntactic fact about `prec` a one-liner:
being a lift, `prec` is set-free and arithmetical, and its instances at numerals
evaluate as the first-order formula does. -/
structure CodedOrder₂ (O : Type) [LinearOrder O] where
  /-- The ordering, in the second-order syntax. -/
  prec : Semiformula ℒₒᵣ ℕ ℕ 0 2
  /-- Its first-order original. -/
  prec₀ : FirstOrder.Semiformula ℒₒᵣ ℕ 2
  /-- The ordering is a lift: in particular it mentions no set variable. -/
  prec_eq : prec = ACA.lift prec₀
  /-- The original has no free variables. -/
  freeVariables_prec₀ : prec₀.freeVariables = ∅
  /-- The coding of the notations by numbers. -/
  code : O → ℕ
  /-- The ordering read in `ℕ`. -/
  precN : ℕ → ℕ → Prop
  /-- **The syntactic bridge.**  At a pair of numerals, in the standard
  ω-structure and for any reading of the set variables, `prec` says `precN`. -/
  eval_precAt_numeral : ∀ (𝕊 : Set (Set ℕ)) (F : ℕ → Set ℕ) (f : ℕ → ℕ) (m n : ℕ),
    Semiformula.Eval 𝕊 F f ![] ![] (precAt₂ prec (numAt m) (numAt n)) ↔ precN m n
  /-- **The semantic bridge.**  Standard codes are ordered as the notations
  are. -/
  precN_code_iff : ∀ a b : O, precN (code a) (code b) ↔ a < b

namespace CodedOrder₂

variable {O : Type} [LinearOrder O] (C : CodedOrder₂ O)

@[simp] theorem setFree_prec : SetFree C.prec := by
  rw [C.prec_eq]; exact setFree_lift _

theorem arith_prec : Arith C.prec := arith_of_setFree C.setFree_prec

@[simp] theorem setFree_precAt {n : ℕ} (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    SetFree (precAt₂ C.prec y x) := setFree_precAt₂ _ C.setFree_prec y x

theorem precN_code_of_lt {a b : O} (h : a < b) : C.precN (C.code a) (C.code b) :=
  (C.precN_code_iff a b).mpr h

theorem lt_of_precN_code {a b : O} (h : C.precN (C.code a) (C.code b)) : a < b :=
  (C.precN_code_iff a b).mp h

/-- **The reading of `k̄ ≺ n̄` in `ℕ`.** -/
theorem trueN₂_precAt (k n : ℕ) :
    TrueN₂ (precAt₂ C.prec (numAt k) (numAt n)) ↔ C.precN k n :=
  C.eval_precAt_numeral _ _ _ k n

theorem trueN₂_neg_precAt (k n : ℕ) :
    TrueN₂ (∼(precAt₂ C.prec (numAt k) (numAt n))) ↔ ¬ C.precN k n := by
  rw [trueN₂_neg]
  exact not_congr (C.trueN₂_precAt k n)

end CodedOrder₂

/-! ### The instance: the `ε_a`-segment of the coded Veblen ordering

`Gentzen/EpsilonSegmentOrder.lean` on the second-order syntax.  The ordering is
the same arithmetic formula, the coding and the reading in `ℕ` are literally the
same functions, and so the two bridges are the ones `CodedVeblen` and
`EpsilonSegmentOrder` already prove — only the syntax around them changed. -/

section EpsilonSeg

open OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.CodedVeblen (precN₁ precN₁_code_iff)
open OrdinalAnalysis.Gentzen.EpsilonSegmentOrder (precNSeg precNSeg_code_iff)
open OrdinalAnalysis.Gamma0Note (epsilonNote)

/-- `≺₁`, as a first-order `ℒₒᵣ`-formula in two variables.  `ACA/Syntax.lean`'s
`precFO` is the same construction at `precDef` (the `ε₀` ordering); this is the
`Γ₀` one. -/
def precFO₁ : FirstOrder.Semiformula ℒₒᵣ ℕ 2 :=
  FirstOrder.Rewriting.emb InternalVNote.precDef₁.val

@[simp] theorem freeVariables_precFO₁ : precFO₁.freeVariables = ∅ := by
  simp [precFO₁]

@[simp] theorem eval_precFO₁ (m n : ℕ) (f : ℕ → ℕ) :
    FirstOrder.Semiformula.Eval (M := ℕ) ![m, n] f precFO₁ ↔ precN₁ m n := by
  simp [precFO₁, precN₁]

/-- The `ε_a`-segment: `x ≺₁ y ∧ y ≺₁ ε_a̅`, as a first-order formula. -/
def precSeg₀ (a : Gamma0Note) : FirstOrder.Semiformula ℒₒᵣ ℕ 2 :=
  precFO₁ ⋏ (FirstOrder.Rew.subst
    ![(#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2),
      (numAt (VNoteBridge.gamma0Code (epsilonNote a)) : FirstOrder.Semiterm ℒₒᵣ ℕ 2)] ▹ precFO₁)

theorem freeVariables_precSeg₀ (a : Gamma0Note) : (precSeg₀ a).freeVariables = ∅ := by
  have h : (FirstOrder.Rew.subst
      ![(#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2),
        (numAt (VNoteBridge.gamma0Code (epsilonNote a)) : FirstOrder.Semiterm ℒₒᵣ ℕ 2)]
      ▹ precFO₁).freeVariables = ∅ := by
    refine LowerSyntax.freeVariables_rew_eq_empty _ freeVariables_precFO₁ ?_
    refine Fin.forall_fin_two.mpr ⟨by simp, ?_⟩
    simp only [FirstOrder.Rew.subst_bvar, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    simp [numAt]
  simp [precSeg₀, h]

theorem eval_precSeg₀ (a : Gamma0Note) (m n : ℕ) (f : ℕ → ℕ) :
    FirstOrder.Semiformula.Eval (M := ℕ) ![m, n] f (precSeg₀ a) ↔ precNSeg a m n := by
  have hsub : FirstOrder.Semiformula.Eval (M := ℕ) ![m, n] f
      (FirstOrder.Rew.subst
        ![(#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2),
          (numAt (VNoteBridge.gamma0Code (epsilonNote a)) : FirstOrder.Semiterm ℒₒᵣ ℕ 2)]
        ▹ precFO₁)
      ↔ precN₁ n (VNoteBridge.gamma0Code (epsilonNote a)) := by
    rw [FirstOrder.Semiformula.eval_rew]
    have e₁ : (FirstOrder.Semiterm.val (M := ℕ) ![m, n] f ∘
        ⇑(FirstOrder.Rew.subst
          ![(#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2),
            (numAt (VNoteBridge.gamma0Code (epsilonNote a)) : FirstOrder.Semiterm ℒₒᵣ ℕ 2)]) ∘
        FirstOrder.Semiterm.bvar) = ![n, VNoteBridge.gamma0Code (epsilonNote a)] := by
      funext i
      revert i
      refine Fin.forall_fin_two.mpr ⟨by simp, by simp⟩
    have e₂ : (FirstOrder.Semiterm.val (M := ℕ) ![m, n] f ∘
        ⇑(FirstOrder.Rew.subst
          ![(#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2),
            (numAt (VNoteBridge.gamma0Code (epsilonNote a)) : FirstOrder.Semiterm ℒₒᵣ ℕ 2)]) ∘
        FirstOrder.Semiterm.fvar) = f := by
      funext x; simp
    rw [e₁, e₂]
    exact eval_precFO₁ _ _ f
  simp only [precSeg₀, LogicalConnective.HomClass.map_and, eval_precFO₁, hsub]
  rfl

/-- **The evaluation bridge for a lifted ordering.**  Substituting numerals into
the lift and reading it in the ω-structure is reading the first-order original
at the two numbers. -/
theorem eval_precAt₂_lift {M : Type*} [FirstOrder.Structure ℒₒᵣ M]
    (prec₀ : FirstOrder.Semiformula ℒₒᵣ ℕ 2) (𝕊 : Set (Set M)) (F : ℕ → Set M)
    (f : ℕ → M) (m n : ℕ) :
    Semiformula.Eval 𝕊 F f ![] ![]
        (precAt₂ (lift prec₀ : Semiformula ℒₒᵣ ℕ ℕ 0 2) (numAt m) (numAt n))
      ↔ FirstOrder.Semiformula.Eval
          ![(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ).val ![] f,
            (numAt n : FirstOrder.SyntacticTerm ℒₒᵣ).val ![] f] f prec₀ := by
  have he : (precAt₂ (lift prec₀ : Semiformula ℒₒᵣ ℕ ℕ 0 2) (numAt m) (numAt n))
      = (lift (FirstOrder.Rew.subst
          ![(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ), numAt n] ▹ prec₀) :
            Semiformula ℒₒᵣ ℕ ℕ 0 0) := by
    rw [lift_rew]; rfl
  rw [he, evalSO_lift, FirstOrder.Semiformula.eval_rew]
  have e₁ : (FirstOrder.Semiterm.val (M := M) ![] f ∘
      ⇑(FirstOrder.Rew.subst ![(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ), numAt n]) ∘
      FirstOrder.Semiterm.bvar)
      = ![(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ).val ![] f,
          (numAt n : FirstOrder.SyntacticTerm ℒₒᵣ).val ![] f] := by
    funext i
    revert i
    refine Fin.forall_fin_two.mpr ⟨by simp, by simp⟩
  have e₂ : (FirstOrder.Semiterm.val (M := M) ![] f ∘
      ⇑(FirstOrder.Rew.subst ![(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ), numAt n]) ∘
      FirstOrder.Semiterm.fvar) = f := by
    funext x; simp
  rw [e₁, e₂]

/-- **The coded ordering of the notations below `ε_a`, second-order.** -/
def epsilonSegOrder₂ (a : Gamma0Note) : CodedOrder₂ (Gamma0Note.EpsilonBelow a) where
  prec := lift (precSeg₀ a)
  prec₀ := precSeg₀ a
  prec_eq := rfl
  freeVariables_prec₀ := freeVariables_precSeg₀ a
  code := fun x => VNoteBridge.gamma0Code x.1
  precN := precNSeg a
  eval_precAt_numeral := by
    intro 𝕊 F f m n
    rw [eval_precAt₂_lift]
    rw [val_numAt, val_numAt]
    exact eval_precSeg₀ a m n f
  precN_code_iff := precNSeg_code_iff a

@[simp] theorem epsilonSegOrder₂_prec (a : Gamma0Note) :
    (epsilonSegOrder₂ a).prec = lift (precSeg₀ a) := rfl

@[simp] theorem epsilonSegOrder₂_code (a : Gamma0Note) (x : Gamma0Note.EpsilonBelow a) :
    (epsilonSegOrder₂ a).code x = VNoteBridge.gamma0Code x.1 := rfl

@[simp] theorem epsilonSegOrder₂_precN (a : Gamma0Note) :
    (epsilonSegOrder₂ a).precN = precNSeg a := rfl

end EpsilonSeg

end OrdinalAnalysis.ACAOmega
