/-
  Task 3 of the lower bound: the class `C` of §C of the specification, and its
  closure under *premise-formation* — the operation the boundedness induction
  performs when it walks up an `OmegaDerivable` derivation.

  The boundedness lemma is an induction over `OmegaDerivable A numLX 0 α Γ` in
  which the hypothesis "`Γ ⊆ C`" must survive every rule.  Each rule of
  `Omega/Calculus.lean` replaces the principal formula of the sequent by one or
  more *premise* formulas:

  | rule          | principal | premises                   |
  |---------------|-----------|----------------------------|
  | `or`          | `φ ⋎ ψ`   | `φ`, `ψ` (in one sequent)  |
  | `and`         | `φ ⋏ ψ`   | `φ` and `ψ` (two sequents) |
  | `omegaRule`   | `∀¹ φ`    | `φ/[n̄]` for every `n`      |
  | `exs`         | `∃¹ φ`    | `φ/[n̄]` for one `n`        |
  | `contraction` | —         | a subsequent               |
  | `atom`, `identity`, `verum`, `cut` | — | none / two contexts |

  So what has to be proved is: *for every member of `C` and every rule whose
  principal formula it can be, the premises are again in `C`.*  That is the
  content of `InC.of_or`, `InC.of_and`, `InC.of_all`, `InC.of_exs` below, and of
  their sequent-level forms `InCSeq.of_or` … `InCSeq.of_subset`.

  Three design points.

  * **The ordering is a parameter.**  Everything below is stated for an
    arbitrary `C : CodedOrder O` (`Gentzen/CodedOrder.lean`) rather than for
    `precCode`; `C.prec` is the ordering's formula and `C.xfree_prec`,
    `C.freeVariables_prec` its two syntactic properties.  Nothing else about
    `C` is used in this file — the coding and the standard reading only enter
    with the boundedness lemma.  The `ε₀` case is `epsilon0Order`.

  * **`X`-freeness is structural.**  `XFree` is a `Prop`-valued recursion over
    `Semiformula LX ℕ n`: an atom is `X`-free when its relation symbol is
    `Sum.inl r` for an arithmetic `r`, and the connectives propagate.  It is
    preserved by every rewriting (`XFree_rew`) and by negation (`XFree_neg`),
    which is all the premise-formation lemmas need.  Its definition and lemmas
    now live in `Gentzen/CodedOrder.lean` — the structure has to speak of them —
    but in this namespace and under these names, so nothing moved as far as any
    other file is concerned.

  * **Head clashes are decided by a numeric tag.**  the pitfall notes: `⋏`, `⋎`,
    `∀¹`, `∃¹` are `LogicalConnective`/`Quantifier` *notation*, not
    constructors, so `injection` and `noConfusion` cannot be pointed at an
    equation between two of them.  `head : Semiformula LX ℕ n → ℕ` tags the
    outermost connective; every `head_*` lemma is `rfl`, and an impossible case
    such as "`φ ⋎ ψ` is `∼(Prog C.prec)`" becomes `(5 : ℕ) = 7`, which `simp`
    kills.  Same-head cases are settled by Foundation's `or_inj`, `and_inj`,
    `all_inj`, `exs_inj`.

  * **`InC` is inverted once.**  `InC.exhaustive` turns membership into a
    nine-way disjunction of *equations*; every later proof `rcases` that and
    never touches the inductive again.  This is also deliverable (d): the list
    the boundedness induction cases on.

  Traps hit, beyond the two `LowerSyntax.lean` already documents.

  * `Sum.noConfusion` cannot be applied to `h : (Sum.inr XRel.X : LX.Rel 1) =
    Sum.inl r`, even after ascribing the type to a literal `⊕`: the universe
    metavariable of `noConfusion` is never solved.  `simp at h` does work — the
    `reduceCtorEq` simproc sees the constructors.
  * `Structure XLang ℕ` must *not* become an instance: `Gentzen/StandardLX.lean`
    owns the standard model of `LX`.  The one place a model is needed here —
    numerals are injective — uses a `private def` of type `Structure LX ℕ`
    passed explicitly as `(str₂ := …)`, so nothing is registered.
-/
import OrdinalAnalysis.Gentzen.CodedOrder
import OrdinalAnalysis.Gentzen.Code
import OrdinalAnalysis.Omega.Calculus

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.LowerClass

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.CodedNotation
open OrdinalAnalysis.Gentzen.LowerSyntax

variable {O : Type} [LinearOrder O] {C : CodedOrder O}

/-! ### (a₂) `X`-free *and* closed

The property the ω-completeness half of the argument consumes: a member of the
sequent that mentions no `X` and has no free variables, hence is decided by the
standard model. -/

/-- `φ` is closed and does not mention `X`. -/
def IsXFreeClosed (φ : Proposition LX) : Prop := XFree φ ∧ φ.freeVariables = ∅

theorem IsXFreeClosed.xfree {φ : Proposition LX} (h : IsXFreeClosed φ) : XFree φ := h.1

theorem IsXFreeClosed.closed {φ : Proposition LX} (h : IsXFreeClosed φ) :
    φ.freeVariables = ∅ := h.2

@[simp] theorem isXFreeClosed_neg {φ : Proposition LX} :
    IsXFreeClosed (∼φ) ↔ IsXFreeClosed φ := by
  simp [IsXFreeClosed]

/-- `or`-premises of an `X`-free closed formula are `X`-free closed. -/
@[simp] theorem isXFreeClosed_or {φ ψ : Proposition LX} :
    IsXFreeClosed (φ ⋎ ψ) ↔ IsXFreeClosed φ ∧ IsXFreeClosed ψ := by
  simp only [IsXFreeClosed, XFree_or, Semiformula.freeVariables_or, Finset.union_eq_empty]
  tauto

/-- `and`-premises of an `X`-free closed formula are `X`-free closed. -/
@[simp] theorem isXFreeClosed_and {φ ψ : Proposition LX} :
    IsXFreeClosed (φ ⋏ ψ) ↔ IsXFreeClosed φ ∧ IsXFreeClosed ψ := by
  simp only [IsXFreeClosed, XFree_and, Semiformula.freeVariables_and, Finset.union_eq_empty]
  tauto

/-- **The quantifier case.**  A numeral instance of an `X`-free closed
quantified formula is `X`-free closed: `XFree_rew` handles the predicate and
`LowerSyntax.freeVariables_rew_eq_empty` the free variables, the bound-variable
image being the closed term `k̄`. -/
theorem isXFreeClosed_subst_numeral {φ : Semiformula LX ℕ 1}
    (hx : XFree φ) (hf : φ.freeVariables = ∅) (k : ℕ) :
    IsXFreeClosed (φ/[numLX k]) := by
  refine ⟨by simpa using hx, ?_⟩
  refine freeVariables_rew_eq_empty _ hf ?_
  intro i
  simp

/-- `omegaRule`-premises of an `X`-free closed `∀¹`. -/
theorem isXFreeClosed_all {φ : Semiformula LX ℕ 1} (h : IsXFreeClosed (∀¹ φ)) (k : ℕ) :
    IsXFreeClosed (φ/[numLX k]) :=
  isXFreeClosed_subst_numeral h.1 h.2 k

/-- `exs`-premises of an `X`-free closed `∃¹`. -/
theorem isXFreeClosed_exs {φ : Semiformula LX ℕ 1} (h : IsXFreeClosed (∃¹ φ)) (k : ℕ) :
    IsXFreeClosed (φ/[numLX k]) :=
  isXFreeClosed_subst_numeral h.1 h.2 k

/-- An `X`-atom is never `X`-free closed. -/
@[simp] theorem not_isXFreeClosed_Xat {t : Semiterm LX ℕ 0} :
    ¬ IsXFreeClosed (Xat t) := fun h => not_XFree_Xat t h.1

/-- Nor is a negated `X`-atom. -/
@[simp] theorem not_isXFreeClosed_neg_Xat {t : Semiterm LX ℕ 0} :
    ¬ IsXFreeClosed (∼(Xat t)) := by simp

/-! ### Head tags

`⋏`, `⋎`, `∀¹`, `∃¹` are notation for type-class fields, so `injection` cannot
see through an equation between two of them (a known pitfall).  Tagging the
outermost connective by a number reduces every "these two members of `C` cannot
be equal" step to arithmetic. -/

/-- The outermost connective of a formula, as a numeric tag. -/
def head {n : ℕ} : Semiformula LX ℕ n → ℕ
  |        ⊤ => 0
  |        ⊥ => 1
  | .rel _ _ => 2
  | .nrel _ _ => 3
  |    _ ⋏ _ => 4
  |    _ ⋎ _ => 5
  |     ∀¹ _ => 6
  |     ∃¹ _ => 7

@[simp] theorem head_verum {n : ℕ} : head (⊤ : Semiformula LX ℕ n) = 0 := rfl

@[simp] theorem head_falsum {n : ℕ} : head (⊥ : Semiformula LX ℕ n) = 1 := rfl

@[simp] theorem head_rel {n k : ℕ} (r : LX.Rel k) (v : Fin k → Semiterm LX ℕ n) :
    head (Semiformula.rel r v) = 2 := rfl

@[simp] theorem head_nrel {n k : ℕ} (r : LX.Rel k) (v : Fin k → Semiterm LX ℕ n) :
    head (Semiformula.nrel r v) = 3 := rfl

@[simp] theorem head_and {n : ℕ} (φ ψ : Semiformula LX ℕ n) : head (φ ⋏ ψ) = 4 := rfl

@[simp] theorem head_or {n : ℕ} (φ ψ : Semiformula LX ℕ n) : head (φ ⋎ ψ) = 5 := rfl

@[simp] theorem head_all {n : ℕ} (φ : Semiformula LX ℕ (n + 1)) : head (∀¹ φ) = 6 := rfl

@[simp] theorem head_exs {n : ℕ} (φ : Semiformula LX ℕ (n + 1)) : head (∃¹ φ) = 7 := rfl

@[simp] theorem head_Xat {n : ℕ} (t : Semiterm LX ℕ n) : head (Xat t) = 2 := rfl

@[simp] theorem head_neg_Xat {n : ℕ} (t : Semiterm LX ℕ n) : head (∼(Xat t)) = 3 := rfl

/-! ### Numerals are injective

`Semiterm.numeral` has no syntactic injectivity lemma in Foundation and the only
cheap proof is semantic.  `Structure.add` (Foundation/FirstOrder/Basic/
Model.lean:92) is an *instance*, so the `XLang` summand is supplied explicitly
as `(str₂ := xStrucAux)` and nothing is registered: the standard model of `LX`
belongs to `Gentzen/StandardLX.lean`, not here. -/

set_option warn.classDefReducibility false in
/-- A throwaway reading of the fresh predicate.  `XLang` has no function
symbols, so only `rel` has to be decided, and the choice is irrelevant. -/
private def xStrucAux : Structure XLang ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ _ _ => False

set_option warn.classDefReducibility false in
/-- Arithmetic standard, `X` empty.  Deliberately *not* an instance. -/
private def stdAux : Structure LX ℕ := Structure.add ℒₒᵣ XLang ℕ (str₂ := xStrucAux)

private theorem val_numLX_aux (k : ℕ) :
    Semiterm.val (s := stdAux) ![] (fun _ => 0) (numLX k) = k := by
  have h : (numLX k : Semiterm LX ℕ 0) = Semiterm.lMap toLX ((k : ℕ) : Semiterm ℒₒᵣ ℕ 0) :=
    (lMap_toLX_numeral k).symm
  have key : Semiterm.val (s := stdAux) ![] (fun _ : ℕ => (0 : ℕ))
      (Semiterm.lMap toLX ((k : ℕ) : Semiterm ℒₒᵣ ℕ 0))
      = Semiterm.val (M := ℕ) ![] (fun _ => 0) ((k : ℕ) : Semiterm ℒₒᵣ ℕ 0) :=
    Structure.val_lMap_add₁ (str₂ := xStrucAux) _ _ _
  rw [h, key]
  simp

/-- **Distinct numerals are distinct terms.** -/
theorem numLX_injective : Function.Injective numLX := by
  intro n m h
  have hval := congrArg (Semiterm.val (s := stdAux) ![] (fun _ => 0)) h
  rw [val_numLX_aux n, val_numLX_aux m] at hval
  exact hval

@[simp] theorem numLX_inj {n m : ℕ} : numLX n = numLX m ↔ n = m :=
  ⟨fun h => numLX_injective h, fun h => by rw [h]⟩

/-- The argument of a unary atom.  Only used to invert `Xat`, which `injection`
cannot do: the arity of `Semiformula.rel` is an index, so its `injEq` produces
`HEq`s, and `Sum.inr XRel.X` may not be looked at by `rw`/`simp`. -/
def xArg {n : ℕ} : Semiformula LX ℕ n → Semiterm LX ℕ n
  | .rel (arity := 1) _ v => v 0
  | _ => &0

@[simp] theorem xArg_Xat {n : ℕ} (t : Semiterm LX ℕ n) : xArg (Xat t) = t := rfl

/-- `Xat` is injective. -/
theorem Xat_inj {n : ℕ} {t s : Semiterm LX ℕ n} (h : Xat t = Xat s) : t = s := by
  simpa using congrArg xArg h

/-- **`X(n̄)` determines `n`.** -/
@[simp] theorem Xat_numLX_inj {n m : ℕ} : Xat (numLX n) = Xat (numLX m) ↔ n = m :=
  ⟨fun h => numLX_injective (Xat_inj h), fun h => by rw [h]⟩

/-- The negated form, likewise. -/
@[simp] theorem neg_Xat_numLX_inj {n m : ℕ} :
    ∼(Xat (numLX n)) = ∼(Xat (numLX m)) ↔ n = m := by simp

/-! ### (b) The named members of `C`

§C of the specification lists nine shapes.  Four of them get a name: they are
the ones the boundedness lemma carries a disjunct for.  All four are formed
from the ordering `C.prec`; only `allXat` is independent of it. -/

/-- `(∀ y ≺ x, X y)` at the numeral `n̄`, that is `∀ y ≺ n̄, X y`. -/
def belowAt (C : CodedOrder O) (n : ℕ) : Proposition LX := (below C.prec)/[numLX n]

/-- `P n := (∀ y ≺ n̄, X y) ⋏ ∼X(n̄)` — the body of the existential
`∼(Prog C.prec)` at `n̄`, and the formula the `exs` case produces. -/
def P (C : CodedOrder O) (n : ℕ) : Proposition LX := belowAt C n ⋏ ∼(Xat (numLX n))

/-- `∼(m̄ ≺ n̄) ⋎ X(m̄)` — the ω-premises of `belowAt C n`. -/
def precOrXat (C : CodedOrder O) (m n : ℕ) : Proposition LX :=
  ∼(precAt C.prec (numLX m) (numLX n)) ⋎ Xat (numLX m)

/-- `∀ x, X x` — the conclusion of transfinite induction. -/
def allXat : Proposition LX := ∀¹ (Xat (#0 : Semiterm LX ℕ 1))

theorem belowAt_def (n : ℕ) : belowAt C n = (below C.prec)/[numLX n] := rfl

theorem P_eq (n : ℕ) : P C n = belowAt C n ⋏ ∼(Xat (numLX n)) := rfl

theorem precOrXat_eq (m n : ℕ) :
    precOrXat C m n = ∼(precAt C.prec (numLX m) (numLX n)) ⋎ Xat (numLX m) := rfl

theorem allXat_eq : allXat = ∀¹ (Xat (#0 : Semiterm LX ℕ 1)) := rfl

/-! Their normal forms; all of them instances of `LowerSyntax`. -/

/-- `TI(≺) = ∼Prog(≺) ⋎ ∀ x, X x`; true by definition. -/
theorem TI_eq : TI C.prec = ∼(Prog C.prec) ⋎ allXat := rfl

/-- `∼Prog(≺) = ∃ x ((∀ y ≺ x, X y) ⋏ ∼X x)`. -/
theorem negProg_eq :
    ∼(Prog C.prec) = ∃¹ ((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LX ℕ 1))) :=
  LowerSyntax.neg_Prog C.prec

/-- **The `exs`-premise of `∼Prog(≺)` at `n̄` is `P n`.** -/
theorem subst_negProg_body (n : ℕ) :
    ((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LX ℕ 1)))/[numLX n] = P C n := by
  simp [P_eq, belowAt_def]

/-- `belowAt C n` is a `∀¹`, with the body the boundedness lemma reads. -/
theorem belowAt_eq (n : ℕ) :
    belowAt C n = ∀¹ (∼(precAt C.prec (#0 : Semiterm LX ℕ 1) (Semiterm.numeral n)) ⋎
      Xat (#0 : Semiterm LX ℕ 1)) :=
  LowerSyntax.subst_below_numeral C.prec n

/-- **The `omegaRule`-premises of `belowAt C n` are the formulas `precOrXat C m n`.** -/
theorem subst_belowAt_body (m n : ℕ) :
    (∼(precAt C.prec (#0 : Semiterm LX ℕ 1) (Semiterm.numeral n)) ⋎
      Xat (#0 : Semiterm LX ℕ 1))/[numLX m] = precOrXat C m n :=
  LowerSyntax.subst_belowBody_numeral C.prec n m

/-- **The `omegaRule`-premises of `∀ x, X x` are the atoms `X(m̄)`.** -/
theorem subst_allXat_body (m : ℕ) :
    (Xat (#0 : Semiterm LX ℕ 1))/[numLX m] = Xat (numLX m) :=
  LowerSyntax.subst_Xat_bvar_numeral m

/-! Head tags of the named members. -/

@[simp] theorem head_TI : head (TI C.prec) = 5 := rfl

@[simp] theorem head_negProg : head (∼(Prog C.prec)) = 7 := by
  rw [negProg_eq]; simp

@[simp] theorem head_allXat : head allXat = 6 := rfl

@[simp] theorem head_belowAt (n : ℕ) : head (belowAt C n) = 6 := by
  rw [belowAt_eq]; simp

@[simp] theorem head_P (n : ℕ) : head (P C n) = 4 := rfl

@[simp] theorem head_precOrXat (m n : ℕ) : head (precOrXat C m n) = 5 := rfl

/-! Closedness of the named members: `univCl` is a typing wrapper on all of
them, which is what lets the embedding of §B move between `Sentence LX` and
`Proposition LX` freely. -/

@[simp] theorem freeVariables_allXat : allXat.freeVariables = ∅ := by
  rw [allXat_eq]; simp

@[simp] theorem freeVariables_belowAt (n : ℕ) : (belowAt C n).freeVariables = ∅ := by
  have h : (precAt C.prec (#0 : Semiterm LX ℕ 1) (Semiterm.numeral n)).freeVariables = ∅ :=
    C.freeVariables_precAt (by simp) (by simp)
  rw [belowAt_eq]
  simp [h]

@[simp] theorem freeVariables_P (n : ℕ) : (P C n).freeVariables = ∅ := by
  rw [P_eq]; simp

@[simp] theorem freeVariables_precOrXat (m n : ℕ) :
    (precOrXat C m n).freeVariables = ∅ := by
  have h : (precAt C.prec (numLX m) (numLX n)).freeVariables = ∅ :=
    C.freeVariables_precAt (by simp) (by simp)
  rw [precOrXat_eq]
  simp [h]

/-- `∼(m̄ ≺ n̄)` is `X`-free and closed: `C.prec` is `X`-free and closed by
assumption, and both arguments are numerals.  This is the only `X`-free member
among the named shapes, and it is the left disjunct of `precOrXat C m n`. -/
theorem isXFreeClosed_neg_precAt (m n : ℕ) :
    IsXFreeClosed (∼(precAt C.prec (numLX m) (numLX n))) := by
  refine ⟨by simp, ?_⟩
  simp only [Semiformula.freeVariables_not]
  exact C.freeVariables_precAt (by simp) (by simp)

/-! ### (b′) The class `C` -/

/-- **The class `C`** of §C of the specification: the shapes that can occur in a
sequent of a cut-free ω-derivation of `TI C.prec`.  Every member is closed,
and every term occurring in one is a numeral.

The binders are written out rather than taken from the section: an `inductive`
absorbs only the section variables it mentions, and the instance binder is not
mentioned by name (a known pitfall). -/
inductive InC {O : Type} [LinearOrder O] (C : CodedOrder O) : Proposition LX → Prop
  /-- every closed `X`-free formula -/
  | xfree {φ : Proposition LX} : IsXFreeClosed φ → InC C φ
  /-- `TI(≺)` -/
  | ti : InC C (TI C.prec)
  /-- `∼Prog(≺)` -/
  | negProg : InC C (∼(Prog C.prec))
  /-- `∀ x, X x` -/
  | allX : InC C allXat
  /-- `∀ y ≺ n̄, X y` -/
  | belowNum (n : ℕ) : InC C (belowAt C n)
  /-- `X(n̄)` -/
  | xatNum (n : ℕ) : InC C (Xat (numLX n))
  /-- `∼X(n̄)` -/
  | negXatNum (n : ℕ) : InC C (∼(Xat (numLX n)))
  /-- `P n` -/
  | pNum (n : ℕ) : InC C (P C n)
  /-- `∼(m̄ ≺ n̄) ⋎ X(m̄)` -/
  | precOrX (m n : ℕ) : InC C (precOrXat C m n)

/-- **(d) The decision lemma.**  Membership in `C`, inverted once and for all
into a disjunction of *equations*; the boundedness induction cases on this. -/
theorem InC.exhaustive {φ : Proposition LX} (h : InC C φ) :
    IsXFreeClosed φ ∨
    φ = TI C.prec ∨
    φ = ∼(Prog C.prec) ∨
    φ = allXat ∨
    (∃ n, φ = belowAt C n) ∨
    (∃ n, φ = Xat (numLX n)) ∨
    (∃ n, φ = ∼(Xat (numLX n))) ∨
    (∃ n, φ = P C n) ∨
    (∃ m n, φ = precOrXat C m n) := by
  cases h with
  | xfree hx => exact Or.inl hx
  | ti => exact Or.inr (Or.inl rfl)
  | negProg => exact Or.inr (Or.inr (Or.inl rfl))
  | allX => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | belowNum n => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))
  | xatNum n => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))
  | negXatNum n =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))))
  | pNum n =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))))
  | precOrX m n =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, n, rfl⟩)))))))

/-- Every member of `C` is closed. -/
theorem InC.freeVariables_eq_empty {φ : Proposition LX} (h : InC C φ) :
    φ.freeVariables = ∅ := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨m, n, he⟩
  · exact hx.2
  · rw [he]; exact C.freeVariables_TI
  · rw [he]; simp
  · rw [he]; simp
  · rw [he]; simp
  · rw [he]; simp
  · rw [he]; simp
  · rw [he]; simp
  · rw [he]; simp

/-! ### (c) Closure under premise-formation

One theorem per rule of `OmegaDerivable` that can have a member of `C` as its
principal formula.  In each proof the premise formula is computed *explicitly*
from the `LowerSyntax` normal forms and shown to be a member again. -/

/-- **`or`.**  The two disjuncts of a member of `C` are members of `C`.

The members with an `⋎` head are: an `X`-free closed disjunction, whose
disjuncts are `X`-free closed; `TI C.prec = ∼Prog(≺) ⋎ ∀ x X x`, whose
disjuncts are the members `∼Prog(≺)` and `∀ x X x`; and
`precOrXat C m n = ∼(m̄ ≺ n̄) ⋎ X(m̄)`, whose disjuncts are the `X`-free closed
`∼(m̄ ≺ n̄)` and the member `X(m̄)`. -/
theorem InC.of_or {φ ψ : Proposition LX} (h : InC C (φ ⋎ ψ)) : InC C φ ∧ InC C ψ := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨m, n, he⟩
  · exact ⟨.xfree (isXFreeClosed_or.mp hx).1, .xfree (isXFreeClosed_or.mp hx).2⟩
  · rw [TI_eq] at he
    obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp he
    exact ⟨.negProg, .allX⟩
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · rw [precOrXat_eq] at he
    obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp he
    exact ⟨.xfree (isXFreeClosed_neg_precAt m n), .xatNum m⟩

/-- **`and`.**  The two conjuncts of a member of `C` are members of `C`.

The members with an `⋏` head are: an `X`-free closed conjunction; and
`P C n = (∀ y ≺ n̄, X y) ⋏ ∼X(n̄)`, whose conjuncts are the members `belowAt C n`
and `∼X(n̄)`. -/
theorem InC.of_and {φ ψ : Proposition LX} (h : InC C (φ ⋏ ψ)) : InC C φ ∧ InC C ψ := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨m, n, he⟩
  · exact ⟨.xfree (isXFreeClosed_and.mp hx).1, .xfree (isXFreeClosed_and.mp hx).2⟩
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · rw [P_eq] at he
    obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp he
    exact ⟨.belowNum n, .negXatNum n⟩
  · exact absurd (congrArg head he) (by simp)

/-- **`omegaRule`.**  Every numeral instance of a universally quantified member
of `C` is a member of `C`.

The members with a `∀¹` head are: an `X`-free closed `∀`, whose instances are
`X`-free closed; `allXat = ∀ x X x`, whose instances are the atoms `X(k̄)`; and
`belowAt C n = ∀ y (∼(y ≺ n̄) ⋎ X y)`, whose instances are `precOrXat C k n`. -/
theorem InC.of_all {φ : Semiformula LX ℕ 1} (h : InC C (∀¹ φ)) (k : ℕ) :
    InC C (φ/[numLX k]) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨m, n, he⟩
  · exact .xfree (isXFreeClosed_all hx k)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · rw [allXat_eq] at he
    obtain rfl := (Semiformula.all_inj _ _).mp he
    rw [subst_allXat_body]
    exact .xatNum k
  · rw [belowAt_eq] at he
    obtain rfl := (Semiformula.all_inj _ _).mp he
    rw [subst_belowAt_body]
    exact .precOrX k n
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)

/-- **`exs`.**  Every numeral instance of an existentially quantified member of
`C` is a member of `C`.

The members with an `∃¹` head are: an `X`-free closed `∃`; and
`∼Prog(≺) = ∃ x ((∀ y ≺ x, X y) ⋏ ∼X x)`, whose instance at `k̄` is `P C k`. -/
theorem InC.of_exs {φ : Semiformula LX ℕ 1} (h : InC C (∃¹ φ)) (k : ℕ) :
    InC C (φ/[numLX k]) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨m, n, he⟩
  · exact .xfree (isXFreeClosed_exs hx k)
  · exact absurd (congrArg head he) (by simp)
  · rw [negProg_eq] at he
    obtain rfl := (Semiformula.exs_inj _ _).mp he
    rw [subst_negProg_body]
    exact .pNum k
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)

/-! ### Sequents -/

/-- A sequent all of whose formulas are in `C`. -/
def InCSeq (C : CodedOrder O) (Γ : Sequent LX) : Prop := ∀ φ ∈ Γ, InC C φ

@[simp] theorem inCSeq_nil : InCSeq C [] := by
  intro φ hφ
  simp at hφ

@[simp] theorem inCSeq_cons {φ : Proposition LX} {Γ : Sequent LX} :
    InCSeq C (φ :: Γ) ↔ InC C φ ∧ InCSeq C Γ := by
  constructor
  · intro h
    exact ⟨h φ List.mem_cons_self, fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)⟩
  · rintro ⟨hφ, hΓ⟩ ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact hφ
    · exact hΓ ψ hψ

theorem inCSeq_cons₂ {φ ψ : Proposition LX} {Γ : Sequent LX} :
    InCSeq C (φ :: ψ :: Γ) ↔ InC C φ ∧ InC C ψ ∧ InCSeq C Γ := by
  simp

@[simp] theorem inCSeq_append {Γ Δ : Sequent LX} :
    InCSeq C (Γ ++ Δ) ↔ InCSeq C Γ ∧ InCSeq C Δ := by
  constructor
  · intro h
    exact ⟨fun φ hφ => h φ (List.mem_append_left _ hφ),
      fun φ hφ => h φ (List.mem_append_right _ hφ)⟩
  · rintro ⟨hΓ, hΔ⟩ φ hφ
    rcases List.mem_append.mp hφ with hφ | hφ
    · exact hΓ φ hφ
    · exact hΔ φ hφ

/-- **`contraction`.**  A subsequent of a `C`-sequent is a `C`-sequent. -/
theorem InCSeq.of_subset {Γ Δ : Sequent LX} (h : InCSeq C Γ) (hs : Δ ⊆ Γ) : InCSeq C Δ :=
  fun φ hφ => h φ (hs hφ)

/-- **`or`, at the level of sequents.** -/
theorem InCSeq.of_or {φ ψ : Proposition LX} {Γ : Sequent LX}
    (h : InCSeq C (φ ⋎ ψ :: Γ)) : InCSeq C (φ :: ψ :: Γ) := by
  rw [inCSeq_cons] at h
  obtain ⟨hor, hΓ⟩ := h
  obtain ⟨h₁, h₂⟩ := hor.of_or
  simp [h₁, h₂, hΓ]

/-- **`and`, at the level of sequents**: both premises at once. -/
theorem InCSeq.of_and {φ ψ : Proposition LX} {Γ : Sequent LX}
    (h : InCSeq C (φ ⋏ ψ :: Γ)) : InCSeq C (φ :: Γ) ∧ InCSeq C (ψ :: Γ) := by
  rw [inCSeq_cons] at h
  obtain ⟨hand, hΓ⟩ := h
  obtain ⟨h₁, h₂⟩ := hand.of_and
  exact ⟨by simp [h₁, hΓ], by simp [h₂, hΓ]⟩

/-- **`omegaRule`, at the level of sequents**: every premise, one per numeral. -/
theorem InCSeq.of_all {φ : Semiformula LX ℕ 1} {Γ : Sequent LX}
    (h : InCSeq C ((∀¹ φ) :: Γ)) (k : ℕ) : InCSeq C (φ/[numLX k] :: Γ) := by
  rw [inCSeq_cons] at h
  obtain ⟨hall, hΓ⟩ := h
  simp [hall.of_all k, hΓ]

/-- **`exs`, at the level of sequents.** -/
theorem InCSeq.of_exs {φ : Semiformula LX ℕ 1} {Γ : Sequent LX}
    (h : InCSeq C ((∃¹ φ) :: Γ)) (k : ℕ) : InCSeq C (φ/[numLX k] :: Γ) := by
  rw [inCSeq_cons] at h
  obtain ⟨hexs, hΓ⟩ := h
  simp [hexs.of_exs k, hΓ]

/-- Every formula of a `C`-sequent is closed. -/
theorem InCSeq.freeVariables_eq_empty {Γ : Sequent LX} (h : InCSeq C Γ)
    {φ : Proposition LX} (hφ : φ ∈ Γ) : φ.freeVariables = ∅ :=
  (h φ hφ).freeVariables_eq_empty

/-! ### (d) Disjointness of the named shapes

The boundedness induction has to know that the shapes of `C` do not overlap:
its disjuncts are membership claims about *distinct* formulas.  Everything
below is either a head clash or `Xat_numLX_inj`. -/

@[simp] theorem Xat_ne_neg_Xat {n m : ℕ} : Xat (numLX n) ≠ ∼(Xat (numLX m)) := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem Xat_ne_TI {n : ℕ} : Xat (numLX n) ≠ TI C.prec := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem Xat_ne_negProg {n : ℕ} : Xat (numLX n) ≠ ∼(Prog C.prec) := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem Xat_ne_allXat {n : ℕ} : Xat (numLX n) ≠ allXat := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem Xat_ne_belowAt {n m : ℕ} : Xat (numLX n) ≠ belowAt C m := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem Xat_ne_P {n m : ℕ} : Xat (numLX n) ≠ P C m := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem Xat_ne_precOrXat {n m k : ℕ} : Xat (numLX n) ≠ precOrXat C m k := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem neg_Xat_ne_TI {n : ℕ} : ∼(Xat (numLX n)) ≠ TI C.prec := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem neg_Xat_ne_allXat {n : ℕ} : ∼(Xat (numLX n)) ≠ allXat := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem neg_Xat_ne_belowAt {n m : ℕ} : ∼(Xat (numLX n)) ≠ belowAt C m := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem neg_Xat_ne_P {n m : ℕ} : ∼(Xat (numLX n)) ≠ P C m := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem TI_ne_allXat : TI C.prec ≠ allXat := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem TI_ne_belowAt {n : ℕ} : TI C.prec ≠ belowAt C n := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem TI_ne_P {n : ℕ} : TI C.prec ≠ P C n := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem TI_ne_negProg : TI C.prec ≠ ∼(Prog C.prec) := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem allXat_ne_belowAt {n : ℕ} : allXat ≠ belowAt C n := by
  intro h
  rw [allXat_eq, belowAt_eq] at h
  exact absurd (congrArg head ((Semiformula.all_inj _ _).mp h)) (by simp)

@[simp] theorem allXat_ne_P {n : ℕ} : allXat ≠ P C n := fun h =>
  absurd (congrArg head h) (by simp)

@[simp] theorem precOrXat_ne_TI {m n : ℕ} : precOrXat C m n ≠ TI C.prec := by
  intro h
  rw [precOrXat_eq, TI_eq] at h
  exact absurd (congrArg head ((Semiformula.or_inj _ _ _ _).mp h).2) (by simp)

@[simp] theorem precOrXat_ne_P {m n k : ℕ} : precOrXat C m n ≠ P C k := fun h =>
  absurd (congrArg head h) (by simp)

/-- `P` is injective: its right conjunct is `∼X(n̄)`. -/
@[simp] theorem P_inj {n m : ℕ} : P C n = P C m ↔ n = m := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rw [P_eq, P_eq] at h
  exact neg_Xat_numLX_inj.mp ((Semiformula.and_inj _ _ _ _).mp h).2

/-- `precOrXat` determines its *first* index: the right disjunct is `X(m̄)`.

Its second index is **not** determined by anything proved here, and neither is
the index of `belowAt`: that would need `C.prec` to depend on its second
argument, which is a fact about the ordering, not about the syntax of `C`.  The
boundedness lemma does not need it — its disjuncts (b) and (c) are membership
claims, and the `m` they speak of is the one recovered here. -/
theorem precOrXat_left_inj {m n m' n' : ℕ}
    (h : precOrXat C m n = precOrXat C m' n') : m = m' := by
  rw [precOrXat_eq, precOrXat_eq] at h
  exact Xat_numLX_inj.mp ((Semiformula.or_inj _ _ _ _).mp h).2

/-! **No named shape other than `∼(m̄ ≺ n̄)` is `X`-free.**  This is the
hypothesis-separation the boundedness lemma needs: an `X`-free member of `Γ`
carries no disjunct, so it must be false in `ℕ`. -/

@[simp] theorem not_isXFreeClosed_allXat : ¬ IsXFreeClosed allXat := by
  intro h
  rw [allXat_eq] at h
  exact not_XFree_Xat (#0 : Semiterm LX ℕ 1) ((XFree_all _).mp h.1)

@[simp] theorem not_isXFreeClosed_belowAt (n : ℕ) : ¬ IsXFreeClosed (belowAt C n) := by
  intro h
  rw [belowAt_eq] at h
  exact not_XFree_Xat (#0 : Semiterm LX ℕ 1)
    ((XFree_or _ _).mp ((XFree_all _).mp h.1)).2

@[simp] theorem not_isXFreeClosed_P (n : ℕ) : ¬ IsXFreeClosed (P C n) := by
  intro h
  rw [P_eq] at h
  exact not_isXFreeClosed_belowAt n (isXFreeClosed_and.mp h).1

@[simp] theorem not_isXFreeClosed_precOrXat (m n : ℕ) :
    ¬ IsXFreeClosed (precOrXat C m n) := by
  intro h
  rw [precOrXat_eq] at h
  exact not_isXFreeClosed_Xat (isXFreeClosed_or.mp h).2

@[simp] theorem not_isXFreeClosed_negProg : ¬ IsXFreeClosed (∼(Prog C.prec)) := by
  intro h
  rw [negProg_eq] at h
  exact not_XFree_Xat (#0 : Semiterm LX ℕ 1)
    ((XFree_and _ _).mp ((XFree_exs _).mp h.1)).2

@[simp] theorem not_isXFreeClosed_TI : ¬ IsXFreeClosed (TI C.prec) := by
  intro h
  rw [TI_eq] at h
  exact not_isXFreeClosed_allXat (isXFreeClosed_or.mp h).2

end OrdinalAnalysis.Gentzen.LowerClass
