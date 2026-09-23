/-
  Substituting an arithmetical unary formula for the free set variable `0`,
  inside the evaluating second-order calculus.

  `Gentzen/SubstX.lean` is the first-order original: it defines `substX ψ` by
  structural recursion, because there the fresh predicate `X` is a *relation
  symbol* of an extended language and no rewriting can touch it.  Here `X` is
  the free set variable `0` of Foundation's monadic second-order syntax, so the
  substitution *is* a rewriting — the very one `Reduction.lean` already needs
  for the `(∀₂)/(∃₂)` cut reduction, `OmegaDerivable₂.subAt ψ 0` — and the whole
  file is a reading of `EvProvider.lean`'s `evFam` at depth `0`.

  Three things about the shape.

  * **No height cost.**  The first-order `OmegaDerivable.substX` pays
    `α ⊕ 2·complexity ψ`, because the atomic identity leaf `[X(t), ∼X(t)]`
    becomes `[ψ(t), ∼ψ(t)]`, derivable only at height `2·complexity ψ`.  The
    second-order calculus has *general* identity — `[φ, ∼φ]` at every height for
    every `φ` — so the substituted leaf is a leaf again and `subst_family`
    transports at the **same** height and rank.  This is exactly the design
    decision recorded in the header of `Calculus.lean`.

  * **`Ok` has to be relaxed at rank `0`.**  `evFam`'s `Ok ρ` is `ω ≤ ρ`,
    because a genuine substitution can raise the rank of a formula and the cut
    rule must stay legal.  At rank `0` — the cut-free calculus the lower bound
    runs in — there are no cuts at all (`rank φ < 0` is false, `NONote.zero_le'`),
    so the field is vacuous.  `evFam₀` is `evFam` with `Ok ρ := ρ = 0`; every
    other field, `S` included, is inherited unchanged, so the two families
    perform the same operation.

  * **The computation lemmas go through the plain application.**  A derivation
    carries `ev₂`-normal formulas, and on a normal form `evApp Ω` is `ev₂ ∘ Ω.app`
    (`evApp_ev₂`).  So `substX₂ ψ (ev₂ χ) = ev₂ ((subAt ψ 0).app χ)`, and the
    right-hand side is computed with Foundation's own `app` homomorphism — no
    `evSub` bookkeeping survives into the statements.  The ordering is a lift,
    hence set-free, hence fixed by every rewriting (`app_of_setFree`), and the
    three shapes `below₂`, `Prog₂`, `TI₂` turn into their `ψ`-versions
    `belowψ₂`, `Progψ₂`, `TIψ₂` with `ψ(·)` where `· ∈& 0` stood.

  A note on the free set variables of `ψ`.  `subAt ψ 0` sends `X₀` to `ψ` and
  `X_{k+1}` to `X_k`: the variables of the conclusion are renumbered down, so a
  free set variable of `ψ` names the variable of the *result*, exactly as in
  `Reduction.lean`.  `Arith ψ` (no set *quantifier* in `ψ`) is all that is
  demanded, as everywhere in this development.

  Contents.

    `app_of_setFree`, `evApp_of_setFree`   a set-free formula is fixed
    `substX₂`                              the substitution
    `substX₂_ev₂`                          …on a normal form
    `belowψ₂`, `Progψ₂`, `TIψ₂`, `TIuptoψ₂`  the `ψ`-shapes
    `TIupto₂`                              `Prog(≺) → ∀ x ≺ t, x ∈ X`
    `app_TI₂`, `app_TIupto₂`               **the computation lemmas**
    `substX₂_ev₂_TI₂`, `substX₂_ev₂_TIupto₂`
    `OmegaDerivable₂.substX₂`              **the transformation of derivations**
-/
import OrdinalAnalysis.ACAOmega.EvProvider
import OrdinalAnalysis.ACAOmega.LowerClass₂

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA

/-! ### Set-free formulas are fixed by every rewriting

A second-order rewriting replaces set atoms; a formula with no set atom and no
set quantifier has nothing to replace.  The set-quantifier clauses of the
induction are vacuous, which is why the statement can keep the *same* `N` on
both sides. -/

/-- **A set-free formula is fixed by every second-order rewriting.** -/
theorem app_of_setFree : ∀ {N n : ℕ} {φ : Semiformula ℒₒᵣ ℕ ℕ N n}, SetFree φ →
    ∀ Ω : SecondOrder.Rew ℒₒᵣ ℕ N ℕ N ℕ, Ω.app φ = φ := by
  intro N n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro _ Ω; simp
  | hNrel r v => intro _ Ω; simp
  | hBvar X t => intro h _; exact absurd h (by simp)
  | hNbvar X t => intro h _; exact absurd h (by simp)
  | hFvar X t => intro h _; exact absurd h (by simp)
  | hNfvar X t => intro h _; exact absurd h (by simp)
  | hVerum => intro _ Ω; simp
  | hFalsum => intro _ Ω; simp
  | hAnd φ ψ ihφ ihψ => intro h Ω; simp [ihφ h.1 Ω, ihψ h.2 Ω]
  | hOr φ ψ ihφ ihψ => intro h Ω; simp [ihφ h.1 Ω, ihψ h.2 Ω]
  | hAll₁ φ ih => intro h Ω; simp [ih h Ω]
  | hExs₁ φ ih => intro h Ω; simp [ih h Ω]
  | hAll₂ φ _ => intro h _; exact absurd h (by simp)
  | hExs₂ φ _ => intro h _; exact absurd h (by simp)

/-- **A set-free formula is fixed by every evaluating rewriting.** -/
theorem evApp_of_setFree : ∀ {N n : ℕ} {φ : Semiformula ℒₒᵣ ℕ ℕ N n}, SetFree φ →
    ∀ Ω : SecondOrder.Rew ℒₒᵣ ℕ N ℕ N ℕ, evApp Ω φ = φ := by
  intro N n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro _ Ω; simp
  | hNrel r v => intro _ Ω; simp
  | hBvar X t => intro h _; exact absurd h (by simp)
  | hNbvar X t => intro h _; exact absurd h (by simp)
  | hFvar X t => intro h _; exact absurd h (by simp)
  | hNfvar X t => intro h _; exact absurd h (by simp)
  | hVerum => intro _ Ω; simp
  | hFalsum => intro _ Ω; simp
  | hAnd φ ψ ihφ ihψ => intro h Ω; simp [ihφ h.1 Ω, ihψ h.2 Ω]
  | hOr φ ψ ihφ ihψ => intro h Ω; simp [ihφ h.1 Ω, ihψ h.2 Ω]
  | hAll₁ φ ih => intro h Ω; simp [ih h Ω]
  | hExs₁ φ ih => intro h Ω; simp [ih h Ω]
  | hAll₂ φ _ => intro h _; exact absurd h (by simp)
  | hExs₂ φ _ => intro h _; exact absurd h (by simp)

/-- A comparison is set-free as soon as the ordering is, so no rewriting moves
it. -/
theorem app_precAt₂ {prec : Semiformula ℒₒᵣ ℕ ℕ 0 2} (hprec : SetFree prec)
    (Ω : SecondOrder.Rew ℒₒᵣ ℕ 0 ℕ 0 ℕ) {n : ℕ} (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    Ω.app (precAt₂ prec y x) = precAt₂ prec y x :=
  app_of_setFree (setFree_precAt₂ prec hprec y x) Ω

/-! ### The substitution -/

/-- **`X₀ ↦ ψ`**, normalising exactly what it creates: `EvProvider.lean`'s
`evFam ψ` at depth `0`, as a bare function. -/
def substX₂ (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) {n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ 0 n) :
    Semiformula ℒₒᵣ ℕ ℕ 0 n :=
  evApp (OmegaDerivable₂.subAt ψ 0) φ

section Basic

variable {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1}

@[simp] theorem substX₂_verum {n : ℕ} :
    substX₂ ψ (⊤ : Semiformula ℒₒᵣ ℕ ℕ 0 n) = ⊤ := rfl

@[simp] theorem substX₂_falsum {n : ℕ} :
    substX₂ ψ (⊥ : Semiformula ℒₒᵣ ℕ ℕ 0 n) = ⊥ := rfl

@[simp] theorem substX₂_rel {n k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    substX₂ ψ (.rel r v : Semiformula ℒₒᵣ ℕ ℕ 0 n) = .rel r v := rfl

@[simp] theorem substX₂_nrel {n k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    substX₂ ψ (.nrel r v : Semiformula ℒₒᵣ ℕ ℕ 0 n) = .nrel r v := rfl

@[simp] theorem substX₂_and {n : ℕ} (φ χ : Semiformula ℒₒᵣ ℕ ℕ 0 n) :
    substX₂ ψ (φ ⋏ χ) = substX₂ ψ φ ⋏ substX₂ ψ χ := rfl

@[simp] theorem substX₂_or {n : ℕ} (φ χ : Semiformula ℒₒᵣ ℕ ℕ 0 n) :
    substX₂ ψ (φ ⋎ χ) = substX₂ ψ φ ⋎ substX₂ ψ χ := rfl

@[simp] theorem substX₂_all₁ {n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ 0 (n + 1)) :
    substX₂ ψ (∀¹ φ) = ∀¹ (substX₂ ψ φ) := rfl

@[simp] theorem substX₂_exs₁ {n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ 0 (n + 1)) :
    substX₂ ψ (∃¹ φ) = ∃¹ (substX₂ ψ φ) := rfl

@[simp] theorem substX₂_neg {n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ 0 n) :
    substX₂ ψ (∼φ) = ∼(substX₂ ψ φ) :=
  evApp_neg φ 0 (OmegaDerivable₂.subAt ψ 0)

/-- The component of `subAt ψ 0` at the substituted variable is `ψ` itself. -/
@[simp] theorem subAt_zero_fv_zero :
    (OmegaDerivable₂.subAt ψ 0).fv 0 = ψ := by
  simp [OmegaDerivable₂.subAt, OmegaDerivable₂.fvAt]

/-- **The atomic clause**: `t ∈ X` becomes `ψ(t)`, normalised. -/
@[simp] theorem substX₂_fvar_zero {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    substX₂ ψ ((t ∈& 0 : Semiformula ℒₒᵣ ℕ ℕ 0 n)) = evSub ψ t := by
  show evSub ((OmegaDerivable₂.subAt ψ 0).fv 0) t = evSub ψ t
  rw [subAt_zero_fv_zero]

@[simp] theorem substX₂_nfvar_zero {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    substX₂ ψ ((t ∉& 0 : Semiformula ℒₒᵣ ℕ ℕ 0 n)) = ∼(evSub ψ t) := by
  show ∼evSub ((OmegaDerivable₂.subAt ψ 0).fv 0) t = ∼evSub ψ t
  rw [subAt_zero_fv_zero]

/-- **A set-free formula is fixed.**  In particular the ordering and every
comparison. -/
theorem substX₂_of_setFree {n : ℕ} {φ : Semiformula ℒₒᵣ ℕ ℕ 0 n} (h : SetFree φ) :
    substX₂ ψ φ = φ :=
  evApp_of_setFree h (OmegaDerivable₂.subAt ψ 0)

/-- **On a normal form the substitution is the normalised plain substitution.**
This is `evApp_ev₂`, and it is what lets every computation below be done with
Foundation's `app` homomorphism. -/
theorem substX₂_ev₂ {n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ 0 n) :
    substX₂ ψ (ev₂ φ) = ev₂ ((OmegaDerivable₂.subAt ψ 0).app φ) :=
  evApp_ev₂ φ 0 (OmegaDerivable₂.subAt ψ 0)

end Basic

/-! ### The transfinite-induction shapes at an arbitrary `ψ`

`CodedOrder₂.lean`'s `below₂`, `Prog₂`, `TI₂` with `ψ(·)` in place of `· ∈& 0`;
`Gentzen/Jump.lean`'s `belowAt`, `progAt`, `tiUptoAt` in the second-order
syntax.  The substitution instances are the *plain* ones — the derivations meet
them under one outermost `ev₂`. -/

/-- `∀ y ≺ x, ψ(y)` — the hypothesis of progressiveness at `x`, for `ψ`. -/
def belowψ₂ (prec : Semiformula ℒₒᵣ ℕ ℕ 0 2) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    Semiformula ℒₒᵣ ℕ ℕ 0 1 :=
  ∀¹ (∼(precAt₂ prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) #1) ⋎
    ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2)])

/-- `Prog(≺, ψ) :≡ ∀ x ((∀ y ≺ x, ψ(y)) → ψ(x))`. -/
def Progψ₂ (prec : Semiformula ℒₒᵣ ℕ ℕ 0 2) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    Proposition ℒₒᵣ :=
  ∀¹ (∼(belowψ₂ prec ψ) ⋎ ψ)

/-- `TI(≺, ψ) :≡ Prog(≺, ψ) → ∀ x, ψ(x)`. -/
def TIψ₂ (prec : Semiformula ℒₒᵣ ℕ ℕ 0 2) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    Proposition ℒₒᵣ :=
  ∼(Progψ₂ prec ψ) ⋎ (∀¹ ψ)

/-- `TIupto(≺, ψ, t) :≡ Prog(≺, ψ) → ∀ x ≺ t, ψ(x)`. -/
def TIuptoψ₂ (prec : Semiformula ℒₒᵣ ℕ ℕ 0 2) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1)
    (t : FirstOrder.SyntacticTerm ℒₒᵣ) : Proposition ℒₒᵣ :=
  ∼(Progψ₂ prec ψ) ⋎ ((belowψ₂ prec ψ)/[t])

/-- `TIupto(≺, t) :≡ Prog(≺, X) → ∀ x ≺ t, x ∈ X`.  This is the sentence the
upper bound proves, one notation at a time; the unrestricted `TI₂` is what the
boundedness lemma refutes. -/
def TIupto₂ (prec : Semiformula ℒₒᵣ ℕ ℕ 0 2) (t : FirstOrder.SyntacticTerm ℒₒᵣ) :
    Proposition ℒₒᵣ :=
  ∼(Prog₂ prec) ⋎ ((below₂ prec)/[t])

theorem TIupto₂_eq (prec : Semiformula ℒₒᵣ ℕ ℕ 0 2) (t : FirstOrder.SyntacticTerm ℒₒᵣ) :
    TIupto₂ prec t = ∼(Prog₂ prec) ⋎ ((below₂ prec)/[t]) := rfl

/-- At a numeral the restricted conclusion is `LowerClass₂.belowAt₂`. -/
theorem TIupto₂_numAt {O : Type} [LinearOrder O] (C : CodedOrder₂ O) (n : ℕ) :
    TIupto₂ C.prec (numAt n) = ∼(Prog₂ C.prec) ⋎ belowAt₂ C n := rfl

/-! ### The computation lemmas -/

section Computation

variable {prec : Semiformula ℒₒᵣ ℕ ℕ 0 2}

/-- `substX₂` turns `below₂` into `belowψ₂`. -/
theorem app_below₂ (hprec : SetFree prec) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    (OmegaDerivable₂.subAt ψ 0).app (below₂ prec) = belowψ₂ prec ψ := by
  show (OmegaDerivable₂.subAt ψ 0).app
      (∀¹ (∼(precAt₂ prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) #1) ⋎
        ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) ∈& 0))) = belowψ₂ prec ψ
  rw [SecondOrder.Rew.app_all₀, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, app_precAt₂ hprec, SecondOrder.Rew.app_fvar,
    subAt_zero_fv_zero]
  rfl

/-- `substX₂` turns `Prog₂` into `Progψ₂`. -/
theorem app_Prog₂ (hprec : SetFree prec) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    (OmegaDerivable₂.subAt ψ 0).app (Prog₂ prec) = Progψ₂ prec ψ := by
  show (OmegaDerivable₂.subAt ψ 0).app
      (∀¹ (∼(below₂ prec) ⋎ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0))) = Progψ₂ prec ψ
  rw [SecondOrder.Rew.app_all₀, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, app_below₂ hprec, SecondOrder.Rew.app_fvar,
    subAt_zero_fv_zero, subst_bvar_self]
  rfl

/-- **`substX₂ ψ (TI₂ prec)` is the transfinite-induction sentence for `ψ`.** -/
theorem app_TI₂ (hprec : SetFree prec) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    (OmegaDerivable₂.subAt ψ 0).app (TI₂ prec) = TIψ₂ prec ψ := by
  show (OmegaDerivable₂.subAt ψ 0).app
      (∼(Prog₂ prec) ⋎ (∀¹ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0))) = TIψ₂ prec ψ
  rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    app_Prog₂ hprec, SecondOrder.Rew.app_all₀, SecondOrder.Rew.app_fvar,
    subAt_zero_fv_zero, subst_bvar_self]
  rfl

/-- **`substX₂ ψ (TIupto₂ prec t)` is the restricted one.** -/
theorem app_TIupto₂ (hprec : SetFree prec) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1)
    (t : FirstOrder.SyntacticTerm ℒₒᵣ) :
    (OmegaDerivable₂.subAt ψ 0).app (TIupto₂ prec t) = TIuptoψ₂ prec ψ t := by
  have hsub : (OmegaDerivable₂.subAt ψ 0).app ((below₂ prec)/[t])
      = (belowψ₂ prec ψ)/[t] := by
    show (OmegaDerivable₂.subAt ψ 0).app (FirstOrder.Rew.subst ![t] ▹ (below₂ prec))
      = FirstOrder.Rew.subst ![t] ▹ (belowψ₂ prec ψ)
    rw [SecondOrder.Rew.app_comm_subst, app_below₂ hprec]
  rw [TIupto₂_eq, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    app_Prog₂ hprec, hsub]
  rfl

/-- The form the lower bound meets: everything under one `ev₂`. -/
theorem substX₂_ev₂_TI₂ (hprec : SetFree prec) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    substX₂ ψ (ev₂ (TI₂ prec)) = ev₂ (TIψ₂ prec ψ) := by
  rw [substX₂_ev₂, app_TI₂ hprec]

theorem substX₂_ev₂_TIupto₂ (hprec : SetFree prec) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1)
    (t : FirstOrder.SyntacticTerm ℒₒᵣ) :
    substX₂ ψ (ev₂ (TIupto₂ prec t)) = ev₂ (TIuptoψ₂ prec ψ t) := by
  rw [substX₂_ev₂, app_TIupto₂ hprec]

end Computation

/-! ### The transformation of derivations -/

namespace OmegaDerivable₂

/-- **The substitution family of `X₀ ↦ ψ`, at cut rank `0`.**  `evFam` with its
rank side condition replaced by `ρ = 0`: the cut rule is unreachable there, so
nothing has to be controlled.  Every other field — `S` above all — is
`evFam`'s. -/
def evFam₀ {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1} (hψ : Arith ψ) :
    SubstFamily trueArithLits₂ evInst₂ :=
  { evFam hψ with
    Ok := fun ρ => ρ = 0
    rank_ctrl := fun _ φ ρ hok h => by
      subst hok
      exact absurd h (not_lt.mpr (NONote.zero_le' (rank φ))) }

@[simp] theorem evFam₀_S {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1} (hψ : Arith ψ)
    (φ : Proposition ℒₒᵣ) : (evFam₀ hψ).S 0 φ = OrdinalAnalysis.ACAOmega.substX₂ ψ φ := rfl

/-- **Substituting `ψ` for the free set variable `0` in a cut-free derivation**,
at the *same* height.  The first-order `OmegaDerivable.substX` pays
`2·complexity ψ` for the atomic identity leaves; general identity makes that
cost disappear. -/
theorem substX₂ {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
    {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1} (hψ : Arith ψ) {α : O} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (h : OmegaDerivable₂ trueArithLits₂ evInst₂ 0 α Γ) :
    OmegaDerivable₂ trueArithLits₂ evInst₂ 0 α
      (Γ.map (fun φ => OrdinalAnalysis.ACAOmega.substX₂ ψ φ)) :=
  subst_family (evFam₀ hψ) rfl h 0

end OmegaDerivable₂

end OrdinalAnalysis.ACAOmega
