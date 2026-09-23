/-
  **`ACA + TI(<Γ₀)`**: the theory of the `Γ₀` station.

  `ACA/LK.lean` builds `ACA` as `ACA₀` together with the universally closed
  induction scheme for every second-order formula.  This file adds, for every
  notation `a : Gamma0Note`, the universally closed scheme of **transfinite
  induction along the coded Veblen ordering `≺₁` below `ā`**

      TIupto(≺₁, ā, ψ)  :≡  Prog(≺₁, ψ) → ∀ x ≺₁ ā, ψ(x)

  with arbitrary number and set parameters, exactly as `indScheme₂` presents
  induction: `tiUptoScheme a ψ := allSets (allNums (tiUptoBody ā ψ))`.

  ### Honesty: which `ψ` the scheme ranges over

  The body shape is `ACAOmega/SubstX₂.lean`'s `TIuptoψ₂` with `n` number
  parameters and `N` set parameters threaded through, and
  `tiUptoScheme_zero` identifies the two at `N = n = 0` on the nose.  The
  **membership condition of `ACAΓ` asks `Arith ψ`** — no set *quantifier* in
  `ψ` — in addition to the two closure conditions `ACA` already asks of its own
  schemes (`NoSetFvar ψ`, `shift₀ ψ = ψ`).  Set *parameters* are allowed, and
  number parameters are allowed; only set quantifiers are not.

  That restriction is forced, and it is not a weakening.

  * **Forced.**  The ω-side (`ACAOmega/AxiomsTI₂.lean`) derives the `ψ`-instance
    from the `X`-instance by `OmegaDerivable₂.substX₂`, whose `Arith ψ`
    hypothesis is *not* about rank control — `SubstX₂.evFam₀` already made the
    rank side condition vacuous at cut rank `0` — but about the `(∃₂)` rule of
    `ACA_∞`, whose witness must be arithmetical.  `SubstFamily.arith` demands
    `Arith ψ → Arith (S m ψ)`, and substituting a non-arithmetical `ψ` into an
    arithmetical `(∃₂)` witness produces a non-arithmetical one: the transformed
    derivation would be a `Z₂_∞`-derivation, not an `ACA_∞`-derivation.  Dropping
    the hypothesis would need a separate induction over derivations *without*
    `(∃₂)`, which `OmegaDerivable₂` (an inductive `Prop`) cannot express as a
    predicate on derivations.  See the notes.
  * **Not a weakening.**  `ψ := #0 ∈# 0` (the bound set variable, at `N = 1`)
    is arithmetical, has no free set variable, and is `shift₀`-fixed, so

        ∀X (Prog(≺₁, X) → ∀ x ≺₁ ā, x ∈ X)

    *is* an instance of the scheme (`tiUptoSet`).  That sentence is the standard
    statement of `TI(<Γ₀)` in second-order arithmetic, and over `ACA₀` it
    returns every arithmetical instance by comprehension.  So `ACAΓ` is exactly
    `ACA + TI(<Γ₀)`, with the redundant arithmetical instances added for free.

  Contents.

    `precG`                        `y ≺₁ x`, at any number of set parameters
    `belowSub`, `atSub`            the two substitutions the body uses
    `belowG`, `progG`, `tiUptoBody`   the parametrised `TIupto` shape
    `tiUptoScheme`                 **the axiom**, universally closed
    `tiUptoScheme_zero`            **the identification lemma** with `TIuptoψ₂`
    `tiUptoSet`                    the `∀X`-instance
    `ACAΓ`                         **the theory**
    `ACAΓ_shift₀_invariant`, `ACAΓ_shift₁_invariant`, `ACA_subset_ACAΓ`
-/
import OrdinalAnalysis.ACA.LK
import OrdinalAnalysis.ACAOmega.SubstX₂
import OrdinalAnalysis.ACAOmega.Gamma0Order₂

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.ACAOmega
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)

/-! ### The coded ordering, at any number of set parameters

`ACAOmega/CodedOrder₂.lean`'s `precAt₂` is fixed at `N = 0` set slots, because
that is all `TI₂` ever needs.  The scheme's body lives under `N` set parameters,
so the comparison is re-lifted here; `precG_zero` says the two agree where both
are defined. -/

/-- **`y ≺₁ x`**, as a second-order formula with `N` set parameters.  A lift of
a first-order formula, hence set-free and fixed by every set-variable
rewriting. -/
def precG {N n : ℕ} (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) : Semiproposition ℒₒᵣ N n :=
  lift (FirstOrder.Rew.subst ![y, x] ▹ precFO₁)

/-- At `N = 0` the comparison is `CodedOrder₂`'s. -/
theorem precG_zero {n : ℕ} (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    (precG y x : Semiproposition ℒₒᵣ 0 n) = precAt₂ gamma0Order₂.prec y x := by
  rw [precG, gamma0Order₂_prec, precAt₂, lift_rew]

@[simp] theorem noSetFvar_precG {N n : ℕ} (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    NoSetFvar (precG y x : Semiproposition ℒₒᵣ N n) := noSetFvar_lift _

/-- The comparison's first-order original is closed as soon as both terms
are. -/
theorem freeVariables_precG₀ {n : ℕ} {y x : FirstOrder.Semiterm ℒₒᵣ ℕ n}
    (hy : y.freeVariables = ∅) (hx : x.freeVariables = ∅) :
    ((FirstOrder.Rew.subst ![y, x] : FirstOrder.Rew ℒₒᵣ ℕ 2 ℕ n)
      ▹ precFO₁).freeVariables = ∅ :=
  Gentzen.LowerSyntax.freeVariables_rew_eq_empty _ freeVariables_precFO₁
    (Fin.forall_fin_two.mpr ⟨by simpa using hy, by simpa using hx⟩)

/-- **The comparison has no free number variable** whenever its two terms have
none. -/
theorem shift₀_precG {N n : ℕ} {y x : FirstOrder.Semiterm ℒₒᵣ ℕ n}
    (hy : y.freeVariables = ∅) (hx : x.freeVariables = ∅) :
    Semiproposition.shift₀ (precG y x : Semiproposition ℒₒᵣ N n) = precG y x := by
  show (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) ▹ (precG y x) = precG y x
  rw [precG, ← lift_rew]
  congr 1
  refine FirstOrder.Semiformula.rew_eq_self_of (by simp) (fun z hz => ?_)
  rw [FirstOrder.Semiformula.FVar?, freeVariables_precG₀ hy hx] at hz
  simp at hz

/-! ### The two substitutions

The de Bruijn convention is `indBody`'s: in a formula `ψ` with `n + 1` number
slots, slot `0` is the induction variable and slots `1, …, n` are the
parameters. -/

/-- The induction variable becomes the innermost bound variable `y`, under two
extra binders (`y` and `x`); each parameter slot is pushed up by two. -/
def belowSub (n : ℕ) : Fin (n + 1) → FirstOrder.Semiterm ℒₒᵣ ℕ (n + 2) :=
  fun i => Fin.cases (#0) (fun j => #(j.succ.succ)) i

@[simp] theorem belowSub_zero (n : ℕ) :
    belowSub n 0 = (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 2)) := rfl

@[simp] theorem belowSub_succ (n : ℕ) (i : Fin n) :
    belowSub n i.succ = (#(i.succ.succ) : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 2)) := rfl

theorem shift_belowSub (n : ℕ) (i : Fin (n + 1)) :
    (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ (n + 2) ℕ (n + 2)) (belowSub n i)
      = belowSub n i := by
  cases i using Fin.cases <;> simp

/-- The induction variable becomes the term `t`; each parameter slot drops back
by one. -/
def atSub {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    Fin (n + 1) → FirstOrder.Semiterm ℒₒᵣ ℕ n :=
  fun i => Fin.cases t (fun j => #j) i

@[simp] theorem atSub_zero {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : atSub t 0 = t := rfl

@[simp] theorem atSub_succ {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) (i : Fin n) :
    atSub t i.succ = (#i : FirstOrder.Semiterm ℒₒᵣ ℕ n) := rfl

theorem shift_atSub {n : ℕ} (c : ℕ) (i : Fin (n + 1)) :
    (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) (atSub (numAt c) i)
      = atSub (numAt c) i := by
  cases i using Fin.cases <;> simp

/-! ### The parametrised `TIupto` shape

`SubstX₂.lean`'s `belowψ₂`, `Progψ₂`, `TIuptoψ₂`, with `ψ`'s number and set
parameters carried along.  `tiUptoScheme_zero` below identifies them at
`N = n = 0`, which is the only place the ω-calculus ever meets them. -/

/-- `∀ y ≺₁ x, ψ(y)` — the hypothesis of progressiveness at `x` (slot `0`). -/
def belowG {N n : ℕ} (ψ : Semiproposition ℒₒᵣ N (n + 1)) : Semiproposition ℒₒᵣ N (n + 1) :=
  ∀¹ (∼(precG (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 2)) #1) ⋎
    (FirstOrder.Rew.subst (belowSub n) ▹ ψ))

/-- `Prog(≺₁, ψ) :≡ ∀ x ((∀ y ≺₁ x, ψ(y)) → ψ(x))`. -/
def progG {N n : ℕ} (ψ : Semiproposition ℒₒᵣ N (n + 1)) : Semiproposition ℒₒᵣ N n :=
  ∀¹ (∼(belowG ψ) ⋎ ψ)

/-- `TIupto(≺₁, t, ψ) :≡ Prog(≺₁, ψ) → ∀ x ≺₁ t, ψ(x)`. -/
def tiUptoBody {N n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n)
    (ψ : Semiproposition ℒₒᵣ N (n + 1)) : Semiproposition ℒₒᵣ N n :=
  ∼(progG ψ) ⋎ (FirstOrder.Rew.subst (atSub t) ▹ (belowG ψ))

/-- **The new axiom**: transfinite induction along `≺₁` below the notation `a`,
for the formula `ψ`, universally closed over all its parameters. -/
def tiUptoScheme {N n : ℕ} (a : Gamma0Note) (ψ : Semiproposition ℒₒᵣ N (n + 1)) :
    Proposition ℒₒᵣ :=
  allSets (allNums (tiUptoBody (numAt (gamma0Code a)) ψ))

/-! ### The identification lemma -/

theorem belowSub_zero_eq : belowSub 0 = ![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2)] := by
  funext i
  match i with
  | 0 => rfl

theorem atSub_zero_eq (t : FirstOrder.Semiterm ℒₒᵣ ℕ 0) : atSub t = ![t] := by
  funext i
  match i with
  | 0 => rfl

theorem belowG_zero (ψ : Semiproposition ℒₒᵣ 0 1) :
    belowG ψ = belowψ₂ gamma0Order₂.prec ψ := by
  rw [belowG, belowψ₂, precG_zero, belowSub_zero_eq]

theorem progG_zero (ψ : Semiproposition ℒₒᵣ 0 1) :
    progG ψ = Progψ₂ gamma0Order₂.prec ψ := by
  rw [progG, belowG_zero, Progψ₂]

theorem tiUptoBody_zero (t : FirstOrder.Semiterm ℒₒᵣ ℕ 0) (ψ : Semiproposition ℒₒᵣ 0 1) :
    tiUptoBody t ψ = TIuptoψ₂ gamma0Order₂.prec ψ t := by
  rw [tiUptoBody, progG_zero, belowG_zero, atSub_zero_eq, TIuptoψ₂]

/-- **The identification lemma.**  With no parameters the scheme is exactly the
shape `ACAOmega/SubstX₂.lean` produces from `TIupto₂` by `substX₂ ψ`, and the
two closure operators are the identity. -/
theorem tiUptoScheme_zero (a : Gamma0Note) (ψ : Semiproposition ℒₒᵣ 0 1) :
    tiUptoScheme a ψ = TIuptoψ₂ gamma0Order₂.prec ψ (numAt (gamma0Code a)) := by
  show tiUptoBody (numAt (gamma0Code a)) ψ = _
  rw [tiUptoBody_zero]

/-! ### The two closure conditions -/

theorem noSetFvar_belowG {N n : ℕ} {ψ : Semiproposition ℒₒᵣ N (n + 1)} (h : NoSetFvar ψ) :
    NoSetFvar (belowG ψ) := by
  simp [belowG, h]

theorem noSetFvar_progG {N n : ℕ} {ψ : Semiproposition ℒₒᵣ N (n + 1)} (h : NoSetFvar ψ) :
    NoSetFvar (progG ψ) := by
  simp [progG, noSetFvar_belowG h, h]

theorem noSetFvar_tiUptoBody {N n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n)
    {ψ : Semiproposition ℒₒᵣ N (n + 1)} (h : NoSetFvar ψ) : NoSetFvar (tiUptoBody t ψ) := by
  simp [tiUptoBody, noSetFvar_progG h, noSetFvar_belowG h]

theorem noSetFvar_tiUptoScheme {N n : ℕ} (a : Gamma0Note)
    {ψ : Semiproposition ℒₒᵣ N (n + 1)} (h : NoSetFvar ψ) :
    NoSetFvar (tiUptoScheme a ψ) :=
  noSetFvar_allSets N _ (noSetFvar_allNums n _ (noSetFvar_tiUptoBody _ h))

theorem shift₀_belowG {N n : ℕ} {ψ : Semiproposition ℒₒᵣ N (n + 1)}
    (h : Semiproposition.shift₀ ψ = ψ) :
    Semiproposition.shift₀ (belowG ψ) = belowG ψ := by
  have hp : Semiproposition.shift₀
      (precG (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 2)) #1 : Semiproposition ℒₒᵣ N (n + 2))
      = precG #0 #1 := shift₀_precG (by simp) (by simp)
  have hs : Semiproposition.shift₀
      ((FirstOrder.Rew.subst (belowSub n) : FirstOrder.Rew ℒₒᵣ ℕ (n + 1) ℕ (n + 2)) ▹ ψ)
      = FirstOrder.Rew.subst (belowSub n) ▹ ψ :=
    shift₀_subst_of (shift_belowSub n) h
  simp only [Semiproposition.shift₀] at hp hs ⊢
  simp [belowG, hp, hs]

theorem shift₀_progG {N n : ℕ} {ψ : Semiproposition ℒₒᵣ N (n + 1)}
    (h : Semiproposition.shift₀ ψ = ψ) :
    Semiproposition.shift₀ (progG ψ) = progG ψ := by
  have hb := shift₀_belowG h
  simp only [Semiproposition.shift₀] at hb h ⊢
  simp [progG, hb, h]

theorem shift₀_tiUptoBody {N n : ℕ} (c : ℕ) {ψ : Semiproposition ℒₒᵣ N (n + 1)}
    (h : Semiproposition.shift₀ ψ = ψ) :
    Semiproposition.shift₀ (tiUptoBody (numAt c) ψ) = tiUptoBody (numAt c) ψ := by
  have hp := shift₀_progG h
  have hs : Semiproposition.shift₀
      ((FirstOrder.Rew.subst (atSub (numAt c)) : FirstOrder.Rew ℒₒᵣ ℕ (n + 1) ℕ n)
        ▹ (belowG ψ))
      = FirstOrder.Rew.subst (atSub (numAt c)) ▹ (belowG ψ) :=
    shift₀_subst_of (shift_atSub c) (shift₀_belowG h)
  simp only [Semiproposition.shift₀] at hp hs ⊢
  simp [tiUptoBody, hp, hs]

theorem shift₀_tiUptoScheme {N n : ℕ} (a : Gamma0Note) {ψ : Semiproposition ℒₒᵣ N (n + 1)}
    (h : Semiproposition.shift₀ ψ = ψ) :
    Semiproposition.shift₀ (tiUptoScheme a ψ) = tiUptoScheme a ψ :=
  shift₀_allSets N _ (shift₀_allNums n _ (shift₀_tiUptoBody _ h))

/-! ### The theory -/

/-- The scheme of transfinite induction along `≺₁` below every notation, for
every **arithmetical** formula with arbitrary number and set parameters.  See
the module docstring for why `Arith` is there and why nothing is lost. -/
def tiGammaScheme : Set (Proposition ℒₒᵣ) :=
  {χ | ∃ (N n : ℕ) (a : Gamma0Note) (ψ : Semiproposition ℒₒᵣ N (n + 1)), Arith ψ ∧
    NoSetFvar ψ ∧ Semiproposition.shift₀ ψ = ψ ∧ χ = tiUptoScheme a ψ}

/-- **`ACA + TI(<Γ₀)`.** -/
def ACAΓ : Set (Proposition ℒₒᵣ) := ACA ∪ tiGammaScheme

theorem tiUptoScheme_mem_ACAΓ {N n : ℕ} (a : Gamma0Note) {ψ : Semiproposition ℒₒᵣ N (n + 1)}
    (hψ : Arith ψ) (hns : NoSetFvar ψ) (h0 : Semiproposition.shift₀ ψ = ψ) :
    tiUptoScheme a ψ ∈ ACAΓ :=
  Or.inr ⟨N, n, a, ψ, hψ, hns, h0, rfl⟩

theorem ACA_subset_ACAΓ : ACA ⊆ ACAΓ := Set.subset_union_left

/-- **Everything `ACA` proves, `ACA + TI(<Γ₀)` proves.** -/
theorem acaΓ_provable_mono {φ : Proposition ℒₒᵣ} (h : Provable ACA φ) : Provable ACAΓ φ :=
  provable_mono ACA_subset_ACAΓ h

/-- **Every axiom of `ACAΓ` is a fixed point of `shift₁`**: it has no free set
variable.  What `Toolkit.lean`'s `gen₂` asks for. -/
theorem ACAΓ_shift₁_invariant : ∀ χ ∈ ACAΓ, Semiproposition.shift₁ χ = χ := by
  rintro χ (h | ⟨N, n, a, ψ, -, hns, -, rfl⟩)
  · exact ACA_shift₁_invariant χ h
  · exact shift₁_eq_self_of_noSetFvar (noSetFvar_tiUptoScheme a hns)

/-- **Every axiom of `ACAΓ` is a fixed point of `shift₀`**: it has no free
number variable.  What `LowerBound₂.numClosed₂_of_shift₀` turns into the
`NumClosed₂` hypothesis of `replay₂_closed`. -/
theorem ACAΓ_shift₀_invariant : ∀ χ ∈ ACAΓ, Semiproposition.shift₀ χ = χ := by
  rintro χ (h | ⟨N, n, a, ψ, -, -, h0, rfl⟩)
  · exact ACA_shift₀_invariant χ h
  · exact shift₀_tiUptoScheme a h0

/-! ### The `∀X`-instance

`ψ := #0 ∈# 0` at `N = 1`, `n = 0`: the sentence `∀X (Prog(≺₁, X) → ∀ x ≺₁ ā,
x ∈ X)`, which is the textbook `TI(<Γ₀)`.  It is an instance of the scheme, so
nothing has to be proved about it here. -/

/-- The unary formula `x ∈ X` at the bound set slot `0`. -/
def memSlot : Semiproposition ℒₒᵣ 1 1 := (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)

@[simp] theorem arith_memSlot : Arith memSlot := trivial

@[simp] theorem noSetFvar_memSlot : NoSetFvar memSlot := trivial

@[simp] theorem shift₀_memSlot : Semiproposition.shift₀ memSlot = memSlot := by
  show (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1) ▹ memSlot = memSlot
  simp [memSlot, Semiformula.rew_bvar]

/-- **`∀X (Prog(≺₁, X) → ∀ x ≺₁ ā, x ∈ X)`**, the textbook `TI(< ā)`. -/
def tiUptoSet (a : Gamma0Note) : Proposition ℒₒᵣ := tiUptoScheme a memSlot

theorem tiUptoSet_mem_ACAΓ (a : Gamma0Note) : tiUptoSet a ∈ ACAΓ :=
  tiUptoScheme_mem_ACAΓ a arith_memSlot noSetFvar_memSlot shift₀_memSlot

end OrdinalAnalysis.ACA
