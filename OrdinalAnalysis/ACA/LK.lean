/-
  **Our own second-order
  one-sided LK**, and `ACA₀` / `ACA` as schemata over it.

  Foundation's `SecondOrder/Derivation.lean` is full second-order logic: its
  `exs₂` rule instantiates a set quantifier by an *arbitrary* formula, which is
  full comprehension — the system it axiomatises is `Z₂`, not `ACA`.  The
  calculus here is Foundation's, rule for rule, with exactly one change:

      exs₂ now demands `Arith ψ`.

  That single side condition is what turns the calculus into Afshari–Rathjen's
  `ACA_∞` (CiE 2012, §2): arithmetical comprehension, and no other comprehension.
  Together with `Syntax.lean`'s `rank_subst₂_lt_exs₂` — an arithmetical instance
  of `∃² φ` has rank strictly below `rank (∃² φ)` — it is what will make cut
  elimination terminate.

  `identity` is kept **general**: `[φ, ∼φ]` for every `φ`, set quantifiers
  included.  Restricting it would be a different (weaker) system; Afshari–Rathjen
  keep it too and pay for it with their Lemma 2.1, which derives it at height
  `2·rank φ`.

  The theories.  `ACA₀` is equality, `PA⁻`, the **set** induction axiom (a single
  `∀²`-sentence, not a schema), set extensionality, and arithmetical
  comprehension; `ACA` adds the induction schema for *all* second-order
  formulas.  That is the whole gap between `ε₀` and `ε_{ε₀}`.

  A design decision, recorded because it is load-bearing.  **Every axiom below
  is a closed `Proposition`: no free set variable, and (as a consequence of how
  they are built) no free number variable either.**  This was not true of the
  first version of this file, which stated `compAx`/`indScheme` with a free set
  *parameter* (`compAx ψ` for `ψ` allowed to mention `t ∈& X`) and `setInduction`
  alone had no set-extensionality companion.  Both defects matter for exactly one
  later step: `all₂` (`LK.lean`'s rule, at the `Derivation` level) and `gen₂`
  (`Toolkit.lean`'s derived rule, at the `Provable` level) can only close a `∀²`
  over a context all of whose formulas satisfy `shift₁ χ = χ` — and a formula
  with a genuine free set variable is moved by `shift₁` (it renumbers `X ↦ X+1`),
  so it can never be closed off that way.  `setExt` repairs the missing
  set-extensionality axiom (`𝗘𝗤 LX`'s `relExt (Sum.inr XRel.X)` has no image in
  the old `ACA₀` at all); `indScheme₂`/`arithComp₂` repair the free-parameter
  problem by moving the parameter under an outermost `∀²`, exactly as
  `setInduction` already quantifies its own set variable.  `ACA_shift₁_invariant`
  below is the formal statement that the repair worked, for every axiom of
  `ACA` (hence of `ACA₀`, since `ACA₀ ⊆ ACA`).

  Instantiating a *particular* free set variable back out of `indScheme₂ φ` or
  `arithComp₂ ψ` (arriving, say, at "induction for the formula `x ∈& 0`") is not
  lost: it is recovered one `Provable`-level `spec₂` application away (at the
  arithmetical witness `#0 ∈& 0`), which is `Toolkit.lean`'s job, not this file's.
-/
import OrdinalAnalysis.ACA.Syntax

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder

/-! ### The calculus -/

/-- **Second-order one-sided LK with arithmetical comprehension.**

Foundation's `LO.SecondOrder.Derivation`, verbatim, except that `exs₂` carries
the hypothesis `Arith ψ`. -/
inductive Derivation : SecondOrder.Sequent ℒₒᵣ → Type
  | identity {φ : Proposition ℒₒᵣ} : Derivation [φ, ∼φ]
  | cut {φ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      Derivation (φ :: Γ) → Derivation (∼φ :: Γ) → Derivation Γ
  | wk {Γ Δ : SecondOrder.Sequent ℒₒᵣ} : Derivation Γ → Γ ⊆ Δ → Derivation Δ
  | verum : Derivation [⊤]
  | and {φ ψ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      Derivation (φ :: Γ) → Derivation (ψ :: Γ) → Derivation (φ ⋏ ψ :: Γ)
  | or {φ ψ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      Derivation (φ :: ψ :: Γ) → Derivation (φ ⋎ ψ :: Γ)
  | all₁ {φ : Semiproposition ℒₒᵣ 0 1} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      Derivation (φ.free₀ :: SecondOrder.Sequent.shift₀ Γ) → Derivation ((∀¹ φ) :: Γ)
  | exs₁ {φ : Semiproposition ℒₒᵣ 0 1} {t : FirstOrder.Semiterm ℒₒᵣ ℕ 0}
      {Γ : SecondOrder.Sequent ℒₒᵣ} :
      Derivation (φ/[t] :: Γ) → Derivation ((∃¹ φ) :: Γ)
  | all₂ {φ : Semiproposition ℒₒᵣ 1 0} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      Derivation (φ.free₁ :: SecondOrder.Sequent.shift₁ Γ) → Derivation ((∀² φ) :: Γ)
  /-- **Arithmetical comprehension.**  The only comprehension of the system: the
  witness `ψ` for a set quantifier must have no set quantifier of its own. -/
  | exs₂ {φ : Semiproposition ℒₒᵣ 1 0} {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1}
      {Γ : SecondOrder.Sequent ℒₒᵣ} (hψ : Arith ψ) :
      Derivation (φ/⟦ψ⟧ :: Γ) → Derivation ((∃² φ) :: Γ)

namespace Derivation

/-- Transport a derivation along an equality of sequents. -/
def cast {Γ Δ : SecondOrder.Sequent ℒₒᵣ} (d : Derivation Γ) (h : Γ = Δ) : Derivation Δ := h ▸ d

/-- Every derivation of the restricted calculus is one of Foundation's full
second-order LK; the restriction only removes rules. -/
def toFull : {Γ : SecondOrder.Sequent ℒₒᵣ} → Derivation Γ → SecondOrder.Derivation Γ
  | _, identity => .identity
  | _, cut dp dn => .cut (toFull dp) (toFull dn)
  | _, wk d h => .wk (toFull d) h
  | _, verum => .verum
  | _, and dp dq => .and (toFull dp) (toFull dq)
  | _, or d => .or (toFull d)
  | _, all₁ d => .all₁ (toFull d)
  | _, exs₁ d => .exs₁ (toFull d)
  | _, all₂ d => .all₂ (toFull d)
  | _, exs₂ _ d => .exs₂ (toFull d)

end Derivation

/-! ### Provability from a schema -/

/-- A derivation of `φ` from finitely many instances of the schema `𝓢`.  The
shape is Foundation's `Schema.Derivation`. -/
structure SchemaDerivation (𝓢 : Set (Proposition ℒₒᵣ)) (φ : Proposition ℒₒᵣ) where
  /-- The axioms used. -/
  axioms : SecondOrder.Sequent ℒₒᵣ
  /-- A derivation of `φ` together with the negated axioms. -/
  derivation : Derivation (φ :: ∼axioms)
  /-- Each of them really is an axiom. -/
  isInstance : ∀ ψ ∈ axioms, ψ ∈ 𝓢

/-- `𝓢 ⊢ φ`. -/
def Provable (𝓢 : Set (Proposition ℒₒᵣ)) (φ : Proposition ℒₒᵣ) : Prop :=
  Nonempty (SchemaDerivation 𝓢 φ)

theorem provable_iff {𝓢 : Set (Proposition ℒₒᵣ)} {φ : Proposition ℒₒᵣ} :
    Provable 𝓢 φ ↔
      ∃ Γ : SecondOrder.Sequent ℒₒᵣ, (∀ ψ ∈ Γ, ψ ∈ 𝓢) ∧ Nonempty (Derivation (φ :: ∼Γ)) :=
  ⟨fun ⟨d⟩ => ⟨d.axioms, d.isInstance, ⟨d.derivation⟩⟩,
   fun ⟨Γ, hΓ, ⟨d⟩⟩ => ⟨⟨Γ, d, hΓ⟩⟩⟩

/-- Provability is monotone in the schema. -/
theorem provable_mono {𝓢 𝓣 : Set (Proposition ℒₒᵣ)} (h : 𝓢 ⊆ 𝓣) {φ : Proposition ℒₒᵣ}
    (hφ : Provable 𝓢 φ) : Provable 𝓣 φ := by
  obtain ⟨d⟩ := hφ
  exact ⟨⟨d.axioms, d.derivation, fun ψ hψ => h (d.isInstance ψ hψ)⟩⟩

/-! ### The axioms -/

/-- `0`, as an `ℒₒᵣ`-term. -/
abbrev zeroT {n : ℕ} : FirstOrder.Semiterm ℒₒᵣ ℕ n := ‘0’

/-- `#0 + 1`, as an `ℒₒᵣ`-term in `n + 1` bound variables (only the innermost,
`#0`, is used — the successor of the induction variable). -/
abbrev succT {n : ℕ} : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1) := ‘#0 + 1’

/-! #### Formulas with no free set variable

`shift₁` (`Semiproposition.shift₁ = SecondOrder.Rew.shift.app`) renumbers a
formula's free set variables, `t ∈& X ↦ t ∈& (X+1)` (and `∉&` likewise), and
leaves everything else — including a *bound* set variable reached through
`∀²`/`∃²`, and the bound-variable atoms `∈#`/`∉#` — untouched (`shift.bv X =
#0 ∈# X`, the identity substitution).  So `shift₁ χ = χ` holds for exactly the
`χ` that never mention `∈&`/`∉&`, and that is the class every axiom below is
built to land in. -/

/-- **No free set variable**: no `∈&`/`∉&` atom anywhere, though `∀²`/`∃²` (and
hence `∈#`/`∉#` underneath them) are entirely permitted. -/
def NoSetFvar {N n : ℕ} : Semiproposition ℒₒᵣ N n → Prop
  |  .rel _ _ => True
  | .nrel _ _ => True
  |    _ ∈# _ => True
  |    _ ∉# _ => True
  |    _ ∈& _ => False
  |    _ ∉& _ => False
  |         ⊤ => True
  |         ⊥ => True
  |     φ ⋏ ψ => NoSetFvar φ ∧ NoSetFvar ψ
  |     φ ⋎ ψ => NoSetFvar φ ∧ NoSetFvar ψ
  |      ∀¹ φ => NoSetFvar φ
  |      ∃¹ φ => NoSetFvar φ
  |      ∀² φ => NoSetFvar φ
  |      ∃² φ => NoSetFvar φ

section NoSetFvarSimp

variable {N n : ℕ}

@[simp] theorem noSetFvar_rel {k : ℕ} (r : (ℒₒᵣ).Rel k) (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    NoSetFvar (.rel r v : Semiproposition ℒₒᵣ N n) := trivial

@[simp] theorem noSetFvar_nrel {k : ℕ} (r : (ℒₒᵣ).Rel k) (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    NoSetFvar (.nrel r v : Semiproposition ℒₒᵣ N n) := trivial

@[simp] theorem noSetFvar_bvar (X : Fin N) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    NoSetFvar (t ∈# X : Semiproposition ℒₒᵣ N n) := trivial

@[simp] theorem noSetFvar_nbvar (X : Fin N) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    NoSetFvar (t ∉# X : Semiproposition ℒₒᵣ N n) := trivial

@[simp] theorem noSetFvar_fvar (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ¬NoSetFvar (t ∈& X : Semiproposition ℒₒᵣ N n) := id

@[simp] theorem noSetFvar_nfvar (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ¬NoSetFvar (t ∉& X : Semiproposition ℒₒᵣ N n) := id

@[simp] theorem noSetFvar_verum : NoSetFvar (⊤ : Semiproposition ℒₒᵣ N n) := trivial

@[simp] theorem noSetFvar_falsum : NoSetFvar (⊥ : Semiproposition ℒₒᵣ N n) := trivial

@[simp] theorem noSetFvar_and (φ ψ : Semiproposition ℒₒᵣ N n) :
    NoSetFvar (φ ⋏ ψ) ↔ NoSetFvar φ ∧ NoSetFvar ψ := Iff.rfl

@[simp] theorem noSetFvar_or (φ ψ : Semiproposition ℒₒᵣ N n) :
    NoSetFvar (φ ⋎ ψ) ↔ NoSetFvar φ ∧ NoSetFvar ψ := Iff.rfl

@[simp] theorem noSetFvar_all₁ (φ : Semiproposition ℒₒᵣ N (n + 1)) :
    NoSetFvar (∀¹ φ) ↔ NoSetFvar φ := Iff.rfl

@[simp] theorem noSetFvar_exs₁ (φ : Semiproposition ℒₒᵣ N (n + 1)) :
    NoSetFvar (∃¹ φ) ↔ NoSetFvar φ := Iff.rfl

@[simp] theorem noSetFvar_all₂ (φ : Semiproposition ℒₒᵣ (N + 1) n) :
    NoSetFvar (∀² φ) ↔ NoSetFvar φ := Iff.rfl

@[simp] theorem noSetFvar_exs₂ (φ : Semiproposition ℒₒᵣ (N + 1) n) :
    NoSetFvar (∃² φ) ↔ NoSetFvar φ := Iff.rfl

end NoSetFvarSimp

/-- No free set variable is invariant under negation. -/
@[simp] theorem noSetFvar_neg {N n : ℕ} (φ : Semiproposition ℒₒᵣ N n) :
    NoSetFvar (∼φ) ↔ NoSetFvar φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- No free set variable is invariant under first-order rewriting (in
particular under `/[t]`, the one-point number-variable substitution). -/
@[simp] theorem noSetFvar_rew {N : ℕ} {n₁ n₂ : ℕ}
    (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂) (φ : Semiproposition ℒₒᵣ N n₁) :
    NoSetFvar (ω ▹ φ) ↔ NoSetFvar φ := by
  induction φ using Semiformula.rec' generalizing n₂ <;>
    simp [Semiformula.rew_rel, Semiformula.rew_nrel, *]

/-- No free set variable is invariant under renaming the bound set variables. -/
@[simp] theorem noSetFvar_bmap {N M n : ℕ} (f : Fin N → Fin M) (φ : Semiproposition ℒₒᵣ N n) :
    NoSetFvar (φ.bmap f) ↔ NoSetFvar φ := by
  induction φ using Semiformula.rec' generalizing M <;> simp [*]

/-- **A lifted first-order formula has no free set variable.**  `lift` never
produces an `∈&`/`∉&` node: its clauses are exactly the first-order
constructors, none of which is a set atom. -/
@[simp] theorem noSetFvar_lift {N n : ℕ} (φ : FirstOrder.Semiformula ℒₒᵣ ℕ n) :
    NoSetFvar (lift φ : Semiproposition ℒₒᵣ N n) := by
  induction φ using FirstOrder.Semiformula.rec' <;> simp [*]

/-- **The shift-invariance criterion.**  Every `NoSetFvar` formula is a fixed
point of `shift₁` — this is `all₂`/`gen₂`'s eligibility test, and it is proved
once here for every formula shape at once instead of axiom by axiom. -/
theorem shift₁_eq_self_of_noSetFvar {N n : ℕ} :
    ∀ {φ : Semiproposition ℒₒᵣ N n}, NoSetFvar φ → Semiproposition.shift₁ φ = φ := by
  intro φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro _; rfl
  | hNrel r v => intro _; rfl
  | hBvar X t => intro _; simp [Semiproposition.shift₁]
  | hNbvar X t => intro _; simp [Semiproposition.shift₁]
  | hFvar X t => intro h; exact h.elim
  | hNfvar X t => intro h; exact h.elim
  | hVerum => intro _; rfl
  | hFalsum => intro _; rfl
  | hAnd φ ψ ihφ ihψ =>
      intro h
      have e1 := ihφ h.1
      have e2 := ihψ h.2
      simp only [Semiproposition.shift₁] at e1 e2 ⊢
      simp [e1, e2]
  | hOr φ ψ ihφ ihψ =>
      intro h
      have e1 := ihφ h.1
      have e2 := ihψ h.2
      simp only [Semiproposition.shift₁] at e1 e2 ⊢
      simp [e1, e2]
  | hAll₁ φ ih =>
      intro h
      have e := ih h
      simp only [Semiproposition.shift₁] at e ⊢
      simp [e]
  | hExs₁ φ ih =>
      intro h
      have e := ih h
      simp only [Semiproposition.shift₁] at e ⊢
      simp [e]
  | hAll₂ φ ih =>
      intro h
      have e := ih h
      simp only [Semiproposition.shift₁] at e ⊢
      simp [e]
  | hExs₂ φ ih =>
      intro h
      have e := ih h
      simp only [Semiproposition.shift₁] at e ⊢
      simp [e]

/-! #### Universal closure over the parameters

**Standard `ACA` has induction and comprehension for formulas with arbitrary
set *and* number parameters, universally closed.**  Foundation's second-order
syntax already carries both closure operators, and `allNums`/`allSets` are
local names for them:

* `LO.FirstOrder.allClosure` (`∀¹*`) iterates `∀¹`, closing every bound
  *number* slot;
* `LO.SecondOrder.allClosure` (`∀²*`) iterates `∀²`, closing every bound *set*
  slot.

The de Bruijn convention throughout is Foundation's, forced by `Rew.q` /
`Rew.subst` and by the semantics (`∀² φ ⇔ ∀X ∈ 𝕊, φ[X :> E]`, `∀¹ φ ⇔ ∀x,
φ[x :> e]`): **slot `0` is the innermost bound variable.**  Consequently
`allSets φ` binds slot `N - 1` outermost and slot `0` innermost, so peeling the
prefix off with `Toolkit.lean`'s `spec₂`/`spec₁` (outermost quantifier first)
instantiates slot `N - 1` first and slot `0` last; `Toolkit.lean`'s
`specSets`/`specNums` package that bookkeeping once and for all. -/

/-- Close every bound **number** slot: `∀¹ ⋯ ∀¹ φ`, `n` times. -/
abbrev allNums {N n : ℕ} (φ : Semiproposition ℒₒᵣ N n) : Semiproposition ℒₒᵣ N 0 := ∀¹* φ

/-- Close every bound **set** slot: `∀² ⋯ ∀² φ`, `N` times. -/
abbrev allSets {N n : ℕ} (φ : Semiproposition ℒₒᵣ N n) : Semiproposition ℒₒᵣ 0 n := ∀²* φ

theorem noSetFvar_allNums {N : ℕ} :
    ∀ (n : ℕ) (φ : Semiproposition ℒₒᵣ N n), NoSetFvar φ → NoSetFvar (allNums φ)
  |       0, _, h => h
  | (n + 1), φ, h => noSetFvar_allNums n (∀¹ φ) (by simpa using h)

theorem noSetFvar_allSets {n : ℕ} :
    ∀ (N : ℕ) (φ : Semiproposition ℒₒᵣ N n), NoSetFvar φ → NoSetFvar (allSets φ)
  |       0, _, h => h
  | (N + 1), φ, h => noSetFvar_allSets N (∀² φ) (by simpa using h)

theorem shift₀_allNums {N : ℕ} :
    ∀ (n : ℕ) (φ : Semiproposition ℒₒᵣ N n),
      Semiproposition.shift₀ φ = φ → Semiproposition.shift₀ (allNums φ) = allNums φ
  |       0, _, h => h
  | (n + 1), φ, h =>
      shift₀_allNums n (∀¹ φ) (by
        show (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) ▹ (∀¹ φ) = ∀¹ φ
        rw [Semiformula.rew_all₀, FirstOrder.Rew.q_shift,
          show (FirstOrder.Rew.shift ▹ φ : Semiproposition ℒₒᵣ N (n + 1)) = φ from h])

theorem shift₀_allSets {n : ℕ} :
    ∀ (N : ℕ) (φ : Semiproposition ℒₒᵣ N n),
      Semiproposition.shift₀ φ = φ → Semiproposition.shift₀ (allSets φ) = allSets φ
  |       0, _, h => h
  | (N + 1), φ, h =>
      shift₀_allSets N (∀² φ) (by
        show (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) ▹ (∀² φ) = ∀² φ
        rw [Semiformula.rew_all₁,
          show (FirstOrder.Rew.shift ▹ φ : Semiproposition ℒₒᵣ (N + 1) n) = φ from h])

/-! #### `shift₀` across a simultaneous substitution

`gen₁` needs every axiom to be `shift₀`-fixed, and the axioms below are built
by substituting *closed* term vectors into a `shift₀`-fixed formula.  For such
a vector the two rewritings simply commute. -/

private theorem shift_comp_subst_eq {n₁ n₂ : ℕ} (v : Fin n₁ → FirstOrder.Semiterm ℒₒᵣ ℕ n₂)
    (hv : ∀ i, FirstOrder.Rew.shift (v i) = v i) :
    (FirstOrder.Rew.shift.comp (FirstOrder.Rew.subst v) : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂) =
      (FirstOrder.Rew.subst v).comp FirstOrder.Rew.shift := by
  ext x <;> simp [FirstOrder.Rew.comp_app, hv]

/-- **`shift₀` is inherited through a substitution by shift-fixed terms.** -/
theorem shift₀_subst_of {N n₁ n₂ : ℕ} {v : Fin n₁ → FirstOrder.Semiterm ℒₒᵣ ℕ n₂}
    (hv : ∀ i, FirstOrder.Rew.shift (v i) = v i) {φ : Semiproposition ℒₒᵣ N n₁}
    (hφ : Semiproposition.shift₀ φ = φ) :
    Semiproposition.shift₀ (FirstOrder.Rew.subst v ▹ φ) = FirstOrder.Rew.subst v ▹ φ := by
  show FirstOrder.Rew.shift ▹ (FirstOrder.Rew.subst v ▹ φ) = _
  rw [← FirstOrder.TransitiveRewriting.comp_app, shift_comp_subst_eq v hv,
    FirstOrder.TransitiveRewriting.comp_app,
    show (FirstOrder.Rew.shift ▹ φ : Semiproposition ℒₒᵣ N n₁) = φ from hφ]

/-! #### The axioms themselves -/

/-- **The set induction axiom.**  A single `∀²`-proposition, not a schema:
`∀X ((0 ∈ X ∧ ∀x (x ∈ X → x+1 ∈ X)) → ∀x x ∈ X)`.  This is the induction of
`ACA₀`; it is *much* weaker than induction for arbitrary second-order formulas,
and the whole `ε₀` vs `ε_{ε₀}` gap is the difference. -/
def setInduction : Proposition ℒₒᵣ :=
  ∀² ((((zeroT : FirstOrder.Semiterm ℒₒᵣ ℕ 0) ∈# (0 : Fin 1)) ⋏
        (∀¹ (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)) 🡒
          ((succT : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)))))
      🡒 (∀¹ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1))))

theorem noSetFvar_setInduction : NoSetFvar setInduction := by
  simp [setInduction, LogicalConnective.DeMorgan.imply]

/-- **Set extensionality.**  `∀²X ∀x∀y (x = y → x ∈ X → y ∈ X)` — the image
under `lift` of `𝗘𝗤 LX`'s `relExt (Sum.inr XRel.X)`, which the old `ACA₀` had
no counterpart for at all (defect (D1) of the design note).  Without it,
`congruence` (`Translate.lean`) has no base case.

The equality atom is written as the primitive `Semiformula.rel FirstOrder.Language.Eq.eq`
rather than through the `“t = u”` macro: the macro builds the atom via
`Semiformula.Operator.operator`, one indirection layer that both `eval` and
`shift₀`/`shift₁` reasoning otherwise has to unfold every time it is touched
(`Operator.eq_def` is the bridge, not tagged `simp`). `Semiformula.rel` is a
primitive constructor, so `noSetFvar_rel`/`eval_rel`/`Semiformula.rew_rel` all
apply to it directly. -/
def setExt : Proposition ℒₒᵣ :=
  ∀² (∀¹ (∀¹
    ((Semiformula.rel FirstOrder.Language.Eq.eq
        ![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2), (#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2)] :
        Semiproposition ℒₒᵣ 1 2) 🡒
      (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) ∈# (0 : Fin 1)) 🡒
        ((#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) ∈# (0 : Fin 1))))))

theorem noSetFvar_setExt : NoSetFvar setExt := by
  simp [setExt, LogicalConnective.DeMorgan.imply]

/-! #### The two schemes, with arbitrary set and number parameters

`φ : Semiproposition ℒₒᵣ N (n + 1)` carries

* the **induction variable** in its innermost bound number slot `#0`;
* `n` **number parameters** in the bound number slots `#1, …, #n`;
* `N` **set parameters** in its bound set slots `0, …, N - 1`;

and no free variable of either kind (that is the membership condition below).
`indBody φ` is then the induction statement at level `n`, and `indScheme₂ φ`
closes the `n` number parameters and the `N` set parameters universally.  A
free-variable instance (e.g. ordinary induction for a formula mentioning
`x ∈& 0` and a number parameter `&3`) is recovered from `indScheme₂ φ` by
`Toolkit.lean`'s `specSets`/`specNums`. -/

/-- The substitution reading the induction formula at the base case: the
induction variable `#0 ↦ 0`, the parameters `#(i+1) ↦ #i`. -/
def indZeroSub (n : ℕ) : Fin (n + 1) → FirstOrder.Semiterm ℒₒᵣ ℕ n :=
  (zeroT : FirstOrder.Semiterm ℒₒᵣ ℕ n) :> fun i => #i

/-- The substitution for the successor step: the induction variable
`#0 ↦ #0 + 1`, the parameters `#(i+1) ↦ #(i+1)`. -/
def indSuccSub (n : ℕ) : Fin (n + 1) → FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1) :=
  (succT : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1)) :> fun i => #(i.succ)

theorem shift_indZeroSub (n : ℕ) (i : Fin (n + 1)) :
    FirstOrder.Rew.shift (indZeroSub n i) = indZeroSub n i := by
  cases i using Fin.cases <;> simp [indZeroSub, zeroT]

theorem shift_indSuccSub (n : ℕ) (i : Fin (n + 1)) :
    FirstOrder.Rew.shift (indSuccSub n i) = indSuccSub n i := by
  cases i using Fin.cases <;> simp [indSuccSub, succT]

@[simp] theorem indZeroSub_zero (n : ℕ) : indZeroSub n 0 = (zeroT : FirstOrder.Semiterm ℒₒᵣ ℕ n) :=
  rfl

@[simp] theorem indZeroSub_succ (n : ℕ) (i : Fin n) : indZeroSub n i.succ = #i := rfl

@[simp] theorem indSuccSub_zero (n : ℕ) :
    indSuccSub n 0 = (succT : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1)) := rfl

@[simp] theorem indSuccSub_succ (n : ℕ) (i : Fin n) : indSuccSub n i.succ = #(i.succ) := rfl

/-- Substituting at the base case undoes a `bShift`: `#0 ↦ 0` never sees a
shifted variable, and every parameter `#(i+1) ↦ #i` puts it back. -/
@[simp] theorem subst_indZeroSub_bShift {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    FirstOrder.Rew.subst (indZeroSub n) (FirstOrder.Rew.bShift t) = t := by
  rw [← FirstOrder.Rew.comp_app,
    show (FirstOrder.Rew.subst (indZeroSub n)).comp FirstOrder.Rew.bShift =
        (FirstOrder.Rew.id : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) from by
      ext x <;> simp [FirstOrder.Rew.comp_app]]
  simp

/-- Substituting at the successor step turns a `bShift` back into a `bShift`. -/
@[simp] theorem subst_indSuccSub_bShift {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    FirstOrder.Rew.subst (indSuccSub n) (FirstOrder.Rew.bShift t) = FirstOrder.Rew.bShift t := by
  rw [← FirstOrder.Rew.comp_app,
    show (FirstOrder.Rew.subst (indSuccSub n)).comp FirstOrder.Rew.bShift =
        (FirstOrder.Rew.bShift : FirstOrder.Rew ℒₒᵣ ℕ n ℕ (n + 1)) from by
      ext x <;> simp [FirstOrder.Rew.comp_app]]

/-- **The induction statement for `φ`**, at the level of its `n` number
parameters and `N` set parameters:
`(φ(0) ∧ ∀x (φ(x) → φ(x+1))) → ∀x φ(x)`. -/
def indBody {N n : ℕ} (φ : Semiproposition ℒₒᵣ N (n + 1)) : Semiproposition ℒₒᵣ N n :=
  ((FirstOrder.Rew.subst (indZeroSub n) ▹ φ) ⋏
      (∀¹ (φ 🡒 FirstOrder.Rew.subst (indSuccSub n) ▹ φ)))
    🡒 (∀¹ φ)

/-- **An induction axiom for an arbitrary second-order formula**, universally
closed over all its parameters.  This is defect (D2) of the design note and its
fix, in the standard form: no free variable of either kind survives, so
`shift₁ (indScheme₂ φ) = indScheme₂ φ` (and likewise for `shift₀`). -/
def indScheme₂ {N n : ℕ} (φ : Semiproposition ℒₒᵣ N (n + 1)) : Proposition ℒₒᵣ :=
  allSets (allNums (indBody φ))

theorem noSetFvar_indBody {N n : ℕ} {φ : Semiproposition ℒₒᵣ N (n + 1)} (h : NoSetFvar φ) :
    NoSetFvar (indBody φ) := by
  simp [indBody, LogicalConnective.DeMorgan.imply, h]

theorem noSetFvar_indScheme₂ {N n : ℕ} {φ : Semiproposition ℒₒᵣ N (n + 1)} (h : NoSetFvar φ) :
    NoSetFvar (indScheme₂ φ) :=
  noSetFvar_allSets N _ (noSetFvar_allNums n _ (noSetFvar_indBody h))

theorem shift₀_indBody {N n : ℕ} {φ : Semiproposition ℒₒᵣ N (n + 1)}
    (h : Semiproposition.shift₀ φ = φ) :
    Semiproposition.shift₀ (indBody φ) = indBody φ := by
  have hφ : (FirstOrder.Rew.shift ▹ φ : Semiproposition ℒₒᵣ N (n + 1)) = φ := h
  have h0 : Semiproposition.shift₀ (FirstOrder.Rew.subst (indZeroSub n) ▹ φ) =
      FirstOrder.Rew.subst (indZeroSub n) ▹ φ := shift₀_subst_of (shift_indZeroSub n) h
  have h1 : Semiproposition.shift₀ (FirstOrder.Rew.subst (indSuccSub n) ▹ φ) =
      FirstOrder.Rew.subst (indSuccSub n) ▹ φ := shift₀_subst_of (shift_indSuccSub n) h
  simp only [Semiproposition.shift₀] at h0 h1 ⊢
  simp [indBody, LogicalConnective.DeMorgan.imply, hφ, h0, h1]

theorem shift₀_indScheme₂ {N n : ℕ} {φ : Semiproposition ℒₒᵣ N (n + 1)}
    (h : Semiproposition.shift₀ φ = φ) :
    Semiproposition.shift₀ (indScheme₂ φ) = indScheme₂ φ :=
  shift₀_allSets N _ (shift₀_allNums n _ (shift₀_indBody h))

/-! #### The induction body across the two kinds of substitution

`indBody` is built from `⋏`/`🡒`/`∀¹` and the two closed substitutions
`indZeroSub`/`indSuccSub`.  Both a number-variable rewriting and a set-variable
substitution therefore slide straight through it — `rew_indBody` is what
identifies a `toSOAt`-image of Foundation's first-order induction sentence with
an `indScheme₂` instance (`Translate.lean`), and `app_indBody` is what lets
`Toolkit.lean`'s `specSets` be applied to the closed axiom and still land on the
induction statement of the *substituted* formula. -/

/-- **A number-variable rewriting slides through `indBody`**, becoming `ω.q`
inside (the induction variable is the innermost bound slot, which `ω.q` fixes).

The two composite identities behind it:
`ω ∘ subst (indZeroSub n₁) = subst (indZeroSub n₂) ∘ ω.q` and
`ω.q ∘ subst (indSuccSub n₁) = subst (indSuccSub n₂) ∘ ω.q`. -/
theorem rew_indBody {N n₁ n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    (φ : Semiproposition ℒₒᵣ N (n₁ + 1)) :
    ω ▹ indBody φ = indBody (ω.q ▹ φ) := by
  have ha : ω.comp (FirstOrder.Rew.subst (indZeroSub n₁)) =
      (FirstOrder.Rew.subst (indZeroSub n₂)).comp ω.q := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [FirstOrder.Rew.comp_app, zeroT]
      | succ i => simp [FirstOrder.Rew.comp_app]
    · simp [FirstOrder.Rew.comp_app]
  have hb : ω.q.comp (FirstOrder.Rew.subst (indSuccSub n₁)) =
      (FirstOrder.Rew.subst (indSuccSub n₂)).comp ω.q := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [FirstOrder.Rew.comp_app, succT]
      | succ i => simp [FirstOrder.Rew.comp_app]
    · simp [FirstOrder.Rew.comp_app]
  show ω ▹ (((FirstOrder.Rew.subst (indZeroSub n₁) ▹ φ) ⋏
      (∀¹ (φ 🡒 FirstOrder.Rew.subst (indSuccSub n₁) ▹ φ))) 🡒 (∀¹ φ)) = _
  rw [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.rew_all₀, Semiformula.rew_all₀, LogicalConnective.HomClass.map_imply,
    ← FirstOrder.TransitiveRewriting.comp_app, ← FirstOrder.TransitiveRewriting.comp_app,
    ha, hb, FirstOrder.TransitiveRewriting.comp_app, FirstOrder.TransitiveRewriting.comp_app]
  rfl

/-- **A set-variable substitution slides through `indBody`.** -/
theorem app_indBody {N₁ N₂ n : ℕ} (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ)
    (φ : Semiproposition ℒₒᵣ N₁ (n + 1)) :
    Ω.app (indBody φ) = indBody (Ω.app φ) := by
  simp [indBody, SecondOrder.Rew.app_comm_subst]

/-- **The comprehension statement for `ψ`**, at the level of its `n` number
parameters and `N` set parameters: `∃Y ∀x (x ∈ Y ↔ ψ(x))`.  `ψ`'s own set
parameters (indexed `0, …, N-1`) are pushed up by `ψ.bmap Fin.succ` once the
comprehended set `Y` has taken the innermost slot `0`. -/
def compBody {N n : ℕ} (ψ : Semiproposition ℒₒᵣ N (n + 1)) : Semiproposition ℒₒᵣ N n :=
  ∃² (∀¹ (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1)) ∈# (0 : Fin (N + 1))) 🡘 ψ.bmap Fin.succ))

/-- **Arithmetical comprehension**, universally closed over all parameters:
`∀X⃗ ∀p⃗ ∃Y ∀x (x ∈ Y ↔ ψ(x, p⃗, X⃗))`. -/
def arithComp₂ {N n : ℕ} (ψ : Semiproposition ℒₒᵣ N (n + 1)) : Proposition ℒₒᵣ :=
  allSets (allNums (compBody ψ))

theorem noSetFvar_compBody {N n : ℕ} {ψ : Semiproposition ℒₒᵣ N (n + 1)} (h : NoSetFvar ψ) :
    NoSetFvar (compBody ψ) := by
  simp [compBody, LogicalConnective.iff, LogicalConnective.DeMorgan.imply, h]

theorem noSetFvar_arithComp₂ {N n : ℕ} {ψ : Semiproposition ℒₒᵣ N (n + 1)} (h : NoSetFvar ψ) :
    NoSetFvar (arithComp₂ ψ) :=
  noSetFvar_allSets N _ (noSetFvar_allNums n _ (noSetFvar_compBody h))

theorem shift₀_compBody {N n : ℕ} {ψ : Semiproposition ℒₒᵣ N (n + 1)}
    (h : Semiproposition.shift₀ ψ = ψ) :
    Semiproposition.shift₀ (compBody ψ) = compBody ψ := by
  have hb : Semiproposition.shift₀ (ψ.bmap Fin.succ) = ψ.bmap Fin.succ := by
    simp only [Semiproposition.shift₀, ← Semiformula.bmap_comm]
    rw [show FirstOrder.Rewriting.shift ψ = ψ from h]
  simp only [Semiproposition.shift₀] at hb ⊢
  simp [compBody, LogicalConnective.iff, LogicalConnective.DeMorgan.imply, hb]

theorem shift₀_arithComp₂ {N n : ℕ} {ψ : Semiproposition ℒₒᵣ N (n + 1)}
    (h : Semiproposition.shift₀ ψ = ψ) :
    Semiproposition.shift₀ (arithComp₂ ψ) = arithComp₂ ψ :=
  shift₀_allSets N _ (shift₀_allNums n _ (shift₀_compBody h))

/-- The lift of a first-order *sentence* to a proposition of the second-order
syntax. -/
def liftSentence (σ : FirstOrder.Sentence ℒₒᵣ) : Proposition ℒₒᵣ :=
  lift (FirstOrder.Rewriting.emb σ)

theorem noSetFvar_liftSentence (σ : FirstOrder.Sentence ℒₒᵣ) : NoSetFvar (liftSentence σ) :=
  noSetFvar_lift _

/-- The equality axioms of `ℒₒᵣ`, lifted. -/
def eqAxioms : Set (Proposition ℒₒᵣ) := liftSentence '' (𝗘𝗤 ℒₒᵣ)

/-- The axioms of `PA⁻`, lifted. -/
def paMinus : Set (Proposition ℒₒᵣ) := liftSentence '' 𝗣𝗔⁻

/-- **`ACA₀`**: equality, `PA⁻`, the set induction axiom, set extensionality,
and arithmetical comprehension with arbitrary set and number parameters,
universally closed.

The parameter formula `ψ` is required to have no free variable of either kind
(`NoSetFvar ψ`, `Semiproposition.shift₀ ψ = ψ`): its Lean *type*
`Semiproposition ℒₒᵣ N (n+1)` still permits stray `∈&` atoms and stray `&x`
number variables, which the closure operators — which bind bound *slots*, not
free variables — would leave free in the axiom, defeating (D1)/(D2).  Nothing
is lost by the restriction: closing a free variable off is a renaming away, and
every instance the design needs (`Jump(X₀)`, `ψ₀`, `#0 ∈& 0`) is presented with
its parameters in slots already. -/
def ACA₀ : Set (Proposition ℒₒᵣ) :=
  eqAxioms ∪ paMinus ∪ {setInduction, setExt} ∪
    {χ | ∃ (N n : ℕ) (ψ : Semiproposition ℒₒᵣ N (n + 1)), Arith ψ ∧ NoSetFvar ψ ∧
      Semiproposition.shift₀ ψ = ψ ∧ χ = arithComp₂ ψ}

set_option linter.dupNamespace false in
/-- **`ACA`**: `ACA₀` with the universally closed induction scheme for *every*
second-order formula, with arbitrary set and number parameters. -/
def ACA : Set (Proposition ℒₒᵣ) :=
  ACA₀ ∪ {χ | ∃ (N n : ℕ) (φ : Semiproposition ℒₒᵣ N (n + 1)), NoSetFvar φ ∧
    Semiproposition.shift₀ φ = φ ∧ χ = indScheme₂ φ}

theorem setInduction_mem_ACA₀ : setInduction ∈ ACA₀ :=
  Or.inl (Or.inr (Or.inl rfl))

theorem setExt_mem_ACA₀ : setExt ∈ ACA₀ :=
  Or.inl (Or.inr (Or.inr rfl))

theorem arithComp₂_mem_ACA₀ {N n : ℕ} {ψ : Semiproposition ℒₒᵣ N (n + 1)} (hψ : Arith ψ)
    (hns : NoSetFvar ψ) (h0 : Semiproposition.shift₀ ψ = ψ) : arithComp₂ ψ ∈ ACA₀ :=
  Or.inr ⟨N, n, ψ, hψ, hns, h0, rfl⟩

theorem eqAxioms_subset_ACA₀ : eqAxioms ⊆ ACA₀ :=
  fun _ h => Or.inl (Or.inl (Or.inl h))

theorem paMinus_subset_ACA₀ : paMinus ⊆ ACA₀ :=
  fun _ h => Or.inl (Or.inl (Or.inr h))

theorem indScheme₂_mem_ACA {N n : ℕ} {φ : Semiproposition ℒₒᵣ N (n + 1)} (h : NoSetFvar φ)
    (h0 : Semiproposition.shift₀ φ = φ) : indScheme₂ φ ∈ ACA :=
  Or.inr ⟨N, n, φ, h, h0, rfl⟩

/-- `ACA₀ ⊆ ACA`. -/
theorem ACA₀_subset_ACA : ACA₀ ⊆ ACA := Set.subset_union_left

/-- **Everything `ACA₀` proves, `ACA` proves.** -/
theorem aca_provable_mono {φ : Proposition ℒₒᵣ} (h : Provable ACA₀ φ) : Provable ACA φ :=
  provable_mono ACA₀_subset_ACA h

/-! #### The shift-invariance of every axiom -/

theorem ACA₀_shift₁_invariant : ∀ χ ∈ ACA₀, Semiproposition.shift₁ χ = χ := by
  rintro χ (((h | h) | h | h) | ⟨N, n, ψ, _, hns, _, rfl⟩)
  · obtain ⟨σ, _, rfl⟩ := h
    exact shift₁_eq_self_of_noSetFvar (noSetFvar_liftSentence σ)
  · obtain ⟨σ, _, rfl⟩ := h
    exact shift₁_eq_self_of_noSetFvar (noSetFvar_liftSentence σ)
  · rw [h]; exact shift₁_eq_self_of_noSetFvar noSetFvar_setInduction
  · rw [h]; exact shift₁_eq_self_of_noSetFvar noSetFvar_setExt
  · exact shift₁_eq_self_of_noSetFvar (noSetFvar_arithComp₂ hns)

/-- **The number-variable analogue of `ACA₀_shift₁_invariant`.**  Every axiom
of `ACA₀` also has no free *number* variable, hence is fixed by `shift₀`. -/
theorem ACA₀_shift₀_invariant : ∀ χ ∈ ACA₀, Semiproposition.shift₀ χ = χ := by
  rintro χ (((h | h) | h | h) | ⟨N, n, ψ, _, _, h0, rfl⟩)
  · obtain ⟨σ, _, rfl⟩ := h
    simp [liftSentence, lift, Semiproposition.shift₀]
  · obtain ⟨σ, _, rfl⟩ := h
    simp [liftSentence, lift, Semiproposition.shift₀]
  · rw [h]; simp [setInduction, Semiproposition.shift₀, LogicalConnective.DeMorgan.imply]
  · rw [h]
    have hv : (fun i => FirstOrder.Rew.shift (![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2),
        (#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2)] i)) =
        ![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2), (#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2)] := by
      funext i
      match i with
      | 0 => simp
      | 1 => simp
    simp [setExt, Semiproposition.shift₀, LogicalConnective.DeMorgan.imply,
      Semiformula.rew_rel, Semiformula.rew_nrel, hv]
  · exact shift₀_arithComp₂ h0

/-- **`ACA_shift₁_invariant`.**  Every axiom of `ACA` is a fixed point of
`shift₁`: it has no free set variable.  This is what makes `Toolkit.lean`'s
`gen₂` usable at `𝓢 = ACA` (and, via `ACA₀_shift₁_invariant`, at `𝓢 = ACA₀`). -/
theorem ACA_shift₁_invariant : ∀ χ ∈ ACA, Semiproposition.shift₁ χ = χ := by
  rintro χ (h | ⟨N, n, φ, hns, _, rfl⟩)
  · exact ACA₀_shift₁_invariant χ h
  · exact shift₁_eq_self_of_noSetFvar (noSetFvar_indScheme₂ hns)

/-- **`ACA_shift₀_invariant`.**  Every axiom of `ACA` also has no free number
variable, hence is fixed by `shift₀`.  This is what makes `Toolkit.lean`'s
`gen₁` usable at `𝓢 = ACA`/`ACA₀`. -/
theorem ACA_shift₀_invariant : ∀ χ ∈ ACA, Semiproposition.shift₀ χ = χ := by
  rintro χ (h | ⟨N, n, φ, _, h0, rfl⟩)
  · exact ACA₀_shift₀_invariant χ h
  · exact shift₀_indScheme₂ h0

end OrdinalAnalysis.ACA
