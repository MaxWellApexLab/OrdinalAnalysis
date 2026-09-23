/-
  The infinitary calculus `ACA_∞`, after
  Afshari–Rathjen 2012 §2, on Foundation's monadic second-order syntax as used in
  `ACA/`.

  What is lifted from `Omega/Calculus.lean`, and what is new.

  * Heights are a generic `[OrdinalNotation O]`; atomic axioms are a set of
    closed first-order literals `Literals₂`; number quantifiers instantiate by
    numeral-then-normalise through an `Instantiation₂`, exactly as before.

  * **Cut ranks are ordinal notations** (`ACA.rank`, valued in `NONote`): a cut
    on `φ` is allowed at rank `ρ` when `rank φ < ρ`.  Set quantifiers cost `ω`,
    so a derivation of rank `≤ ω` has no set-quantifier cuts at all; those are
    the cuts the second cut-elimination theorem charges `α ↦ ε_α` for.

  * The **(∀₂) rule is an eigenvariable rule**, Foundation's `all₂` verbatim:
    from `φ.free₁ :: shift₁ Γ` conclude `∀² φ :: Γ`.  The **(∃₂) rule** instantiates
    by an *arithmetical* one-hole formula `ψ` and — this is a design decision —
    normalises the result: its premise is `I.nf (φ/⟦ψ⟧)`, not `φ/⟦ψ⟧`.  The
    evaluating replay of a finitary `exs₂` produces `ev ((σφ)/⟦σψ⟧)`, and that is
    not of the form `(ev' φ')/⟦ψ'⟧` for any `ψ'` (take `ψ = R(#0 + 1)`), so a raw
    premise could not be replayed.  With `I := Instantiation₂.raw` the premise is
    the plain `φ/⟦ψ⟧`.

  * **Identity is general**: `[φ, ∼φ]` for every `φ`, at every height.  The
    reduction of a (∀₂)/(∃₂) cut substitutes the witness `ψ` for the eigenvariable
    in the (∀₂) premise, and that substitution has to preserve heights exactly,
    because the reduction lemma's bound `redOrd β γ` leaves no room for anything
    that depends on `ψ`.  With atomic identity only, the leaf `[t ∈ X, t ∉ X]` at
    height `0` would become `[ψ(t), ∼ψ(t)]`, derivable only at height
    `2·complexity ψ`; general identity makes the substituted leaf a leaf again.
    General identity is admissible from atomic identity at height
    `2·complexity` (the set-quantifier case goes through `shift₁`/`free₁`), so the
    calculus proves exactly what the atomic version proves, at heights that
    differ by a finite amount.

  * The **substitution lemma** is abstract: a `SubstFamily` is a depth-indexed
    family of formula maps with the laws the induction over derivations consumes,
    and `subst_family` transports a derivation along it at the same height and
    rank.  Any second-order `Rew` whose components are arithmetical and which
    commutes with the normaliser gives one (`RewFamily.toSubstFamily`); the
    renamings of free set variables always do (`nf_rename` is a field of
    `Instantiation₂`), which gives the shift transport `map_shift₁` that the
    (∀₂) cases of the reduction lemma need.  The substitution of a formula for
    the eigenvariable is supplied per instantiation: for `Instantiation₂.raw` in
    `Reduction.lean`; for an evaluating instantiation it is the "substitute, then
    normalise the fresh subformulas" map, whose laws are the evaluator's
    congruence laws (not done here).
-/
import OrdinalAnalysis.ACA.Syntax
import OrdinalAnalysis.Ordinal.Notation

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA

variable {L : FirstOrder.Language}

/-! ### Two facts about negation -/

theorem neg_ne_self {Ξ ξ : Type*} {N n : ℕ} (φ : Semiformula L Ξ ξ N n) : ∼φ ≠ φ := by
  cases φ using Semiformula.cases' <;> simp

theorem neg_injective {Ξ ξ : Type*} {N n : ℕ} {φ ψ : Semiformula L Ξ ξ N n} (h : ∼φ = ∼ψ) :
    φ = ψ := by
  have := congrArg (fun χ => ∼χ) h
  simpa only [Semiformula.neg_neg] using this

/-! ### The atomic axioms -/

/-- The atomic axioms: a consistent set of closed first-order literals.  Set
atoms `t ∈& X` are never axioms — the calculus reasons about a free set variable
only through identity, exactly as the first-order calculus reasons about its
predicate symbol `X`. -/
structure Literals₂ (L : FirstOrder.Language) where
  /-- The axioms. -/
  T : Proposition L → Prop
  /-- Every axiom is a first-order literal. -/
  literal : ∀ φ, T φ →
    ∃ (k : ℕ) (rl : L.Rel k) (v : Fin k → FirstOrder.Semiterm L ℕ 0),
      φ = Semiformula.rel rl v ∨ φ = Semiformula.nrel rl v
  /-- No axiom is asserted together with its negation. -/
  consistent : ∀ φ, T φ → T (∼φ) → False

namespace Literals₂

variable {A : Literals₂ L}

theorem ne_verum {φ : Proposition L} (h : A.T φ) : φ ≠ ⊤ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem ne_falsum {φ : Proposition L} (h : A.T φ) : φ ≠ ⊥ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem ne_or {φ ψ₁ ψ₂ : Proposition L} (h : A.T φ) : φ ≠ ψ₁ ⋎ ψ₂ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem ne_and {φ ψ₁ ψ₂ : Proposition L} (h : A.T φ) : φ ≠ ψ₁ ⋏ ψ₂ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem ne_all₁ {φ : Proposition L} {ψ : Semiproposition L 0 1} (h : A.T φ) : φ ≠ ∀¹ ψ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem ne_exs₁ {φ : Proposition L} {ψ : Semiproposition L 0 1} (h : A.T φ) : φ ≠ ∃¹ ψ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem ne_all₂ {φ : Proposition L} {ψ : Semiproposition L 1 0} (h : A.T φ) : φ ≠ ∀² ψ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem ne_exs₂ {φ : Proposition L} {ψ : Semiproposition L 1 0} (h : A.T φ) : φ ≠ ∃² ψ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

/-- The negation of an axiom is a first-order literal too. -/
theorem neg_literal {φ : Proposition L} (h : A.T φ) :
    ∃ (k : ℕ) (rl : L.Rel k) (v : Fin k → FirstOrder.Semiterm L ℕ 0),
      ∼φ = Semiformula.rel rl v ∨ ∼φ = Semiformula.nrel rl v := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h
  · exact ⟨k, rl, v, Or.inr rfl⟩
  · exact ⟨k, rl, v, Or.inl rfl⟩

theorem neg_ne_verum {φ : Proposition L} (h : A.T φ) : ∼φ ≠ ⊤ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem neg_ne_falsum {φ : Proposition L} (h : A.T φ) : ∼φ ≠ ⊥ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem neg_ne_or {φ ψ₁ ψ₂ : Proposition L} (h : A.T φ) : ∼φ ≠ ψ₁ ⋎ ψ₂ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem neg_ne_and {φ ψ₁ ψ₂ : Proposition L} (h : A.T φ) : ∼φ ≠ ψ₁ ⋏ ψ₂ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem neg_ne_all₁ {φ : Proposition L} {ψ : Semiproposition L 0 1} (h : A.T φ) :
    ∼φ ≠ ∀¹ ψ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem neg_ne_exs₁ {φ : Proposition L} {ψ : Semiproposition L 0 1} (h : A.T φ) :
    ∼φ ≠ ∃¹ ψ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem neg_ne_all₂ {φ : Proposition L} {ψ : Semiproposition L 1 0} (h : A.T φ) :
    ∼φ ≠ ∀² ψ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem neg_ne_exs₂ {φ : Proposition L} {ψ : Semiproposition L 1 0} (h : A.T φ) :
    ∼φ ≠ ∃² ψ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

/-- Axioms have rank `0`, hence rank at most anything. -/
theorem rank_eq_zero {φ : Proposition L} (h : A.T φ) : rank φ = 0 := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

end Literals₂

/-! ### Two identities about second-order rewriting

These are needed already by `Instantiation₂.raw` below, and again by the
substitution lemma. -/

/-- `χ/[#0] = χ`. -/
theorem subst_bvar_self {Ξ ξ : Type*} {N : ℕ} (χ : Semiformula L Ξ ξ N 1) :
    χ/[(#0 : FirstOrder.Semiterm L ξ 1)] = χ := by
  have e : (FirstOrder.Rew.subst ![(#0 : FirstOrder.Semiterm L ξ 1)]) =
      (FirstOrder.Rew.id : FirstOrder.Rew L ξ 1 ξ 1) := by
    rw [← FirstOrder.Rew.subst_eq_id]
    congr 1
    funext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  show FirstOrder.Rew.subst ![(#0 : FirstOrder.Semiterm L ξ 1)] ▹ χ = χ
  rw [e]
  simp

/-- Restricting a one-variable substitution to no variables is the identity. -/
theorem subst_bRight_succ (Φ : Fin 1 → Semiformula L ℕ ℕ 0 1) :
    (SecondOrder.Rew.subst Φ).bRight (Fin.succ : Fin 0 → Fin 1) = SecondOrder.Rew.id := by
  ext X
  · exact X.elim0
  · simp

/-- Restricting `free` to no bound variables is `shift`. -/
theorem free_bRight_succ :
    (SecondOrder.Rew.free (L := L) (ξ := ℕ) (N := 0)).bRight (Fin.succ : Fin 0 → Fin 1) =
      SecondOrder.Rew.shift := by
  ext X
  · exact X.elim0
  · simp

/-- **A second-order substitution commutes with instantiating a set quantifier.** -/
theorem app_subst₂ (Ω : SecondOrder.Rew L ℕ 0 ℕ 0 ℕ) (φ : Semiproposition L 1 0)
    (ψ : Semiformula L ℕ ℕ 0 1) :
    Ω.app (φ/⟦ψ⟧) = (Ω.q.app φ)/⟦Ω.app ψ⟧ := by
  have e : Ω.comp (SecondOrder.Rew.subst ![ψ]) =
      (SecondOrder.Rew.subst ![Ω.app ψ]).comp Ω.q := by
    ext X
    · cases X using Fin.cases with
      | zero => simp
      | succ X => exact X.elim0
    · simp only [SecondOrder.Rew.comp_fv, SecondOrder.Rew.subst_fv, SecondOrder.Rew.app_fvar,
        SecondOrder.Rew.q_fv, SecondOrder.Rew.bmap_app_eq, subst_bRight_succ,
        SecondOrder.Rew.app_id, subst_bvar_self]
  show Ω.app ((SecondOrder.Rew.subst ![ψ]).app φ) =
    (SecondOrder.Rew.subst ![Ω.app ψ]).app (Ω.q.app φ)
  rw [← SecondOrder.Rew.app_comp, ← SecondOrder.Rew.app_comp, e]

/-! ### Instantiation -/

/-- How quantifiers instantiate: a family of numerals, a normaliser applied after
every number substitution, the instance of a *set*-quantifier body, and the laws
the calculus consumes.  `rank_nf` replaces the first-order `complexity_nf`;
`nf_rename` says the normaliser does not look at the names of free set
variables, which is what makes the shift transport `map_shift₁` available for
every instantiation.

`inst₂` is a **field**, not `nf (φ/⟦ψ⟧)`.  It has to be, because a substitution
family has to agree with it on `free₁ φ` and be the identity on `shift₁ γ`, and
those two ranges overlap: with `inst₂ φ ψ = nf (φ/⟦ψ⟧)` and a normaliser that
moves a formula with no set variable in it at all — the evaluator of
`ACAOmega/Evaluate.lean` is one — no such family exists.  The evaluating
instantiation therefore takes for `inst₂` the map that substitutes `ψ` and
normalises *only the freshly created* instances `ψ/[t]`; `raw` takes plain
substitution, and `nf (φ/⟦ψ⟧)` is still a legal choice for any `nf` that fixes
what it does not create. -/
structure Instantiation₂ (L : FirstOrder.Language) where
  /-- The numerals. -/
  num : ℕ → FirstOrder.SyntacticTerm L
  /-- The normaliser. -/
  nf : Proposition L → Proposition L
  /-- The normaliser commutes with negation. -/
  nf_neg : ∀ φ : Proposition L, nf (∼φ) = ∼nf φ
  /-- The normaliser preserves the rank. -/
  rank_nf : ∀ φ : Proposition L, rank (nf φ) = rank φ
  /-- The normaliser commutes with renaming the free set variables. -/
  nf_rename : ∀ (f : ℕ → ℕ) (φ : Proposition L),
    nf ((SecondOrder.Rew.rewrite f).app φ) = (SecondOrder.Rew.rewrite f).app (nf φ)
  /-- The instance of a set-quantifier body by the one-hole formula `ψ`. -/
  inst₂ : Semiproposition L 1 0 → Semiformula L ℕ ℕ 0 1 → Proposition L
  /-- Instantiation commutes with negation. -/
  inst₂_neg : ∀ (φ : Semiproposition L 1 0) (ψ : Semiformula L ℕ ℕ 0 1),
    inst₂ (∼φ) ψ = ∼inst₂ φ ψ
  /-- Instantiation has the rank of the plain substitution — this is what makes
  the `(∃₂)` rule reduce the cut rank. -/
  rank_inst₂ : ∀ (φ : Semiproposition L 1 0) (ψ : Semiformula L ℕ ℕ 0 1),
    rank (inst₂ φ ψ) = rank (φ/⟦ψ⟧)
  /-- Instantiation commutes with renaming the free set variables. -/
  inst₂_rename : ∀ (f : ℕ → ℕ) (φ : Semiproposition L 1 0) (ψ : Semiformula L ℕ ℕ 0 1),
    (SecondOrder.Rew.rewrite f).app (inst₂ φ ψ)
      = inst₂ ((SecondOrder.Rew.rewrite f).app φ) ((SecondOrder.Rew.rewrite f).app ψ)

attribute [simp] Instantiation₂.inst₂_neg

namespace Instantiation₂

variable (I : Instantiation₂ L)

/-- The `n`-th instance of a number-quantifier body. -/
def inst (φ : Semiproposition L 0 1) (n : ℕ) : Proposition L := I.nf (φ/[I.num n])

@[simp] theorem inst_neg (φ : Semiproposition L 0 1) (n : ℕ) :
    I.inst (∼φ) n = ∼I.inst φ n := by
  simp only [inst]
  rw [← I.nf_neg]
  congr 1
  simp

@[simp] theorem rank_inst (φ : Semiproposition L 0 1) (n : ℕ) :
    rank (I.inst φ n) = rank φ := by
  simp only [inst, I.rank_nf, rank_subst₁]

/-- **The instantiation bound.**  An arithmetical instance of a set-quantifier
body has rank strictly below the rank of the quantified formula. -/
theorem rank_inst₂_lt_exs₂ {φ : Semiproposition L 1 0} {ψ : Semiformula L ℕ ℕ 0 1}
    (hψ : Arith ψ) : rank (I.inst₂ φ ψ) < rank (∃² φ) := by
  rw [I.rank_inst₂]
  exact rank_subst₂_lt_exs₂ hψ

theorem rank_inst₂_lt_all₂ {φ : Semiproposition L 1 0} {ψ : Semiformula L ℕ ℕ 0 1}
    (hψ : Arith ψ) : rank (I.inst₂ φ ψ) < rank (∀² φ) := by
  rw [I.rank_inst₂]
  exact rank_subst₂_lt_all₂ hψ

/-- Plain substitution, with no normalisation. -/
def raw (num : ℕ → FirstOrder.SyntacticTerm L) : Instantiation₂ L where
  num := num
  nf := id
  nf_neg _ := rfl
  rank_nf _ := rfl
  nf_rename _ _ := rfl
  inst₂ φ ψ := φ/⟦ψ⟧
  inst₂_neg _ _ := by simp [Semiproposition.subst₁]
  rank_inst₂ _ _ := rfl
  inst₂_rename f φ ψ := by
    have h := app_subst₂ (SecondOrder.Rew.rewrite f) φ ψ
    rwa [SecondOrder.Rew.q_rewrite] at h

@[simp] theorem raw_num (num : ℕ → FirstOrder.SyntacticTerm L) : (raw num).num = num := rfl

@[simp] theorem raw_nf (num : ℕ → FirstOrder.SyntacticTerm L) (φ : Proposition L) :
    (raw num).nf φ = φ := rfl

@[simp] theorem raw_inst (num : ℕ → FirstOrder.SyntacticTerm L) (φ : Semiproposition L 0 1)
    (n : ℕ) : (raw num).inst φ n = φ/[num n] := rfl

@[simp] theorem raw_inst₂ (num : ℕ → FirstOrder.SyntacticTerm L) (φ : Semiproposition L 1 0)
    (ψ : Semiformula L ℕ ℕ 0 1) : (raw num).inst₂ φ ψ = φ/⟦ψ⟧ := rfl

end Instantiation₂

/-! ### The calculus -/

/-- Derivability in `ACA_∞`, at cut rank `ρ` (cuts on formulas of rank `< ρ`),
of height below `α`, with number instances supplied by `I` and atomic axioms by
`A`. -/
inductive OmegaDerivable₂ {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
    (A : Literals₂ L) (I : Instantiation₂ L) (ρ : NONote) :
    O → SecondOrder.Sequent L → Prop
  | atom {α : O} {φ : Proposition L} :
      A.T φ → OmegaDerivable₂ A I ρ α [φ]
  | identity {α : O} (φ : Proposition L) :
      OmegaDerivable₂ A I ρ α [φ, ∼φ]
  | verum {α : O} :
      OmegaDerivable₂ A I ρ α [⊤]
  | or {α β : O} {φ ψ : Proposition L} {Γ : SecondOrder.Sequent L} :
      β < α → OmegaDerivable₂ A I ρ β (φ :: ψ :: Γ) →
      OmegaDerivable₂ A I ρ α (φ ⋎ ψ :: Γ)
  | and {α β γ : O} {φ ψ : Proposition L} {Γ : SecondOrder.Sequent L} :
      β < α → γ < α →
      OmegaDerivable₂ A I ρ β (φ :: Γ) → OmegaDerivable₂ A I ρ γ (ψ :: Γ) →
      OmegaDerivable₂ A I ρ α (φ ⋏ ψ :: Γ)
  | omegaRule {α : O} {φ : Semiproposition L 0 1} {Γ : SecondOrder.Sequent L}
      (β : ℕ → O) :
      (∀ n, β n < α) →
      (∀ n : ℕ, OmegaDerivable₂ A I ρ (β n) (I.inst φ n :: Γ)) →
      OmegaDerivable₂ A I ρ α ((∀¹ φ) :: Γ)
  | exs {α β : O} {φ : Semiproposition L 0 1} {Γ : SecondOrder.Sequent L} (n : ℕ) :
      β < α → OmegaDerivable₂ A I ρ β (I.inst φ n :: Γ) →
      OmegaDerivable₂ A I ρ α ((∃¹ φ) :: Γ)
  | all₂ {α β : O} {φ : Semiproposition L 1 0} {Γ : SecondOrder.Sequent L} :
      β < α → OmegaDerivable₂ A I ρ β (φ.free₁ :: SecondOrder.Sequent.shift₁ Γ) →
      OmegaDerivable₂ A I ρ α ((∀² φ) :: Γ)
  | exs₂ {α β : O} {φ : Semiproposition L 1 0} {ψ : Semiformula L ℕ ℕ 0 1}
      {Γ : SecondOrder.Sequent L} (hψ : Arith ψ) :
      β < α → OmegaDerivable₂ A I ρ β (I.inst₂ φ ψ :: Γ) →
      OmegaDerivable₂ A I ρ α ((∃² φ) :: Γ)
  | contraction {α : O} {Δ Γ : SecondOrder.Sequent L} :
      Δ ⊆ Γ → OmegaDerivable₂ A I ρ α Δ →
      OmegaDerivable₂ A I ρ α Γ
  | cut {α β γ : O} {φ : Proposition L} {Γ Δ : SecondOrder.Sequent L} :
      rank φ < ρ → β < α → γ < α →
      OmegaDerivable₂ A I ρ β (φ :: Γ) → OmegaDerivable₂ A I ρ γ (∼φ :: Δ) →
      OmegaDerivable₂ A I ρ α (Γ ++ Δ)

namespace OmegaDerivable₂

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals₂ L} {I : Instantiation₂ L}

/-- Weakening in the ordinal index. -/
theorem mono_ord {ρ : NONote} {α β : O} {Γ : SecondOrder.Sequent L}
    (h : OmegaDerivable₂ A I ρ α Γ) (hab : α ≤ β) : OmegaDerivable₂ A I ρ β Γ := by
  induction h generalizing β with
  | atom h => exact .atom h
  | identity φ => exact .identity φ
  | verum => exact .verum
  | or hlt _ ih => exact .or (lt_of_lt_of_le hlt hab) (ih le_rfl)
  | and h₁ h₂ _ _ ih₁ ih₂ =>
      exact .and (lt_of_lt_of_le h₁ hab) (lt_of_lt_of_le h₂ hab) (ih₁ le_rfl) (ih₂ le_rfl)
  | omegaRule f hf _ ih =>
      exact .omegaRule f (fun n => lt_of_lt_of_le (hf n) hab) (fun n => ih n le_rfl)
  | exs n hlt _ ih => exact .exs n (lt_of_lt_of_le hlt hab) (ih le_rfl)
  | all₂ hlt _ ih => exact .all₂ (lt_of_lt_of_le hlt hab) (ih le_rfl)
  | exs₂ hψ hlt _ ih => exact .exs₂ hψ (lt_of_lt_of_le hlt hab) (ih le_rfl)
  | contraction ss _ ih => exact .contraction ss (ih hab)
  | cut hc h₁ h₂ _ _ ih₁ ih₂ =>
      exact .cut hc (lt_of_lt_of_le h₁ hab) (lt_of_lt_of_le h₂ hab) (ih₁ le_rfl) (ih₂ le_rfl)

/-- Weakening in the cut rank. -/
theorem mono_rank {ρ σ : NONote} {α : O} {Γ : SecondOrder.Sequent L}
    (h : OmegaDerivable₂ A I ρ α Γ) (hrs : ρ ≤ σ) : OmegaDerivable₂ A I σ α Γ := by
  induction h with
  | atom h => exact .atom h
  | identity φ => exact .identity φ
  | verum => exact .verum
  | or hlt _ ih => exact .or hlt ih
  | and h₁ h₂ _ _ ih₁ ih₂ => exact .and h₁ h₂ ih₁ ih₂
  | omegaRule f hf _ ih => exact .omegaRule f hf ih
  | exs n hlt _ ih => exact .exs n hlt ih
  | all₂ hlt _ ih => exact .all₂ hlt ih
  | exs₂ hψ hlt _ ih => exact .exs₂ hψ hlt ih
  | contraction ss _ ih => exact .contraction ss ih
  | cut hc h₁ h₂ _ _ ih₁ ih₂ => exact .cut (lt_of_lt_of_le hc hrs) h₁ h₂ ih₁ ih₂

/-- A sequent carrying a formula together with its negation is derivable outright. -/
theorem of_mem_identity {ρ : NONote} {α : O} {Θ : SecondOrder.Sequent L}
    (φ : Proposition L) (hp : φ ∈ Θ) (hn : ∼φ ∈ Θ) : OmegaDerivable₂ A I ρ α Θ := by
  refine .contraction ?_ (.identity φ)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hp
  · exact hn

/-- `⊤` in a sequent makes it derivable outright. -/
theorem of_mem_verum {ρ : NONote} {α : O} {Θ : SecondOrder.Sequent L}
    (h : (⊤ : Proposition L) ∈ Θ) : OmegaDerivable₂ A I ρ α Θ := by
  refine .contraction ?_ .verum
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl
  exact h

/-- If the head of a derivable sequent already occurs in its tail, drop it. -/
theorem drop_head {ρ : NONote} {α : O} {ψ : Proposition L} {Θ : SecondOrder.Sequent L}
    (h : OmegaDerivable₂ A I ρ α (ψ :: Θ)) (hmem : ψ ∈ Θ) : OmegaDerivable₂ A I ρ α Θ := by
  refine .contraction ?_ h
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hmem
  · exact hx

/-- An identity sequent inside a bigger one: the two members are either both in
the rest, or one of them is the distinguished formula and the other its
negation, sitting in the rest. -/
theorem identity_cases {χ φ : Proposition L} {Θ : SecondOrder.Sequent L}
    (hss : ([χ, ∼χ] : SecondOrder.Sequent L) ⊆ φ :: Θ) :
    (χ ∈ Θ ∧ ∼χ ∈ Θ) ∨ ∼φ ∈ Θ := by
  have h₁ := hss (show χ ∈ [χ, ∼χ] by simp)
  have h₂ := hss (show ∼χ ∈ [χ, ∼χ] by simp)
  simp only [List.mem_cons] at h₁ h₂
  rcases h₁ with rfl | h₁
  · rcases h₂ with h₂ | h₂
    · exact absurd h₂ (neg_ne_self χ)
    · exact Or.inr h₂
  · rcases h₂ with h₂ | h₂
    · refine Or.inr ?_
      rw [← h₂, Semiformula.neg_neg]
      exact h₁
    · exact Or.inl ⟨h₁, h₂⟩

/-! ### Substitution

The abstract substitution lemma; the two identities about Foundation's
second-order rewriting that it needs are above, before `Instantiation₂`. -/

/-- Lifting a substitution under `N` set binders. -/
def liftN (Ω : SecondOrder.Rew L ℕ 0 ℕ 0 ℕ) : (N : ℕ) → SecondOrder.Rew L ℕ N ℕ N ℕ
  | 0 => Ω
  | N + 1 => (liftN Ω N).q

@[simp] theorem liftN_zero (Ω : SecondOrder.Rew L ℕ 0 ℕ 0 ℕ) : liftN Ω 0 = Ω := rfl

@[simp] theorem liftN_succ (Ω : SecondOrder.Rew L ℕ 0 ℕ 0 ℕ) (N : ℕ) :
    liftN Ω (N + 1) = (liftN Ω N).q := rfl

/-- **A substitution family**: a depth-indexed family of formula maps that
respects every rule of the calculus.  Depth `m` is the number of `(∀₂)` binders
the induction has passed under; `free` and `shift` say what happens under one
more.  `Ok` is the set of cut ranks at which the family may be applied — all of
them for a renaming, the ranks `≥ ω` for a genuine substitution. -/
structure SubstFamily (A : Literals₂ L) (I : Instantiation₂ L) where
  /-- The maps, at every depth and on every kind of semiformula. -/
  S : ℕ → ∀ {N n : ℕ}, Semiformula L ℕ ℕ N n → Semiformula L ℕ ℕ N n
  neg : ∀ (m : ℕ) {N n : ℕ} (φ : Semiformula L ℕ ℕ N n), S m (∼φ) = ∼S m φ
  verum : ∀ (m : ℕ) {N n : ℕ}, S m (⊤ : Semiformula L ℕ ℕ N n) = ⊤
  or : ∀ (m : ℕ) {N n : ℕ} (φ ψ : Semiformula L ℕ ℕ N n), S m (φ ⋎ ψ) = S m φ ⋎ S m ψ
  and : ∀ (m : ℕ) {N n : ℕ} (φ ψ : Semiformula L ℕ ℕ N n), S m (φ ⋏ ψ) = S m φ ⋏ S m ψ
  all₁ : ∀ (m : ℕ) {N n : ℕ} (φ : Semiformula L ℕ ℕ N (n + 1)), S m (∀¹ φ) = ∀¹ (S m φ)
  exs₁ : ∀ (m : ℕ) {N n : ℕ} (φ : Semiformula L ℕ ℕ N (n + 1)), S m (∃¹ φ) = ∃¹ (S m φ)
  all₂ : ∀ (m : ℕ) {N n : ℕ} (φ : Semiformula L ℕ ℕ (N + 1) n), S m (∀² φ) = ∀² (S m φ)
  exs₂ : ∀ (m : ℕ) {N n : ℕ} (φ : Semiformula L ℕ ℕ (N + 1) n), S m (∃² φ) = ∃² (S m φ)
  inst : ∀ (m : ℕ) (φ : Semiproposition L 0 1) (n : ℕ), S m (I.inst φ n) = I.inst (S m φ) n
  arith : ∀ (m : ℕ) (ψ : Semiformula L ℕ ℕ 0 1), Arith ψ → Arith (S m ψ)
  inst₂ : ∀ (m : ℕ) (φ : Semiproposition L 1 0) (ψ : Semiformula L ℕ ℕ 0 1),
    S m (I.inst₂ φ ψ) = I.inst₂ (S m φ) (S m ψ)
  free : ∀ (m : ℕ) (φ : Semiproposition L 1 0),
    S (m + 1) (Semiproposition.free₁ φ) = Semiproposition.free₁ (S m φ)
  shift : ∀ (m : ℕ) (φ : Proposition L),
    S (m + 1) (Semiproposition.shift₁ φ) = Semiproposition.shift₁ (S m φ)
  atom : ∀ (m : ℕ) (φ : Proposition L), A.T φ → S m φ = φ
  /-- The cut ranks at which the family is safe. -/
  Ok : NONote → Prop
  rank_ctrl : ∀ (m : ℕ) (φ : Proposition L) (ρ : NONote), Ok ρ → rank φ < ρ → rank (S m φ) < ρ

theorem shift₁_map_eq (F : SubstFamily A I) (m : ℕ) (Γ : SecondOrder.Sequent L) :
    (SecondOrder.Sequent.shift₁ Γ).map (F.S (m + 1)) =
      SecondOrder.Sequent.shift₁ (Γ.map (F.S m)) := by
  show (Γ.map Semiproposition.shift₁).map (F.S (m + 1)) =
    (Γ.map (F.S m)).map Semiproposition.shift₁
  rw [List.map_map, List.map_map]
  congr 1
  funext φ
  exact F.shift m φ

/-- **The substitution lemma.**  A derivation transports along a substitution
family, at every depth, at the same height and rank. -/
theorem subst_family (F : SubstFamily A I) {ρ : NONote} (hρ : F.Ok ρ) :
    ∀ {α : O} {Γ : SecondOrder.Sequent L}, OmegaDerivable₂ A I ρ α Γ →
      ∀ m : ℕ, OmegaDerivable₂ A I ρ α (Γ.map (F.S m)) := by
  intro α Γ h
  induction h with
  | atom hφ =>
      intro m
      rw [List.map_cons, List.map_nil, F.atom m _ hφ]
      exact .atom hφ
  | identity φ =>
      intro m
      rw [List.map_cons, List.map_cons, List.map_nil, F.neg]
      exact .identity _
  | verum =>
      intro m
      rw [List.map_cons, List.map_nil, F.verum]
      exact .verum
  | or hlt _ ih =>
      intro m
      rw [List.map_cons, F.or]
      exact .or hlt (by simpa only [List.map_cons] using ih m)
  | and h₁ h₂ _ _ ih₁ ih₂ =>
      intro m
      rw [List.map_cons, F.and]
      exact .and h₁ h₂ (by simpa only [List.map_cons] using ih₁ m)
        (by simpa only [List.map_cons] using ih₂ m)
  | omegaRule β hβ _ ih =>
      intro m
      rw [List.map_cons, F.all₁]
      refine .omegaRule β hβ (fun n => ?_)
      have := ih n m
      rwa [List.map_cons, F.inst] at this
  | exs n hlt _ ih =>
      intro m
      rw [List.map_cons, F.exs₁]
      refine .exs n hlt ?_
      have := ih m
      rwa [List.map_cons, F.inst] at this
  | all₂ hlt _ ih =>
      intro m
      rw [List.map_cons, F.all₂]
      refine .all₂ hlt ?_
      have := ih (m + 1)
      rwa [List.map_cons, F.free, shift₁_map_eq] at this
  | exs₂ hψ hlt _ ih =>
      intro m
      rw [List.map_cons, F.exs₂]
      refine .exs₂ (F.arith m _ hψ) hlt ?_
      have := ih m
      rwa [List.map_cons, F.inst₂] at this
  | contraction ss _ ih =>
      intro m
      exact .contraction (List.map_subset _ ss) (ih m)
  | @cut _ _ _ φ _ _ hc h₁ h₂ _ _ ih₁ ih₂ =>
      intro m
      rw [List.map_append]
      refine .cut (F.rank_ctrl m φ _ hρ hc) h₁ h₂ (by simpa only [List.map_cons] using ih₁ m)
        (by simpa only [List.map_cons, F.neg] using ih₂ m)

/-- A family of second-order rewritings, one per depth, from which a
substitution family is built: every free-variable component is arithmetical,
the family is closed under passing a `(∀₂)` binder, and the normaliser commutes
with every member. -/
structure RewFamily (I : Instantiation₂ L) where
  Ω : ℕ → SecondOrder.Rew L ℕ 0 ℕ 0 ℕ
  arith_fv : ∀ (m : ℕ) (X : ℕ), Arith ((Ω m).fv X)
  free_comp : ∀ m : ℕ,
    (Ω (m + 1)).comp SecondOrder.Rew.free = SecondOrder.Rew.free.comp (Ω m).q
  shift_comp : ∀ m : ℕ,
    (Ω (m + 1)).comp SecondOrder.Rew.shift = SecondOrder.Rew.shift.comp (Ω m)
  nf_comm : ∀ (m : ℕ) (φ : Proposition L), I.nf ((Ω m).app φ) = (Ω m).app (I.nf φ)
  /-- The rewriting commutes with instantiating a set quantifier.  With
  `inst₂ φ ψ = nf (φ/⟦ψ⟧)` this is `nf_comm` and `app_subst₂`; in general it is
  an extra demand, because `inst₂` is a field of `Instantiation₂`. -/
  inst₂_comm : ∀ (m : ℕ) (φ : Semiproposition L 1 0) (ψ : Semiformula L ℕ ℕ 0 1),
    (Ω m).app (I.inst₂ φ ψ) = I.inst₂ ((Ω m).q.app φ) ((Ω m).app ψ)
  Ok : NONote → Prop
  rank_ctrl : ∀ (m : ℕ) (φ : Proposition L) (ρ : NONote),
    Ok ρ → rank φ < ρ → rank ((Ω m).app φ) < ρ

/-- The substitution family of a rewriting family. -/
def RewFamily.toSubstFamily (A : Literals₂ L) (R : RewFamily I) : SubstFamily A I where
  S m {N} {_} φ := (liftN (R.Ω m) N).app φ
  neg := by intros; simp
  verum := by intros; simp
  or := by intros; simp
  and := by intros; simp
  all₁ := by intros; rfl
  exs₁ := by intros; rfl
  all₂ := by intros; rfl
  exs₂ := by intros; rfl
  inst m φ n := by
    simp only [Instantiation₂.inst, liftN_zero]
    rw [← R.nf_comm]
    congr 1
    exact SecondOrder.Rew.app_comm_subst _ _ _
  arith m ψ hψ := arith_app ψ hψ (R.Ω m) (fun X => X.elim0) (fun X => R.arith_fv m X)
  inst₂ m φ ψ := R.inst₂_comm m φ ψ
  free m φ := by
    show (R.Ω (m + 1)).app (SecondOrder.Rew.free.app φ) =
      SecondOrder.Rew.free.app ((R.Ω m).q.app φ)
    rw [← SecondOrder.Rew.app_comp, ← SecondOrder.Rew.app_comp, R.free_comp]
  shift m φ := by
    show (R.Ω (m + 1)).app (SecondOrder.Rew.shift.app φ) =
      SecondOrder.Rew.shift.app ((R.Ω m).app φ)
    rw [← SecondOrder.Rew.app_comp, ← SecondOrder.Rew.app_comp, R.shift_comp]
  atom m φ hφ := by
    obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ hφ <;> simp
  Ok := R.Ok
  rank_ctrl m φ ρ hok h := R.rank_ctrl m φ ρ hok h

/-! ### Renamings, and the shift transport -/

/-- The renaming one binder further in: the eigenvariable `0` is kept, and `f`
acts on the rest. -/
def liftF (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | X + 1 => f X + 1

/-- The renaming at depth `m`. -/
def liftFN (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => f
  | m + 1 => liftF (liftFN f m)

@[simp] theorem liftF_zero (f : ℕ → ℕ) : liftF f 0 = 0 := rfl

@[simp] theorem liftF_succ (f : ℕ → ℕ) (X : ℕ) : liftF f (X + 1) = f X + 1 := rfl

@[simp] theorem liftFN_zero (f : ℕ → ℕ) : liftFN f 0 = f := rfl

@[simp] theorem liftFN_succ (f : ℕ → ℕ) (m : ℕ) : liftFN f (m + 1) = liftF (liftFN f m) := rfl

/-- The rank does not see a renaming of the free set variables. -/
theorem rank_rewrite (f : ℕ → ℕ) : ∀ {N n : ℕ} (φ : Semiformula L ℕ ℕ N n),
    rank ((SecondOrder.Rew.rewrite f).app φ) = rank φ := by
  intro N n φ
  induction φ using Semiformula.rec' with
  | hRel r v => simp
  | hNrel r v => simp
  | hBvar X t => simp
  | hNbvar X t => simp
  | hFvar X t => simp
  | hNfvar X t => simp
  | hVerum => simp
  | hFalsum => simp
  | hAnd φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hOr φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hAll₁ φ ih => simp [ih]
  | hExs₁ φ ih => simp [ih]
  | hAll₂ φ ih => simp [SecondOrder.Rew.q_rewrite, ih]
  | hExs₂ φ ih => simp [SecondOrder.Rew.q_rewrite, ih]

/-- The renamings form a rewriting family, safe at every rank. -/
def renameFamily (I : Instantiation₂ L) (f : ℕ → ℕ) : RewFamily I where
  Ω m := SecondOrder.Rew.rewrite (liftFN f m)
  arith_fv m X := by simp
  free_comp m := by
    have e : (SecondOrder.Rew.free (L := L) (ξ := ℕ) (N := 0)).bv 0 = #0 ∈& 0 :=
      SecondOrder.Rew.free_bvar_last 0
    ext X
    · cases X using Fin.cases with
      | zero => simp [e]
      | succ X => exact X.elim0
    · simp
  shift_comp m := by
    ext X
    · exact X.elim0
    · simp
  nf_comm m φ := I.nf_rename _ φ
  inst₂_comm m φ ψ := by
    rw [SecondOrder.Rew.q_rewrite]
    exact I.inst₂_rename _ φ ψ
  Ok _ := True
  rank_ctrl m φ ρ _ h := by rw [rank_rewrite]; exact h

/-- **Renaming transport.**  A renaming of the free set variables preserves
derivability, at the same height and rank. -/
theorem map_rename {ρ : NONote} (f : ℕ → ℕ) {α : O} {Γ : SecondOrder.Sequent L}
    (h : OmegaDerivable₂ A I ρ α Γ) :
    OmegaDerivable₂ A I ρ α (Γ.map (SecondOrder.Rew.rewrite f).app) :=
  subst_family (RewFamily.toSubstFamily A (renameFamily I f)) trivial h 0

/-- **Shift transport.**  The (∀₂) rule shifts its context; this carries the
other premise of a cut along. -/
theorem map_shift₁ {ρ : NONote} {α : O} {Γ : SecondOrder.Sequent L}
    (h : OmegaDerivable₂ A I ρ α Γ) :
    OmegaDerivable₂ A I ρ α (SecondOrder.Sequent.shift₁ Γ) :=
  map_rename (· + 1) h

theorem mem_shift₁ {x : Proposition L} {Γ : SecondOrder.Sequent L} :
    x ∈ SecondOrder.Sequent.shift₁ Γ ↔ ∃ y ∈ Γ, Semiproposition.shift₁ y = x :=
  List.mem_map

theorem shift₁_mem {y : Proposition L} {Γ : SecondOrder.Sequent L} (h : y ∈ Γ) :
    Semiproposition.shift₁ y ∈ SecondOrder.Sequent.shift₁ Γ :=
  List.mem_map_of_mem h

theorem shift₁_subset {Γ Δ : SecondOrder.Sequent L} (h : Γ ⊆ Δ) :
    SecondOrder.Sequent.shift₁ Γ ⊆ SecondOrder.Sequent.shift₁ Δ :=
  List.map_subset _ h

@[simp] theorem shift₁_neg (φ : Proposition L) :
    Semiproposition.shift₁ (∼φ) = ∼Semiproposition.shift₁ φ :=
  LogicalConnective.HomClass.map_neg _ _

@[simp] theorem shift₁_falsum : Semiproposition.shift₁ (⊥ : Proposition L) = ⊥ :=
  LogicalConnective.HomClass.map_bot _

@[simp] theorem shift₁_verum : Semiproposition.shift₁ (⊤ : Proposition L) = ⊤ :=
  LogicalConnective.HomClass.map_top _

@[simp] theorem rank_shift₁ (φ : Proposition L) :
    rank (Semiproposition.shift₁ φ) = rank φ :=
  rank_rewrite _ φ

/-! ### `⊥` is a passenger -/

/-- Membership in a subset of `⊥ :: Θ`, after a shift. -/
theorem shift₁_subset_falsum {Γ Θ : SecondOrder.Sequent L}
    (hss : Γ ⊆ (⊥ : Proposition L) :: Θ) :
    SecondOrder.Sequent.shift₁ Γ ⊆ (⊥ : Proposition L) :: SecondOrder.Sequent.shift₁ Θ := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_shift₁.mp hx
  have := hss hy
  simp only [List.mem_cons] at this ⊢
  rcases this with rfl | h
  · exact Or.inl shift₁_falsum
  · exact Or.inr (shift₁_mem h)

set_option maxHeartbeats 1000000 in
/-- `⊥` is a passenger: no rule introduces it, so it can only have entered by
weakening and can be dropped again. -/
theorem drop_falsum {ρ : NONote} :
    ∀ {α : O} {Γ : SecondOrder.Sequent L}, OmegaDerivable₂ A I ρ α Γ →
      ∀ {Θ : SecondOrder.Sequent L}, Γ ⊆ (⊥ : Proposition L) :: Θ →
        OmegaDerivable₂ A I ρ α Θ := by
  intro α Γ h
  induction h with
  | @atom α' φ hφ =>
      intro Θ hss
      have hm := hss List.mem_cons_self
      simp only [List.mem_cons] at hm
      rcases hm with hbot | hm
      · exact absurd hbot (Literals₂.ne_falsum hφ)
      · refine .contraction ?_ (.atom hφ)
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rw [hx]; exact hm
  | @identity α' χ =>
      intro Θ hss
      rcases identity_cases hss with ⟨h₁, h₂⟩ | h
      · exact of_mem_identity χ h₁ h₂
      · exact of_mem_verum (by simpa using h)
  | verum =>
      intro Θ hss
      have := hss (show (⊤ : Proposition L) ∈ [(⊤ : Proposition L)] by simp)
      simp only [List.mem_cons] at this
      rcases this with hbot | hm
      · exact absurd hbot (by simp)
      · exact of_mem_verum hm
  | @or α' β' χ ψ Γ' hlt _ ih =>
      intro Θ hss
      have hmem : (χ ⋎ ψ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have key := ih (Θ := χ :: ψ :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · rcases hx with rfl | hx
          · tauto
          · have := hss (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto)
      exact drop_head (.or hlt key) hmem
  | @and α' β' γ' χ ψ Γ' hb hc _ _ ihp ihq =>
      intro Θ hss
      have hmem : (χ ⋏ ψ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have hsub : ∀ ζ : Proposition L, (ζ :: Γ') ⊆ (⊥ : Proposition L) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto
      exact drop_head (.and hb hc (ihp (hsub χ)) (ihq (hsub ψ))) hmem
  | @omegaRule α' χ Γ' f hf _ ih =>
      intro Θ hss
      have hmem : (∀¹ χ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      refine drop_head (.omegaRule f hf (fun n => ih n ?_)) hmem
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · tauto
      · have := hss (List.mem_cons_of_mem _ hx)
        simp only [List.mem_cons] at this
        tauto
  | @exs α' β' χ Γ' n hlt _ ih =>
      intro Θ hss
      have hmem : (∃¹ χ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have key := ih (Θ := I.inst χ n :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto)
      exact drop_head (.exs n hlt key) hmem
  | @all₂ α' β' χ Γ' hlt _ ih =>
      intro Θ hss
      have hmem : (∀² χ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have hss' : Γ' ⊆ (⊥ : Proposition L) :: Θ := fun x hx => hss (List.mem_cons_of_mem _ hx)
      have key := ih (Θ := Semiproposition.free₁ χ :: SecondOrder.Sequent.shift₁ Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := shift₁_subset_falsum hss' hx
          simp only [List.mem_cons] at this
          tauto)
      exact drop_head (.all₂ hlt key) hmem
  | @exs₂ α' β' χ σ Γ' hσ hlt _ ih =>
      intro Θ hss
      have hmem : (∃² χ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have key := ih (Θ := I.inst₂ χ σ :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto)
      exact drop_head (.exs₂ hσ hlt key) hmem
  | contraction ss _ ih =>
      intro Θ hss
      exact ih (fun x hx => hss (ss hx))
  | @cut α' β' γ' χ Γ₁ Γ₂ hc hb1 hb2 _ _ ihp ihn =>
      intro Θ hss
      have kp := ihp (Θ := χ :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_append_left _ hx)
          simp only [List.mem_cons] at this
          tauto)
      have kn := ihn (Θ := ∼χ :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_append_right _ hx)
          simp only [List.mem_cons] at this
          tauto)
      refine .contraction ?_ (.cut hc hb1 hb2 kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto

end OmegaDerivable₂

end OrdinalAnalysis.ACAOmega
