/-
  **`|ACA + TI(<Γ₀)| = Γ₀`**.

  ## What is proved here, and what is not

  **The content of this file is the non-provability half.**  For every notation
  `a : Gamma0Note` the theory `ACAΓ = ACA + TI(<Γ₀)` proves transfinite induction
  along the coded Veblen ordering `≺₁` *below `ā`* — that is one of its axioms,
  so `gamma0_upper_bound` is `Toolkit.ofAxiom` and nothing more.  What is a
  theorem is the other half: adding all of those axioms does **not** let the
  theory prove transfinite induction along the *whole* of `≺₁`
  (`gamma0_lower_bound`).  In other words the new axioms do not bootstrap past
  `Γ₀`, which is exactly the ordinal-analytic content of the equality.

  **This is `|ACA + TI(<Γ₀)| = Γ₀` in the Avigad family sense.**  It is *not*
  `|ATR₀| = Γ₀`, and it is *not* the Feferman–Schütte theorem: neither `ATR₀` nor
  ramified analysis appears anywhere in this development, and no predicative
  cut elimination is performed (the cut elimination used is the same `ε`-jump
  `ACAOmega/SecondCut.lean` uses for `|ACA| = ε_{ε₀}`).  The reason `Γ₀` appears
  at all is that `Γ₀` is the closure ordinal of the notation system the heights
  live in, and `ACAOmega/Boundedness₂.lean`'s `not_derivable_TI₂` is generic in
  the coded order.

  Likewise, the scheme `ACAΓ` adds is restricted to **arithmetical** induction
  formulas (with arbitrary number and set parameters).  `ACA/TIGamma.lean`'s
  header explains why that is forced by the `(∃₂)` side condition of `ACA_∞`, and
  why it costs nothing: `∀X (Prog(≺₁, X) → ∀ x ≺₁ ā, x ∈ X)` — the textbook
  `TI(< ā)` — is itself one of the instances (`ACA.tiUptoSet`).

  ## The chain

  All of it in `O := Gamma0Note`; **no `Below` is needed**, because
  `not_derivable_TI₂_gamma0` refutes the conclusion at *every* notation, not
  merely below some bound.  That is the one structural simplification over
  `ACAOmega/LowerBound₂.lean`, whose `ε_{ε₀}` target forced the whole replay into
  `Below ε₀`.

      Provable ACAΓ (TI₂ ≺₁)
        →  provable_iff                a finitary derivation of `TI₂ ≺₁ :: ∼axioms`
        →  replay₂_closed              an `ACA_∞`-derivation of the same sequent,
                                       evaluated, at rank `cutRank₂ d`
        →  cut_axioms₂_of ACAΓ         the negated axioms cut away, at rank `ω + K`
             with `AxiomsTI₂.acaΓ_axiom_derivable`
        →  cutElimination_omegaAdd_ev  cut free, at height `ε_{ω_K(α)} : Gamma0Note`
        →  not_derivable_TI₂_gamma0    contradiction.

  Contents.

    `shift₀_TI₂_gamma0`, `numClosed₂_TI₂_gamma0`   the closedness of the target
    `numClosed₂_neg_of_mem_ACAΓ`                   the closedness of the axioms
    `gamma0_lower_bound`    **`ACAΓ ⊬ TI(≺₁, X)`**
    `gamma0_upper_bound`    `ACAΓ ⊢ ∀X TIupto(≺₁, ā, X)` — an axiom
    `acaΓ_consistent`       `ACAΓ ⊬ ⊥`
    `gamma0_theorem`        **the two halves together**
-/
import OrdinalAnalysis.ACAOmega.AxiomsTI₂
import OrdinalAnalysis.ACAOmega.RankBound
import OrdinalAnalysis.ACAOmega.Embed₂
import OrdinalAnalysis.ACAOmega.LowerBound₂
import OrdinalAnalysis.ACA.Toolkit

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA
open OrdinalAnalysis.ACAOmega.NumSubst₂
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)

namespace Gamma0Theorem

/-! ### The target sentence has no free number variable

`TI₂ gamma0Order₂.prec` is built from the lifted, closed ordering `precFO₁` and
the free set variable's atom, so no number variable is free in it.  The one step
that is not `simp` is the ordering itself, and `ACA/TIGamma.lean`'s
`shift₀_precG` has already done it. -/

section Closed

variable {O : Type} [LinearOrder O] (C : CodedOrder₂ O)

/-- **A comparison of two closed terms in a coded ordering has no free number
variable.**  The ordering is a lift of a closed first-order formula, so the
substituted formula is closed and `Rew.shift` — which moves only free
variables — fixes it. -/
theorem shift₀_precAt₂_of {n : ℕ} {y x : FirstOrder.Semiterm ℒₒᵣ ℕ n}
    (hy : y.freeVariables = ∅) (hx : x.freeVariables = ∅) :
    Semiproposition.shift₀ (precAt₂ C.prec y x) = precAt₂ C.prec y x := by
  have hc : precAt₂ C.prec y x
      = lift ((FirstOrder.Rew.subst ![y, x] : FirstOrder.Rew ℒₒᵣ ℕ 2 ℕ n) ▹ C.prec₀) := by
    rw [precAt₂, C.prec_eq, lift_rew]
  rw [hc]
  show (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) ▹ (lift _) = lift _
  rw [← lift_rew]
  congr 1
  refine FirstOrder.Semiformula.rew_eq_self_of (by simp) (fun z hz => ?_)
  rw [FirstOrder.Semiformula.FVar?,
    Gentzen.LowerSyntax.freeVariables_rew_eq_empty _ C.freeVariables_prec₀
      (Fin.forall_fin_two.mpr ⟨by simpa using hy, by simpa using hx⟩)] at hz
  simp at hz

theorem shift₀_below₂_of :
    Semiproposition.shift₀ (below₂ C.prec) = below₂ C.prec := by
  have hp : (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 2 ℕ 2) ▹
      (precAt₂ C.prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) #1)
      = precAt₂ C.prec #0 #1 := shift₀_precAt₂_of C (by simp) (by simp)
  show (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1) ▹ (below₂ C.prec) = _
  rw [below₂, Semiformula.rew_all₀, FirstOrder.Rew.q_shift,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, hp,
    Semiformula.rew_fvar]
  simp

theorem shift₀_Prog₂_of :
    Semiproposition.shift₀ (Prog₂ C.prec) = Prog₂ C.prec := by
  have hb : (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1) ▹
      (below₂ C.prec) = below₂ C.prec := shift₀_below₂_of C
  show (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹ (Prog₂ C.prec) = _
  rw [Prog₂, Semiformula.rew_all₀, FirstOrder.Rew.q_shift,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, hb,
    Semiformula.rew_fvar]
  simp

theorem shift₀_TI₂_of : Semiproposition.shift₀ (TI₂ C.prec) = TI₂ C.prec := by
  have hp : (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹
      (Prog₂ C.prec) = Prog₂ C.prec := shift₀_Prog₂_of C
  show (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹ (TI₂ C.prec) = _
  rw [TI₂, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, hp,
    Semiformula.rew_all₀, FirstOrder.Rew.q_shift, Semiformula.rew_fvar]
  simp

/-- **The transfinite-induction sentence of a coded ordering is `NumClosed₂`**,
which is what `replay₂_closed` asks of every member of the replayed sequent. -/
theorem numClosed₂_TI₂_of : NumClosed₂ (TI₂ C.prec) :=
  LowerBound₂.numClosed₂_of_shift₀ (shift₀_TI₂_of C)

end Closed

theorem shift₀_TI₂_gamma0 :
    Semiproposition.shift₀ (TI₂ gamma0Order₂.prec) = TI₂ gamma0Order₂.prec :=
  shift₀_TI₂_of gamma0Order₂

theorem numClosed₂_TI₂_gamma0 : NumClosed₂ (TI₂ gamma0Order₂.prec) :=
  numClosed₂_TI₂_of gamma0Order₂

/-- Every axiom of `ACAΓ` is `NumClosed₂`, and so is its negation. -/
theorem numClosed₂_neg_of_mem_ACAΓ {σ : Proposition ℒₒᵣ} (h : σ ∈ ACAΓ) :
    NumClosed₂ (∼σ) := by
  refine LowerBound₂.numClosed₂_of_shift₀ ?_
  show (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹ (∼σ) = ∼σ
  rw [LogicalConnective.HomClass.map_neg]
  exact congrArg (∼·) (ACAΓ_shift₀_invariant σ h)

/-! ### The lower bound -/

/-- **`ACA + TI(<Γ₀)` does not prove transfinite induction along the coded
Veblen ordering `≺₁`.**  The non-provability half of `|ACA + TI(<Γ₀)| = Γ₀`; see
the module docstring for what that does and does not mean. -/
theorem gamma0_lower_bound : ¬ Provable ACAΓ (TI₂ gamma0Order₂.prec) := by
  intro hprov
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := provable_iff.mp hprov
  -- every member of the replayed sequent has no free number variable
  have hclosed : ∀ φ ∈ (TI₂ gamma0Order₂.prec :: ∼Δ), NumClosed₂ φ := by
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact numClosed₂_TI₂_gamma0
    · have hφ' : φ ∈ Δ.map (∼·) := hφ
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hφ'
      exact numClosed₂_neg_of_mem_ACAΓ (hΔ σ hσ)
  -- replay, at heights in `Gamma0Note` itself: every notation is below `Γ₀`
  have h₁ := Embed₂.replay₂_closed (O := Gamma0Note) d hclosed
  rw [List.map_cons] at h₁
  -- a common rank bound `ω + K` for the derivation's cuts and the axioms
  obtain ⟨k₁, hk₁⟩ := LowerBound₂.exists_omegaAdd_cutRank d
  obtain ⟨k₂, hk₂⟩ := OmegaDerivable₂.exists_omegaAdd_bound Δ
  have hρ : cutRank₂ d ≤ OmegaDerivable₂.omegaAdd (max k₁ k₂) :=
    le_trans hk₁ (OmegaDerivable₂.omegaAdd_le_omegaAdd (le_max_left _ _))
  have hrk : ∀ σ ∈ Δ, rank (ev₂ σ) < OmegaDerivable₂.omegaAdd (max k₁ k₂) := fun σ hσ =>
    lt_of_lt_of_le (hk₂ σ hσ) (OmegaDerivable₂.omegaAdd_le_omegaAdd (le_max_right _ _))
  -- cut the negated axioms away
  obtain ⟨α, h₂⟩ := Axioms₂.cut_axioms₂_of ACAΓ (OmegaDerivable₂.omegaAdd (max k₁ k₂))
    AxiomsTI₂.acaΓ_axiom_derivable Δ hΔ hrk hρ (Θ := [ev₂ (TI₂ gamma0Order₂.prec)])
    (by simpa using h₁)
  -- the second cut elimination, and boundedness
  have h₃ := OmegaDerivable₂.cutElimination_omegaAdd_ev (max k₁ k₂) h₂
  exact not_derivable_TI₂_gamma0 _ h₃

/-! ### The upper bound

An axiom is provable.  There is nothing else to say: the provability half of
`|ACA + TI(<Γ₀)| = Γ₀` is *assumed*, not derived — that is what "adding
`TI(<Γ₀)` as an axiom scheme" means. -/

/-- **`ACA + TI(<Γ₀)` proves `∀X (Prog(≺₁, X) → ∀ x ≺₁ ā, x ∈ X)`, for every
notation `a`.**  It is an axiom. -/
theorem gamma0_upper_bound (a : Gamma0Note) : Provable ACAΓ (tiUptoSet a) :=
  ofAxiom (tiUptoSet_mem_ACAΓ a)

/-- The same for every arithmetical formula with parameters. -/
theorem gamma0_upper_bound_scheme {N n : ℕ} (a : Gamma0Note)
    {ψ : Semiproposition ℒₒᵣ N (n + 1)} (hψ : Arith ψ) (hns : NoSetFvar ψ)
    (h0 : Semiproposition.shift₀ ψ = ψ) : Provable ACAΓ (tiUptoScheme a ψ) :=
  ofAxiom (tiUptoScheme_mem_ACAΓ a hψ hns h0)

/-- The parameter-free instance, in the shape `ACAOmega/SubstX₂.lean` produces:
`TIupto(≺₁, ā, ψ)`. -/
theorem gamma0_upper_bound_zero (a : Gamma0Note) {ψ : Semiproposition ℒₒᵣ 0 1}
    (hψ : Arith ψ) (hns : NoSetFvar ψ) (h0 : Semiproposition.shift₀ ψ = ψ) :
    Provable ACAΓ (TIuptoψ₂ gamma0Order₂.prec ψ (numAt (gamma0Code a))) := by
  rw [← tiUptoScheme_zero]
  exact gamma0_upper_bound_scheme a hψ hns h0

/-! ### The upper bound at the free set variable

`gamma0_upper_bound` is stated with the set quantifier bound; specialising it
back to the *free* set variable `0` — by `Toolkit.spec₂` at the arithmetical
witness `x ∈ X₀` — puts the two halves of the theorem in exactly the same
syntactic shape: `TIupto₂ ≺₁ ā` is provable for every `a`, `TI₂ ≺₁` is not. -/

/-- The witness recovering the free set variable `0`. -/
def xWitness : Semiformula ℒₒᵣ ℕ ℕ 0 1 := ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& (0 : ℕ))

theorem arith_xWitness : Arith xWitness := trivial

/-- Specialising the set quantifier at `xWitness` undoes the binding of
`memSlot`. -/
theorem app_memSlot {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    (SecondOrder.Rew.subst ![xWitness]).app
        ((t ∈# (0 : Fin 1)) : Semiproposition ℒₒᵣ 1 n)
      = (t ∈& (0 : ℕ)) := by
  rw [SecondOrder.Rew.app_bvar]
  show (xWitness)/[t] = _
  simp [xWitness]

theorem app_precG {n : ℕ} (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    (SecondOrder.Rew.subst ![xWitness]).app (precG y x : Semiproposition ℒₒᵣ 1 n)
      = precAt₂ gamma0Order₂.prec y x := by
  rw [← precG_zero]
  exact AxiomsTI₂.app_lift _ _

theorem app_belowG :
    (SecondOrder.Rew.subst ![xWitness]).app (belowG memSlot) = below₂ gamma0Order₂.prec := by
  rw [belowG, SecondOrder.Rew.app_all₀, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, app_precG, SecondOrder.Rew.app_comm_subst, memSlot,
    app_memSlot, below₂]
  simp [belowSub]

theorem app_progG :
    (SecondOrder.Rew.subst ![xWitness]).app (progG memSlot) = Prog₂ gamma0Order₂.prec := by
  rw [progG, SecondOrder.Rew.app_all₀, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, app_belowG, memSlot, app_memSlot, Prog₂]

theorem app_tiUptoBody (c : ℕ) :
    (SecondOrder.Rew.subst ![xWitness]).app
        (tiUptoBody (numAt c : FirstOrder.SyntacticTerm ℒₒᵣ) memSlot)
      = TIupto₂ gamma0Order₂.prec (numAt c) := by
  rw [tiUptoBody, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    app_progG, SecondOrder.Rew.app_comm_subst, app_belowG, atSub_zero_eq, TIupto₂_eq]

/-- **`ACA + TI(<Γ₀)` proves `Prog(≺₁, X) → ∀ x ≺₁ ā, x ∈ X`** at the *free* set
variable, for every notation `a`.  One specialisation of the axiom. -/
theorem gamma0_upper_bound_X (a : Gamma0Note) :
    Provable ACAΓ (TIupto₂ gamma0Order₂.prec (numAt (gamma0Code a))) := by
  have h : Provable ACAΓ (∀² (tiUptoBody
      (numAt (gamma0Code a) : FirstOrder.SyntacticTerm ℒₒᵣ) memSlot)) :=
    gamma0_upper_bound a
  have hs := spec₂ h arith_xWitness
  rwa [show (tiUptoBody (numAt (gamma0Code a) : FirstOrder.SyntacticTerm ℒₒᵣ)
      memSlot)/⟦xWitness⟧ = TIupto₂ gamma0Order₂.prec (numAt (gamma0Code a)) from
    app_tiUptoBody _] at hs

/-! ### Consistency, and the two halves together -/

/-- **`ACA + TI(<Γ₀)` is consistent.**  From `⊥` everything follows, the
transfinite-induction sentence included, so this is `gamma0_lower_bound` and one
cut. -/
theorem acaΓ_consistent : ¬ Provable ACAΓ (⊥ : Proposition ℒₒᵣ) := by
  intro h
  refine gamma0_lower_bound ?_
  obtain ⟨Γ, hΓ, ⟨d⟩⟩ := provable_iff.mp h
  refine provable_iff.mpr ⟨Γ, hΓ, ⟨?_⟩⟩
  refine ACA.Derivation.cut (φ := ⊥) (d.wk ?_) (ACA.Derivation.wk ACA.Derivation.verum ?_)
  · intro x hx
    simp only [List.mem_cons] at hx ⊢
    tauto
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp only [List.mem_cons]
    left
    rfl

/-- **`|ACA + TI(<Γ₀)| = Γ₀`, in the form the station states it.**  For the one
free set variable `X` and the one ordering `≺₁`: transfinite induction below
every single notation `ā` is available, and transfinite induction along all of
`≺₁` is not. -/
theorem gamma0_theorem :
    (∀ a : Gamma0Note, Provable ACAΓ (TIupto₂ gamma0Order₂.prec (numAt (gamma0Code a)))) ∧
      ¬ Provable ACAΓ (TI₂ gamma0Order₂.prec) :=
  ⟨gamma0_upper_bound_X, gamma0_lower_bound⟩

/-- The same with the set quantifier bound, which is how `TI(< ā)` is usually
written. -/
theorem gamma0_theorem_set :
    (∀ a : Gamma0Note, Provable ACAΓ (tiUptoSet a)) ∧
      ¬ Provable ACAΓ (TI₂ gamma0Order₂.prec) :=
  ⟨gamma0_upper_bound, gamma0_lower_bound⟩

end Gamma0Theorem

end OrdinalAnalysis.ACAOmega
