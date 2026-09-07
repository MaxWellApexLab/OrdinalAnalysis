/-
  The lower bound at `ε₁`: `PA[X] + TI(ε₀)` does not prove transfinite
  induction along the coded ordering of the notations below `ε₁`.

  The chain is the one of `LowerBound.lean`, run one level up, with every
  height in `Gamma0Note.EpsilonBelow 1` — the notations below `ε₁`.

  1. A proof of `TI(≺₁')` from `paLX₁` is a one-sided LK derivation of
     `TI(≺₁')` together with the negations of finitely many axioms
     (`provable_iff`).
  2. The replay (`Embed.replay_closed`), generic in the height system, turns
     it into a derivation in the evaluating ω-calculus with heights in
     `EpsilonBelow 1`.
  3. Every axiom of `paLX₁` has a cut-free derivation there: the axioms of
     `paLX` by `LowerBound.paLX_axiom_derivable`, whose `NONote` height is
     carried into the Veblen notations by `ofNONote` and lands below
     `ε₀ < ε₁`; the new axiom `TI₀` by `Epsilon1Axiom.TI₀_derivable`, at
     height `ε₀ + 1 < ε₁`.  `OmegaDerivable.toBelow` restricts each to
     `EpsilonBelow 1`, and `CutAxioms.cut_axioms_of` cuts each negated axiom
     away.
  4. Cut elimination (`OmegaDerivable.cutElimination`), generic in the height
     system, removes the cuts; the height stays a notation below `ε₁`.
  5. Boundedness (`Boundedness.not_derivable_TI epsilon1Order`) says no such
     cut-free derivation of `TI(≺₁')` exists.

  As in the `ε₀` case, `ε₁` enters only through the fact that every height
  produced is a notation below `ε₁`.  Consistency of `paLX₁` falls out of the
  same chain, as `Consistency.lean` records it for `paLX`; the two small
  "no derivation of the empty sequent" lemmas of that file are stated there
  for `NONote` heights, so they are restated here for an arbitrary system.
-/
import OrdinalAnalysis.Gentzen.CutAxioms
import OrdinalAnalysis.Ordinal.BelowDerivation
import OrdinalAnalysis.Gentzen.Epsilon1Axiom
import OrdinalAnalysis.Gentzen.Epsilon1Order
import OrdinalAnalysis.Gentzen.LowerBound

set_option autoImplicit false

namespace OrdinalAnalysis

open LO LO.FirstOrder

/-! ### No derivation of the empty sequent, generically -/

namespace OmegaDerivable

variable {L : Language}
variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- No cut-free derivation has the empty sequent as conclusion.  The `NONote`
statement of `Consistency.lean`, for an arbitrary height system. -/
theorem not_derivable_nil' {A : Literals L} {I : Instantiation L} :
    ∀ {α : O} {Γ : Sequent L}, OmegaDerivable A I 0 α Γ → Γ = [] → False := by
  intro α Γ h
  induction h with
  | atom _ => intro e; exact List.cons_ne_nil _ _ e
  | identity _ _ => intro e; exact List.cons_ne_nil _ _ e
  | verum => intro e; exact List.cons_ne_nil _ _ e
  | or _ _ _ => intro e; exact List.cons_ne_nil _ _ e
  | and _ _ _ _ _ _ => intro e; exact List.cons_ne_nil _ _ e
  | omegaRule _ _ _ _ => intro e; exact List.cons_ne_nil _ _ e
  | exs _ _ _ _ => intro e; exact List.cons_ne_nil _ _ e
  | contraction ss _ ih =>
      intro e
      subst e
      exact ih (List.subset_nil.mp ss)
  | cut hc _ _ _ _ _ _ => exact absurd hc (Nat.not_lt_zero _)

/-- No cut-free derivation of `⊥` alone. -/
theorem not_derivable_falsum' {A : Literals L} {I : Instantiation L} {α : O}
    (h : OmegaDerivable A I 0 α [(⊥ : Proposition L)]) : False :=
  not_derivable_nil' (drop_falsum h (Θ := []) (fun _ hx => by simpa using hx)) rfl

end OmegaDerivable

namespace Gentzen.Epsilon1LowerBound

open LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.StandardLX (trueArithLits)
open OrdinalAnalysis.Gentzen.Evaluate OrdinalAnalysis.Gentzen.EvInst
open OrdinalAnalysis.Gentzen.Embed OrdinalAnalysis.Gentzen.Boundedness
open OrdinalAnalysis.Gentzen.CutAxioms OrdinalAnalysis.Gentzen.Epsilon1Axiom
open OrdinalAnalysis.Gentzen.Epsilon1Order
open OrdinalAnalysis.Gamma0Note

/-- Every axiom of `paLX₁` is cut-free derivable, evaluated, at some height
below `ε₁`. -/
theorem paLX₁_axiom_derivable (σ : Sentence LX) (h : σ ∈ paLX₁) :
    ∃ β : EpsilonBelow 1,
      OmegaDerivable trueArithLits evInst 0 β [ev (Rewriting.emb σ : Proposition LX)] := by
  rcases mem_paLX₁.mp h with rfl | h
  · obtain ⟨β, hβ, hd⟩ := TI₀_derivable
    exact ⟨Below.mk β hβ, hd.toBelow hβ⟩
  · obtain ⟨β, hd⟩ := LowerBound.paLX_axiom_derivable σ h
    have hd' := hd.map_height ofNONote ofNONote_strictMono
    have hlt : ofNONote β < epsilonNote 1 :=
      (ofNONote_lt_epsilonNote_zero β).trans (epsilon_lt_epsilon Gamma0Note.zero_lt_one)
    exact ⟨Below.mk _ hlt, hd'.toBelow hlt⟩

/-- **The lower bound at `ε₁`.**  `PA[X] + TI(ε₀)` does not prove `TI(≺₁')`,
transfinite induction along the coded ordering of the notations below `ε₁`. -/
theorem epsilon1_lower_bound : paLX₁ ⊬ (TI epsilon1Order.prec).univCl := by
  intro hprov
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp hprov
  have hclosed : ∀ φ ∈ (((TI epsilon1Order.prec).univCl : Proposition LX) :: ∼Sequent.embed Δ),
      Semiformula.freeVariables φ = ∅ := by
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ
    · simp
    · exact LowerBound.closed_neg_embed Δ φ hφ
  have h₁ := replay_closed (O := EpsilonBelow 1) d hclosed
  rw [List.map_cons] at h₁
  have e : ev ((TI epsilon1Order.prec).univCl : Proposition LX) = ev (TI epsilon1Order.prec) := by
    rw [Semiformula.coe_univCl_eq_univCl', epsilon1Order.univCl'_TI]
  rw [e] at h₁
  obtain ⟨r', α', h₂⟩ := cut_axioms_of paLX₁ paLX₁_axiom_derivable Δ hΔ
    (Θ := [ev (TI epsilon1Order.prec)]) (by simpa using h₁)
  exact not_derivable_TI epsilon1Order _ (OmegaDerivable.cutElimination r' h₂)

/-- **Consistency of `PA[X] + TI(ε₀)`**, by the same chain. -/
theorem paLX₁_consistent : paLX₁ ⊬ (⊥ : Sentence LX) := by
  intro hprov
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp hprov
  have hclosed : ∀ φ ∈ (((⊥ : Sentence LX) : Proposition LX) :: ∼Sequent.embed Δ),
      Semiformula.freeVariables φ = ∅ := by
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ
    · simp
    · exact LowerBound.closed_neg_embed Δ φ hφ
  have h₁ := replay_closed (O := EpsilonBelow 1) d hclosed
  rw [List.map_cons] at h₁
  have e : ev (((⊥ : Sentence LX) : Proposition LX)) = (⊥ : Proposition LX) := by simp
  rw [e] at h₁
  obtain ⟨r', α', h₂⟩ := cut_axioms_of paLX₁ paLX₁_axiom_derivable Δ hΔ
    (Θ := [(⊥ : Proposition LX)]) (by simpa using h₁)
  exact OmegaDerivable.not_derivable_falsum' (OmegaDerivable.cutElimination r' h₂)

end Gentzen.Epsilon1LowerBound

end OrdinalAnalysis
