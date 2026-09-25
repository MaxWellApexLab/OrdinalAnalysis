/-
  The lower bound at `ε₁`, for the *scheme* theory.

  `Epsilon1LowerBound.epsilon1_lower_bound` refutes `TI(≺₁')` over
  `insert TI₀ paLX` — `PA[X]` with transfinite induction below `ε₀` asserted for
  the fresh predicate `X` alone.  The upper bound is proved over the larger
  theory `Epsilon1UpperBound.paLX₁ = paLX ∪ tiScheme₀`, where the induction is
  asserted for *every* formula, and it has to be: with the single `X`-instance
  the upper bound is false (design decision 4).
  A two-sided theorem needs both halves over the same theory, and the larger
  theory is the harder side of the lower bound, so it is the one to prove.

  Nothing in the chain changes.  `CutAxioms.cut_axioms_of` is already generic in
  the theory, and asks only that every axiom be cut-free derivable below `ε₁`;
  `Epsilon1Scheme.scheme_axiom_derivable` supplies that for the new axioms, so
  the proof below is `Epsilon1LowerBound`'s with one case of `hax` replaced.
-/
import OrdinalAnalysis.Gentzen.Epsilon1LowerBound
import OrdinalAnalysis.Gentzen.Epsilon1Scheme

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.Epsilon1LowerBoundScheme

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.StandardLX (trueArithLits)
open OrdinalAnalysis.Gentzen.Evaluate OrdinalAnalysis.Gentzen.EvInst
open OrdinalAnalysis.Gentzen.Embed OrdinalAnalysis.Gentzen.Boundedness
open OrdinalAnalysis.Gentzen.CutAxioms
open OrdinalAnalysis.Gentzen.Epsilon1Order
open OrdinalAnalysis.Gamma0Note

/-- **Every axiom of `paLX ∪ tiScheme₀` is cut-free derivable below `ε₁`.**

The axioms of `paLX` by `LowerBound.paLX_axiom_derivable`, whose `NONote`
height is carried into the Veblen notations by `ofNONote` and lands below
`ε₀ < ε₁`; the scheme axioms by `Epsilon1Scheme.scheme_axiom_derivable`. -/
theorem paLX₁_axiom_derivable (σ : Sentence LX) (h : σ ∈ Epsilon1UpperBound.paLX₁) :
    ∃ β : EpsilonBelow 1,
      OmegaDerivable trueArithLits evInst 0 β [ev (Rewriting.emb σ : Proposition LX)] := by
  rcases h with h | ⟨φ, rfl⟩
  · obtain ⟨β, hd⟩ := LowerBound.paLX_axiom_derivable σ h
    have hd' := hd.map_height ofNONote ofNONote_strictMono
    have hlt : ofNONote β < epsilonNote 1 :=
      (ofNONote_lt_epsilonNote_zero β).trans (epsilon_lt_epsilon Gamma0Note.zero_lt_one)
    exact ⟨Below.mk _ hlt, hd'.toBelow hlt⟩
  · obtain ⟨β, hβ, hd⟩ := Epsilon1Scheme.scheme_axiom_derivable φ
    exact ⟨Below.mk β hβ, hd.toBelow hβ⟩

/-- **The lower bound at `ε₁`, over the scheme theory.**  `PA[X] + TI(≺₁ ↾ ε₀)`
— with the induction asserted for every formula — does not prove `TI(≺₁')`,
transfinite induction along the coded ordering of the notations below `ε₁`. -/
theorem epsilon1_lower_bound_scheme :
    Epsilon1UpperBound.paLX₁ ⊬ (TI Epsilon1Order.epsilon1Order.prec).univCl := by
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
  obtain ⟨r', α', h₂⟩ := cut_axioms_of Epsilon1UpperBound.paLX₁ paLX₁_axiom_derivable Δ hΔ
    (Θ := [ev (TI epsilon1Order.prec)]) (by simpa using h₁)
  exact not_derivable_TI epsilon1Order _ (OmegaDerivable.cutElimination r' h₂)

/-- **Consistency of the scheme theory**, by the same chain. -/
theorem paLX₁_scheme_consistent : Epsilon1UpperBound.paLX₁ ⊬ (⊥ : Sentence LX) := by
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
  obtain ⟨r', α', h₂⟩ := cut_axioms_of Epsilon1UpperBound.paLX₁ paLX₁_axiom_derivable Δ hΔ
    (Θ := [(⊥ : Proposition LX)]) (by simpa using h₁)
  exact OmegaDerivable.not_derivable_falsum' (OmegaDerivable.cutElimination r' h₂)

end OrdinalAnalysis.Gentzen.Epsilon1LowerBoundScheme
