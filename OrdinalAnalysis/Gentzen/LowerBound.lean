/-
  The lower bound: `PA[X]` does not prove transfinite induction along the coded
  ordering below `ε₀`.

  The chain is the one Gentzen laid out and Buchholz made exact.

  1. A proof of `TI(≺)` from `paLX` is a one-sided LK derivation of `TI(≺)`
     together with the negations of finitely many axioms (`provable_iff`).
  2. The replay (`Embed.replay_closed`) turns it into a derivation in the
     evaluating ω-calculus, at some cut rank and some height below `ε₀`.
  3. Every axiom of `paLX` has a cut-free derivation in that calculus — the
     equality and `PA⁻` axioms by ω-completeness, the induction instances by
     the chain along the numerals — so each negated axiom is cut away.
  4. Cut elimination (`OmegaDerivable.cutElimination`) removes the cuts; the
     height stays a notation below `ε₀`.
  5. Boundedness (`Boundedness.not_derivable_TI`) says no such cut-free
     derivation of `TI(≺)` exists.

  Nothing in the argument needs the order type of `≺` or the surjectivity of
  the coding: `ε₀` enters only through the fact that every height produced is
  a normal-form notation, and those are exactly the ordinals below `ε₀`.
-/
import OrdinalAnalysis.Gentzen.Embed
import OrdinalAnalysis.Gentzen.AxiomsLogic
import OrdinalAnalysis.Gentzen.AxiomsInduction
import OrdinalAnalysis.Gentzen.Boundedness
import OrdinalAnalysis.Omega.Reduction

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.LowerBound

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen OrdinalAnalysis.Gentzen.StandardLX
open OrdinalAnalysis.Gentzen.LowerSyntax OrdinalAnalysis.Gentzen.Evaluate
open OrdinalAnalysis.Gentzen.EvInst OrdinalAnalysis.Gentzen.Embed
open OrdinalAnalysis.Gentzen.AxiomsLogic OrdinalAnalysis.Gentzen.AxiomsInduction
open OrdinalAnalysis.Gentzen.Boundedness OrdinalAnalysis.Gentzen.CodedNotation

/-- Every axiom of `paLX` is cut-free derivable, evaluated, at some height. -/
theorem paLX_axiom_derivable (σ : Sentence LX) (h : σ ∈ paLX) :
    ∃ β : NONote,
      OmegaDerivable trueArithLits evInst 0 β [ev (Rewriting.emb σ : Proposition LX)] := by
  rcases h with h | h | h
  · exact eq_axiom_derivable σ h
  · exact paMinus_axiom_derivable σ h
  · exact induction_axiom_derivable σ h

/-- Cutting away the negated axioms, one at a time. -/
theorem cut_axioms : ∀ (Δ : List (Sentence LX)), (∀ σ ∈ Δ, σ ∈ paLX) →
    ∀ {r : ℕ} {α : NONote} {Θ : Sequent LX},
      OmegaDerivable trueArithLits evInst r α (Θ ++ (∼Sequent.embed Δ).map ev) →
      ∃ (r' : ℕ) (α' : NONote), OmegaDerivable trueArithLits evInst r' α' Θ
  | [], _, r, α, Θ, h => ⟨r, α, by simpa [List.tilde_def] using h⟩
  | σ :: Δ, hΔ, r, α, Θ, h => by
      obtain ⟨β, hσ⟩ := paLX_axiom_derivable σ (hΔ σ (by simp))
      set φ : Proposition LX := ev (Rewriting.emb σ : Proposition LX) with hφ
      set rest : Sequent LX := (∼Sequent.embed Δ).map ev with hrest
      have h' : OmegaDerivable trueArithLits evInst r α (Θ ++ ((∼φ) :: rest)) := by
        have e : (∼Sequent.embed (σ :: Δ)).map ev = (∼φ) :: rest := by
          simp only [Sequent.embed_cons, List.tilde_def, List.map_cons, hφ, hrest, ev_neg]
        rw [← e]
        exact h
      set r' : ℕ := max r (φ.complexity + 1) with hr'
      have hL : OmegaDerivable trueArithLits evInst r' α ((∼φ) :: (Θ ++ rest)) := by
        refine OmegaDerivable.contraction ?_ (h'.mono_rank (le_max_left _ _))
        intro x hx
        simp only [List.mem_append, List.mem_cons] at hx ⊢
        tauto
      have hR : OmegaDerivable trueArithLits evInst r' β (φ :: []) :=
        hσ.mono_rank (Nat.zero_le _)
      have hcut : OmegaDerivable trueArithLits evInst r'
          (NONote.succ (NONote.nadd β α)) ([] ++ (Θ ++ rest)) :=
        OmegaDerivable.cut (by omega)
          (NONote.lt_succ_of_le (NONote.le_nadd_left _ _))
          (NONote.lt_succ_of_le (NONote.le_nadd_right _ _)) hR hL
      exact cut_axioms Δ (fun τ hτ => hΔ τ (List.mem_cons_of_mem _ hτ)) (by simpa using hcut)

/-- The negated axioms are closed formulas. -/
theorem closed_neg_embed (Δ : List (Sentence LX)) :
    ∀ φ ∈ (∼Sequent.embed Δ : Sequent LX), Semiformula.freeVariables φ = ∅ := by
  intro φ hφ
  rw [List.tilde_def, Sequent.embed, List.map_map] at hφ
  obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hφ
  simp

/-- **The lower bound.**  `PA[X]` does not prove `TI(≺)`. -/
theorem gentzen_lower_bound : paLX ⊬ (TI precCode).univCl := by
  intro hprov
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp hprov
  have hclosed : ∀ φ ∈ (((TI precCode).univCl : Proposition LX) :: ∼Sequent.embed Δ),
      Semiformula.freeVariables φ = ∅ := by
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ
    · simp
    · exact closed_neg_embed Δ φ hφ
  have h₁ := replay_closed (O := NONote) d hclosed
  rw [List.map_cons] at h₁
  have e : ev ((TI precCode).univCl : Proposition LX) = ev (TI precCode) := by
    rw [Semiformula.coe_univCl_eq_univCl',
      Semiformula.univCl'_eq_self_of _ freeVariables_TI_precCode]
  rw [e] at h₁
  obtain ⟨r', α', h₂⟩ := cut_axioms Δ hΔ (Θ := [ev (TI precCode)]) (by simpa using h₁)
  exact not_derivable_TI epsilon0Order _ (OmegaDerivable.cutElimination r' h₂)

end OrdinalAnalysis.Gentzen.LowerBound
