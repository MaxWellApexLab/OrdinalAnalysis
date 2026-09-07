/-
  Cutting away the negated axioms, generically.

  `LowerBound.cut_axioms` cuts the negated axioms of `paLX` out of a replayed
  derivation one at a time, at heights in `NONote`.  The proof uses nothing
  about `paLX` beyond "every axiom is cut-free derivable at some height", and
  nothing about `NONote` beyond the successor and the natural sum of the
  `OrdinalNotation` class.  This file is that proof with the theory and the
  height system as parameters, so that `|PA + TI(ε₀)| = ε₁` — where the theory
  gains an axiom and the heights leave `ε₀` — can run it unchanged.
-/
import OrdinalAnalysis.Gentzen.EvInst

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.CutAxioms

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.StandardLX (trueArithLits)
open OrdinalAnalysis.Gentzen.Evaluate OrdinalAnalysis.Gentzen.EvInst

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- **Cutting away the negated axioms of a theory `T`**, one at a time, given
that every axiom of `T` is cut-free derivable at some height in `O`. -/
theorem cut_axioms_of (T : Theory LX)
    (hax : ∀ σ ∈ T, ∃ β : O,
      OmegaDerivable trueArithLits evInst 0 β [ev (Rewriting.emb σ : Proposition LX)]) :
    ∀ (Δ : List (Sentence LX)), (∀ σ ∈ Δ, σ ∈ T) → ∀ {r : ℕ} {α : O} {Θ : Sequent LX},
      OmegaDerivable trueArithLits evInst r α (Θ ++ (∼Sequent.embed Δ).map ev) →
      ∃ (r' : ℕ) (α' : O), OmegaDerivable trueArithLits evInst r' α' Θ
  | [], _, r, α, Θ, h => ⟨r, α, by simpa [List.tilde_def] using h⟩
  | σ :: Δ, hΔ, r, α, Θ, h => by
      obtain ⟨β, hσ⟩ := hax σ (hΔ σ (by simp))
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
          (OrdinalNotation.succ (OrdinalNotation.nadd β α)) ([] ++ (Θ ++ rest)) :=
        OmegaDerivable.cut (by omega)
          (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_left _ _))
          (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_right _ _)) hR hL
      exact cut_axioms_of T hax Δ (fun τ hτ => hΔ τ (List.mem_cons_of_mem _ hτ))
        (by simpa using hcut)

end OrdinalAnalysis.Gentzen.CutAxioms
