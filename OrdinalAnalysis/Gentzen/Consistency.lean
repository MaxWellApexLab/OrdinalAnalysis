/-
  Consistency of `PA[X]`, as a corollary.

  The lower bound's chain — replay, cut away the axioms, eliminate the cuts —
  applies to a proof of `⊥` just as well as to a proof of `TI(≺)`, and ends in
  a cut-free derivation of the sequent `⊥`, hence of the empty sequent, which
  no rule of the calculus concludes.  This is Gentzen 1936 as a footnote to
  Gentzen 1943; it has been formalized before, in Coq and in Lean, and is
  recorded here only because it falls out.
-/
import OrdinalAnalysis.Gentzen.LowerBound

set_option autoImplicit false

namespace OrdinalAnalysis

open LO LO.FirstOrder

variable {L : Language}

namespace OmegaDerivable

/-- No cut-free derivation has the empty sequent as conclusion. -/
theorem not_derivable_nil {A : Literals L} {I : Instantiation L} :
    ∀ {α : NONote} {Γ : Sequent L}, OmegaDerivable A I 0 α Γ → Γ = [] → False := by
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
theorem not_derivable_falsum {A : Literals L} {I : Instantiation L} {α : NONote}
    (h : OmegaDerivable A I 0 α [(⊥ : Proposition L)]) : False :=
  not_derivable_nil (drop_falsum h (Θ := []) (fun _ hx => by simpa using hx)) rfl

end OmegaDerivable

namespace Gentzen

open OrdinalAnalysis.Gentzen.Evaluate OrdinalAnalysis.Gentzen.LowerBound
open OrdinalAnalysis.Gentzen.Embed OrdinalAnalysis.Gentzen.EvInst

/-- **Consistency of `PA[X]`.** -/
theorem paLX_consistent : paLX ⊬ (⊥ : Sentence LX) := by
  intro hprov
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp hprov
  have hclosed : ∀ φ ∈ (((⊥ : Sentence LX) : Proposition LX) :: ∼Sequent.embed Δ),
      Semiformula.freeVariables φ = ∅ := by
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ
    · simp
    · exact closed_neg_embed Δ φ hφ
  have h₁ := replay_closed (O := NONote) d hclosed
  rw [List.map_cons] at h₁
  have e : ev (((⊥ : Sentence LX) : Proposition LX)) = (⊥ : Proposition LX) := by simp
  rw [e] at h₁
  obtain ⟨r', α', h₂⟩ := cut_axioms Δ hΔ (Θ := [(⊥ : Proposition LX)]) (by simpa using h₁)
  exact OmegaDerivable.not_derivable_falsum (OmegaDerivable.cutElimination r' h₂)

end Gentzen

end OrdinalAnalysis
