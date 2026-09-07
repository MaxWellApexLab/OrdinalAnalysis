/-
  The replay of finitary derivations in the infinitary calculus.

  Every derivation of Foundation's one-sided LK becomes a derivation in the
  evaluating ω-calculus, at the same cut rank and the same ordinal height, of
  every numeral instance of its sequent — the free variable `x` sent to the
  numeral `f x`, every ground term then replaced by the numeral of its value.

  The statement is proved for all assignments `f` at once; that is what makes
  it an induction.  The cut rule may introduce a formula with free variables
  the conclusion does not have, so "closed" is not an invariant of the
  derivation, but "instantiated by `f`" is.  The two quantifier rules are the
  content.

  * `all` introduces a fresh free variable; the ω-rule asks for every numeral
    instance.  The premise under `n :>ₙ f` is the `n`-th instance of the
    conclusion's body under `f` (`NumSubst.numSubst_free`), the shifted context
    is unaffected (`seqSubst_shifts`), and the premise's evaluated form is the
    instance the ω-rule wants because evaluating the body first changes
    nothing (`EvInst.evInst_inst_ev`).

  * `exs` may use any term as witness; the ω-calculus only a numeral.  After
    the assignment the witness is a ground term, and the evaluator turns
    substitution by a ground term into substitution by the numeral of its
    value (`Evaluate.ev_subst_ground`).  This is the point of evaluating:
    without it the calculus could not replay an existential inference whose
    witness is compound, having no equality reasoning about `X`.

  Ordinals and ranks are `Proof/Bridge.ordN` and `Proof/CutRank.cutRank`,
  exactly as for the finitary indexed calculus.  The heights are an arbitrary
  `[OrdinalNotation O]`, matching `Omega/Calculus.lean` and `Proof/Bridge.ordN`:
  the replay is what carries a finitary proof into the infinitary calculus, and
  the results above `ε₀` need it to land in a notation system larger than
  `NONote`.  Every ordinal step it takes — `lt_succ`, `lt_succ_of_le`,
  `le_nadd_left`, `le_nadd_right` — is a lemma of the class.
-/
import OrdinalAnalysis.Proof.Bridge
import OrdinalAnalysis.Gentzen.EvInst
import OrdinalAnalysis.Gentzen.NumSubst

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.Embed

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen OrdinalAnalysis.Gentzen.StandardLX
open OrdinalAnalysis.Gentzen.Evaluate OrdinalAnalysis.Gentzen.NumSubst
open OrdinalAnalysis.Gentzen.EvInst

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- **The replay.**  An LK derivation of `Γ` yields, for every assignment `f`,
an ω-derivation of the evaluated `f`-instance of `Γ`, at the same rank and
height. -/
theorem replay : ∀ {Γ : Sequent LX} (d : ⊢ᴸᴷ¹ Γ) (f : ℕ → ℕ),
    OmegaDerivable trueArithLits evInst (cutRank d) (ordN d : O) ((seqSubst f Γ).map ev)
  | _, Derivation.identity rl v, f => by
      simp only [seqSubst_cons, seqSubst_nil, List.map_cons, List.map_nil,
        Semiformula.rew_rel, Semiformula.rew_nrel, ev_rel, ev_nrel]
      exact OmegaDerivable.identity _ _
  | _, Derivation.verum, f => by
      simpa using OmegaDerivable.verum
  | _, Derivation.contraction d ss, f =>
      OmegaDerivable.contraction (List.map_subset _ (seqSubst_subset ss)) (replay d f)
  | _, Derivation.or d, f => by
      have h := replay d f
      simp only [seqSubst_cons, List.map_cons] at h ⊢
      simp only [LogicalConnective.HomClass.map_or, ev_or]
      exact OmegaDerivable.or (OrdinalNotation.lt_succ _) (h.mono_rank (by simp [cutRank]))
  | _, Derivation.and dp dq, f => by
      have hp := replay dp f
      have hq := replay dq f
      simp only [seqSubst_cons, List.map_cons] at hp hq ⊢
      simp only [LogicalConnective.HomClass.map_and, ev_and]
      exact OmegaDerivable.and (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_left _ _))
        (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_right _ _))
        (hp.mono_rank (by simp [cutRank])) (hq.mono_rank (by simp [cutRank]))
  | _, Derivation.cut dp dn, f => by
      have hp := replay dp f
      have hn := replay dn f
      simp only [seqSubst_cons, List.map_cons] at hp hn
      simp only [LogicalConnective.HomClass.map_neg, ev_neg] at hn
      simp only [seqSubst_append, List.map_append]
      refine OmegaDerivable.cut ?_ (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_left _ _))
        (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_right _ _))
        (hp.mono_rank (by simp [cutRank])) (hn.mono_rank (by simp [cutRank]))
      simp only [cutRank, Semiformula.complexity_rew, complexity_ev]
      omega
  | _, Derivation.all d, f => by
      simp only [seqSubst_cons, List.map_cons, numSubst_all, ev_all]
      refine OmegaDerivable.omegaRule (fun _ => (ordN d : O))
        (fun _ => OrdinalNotation.lt_succ _)
        (fun n => ?_)
      have h := replay d (n :>ₙ f)
      simp only [seqSubst_cons, List.map_cons, seqSubst_shifts, numSubst_free] at h
      rw [evInst_inst_ev]
      exact h.mono_rank (by simp [cutRank])
  | _, Derivation.exs d, f => by
      rename_i φ t Γ
      have h := replay d f
      simp only [seqSubst_cons, List.map_cons, numSubst_subst] at h
      simp only [seqSubst_cons, List.map_cons, numSubst_exs, ev_exs]
      refine OmegaDerivable.exs (evTerm (numSubst f t)) (OrdinalNotation.lt_succ _) ?_
      rw [evInst_inst_ev,
        ← ev_subst_ground (ground_of_closed (freeVariables_numSubst_term f t))]
      exact h.mono_rank (by simp [cutRank])

/-- **The replay of a closed sequent** is a derivation of its evaluation. -/
theorem replay_closed {Γ : Sequent LX} (d : ⊢ᴸᴷ¹ Γ)
    (hc : ∀ φ ∈ Γ, Semiformula.freeVariables φ = ∅) :
    OmegaDerivable trueArithLits evInst (cutRank d) (ordN d : O) (Γ.map ev) := by
  have h := replay (O := O) d (fun _ => 0)
  rwa [seqSubst_eq_self hc] at h

end OrdinalAnalysis.Gentzen.Embed
