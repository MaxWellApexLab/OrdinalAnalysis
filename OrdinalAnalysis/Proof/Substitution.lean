/-
  Derivations are closed under substitution of free variables, at the same
  ordinal and the same cut rank.

  This is the prerequisite for inverting the `∀` rule: the reduction lemma
  takes the witness `t` from the `∃` side and needs the `∀` side instantiated
  at `t`.

  The proof mirrors Foundation's `Derivation.rewrite` for concrete derivations.
  Two things are forced.  The substitution must be quantified *inside* the
  induction, because the `∀` case applies the induction hypothesis at a
  different substitution `g`.  And the cut case needs
  `Semiformula.complexity_rew`: substitution does not change the complexity of
  a formula, so the rank side condition survives.
-/
import OrdinalAnalysis.Proof.Weakening

namespace OrdinalAnalysis

open LO LO.FirstOrder LO.FirstOrder.Derivation
open LO.FirstOrder.Rewriting LO.FirstOrder.LawfulSyntacticRewriting
open ONote

variable {L : Language}

namespace BoundedDerivable

theorem rewrite {r : ℕ} :
    ∀ {α : NONote} {Γ : Sequent L}, BoundedDerivable r α Γ →
      ∀ (f : ℕ → SyntacticTerm L),
        BoundedDerivable r α (Γ.map (Rew.rewrite f ▹ ·)) := by
  intro α Γ h
  induction h with
  | identity rl v =>
      intro f
      simpa using BoundedDerivable.identity (α := _) rl (Rew.rewrite f ∘ v)
  | verum =>
      intro f
      simpa using BoundedDerivable.verum (α := _)
  | @or α β χ ρ Γ' hlt _ ih =>
      intro f
      have key := ih f
      simp only [List.map_cons] at key ⊢
      exact BoundedDerivable.or hlt key
  | @and α β γ χ ρ Γ' hβ hγ _ _ ihp ihq =>
      intro f
      have kp := ihp f
      have kq := ihq f
      simp only [List.map_cons] at kp kq ⊢
      exact BoundedDerivable.and hβ hγ kp kq
  | @exs α β χ Γ' t hlt _ ih =>
      intro f
      have key := ih f
      simp only [List.map_cons] at key ⊢
      refine BoundedDerivable.exs (Rew.rewrite f t) hlt ?_
      simp only [rewrite_subst_eq, Rew.q_rewrite, Function.comp_def] at key ⊢
      exact key
  | @contraction α Δ Γ' ss _ ih =>
      intro f
      exact BoundedDerivable.contraction (List.map_subset _ ss) (ih f)
  | @cut α β γ χ Γ₁ Γ₂ hc hβ hγ _ _ ihp ihn =>
      intro f
      have kp := ihp f
      have kn := ihn f
      simp only [List.map_cons, List.map_append] at kp kn ⊢
      refine BoundedDerivable.cut (φ := Rew.rewrite f ▹ χ) ?_ hβ hγ kp ?_
      · simpa using hc
      · simpa using kn
  | @all α β χ Γ' hlt _ ih =>
      intro f
      have key := ih (&0 :>ₙ fun x ↦ Rew.shift (f x))
      simp only [List.map_cons] at key ⊢
      refine BoundedDerivable.all hlt ?_
      simp only [Rewriting.shifts, shift_rewrite_eq,
        Function.comp_def, Rew.q_rewrite, List.map_map] at key ⊢
      have e : (Semiformula.rewAux (Rew.rewrite fun x ↦ Rew.bShift (f x)) χ).free
          = (Rew.rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x))) ▹ Semiformula.free χ :=
        free_rewrite_eq f χ
      rw [e]
      exact key

/-- Shifting the whole context preserves derivability.  Needed by the `∀` case of
the reduction lemma: that rule shifts its context, so the cut formula has to be
shifted along with it.

Foundation defines `Derivation.shift` the same way, as `rewrite` at
`fun x ↦ &(x+1)`; `Γ.map (Rew.rewriteMap Nat.succ ▹ ·)` is `Γ⁺` definitionally. -/
theorem shift {r : ℕ} {α : NONote} {Γ : Sequent L} (h : BoundedDerivable r α Γ) :
    BoundedDerivable r α Γ⁺ :=
  h.rewrite (fun x => &(Nat.succ x))

end BoundedDerivable

end OrdinalAnalysis
