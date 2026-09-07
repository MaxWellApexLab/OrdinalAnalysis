/-
  Inversion for the universal quantifier.

  This is the last inversion the reduction lemma needs.  When the cut formula
  is `∀¹ χ`, its negation is `∃¹ (∼χ)`; the existential side supplies a witness
  `t`, and the universal side has to be instantiated there.

  The principal case is the only one that is not bookkeeping: from a premise
  `⊢^β χ.free :: Γ'⁺` one substitutes `&0 ↦ t` and every later free variable
  back down, which turns `χ.free` into `χ/[t]` and undoes the shift on the
  context.  Both facts are Foundation's: `rewrite_free_eq_subst` and
  `rewrite_comp_shift_eq_id`.
-/
import OrdinalAnalysis.Proof.Substitution

namespace OrdinalAnalysis

open LO LO.FirstOrder LO.FirstOrder.Derivation
open LO.FirstOrder.Rewriting LO.FirstOrder.LawfulSyntacticRewriting
open ONote

variable {L : Language}

namespace BoundedDerivable

/-- Substituting the witness into a shifted context restores it. -/
theorem map_rewrite_shifts (t : SyntacticTerm L) (Γ : Sequent L) :
    (Γ⁺).map (Rew.rewrite (t :>ₙ fun x ↦ &x) ▹ ·) = Γ := by
  have key : ∀ φ : Proposition L,
      Rew.rewrite (t :>ₙ fun x ↦ &x) ▹ (Rewriting.shift φ) = φ := by
    intro φ
    have h : (Rew.rewrite (t :>ₙ Semiterm.fvar)).comp Rew.shift = Rew.id :=
      Rew.rewrite_comp_shift_eq_id t
    rw [show Rewriting.shift φ = Rew.shift ▹ φ from rfl,
      ← TransitiveRewriting.comp_app, h]
    simp
  simp only [Rewriting.shifts, List.map_map, Function.comp_def, key]
  exact List.map_id _

/-- The principal case of `∀`-inversion, and the heart of it: a premise of the
`∀` rule can be instantiated at any term.  Everything else in a full inversion
proof is bookkeeping around this step. -/
theorem all_premise_subst {r : ℕ} {α : NONote} {χ : Semiproposition L 1}
    {Γ : Sequent L} (h : BoundedDerivable r α (Semiformula.free χ :: Γ⁺))
    (t : SyntacticTerm L) :
    BoundedDerivable r α (χ/[t] :: Γ) := by
  have key := h.rewrite (t :>ₙ fun x ↦ &x)
  simp only [List.map_cons] at key
  rw [map_rewrite_shifts t Γ] at key
  rw [show (Rew.rewrite (t :>ₙ fun x ↦ &x) ▹ Semiformula.free χ) = χ/[t] from
    rewrite_free_eq_subst t χ] at key
  exact key

end BoundedDerivable

end OrdinalAnalysis
