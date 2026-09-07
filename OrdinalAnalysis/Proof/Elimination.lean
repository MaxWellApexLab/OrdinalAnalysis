/-
  The elimination lemma: one level of cut rank costs one exponentiation.

  Given a derivation of ordinal height below `α` whose cuts all have complexity
  at most `r`, it produces one of height below `ω ^ α` whose cuts all have
  complexity strictly below `r`.  Iterating it `r` times drives the rank to
  zero, and a rank-zero derivation is cut free.

  The cut case does not split.  A cut admitted at rank `r + 1` has
  `φ.complexity < r + 1`, which is `φ.complexity ≤ r`, which is exactly the
  reduction lemma's hypothesis — so *every* cut is reduced, not only the maximal
  ones, and no case analysis on the rank is needed.

  The ordinal accounting is where `ω ^ α` earns its place.  The two premises
  land at `ω ^ β` and `ω ^ γ` with `β, γ < α`, so both are below `ω ^ α`; the
  reduction lemma returns their doubled natural sum, and `ω ^ α` is additively
  indecomposable for the natural sum, so that is still below `ω ^ α`.  This is
  also the retroactive justification for the reduction lemma's doubling: any
  natural-sum slack is invisible here.
-/
import OrdinalAnalysis.Proof.Reduction
import OrdinalAnalysis.Ordinal.OmegaPow

namespace OrdinalAnalysis

open LO LO.FirstOrder LO.FirstOrder.Derivation

variable {L : Language}

namespace BoundedDerivable

/-- **Elimination.**  One level of cut rank, at the cost of one `ω`-power. -/
theorem elimination {r : ℕ} :
    ∀ {α : NONote} {Γ : Sequent L}, BoundedDerivable (r + 1) α Γ →
      BoundedDerivable r (NONote.omegaPow α) Γ := by
  intro α Γ h
  induction h with
  | identity rl v => exact .identity rl v
  | verum => exact .verum
  | @or α' β' φ ψ Γ' hlt _ ih =>
      exact .or (NONote.omegaPow_lt_omegaPow hlt) ih
  | @and α' β' γ' φ ψ Γ' hb hc _ _ ihp ihq =>
      exact .and (NONote.omegaPow_lt_omegaPow hb)
        (NONote.omegaPow_lt_omegaPow hc) ihp ihq
  | @all α' β' φ Γ' hlt _ ih =>
      exact .all (NONote.omegaPow_lt_omegaPow hlt) ih
  | @exs α' β' φ Γ' t hlt _ ih =>
      exact .exs t (NONote.omegaPow_lt_omegaPow hlt) ih
  | @contraction α' Δ Γ' ss _ ih =>
      exact .contraction ss ih
  | @cut α' β' γ' φ Γ₁ Γ₂ hcomp hb hc _ _ ihp ihn =>
      -- every cut is reduced, whatever its rank: `φ.complexity < r + 1` is
      -- `φ.complexity ≤ r`, which is what the reduction lemma asks for
      have hφ : φ.complexity ≤ r := Nat.lt_succ_iff.mp hcomp
      have hkey := reduction (NONote.omegaPow β') (NONote.omegaPow γ') (Θ := Γ₁ ++ Γ₂) hφ ihp
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr (List.mem_append_left _ hx))
        ihn
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr (List.mem_append_right _ hx))
      exact hkey.mono_ord
        (le_of_lt (NONote.redOrd_lt_omegaPow
          (NONote.omegaPow_lt_omegaPow hb) (NONote.omegaPow_lt_omegaPow hc)))

end BoundedDerivable

end OrdinalAnalysis
