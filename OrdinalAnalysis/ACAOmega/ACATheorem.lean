/-
  **`|ACA| = ε_{ε₀}`, the lower half**.

  This file is the single place the two halves of the `ACA` ordinal analysis are
  meant to meet.  Only the lower half exists today; the upper half is in
  progress elsewhere, and when it lands the two-sided theorem is
  one `⟨_, _⟩` away.

  ### What the lower half says

      aca_lower_bound_statement : ¬ Provable ACA TIsegSO

  `Provable` is `ACA/LK.lean`'s schema-provability in the restricted
  second-order one-sided LK whose `∃₂` rule demands `Arith` — Afshari–Rathjen's
  `ACA_∞` at the finitary level — and `ACA` is `ACA₀` (equality, `PA⁻`, the set
  induction axiom, set extensionality, arithmetical comprehension with arbitrary
  set and number parameters) together with the induction scheme for *every*
  second-order formula, all universally closed.

  `TIsegSO` is `ACA/TI.lean`'s single source of the transfinite-induction
  sentence: `TI(≺, X)` at the free set variable `0`, over the coded Veblen
  ordering **restricted to the notations below `ε_{ε₀}`**
  (`Gentzen/EpsilonSegmentOrder.precCodeSeg (epsilonNote 0)`).  So the statement
  reads: *`ACA` does not prove transfinite induction along `ε_{ε₀}`.*
  `LowerBound₂.TIsegSO_eq` certifies that this is, on the nose, the sentence
  `ACAOmega/Boundedness₂.lean` refutes — the upper and lower halves are about
  one formula, not two.

  ### What the upper half will say

  Transfinite induction along every *proper initial segment* is provable:
  for each `a < ε_{ε₀}`, `Provable ACA (tiUptoSegSO a)` (`ACA/TI.lean`).  The
  two together are the ordinal analysis: `|ACA| = ε_{ε₀}`.

  ### Assembly, when the upper half lands

      theorem aca_theorem :
          (∀ a : Gamma0Note.EpsilonBelow (Gamma0Note.epsilonNote 0),
             Provable ACA (tiUptoSegSO a.val)) ∧ ¬ Provable ACA TIsegSO :=
        ⟨<the upper bound>, aca_lower_bound_statement⟩

  Nothing else has to change here.
-/
import OrdinalAnalysis.ACAOmega.LowerBound₂

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA

namespace ACATheorem

/-- **The lower half of `|ACA| = ε_{ε₀}`.**  `ACA` does not prove transfinite
induction along the coded Veblen ordering of the notations below `ε_{ε₀}`.

Re-exported from `ACAOmega/LowerBound₂.lean` so that the two-sided theorem can
be assembled from this file alone. -/
theorem aca_lower_bound_statement : ¬ Provable ACA TIsegSO :=
  LowerBound₂.aca_lower_bound

/-- **`ACA` is consistent**, by the same chain. -/
theorem aca_consistent_statement : ¬ Provable ACA (⊥ : Proposition ℒₒᵣ) :=
  LowerBound₂.aca_consistent

end ACATheorem

end OrdinalAnalysis.ACAOmega
