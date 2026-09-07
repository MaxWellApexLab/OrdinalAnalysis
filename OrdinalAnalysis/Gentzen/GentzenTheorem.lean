/-
  Gentzen's theorem: the proof-theoretic ordinal of Peano arithmetic is `ε₀`.

  Two halves, one language.  `paLX` is Peano arithmetic in the language with a
  fresh unary predicate `X`: the equality axioms, the axioms of `PA⁻`, and the
  induction scheme for every formula, `X` included.  `≺` is the coded ordering
  on the normal-form notations below `ε₀` (`precCode`), definable in the
  language of arithmetic.

  * **Upper bound** (Gentzen 1943): for every notation `a`, `paLX` proves
    transfinite induction along `≺` up to `a`.
  * **Lower bound** (Gentzen 1943, made exact by Buchholz): `paLX` does not
    prove transfinite induction along the whole of `≺`.

  Together: `ε₀` is exactly the supremum of the orderings `PA` proves well
  founded, and `|PA| = ε₀`.
-/
import OrdinalAnalysis.Gentzen.UpperBound
import OrdinalAnalysis.Gentzen.LowerBound

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen

open LO LO.FirstOrder
open OrdinalAnalysis.Gentzen.UpperBound OrdinalAnalysis.Gentzen.OmegaTower
open OrdinalAnalysis.Gentzen.NotationBridge OrdinalAnalysis.Gentzen.CodedNotation
open OrdinalAnalysis.Gentzen.Order OrdinalAnalysis.Gentzen.InternalONote

/-- **Gentzen's theorem.**  `paLX` proves transfinite induction along `≺` below
every notation, and does not prove it along all of `≺`. -/
theorem gentzen_theorem :
    (∀ (φ : Semiformula LX ℕ 1) (a : ONote) (ha : ONote.NF a),
        paLX ⊢ closedTI φ (notationTerm ⟨a, ha⟩)) ∧
      paLX ⊬ (TI CodedNotation.precCode).univCl :=
  ⟨fun φ a ha => gentzen_upper_bound φ a ha, LowerBound.gentzen_lower_bound⟩

end OrdinalAnalysis.Gentzen
