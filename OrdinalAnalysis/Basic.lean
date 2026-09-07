/-
  Ordinal analysis, on top of the LK calculus of `FormalizedFormalLogic/Foundation`.

  Foundation proves cut admissibility by Avigad's algebraic route (a canonical
  model). That establishes *that* cut-free derivations exist; it says nothing
  about *how large* they are, so it yields no ordinal bound and no consistency
  proof in Gentzen's sense.

  This development takes the syntactic route instead: assign an ordinal to every
  derivation, show the cut-reduction steps strictly decrease it, and read off
  `|PA| = ε₀`.
-/
import Foundation.FirstOrder.Basic.CutFree
import Mathlib.SetTheory.Ordinal.Notation

namespace OrdinalAnalysis
end OrdinalAnalysis
