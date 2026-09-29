/-
  **`CollapseHyps A` from positivity alone.**  `IDw/Collapsing/Theorem.lean`'s
  `collapseHyps_of` takes `positive` and the `predCut` field; `IDw/PredCut.lean`'s
  `collapseHyps_predCut` supplies the latter.  So the final collapsing theorem needs only
  `PositiveP A` (and the fourteen `CollapseCases`).
-/
import OrdinalAnalysis.IDw.Collapsing.Theorem
import OrdinalAnalysis.IDw.PredCut

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

variable {A : FormJ}

/-- **`CollapseHyps A` from `PositiveP A` alone**: `bound`/`negStage` from
`IDw/Boundedness.lean` (via `collapseHyps_of`), `predCut` from `collapseHyps_predCut`. -/
theorem collapseHyps (hA : PositiveP A) : CollapseHyps A :=
  collapseHyps_of hA collapseHyps_predCut

end Collapsing

end IDw

end OrdinalAnalysis
