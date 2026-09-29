/-
  **The full `EmbedHyps A` for every positive operator form**, assembled from the merged bridge
  files: `taut` (`IDw/AxiomsLogic`, via `EmbedHypsLogic`), `eq_axiom`/`paMinus_axiom`
  (`EmbedHypsLogic`), `induction_axiom` (`EmbedHypsPA`, its four side hypotheses discharged by the
  real `Sim`, `sim_subst_closed`, `IDwDerivable.replace_head`, `allClosure_derivable`), and
  `closure_axiom`/`indAx_axiom` (`EmbedHypsID`). Unlike `IDn/EmbedHypsAll.lean`, no field is taken
  as a hypothesis.
-/
import OrdinalAnalysis.IDw.EmbedHypsLogic
import OrdinalAnalysis.IDw.EmbedHypsPA
import OrdinalAnalysis.IDw.EmbedHypsID

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder

/-- **`EmbedHyps A` for every operator form `A`**: every field is a theorem. -/
theorem embedHyps (A : FormJ) : EmbedHyps A where
  taut := fun hH ψ hc => embedHyps_taut_of_al hH ψ hc
  eq_axiom := (embedHypsLogicPart (A := A)).eq_axiom
  paMinus_axiom := (embedHypsLogicPart (A := A)).paMinus_axiom
  induction_axiom :=
    embedHyps_induction_of_pa (fun hH ψ hc => embedHyps_taut_of_al hH ψ hc)
      Sim sim_subst_closed (fun hH => IDwDerivable.replace_head hH)
      allClosure_derivable
  closure_axiom := embedHyps_closure_axiom
  indAx_axiom := embedHyps_indAx_axiom

end IDw

end OrdinalAnalysis
