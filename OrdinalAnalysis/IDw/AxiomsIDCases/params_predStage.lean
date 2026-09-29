/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\params_predStage.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.AxiomsIDCases.Defs
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_or
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_rel
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_neg
import OrdinalAnalysis.IDw.AxiomsIDCases.FixF_q
import OrdinalAnalysis.IDw.AxiomsIDCases.predOf_rew
import OrdinalAnalysis.IDw.AxiomsIDCases.NumF_q
import OrdinalAnalysis.IDw.AxiomsIDCases.rew_plugI_num
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_lMap_top
import OrdinalAnalysis.IDw.AxiomsIDCases.opShape_rew
import OrdinalAnalysis.IDw.AxiomsIDCases.params_plugI

set_option autoImplicit false
namespace OrdinalAnalysis

variable (k : ℕ)


namespace IDw


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### The two plugged forms -/

section PlugForms


variable (P : Pred)


-- case_skeleton: generated header ends here

theorem params_predStage (g : StageAt k) (m : ℕ) (s : Semiterm (LIinfW) ℕ m) :
    params (predStage k g m s) ⊆ {(⟨k, g⟩ : Stage)} := subset_refl _

theorem params_predOf (G : Semiformula (LIinfW) ℕ 1) (m : ℕ) (s : Semiterm (LIinfW) ℕ m) :
    params (predOf G m s) ⊆ params G := by
  show params (Rew.subst ![s] ▹ G) ⊆ _; rw [params_rew]

theorem xFreeI_predStage (g : StageAt k) (m : ℕ) (s : Semiterm (LIinfW) ℕ m) :
    XFreeI (predStage k g m s) := fun h => h


end PlugForms
end IDw
end OrdinalAnalysis
