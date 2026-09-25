import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_or
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_rel
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_neg
import OrdinalAnalysis.IDn.AxiomsIDCases.FixF_q
import OrdinalAnalysis.IDn.AxiomsIDCases.predOf_rew
import OrdinalAnalysis.IDn.AxiomsIDCases.NumF_q
import OrdinalAnalysis.IDn.AxiomsIDCases.rew_plugI_num
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_lMap_top
import OrdinalAnalysis.IDn.AxiomsIDCases.embK_substI
import OrdinalAnalysis.IDn.AxiomsIDCases.opShape_rew
import OrdinalAnalysis.IDn.AxiomsIDCases.params_plugI

set_option autoImplicit false
namespace OrdinalAnalysis

variable {n : ℕ} (k : Fin n)


namespace IDn


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### The two plugged forms -/

section PlugForms


variable (P : Pred n)


-- case_skeleton: generated header ends here

theorem params_predStage (g : StageAt k.val) (m : ℕ) (s : Semiterm (LIinfN n) ℕ m) :
    params (predStage k g m s) ⊆ {(⟨k, g⟩ : Stage n)} := subset_refl _

theorem params_predOf (G : Semiformula (LIinfN n) ℕ 1) (m : ℕ) (s : Semiterm (LIinfN n) ℕ m) :
    params (predOf G m s) ⊆ params G := by
  show params (Rew.subst ![s] ▹ G) ⊆ _; rw [params_rew]

theorem xFreeI_predStage (g : StageAt k.val) (m : ℕ) (s : Semiterm (LIinfN n) ℕ m) :
    XFreeI (predStage k g m s) := fun h => h


end PlugForms
end IDn
end OrdinalAnalysis
