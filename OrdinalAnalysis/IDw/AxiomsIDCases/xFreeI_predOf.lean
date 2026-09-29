/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\xFreeI_predOf.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

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
import OrdinalAnalysis.IDw.AxiomsIDCases.params_predStage

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

theorem xFreeI_predOf {G : Semiformula (LIinfW) ℕ 1} (hG : XFreeI G) (m : ℕ)
    (s : Semiterm (LIinfW) ℕ m) : XFreeI (predOf G m s) := (xFreeI_rew _ _).mpr hG

theorem freeVariables_predOf {G : Semiformula (LIinfW) ℕ 1} (hG : G.freeVariables = ∅) (m : ℕ)
    (s : Semiterm (LIinfW) ℕ m) (hs : s.freeVariables = ∅) : (predOf G m s).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![s]) (φ := G) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ ((Rew.subst ![s]) #i : Semiterm (LIinfW) ℕ m).freeVariables := hi
    obtain rfl := Subsingleton.elim i 0
    simp only [Rew.subst_bvar, Matrix.cons_val_zero, hs] at hi'
    exact Finset.notMem_empty x hi'
  · have hz' : z ∈ G.freeVariables := hz
    rw [hG] at hz'
    exact Finset.notMem_empty z hz'


end PlugForms
end IDw
end OrdinalAnalysis
