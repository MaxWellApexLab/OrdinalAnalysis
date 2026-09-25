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
import OrdinalAnalysis.IDn.AxiomsIDCases.params_predStage

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

theorem xFreeI_predOf {G : Semiformula (LIinfN n) ℕ 1} (hG : XFreeI G) (m : ℕ)
    (s : Semiterm (LIinfN n) ℕ m) : XFreeI (predOf G m s) := (xFreeI_rew _ _).mpr hG

theorem freeVariables_predOf {G : Semiformula (LIinfN n) ℕ 1} (hG : G.freeVariables = ∅) (m : ℕ)
    (s : Semiterm (LIinfN n) ℕ m) (hs : s.freeVariables = ∅) : (predOf G m s).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![s]) (φ := G) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ ((Rew.subst ![s]) #i : Semiterm (LIinfN n) ℕ m).freeVariables := hi
    obtain rfl := Subsingleton.elim i 0
    simp only [Rew.subst_bvar, Matrix.cons_val_zero, hs] at hi'
    exact Finset.notMem_empty x hi'
  · have hz' : z ∈ G.freeVariables := hz
    rw [hG] at hz'
    exact Finset.notMem_empty z hz'


end PlugForms
end IDn
end OrdinalAnalysis
