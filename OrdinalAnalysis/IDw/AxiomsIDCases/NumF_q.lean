/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\NumF_q.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.AxiomsIDCases.Defs
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_or
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_rel
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_neg
import OrdinalAnalysis.IDw.AxiomsIDCases.FixF_q
import OrdinalAnalysis.IDw.AxiomsIDCases.predOf_rew

set_option autoImplicit false
namespace OrdinalAnalysis

variable (k : ℕ)


namespace IDw


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### Predicates plugged into an operator form -/

section Plug


variable (P : Pred)


-- case_skeleton: generated header ends here

theorem NumF.q {f : ℕ → ℕ} {n₁ n₂ : ℕ} {ω : Rew (LIinfW) ℕ n₁ ℕ n₂} (h : NumF f ω) :
    NumF f ω.q := by
  intro x; rw [Rew.q_fvar, h x]; simp

theorem predOf_numF (f : ℕ → ℕ) (G : Semiformula (LIinfW) ℕ 1) {n₁ n₂ : ℕ}
    {ω : Rew (LIinfW) ℕ n₁ ℕ n₂} (hω : NumF f ω) (s : Semiterm (LIinfW) ℕ n₁) :
    ω ▹ predOf G n₁ s = predOf ((numSubst₁ f) ▹ G) n₂ (ω s) := by
  show ω ▹ (G ⇜ ![s]) = ((numSubst₁ f) ▹ G) ⇜ ![ω s]
  simpa [← comp_app] using smul_ext' (φ := G) <| by
    ext x
    · obtain rfl := Subsingleton.elim x 0; simp [Rew.comp_app]
    · simp [Rew.comp_app, hω x, numSubst₁]

theorem numF_numSubst₁ (f : ℕ → ℕ) : NumF f (numSubst₁ f) := fun _ => rfl


end Plug
end IDw
end OrdinalAnalysis
