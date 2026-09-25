import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_or
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_rel
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_neg
import OrdinalAnalysis.IDn.AxiomsIDCases.FixF_q
import OrdinalAnalysis.IDn.AxiomsIDCases.predOf_rew

set_option autoImplicit false
namespace OrdinalAnalysis

variable {n : ℕ} (k : Fin n)


namespace IDn


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### Predicates plugged into an operator form -/

section Plug


variable (P : Pred n)


-- case_skeleton: generated header ends here

theorem NumF.q {f : ℕ → ℕ} {n₁ n₂ : ℕ} {ω : Rew (LIinfN n) ℕ n₁ ℕ n₂} (h : NumF f ω) :
    NumF f ω.q := by
  intro x; rw [Rew.q_fvar, h x]; simp

theorem predOf_numF (f : ℕ → ℕ) (G : Semiformula (LIinfN n) ℕ 1) {n₁ n₂ : ℕ}
    {ω : Rew (LIinfN n) ℕ n₁ ℕ n₂} (hω : NumF f ω) (s : Semiterm (LIinfN n) ℕ n₁) :
    ω ▹ predOf G n₁ s = predOf ((numSubst₁ (n := n) f) ▹ G) n₂ (ω s) := by
  show ω ▹ (G ⇜ ![s]) = ((numSubst₁ (n := n) f) ▹ G) ⇜ ![ω s]
  simpa [← comp_app] using smul_ext' (φ := G) <| by
    ext x
    · obtain rfl := Subsingleton.elim x 0; simp [Rew.comp_app]
    · simp [Rew.comp_app, hω x, numSubst₁]

theorem numF_numSubst₁ (f : ℕ → ℕ) : NumF f (numSubst₁ (n := n) f) := fun _ => rfl


end Plug
end IDn
end OrdinalAnalysis
