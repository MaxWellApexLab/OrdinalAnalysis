import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_or
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_rel
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_neg
import OrdinalAnalysis.IDn.AxiomsIDCases.FixF_q

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

theorem predOf_rew (G : Semiformula (LIinfN n) ℕ 1) {n₁ n₂ : ℕ} {ω : Rew (LIinfN n) ℕ n₁ ℕ n₂}
    (hω : FixF ω) (s : Semiterm (LIinfN n) ℕ n₁) : ω ▹ predOf G n₁ s = predOf G n₂ (ω s) := by
  show ω ▹ (G ⇜ ![s]) = G ⇜ ![ω s]
  simpa [← comp_app] using smul_ext' (φ := G) <| by
    ext x
    · obtain rfl := Subsingleton.elim x 0; simp [Rew.comp_app]
    · simp [Rew.comp_app, hω x]

/-- Plugging a stage commutes with the substitutions of the calculus. -/
theorem rew_plugI_stage (g : StageAt k.val) {n₁ n₂ : ℕ} {ω : Rew (LIinfN n) ℕ n₁ ℕ n₂} (hω : FixF ω)
    (φ : Semiformula (LIinfN n) ℕ n₁) :
    ω ▹ plugI k (predStage k g) φ = plugI k (predStage k g) (ω ▹ φ) :=
  rew_plugI k (predStage k g) (predStage k g) FixF (fun h => h.q)
    (fun {_ _} {ω} _ s => predStage_rew k g ω s) φ hω

theorem rew_plugI_of (G : Semiformula (LIinfN n) ℕ 1) {n₁ n₂ : ℕ} {ω : Rew (LIinfN n) ℕ n₁ ℕ n₂}
    (hω : FixF ω) (φ : Semiformula (LIinfN n) ℕ n₁) :
    ω ▹ plugI k (predOf G) φ = plugI k (predOf G) (ω ▹ φ) :=
  rew_plugI k (predOf G) (predOf G) FixF (fun h => h.q) (fun h s => predOf_rew G h s) φ hω


end Plug
end IDn
end OrdinalAnalysis
