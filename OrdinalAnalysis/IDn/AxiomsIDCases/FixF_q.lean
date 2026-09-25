import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_or
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_rel
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_neg

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

theorem FixF.q {n₁ n₂ : ℕ} {ω : Rew (LIinfN n) ℕ n₁ ℕ n₂} (h : FixF ω) : FixF ω.q := by
  intro x; rw [Rew.q_fvar, h x]; rfl

theorem fixF_subst {m j : ℕ} (w : Fin j → Semiterm (LIinfN n) ℕ m) : FixF (Rew.subst w) :=
  fun x => Rew.subst_fvar w x

theorem predStage_rew (g : StageAt k.val) {n₁ n₂ : ℕ} (ω : Rew (LIinfN n) ℕ n₁ ℕ n₂)
    (s : Semiterm (LIinfN n) ℕ n₁) : ω ▹ predStage k g n₁ s = predStage k g n₂ (ω s) :=
  Semiformula.rew_rel1 ω


end Plug
end IDn
end OrdinalAnalysis
