/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\FixF_q.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.AxiomsIDCases.Defs
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_or
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_rel
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_neg

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

theorem FixF.q {n₁ n₂ : ℕ} {ω : Rew (LIinfW) ℕ n₁ ℕ n₂} (h : FixF ω) : FixF ω.q := by
  intro x; rw [Rew.q_fvar, h x]; rfl

theorem fixF_subst {m j : ℕ} (w : Fin j → Semiterm (LIinfW) ℕ m) : FixF (Rew.subst w) :=
  fun x => Rew.subst_fvar w x

theorem predStage_rew (g : StageAt k) {n₁ n₂ : ℕ} (ω : Rew (LIinfW) ℕ n₁ ℕ n₂)
    (s : Semiterm (LIinfW) ℕ n₁) : ω ▹ predStage k g n₁ s = predStage k g n₂ (ω s) :=
  Semiformula.rew_rel1 ω


end Plug
end IDw
end OrdinalAnalysis
