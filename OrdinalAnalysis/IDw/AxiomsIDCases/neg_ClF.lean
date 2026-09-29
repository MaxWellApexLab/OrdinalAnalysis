/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\neg_ClF.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.AxiomsIDCases.Defs

set_option autoImplicit false
namespace OrdinalAnalysis

variable (k : ℕ)

namespace IDw

open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting

/-! ### Proposition 6.4: the induction axiom -/

section Induction

theorem neg_ClF (A : FormJ) (G : Semiformula (LIinfW) ℕ 1) :
    ∼(ClF k A G) = ∃¹ (plugI k (predOf G) (bodyTop k A) ⋏ ∼G) := by
  simp [ClF]

theorem numSubst₁_eq_self {φ : Semiformula (LIinfW) ℕ 1} (h : φ.freeVariables = ∅) (g : ℕ → ℕ) :
    numSubst₁ g ▹ φ = φ := by
  refine Semiformula.rew_eq_self_of (fun x => numSubst₁_bvar g x) ?_
  intro x hx
  have hx' : x ∈ φ.freeVariables := hx
  rw [h] at hx'
  exact absurd hx' (by simp)

end Induction
end IDw
end OrdinalAnalysis
