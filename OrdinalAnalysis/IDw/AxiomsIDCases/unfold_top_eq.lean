/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\unfold_top_eq.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.AxiomsIDCases.Defs

set_option autoImplicit false
namespace OrdinalAnalysis

variable (k : ℕ)

namespace IDw

open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting

/-! ### Proposition 6.2: the closure axiom -/

section Closure

/-- **The top unfolding is `bodyTop` at `t`**: `unfoldW A k Ω_{k+1} t = A(x, I_k^{≺Ω_{k+1}})[x := t]`
(the level `y = k̄` was already fixed inside `bodyTop`). -/
theorem unfold_top_eq (A : FormJ) (t : SyntacticTerm (LIinfW)) :
    unfoldW A k (StageAt.top k) t = (bodyTop k A)/[t] := by
  have hc : (Rew.subst ![t] : Rew LIinfW ℕ 1 ℕ 0).comp
      (Rew.subst ![(#0 : Semiterm LIinfW ℕ 1), (Semiterm.numeral k : Semiterm LIinfW ℕ 1)]) =
      Rew.subst ![t, (Semiterm.numeral k : Semiterm LIinfW ℕ 0)] := by
    refine Rew.ext _ _ ?_ ?_
    · intro x; fin_cases x <;> simp [Rew.comp_app]
    · intro x; simp [Rew.comp_app]
  unfold bodyTop unfoldW
  show _ = Rew.subst ![t] ▹ (Rew.subst ![(#0 : Semiterm LIinfW ℕ 1),
    (Semiterm.numeral k : Semiterm LIinfW ℕ 1)] ▹ _)
  rw [← TransitiveRewriting.comp_app, hc]

end Closure
end IDw
end OrdinalAnalysis
