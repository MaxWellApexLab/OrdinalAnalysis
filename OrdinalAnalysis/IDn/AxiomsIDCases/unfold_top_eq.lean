import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.embK_substI
import OrdinalAnalysis.IDn.AxiomsLogic

set_option autoImplicit false
namespace OrdinalAnalysis

variable {n : ℕ} (k : Fin n)


namespace IDn


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### Proposition 6.2: the closure axiom -/

section Closure


variable {A : Semisentence (LXIn n) 1}


-- case_skeleton: generated header ends here

theorem unfold_top_eq (A : Semisentence (LXIn n) 1) (t : SyntacticTerm (LIinfN n)) :
    unfold A k (StageAt.top k.val) t = (bodyTop k A)/[t] := rfl

theorem emb_embK_eq_bodyTop (hX : XFreeL A) :
    (Rewriting.emb (embK A) : Semiformula (LIinfN n) ℕ 1) = bodyTop k A := by
  rw [embK_eq_embed hX]
  show (Rewriting.emb (embed A) : Semiformula (LIinfN n) ℕ 1) =
    (Rew.emb ▹ formAt A k (StageAt.top k.val) : Semiformula (LIinfN n) ℕ 1)
  rw [formAt_top]

theorem emb_embK_closureAx (hX : XFreeL A) :
    (Rewriting.emb (embK (closureAxAt k A)) : Proposition (LIinfN n)) =
      ∀¹ (∼(bodyTop k A) ⋎ IOmegaAt k (#0 : Semiterm (LIinfN n) ℕ 1)) := by
  rw [closureAxAt, embK_all, embK_imp, embK_Iat, Semiformula.imp_eq]
  simp only [Rewriting.app_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, rew_IOmegaAt, embT, Semiterm.lMap_bvar]
  rw [show ((Rew.emb).q ▹ embK A : Semiformula (LIinfN n) ℕ 1) = Rewriting.emb (embK A) by
    rw [Rew.q_emb], emb_embK_eq_bodyTop k hX]
  rfl


end Closure
end IDn
end OrdinalAnalysis
