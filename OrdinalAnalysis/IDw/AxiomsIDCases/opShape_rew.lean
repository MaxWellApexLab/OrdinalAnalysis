/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\opShape_rew.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

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

set_option autoImplicit false
namespace OrdinalAnalysis

variable (k : ℕ)


namespace IDw


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### The two plugged forms -/

section PlugForms


-- case_skeleton: generated header ends here

theorem opShape_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew (LIinfW) ξ₁ n₁ ξ₂ n₂)
    {φ : Semiformula (LIinfW) ξ₁ n₁} (h : OpShape k φ) : OpShape k (ω ▹ φ) := by
  revert h
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => intro _; simp only [LogicalConnective.HomClass.map_top]; trivial
  | hfalsum => intro _; simp only [LogicalConnective.HomClass.map_bot]; trivial
  | hrel r v => intro h; rw [Semiformula.rew_rel]; exact h
  | hnrel r v => intro h; rw [Semiformula.rew_nrel]; exact h
  | hand φ ψ ihφ ihψ =>
    intro h; rw [LogicalConnective.HomClass.map_and]; exact ⟨ihφ ω h.1, ihψ ω h.2⟩
  | hor φ ψ ihφ ihψ =>
    intro h; rw [LogicalConnective.HomClass.map_or]; exact ⟨ihφ ω h.1, ihψ ω h.2⟩
  | hall φ ih => intro h; rw [Rewriting.app_all]; exact ih ω.q h
  | hexs φ ih => intro h; rw [Rewriting.app_exs]; exact ih ω.q h

/-- The image of a schema formula, positive in `P`, under `formHomAt k (Ω_{k+1})` has the shape
Exercise 6.3 needs: `P ↦ I_k^{≺Ω_{k+1}}` only positively, `Q ↦ Jlev k` in either polarity. -/
theorem opShape_lMap_top (k : ℕ) {ξ : Type*} :
    ∀ {m : ℕ} (φ : Semiformula LForm ξ m), PositiveP φ →
      OpShape k (Semiformula.lMap (formHomAt k (StageAt.top k)) φ)
  | _, .verum, _ => trivial
  | _, .falsum, _ => trivial
  | _, .rel (Sum.inl _) _, _ => trivial
  | _, .rel (Sum.inr PQRel.P) _, _ => by
      show OpRel k (formRelAt k (StageAt.top k) (Sum.inr PQRel.P))
      exact Or.inr rfl
  | _, .rel (Sum.inr PQRel.Q) _, _ => trivial
  | _, .nrel (Sum.inl _) _, _ => trivial
  | _, .nrel (Sum.inr PQRel.P) _, h => h.elim
  | _, .nrel (Sum.inr PQRel.Q) _, _ => trivial
  | _, .and φ ψ, hp => ⟨opShape_lMap_top k φ hp.1, opShape_lMap_top k ψ hp.2⟩
  | _, .or φ ψ, hp => ⟨opShape_lMap_top k φ hp.1, opShape_lMap_top k ψ hp.2⟩
  | _, .all φ, hp => opShape_lMap_top k φ hp
  | _, .exs φ, hp => opShape_lMap_top k φ hp

/-- The embedded operator form `A(t, I_k^{≺Ω_{k+1}})` of an `A` positive in `P` has the shape
Exercise 6.3 needs. -/
theorem opShape_unfold {A : FormJ} (hA : PositiveP A)
    (t : SyntacticTerm (LIinfW)) : OpShape k (unfoldW A k (StageAt.top k) t) :=
  opShape_rew k _ (opShape_rew k _ (opShape_lMap_top k A hA))


end PlugForms
end IDw
end OrdinalAnalysis
