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

set_option autoImplicit false
namespace OrdinalAnalysis

variable {n : ℕ} (k : Fin n)


namespace IDn


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### The two plugged forms -/

section PlugForms


-- case_skeleton: generated header ends here

theorem opShape_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew (LIinfN n) ξ₁ n₁ ξ₂ n₂)
    {φ : Semiformula (LIinfN n) ξ₁ n₁} (h : OpShape k φ) : OpShape k (ω ▹ φ) := by
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

theorem opShape_lMap_top (k : Fin n) {ξ : Type*} :
    ∀ {m : ℕ} (φ : Semiformula (LXIn n) ξ m), PositiveIn k φ → XFreeL φ →
      OpShape k (Semiformula.lMap (stageHom k (StageAt.top k.val)) φ)
  | _, .verum, _, _ => trivial
  | _, .falsum, _, _ => trivial
  | _, .rel (Sum.inl _) _, _, _ => trivial
  | _, .rel (Sum.inr IXRelN.X) _, _, h => h.elim
  | _, .rel (Sum.inr (IXRelN.I j)) _, _, _ => by
      show OpRel k (stageRel k (StageAt.top k.val) (Sum.inr (IXRelN.I j)))
      by_cases hjk : j = k
      · subst hjk; rw [stageRel_I, dif_pos rfl]; exact Or.inr rfl
      · rw [stageRel_I, dif_neg hjk]; exact Or.inl (by simpa using hjk)
  | _, .nrel (Sum.inl _) _, _, _ => trivial
  | _, .nrel (Sum.inr IXRelN.X) _, _, h => h.elim
  | _, .nrel (Sum.inr (IXRelN.I j)) _, h, _ => by
      show OpNrel k (stageRel k (StageAt.top k.val) (Sum.inr (IXRelN.I j)))
      have hjk : j ≠ k := h
      rw [stageRel_I, dif_neg hjk]
      show (Stage.top j : Stage n).lvl ≠ k
      simpa using hjk
  | _, .and φ ψ, hp, hx => ⟨opShape_lMap_top k φ hp.1 hx.1, opShape_lMap_top k ψ hp.2 hx.2⟩
  | _, .or φ ψ, hp, hx => ⟨opShape_lMap_top k φ hp.1 hx.1, opShape_lMap_top k ψ hp.2 hx.2⟩
  | _, .all φ, hp, hx => opShape_lMap_top k φ hp hx
  | _, .exs φ, hp, hx => opShape_lMap_top k φ hp hx

/-- The embedded operator form `A(t, I_k^{≺Ω_{k+1}})` of an `A` positive in level `k`, `X`-free,
has the shape Exercise 6.3 needs. -/
theorem opShape_unfold {A : Semisentence (LXIn n) 1} (hA : PositiveIn k A) (hX : XFreeL A)
    (t : SyntacticTerm (LIinfN n)) : OpShape k (unfold A k (StageAt.top k.val) t) :=
  opShape_rew k _ (opShape_rew k _ (opShape_lMap_top k A hA hX))


end PlugForms
end IDn
end OrdinalAnalysis
