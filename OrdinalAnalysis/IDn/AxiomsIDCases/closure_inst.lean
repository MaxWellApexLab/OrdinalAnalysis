import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.embK_substI
import OrdinalAnalysis.IDn.AxiomsIDCases.unfold_top_eq
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

theorem closure_inst (A : Semisentence (LXIn n) 1) (m : ℕ) :
    (∼(bodyTop k A) ⋎ IOmegaAt k (#0 : Semiterm (LIinfN n) ℕ 1))/[numI m] =
      ∼(unfold A k (StageAt.top k.val) (numI m)) ⋎ IOmegaAt k (numI m) := by
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    rew_IOmegaAt, Rew.subst_bvar, Matrix.cons_val_zero]
  rfl

theorem freeVariables_bodyTop (A : Semisentence (LXIn n) 1) : (bodyTop k A).freeVariables = ∅ :=
  Semiformula.freeVariables_emb _

/-- Every parameter of `bodyTop k A` is the top stage of some level. -/
theorem params_bodyTop (A : Semisentence (LXIn n) 1) :
    params (bodyTop k A) ⊆ {s : Stage n | ∃ j : Fin n, s = Stage.top j} := by
  show params (Rew.emb ▹ formAt A k (StageAt.top k.val) : Semiformula (LIinfN n) ℕ 1) ⊆ _
  rw [params_rew]
  intro s hs
  rcases params_lMap_stageHom k (StageAt.top k.val) A hs with h | h
  · exact ⟨k, h⟩
  · exact h


end Closure
end IDn
end OrdinalAnalysis
