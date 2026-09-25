import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.embK_substI
import OrdinalAnalysis.IDn.AxiomsIDCases.unfold_top_eq
import OrdinalAnalysis.IDn.AxiomsIDCases.closure_inst
import OrdinalAnalysis.IDn.AxiomsLogic

set_option autoImplicit false
namespace OrdinalAnalysis

variable {n : ℕ} (k : Fin n)


namespace IDn


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### Proposition 6.4: the induction axiom -/

section Induction


variable {A : Semisentence (LXIn n) 1} {H : Set ThetaWNoteD → Set ThetaWNoteD}


-- case_skeleton: generated header ends here

theorem neg_ClF (A : Semisentence (LXIn n) 1) (G : Semiformula (LIinfN n) ℕ 1) :
    ∼(ClF k A G) = ∃¹ (plugI k (predOf G) (bodyTop k A) ⋏ ∼G) := by
  simp [ClF]

theorem numSubst₁_eq_self {φ : Semiformula (LIinfN n) ℕ 1} (h : φ.freeVariables = ∅) (g : ℕ → ℕ) :
    numSubst₁ g ▹ φ = φ := by
  refine Semiformula.rew_eq_self_of (fun x => numSubst₁_bvar g x) ?_
  intro x hx
  have hx' : x ∈ φ.freeVariables := hx
  rw [h] at hx'
  exact absurd hx' (by simp)

/-- **The embedded induction axiom under a numeral assignment**: `¬Cl(G) ∨ ∀x (¬I x ∨ G(x))`
with `G = F⁺` under the assignment. -/
theorem indAx_inst (hX : XFreeL A) (F : Semiformula (LXIn n) ℕ 1) (g : ℕ → ℕ) :
    numSubst g ▹ embK ((∀¹ (opAt k A F 🡒 F)) 🡒 ∀¹ (Iat k #0 🡒 F)) =
      ∼(ClF k A (numSubst₁ g ▹ embK F)) ⋎
        (∀¹ (∼(IOmegaAt k (#0 : Semiterm (LIinfN n) ℕ 1)) ⋎ (numSubst₁ g ▹ embK F))) := by
  have hO : embK (opAt k A F) = plugI k (predOf (embK F)) (bodyTop k A) := by
    rw [opAt, embK_substI, embK_emb, emb_embK_eq_bodyTop k hX]
  simp only [Semiformula.imp_eq, embK_or, embK_neg, embK_all, embK_Iat, embT,
    Semiterm.lMap_bvar, hO, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    numSubst_all, rew_IOmegaAt]
  rw [rew_plugI_num, numSubst₁_eq_self (freeVariables_bodyTop k A), numSubst₁_bvar]
  rfl


end Induction
end IDn
end OrdinalAnalysis
