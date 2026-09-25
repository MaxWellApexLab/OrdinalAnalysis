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

/-- **The embedded `A(x, F)` is `A(x, I_k^{≺Ω_{k+1}})` with `F⁺` plugged in.** -/
theorem embK_substI (F : Semiformula (LXIn n) ℕ 1) :
    ∀ {m : ℕ} (φ : Semiformula (LXIn n) ℕ m),
      embK (substIAt k F φ) = plugI k (predOf (embK F)) (embK φ) := by
  intro m φ
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
    rcases r with r | r
    · rfl
    · cases r with
      | X => rfl
      | I j =>
        have hv : Semiformula.rel (Sum.inr (IXRelN.I j) : (LXIn n).Rel 1) v = Iat j (v 0) := by
          show Semiformula.rel _ v = Semiformula.rel _ ![v 0]
          congr 1; funext i; obtain rfl := Subsingleton.elim i 0; rfl
        rw [hv]
        by_cases hjk : j = k
        · subst hjk
          rw [show substIAt j F (Iat j (v 0)) = F/[v 0] from dif_pos rfl, embK_subst₁ j, embK_Iat]
          show (embK F)/[embT j (v 0)] =
              plugRel j (predOf (embK F)) (Sum.inr (IInfRelN.stage (Stage.top j))) ![embT j (v 0)]
          simp only [plugRel, if_true]
          rfl
        · rw [show substIAt k F (Iat j (v 0)) = Iat j (v 0) from dif_neg hjk, embK_Iat]
          show IOmegaAt j (embT j (v 0)) =
              plugRel k (predOf (embK F)) (Sum.inr (IInfRelN.stage (Stage.top j))) ![embT j (v 0)]
          have hne : (Stage.top j : Stage n) ≠ Stage.top k :=
            fun e => hjk (Stage.top_inj.mp e)
          simp only [plugRel, if_neg hne]
          rfl
  | hnrel r v =>
    rcases r with r | r
    · rfl
    · cases r with
      | X => rfl
      | I j =>
        have hv : Semiformula.nrel (Sum.inr (IXRelN.I j) : (LXIn n).Rel 1) v = ∼(Iat j (v 0)) := by
          show Semiformula.nrel _ v = Semiformula.nrel _ ![v 0]
          congr 1; funext i; obtain rfl := Subsingleton.elim i 0; rfl
        rw [hv]
        by_cases hjk : j = k
        · subst hjk
          rw [show substIAt j F (∼(Iat j (v 0))) = ∼(F/[v 0]) from dif_pos rfl,
            embK_neg, embK_neg, embK_subst₁ j, embK_Iat]
          show ∼((embK F)/[embT j (v 0)]) =
              plugNrel j (predOf (embK F)) (Sum.inr (IInfRelN.stage (Stage.top j))) ![embT j (v 0)]
          simp only [plugNrel, if_true]
          rfl
        · rw [show substIAt k F (∼(Iat j (v 0))) = ∼(Iat j (v 0)) from dif_neg hjk,
            embK_neg, embK_Iat]
          show ∼(IOmegaAt j (embT j (v 0))) =
              plugNrel k (predOf (embK F)) (Sum.inr (IInfRelN.stage (Stage.top j))) ![embT j (v 0)]
          have hne : (Stage.top j : Stage n) ≠ Stage.top k :=
            fun e => hjk (Stage.top_inj.mp e)
          simp only [plugNrel, if_neg hne]
          rfl
  | hand φ ψ ihφ ihψ =>
    show embK (substIAt k F φ ⋏ substIAt k F ψ) = _
    rw [embK_and, embK_and, plugI_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
    show embK (substIAt k F φ ⋎ substIAt k F ψ) = _
    rw [embK_or, embK_or, plugI_or, ihφ, ihψ]
  | hall φ ih =>
    show embK (∀¹ substIAt k F φ) = _
    rw [embK_all, embK_all, plugI_all, ih]
  | hexs φ ih =>
    show embK (∃¹ substIAt k F φ) = _
    rw [embK_exs, embK_exs, plugI_exs, ih]


end PlugForms
end IDn
end OrdinalAnalysis
