/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\plugI_lMap_top.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.AxiomsIDCases.Defs
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_or
import OrdinalAnalysis.IDw.Boundedness
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_rel
import OrdinalAnalysis.IDw.AxiomsIDCases.plugI_neg
import OrdinalAnalysis.IDw.AxiomsIDCases.FixF_q
import OrdinalAnalysis.IDw.AxiomsIDCases.predOf_rew
import OrdinalAnalysis.IDw.AxiomsIDCases.NumF_q
import OrdinalAnalysis.IDw.AxiomsIDCases.rew_plugI_num

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

/-- **Plugging `I_k^{≺g}` into the top-level unfolding of a schema gives the `g`-level unfolding**:
`formHomAt k (Ω_{k+1})` composed with the plug is `formHomAt k g` (`P ↦ I_k^{≺g}`; `Q ↦ Jlev k`
is fixed by the plug). -/
theorem plugI_lMap_top (g : StageAt k) :
    ∀ {m : ℕ} (φ : Semiformula LForm ℕ m),
      plugI k (predStage k g) (Semiformula.lMap (formHomAt k (StageAt.top k)) φ) =
        Semiformula.lMap (formHomAt k g) φ := by
  intro m φ
  induction φ using Semiformula.rec' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v =>
    rw [Semiformula.lMap_rel, Semiformula.lMap_rel, plugI_rel]
    rcases r with r | r
    · show Semiformula.rel _ _ = Semiformula.rel _ _
      congr 1
      funext i
      exact lMap_formHomAt_term k _ _ (v i)
    · cases r with
      | P =>
        show plugRel k (predStage k g)
            (Sum.inr (IInfRelW.stage ⟨k, StageAt.top k⟩))
            (Semiterm.lMap (formHomAt k (StageAt.top k)) ∘ v) =
          Semiformula.rel (Sum.inr (IInfRelW.stage ⟨k, g⟩))
            (Semiterm.lMap (formHomAt k g) ∘ v)
        have hcond : (⟨k, StageAt.top k⟩ : Stage) = Stage.top k := rfl
        simp only [plugRel, if_pos hcond]
        show stageAt (⟨k, g⟩ : Stage) _ = Semiformula.rel (Sum.inr (IInfRelW.stage ⟨k, g⟩)) _
        rw [rel_eq_vec (Sum.inr (IInfRelW.stage (⟨k, g⟩ : Stage)))]
        show Semiformula.rel _ _ = Semiformula.rel _ _
        congr 1
        funext i
        obtain rfl := Subsingleton.elim i 0
        exact lMap_formHomAt_term k _ _ (v 0)
      | Q =>
        show Semiformula.rel _ _ = Semiformula.rel _ _
        congr 1
        funext i
        exact lMap_formHomAt_term k _ _ (v i)
  | hnrel r v =>
    rw [Semiformula.lMap_nrel, Semiformula.lMap_nrel, plugI_nrel]
    rcases r with r | r
    · show Semiformula.nrel _ _ = Semiformula.nrel _ _
      congr 1
      funext i
      exact lMap_formHomAt_term k _ _ (v i)
    · cases r with
      | P =>
        show plugNrel k (predStage k g)
            (Sum.inr (IInfRelW.stage ⟨k, StageAt.top k⟩))
            (Semiterm.lMap (formHomAt k (StageAt.top k)) ∘ v) =
          Semiformula.nrel (Sum.inr (IInfRelW.stage ⟨k, g⟩))
            (Semiterm.lMap (formHomAt k g) ∘ v)
        have hcond : (⟨k, StageAt.top k⟩ : Stage) = Stage.top k := rfl
        simp only [plugNrel, if_pos hcond]
        show ∼(stageAt (⟨k, g⟩ : Stage) _) = Semiformula.nrel (Sum.inr (IInfRelW.stage ⟨k, g⟩)) _
        rw [nrel_eq_vec (Sum.inr (IInfRelW.stage (⟨k, g⟩ : Stage)))]
        show Semiformula.nrel _ _ = Semiformula.nrel _ _
        congr 1
        funext i
        obtain rfl := Subsingleton.elim i 0
        exact lMap_formHomAt_term k _ _ (v 0)
      | Q =>
        show Semiformula.nrel _ _ = Semiformula.nrel _ _
        congr 1
        funext i
        exact lMap_formHomAt_term k _ _ (v i)
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and, plugI_and, ihφ,
      ihψ]
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or, plugI_or, ihφ, ihψ]
  | hall φ ih => rw [Semiformula.lMap_all, Semiformula.lMap_all, plugI_all, ih]
  | hexs φ ih => rw [Semiformula.lMap_exs, Semiformula.lMap_exs, plugI_exs, ih]

/-- The unfolding as a rewriting of the `lMap`-image: `A[y := k̄, x := t]` under `formHomAt k a`. -/
theorem unfold_eq_rew (A : FormJ) (a : StageAt k) (t : SyntacticTerm (LIinfW)) :
    unfoldW A k a t =
      Rew.subst ![t, (Semiterm.numeral k : SyntacticTerm LIinfW)] ▹
        Semiformula.lMap (formHomAt k a) (Rewriting.emb A : Semiformula LForm ℕ 2) := by
  rw [unfoldW, formAtW, Semiformula.lMap_emb]

/-- **`φ(t, I_k^{≺γ})` is `φ(t, I_k^{≺Ω_{k+1}})` with the stage `I_k^{≺γ}` plugged in.** -/
theorem plugI_unfold (A : FormJ) (g : StageAt k) (t : SyntacticTerm (LIinfW)) :
    plugI k (predStage k g) (unfoldW A k (StageAt.top k) t) = unfoldW A k g t := by
  rw [unfold_eq_rew, unfold_eq_rew, ← rew_plugI_stage k g (fixF_subst _), plugI_lMap_top]


end PlugForms
end IDw
end OrdinalAnalysis
