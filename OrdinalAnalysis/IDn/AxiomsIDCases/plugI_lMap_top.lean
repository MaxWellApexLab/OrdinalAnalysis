import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_verum
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_or
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_rel
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_neg
import OrdinalAnalysis.IDn.AxiomsIDCases.FixF_q
import OrdinalAnalysis.IDn.AxiomsIDCases.predOf_rew
import OrdinalAnalysis.IDn.AxiomsIDCases.NumF_q
import OrdinalAnalysis.IDn.AxiomsIDCases.rew_plugI_num

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

theorem plugI_lMap_top (g : StageAt k.val) :
    ∀ {m : ℕ} (φ : Semiformula (LXIn n) ℕ m),
      plugI k (predStage k g) (Semiformula.lMap (stageHom k (StageAt.top k.val)) φ) =
        Semiformula.lMap (stageHom k g) φ := by
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
      exact lMap_stageHom_term k k _ _ (v i)
    · cases r with
      | X =>
        show Semiformula.rel _ _ = Semiformula.rel _ _
        congr 1
        funext i
        exact lMap_stageHom_term k k _ _ (v i)
      | I j =>
        by_cases hjk : j = k
        · subst hjk
          show plugRel j (predStage j g)
              (stageRel j (StageAt.top j.val) (Sum.inr (IXRelN.I j)))
              (Semiterm.lMap (stageHom j (StageAt.top j.val)) ∘ v) =
            Semiformula.rel (stageRel j g (Sum.inr (IXRelN.I j)))
              (Semiterm.lMap (stageHom j g) ∘ v)
          rw [stageRel_I, dif_pos rfl, stageRel_I, dif_pos rfl]
          have hcond : (⟨j, StageAt.top j.val⟩ : Stage n) = Stage.top j := rfl
          simp only [plugRel, if_pos hcond]
          show stageAt (⟨j, g⟩ : Stage n) _ = Semiformula.rel (Sum.inr (IInfRelN.stage ⟨j, g⟩)) _
          rw [rel_eq_vec (Sum.inr (IInfRelN.stage (⟨j, g⟩ : Stage n)))]
          show Semiformula.rel _ _ = Semiformula.rel _ _
          congr 1
          funext i
          obtain rfl := Subsingleton.elim i 0
          exact lMap_stageHom_term j j _ _ (v 0)
        · show plugRel k (predStage k g)
              (stageRel k (StageAt.top k.val) (Sum.inr (IXRelN.I j)))
              (Semiterm.lMap (stageHom k (StageAt.top k.val)) ∘ v) =
            Semiformula.rel (stageRel k g (Sum.inr (IXRelN.I j)))
              (Semiterm.lMap (stageHom k g) ∘ v)
          rw [stageRel_I, dif_neg hjk, stageRel_I, dif_neg hjk]
          have hne : (Stage.top j : Stage n) ≠ Stage.top k :=
            fun e => hjk (Stage.top_inj.mp e)
          simp only [plugRel, if_neg hne]
          show Semiformula.rel _ _ = Semiformula.rel _ _
          congr 1
          funext i
          exact lMap_stageHom_term k k _ _ (v i)
  | hnrel r v =>
    rw [Semiformula.lMap_nrel, Semiformula.lMap_nrel, plugI_nrel]
    rcases r with r | r
    · show Semiformula.nrel _ _ = Semiformula.nrel _ _
      congr 1
      funext i
      exact lMap_stageHom_term k k _ _ (v i)
    · cases r with
      | X =>
        show Semiformula.nrel _ _ = Semiformula.nrel _ _
        congr 1
        funext i
        exact lMap_stageHom_term k k _ _ (v i)
      | I j =>
        by_cases hjk : j = k
        · subst hjk
          show plugNrel j (predStage j g)
              (stageRel j (StageAt.top j.val) (Sum.inr (IXRelN.I j)))
              (Semiterm.lMap (stageHom j (StageAt.top j.val)) ∘ v) =
            Semiformula.nrel (stageRel j g (Sum.inr (IXRelN.I j)))
              (Semiterm.lMap (stageHom j g) ∘ v)
          rw [stageRel_I, dif_pos rfl, stageRel_I, dif_pos rfl]
          have hcond : (⟨j, StageAt.top j.val⟩ : Stage n) = Stage.top j := rfl
          simp only [plugNrel, if_pos hcond]
          show ∼(stageAt (⟨j, g⟩ : Stage n) _) = Semiformula.nrel (Sum.inr (IInfRelN.stage ⟨j, g⟩)) _
          rw [nrel_eq_vec (Sum.inr (IInfRelN.stage (⟨j, g⟩ : Stage n)))]
          show Semiformula.nrel _ _ = Semiformula.nrel _ _
          congr 1
          funext i
          obtain rfl := Subsingleton.elim i 0
          exact lMap_stageHom_term j j _ _ (v 0)
        · show plugNrel k (predStage k g)
              (stageRel k (StageAt.top k.val) (Sum.inr (IXRelN.I j)))
              (Semiterm.lMap (stageHom k (StageAt.top k.val)) ∘ v) =
            Semiformula.nrel (stageRel k g (Sum.inr (IXRelN.I j)))
              (Semiterm.lMap (stageHom k g) ∘ v)
          rw [stageRel_I, dif_neg hjk, stageRel_I, dif_neg hjk]
          have hne : (Stage.top j : Stage n) ≠ Stage.top k :=
            fun e => hjk (Stage.top_inj.mp e)
          simp only [plugNrel, if_neg hne]
          show Semiformula.nrel _ _ = Semiformula.nrel _ _
          congr 1
          funext i
          exact lMap_stageHom_term k k _ _ (v i)
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and, plugI_and, ihφ,
      ihψ]
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or, plugI_or, ihφ, ihψ]
  | hall φ ih => rw [Semiformula.lMap_all, Semiformula.lMap_all, plugI_all, ih]
  | hexs φ ih => rw [Semiformula.lMap_exs, Semiformula.lMap_exs, plugI_exs, ih]

theorem unfold_eq_rew (A : Semisentence (LXIn n) 1) (a : StageAt k.val) (t : SyntacticTerm (LIinfN n)) :
    unfold A k a t =
      Rew.subst ![t] ▹ Semiformula.lMap (stageHom k a) (Rewriting.emb A : Semiformula (LXIn n) ℕ 1) := by
  rw [unfold, formAt, Semiformula.lMap_emb]

/-- **`φ(t, I_k^{≺γ})` is `φ(t, I_k^{≺Ω_{k+1}})` with the stage `I_k^{≺γ}` plugged in.** -/
theorem plugI_unfold (A : Semisentence (LXIn n) 1) (g : StageAt k.val) (t : SyntacticTerm (LIinfN n)) :
    plugI k (predStage k g) (unfold A k (StageAt.top k.val) t) = unfold A k g t := by
  rw [unfold_eq_rew, unfold_eq_rew, ← rew_plugI_stage k g (fixF_subst _), plugI_lMap_top]


end PlugForms
end IDn
end OrdinalAnalysis
