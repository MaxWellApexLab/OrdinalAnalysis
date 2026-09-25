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
import OrdinalAnalysis.IDn.AxiomsIDCases.opShape_rew
import OrdinalAnalysis.IDn.AxiomsIDCases.params_plugI
import OrdinalAnalysis.IDn.AxiomsIDCases.params_predStage
import OrdinalAnalysis.IDn.AxiomsIDCases.xFreeI_predOf
import OrdinalAnalysis.IDn.AxiomsLogic

set_option autoImplicit false
namespace OrdinalAnalysis

variable {n : ℕ} (k : Fin n)


namespace IDn


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### Exercise 6.3 -/

section Ex63


variable {A : Fin n → Semisentence (LXIn n) 1} {ρ : ThetaWNoteD} {H : Set ThetaWNoteD → Set ThetaWNoteD}


-- case_skeleton: generated header ends here

theorem plugI_subst_numI (P : Pred n) (hP : ∀ {n₁ n₂ : ℕ} {ω : Rew (LIinfN n) ℕ n₁ ℕ n₂}, FixF ω →
      ∀ s, ω ▹ P n₁ s = P n₂ (ω s)) (φ : Semiformula (LIinfN n) ℕ 1) (m : ℕ) :
    (plugI k P φ)/[numI m] = plugI k P (φ/[numI m]) :=
  rew_plugI k P P FixF (fun h => h.q) hP φ (fixF_subst _)

/-- **Freund, Exercise 6.3** (monotonicity of positive operator forms), read at a fixed level
`k : Fin n`: if `H ⊢^α_ρ Γ, ¬I_k^{≺γ}(s), G(s)` for every closed term `s`, then
`H ⊢^{α ⊕ 2c}_ρ Γ, ¬B(I_k^{≺γ}), B(G)` for every closed `B` of the shape of `A_k(t, I_k^{≺Ω_{k+1}})`
(`OpShape k`) of complexity at most `c`, where `B(P)` plugs `P` in for `I_k^{≺Ω_{k+1}}`.

Unlike `ID1`'s single-level statement, `B` may also mention *other* levels' stage atoms (in
either polarity, per `OpRel`/`OpNrel`'s `a.lvl ≠ k` branch: `stageHom k` sends every level
`j ≠ k` unconditionally to its own top, so `A_k` may legally mention `I_j` for `j ≠ k`). Such an
atom is untouched by `plugI k` (`predStage`/`predOf` only ever replace level `k`'s own top), so
closing that case falls back on Lemma 6.1 (`taut`) applied to the bare atom — which needs
`FamilyLevelBounded A` (`hAb`, absent from the one-level source, standard elsewhere in this
generalisation, e.g. `AxiomsLogic.taut`/`Elimination.elim_aux`) and a height bound on that atom's
own rank (`hΩ`, likewise new: `ω ⪯ α` alone bounds only the finitely-many `(V)`/`(W)` steps of the
induction on `c`, not an arbitrary other-level atom's `Ω_j + ω·a.val`-shaped rank). -/
theorem ex63 (hAb : FamilyLevelBounded A) (hH : ThetaWNoteD.NiceS H) (g : StageAt k.val)
    (G : Semiformula (LIinfN n) ℕ 1) {α : ThetaWNoteD} (hω : omegaT ≤ α)
    (hΩ : ∀ {s : Stage n}, s.lvl ≠ k → ThetaWNoteD.omegaMul (atomRkStage s) ≤ α)
    (hα : α ∈ H ∅) (Γ : Sequent (LIinfN n)) (hΓ : paramsVal Γ ⊆ H ∅)
    (hg : g.1 ∈ H ∅) (hG : Stage.val '' params G ⊆ H ∅)
    (hyp : ∀ u : SyntacticTerm (LIinfN n), u.freeVariables = ∅ →
      IDnDerivable A ρ H α (∼(stageAt (⟨k, g⟩ : Stage n) u) :: G/[u] :: Γ)) :
    ∀ (c : ℕ) (B : Proposition (LIinfN n)), B.complexity ≤ c → OpShape k B → B.freeVariables = ∅ →
      Stage.val '' params B ⊆ H ∅ →
      IDnDerivable A ρ H (ThetaWNoteD.nadd α (ThetaWNoteD.ofNat (2 * c)))
        (∼(plugI k (predStage k g) B) :: plugI k (predOf G) B :: Γ) := by
  have hθ : ∀ {m : ℕ} (χ : Semiformula (LIinfN n) ℕ m), Stage.val '' params χ ⊆ H ∅ →
      Stage.val '' params (plugI k (predStage k g) χ) ⊆ H ∅ := fun χ h => by
    have hsub := Set.image_mono
      (params_plugI k (predStage k g) (params_predStage k g) χ) (f := Stage.val)
    rw [Set.image_union, Set.image_singleton] at hsub
    exact hsub.trans (Set.union_subset h (Set.singleton_subset_iff.mpr hg))
  have hψ : ∀ {m : ℕ} (χ : Semiformula (LIinfN n) ℕ m), Stage.val '' params χ ⊆ H ∅ →
      Stage.val '' params (plugI k (predOf G) χ) ⊆ H ∅ := fun χ h => by
    have hsub := Set.image_mono (params_plugI k (predOf G) (params_predOf G) χ) (f := Stage.val)
    rw [Set.image_union] at hsub
    exact hsub.trans (Set.union_subset h hG)
  have hmem : ∀ j : ℕ, ThetaWNoteD.nadd α (ThetaWNoteD.ofNat j) ∈ H ∅ := fun j =>
    hH.nadd_mem hα (hH.ofNat_mem j)
  have hone : ∀ j, ThetaWNoteD.one < ThetaWNoteD.nadd α (ThetaWNoteD.ofNat j) := fun j =>
    lt_of_lt_of_le (by rw [← ThetaWNoteD.ofNat_one]; exact ThetaWNoteD.ofNat_lt_omega 1)
      (le_trans hω (ThetaWNoteD.le_nadd_left _ _))
  have hnum : ∀ (m' j : ℕ), ThetaWNoteD.ofNat m' < ThetaWNoteD.nadd α (ThetaWNoteD.ofNat j) := fun m' j =>
    lt_of_lt_of_le (ThetaWNoteD.ofNat_lt_omega m') (le_trans hω (ThetaWNoteD.le_nadd_left _ _))
  have hlt : ∀ i j : ℕ, i < j → ThetaWNoteD.nadd α (ThetaWNoteD.ofNat i) <
      ThetaWNoteD.nadd α (ThetaWNoteD.ofNat j) := fun i j h => ThetaWNoteD.nadd_ofNat_lt_nadd_ofNat' _ h
  have hΘ := plugI_subst_numI k (predStage k g) (fun {_ _} {ω} _ s => predStage_rew k g ω s)
  have hΨ := plugI_subst_numI k (predOf G) (fun h s => predOf_rew G h s)
  have pl : ∀ Δ : Sequent (LIinfN n), (∀ χ ∈ Δ, Stage.val '' params χ ⊆ H ∅) →
      paramsVal Δ ⊆ H ∅ := by
    intro Δ h x hx
    obtain ⟨s, ⟨χ, hχ, hs⟩, rfl⟩ := hx
    exact h χ hχ ⟨s, hs, rfl⟩
  have plΓ : ∀ χ ∈ Γ, Stage.val '' params χ ⊆ H ∅ := fun χ hχ =>
    (Set.image_mono (params_subset_paramsList hχ) (f := Stage.val)).trans hΓ
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro B hc hS hf hp
  -- the sequent and its parameters
  have pseq : ∀ χ ∈ (∼(plugI k (predStage k g) B) :: plugI k (predOf G) B :: Γ),
      Stage.val '' params χ ⊆ H ∅ := by
    intro χ hχ
    simp only [List.mem_cons] at hχ
    rcases hχ with rfl | rfl | hχ
    · rw [params_neg]; exact hθ B hp
    · exact hψ B hp
    · exact plΓ χ hχ
  have hP := pl _ pseq
  revert hc hS hf hp pseq hP
  cases B using cases0 with
  | hverum =>
    intro _ _ _ _ _ hP
    exact .verum (hmem _) hP (List.mem_cons_of_mem _ List.mem_cons_self)
  | hfalsum =>
    intro _ _ _ _ _ hP
    exact .verum (hmem _) hP List.mem_cons_self
  | hrel j r v =>
    intro _ hS hf hp _ hP
    rcases r with r | r
    · -- an arithmetic literal: one of the two is true
      have hl : IsArithLit (Semiformula.rel (Sum.inl r : (LIinfN n).Rel j) v) :=
        ⟨j, r, v, Or.inl rfl, freeVariables_rel_arg hf⟩
      by_cases ht : TrueN (Semiformula.rel (Sum.inl r : (LIinfN n).Rel j) v)
      · exact .literal (hmem _) hP ⟨hl, ht⟩ (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact .literal (hmem _) hP ⟨hl.neg, (trueN_neg _).mpr ht⟩ List.mem_cons_self
    · cases r with
      | X => exact hS.elim
      | stage a =>
        rcases hS with hlvl | rfl
        · -- a stage atom of a *different* level: untouched by either plugging, closed by
          -- Lemma 6.1 (Freund's Lemma 6.1 is level-free: any closed proposition is `taut`)
          have hane : a ≠ Stage.top k := Stage.ne_top_of_lvl_ne hlvl
          have e1 : plugI k (predStage k g)
              (Semiformula.rel (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v) =
              Semiformula.rel (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v := by
            rw [plugI_rel k (predStage k g) (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v]
            simp only [plugRel, if_neg hane]
          have e2 : plugI k (predOf G)
              (Semiformula.rel (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v) =
              Semiformula.rel (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v := by
            rw [plugI_rel k (predOf G) (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v]
            simp only [plugRel, if_neg hane]
          rw [e1, e2] at hP ⊢
          have T := taut hAb hH
            (Semiformula.rel (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v) hf
          rw [ThetaWNoteD.adjoin_eq_self hH.isOperator hp] at T
          refine (T.mono_rank (ThetaWNoteD.zero_le' ρ)).weaken hH.isOperator ?_
            (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto)
            (hmem _) hP
          rw [rk_rel (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v]
          exact le_trans (hΩ hlvl) (ThetaWNoteD.le_nadd_left _ _)
        · -- `a = Stage.top k`: the atom `I_k^{≺Ω_{k+1}} s`, the hypothesis at `s`
          have e1 : plugI k (predStage k g)
              (Semiformula.rel (Sum.inr (IInfRelN.stage (Stage.top k)) : (LIinfN n).Rel 1) v) =
              stageAt (⟨k, g⟩ : Stage n) (v 0) := by
            rw [plugI_rel k (predStage k g)
              (Sum.inr (IInfRelN.stage (Stage.top k)) : (LIinfN n).Rel 1) v]
            simp only [plugRel, if_true, predStage]
          have e2 : plugI k (predOf G)
              (Semiformula.rel (Sum.inr (IInfRelN.stage (Stage.top k)) : (LIinfN n).Rel 1) v) =
              G/[v 0] := by
            rw [plugI_rel k (predOf G)
              (Sum.inr (IInfRelN.stage (Stage.top k)) : (LIinfN n).Rel 1) v]
            simp only [plugRel, if_true, predOf]
          rw [e1, e2]
          exact (hyp (v 0) (freeVariables_rel_arg hf 0)).mono_height
            (ThetaWNoteD.le_nadd_left _ _) (hmem _)
  | hnrel j r v =>
    intro _ hS hf hp _ hP
    rcases r with r | r
    · have hl : IsArithLit (Semiformula.nrel (Sum.inl r : (LIinfN n).Rel j) v) :=
        ⟨j, r, v, Or.inr rfl, freeVariables_nrel_arg hf⟩
      by_cases ht : TrueN (Semiformula.nrel (Sum.inl r : (LIinfN n).Rel j) v)
      · exact .literal (hmem _) hP ⟨hl, ht⟩ (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact .literal (hmem _) hP ⟨hl.neg, (trueN_neg _).mpr ht⟩ List.mem_cons_self
    · cases r with
      | X => exact hS.elim
      | stage a =>
        -- `OpNrel` never permits a negated atom of level `k`'s own top (positivity): `hS`
        -- directly gives `a.lvl ≠ k`, closed exactly as the `hrel` "other level" branch
        have hane : a ≠ Stage.top k := Stage.ne_top_of_lvl_ne hS
        have e1 : plugI k (predStage k g)
            (Semiformula.nrel (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v) =
            Semiformula.nrel (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v := by
          rw [plugI_nrel k (predStage k g) (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v]
          simp only [plugNrel, if_neg hane]
        have e2 : plugI k (predOf G)
            (Semiformula.nrel (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v) =
            Semiformula.nrel (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v := by
          rw [plugI_nrel k (predOf G) (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v]
          simp only [plugNrel, if_neg hane]
        rw [e1, e2] at hP ⊢
        have T := taut hAb hH
          (Semiformula.nrel (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v) hf
        rw [ThetaWNoteD.adjoin_eq_self hH.isOperator hp] at T
        refine (T.mono_rank (ThetaWNoteD.zero_le' ρ)).weaken hH.isOperator ?_
          (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto)
          (hmem _) hP
        rw [rk_nrel (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel 1) v]
        exact le_trans (hΩ hS) (ThetaWNoteD.le_nadd_left _ _)
  | hand B₀ B₁ =>
    intro hc hS hf hp pseq hP
    rw [Semiformula.complexity_and] at hc
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [Semiformula.freeVariables_and, Finset.union_eq_empty] at hf
    rw [params_and, Set.image_union] at hp
    have hp0 : Stage.val '' params B₀ ⊆ H ∅ := Set.subset_union_left.trans hp
    have hp1 : Stage.val '' params B₁ ⊆ H ∅ := Set.subset_union_right.trans hp
    set X₀ := plugI k (predStage k g) B₀
    set X₁ := plugI k (predStage k g) B₁
    set Y₀ := plugI k (predOf G) B₀
    set Y₁ := plugI k (predOf G) B₁
    have eX : ∼(plugI k (predStage k g) (B₀ ⋏ B₁)) = ∼X₀ ⋎ ∼X₁ := by simp [X₀, X₁]
    have eY : plugI k (predOf G) (B₀ ⋏ B₁) = Y₀ ⋏ Y₁ := rfl
    rw [eX, eY] at hP ⊢
    have step : ∀ (Xi Yi : Proposition (LIinfN n)), Stage.val '' params Xi ⊆ H ∅ →
        Stage.val '' params Yi ⊆ H ∅ →
        IDnDerivable A ρ H (ThetaWNoteD.nadd α (ThetaWNoteD.ofNat (2 * c'))) (∼Xi :: Yi :: Γ) →
        IDnDerivable A ρ H (ThetaWNoteD.nadd α (ThetaWNoteD.ofNat (2 * c')))
          (∼Xi :: Yi :: (∼X₀ ⋎ ∼X₁) :: (Y₀ ⋏ Y₁) :: Γ) := by
      intro Xi Yi hXi hYi d
      refine d.weaken_seq hH.isOperator (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        tauto) (pl _ ?_)
      intro χ hχ
      simp only [List.mem_cons] at hχ
      rcases hχ with rfl | rfl | rfl | rfl | hχ
      · rw [params_neg]; exact hXi
      · exact hYi
      · rw [params_or, Set.image_union, params_neg, params_neg]
        exact Set.union_subset (hθ B₀ hp0) (hθ B₁ hp1)
      · rw [params_and, Set.image_union]; exact Set.union_subset (hψ B₀ hp0) (hψ B₁ hp1)
      · exact plΓ χ hχ
    have d0 := step X₀ Y₀ (hθ B₀ hp0) (hψ B₀ hp0)
      (ih c' (by omega) B₀ (by omega) hS.1 hf.1 hp0)
    have d1 := step X₁ Y₁ (hθ B₁ hp1) (hψ B₁ hp1)
      (ih c' (by omega) B₁ (by omega) hS.2 hf.2 hp1)
    have pY : ∀ Yi, Stage.val '' params Yi ⊆ H ∅ →
        paramsVal (Yi :: (∼X₀ ⋎ ∼X₁) :: (Y₀ ⋏ Y₁) :: Γ) ⊆ H ∅ := by
      intro Yi hYi
      rw [paramsVal_cons]; exact Set.union_subset hYi hP
    have e0 : IDnDerivable A ρ H (ThetaWNoteD.nadd α (ThetaWNoteD.ofNat (2 * c' + 1)))
        (Y₀ :: (∼X₀ ⋎ ∼X₁) :: (Y₀ ⋏ Y₁) :: Γ) :=
      .orL (hmem _) (pY Y₀ (hψ B₀ hp0)) (List.mem_cons_of_mem _ List.mem_cons_self)
        (hlt _ _ (by omega)) d0
    have e1 : IDnDerivable A ρ H (ThetaWNoteD.nadd α (ThetaWNoteD.ofNat (2 * c' + 1)))
        (Y₁ :: (∼X₀ ⋎ ∼X₁) :: (Y₀ ⋏ Y₁) :: Γ) :=
      .orR (hmem _) (pY Y₁ (hψ B₁ hp1)) (List.mem_cons_of_mem _ List.mem_cons_self) (hone _)
        (hlt _ _ (by omega)) d1
    exact .and (hmem _) hP (List.mem_cons_of_mem _ List.mem_cons_self) (hlt _ _ (by omega))
      (hlt _ _ (by omega)) e0 e1
  | hor B₀ B₁ =>
    intro hc hS hf hp pseq hP
    rw [Semiformula.complexity_or] at hc
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [Semiformula.freeVariables_or, Finset.union_eq_empty] at hf
    rw [params_or, Set.image_union] at hp
    have hp0 : Stage.val '' params B₀ ⊆ H ∅ := Set.subset_union_left.trans hp
    have hp1 : Stage.val '' params B₁ ⊆ H ∅ := Set.subset_union_right.trans hp
    set X₀ := plugI k (predStage k g) B₀
    set X₁ := plugI k (predStage k g) B₁
    set Y₀ := plugI k (predOf G) B₀
    set Y₁ := plugI k (predOf G) B₁
    have eX : ∼(plugI k (predStage k g) (B₀ ⋎ B₁)) = ∼X₀ ⋏ ∼X₁ := by simp [X₀, X₁]
    have eY : plugI k (predOf G) (B₀ ⋎ B₁) = Y₀ ⋎ Y₁ := rfl
    rw [eX, eY] at hP ⊢
    have step : ∀ (Xi Yi : Proposition (LIinfN n)), Stage.val '' params Xi ⊆ H ∅ →
        Stage.val '' params Yi ⊆ H ∅ →
        IDnDerivable A ρ H (ThetaWNoteD.nadd α (ThetaWNoteD.ofNat (2 * c'))) (∼Xi :: Yi :: Γ) →
        IDnDerivable A ρ H (ThetaWNoteD.nadd α (ThetaWNoteD.ofNat (2 * c')))
          (Yi :: ∼Xi :: (∼X₀ ⋏ ∼X₁) :: (Y₀ ⋎ Y₁) :: Γ) := by
      intro Xi Yi hXi hYi d
      refine d.weaken_seq hH.isOperator (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        tauto) (pl _ ?_)
      intro χ hχ
      simp only [List.mem_cons] at hχ
      rcases hχ with rfl | rfl | rfl | rfl | hχ
      · exact hYi
      · rw [params_neg]; exact hXi
      · rw [params_and, Set.image_union, params_neg, params_neg]
        exact Set.union_subset (hθ B₀ hp0) (hθ B₁ hp1)
      · rw [params_or, Set.image_union]; exact Set.union_subset (hψ B₀ hp0) (hψ B₁ hp1)
      · exact plΓ χ hχ
    have d0 := step X₀ Y₀ (hθ B₀ hp0) (hψ B₀ hp0) (ih c' (by omega) B₀ (by omega) hS.1 hf.1 hp0)
    have d1 := step X₁ Y₁ (hθ B₁ hp1) (hψ B₁ hp1) (ih c' (by omega) B₁ (by omega) hS.2 hf.2 hp1)
    have pX : ∀ Xi, Stage.val '' params Xi ⊆ H ∅ →
        paramsVal (∼Xi :: (∼X₀ ⋏ ∼X₁) :: (Y₀ ⋎ Y₁) :: Γ) ⊆ H ∅ := by
      intro Xi hXi
      rw [paramsVal_cons, params_neg]; exact Set.union_subset hXi hP
    have e0 : IDnDerivable A ρ H (ThetaWNoteD.nadd α (ThetaWNoteD.ofNat (2 * c' + 1)))
        (∼X₀ :: (∼X₀ ⋏ ∼X₁) :: (Y₀ ⋎ Y₁) :: Γ) :=
      .orL (hmem _) (pX X₀ (hθ B₀ hp0))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (hlt _ _ (by omega)) d0
    have e1 : IDnDerivable A ρ H (ThetaWNoteD.nadd α (ThetaWNoteD.ofNat (2 * c' + 1)))
        (∼X₁ :: (∼X₀ ⋏ ∼X₁) :: (Y₀ ⋎ Y₁) :: Γ) :=
      .orR (hmem _) (pX X₁ (hθ B₁ hp1))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (hone _)
        (hlt _ _ (by omega)) d1
    exact .and (hmem _) hP List.mem_cons_self (hlt _ _ (by omega)) (hlt _ _ (by omega)) e0 e1
  | hall φ =>
    intro hc hS hf hp pseq hP
    rw [Semiformula.complexity_all] at hc
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [Semiformula.freeVariables_all] at hf
    rw [params_all] at hp
    have eX : ∼(plugI k (predStage k g) (∀¹ φ)) = ∃¹ (∼plugI k (predStage k g) φ) := by simp
    have eY : plugI k (predOf G) (∀¹ φ) = ∀¹ plugI k (predOf G) φ := rfl
    rw [eX, eY] at hP ⊢
    refine .all (fun _ => ThetaWNoteD.nadd α (ThetaWNoteD.ofNat (2 * c' + 1))) (hmem _) hP
      (List.mem_cons_of_mem _ List.mem_cons_self)
      (fun _ => hlt (2 * c' + 1) (2 * (c' + 1)) (by omega)) (fun m' => ?_)
    have hpn : Stage.val '' params (φ/[numI m']) ⊆ H ∅ := by rw [params_subst]; exact hp
    have d := ih c' (by omega) (φ/[numI m']) (by rw [Semiformula.complexity_rew]; omega)
      (opShape_rew k _ hS) (freeVariables_subst_numI φ hf m') hpn
    rw [← hΘ, ← hΨ] at d
    have hneg : (∼plugI k (predStage k g) φ)/[numI m'] =
        ∼((plugI k (predStage k g) φ)/[numI m']) := by simp
    refine .exs (α₀ := ThetaWNoteD.nadd α (ThetaWNoteD.ofNat (2 * c'))) m' (hmem _) ?_
      (List.mem_cons_of_mem _ List.mem_cons_self) (hnum _ _)
      (hlt (2 * c') (2 * c' + 1) (by omega)) ?_
    · rw [paramsVal_cons, params_subst]
      exact Set.union_subset (hψ φ hp) hP
    · rw [hneg]
      refine d.weaken_seq hH.isOperator (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        tauto) ?_
      rw [paramsVal_cons, paramsVal_cons, params_neg, params_subst, params_subst]
      exact Set.union_subset (hθ φ hp) (Set.union_subset (hψ φ hp) hP)
  | hexs φ =>
    intro hc hS hf hp pseq hP
    rw [Semiformula.complexity_exs] at hc
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [Semiformula.freeVariables_exs] at hf
    rw [params_exs] at hp
    have eX : ∼(plugI k (predStage k g) (∃¹ φ)) = ∀¹ (∼plugI k (predStage k g) φ) := by simp
    have eY : plugI k (predOf G) (∃¹ φ) = ∃¹ plugI k (predOf G) φ := rfl
    rw [eX, eY] at hP ⊢
    refine .all (fun _ => ThetaWNoteD.nadd α (ThetaWNoteD.ofNat (2 * c' + 1))) (hmem _) hP
      List.mem_cons_self (fun _ => hlt (2 * c' + 1) (2 * (c' + 1)) (by omega)) (fun m' => ?_)
    have hpn : Stage.val '' params (φ/[numI m']) ⊆ H ∅ := by rw [params_subst]; exact hp
    have d := ih c' (by omega) (φ/[numI m']) (by rw [Semiformula.complexity_rew]; omega)
      (opShape_rew k _ hS) (freeVariables_subst_numI φ hf m') hpn
    rw [← hΘ, ← hΨ] at d
    have hneg : (∼plugI k (predStage k g) φ)/[numI m'] =
        ∼((plugI k (predStage k g) φ)/[numI m']) := by simp
    rw [hneg]
    refine .exs (α₀ := ThetaWNoteD.nadd α (ThetaWNoteD.ofNat (2 * c'))) m' (hmem _) ?_
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (hnum _ _) (hlt (2 * c') (2 * c' + 1) (by omega)) ?_
    · rw [paramsVal_cons, params_neg, params_subst]
      exact Set.union_subset (hθ φ hp) hP
    · refine d.weaken_seq hH.isOperator (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        tauto) ?_
      rw [paramsVal_cons, paramsVal_cons, params_neg, params_subst, params_subst]
      exact Set.union_subset (hψ φ hp) (Set.union_subset (hθ φ hp) hP)


end Ex63
end IDn
end OrdinalAnalysis
