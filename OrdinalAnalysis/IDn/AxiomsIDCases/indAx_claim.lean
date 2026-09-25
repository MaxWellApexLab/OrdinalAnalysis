import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.opShape_rew
import OrdinalAnalysis.IDn.AxiomsIDCases.params_plugI
import OrdinalAnalysis.IDn.AxiomsIDCases.params_predStage
import OrdinalAnalysis.IDn.AxiomsIDCases.xFreeI_predOf
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_lMap_top
import OrdinalAnalysis.IDn.AxiomsIDCases.predOf_rew
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_subst_numI
import OrdinalAnalysis.IDn.AxiomsIDCases.unfold_top_eq
import OrdinalAnalysis.IDn.AxiomsIDCases.closure_inst
import OrdinalAnalysis.IDn.AxiomsIDCases.ThetaWNoteD_add_ofNat_eq_nadd
import OrdinalAnalysis.IDn.AxiomsIDCases.ThetaWNoteD_nadd_Omega_add_Omega
import OrdinalAnalysis.IDn.AxiomsIDCases.neg_ClF
import OrdinalAnalysis.IDn.AxiomsPA
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


variable {A : Fin n → Semisentence (LXIn n) 1} {H : Set ThetaWNoteD → Set ThetaWNoteD}


-- case_skeleton: generated header ends here

/-- Every `s : Stage n` has `atomRkStage s ≤ Omega (n-1)`, hence `omegaMul (atomRkStage s) =
Omega (n-1)` (a fixed point), always `≤` any bound already `≥ Omega (n-1)`. -/
private theorem omegaMul_atomRkStage_le {x : ThetaWNoteD} (hx : ThetaWNoteD.Omega (n - 1) ≤ x)
    (s : Stage n) : ThetaWNoteD.omegaMul (atomRkStage s) ≤ x := by
  refine le_trans ?_ hx
  calc ThetaWNoteD.omegaMul (atomRkStage s)
      ≤ ThetaWNoteD.omegaMul (ThetaWNoteD.Omega (n - 1)) :=
        ThetaWNoteD.omegaMul_le_omegaMul (le_trans (atomRkStage_mk_le_Omega s.lvl s.2)
          (Omega_le_Omega_of_le (by have := s.lvl.isLt; omega)))
    _ = ThetaWNoteD.Omega (n - 1) := ThetaWNoteD.omegaMul_Omega _

/-- `Omega (n-1)` is itself the value of some level's top stage (`k` witnesses `n ≥ 1`). -/
theorem omega_pred_mem_tops (k : Fin n) :
    ThetaWNoteD.Omega (n - 1) ∈ Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} := by
  have hk : k.val < n := k.isLt
  exact ⟨Stage.top ⟨n - 1, by omega⟩, ⟨⟨n - 1, by omega⟩, rfl⟩, Stage.val_top _⟩

/-- **The induction on stages** in the proof of Proposition 6.4:
`H[δ] ⊢^{ω·β + ω·δ}_0 ¬Cl(G), ¬I_k^{≺δ} s, G(s)` for every stage `δ ⪯ Ω_{k+1}` of level `k` and
every closed `s`, with `β = Ω_n ⊕ c`, `c` the complexity of `G`. -/
theorem indAx_claim (A : Fin n → Semisentence (LXIn n) 1) (hAb : FamilyLevelBounded A)
    (hA : PositiveIn k (A k)) (hX : ∀ j, XFreeL (A j)) (hH : ThetaWNoteD.NiceS H)
    (G : Semiformula (LIinfN n) ℕ 1) (hGf : G.freeVariables = ∅) (hGX : XFreeI G)
    (hGp : Stage.val '' params G ⊆ Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j}) :
    ∀ (δ : StageAt k.val) (s : SyntacticTerm (LIinfN n)), s.freeVariables = ∅ →
      IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H {δ.1})
        (ThetaWNoteD.omegaMul (ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) (ThetaWNoteD.ofNat G.complexity)) +
          ThetaWNoteD.omegaMul δ.1)
        [∼(ClF k (A k) G), nstageAt (⟨k, δ⟩ : Stage n) s, G/[s]] := by
  set β : ThetaWNoteD := ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) (ThetaWNoteD.ofNat G.complexity)
    with hβ
  set Φ : Semiformula (LIinfN n) ℕ 1 := plugI k (predOf G) (bodyTop k (A k)) with hΦ
  set cB : ℕ := (bodyTop k (A k)).complexity with hcB
  have hΩb : ThetaWNoteD.Omega (n - 1) ≤ ThetaWNoteD.omegaMul β := by
    rw [← ThetaWNoteD.omegaMul_Omega (n - 1)]
    exact ThetaWNoteD.omegaMul_le_omegaMul (ThetaWNoteD.le_nadd_left _ _)
  have hαω : ∀ x : ThetaWNoteD, omegaT ≤ ThetaWNoteD.omegaMul β + ThetaWNoteD.omegaMul x := fun x =>
    le_trans (le_of_lt (lt_of_lt_of_le (ThetaWNoteD.omegaPow_lt_Omega
      (ThetaWNoteD.one_lt_prin (p := (ThetaWNoteD.Omega (n - 1))) trivial)) hΩb)) (ThetaWNoteD.le_add_right' _ _)
  have hrkG : ∀ x : ThetaWNoteD,
      ThetaWNoteD.omegaMul (rk G) ≤ ThetaWNoteD.omegaMul β + ThetaWNoteD.omegaMul x := fun x =>
    le_trans (ThetaWNoteD.omegaMul_le_omegaMul (rk_le_Omega_nadd G)) (ThetaWNoteD.le_add_right' _ _)
  have hΩbound : ∀ x : ThetaWNoteD, ThetaWNoteD.Omega (n - 1) ≤ ThetaWNoteD.omegaMul β + ThetaWNoteD.omegaMul x :=
    fun x => le_trans hΩb (ThetaWNoteD.le_add_right' _ _)
  have hΦf : Φ.freeVariables = ∅ :=
    freeVariables_plugI k (predOf G) (freeVariables_predOf hGf) _ (freeVariables_bodyTop k (A k))
  have hΦX : XFreeI Φ :=
    xFreeI_plugI k (predOf G) (xFreeI_predOf hGX) _ (xFreeI_unfold_body (hX k) k (StageAt.top k.val))
  -- `bodyTop k (A k)` may mention *every* level's own top (`params_bodyTop`), not just level
  -- `n - 1`'s, so `Φ`'s parameters land in the wider "some level's top" set, not the singleton
  -- `hGp` bounds `G` by.
  have hΦp : Stage.val '' params Φ ⊆ Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} := by
    have hsub := Set.image_mono (params_plugI k (predOf G) (params_predOf G) (bodyTop k (A k)))
      (f := Stage.val)
    rw [Set.image_union] at hsub
    exact hsub.trans (Set.union_subset (Set.image_mono (params_bodyTop k (A k))) hGp)
  have hClp : Stage.val '' params (∼(ClF k (A k) G)) ⊆
      Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} := by
    rw [params_neg, ClF, params_all, params_or, params_neg, Set.image_union]
    exact Set.union_subset hΦp hGp
  suffices key : ∀ d : ThetaWNoteD, ∀ δ : StageAt k.val, δ.1 = d → ∀ s : SyntacticTerm (LIinfN n),
      s.freeVariables = ∅ →
      IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H {δ.1})
        (ThetaWNoteD.omegaMul β + ThetaWNoteD.omegaMul δ.1)
        [∼(ClF k (A k) G), nstageAt (⟨k, δ⟩ : Stage n) s, G/[s]] from
    fun δ => key δ.1 δ rfl
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
  intro δ hδ s hs
  subst hδ
  have hKδ := hH.adjoin {δ.1}
  have hδmem : δ.1 ∈ ThetaWNoteD.adjoin H {δ.1} ∅ := subset_adjoin_empty hH.isOperator _ rfl
  have hΩδ : ThetaWNoteD.Omega (n - 1) ∈ ThetaWNoteD.adjoin H {δ.1} ∅ := hKδ.Omega_mem (n - 1)
  have hOδtops : Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} ⊆
      ThetaWNoteD.adjoin H {δ.1} ∅ := by
    rintro _ ⟨s, ⟨j, rfl⟩, rfl⟩; rw [Stage.val_top]; exact hKδ.Omega_mem j.val
  have hαmem : ThetaWNoteD.omegaMul β + ThetaWNoteD.omegaMul δ.1 ∈ ThetaWNoteD.adjoin H {δ.1} ∅ :=
    hKδ.add_mem (hKδ.omegaMul_mem (hKδ.nadd_mem hΩδ (hKδ.ofNat_mem _)))
      (hKδ.omegaMul_mem hδmem)
  have hPδ : paramsVal [∼(ClF k (A k) G), nstageAt (⟨k, δ⟩ : Stage n) s, G/[s]] ⊆
      ThetaWNoteD.adjoin H {δ.1} ∅ := by
    rw [paramsVal_cons, paramsVal_cons, paramsVal_cons, paramsVal_nil, Set.union_empty]
    refine Set.union_subset (hClp.trans hOδtops) (Set.union_subset ?_ ?_)
    · rw [show params (nstageAt (⟨k, δ⟩ : Stage n) s) = {(⟨k, δ⟩ : Stage n)} from rfl,
        Set.image_singleton]
      exact Set.singleton_subset_iff.mpr hδmem
    · rw [params_subst]
      exact hGp.trans hOδtops
  refine .nstage (fun g => ThetaWNoteD.nadd (ThetaWNoteD.omegaMul β + ThetaWNoteD.omegaMul g.1)
    (ThetaWNoteD.ofNat (2 * cB + 2))) hαmem hPδ (List.mem_cons_of_mem _ List.mem_cons_self)
    (fun g hg => stage_sum_lt β hg _) (fun g hg => ?_)
  -- the premise for `γ ≺ δ`
  set K := ThetaWNoteD.adjoin (ThetaWNoteD.adjoin H {δ.1}) {g.1} with hK
  have hKn : ThetaWNoteD.NiceS K := hKδ.adjoin {g.1}
  have hgK : g.1 ∈ K ∅ := subset_adjoin_empty hKδ.isOperator _ rfl
  have hΩK : ThetaWNoteD.Omega (n - 1) ∈ K ∅ := hKn.Omega_mem (n - 1)
  have hO : {(ThetaWNoteD.Omega (n - 1))} ⊆ K ∅ := Set.singleton_subset_iff.mpr hΩK
  have hOKtops : Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} ⊆ K ∅ := by
    rintro _ ⟨s, ⟨j, rfl⟩, rfl⟩; rw [Stage.val_top]; exact hKn.Omega_mem j.val
  have hsubK : ThetaWNoteD.adjoin H {δ.1} ∅ ⊆ K ∅ := hKδ.isOperator.mono (Set.empty_subset _)
  have hαg : ∀ j : ℕ, ThetaWNoteD.nadd (ThetaWNoteD.omegaMul β + ThetaWNoteD.omegaMul g.1)
      (ThetaWNoteD.ofNat j) ∈ K ∅ := fun j =>
    hKn.nadd_mem (hKn.add_mem (hKn.omegaMul_mem (hKn.nadd_mem hΩK (hKn.ofNat_mem _)))
      (hKn.omegaMul_mem hgK)) (hKn.ofNat_mem j)
  have hαg0 : ThetaWNoteD.omegaMul β + ThetaWNoteD.omegaMul g.1 ∈ K ∅ := by
    have := hαg 0; rwa [ThetaWNoteD.ofNat_zero, ThetaWNoteD.nadd_zero] at this
  have hop : ∀ X, ThetaWNoteD.adjoin H {g.1} X ⊆ K X := by
    intro X
    rw [hK, ThetaWNoteD.adjoin_adjoin]
    exact adjoin_le_adjoin hH.isOperator Set.subset_union_right X
  have pl : ∀ Δ : Sequent (LIinfN n), (∀ χ ∈ Δ, Stage.val '' params χ ⊆ K ∅) → paramsVal Δ ⊆ K ∅ := by
    intro Δ h
    induction Δ with
    | nil => simp [paramsVal]
    | cons χ Δ ih' =>
      rw [paramsVal_cons]
      exact Set.union_subset (h χ List.mem_cons_self)
        (ih' (fun χ' hχ' => h χ' (List.mem_cons_of_mem _ hχ')))
  have pCl : Stage.val '' params (∼(ClF k (A k) G)) ⊆ K ∅ := hClp.trans hOKtops
  have pGu : ∀ u : SyntacticTerm (LIinfN n), Stage.val '' params (G/[u]) ⊆ K ∅ := fun u => by
    rw [params_subst]; exact hGp.trans hOKtops
  -- the hypothesis of Exercise 6.3, from the induction hypothesis at `γ`
  have hyp : ∀ u : SyntacticTerm (LIinfN n), u.freeVariables = ∅ →
      IDnDerivable A ThetaWNoteD.zero K (ThetaWNoteD.omegaMul β + ThetaWNoteD.omegaMul g.1)
        (∼(stageAt (⟨k, g⟩ : Stage n) u) :: G/[u] :: [∼(ClF k (A k) G)]) := by
    intro u hu
    refine (ih g.1 hg g rfl u hu).lift hKn.isOperator hop (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) (pl _ ?_)
    intro χ hχ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
    rcases hχ with rfl | rfl | rfl
    · rw [params_neg, show params (stageAt (⟨k, g⟩ : Stage n) u) = {(⟨k, g⟩ : Stage n)} from rfl,
        Set.image_singleton]
      exact Set.singleton_subset_iff.mpr hgK
    · exact pGu u
    · exact pCl
  have hUp : Stage.val '' params (unfold (A k) k (StageAt.top k.val) s) ⊆ K ∅ := by
    refine (Set.image_mono ?_).trans hOKtops
    intro x hx
    rcases params_unfold (A k) k (StageAt.top k.val) s hx with h | h
    · exact ⟨k, h⟩
    · exact h
  have E1 := ex63 k hAb hKn g G (hαω g.1) (fun {s} _ => omegaMul_atomRkStage_le (hΩbound g.1) s)
    hαg0 [∼(ClF k (A k) G)] (pl _ (by
      intro χ hχ; rw [List.mem_singleton.mp hχ]; exact pCl)) hgK (hGp.trans hOKtops) hyp cB
    (unfold (A k) k (StageAt.top k.val) s)
    (le_of_eq (by rw [unfold_top_eq, Semiformula.complexity_rew]))
    (opShape_unfold k hA (hX k) s) (freeVariables_unfold k (StageAt.top k.val) hs) hUp
  rw [plugI_unfold k, unfold_top_eq, ← rew_plugI_of k G (fixF_subst _)] at E1
  -- Lemma 6.1 for `G(s)`
  have T := taut (A := A) hAb hH (G/[s]) (freeVariables_subst_of_closed G hGf hs)
  rw [ThetaWNoteD.adjoin_eq_self hH.isOperator (by
    rw [params_subst]
    exact hGp.trans (by rintro _ ⟨s, ⟨j, rfl⟩, rfl⟩; rw [Stage.val_top]; exact hH.Omega_mem j.val)),
    rk_subst] at T
  set C : Proposition (LIinfN n) := Φ/[s] ⋏ ∼(G/[s]) with hC
  have pC : Stage.val '' params C ⊆ K ∅ := by
    rw [hC, params_and, params_neg, params_subst, Set.image_union]
    exact Set.union_subset (hΦp.trans hOKtops) (pGu s)
  have pUg : Stage.val '' params (∼(unfold (A k) k g s)) ⊆ K ∅ := by
    rw [params_neg]
    rintro _ ⟨x, hx, rfl⟩
    rcases params_unfold (A k) k g s hx with h | h
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      exact hgK
    · obtain ⟨j, rfl⟩ := h
      rw [Stage.val_top]
      exact hKn.Omega_mem j.val
  have pΔ : paramsVal [C, ∼(unfold (A k) k g s), ∼(ClF k (A k) G), G/[s]] ⊆ K ∅ := pl _ (by
    intro χ hχ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
    rcases hχ with rfl | rfl | rfl | rfl
    · exact pC
    · exact pUg
    · exact pCl
    · exact pGu s)
  have E2 : IDnDerivable A ThetaWNoteD.zero K
      (ThetaWNoteD.nadd (ThetaWNoteD.omegaMul β + ThetaWNoteD.omegaMul g.1) (ThetaWNoteD.ofNat (2 * cB + 1)))
      [C, ∼(unfold (A k) k g s), ∼(ClF k (A k) G), G/[s]] := by
    refine .and (hαg _) pΔ List.mem_cons_self
      (ThetaWNoteD.nadd_ofNat_lt_nadd_ofNat' _ (Nat.lt_succ_self _))
      (lt_of_le_of_lt (hrkG g.1) (ThetaWNoteD.lt_nadd_ofNat_succ _ _)) ?_ ?_
    · refine E1.weaken_seq hKn.isOperator (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
      rw [paramsVal_cons, params_subst]; exact Set.union_subset (hΦp.trans hOKtops) pΔ
    · refine T.lift hKn.isOperator
        (fun X => hH.isOperator.mono (Set.subset_union_right.trans Set.subset_union_right))
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
      rw [paramsVal_cons, params_neg]; exact Set.union_subset (pGu s) pΔ
  -- the numeral of the value of `s`
  have hCs : C = (Φ ⋏ ∼G)/[s] := by
    rw [hC]; simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg]
  have hsim : Sim C ((Φ ⋏ ∼G)/[numI (closedVal s)]) := by
    rw [hCs]
    exact sim_subst_numI (φ := Φ ⋏ ∼G) (by
      rw [Semiformula.freeVariables_and, Semiformula.freeVariables_not, hΦf, hGf]; rfl)
      (show XFreeI Φ ∧ XFreeI (∼G) from ⟨hΦX, (xFreeI_neg G).mpr hGX⟩) hs
  have E3 := E2.replace_head hX hKn.isOperator hsim
  have E4 : IDnDerivable A ThetaWNoteD.zero K
      (ThetaWNoteD.nadd (ThetaWNoteD.omegaMul β + ThetaWNoteD.omegaMul g.1) (ThetaWNoteD.ofNat (2 * cB + 2)))
      [∼(unfold (A k) k g s), ∼(ClF k (A k) G), G/[s]] :=
    .exs (closedVal s) (hαg _) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl
        · exact pUg
        · exact pCl
        · exact pGu s))
      (by rw [← neg_ClF]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      (lt_of_lt_of_le (ThetaWNoteD.ofNat_lt_omega _)
        (le_trans (hαω g.1) (ThetaWNoteD.le_nadd_left _ _)))
      (ThetaWNoteD.nadd_ofNat_lt_nadd_ofNat' _ (Nat.lt_succ_self _)) E3
  refine E4.weaken_seq hKn.isOperator (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
  refine pl _ ?_
  intro χ hχ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
  rcases hχ with rfl | rfl | rfl | rfl
  · exact pUg
  · exact pCl
  · rw [show params (nstageAt (⟨k, δ⟩ : Stage n) s) = {(⟨k, δ⟩ : Stage n)} from rfl,
      Set.image_singleton]
    exact Set.singleton_subset_iff.mpr (hsubK hδmem)
  · exact pGu s


end Induction
end IDn
end OrdinalAnalysis
