import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.params_plugI
import OrdinalAnalysis.IDn.AxiomsIDCases.plugI_subst_numI
import OrdinalAnalysis.IDn.AxiomsIDCases.unfold_top_eq
import OrdinalAnalysis.IDn.AxiomsIDCases.closure_inst
import OrdinalAnalysis.IDn.AxiomsIDCases.ThetaWNoteD_add_ofNat_eq_nadd
import OrdinalAnalysis.IDn.AxiomsIDCases.ThetaWNoteD_nadd_Omega_add_Omega
import OrdinalAnalysis.IDn.AxiomsIDCases.neg_ClF
import OrdinalAnalysis.IDn.AxiomsIDCases.indAx_claim
import OrdinalAnalysis.IDn.AxiomsPA
import OrdinalAnalysis.IDn.AxiomsLogic
import OrdinalAnalysis.IDn.EmbedHypsLogic

set_option autoImplicit false
namespace OrdinalAnalysis

variable {n : ℕ} (k : Fin n)


namespace IDn


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### Proposition 6.4, the axiom -/

section IndAxiom


variable {A : Fin n → Semisentence (LXIn n) 1} {H : Set ThetaWNoteD → Set ThetaWNoteD}


-- case_skeleton: generated header ends here

theorem indBody_inst (G : Semiformula (LIinfN n) ℕ 1) (m : ℕ) :
    (∼(IOmegaAt k (#0 : Semiterm (LIinfN n) ℕ 1)) ⋎ G)/[numI m] = ∼(IOmegaAt k (numI m)) ⋎ G/[numI m] := by
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    rew_IOmegaAt, Rew.subst_bvar, Matrix.cons_val_zero]

/-- **Freund, Proposition 6.4**, for the instance with the free variables replaced by
numerals: `H ⊢^{Ω_n·2 ⊕ 5}_0 Cl(G) → ∀x (I_k x → G(x))`. -/
theorem indAx_closed_derivable (A : Fin n → Semisentence (LXIn n) 1) (hAb : FamilyLevelBounded A)
    (hA : PositiveIn k (A k)) (hX : ∀ j, XFreeL (A j)) (hH : ThetaWNoteD.NiceS H)
    (G : Semiformula (LIinfN n) ℕ 1) (hGf : G.freeVariables = ∅) (hGX : XFreeI G)
    (hGp : Stage.val '' params G ⊆ Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j}) :
    IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat 5))
      [∼(ClF k (A k) G) ⋎ (∀¹ (∼(IOmegaAt k (#0 : Semiterm (LIinfN n) ℕ 1)) ⋎ G))] := by
  have hΩ : ThetaWNoteD.Omega (n - 1) ∈ H ∅ := hH.Omega_mem (n - 1)
  have hOtops : Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} ⊆ H ∅ := by
    rintro _ ⟨s, ⟨j, rfl⟩, rfl⟩; rw [Stage.val_top]; exact hH.Omega_mem j.val
  have hO : {(ThetaWNoteD.Omega (n - 1))} ⊆ H ∅ := Set.singleton_subset_iff.mpr hΩ
  have hmem : ∀ j, ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat j) ∈ H ∅ :=
    OmegaTwo_mem_al hH ∅
  have hlt : ∀ i j : ℕ, i < j → ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat i) <
      ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat j) := fun i j h =>
    ThetaWNoteD.nadd_ofNat_lt_nadd_ofNat' _ h
  have hone : ∀ j, ThetaWNoteD.one < ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat j) :=
    fun j => lt_of_lt_of_le (ThetaWNoteD.one_lt_prin (p := (ThetaWNoteD.Omega (n - 1))) trivial)
      (Omega_le_OmegaTwo_nadd j)
  have hO2 : OmegaTwo_al (n := n) < ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat 1) :=
    ThetaWNoteD.lt_nadd_ofNat_succ _ 0
  set Cl : Proposition (LIinfN n) := ∼(ClF k (A k) G) with hCl
  set V : Proposition (LIinfN n) := ∀¹ (∼(IOmegaAt k (#0 : Semiterm (LIinfN n) ℕ 1)) ⋎ G) with hV
  have pΦ : Stage.val '' params (plugI k (predOf G) (bodyTop k (A k))) ⊆
      Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} := by
    have hsub := Set.image_mono (params_plugI k (predOf G) (params_predOf G) (bodyTop k (A k)))
      (f := Stage.val)
    rw [Set.image_union] at hsub
    exact hsub.trans (Set.union_subset (Set.image_mono (params_bodyTop k (A k))) hGp)
  have pCl : Stage.val '' params Cl ⊆ Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} := by
    rw [hCl, params_neg, ClF, params_all, params_or, params_neg, Set.image_union]
    exact Set.union_subset pΦ hGp
  have pV : Stage.val '' params V ⊆ Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} := by
    rw [hV, params_all, params_or, params_neg, Set.image_union]
    exact Set.union_subset (by
      rw [show params (IOmegaAt k (#0 : Semiterm (LIinfN n) ℕ 1)) = {Stage.top k} from rfl,
        Set.image_singleton]
      exact Set.singleton_subset_iff.mpr ⟨Stage.top k, ⟨k, rfl⟩, rfl⟩)
      hGp
  have pM : Stage.val '' params (Cl ⋎ V) ⊆ Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} := by
    rw [params_or, Set.image_union]; exact Set.union_subset pCl pV
  have pGn : ∀ m, Stage.val '' params (G/[numI m]) ⊆
      Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} := fun m => by
    rw [params_subst]; exact hGp
  have pIn : ∀ m, Stage.val '' params (∼(IOmegaAt k (numI m))) ⊆
      Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} := fun m => by
    rw [params_neg, show params (IOmegaAt k (numI m)) = {Stage.top k} from rfl, Set.image_singleton]
    exact Set.singleton_subset_iff.mpr ⟨Stage.top k, ⟨k, rfl⟩, rfl⟩
  have pDn : ∀ m, Stage.val '' params (∼(IOmegaAt k (numI m)) ⋎ G/[numI m]) ⊆
      Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} := fun m => by
    rw [params_or, Set.image_union]
    exact Set.union_subset (pIn m) (pGn m)
  have pl : ∀ Δ : Sequent (LIinfN n),
      (∀ χ ∈ Δ, Stage.val '' params χ ⊆ Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j}) →
      paramsVal Δ ⊆ H ∅ := by
    intro Δ h
    induction Δ with
    | nil => simp [paramsVal]
    | cons χ Δ ih =>
      rw [paramsVal_cons]
      exact Set.union_subset ((h χ List.mem_cons_self).trans hOtops)
        (ih (fun χ' hχ' => h χ' (List.mem_cons_of_mem _ hχ')))
  -- the ω-rule on `∀x (¬I x ∨ G(x))`
  have p4 : IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat 3))
      [Cl, V] := by
    refine .all (fun _ => ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat 2)) (hmem 3)
      (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl
        · exact pCl
        · exact pV)) (List.mem_cons_of_mem _ List.mem_cons_self)
      (fun _ => hlt 2 3 (by omega)) (fun m => ?_)
    rw [indBody_inst]
    set D : Proposition (LIinfN n) := ∼(IOmegaAt k (numI m)) ⋎ G/[numI m] with hD
    -- the induction on stages, at `δ = Ω_{k+1}`
    have c0 := indAx_claim k A hAb hA hX hH G hGf hGX hGp (StageAt.top k.val) (numI m)
      (numI_freeVariables m)
    rw [StageAt.top_val, ThetaWNoteD.adjoin_eq_self hH.isOperator
      (Set.singleton_subset_iff.mpr (hH.Omega_mem k.val))] at c0
    have hOT2mem := OmegaTwo_mem_al (n := n) hH ∅ 0
    rw [ThetaWNoteD.ofNat_zero, ThetaWNoteD.nadd_zero] at hOT2mem
    have hle : ThetaWNoteD.omegaMul (ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1))
        (ThetaWNoteD.ofNat G.complexity)) + ThetaWNoteD.omegaMul (ThetaWNoteD.Omega k.val) ≤
        OmegaTwo_al (n := n) :=
      omegaMul_beta_add_Omega_le G.complexity k.val (by have := k.isLt; omega)
    have c0' := c0.mono_height hle hOT2mem
    have p1 : IDnDerivable A ThetaWNoteD.zero H (OmegaTwo_al (n := n))
        [G/[numI m], ∼(IOmegaAt k (numI m)), D, Cl, V] :=
      c0'.weaken_seq hH.isOperator (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl) (pl _ (by
          intro χ hχ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
          rcases hχ with rfl | rfl | rfl | rfl | rfl
          · exact pGn m
          · exact pIn m
          · exact pDn m
          · exact pCl
          · exact pV))
    have p2 : IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat 1))
        [∼(IOmegaAt k (numI m)), D, Cl, V] :=
      .orR (hmem 1) (pl _ (by
          intro χ hχ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
          rcases hχ with rfl | rfl | rfl | rfl
          · exact pIn m
          · exact pDn m
          · exact pCl
          · exact pV))
        (List.mem_cons_of_mem _ List.mem_cons_self) (hone 1) hO2 p1
    exact .orL (hmem 2) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl
        · exact pDn m
        · exact pCl
        · exact pV))
      List.mem_cons_self (hlt 1 2 (by omega)) p2
  -- the two disjunctions
  have p5 : IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat 4))
      [Cl, Cl ⋎ V] :=
    .orR (hmem 4) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl
        · exact pCl
        · exact pM))
      (List.mem_cons_of_mem _ List.mem_cons_self) (hone 4) (hlt 3 4 (by omega))
      (p4.weaken_seq hH.isOperator (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
        (pl _ (by
          intro χ hχ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
          rcases hχ with rfl | rfl | rfl
          · exact pV
          · exact pCl
          · exact pM)))
  exact .orL (hmem 5) (pl _ (by
      intro χ hχ; rw [List.mem_singleton.mp hχ]; exact pM))
    List.mem_cons_self (hlt 4 5 (by omega)) p5

/-- **The induction axiom** `indAxAt k (A k) F` (Freund, Proposition 6.4, and the universal
closure in the proof of Theorem 6.5), bridged to `Embed.lean`'s `AxDerivable`/`OmegaTwo`
convention via `axDerivable_of_al`. -/
theorem indAx_axiom (A : Fin n → Semisentence (LXIn n) 1) (hAb : FamilyLevelBounded A)
    (hA : PositiveIn k (A k)) (hX : ∀ j, XFreeL (A j)) (F : Semiformula (LXIn n) ℕ 1) :
    AxDerivable A (indAxAt k (A k) F) := by
  set ψ0 : Proposition (LXIn n) := (∀¹ (opAt k (A k) F 🡒 F)) 🡒 ∀¹ (Iat k #0 🡒 F) with hψ0
  refine axDerivable_of_al (σ := indAxAt k (A k) F) ?_
  refine axDerivable_of_le_al (5 + (0 + ψ0.fvSup))
    (ThetaWNoteD.nadd (ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat 5))
      (ThetaWNoteD.ofNat (0 + ψ0.fvSup)))
    (le_of_eq (by rw [ThetaWNoteD.nadd_assoc, ThetaWNoteD.ofNat_nadd_ofNat])) (fun H hH => ?_)
  have hΩ : ThetaWNoteD.Omega (n - 1) ∈ H ∅ := hH.Omega_mem (n - 1)
  have hO : {(ThetaWNoteD.Omega (n - 1))} ⊆ H ∅ := Set.singleton_subset_iff.mpr hΩ
  have hσTops : Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} ⊆ H ∅ := by
    rintro _ ⟨s, ⟨j, rfl⟩, rfl⟩; rw [Stage.val_top]; exact hH.Omega_mem j.val
  rw [indAxAt, emb_embK_univCl]
  refine allClosure_derivable hH.isOperator _
    (fun j => hH.nadd_mem (OmegaTwo_mem_al hH ∅ 5) (hH.ofNat_mem j))
    ((Set.image_mono (params_embK _)).trans hσTops) (fun w => ?_)
  rw [embK_fixitr_inst k, indAx_inst k (hX k)]
  set g : ℕ → ℕ := fun y => if hy : y < 0 + ψ0.fvSup then w ⟨y, hy⟩ else 0 with hg
  exact indAx_closed_derivable k A hAb hA hX hH (numSubst₁ g ▹ embK F) (freeVariables_numSubst₁ g _)
    ((xFreeI_rew (numSubst₁ g) _).mpr (xFreeI_embK F)) (by
      rw [params_rew]; exact Set.image_mono (params_embK F))


end IndAxiom
end IDn
end OrdinalAnalysis
