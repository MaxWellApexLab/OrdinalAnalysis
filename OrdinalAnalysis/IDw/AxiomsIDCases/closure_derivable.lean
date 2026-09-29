/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\closure_derivable.lean (level `k : Fin n` generalised to
   `k : ℕ`, ID_n -> ID_omega).  Freund, Proposition 6.2, uniform version: the ω-rule over
   `y = k̄`, and per level the transfer from `Jlev ⊤` to the level-`k` unfolding
   (`Transfer.transfer5_bwd`), the rule (Fix) at `I_k` and the rule (jlev) back to `Jlev ⊤`
   -- all cut-free. -/

import OrdinalAnalysis.IDw.AxiomsIDCases.closure_inst
import OrdinalAnalysis.IDw.Transfer
import OrdinalAnalysis.IDw.Embed

set_option autoImplicit false
namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting

/-! ### Proposition 6.2: the closure axiom -/

section Closure

variable {A : FormJ} {H : Set ThetaVNoteD → Set ThetaVNoteD}

/-- **One instance of the closure axiom**, cut-free: `⊢ ¬A_{k̄}(t; …) ∨ Jlev ⊤ (k̄, t)` at height
`Ω_{k+1} ⊕ (8 + 2c)`, from the congruence `Cong (OkBwd k) c E U` between the embedded body `E`
and the level-`k` unfolding `U`: `transfer5_bwd` gives `⊢ ¬E, U`, (Fix) turns `U` into `I_k t`,
(jlev) turns `I_k t` into `Jlev ⊤ (k̄, t)`, then two disjunction rules. -/
theorem closure_instance_derivable (hH : ThetaVNoteD.NiceS H) {c k : ℕ} {t : SyntacticTerm LIinfW}
    (ht : t.freeVariables = ∅)
    (hC : Transfer.Cong (Transfer.OkBwd k) c
      ((closureBody2 A)/[t, (Semiterm.numeral k : Semiterm LIinfW ℕ 0)])
      (unfoldW A k (StageAt.top k) t))
    (Γ : Sequent LIinfW) (hΓ : paramsVal Γ ⊆ H ∅) :
    IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat (8 + 2 * c)))
      ((∼((closureBody2 A)/[t, (Semiterm.numeral k : Semiterm LIinfW ℕ 0)]) ⋎
        jlevAt ⊤ (numI k) t) :: Γ) := by
  set E : Proposition LIinfW :=
    (closureBody2 A)/[t, (Semiterm.numeral k : Semiterm LIinfW ℕ 0)] with hE
  set U : Proposition LIinfW := unfoldW A k (StageAt.top k) t with hU
  set J : Proposition LIinfW := jlevAt ⊤ (numI k) t with hJ
  set I : Proposition LIinfW := IOmegaAt k t with hI
  set D : Proposition LIinfW := ∼E ⋎ J with hD
  have pE : Stage.val '' params E ⊆ H ∅ := by
    rw [hE, params_subst2, params_closureBody2, Set.image_empty]; exact Set.empty_subset _
  have pnE : Stage.val '' params (∼E) ⊆ H ∅ := by rw [params_neg]; exact pE
  have pU : Stage.val '' params U ⊆ H ∅ := by
    refine (Set.image_mono (params_unfoldW A k (StageAt.top k) t)).trans ?_
    rw [Set.image_singleton]
    exact Set.singleton_subset_iff.mpr (hH.Omega_mem k)
  have pJ : Stage.val '' params J ⊆ H ∅ := by
    rw [hJ, params_jlevAt, Set.image_empty]; exact Set.empty_subset _
  have pI : Stage.val '' params I ⊆ H ∅ := Transfer.omega_image hH k
  have pD : Stage.val '' params D ⊆ H ∅ := by
    rw [hD, params_or, Set.image_union]; exact Set.union_subset pnE pJ
  have hmem : ∀ j : ℕ, ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat j) ∈ H ∅ :=
    fun j => Transfer.nadd_Omega_mem hH k j
  have hlt : ∀ i j : ℕ, i < j → ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat i) <
      ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat j) := fun i j h =>
    ThetaVNoteD.nadd_ofNat_lt_nadd_ofNat' _ h
  have hone : ∀ j : ℕ, ThetaVNoteD.one <
      ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat j) := fun j =>
    lt_of_lt_of_le (Transfer.one_lt_Omega k) (ThetaVNoteD.le_nadd_left _ _)
  -- the transfer
  have hΓ1 : paramsVal (I :: J :: D :: Γ) ⊆ H ∅ := paramsVal_cons_sub pI
    (paramsVal_cons_sub pJ (paramsVal_cons_sub pD hΓ))
  have d0 := Transfer.transfer5_bwd (A := A) hH k hΓ1 hC pE pU
  have hP0 : paramsVal (U :: I :: J :: ∼E :: D :: Γ) ⊆ H ∅ := paramsVal_cons_sub pU
    (paramsVal_cons_sub pI (paramsVal_cons_sub pJ (paramsVal_cons_sub pnE
      (paramsVal_cons_sub pD hΓ))))
  have S0 : IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat (4 + 2 * c)))
      (U :: I :: J :: ∼E :: D :: Γ) :=
    d0.weaken_seq hH.1 (by
      intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hP0
  -- (Fix)
  have hP1 : paramsVal (I :: J :: ∼E :: D :: Γ) ⊆ H ∅ := paramsVal_cons_sub pI
    (paramsVal_cons_sub pJ (paramsVal_cons_sub pnE (paramsVal_cons_sub pD hΓ)))
  have S1 : IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat (5 + 2 * c)))
      (I :: J :: ∼E :: D :: Γ) :=
    .fix (hmem _) hP1 List.mem_cons_self (ThetaVNoteD.le_nadd_left _ _) (hlt (4 + 2 * c) (5 + 2 * c) (by omega)) S0
  -- (jlev)
  have hP2 : paramsVal (J :: ∼E :: D :: Γ) ⊆ H ∅ :=
    paramsVal_cons_sub pJ (paramsVal_cons_sub pnE (paramsVal_cons_sub pD hΓ))
  have S2 : IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat (6 + 2 * c)))
      (J :: ∼E :: D :: Γ) :=
    .jlev (hmem _) hP2 List.mem_cons_self (numI_freeVariables k) ht
      (by rw [termVal_numI]; exact WithTop.coe_lt_top k) (hlt (5 + 2 * c) (6 + 2 * c) (by omega))
      (by rw [termVal_numI]; exact S1)
  -- the two disjunctions
  have hP3 : paramsVal (∼E :: D :: Γ) ⊆ H ∅ := paramsVal_cons_sub pnE (paramsVal_cons_sub pD hΓ)
  have S3 : IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat (7 + 2 * c)))
      (∼E :: D :: Γ) :=
    .orR (hmem _) hP3 (List.mem_cons_of_mem _ List.mem_cons_self) (hone _)
      (hlt (6 + 2 * c) (7 + 2 * c) (by omega)) S2
  exact .orL (hmem _) (paramsVal_cons_sub pD hΓ) List.mem_cons_self (hlt (7 + 2 * c) (8 + 2 * c) (by omega)) S3

/-- **Freund, Proposition 6.2, uniform**: the embedded closure axiom `closureAxJ A`, cut-free at
height `Ω_ω` (`≤ Ω_ω · 2 ⊕ 0`), from the congruence `closureCong` of the `Cong` producer: the ω-rule over
`y = k̄` and over `x`, each instance `closure_instance_derivable`. -/
theorem closure_derivable (hA : PositiveP A) : AxDerivable A (closureAxJ A) := by
  set c : ℕ := Transfer.cdepth A with hcdef
  refine axDerivable_of_le A 0 ThetaVNoteD.OmegaW ?_ (fun H hH => ?_)
  · rw [ThetaVNoteD.ofNat_zero, ThetaVNoteD.add_zero]
    exact ThetaVNoteD.le_add_right _ _
  rw [emb_embK_closureAx]
  set ψ : Semiformula LIinfW ℕ 2 := ∼(closureBody2 A) ⋎ jlevAt ⊤ (#1) (#0) with hψ
  have hpψ : params ψ = ∅ := by
    rw [hψ, params_or, params_neg, params_closureBody2, params_jlevAt]; simp
  have pψ : ∀ k : ℕ, Stage.val '' params (∀¹ (ψ/[(#0 : Semiterm LIinfW ℕ 1),
      (Semiterm.numeral k : Semiterm LIinfW ℕ 1)])) ⊆ H ∅ := by
    intro k
    rw [params_all, params_subst2, hpψ, Set.image_empty]; exact Set.empty_subset _
  have pnil : paramsVal ([] : Sequent LIinfW) ⊆ H ∅ := by
    rw [paramsVal_nil]; exact Set.empty_subset _
  have hΓ0 : paramsVal [∀¹ ∀¹ ψ] ⊆ H ∅ := paramsVal_cons_sub (by
    rw [params_all, params_all, hpψ, Set.image_empty]; exact Set.empty_subset _) pnil
  have hΓk : ∀ k : ℕ, paramsVal [∀¹ (ψ/[(#0 : Semiterm LIinfW ℕ 1),
      (Semiterm.numeral k : Semiterm LIinfW ℕ 1)]), ∀¹ ∀¹ ψ] ⊆ H ∅ :=
    fun k => paramsVal_cons_sub (pψ k) hΓ0
  refine .all (φ := ∀¹ ψ)
    (fun k => ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat (9 + 2 * c)))
    hH.OmegaW_mem hΓ0 List.mem_cons_self
    (fun k => ThetaVNoteD.nadd_lt_prin ThetaVTerm.isPrin_OmegaW (ThetaVNoteD.Omega_lt_OmegaW k)
      (ThetaVNoteD.ofNat_lt_prin ThetaVTerm.isPrin_OmegaW _)) (fun k => ?_)
  rw [subst_all_numeral]
  refine .all (φ := ψ/[(#0 : Semiterm LIinfW ℕ 1), (Semiterm.numeral k : Semiterm LIinfW ℕ 1)])
    (fun _ => ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat (8 + 2 * c)))
    (Transfer.nadd_Omega_mem hH k _) (hΓk k)
    List.mem_cons_self (fun m => ThetaVNoteD.nadd_ofNat_lt_nadd_ofNat' _ (by omega))
    (fun m => ?_)
  rw [subst_numeral_comp, hψ, closure_inst]
  exact closure_instance_derivable hH (numI_freeVariables m) (closureCong hA k (numI_freeVariables m))
    _ (hΓk k)

end Closure
end IDw
end OrdinalAnalysis
