import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.unfold_top_eq
import OrdinalAnalysis.IDn.AxiomsIDCases.closure_inst
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


/-! ### Proposition 6.2: the closure axiom -/

section Closure


variable {A : Fin n → Semisentence (LXIn n) 1}


-- case_skeleton: generated header ends here

/-- Every parameter of a formula built from `bodyTop k (A k)`/`IOmegaAt k` alone (the shapes
occurring in this proof) is some level's top stage, whose `.val` is that level's `Omega`,
always in `H ∅` for a nice `H` (`NiceS.Omega_mem`, at *any* level, not just the top one). -/
private theorem stageVal_tops_subset {H : Set ThetaWNoteD → Set ThetaWNoteD}
    (hH : ThetaWNoteD.NiceS H) :
    Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} ⊆ H ∅ := by
  rintro _ ⟨s, ⟨j, rfl⟩, rfl⟩
  rw [Stage.val_top]
  exact hH.Omega_mem j.val

/-- **Freund, Proposition 6.2**: the embedded closure axiom `∀x (A(x, I) → I x)` is derivable,
cut-free, at height `Ω_n · 2 ⊕ m` (`AxiomsLogic`'s convention, `AxDerivable_al`) for every nice
operator. -/
theorem closure_derivable (A : Fin n → Semisentence (LXIn n) 1) (hAb : FamilyLevelBounded A)
    (hX : ∀ j, XFreeL (A j)) :
    AxDerivable_al A (closureAxAt k (A k)) := by
  set c : ℕ := (bodyTop k (A k)).complexity with hc
  refine axDerivable_of_le_al (c + 1)
    (ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) (ThetaWNoteD.omegaMul (ThetaWNoteD.ofNat (c + 1))))
    (nadd_Omega_le_OmegaTwo (omegaMul_ofNat_lt_Omega (c + 1)) (c + 1)) (fun H hH => ?_)
  have hΩ : ThetaWNoteD.Omega (n - 1) ∈ H ∅ := hH.Omega_mem (n - 1)
  have hO : Stage.val '' {s : Stage n | ∃ j : Fin n, s = Stage.top j} ⊆ H ∅ :=
    stageVal_tops_subset hH
  set h2 : ThetaWNoteD := ThetaWNoteD.succ (ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1))
    (ThetaWNoteD.omegaMul (ThetaWNoteD.ofNat c))) with hh2
  have hmem : ∀ j, ThetaWNoteD.nadd h2 (ThetaWNoteD.ofNat j) ∈ H ∅ := fun j =>
    hH.nadd_mem (hH.succ_mem (hH.nadd_mem hΩ (hH.omegaMul_mem (hH.ofNat_mem c)))) (hH.ofNat_mem j)
  have hlt : ∀ i j : ℕ, i < j → ThetaWNoteD.nadd h2 (ThetaWNoteD.ofNat i) <
      ThetaWNoteD.nadd h2 (ThetaWNoteD.ofNat j) := fun i j h => ThetaWNoteD.nadd_ofNat_lt_nadd_ofNat' _ h
  have hone : ∀ j, ThetaWNoteD.one < ThetaWNoteD.nadd h2 (ThetaWNoteD.ofNat j) := fun j =>
    lt_of_lt_of_le (ThetaWNoteD.one_lt_prin (p := (ThetaWNoteD.Omega (n - 1))) trivial)
      (le_trans (le_trans (ThetaWNoteD.le_nadd_left _ _) (le_of_lt (ThetaWNoteD.lt_succ _)))
        (ThetaWNoteD.le_nadd_left _ _))
  set M : Proposition (LIinfN n) :=
    ∀¹ (∼(bodyTop k (A k)) ⋎ IOmegaAt k (#0 : Semiterm (LIinfN n) ℕ 1)) with hM
  have pbody : Stage.val '' params (bodyTop k (A k)) ⊆ H ∅ :=
    (Set.image_mono (params_bodyTop k (A k))).trans hO
  have pM : Stage.val '' params M ⊆ H ∅ := by
    rw [hM, params_all, params_or, params_neg, Set.image_union]
    refine Set.union_subset pbody ?_
    rw [show params (IOmegaAt k (#0 : Semiterm (LIinfN n) ℕ 1)) = {Stage.top k} from rfl,
      Set.image_singleton, Stage.val_top]
    exact Set.singleton_subset_iff.mpr (hH.Omega_mem k.val)
  have pl : ∀ Δ : Sequent (LIinfN n), (∀ χ ∈ Δ, Stage.val '' params χ ⊆ H ∅) →
      paramsVal Δ ⊆ H ∅ := by
    intro Δ h
    induction Δ with
    | nil => simp [paramsVal]
    | cons χ Δ ih =>
      rw [paramsVal_cons]
      exact Set.union_subset (h χ List.mem_cons_self)
        (ih (fun χ' hχ' => h χ' (List.mem_cons_of_mem _ hχ')))
  have hfin : ThetaWNoteD.nadd h2 (ThetaWNoteD.ofNat 2) <
      ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) (ThetaWNoteD.omegaMul (ThetaWNoteD.ofNat (c + 1))) := by
    rw [hh2, ← ThetaWNoteD.nadd_ofNat_one, ThetaWNoteD.nadd_assoc, ThetaWNoteD.nadd_assoc,
      ThetaWNoteD.ofNat_nadd_ofNat]
    exact ThetaWNoteD.nadd_lt_nadd_right _
      (ThetaWNoteD.omegaMul_nadd_ofNat_lt (ThetaWNoteD.ofNat_lt_ofNat (Nat.lt_succ_self c)) _)
  rw [emb_embK_closureAx k (hX k)]
  refine .all (fun _ => ThetaWNoteD.nadd h2 (ThetaWNoteD.ofNat 2))
    (hH.nadd_mem hΩ (hH.omegaMul_mem (hH.ofNat_mem _))) (by
      rw [paramsVal_cons, paramsVal_nil, Set.union_empty]; exact pM) List.mem_cons_self
    (fun _ => hfin) (fun m' => ?_)
  rw [closure_inst k (A k) m']
  set U : Proposition (LIinfN n) := unfold (A k) k (StageAt.top k.val) (numI m') with hU
  set Q : Proposition (LIinfN n) := IOmegaAt k (numI m') with hQ
  have pU : Stage.val '' params U ⊆ H ∅ := by
    refine (Set.image_mono ?_).trans hO
    intro s hs
    rcases params_unfold (A k) k (StageAt.top k.val) (numI m') hs with h | h
    · exact ⟨k, h⟩
    · exact h
  have pQ : Stage.val '' params Q ⊆ H ∅ := by
    rw [hQ, show params (IOmegaAt k (numI m')) = {Stage.top k} from rfl, Set.image_singleton,
      Stage.val_top]
    exact Set.singleton_subset_iff.mpr (hH.Omega_mem k.val)
  have pM' : Stage.val '' params M ⊆ H ∅ := pM
  have pD : Stage.val '' params (∼U ⋎ Q) ⊆ H ∅ := by
    rw [params_or, params_neg, Set.image_union]; exact Set.union_subset pU pQ
  have hcU : U.complexity = c := by rw [hU, unfold_top_eq, Semiformula.complexity_rew]
  -- Lemma 6.1 for `A(m'̄, I^{≺Ω})`
  have t0 := taut (A := A) hAb hH U (freeVariables_unfold k (StageAt.top k.val) (numI_freeVariables m'))
  rw [ThetaWNoteD.adjoin_eq_self hH.isOperator pU] at t0
  have hrk : ThetaWNoteD.omegaMul (rk U) < h2 := by
    refine lt_of_le_of_lt ?_ (ThetaWNoteD.lt_succ _)
    have := omegaMul_rk_le U
    rwa [hcU] at this
  have t1 : IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.omegaMul (rk U))
      [U, ∼U, Q, ∼U ⋎ Q, M] :=
    t0.weaken_seq hH.isOperator (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
      (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl | rfl | rfl
        · exact pU
        · rw [params_neg]; exact pU
        · exact pQ
        · exact pD
        · exact pM'))
  -- clause (Fix)
  have t2 : IDnDerivable A ThetaWNoteD.zero H h2 [∼U, Q, ∼U ⋎ Q, M] :=
    .fix (hH.succ_mem (hH.nadd_mem hΩ (hH.omegaMul_mem (hH.ofNat_mem c))))
      (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl | rfl
        · rw [params_neg]; exact pU
        · exact pQ
        · exact pD
        · exact pM'))
      (t := numI m') (List.mem_cons_of_mem _ List.mem_cons_self)
      (le_trans (Omega_le_Omega_of_le (by omega : k.val ≤ n - 1))
        (le_trans (ThetaWNoteD.le_nadd_left _ _) (le_of_lt (ThetaWNoteD.lt_succ _))))
      hrk t1
  have t3 : IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.nadd h2 (ThetaWNoteD.ofNat 1))
      [∼U, ∼U ⋎ Q, M] :=
    .orR (hmem 1) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl
        · rw [params_neg]; exact pU
        · exact pD
        · exact pM'))
      (List.mem_cons_of_mem _ List.mem_cons_self) (hone 1)
      (ThetaWNoteD.lt_nadd_ofNat_succ h2 0)
      (t2.weaken_seq hH.isOperator (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
        (pl _ (by
          intro χ hχ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
          rcases hχ with rfl | rfl | rfl | rfl
          · exact pQ
          · rw [params_neg]; exact pU
          · exact pD
          · exact pM')))
  exact .orL (hmem 2) (pl _ (by
      intro χ hχ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
      rcases hχ with rfl | rfl
      · exact pD
      · exact pM'))
    List.mem_cons_self (hlt 1 2 (by omega)) t3

/-- **The closure axiom** in the form of the proof of Theorem 6.5, bridged to `Embed.lean`'s
`AxDerivable`/`OmegaTwo` convention via `axDerivable_of_al`. -/
theorem closure_axiom (hAb : FamilyLevelBounded A) (hX : ∀ j, XFreeL (A j)) :
    AxDerivable A (closureAxAt k (A k)) :=
  axDerivable_of_al (closure_derivable k A hAb hX)


end Closure
end IDn
end OrdinalAnalysis
