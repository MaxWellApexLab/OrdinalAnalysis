/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\indAx_claim.lean (level `k : Fin n` generalised to
   `k : ℕ`, ID_n -> ID_omega).  Freund, Proposition 6.4, uniform version: the induction on stages
   at one level `k`.  In IDn the step composes the induction hypothesis with Exercise 6.3 (`ex63`)
   and `plugI`; here the (cut-free) monotone plugging is the generic `Cong` of `IDw.Transfer`, and
   the congruence *from the unfolding `A_k(t; I_k^{≺γ}, Jlev k)` straight to the embedded instance
   `A_{k̄}(t; F, j < k̄ ∧ Jlev ⊤)`* is supplied as a hypothesis of the abstract claim. -/

import OrdinalAnalysis.IDw.AxiomsIDCases.closure_inst
import OrdinalAnalysis.IDw.Transfer
import OrdinalAnalysis.IDw.AxiomsLogic
import OrdinalAnalysis.IDw.AxiomsPA
import OrdinalAnalysis.IDw.Embed

set_option autoImplicit false
namespace OrdinalAnalysis

/-! ### Ordinal sums for Proposition 6.4 -/

namespace ThetaVNoteD

open ThetaVTerm in
/-- `(Ω_ω ⊕ y) + Ω_ω = Ω_ω · 2` for `y ≺ Ω_ω`: the summands of `y` are absorbed. -/
theorem nadd_OmegaW_add_OmegaW {y : ThetaVNoteD} (hy : y < OmegaW) :
    nadd OmegaW y + OmegaW = nadd OmegaW OmegaW := by
  have hy' : ∀ e ∈ y.entries, e < ThetaVTerm.OmegaW :=
    (lt_prin_iff (p := OmegaW) trivial).mp hy
  have hE : OmegaW.entries = [ThetaVTerm.OmegaW] := rfl
  have e1 : (nadd OmegaW y).entries = ThetaVTerm.OmegaW :: y.entries := by
    rw [entries_nadd, hE]
    cases hys : y.entries with
    | nil => exact mergeL_nil_right _
    | cons y0 ys =>
      rw [mergeL_cons_cons_of_le [] ys
        (le_of_lt' (hy' y0 (by rw [hys]; exact List.mem_cons_self))), mergeL_nil_left]
  refine ext_entries ?_
  rw [entries_add, e1, hE, addL_cons, entries_nadd, hE,
    mergeL_cons_cons_of_le [] [] (le_refl' _), mergeL_nil_left]
  rw [List.filter_cons_of_pos (by simp [geb]),
    List.filter_eq_nil_iff.mpr (fun e he => by
      simp only [geb, decide_eq_true_eq]
      exact not_le_of_lt' (hy' e he))]
  rfl

/-- The step of the induction on stages: `(ω·β + ω·γ) ⊕ k ≺ ω·β + ω·δ` for `γ ≺ δ`. -/
theorem stage_sum_lt (b : ThetaVNoteD) {g d : ThetaVNoteD} (h : g < d) (k : ℕ) :
    nadd (omegaMul b + omegaMul g) (ofNat k) < omegaMul b + omegaMul d := by
  rw [← add_ofNat_eq_nadd, add_assoc, add_ofNat_eq_nadd]
  exact add_lt_add_left _ (omegaMul_nadd_ofNat_lt h k)

end ThetaVNoteD

namespace IDw

open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting

section Sums

/-- `ω · (Ω_ω ⊕ c) + ω · Ω_j ⪯ Ω_ω · 2` for every level `j`. -/
theorem omegaMul_beta_add_Omega_le (c j : ℕ) :
    ThetaVNoteD.omegaMul (ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat c)) +
        ThetaVNoteD.omegaMul (ThetaVNoteD.Omega j) ≤ OmegaTwo_pa := by
  rw [ThetaVNoteD.omegaMul_nadd, ThetaVNoteD.omegaMul_OmegaW, ThetaVNoteD.omegaMul_Omega]
  calc ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.omegaMul (ThetaVNoteD.ofNat c)) +
        ThetaVNoteD.Omega j
      ≤ ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.omegaMul (ThetaVNoteD.ofNat c)) +
          ThetaVNoteD.OmegaW :=
        ThetaVNoteD.add_le_add_left _ (le_of_lt (ThetaVNoteD.Omega_lt_OmegaW j))
    _ = OmegaTwo_pa := ThetaVNoteD.nadd_OmegaW_add_OmegaW (omegaMul_ofNat_lt_Omega c)

end Sums

/-! ### The atom pairs of the induction step, and the map along a numeral substitution -/

section Congruence

variable {A : FormJ} {H : Set ThetaVNoteD → Set ThetaVNoteD}

/-- **The atom pairs of the induction step** (source: the unfolding `A_k(t; I_k^{≺g}, Jlev k)`; target: the
embedded finitary instance): an arithmetic literal is its own image, `I_k^{≺g} s ↦ P_t(s)` (the
own place, `P_t := F(·, k̄)`), `Jlev k (j,a) ↦ j < k̄ ∧ Jlev ⊤ (j,a)` and `¬Jlev k (j,a) ↦
¬(j < k̄ ∧ Jlev ⊤ (j,a))`. `OkFwd k` is the case `g = Ω_{k+1}`, `P_t = Jlev ⊤ (k̄,·)`. -/
def OkP (k : ℕ) (g : StageAt k) (Pt : SyntacticTerm LIinfW → Proposition LIinfW)
    (B B' : Proposition LIinfW) : Prop :=
  (IsArithLit B ∧ B' = B) ∨
  (∃ s : SyntacticTerm LIinfW, s.freeVariables = ∅ ∧ B = stageAt (⟨k, g⟩ : Stage) s ∧
    B' = Pt s) ∨
  (∃ j a : SyntacticTerm LIinfW, j.freeVariables = ∅ ∧ a.freeVariables = ∅ ∧
    B = jlevAt (k : WithTop ℕ) j a ∧ B' = Transfer.qTop k j a) ∨
  (∃ j a : SyntacticTerm LIinfW, j.freeVariables = ∅ ∧ a.freeVariables = ∅ ∧
    B = njlevAt (k : WithTop ℕ) j a ∧ B' = ∼(Transfer.qTop k j a))

/-- **Every atom pair of `OkP` is derivable** at the height `α ⪰ Ω_{k+1} ⊕ 4`, given the own-place
pairs `⊢ ¬I_k^{≺g} s, P_t(s)` at the height `α`. -/
theorem okP_derivable (hH : ThetaVNoteD.NiceS H) (k : ℕ) (g : StageAt k)
    (Pt : SyntacticTerm LIinfW → Proposition LIinfW) {Γ : Sequent LIinfW}
    (hΓ : paramsVal Γ ⊆ H ∅) {α : ThetaVNoteD} (hα : α ∈ H ∅)
    (hkα : ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 4) ≤ α)
    (hP : ∀ s : SyntacticTerm LIinfW, s.freeVariables = ∅ →
      IDwDerivable A ThetaVNoteD.zero H α (∼(stageAt (⟨k, g⟩ : Stage) s) :: Pt s :: Γ))
    (B B' : Proposition LIinfW) (h : OkP k g Pt B B')
    (hp : Stage.val '' params B ⊆ H ∅) (hp' : Stage.val '' params B' ⊆ H ∅) :
    IDwDerivable A ThetaVNoteD.zero H α (∼B :: B' :: Γ) := by
  have hPar : paramsVal (∼B :: B' :: Γ) ⊆ H ∅ := by
    rw [paramsVal_cons, paramsVal_cons, params_neg]
    exact Set.union_subset hp (Set.union_subset hp' hΓ)
  rcases h with ⟨hl, rfl⟩ | ⟨s, hs, rfl, rfl⟩ | ⟨j, a, hj, ha, rfl, rfl⟩ | ⟨j, a, hj, ha, rfl, rfl⟩
  · exact Transfer.arith_identity hα hl hPar
  · exact hP s hs
  · exact (Transfer.transfer4 hH k hj ha).weaken hH.1
      (le_trans (Transfer.nadd_Omega_le k (by omega)) hkα)
      (List.cons_subset.mpr ⟨List.mem_cons_self, List.cons_subset.mpr
        ⟨List.mem_cons_of_mem _ List.mem_cons_self, List.nil_subset _⟩⟩) hα hPar
  · exact (Transfer.transfer3 hH k hj ha).weaken hH.1
      (le_trans (Transfer.nadd_Omega_le k (by omega)) hkα)
      (List.cons_subset.mpr ⟨List.mem_cons_of_mem _ List.mem_cons_self, List.cons_subset.mpr
        ⟨List.mem_cons_self, List.nil_subset _⟩⟩) hα hPar

/-- **A congruence along a numeral substitution of the target.**  `numSubst f` only changes free
variables; on the (closed) instances it leaves the atoms alone, and commutes with the numeral
instances of the quantifiers. -/
theorem cong_map_numSubst (f : ℕ → ℕ) {Ok : Proposition LIinfW → Proposition LIinfW → Prop}
    {c : ℕ} {B B' : Proposition LIinfW} (h : Transfer.Cong Ok c B B') :
    Transfer.Cong (fun X Y => ∃ Y', Ok X Y' ∧ Y = numSubst f ▹ Y') c B (numSubst f ▹ B') := by
  induction h with
  | atom h => exact .atom ⟨_, h, rfl⟩
  | verum => simpa using Transfer.Cong.verum
  | falsum => simpa using Transfer.Cong.falsum
  | and h0 h1 ih0 ih1 =>
    simpa only [LogicalConnective.HomClass.map_and] using Transfer.Cong.and ih0 ih1
  | or h0 h1 ih0 ih1 =>
    simpa only [LogicalConnective.HomClass.map_or] using Transfer.Cong.or ih0 ih1
  | all h ih =>
    rw [numSubst_all]
    refine Transfer.Cong.all (fun m => ?_)
    have := ih m
    rwa [numSubst_subst, show numSubst f (numI m) = numI m by simp [numI]] at this
  | exs h ih =>
    rw [numSubst_exs]
    refine Transfer.Cong.exs (fun m => ?_)
    have := ih m
    rwa [numSubst_subst, show numSubst f (numI m) = numI m by simp [numI]] at this

end Congruence

/-! ### Proposition 6.4: the induction on stages -/

section Induction

variable {A : FormJ} {H : Set ThetaVNoteD → Set ThetaVNoteD}

/-- `Cl(E₁, G) = ∀x (¬E₁(x) ∨ G(x))`, the premise `∀x (A(x, G) → G(x))` of the induction axiom,
with `E₁ = A(x, G)` the embedded body at the level `k̄`. -/
def ClE (E1 G : Semiformula LIinfW ℕ 1) : Proposition LIinfW := ∀¹ (∼E1 ⋎ G)

theorem neg_ClE (E1 G : Semiformula LIinfW ℕ 1) : ∼(ClE E1 G) = ∃¹ (E1 ⋏ ∼G) := by
  simp [ClE]

theorem params_ClE {E1 G : Semiformula LIinfW ℕ 1} (hE : params E1 = ∅) (hG : params G = ∅) :
    params (ClE E1 G) = ∅ := by
  simp [ClE, hE, hG]

/-- **The induction on stages** in the proof of Freund's Proposition 6.4 (uniform version):
`H[δ] ⊢^{ω·β + ω·δ}_0 ¬Cl(E₁, G), ¬I_k^{≺δ} s, G(s)` for every stage `δ ⪯ Ω_{k+1}` of level `k` and
every closed `s`, with `β = Ω_ω ⊕ c_G`, `c_G` the complexity of `G` (so `ω · rk G ⪯ ω · β`).
The step for `γ ≺ δ` (the rule (nstage)) is one `Cong` from the unfolding `A_k(s; I_k^{≺γ}, Jlev k)`
to the embedded body `E₁(s)`, whose own-place pairs `¬I_k^{≺γ} u, G(u)` are the induction
hypothesis at `γ`, then Lemma 6.1 for `G(s)`, `(∧)`, the replacement of `s` by the numeral of its
value, and `(∃)` on `¬Cl`.  Everything is cut-free. -/
theorem indAx_claim (hH : ThetaVNoteD.NiceS H) {k : ℕ} (E1 G : Semiformula LIinfW ℕ 1) (c : ℕ)
    (hGf : G.freeVariables = ∅) (hGX : XFreeI G) (hGp : params G = ∅)
    (hEf : E1.freeVariables = ∅) (hEX : XFreeI E1) (hEp : params E1 = ∅)
    (hC : ∀ (g : StageAt k) (t : SyntacticTerm LIinfW), t.freeVariables = ∅ →
      Transfer.Cong (OkP k g (fun s => G/[s])) c (unfoldW A k g t) (E1/[t])) :
    ∀ (δ : StageAt k) (s : SyntacticTerm LIinfW), s.freeVariables = ∅ →
      IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H {δ.1})
        (ThetaVNoteD.omegaMul (ThetaVNoteD.nadd ThetaVNoteD.OmegaW
          (ThetaVNoteD.ofNat G.complexity)) + ThetaVNoteD.omegaMul δ.1)
        [∼(ClE E1 G), nstageAt (⟨k, δ⟩ : Stage) s, G/[s]] := by
  set β : ThetaVNoteD := ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat G.complexity)
    with hβ
  have hΩb : ThetaVNoteD.OmegaW ≤ ThetaVNoteD.omegaMul β := by
    rw [← ThetaVNoteD.omegaMul_OmegaW]
    exact ThetaVNoteD.omegaMul_le_omegaMul (ThetaVNoteD.le_nadd_left _ _)
  have hαω : ∀ x : ThetaVNoteD, omegaT ≤ ThetaVNoteD.omegaMul β + ThetaVNoteD.omegaMul x :=
    fun x => le_trans (le_of_lt (lt_of_lt_of_le
      (ThetaVNoteD.omegaPow_lt_prin ThetaVTerm.isPrin_OmegaW
        (ThetaVNoteD.one_lt_prin ThetaVTerm.isPrin_OmegaW)) hΩb)) (ThetaVNoteD.le_add_right _ _)
  have hrkG : ∀ x : ThetaVNoteD,
      ThetaVNoteD.omegaMul (rk G) ≤ ThetaVNoteD.omegaMul β + ThetaVNoteD.omegaMul x := fun x =>
    le_trans (ThetaVNoteD.omegaMul_le_omegaMul (rk_le_Omega_nadd G)) (ThetaVNoteD.le_add_right _ _)
  have hΩbound : ∀ x : ThetaVNoteD,
      ThetaVNoteD.OmegaW ≤ ThetaVNoteD.omegaMul β + ThetaVNoteD.omegaMul x :=
    fun x => le_trans hΩb (ThetaVNoteD.le_add_right _ _)
  have hk4 : ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 4) <
      ThetaVNoteD.OmegaW :=
    ThetaVNoteD.nadd_lt_prin ThetaVTerm.isPrin_OmegaW (ThetaVNoteD.Omega_lt_OmegaW k)
      (ThetaVNoteD.ofNat_lt_prin ThetaVTerm.isPrin_OmegaW 4)
  have hClp : params (∼(ClE E1 G)) = ∅ := by rw [params_neg]; exact params_ClE hEp hGp
  have hnegC : ∼(ClE E1 G) = ∃¹ (E1 ⋏ ∼G) := neg_ClE E1 G
  suffices key : ∀ d : ThetaVNoteD, ∀ δ : StageAt k, δ.1 = d → ∀ s : SyntacticTerm LIinfW,
      s.freeVariables = ∅ →
      IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H {δ.1})
        (ThetaVNoteD.omegaMul β + ThetaVNoteD.omegaMul δ.1)
        [∼(ClE E1 G), nstageAt (⟨k, δ⟩ : Stage) s, G/[s]] from
    fun δ => key δ.1 δ rfl
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
  intro δ hδ s hs
  subst hδ
  have hKδ := hH.adjoin {δ.1}
  have hδmem : δ.1 ∈ ThetaVNoteD.adjoin H {δ.1} ∅ := subset_adjoin_empty hH.isOperator _ rfl
  have hαmem : ThetaVNoteD.omegaMul β + ThetaVNoteD.omegaMul δ.1 ∈
      ThetaVNoteD.adjoin H {δ.1} ∅ :=
    hKδ.add_mem (hKδ.omegaMul_mem (hKδ.nadd_mem hKδ.OmegaW_mem (hKδ.ofNat_mem _)))
      (hKδ.omegaMul_mem hδmem)
  have pGs : ∀ u : SyntacticTerm LIinfW, params (G/[u]) = ∅ := fun u => by
    rw [params_subst1, hGp]
  have emptyP : ∀ (φ : Proposition LIinfW) (Z : Set ThetaVNoteD), params φ = ∅ →
      Stage.val '' params φ ⊆ Z := fun φ Z h => by
    rw [h, Set.image_empty]; exact Set.empty_subset _
  have pnil : ∀ Z : Set ThetaVNoteD, paramsVal ([] : Sequent LIinfW) ⊆ Z := fun Z => by
    rw [paramsVal_nil]; exact Set.empty_subset _
  have hPδ : paramsVal [∼(ClE E1 G), nstageAt (⟨k, δ⟩ : Stage) s, G/[s]] ⊆
      ThetaVNoteD.adjoin H {δ.1} ∅ := by
    refine paramsVal_cons_sub (emptyP _ _ hClp)
      (paramsVal_cons_sub ?_ (paramsVal_cons_sub (emptyP _ _ (pGs s)) (pnil _)))
    rw [show params (nstageAt (⟨k, δ⟩ : Stage) s) = {(⟨k, δ⟩ : Stage)} from rfl,
      Set.image_singleton]
    exact Set.singleton_subset_iff.mpr hδmem
  refine .nstage (fun g => ThetaVNoteD.nadd (ThetaVNoteD.omegaMul β + ThetaVNoteD.omegaMul g.1)
    (ThetaVNoteD.ofNat (2 * c + 2))) hαmem hPδ (List.mem_cons_of_mem _ List.mem_cons_self)
    (fun g hg => ThetaVNoteD.stage_sum_lt β hg _) (fun g hg => ?_)
  -- the premise for `γ ≺ δ`
  set K := ThetaVNoteD.adjoin (ThetaVNoteD.adjoin H {δ.1}) {g.1} with hK
  have hKn : ThetaVNoteD.NiceS K := hKδ.adjoin {g.1}
  have hgK : g.1 ∈ K ∅ := subset_adjoin_empty hKδ.isOperator _ rfl
  have hsubK : ThetaVNoteD.adjoin H {δ.1} ∅ ⊆ K ∅ := hKδ.isOperator.mono (Set.empty_subset _)
  have hαg : ∀ j : ℕ, ThetaVNoteD.nadd (ThetaVNoteD.omegaMul β + ThetaVNoteD.omegaMul g.1)
      (ThetaVNoteD.ofNat j) ∈ K ∅ := fun j =>
    hKn.nadd_mem (hKn.add_mem (hKn.omegaMul_mem (hKn.nadd_mem hKn.OmegaW_mem (hKn.ofNat_mem _)))
      (hKn.omegaMul_mem hgK)) (hKn.ofNat_mem j)
  have hαg0 : ThetaVNoteD.omegaMul β + ThetaVNoteD.omegaMul g.1 ∈ K ∅ := by
    have := hαg 0; rwa [ThetaVNoteD.ofNat_zero, ThetaVNoteD.nadd_zero] at this
  have hop : ∀ X, ThetaVNoteD.adjoin H {g.1} X ⊆ K X := by
    intro X
    exact hH.isOperator.mono (Set.subset_union_right : ({g.1} ∪ X : Set ThetaVNoteD) ⊆
      {δ.1} ∪ ({g.1} ∪ X))
  have pl : ∀ Δ : Sequent LIinfW, (∀ χ ∈ Δ, Stage.val '' params χ ⊆ K ∅) → paramsVal Δ ⊆ K ∅ :=
    fun Δ h => Transfer.paramsVal_subset h
  have pE : ∀ u : SyntacticTerm LIinfW, Stage.val '' params (E1/[u]) ⊆ K ∅ := fun u => by
    rw [params_subst1, hEp, Set.image_empty]; exact Set.empty_subset _
  have pGu : ∀ u : SyntacticTerm LIinfW, Stage.val '' params (G/[u]) ⊆ K ∅ := fun u => by
    rw [pGs, Set.image_empty]; exact Set.empty_subset _
  have pCl : Stage.val '' params (∼(ClE E1 G)) ⊆ K ∅ := by
    rw [hClp, Set.image_empty]; exact Set.empty_subset _
  have pU : Stage.val '' params (unfoldW A k g s) ⊆ K ∅ := by
    refine (Set.image_mono (params_unfoldW A k g s)).trans ?_
    rw [Set.image_singleton]; exact Set.singleton_subset_iff.mpr hgK
  have pnU : Stage.val '' params (∼(unfoldW A k g s)) ⊆ K ∅ := by rw [params_neg]; exact pU
  -- the induction hypothesis at `γ`, in the shape of an own-place pair
  have hyp : ∀ u : SyntacticTerm LIinfW, u.freeVariables = ∅ →
      IDwDerivable A ThetaVNoteD.zero K (ThetaVNoteD.omegaMul β + ThetaVNoteD.omegaMul g.1)
        (∼(stageAt (⟨k, g⟩ : Stage) u) :: G/[u] :: [∼(ClE E1 G)]) := by
    intro u hu
    refine (ih g.1 hg g rfl u hu).lift hKn.isOperator hop (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) (pl _ ?_)
    intro χ hχ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
    rcases hχ with rfl | rfl | rfl
    · rw [params_neg, show params (stageAt (⟨k, g⟩ : Stage) u) = {(⟨k, g⟩ : Stage)} from rfl,
        Set.image_singleton]
      exact Set.singleton_subset_iff.mpr hgK
    · exact pGu u
    · exact pCl
  -- the congruence from the unfolding at `γ` to the embedded body, height `α_γ ⊕ 2c`
  have hαnum : ∀ m : ℕ, ThetaVNoteD.ofNat m <
      ThetaVNoteD.omegaMul β + ThetaVNoteD.omegaMul g.1 := fun m =>
    lt_of_lt_of_le (ThetaVNoteD.ofNat_lt_omega m) (hαω g.1)
  have hαone : ThetaVNoteD.one < ThetaVNoteD.omegaMul β + ThetaVNoteD.omegaMul g.1 := by
    have := hαnum 1; rwa [ThetaVNoteD.ofNat_one] at this
  have pΓc : paramsVal [∼(ClE E1 G)] ⊆ K ∅ :=
    paramsVal_cons_sub pCl (by rw [paramsVal_nil]; exact Set.empty_subset _)
  have E1s : IDwDerivable A ThetaVNoteD.zero K
      (ThetaVNoteD.nadd (ThetaVNoteD.omegaMul β + ThetaVNoteD.omegaMul g.1)
        (ThetaVNoteD.ofNat (2 * c)))
      (∼(unfoldW A k g s) :: E1/[s] :: [∼(ClE E1 G)]) :=
    Transfer.cong_derivable hKn hαg0 hαone hαnum pΓc
      (okP_derivable hKn k g (fun u => G/[u]) pΓc hαg0
        (le_trans (le_of_lt hk4) (hΩbound g.1)) hyp)
      (hC g s hs) pU (pE s)
  -- Lemma 6.1 for `G(s)`
  have T := taut (A := A) hH (G/[s]) (freeVariables_subst_of_closed G hGf hs)
  rw [ThetaVNoteD.adjoin_eq_self hH.isOperator (emptyP _ _ (pGs s)), rk_subst] at T
  set C : Proposition LIinfW := E1/[s] ⋏ ∼(G/[s]) with hC'
  have pC : Stage.val '' params C ⊆ K ∅ := by
    rw [hC', params_and, params_neg, Set.image_union]
    exact Set.union_subset (pE s) (pGu s)
  have pΔ : paramsVal [C, ∼(unfoldW A k g s), ∼(ClE E1 G), G/[s]] ⊆ K ∅ := pl _ (by
    intro χ hχ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
    rcases hχ with rfl | rfl | rfl | rfl
    · exact pC
    · exact pnU
    · exact pCl
    · exact pGu s)
  have E2 : IDwDerivable A ThetaVNoteD.zero K
      (ThetaVNoteD.nadd (ThetaVNoteD.omegaMul β + ThetaVNoteD.omegaMul g.1)
        (ThetaVNoteD.ofNat (2 * c + 1)))
      [C, ∼(unfoldW A k g s), ∼(ClE E1 G), G/[s]] := by
    refine .and (hαg _) pΔ List.mem_cons_self
      (ThetaVNoteD.nadd_ofNat_lt_nadd_ofNat' _ (Nat.lt_succ_self _))
      (lt_of_le_of_lt (hrkG g.1) (ThetaVNoteD.lt_nadd_ofNat_succ _ _)) ?_ ?_
    · refine E1s.weaken_seq hKn.isOperator (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
      rw [paramsVal_cons]; exact Set.union_subset (pE s) pΔ
    · refine T.lift hKn.isOperator
        (fun X => hH.isOperator.mono (Set.subset_union_right.trans Set.subset_union_right))
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
      rw [paramsVal_cons, params_neg]; exact Set.union_subset (pGu s) pΔ
  -- the numeral of the value of `s`
  have hCs : C = (E1 ⋏ ∼G)/[s] := by
    rw [hC']; simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg]
  have hφf : (E1 ⋏ ∼G).freeVariables = ∅ := by
    rw [Semiformula.freeVariables_and, Semiformula.freeVariables_not, hEf, hGf]; rfl
  obtain ⟨v, E3⟩ := replaceHeadNumI (A := A) s hφf hs ⟨hEX, (xFreeI_neg G).mpr hGX⟩
    hKn.isOperator (hCs ▸ E2)
  have E4 : IDwDerivable A ThetaVNoteD.zero K
      (ThetaVNoteD.nadd (ThetaVNoteD.omegaMul β + ThetaVNoteD.omegaMul g.1)
        (ThetaVNoteD.ofNat (2 * c + 2)))
      [∼(unfoldW A k g s), ∼(ClE E1 G), G/[s]] :=
    .exs v (hαg _) (pl _ (by
        intro χ hχ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl
        · exact pnU
        · exact pCl
        · exact pGu s))
      (by rw [← hnegC]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      (lt_of_lt_of_le (ThetaVNoteD.ofNat_lt_omega _)
        (le_trans (hαω g.1) (ThetaVNoteD.le_nadd_left _ _)))
      (ThetaVNoteD.nadd_ofNat_lt_nadd_ofNat' _ (Nat.lt_succ_self _)) E3
  refine E4.weaken_seq hKn.isOperator (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
  refine pl _ ?_
  intro χ hχ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
  rcases hχ with rfl | rfl | rfl | rfl
  · exact pnU
  · exact pCl
  · rw [show params (nstageAt (⟨k, δ⟩ : Stage) s) = {(⟨k, δ⟩ : Stage)} from rfl,
      Set.image_singleton]
    exact Set.singleton_subset_iff.mpr (hsubK hδmem)
  · exact pGu s

end Induction

end IDw
end OrdinalAnalysis
