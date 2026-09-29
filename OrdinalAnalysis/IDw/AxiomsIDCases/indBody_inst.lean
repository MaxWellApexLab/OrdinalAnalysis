/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\indBody_inst.lean (level `k : Fin n` generalised to
   `k : ℕ`, ID_n -> ID_omega).  Freund, Proposition 6.4 and the universal closure in the proof of
   Theorem 6.5, uniform version: the ω-rule over `y = k̄`, the per-level derivation from
   `indAx_claim`, and the universal closure over the free variables of `F`. -/

import OrdinalAnalysis.IDw.AxiomsIDCases.indAx_claim
import OrdinalAnalysis.IDw.EmbedHypsLogic
import OrdinalAnalysis.IDw.TransferCong

set_option autoImplicit false
namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting

/-! ### Proposition 6.4, the axiom -/

section IndAxiom

variable {A : FormJ} {H : Set ThetaVNoteD → Set ThetaVNoteD}

/-- The numeral substitution under two binders. -/
def numSubst₂ (f : ℕ → ℕ) : Rew LIinfW ℕ 2 ℕ 2 := (numSubst₁ f).q

/-- **The embedded body `A(x, F)` of the induction axiom, under the numeral assignment `f`**
(`x = #0`, `y = #1`). -/
def indE2 (A : FormJ) (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) : Semiformula LIinfW ℕ 2 :=
  numSubst₂ f ▹ embK (AAt F (#1 : Semiterm LXJ ℕ 2) (Rewriting.emb A : Semiformula LForm ℕ 2))

/-- **The embedded own place `F(x, y)`, under the numeral assignment `f`.** -/
def indF2 (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) : Semiformula LIinfW ℕ 2 :=
  numSubst₂ f ▹ embK F

/-- The matrix of the induction axiom, `∀y (∀x (A(x,F) → F) → ∀x (J(y,x) → F))`, embedded. -/
def indMat (A : FormJ) (F : Semiformula LXJ ℕ 2) : Proposition LXJ :=
  ∀¹ ((∀¹ (AAt F (#1 : Semiterm LXJ ℕ 2) (Rewriting.emb A : Semiformula LForm ℕ 2) 🡒 F)) 🡒
    (∀¹ (Jat #1 #0 🡒 F)))

theorem indAxJ_eq (A : FormJ) (F : Semiformula LXJ ℕ 2) :
    indAxJ A F = Semiformula.univCl (indMat A F) := rfl

/-- **The closed instance of the embedded induction axiom under `f`** is
`∀y (¬(∀x (¬E ∨ F)) ∨ ∀x (¬J(y,x) ∨ F))` with `E`, `F` the embedded bodies under `f`. -/
theorem numSubst_embK_indMat (A : FormJ) (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) :
    numSubst f ▹ embK (indMat A F) =
      ∀¹ (∼(∀¹ (∼(indE2 A F f) ⋎ indF2 F f)) ⋎
        (∀¹ (∼(jlevAt ⊤ (#1 : Semiterm LIinfW ℕ 2) (#0 : Semiterm LIinfW ℕ 2)) ⋎ indF2 F f))) := by
  simp only [indMat, embK_all, embK_Jat, Semiformula.imp_eq, embK_or, embK_neg,
    Rewriting.app_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, rew_jlevAt_al, embT, Semiterm.lMap_bvar]
  rw [numSubst_q]
  rfl

/-! #### The numeral substitution under two binders, and the closed data of one level -/

theorem numSubst₂_bvar (f : ℕ → ℕ) (x : Fin 2) : numSubst₂ f #x = (#x : Semiterm LIinfW ℕ 2) := by
  fin_cases x
  · show (numSubst₁ f).q #0 = _
    rw [Rew.q_bvar_zero]; rfl
  · show (numSubst₁ f).q #(Fin.succ 0) = _
    rw [Rew.q_bvar_succ]; simp

theorem numSubst₂_fvar (f : ℕ → ℕ) (x : ℕ) :
    numSubst₂ f &x = (Semiterm.numeral (f x) : Semiterm LIinfW ℕ 2) := by
  show (numSubst₁ f).q &x = _
  rw [Rew.q_fvar]; simp

/-- A rewriting that sends the bound variables to closed terms yields a formula without free
variables from one without free variables. -/
theorem freeVariables_rew_of_closed_src {n₁ n₂ : ℕ} (ω : Rew (LIinfW) ℕ n₁ ℕ n₂)
    (hb : ∀ x, (ω #x).freeVariables = ∅) (φ : Semiformula (LIinfW) ℕ n₁)
    (hφ : φ.freeVariables = ∅) : (ω ▹ φ).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := ω) (φ := φ) (x := x) hx with ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ (ω #i).freeVariables := hi
    rw [hb i] at hi'
    exact Finset.notMem_empty x hi'
  · have hz' : z ∈ φ.freeVariables := hz
    rw [hφ] at hz'
    exact Finset.notMem_empty z hz'

theorem freeVariables_indF2 (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) :
    (indF2 F f).freeVariables = ∅ :=
  freeVariables_rew_closed _ (fun x => by rw [numSubst₂_bvar]; rfl)
    (fun x => by rw [numSubst₂_fvar]; exact numeral_freeVariables _) _

theorem freeVariables_indE2 (A : FormJ) (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) :
    (indE2 A F f).freeVariables = ∅ :=
  freeVariables_rew_closed _ (fun x => by rw [numSubst₂_bvar]; rfl)
    (fun x => by rw [numSubst₂_fvar]; exact numeral_freeVariables _) _

/-- `E₁(x) := A(x, F)` at the level `k̄` (`y := k̄`), under `f`. -/
def indE1 (A : FormJ) (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) (k : ℕ) : Semiformula LIinfW ℕ 1 :=
  (indE2 A F f)/[(#0 : Semiterm LIinfW ℕ 1), (Semiterm.numeral k : Semiterm LIinfW ℕ 1)]

/-- `G(x) := F(x, k̄)`, under `f`. -/
def indG (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) (k : ℕ) : Semiformula LIinfW ℕ 1 :=
  (indF2 F f)/[(#0 : Semiterm LIinfW ℕ 1), (Semiterm.numeral k : Semiterm LIinfW ℕ 1)]

theorem freeVariables_subst_bvar_numeral (ψ : Semiformula LIinfW ℕ 2) (hψ : ψ.freeVariables = ∅)
    (k : ℕ) :
    (ψ/[(#0 : Semiterm LIinfW ℕ 1), (Semiterm.numeral k : Semiterm LIinfW ℕ 1)]).freeVariables =
      ∅ :=
  freeVariables_rew_of_closed_src _ (fun x => by
    fin_cases x
    · exact rfl
    · exact numeral_freeVariables _) ψ hψ

theorem freeVariables_indE1 (A : FormJ) (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) (k : ℕ) :
    (indE1 A F f k).freeVariables = ∅ :=
  freeVariables_subst_bvar_numeral _ (freeVariables_indE2 A F f) k

theorem freeVariables_indG (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) (k : ℕ) :
    (indG F f k).freeVariables = ∅ :=
  freeVariables_subst_bvar_numeral _ (freeVariables_indF2 F f) k

theorem xFreeI_indE1 (A : FormJ) (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) (k : ℕ) :
    XFreeI (indE1 A F f k) :=
  (xFreeI_rew _ _).mpr ((xFreeI_rew _ _).mpr (xFreeI_embK _))

theorem xFreeI_indG (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) (k : ℕ) : XFreeI (indG F f k) :=
  (xFreeI_rew _ _).mpr ((xFreeI_rew _ _).mpr (xFreeI_embK _))

theorem params_indE1 (A : FormJ) (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) (k : ℕ) :
    params (indE1 A F f k) = ∅ := by
  unfold indE1 indE2
  rw [params_subst2, params_rew, params_embK]

theorem params_indG (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) (k : ℕ) :
    params (indG F f k) = ∅ := by
  unfold indG indF2
  rw [params_subst2, params_rew, params_embK]

/-! #### The congruence at one level, under the numeral assignment `f` -/

theorem numSubst_term_eq_self (f : ℕ → ℕ) {s : SyntacticTerm LIinfW} (hs : s.freeVariables = ∅) :
    numSubst f s = s := by
  have h := Semiterm.rew_eq_of_funEqOn (numSubst f) Rew.id s (fun x => x.elim0) (by
    intro x hx
    have hx' : x ∈ s.freeVariables := hx
    rw [hs] at hx'
    exact absurd hx' (by simp))
  simpa using h

theorem numSubst_subst2 (f : ℕ → ℕ) (φ : Semiformula LIinfW ℕ 2) (a b : SyntacticTerm LIinfW) :
    numSubst f ▹ (φ/[a, b]) = (numSubst₂ f ▹ φ)/[numSubst f a, numSubst f b] := by
  have hc : (numSubst f).comp (Rew.subst ![a, b]) =
      (Rew.subst ![numSubst f a, numSubst f b]).comp (numSubst₂ f) := by
    refine Rew.ext _ _ ?_ ?_
    · intro x; fin_cases x <;> simp [Rew.comp_app, numSubst₂_bvar]
    · intro x; simp [Rew.comp_app, numSubst₂_fvar, numI]
  show numSubst f ▹ (Rew.subst _ ▹ φ) = Rew.subst _ ▹ (numSubst₂ f ▹ φ)
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, hc]

theorem freeVariables_of_isArithLit {B : Proposition LIinfW} (h : IsArithLit B) :
    B.freeVariables = ∅ := by
  obtain ⟨j, r, v, (rfl | rfl), hv⟩ := h
  · ext x
    simp only [Finset.notMem_empty, iff_false]
    intro hx
    obtain ⟨i, hi⟩ : ∃ i, x ∈ (v i).freeVariables := by
      simpa [Semiformula.freeVariables] using hx
    rw [hv i] at hi
    exact Finset.notMem_empty x hi
  · ext x
    simp only [Finset.notMem_empty, iff_false]
    intro hx
    obtain ⟨i, hi⟩ : ∃ i, x ∈ (v i).freeVariables := by
      simpa [Semiformula.freeVariables] using hx
    rw [hv i] at hi
    exact Finset.notMem_empty x hi

theorem freeVariables_qTop (k : ℕ) {j a : SyntacticTerm LIinfW} (hj : j.freeVariables = ∅)
    (ha : a.freeVariables = ∅) : (Transfer.qTop k j a).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  simp [Transfer.qTop, Transfer.ltW, jlevAt, Semiformula.freeVariables, hj, ha,
    numeral_freeVariables] at hx

/-- **The congruence at level `k` under `f`** (from the `Cong` producer, mapped along `numSubst f`):
the unfolding `A_k(t; I_k^{≺g}, Jlev k)` and the closed embedded body `E₁(t)` are
`OkP k g G`-congruent, the own-place pairs being `I_k^{≺g} s ↦ G(s)`. -/
theorem ind_cong (hA : PositiveP A) (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) (k : ℕ)
    (g : StageAt k) {t : SyntacticTerm LIinfW} (ht : t.freeVariables = ∅) :
    Transfer.Cong (OkP k g (fun s => (indG F f k)/[s])) (Transfer.cdepth A)
      (unfoldW A k g t) ((indE1 A F f k)/[t]) := by
  have h0 := Transfer.cong_unfold (A := A) k g F
    (Ok := OkP k g (fun s => (embK F)/[s, numI k]))
    (fun B hB => Or.inl ⟨hB, rfl⟩) (fun s hs => Or.inr (Or.inl ⟨s, hs, rfl, rfl⟩))
    (fun j a hj ha => Or.inr (Or.inr (Or.inl ⟨j, a, hj, ha, rfl, rfl⟩)))
    (fun j a hj ha => Or.inr (Or.inr (Or.inr ⟨j, a, hj, ha, rfl, rfl⟩))) hA ht
  have h1 := cong_map_numSubst f h0
  have e : numSubst f ▹ Transfer.embInst F k A t = (indE1 A F f k)/[t] := by
    unfold Transfer.embInst
    rw [numSubst_subst2, numSubst_term_eq_self f ht, show numSubst f (numI k) = numI k by
      simp [numI]]
    unfold indE1 indE2
    rw [subst_zero_comp]
  rw [e] at h1
  refine Transfer.Cong.mono ?_ h1
  rintro B B'' ⟨Y', hY', rfl⟩
  rcases hY' with ⟨hl, rfl⟩ | ⟨s, hs, rfl, rfl⟩ | ⟨j, a, hj, ha, rfl, rfl⟩ | ⟨j, a, hj, ha, rfl, rfl⟩
  · exact Or.inl ⟨hl, numSubst_eq_self (freeVariables_of_isArithLit hl)⟩
  · refine Or.inr (Or.inl ⟨s, hs, rfl, ?_⟩)
    rw [numSubst_subst2, numSubst_term_eq_self f hs, show numSubst f (numI k) = numI k by
      simp [numI]]
    unfold indG indF2
    show (numSubst₂ f ▹ embK F)/[s, numI k] = ((numSubst₂ f ▹ embK F)/[(#0 : Semiterm LIinfW ℕ 1),
      (Semiterm.numeral k : Semiterm LIinfW ℕ 1)])/[s]
    rw [subst_zero_comp]
  · exact Or.inr (Or.inr (Or.inl ⟨j, a, hj, ha, rfl,
      numSubst_eq_self (freeVariables_qTop k hj ha)⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨j, a, hj, ha, rfl, ?_⟩))
    rw [LogicalConnective.HomClass.map_neg, numSubst_eq_self (freeVariables_qTop k hj ha)]

/-! #### One level of the induction axiom, cut-free -/

theorem indBody_inst (k : ℕ) (G : Semiformula LIinfW ℕ 1) (m : ℕ) :
    (∼(jlevAt ⊤ (Semiterm.numeral k : Semiterm LIinfW ℕ 1) (#0 : Semiterm LIinfW ℕ 1)) ⋎ G)/[numI m] =
      njlevAt ⊤ (numI k) (numI m) ⋎ G/[numI m] := by
  simp only [LogicalConnective.HomClass.map_or, neg_jlevAt]
  simp

/-- **Freund, Proposition 6.4, for one level `k` and one numeral assignment**: cut-free,
`⊢ ¬Cl(E₁, G) ∨ ∀x (¬Jlev ⊤ (k̄, x) ∨ G(x))` at the height `Ω_ω · 2 ⊕ 6`, from the induction on
stages `indAx_claim` at `δ = Ω_{k+1}`, (njlev), and the ω-rule. -/
theorem indAx_level (hH : ThetaVNoteD.NiceS H) (hA : PositiveP A) (F : Semiformula LXJ ℕ 2)
    (f : ℕ → ℕ) (k : ℕ) (Γ : Sequent LIinfW) (hΓ : paramsVal Γ ⊆ H ∅) :
    IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat 6))
      ((∼(ClE (indE1 A F f k) (indG F f k)) ⋎
        (∀¹ (∼(jlevAt ⊤ (Semiterm.numeral k : Semiterm LIinfW ℕ 1) (#0 : Semiterm LIinfW ℕ 1)) ⋎
          indG F f k))) :: Γ) := by
  set E1 := indE1 A F f k with hE1
  set G := indG F f k with hG
  set Cl : Proposition LIinfW := ClE E1 G with hCl
  set V : Proposition LIinfW :=
    ∀¹ (∼(jlevAt ⊤ (Semiterm.numeral k : Semiterm LIinfW ℕ 1) (#0 : Semiterm LIinfW ℕ 1)) ⋎ G)
    with hV
  have hmem : ∀ j : ℕ, ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat j) ∈ H ∅ :=
    fun j => OmegaTwo_mem_al hH ∅ j
  have hlt : ∀ i j : ℕ, i < j → ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat i) <
      ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat j) := fun i j h =>
    ThetaVNoteD.nadd_ofNat_lt_nadd_ofNat' _ h
  have hone : ∀ j : ℕ, ThetaVNoteD.one <
      ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat j) := fun j =>
    lt_of_lt_of_le (ThetaVNoteD.one_lt_prin ThetaVTerm.isPrin_OmegaW) (Omega_le_OmegaTwo_nadd j)
  have e0 : ∀ φ : Proposition LIinfW, params φ = ∅ → Stage.val '' params φ ⊆ H ∅ :=
    fun φ h => by rw [h, Set.image_empty]; exact Set.empty_subset _
  have pGm : ∀ u : SyntacticTerm LIinfW, params (G/[u]) = ∅ := fun u => by
    rw [params_subst1, hG, params_indG]
  have hpCl : params Cl = ∅ := params_ClE (params_indE1 A F f k) (params_indG F f k)
  have hpV : params V = ∅ := by
    rw [hV, params_all, params_or, params_neg, params_jlevAt, hG, params_indG]; simp
  have hpN : ∀ m : ℕ, params (njlevAt ⊤ (numI k) (numI m) ⋎ G/[numI m]) = ∅ := fun m => by
    rw [params_or, params_njlevAt, pGm]; simp
  -- one instance of the ω-rule on `V`
  have inst : ∀ m : ℕ, IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat 3))
      ((njlevAt ⊤ (numI k) (numI m) ⋎ G/[numI m]) :: ∼Cl :: V :: Γ) := by
    intro m
    set N : Proposition LIinfW := njlevAt ⊤ (numI k) (numI m) with hN
    set D : Proposition LIinfW := N ⋎ G/[numI m] with hD
    have pN : Stage.val '' params N ⊆ H ∅ := e0 _ (by rw [hN, params_njlevAt])
    have pD : Stage.val '' params D ⊆ H ∅ := e0 _ (hpN m)
    have pCl : Stage.val '' params (∼Cl) ⊆ H ∅ := e0 _ (by rw [params_neg, hpCl])
    have pV : Stage.val '' params V ⊆ H ∅ := e0 _ hpV
    have pG : Stage.val '' params (G/[numI m]) ⊆ H ∅ := e0 _ (pGm _)
    have pI : Stage.val '' params (∼(IOmegaAt k (numI m))) ⊆ H ∅ := Transfer.omega_image_neg hH k
    -- the induction on stages at the top stage
    have c0 := indAx_claim (A := A) hH E1 G (Transfer.cdepth A) (freeVariables_indG F f k)
      (xFreeI_indG F f k) (params_indG F f k) (freeVariables_indE1 A F f k) (xFreeI_indE1 A F f k)
      (params_indE1 A F f k) (fun g t ht => ind_cong hA F f k g ht) (StageAt.top k) (numI m)
      (numI_freeVariables m)
    rw [StageAt.top_val, ThetaVNoteD.adjoin_eq_self hH.1
      (Set.singleton_subset_iff.mpr (hH.Omega_mem k))] at c0
    have hOT2 : OmegaTwo_al ∈ H ∅ := by
      have := hmem 0; rwa [ThetaVNoteD.ofNat_zero, ThetaVNoteD.nadd_zero] at this
    have c0' : IDwDerivable A ThetaVNoteD.zero H OmegaTwo_al
        [∼Cl, ∼(IOmegaAt k (numI m)), G/[numI m]] :=
      c0.mono_height (omegaMul_beta_add_Omega_le G.complexity k) hOT2
    -- `(njlev)`
    have hP0 : paramsVal (G/[numI m] :: N :: D :: ∼Cl :: V :: Γ) ⊆ H ∅ :=
      paramsVal_cons_sub pG (paramsVal_cons_sub pN (paramsVal_cons_sub pD
        (paramsVal_cons_sub pCl (paramsVal_cons_sub pV hΓ))))
    have T0 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat 1))
        (G/[numI m] :: N :: D :: ∼Cl :: V :: Γ) :=
      .njlev (hmem 1) hP0 (List.mem_cons_of_mem _ List.mem_cons_self) (numI_freeVariables k)
        (numI_freeVariables m)
        (fun _ => ThetaVNoteD.lt_nadd_ofNat_succ _ 0)
        (fun _ => by
          rw [termVal_numI]
          refine c0'.weaken_seq hH.1 (by
            intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) ?_
          exact paramsVal_cons_sub pI hP0)
    have hP1 : paramsVal (N :: D :: ∼Cl :: V :: Γ) ⊆ H ∅ :=
      paramsVal_cons_sub pN (paramsVal_cons_sub pD (paramsVal_cons_sub pCl
        (paramsVal_cons_sub pV hΓ)))
    have T1 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat 2))
        (N :: D :: ∼Cl :: V :: Γ) :=
      .orR (hmem 2) hP1 (List.mem_cons_of_mem _ List.mem_cons_self) (hone 2)
        (hlt 1 2 (by omega)) T0
    exact .orL (hmem 3) (paramsVal_cons_sub pD (paramsVal_cons_sub pCl
        (paramsVal_cons_sub pV hΓ))) List.mem_cons_self (hlt 2 3 (by omega)) T1
  have hP4 : paramsVal (∼Cl :: V :: Γ) ⊆ H ∅ :=
    paramsVal_cons_sub (e0 _ (by rw [params_neg, hpCl])) (paramsVal_cons_sub (e0 _ hpV) hΓ)
  -- the ω-rule
  have p4 : IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat 4)) (∼Cl :: V :: Γ) :=
    .all (φ := ∼(jlevAt ⊤ (Semiterm.numeral k : Semiterm LIinfW ℕ 1) (#0 : Semiterm LIinfW ℕ 1)) ⋎ G)
      (fun _ => ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat 3)) (hmem 4) hP4
      (List.mem_cons_of_mem _ List.mem_cons_self) (fun _ => hlt 3 4 (by omega))
      (fun m => by rw [indBody_inst]; exact inst m)
  -- the two disjunctions
  have pM : Stage.val '' params (∼Cl ⋎ V) ⊆ H ∅ :=
    e0 _ (by rw [params_or, params_neg, hpCl, hpV]; simp)
  have hP5 : paramsVal (∼Cl :: (∼Cl ⋎ V) :: Γ) ⊆ H ∅ :=
    paramsVal_cons_sub (e0 _ (by rw [params_neg, hpCl])) (paramsVal_cons_sub pM hΓ)
  have p5 : IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat 5)) (∼Cl :: (∼Cl ⋎ V) :: Γ) :=
    .orR (hmem 5) hP5 (List.mem_cons_of_mem _ List.mem_cons_self) (hone 5) (hlt 4 5 (by omega))
      (p4.weaken_seq hH.1 (by
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
        (paramsVal_cons_sub (e0 _ hpV) hP5))
  exact .orL (hmem 6) (paramsVal_cons_sub pM hΓ) List.mem_cons_self (hlt 5 6 (by omega)) p5

/-! #### The closed instance and the axiom -/

theorem params_indE2 (A : FormJ) (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) :
    params (indE2 A F f) = ∅ := by
  unfold indE2; rw [params_rew, params_embK]

theorem params_indF2 (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) : params (indF2 F f) = ∅ := by
  unfold indF2; rw [params_rew, params_embK]

/-- The instance of the closed matrix at `y := k̄`. -/
theorem indAx_inst_k (A : FormJ) (F : Semiformula LXJ ℕ 2) (f : ℕ → ℕ) (k : ℕ) :
    (∼(∀¹ (∼(indE2 A F f) ⋎ indF2 F f)) ⋎
        (∀¹ (∼(jlevAt ⊤ (#1 : Semiterm LIinfW ℕ 2) (#0 : Semiterm LIinfW ℕ 2)) ⋎
          indF2 F f)))/[numI k] =
      ∼(ClE (indE1 A F f k) (indG F f k)) ⋎
        (∀¹ (∼(jlevAt ⊤ (Semiterm.numeral k : Semiterm LIinfW ℕ 1) (#0 : Semiterm LIinfW ℕ 1)) ⋎
          indG F f k)) := by
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    subst_all_numeral, ClE, indE1, indG, rew_jlevAt_al]
  simp

/-- **The closed instance of the embedded induction axiom, cut-free**: the ω-rule over `y = k̄`,
each instance `indAx_level`; height `Ω_ω · 2 ⊕ 7`. -/
theorem indAx_closed (hH : ThetaVNoteD.NiceS H) (hA : PositiveP A) (F : Semiformula LXJ ℕ 2)
    (f : ℕ → ℕ) :
    IDwDerivable A ThetaVNoteD.zero H (ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat 7))
      [numSubst f ▹ embK (indMat A F)] := by
  rw [numSubst_embK_indMat]
  have hΓ0 : paramsVal [(∀¹ (∼(∀¹ (∼(indE2 A F f) ⋎ indF2 F f)) ⋎
      (∀¹ (∼(jlevAt ⊤ (#1 : Semiterm LIinfW ℕ 2) (#0 : Semiterm LIinfW ℕ 2)) ⋎
        indF2 F f)))  : Proposition LIinfW)] ⊆ H ∅ := by
    refine paramsVal_cons_sub ?_ (by rw [paramsVal_nil]; exact Set.empty_subset _)
    simp [params_indE2, params_indF2]
  refine .all (φ := ∼(∀¹ (∼(indE2 A F f) ⋎ indF2 F f)) ⋎
      (∀¹ (∼(jlevAt ⊤ (#1 : Semiterm LIinfW ℕ 2) (#0 : Semiterm LIinfW ℕ 2)) ⋎ indF2 F f)))
    (fun _ => ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat 6)) (OmegaTwo_mem_al hH ∅ 7) hΓ0
    List.mem_cons_self (fun _ => ThetaVNoteD.nadd_ofNat_lt_nadd_ofNat' _ (by omega))
    (fun k => ?_)
  rw [indAx_inst_k]
  exact indAx_level hH hA F f k _ hΓ0

/-- **Freund, Proposition 6.4 and the universal closure of Theorem 6.5**: every instance of the
induction axiom of `IDw A`, for a positive form `A`, is cut-free derivable at a height
`Ω_ω · 2 + m`. -/
theorem indAx_axiom (hA : PositiveP A) (F : Semiformula LXJ ℕ 2) :
    AxDerivable A (indAxJ A F) := by
  set ψ0 : Proposition LXJ := indMat A F with hψ0
  refine axDerivable_of_al ?_
  refine axDerivable_of_le_al (7 + ψ0.fvSup)
    (ThetaVNoteD.nadd (ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat 7))
      (ThetaVNoteD.ofNat (0 + ψ0.fvSup)))
    (le_of_eq (by rw [ThetaVNoteD.nadd_assoc, ThetaVNoteD.ofNat_nadd_ofNat, Nat.zero_add]))
    (fun H hH => ?_)
  rw [indAxJ_eq, emb_embK_univCl]
  refine allClosure_derivable hH.isOperator _
    (fun j => hH.nadd_mem (OmegaTwo_mem_al hH ∅ 7) (hH.ofNat_mem j))
    (by rw [params_embK, Set.image_empty]; exact Set.empty_subset _) (fun w => ?_)
  rw [embK_fixitr_inst]
  exact indAx_closed hH hA F _

end IndAxiom
end IDw
end OrdinalAnalysis
