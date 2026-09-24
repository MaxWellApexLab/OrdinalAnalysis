/-
  The collapsing theorem for the operator-controlled calculus `ID₁^∞`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Theorem 6.7 (adapted there from Buchholz 1992), with
  Definition 3.10, Proposition 3.9, Proposition 3.11 and Exercise 5.5 for the operators
  `H_α`, Theorem 5.9 (boundedness) and Exercise 6.6.

  **Theorem 6.7 (Collapsing).**  Let `Γ` be a `Σ(Ω)`-sequent, and let `α ∈ H_α(X)` and
  `X ⊆ ⋂ {C^ξ(ϑ ξ) | α ≺ ξ}`.  Then

      H_α[X] ⊢^β_{Ω+1} Γ   ⇒   H_η[X] ⊢^{ϑη}_{ϑη} Γ     for   η = α + ω(β).

  Here `H_α` is `ThetaNote.Hop α`, `H[X]` is `ThetaNote.adjoin H X`, the hypothesis on `X` is
  `ThetaNote.HullHyp α X`, `ω(β)` is `ThetaNote.omegaPow β`, `ϑ` is `ThetaNote.theta`, and the
  operator form `A` is positive (Freund's operator forms are positive by definition).

  The proof is Freund's, by induction on `β`:

    * (Fix) on `I t`: the induction hypothesis collapses the premise `Γ, A(t, I^{≺Ω})` (a
      `Σ(Ω)` sequent since `A` is positive) to height `ϑη'`, `η' = α + ω(β')`; boundedness
      (Theorem 5.9) at `ϑη'` gives `Γ, A(t, I^{≺ϑη'})`, and (W) on `I t = I^{≺Ω} t` with the
      witness `ϑη' ≺ ϑη` (Proposition 3.11 (c)) concludes;
    * (Cut) of rank `Ω`, on `I t`: the positive premise is collapsed and bounded to
      `Γ, I^{≺ϑη'} t`; the negative premise is moved to `H_{η'}[X]`, turned into
      `Γ, ¬I^{≺ϑη'} t` by Exercise 6.6, and collapsed with `η'` in place of `α`, to height
      `ϑη''`, `η'' = η' + ω(β') ≺ η`; a cut on `I^{≺ϑη'} t`, of rank `ω · ϑη' = ϑη' ≺ ϑη`,
      concludes.  A cut on `¬I t` is the same cut;
    * (Cut) of rank `≺ Ω`: both premises are `Σ(Ω)`; the rank lies in `H_α(X) ∩ Ω`
      (Exercise 5.5 (e)), hence below `ϑη` (Proposition 3.9);
    * (W): the witness lies in `H_α(X) ∩ Ω`, hence below `ϑη`;
    * (V): for `¬I^{≺δ} t` in a `Σ(Ω)` sequent `δ ≺ Ω`, and `δ ∈ H_α(X)`, so every `γ ≺ δ`
      may be added to `X` (`HullHyp.union_singleton`), and the premises are collapsed with
      `X ∪ {γ}`.

  The rank bound `Ω + 1` is `ThetaNote.Omega + ThetaNote.one`.

  **The induction.**  Freund's induction is on the height `β`, and it is needed as such:
  in the case of a cut on `I t`, the induction hypothesis is applied to a derivation that
  is not a subderivation (the negative premise after Exercise 6.6).  Here it is
  well-founded induction on `β` in `ThetaNote` (`WellFoundedLT`).
-/
import OrdinalAnalysis.ID1.Boundedness

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

open LO LO.FirstOrder

/-! ### Preliminaries -/

theorem adjoin_empty (H : Set ThetaNote → Set ThetaNote) (X : Set ThetaNote) :
    ThetaNote.adjoin H X ∅ = H X := by
  simp [ThetaNote.adjoin]

theorem atomRk_le_Omega : ∀ {k : ℕ} (r : LIinf.Rel k), atomRk r ≤ ThetaNote.Omega := fun r =>
  le_trans (atomRk_le_omegaMul r (relParams_le_Omega r)) (le_of_eq ThetaNote.omegaMul_Omega)

/-- **A formula of rank `≺ Ω + 1` has rank `⪯ Ω`.** -/
theorem rk_le_Omega_of_lt {ξ : Type*} {n : ℕ} {φ : Semiformula LIinf ξ n}
    (h : rk φ < ThetaNote.Omega + ThetaNote.one) : rk φ ≤ ThetaNote.Omega := by
  rw [ThetaNote.add_one_eq_succ] at h
  have key : ∀ m : ThetaNote, ThetaNote.succ m < ThetaNote.succ ThetaNote.Omega →
      ThetaNote.succ m ≤ ThetaNote.Omega := by
    intro m hm
    have hm' : m < ThetaNote.Omega :=
      lt_of_not_ge fun h' => absurd hm (not_lt_of_ge (ThetaNote.succ_le_succ h'))
    exact le_of_lt (ThetaNote.succ_lt_prin trivial hm')
  cases φ with
  | verum =>
    exact le_of_eq_of_le (rk_verum (ξ := ξ) (n := n)) (ThetaNote.zero_le' _)
  | falsum =>
    exact le_of_eq_of_le (rk_falsum (ξ := ξ) (n := n)) (ThetaNote.zero_le' _)
  | rel r v => exact le_of_eq_of_le (rk_rel r v) (atomRk_le_Omega r)
  | nrel r v => exact le_of_eq_of_le (rk_nrel r v) (atomRk_le_Omega r)
  | and φ ψ =>
    have e : rk (Semiformula.and φ ψ) = ThetaNote.succ (max (rk φ) (rk ψ)) := rk_and φ ψ
    rw [e] at h ⊢
    exact key _ h
  | or φ ψ =>
    have e : rk (Semiformula.or φ ψ) = ThetaNote.succ (max (rk φ) (rk ψ)) := rk_or φ ψ
    rw [e] at h ⊢
    exact key _ h
  | all φ =>
    have e : rk (Semiformula.all φ) = ThetaNote.succ (rk φ) := rk_all φ
    rw [e] at h ⊢
    exact key _ h
  | exs φ =>
    have e : rk (Semiformula.exs φ) = ThetaNote.succ (rk φ) := rk_exs φ
    rw [e] at h ⊢
    exact key _ h

theorem sigmaOmega_cons {φ : Proposition LIinf} {Γ : Sequent LIinf} (hφ : SigmaOmega φ)
    (hΓ : ∀ ψ ∈ Γ, SigmaOmega ψ) : ∀ ψ ∈ φ :: Γ, SigmaOmega ψ := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hφ
  · exact hΓ ψ hψ

/-! ### Theorem 6.7 -/

section Collapse

variable {A : Semisentence LXI 1}

/-- **Theorem 6.7, the induction on `β`.** -/
theorem collapsing_aux (hA : Positive A) (β : ThetaNote) :
    ∀ (α : ThetaNote) (X : Set ThetaNote) (Γ : Sequent LIinf), (∀ φ ∈ Γ, SigmaOmega φ) →
      α ∈ ThetaNote.Hop α X → ThetaNote.HullHyp α X →
      IDerivable A (ThetaNote.Omega + ThetaNote.one) (ThetaNote.adjoin (ThetaNote.Hop α) X) β Γ →
      IDerivable A (ThetaNote.theta (α + ThetaNote.omegaPow β))
        (ThetaNote.adjoin (ThetaNote.Hop (α + ThetaNote.omegaPow β)) X)
        (ThetaNote.theta (α + ThetaNote.omegaPow β)) Γ := by
  induction β using WellFoundedLT.induction with
  | ind β ih =>
  intro α X Γ hΓ hα hX d
  -- the facts of the first paragraph of Freund's proof
  have hβ : β ∈ ThetaNote.Hop α X := by
    have h := d.height_mem; rwa [adjoin_empty] at h
  have hΓα : paramsList Γ ⊆ ThetaNote.Hop α X := by
    have h := d.params_subset; rwa [adjoin_empty] at h
  have hαη : α < α + ThetaNote.omegaPow β := ThetaNote.lt_add_omegaPow_hull α β
  have hθη : ThetaNote.theta (α + ThetaNote.omegaPow β) ∈
      ThetaNote.adjoin (ThetaNote.Hop (α + ThetaNote.omegaPow β)) X ∅ := by
    rw [adjoin_empty]; exact ThetaNote.theta_add_omegaPow_mem_Hop hα hβ
  have hΓη : paramsList Γ ⊆ ThetaNote.adjoin (ThetaNote.Hop (α + ThetaNote.omegaPow β)) X ∅ := by
    rw [adjoin_empty]; exact hΓα.trans (ThetaNote.Hop_subset_Hop hαη X)
  have hmem : ∀ x, x ∈ ThetaNote.Hop α X → x < ThetaNote.Omega →
      x < ThetaNote.theta (α + ThetaNote.omegaPow β) :=
    fun x hx hxΩ => hX.lt_theta hαη hx hxΩ
  have hopH : ∀ (a : ThetaNote) (Y : Set ThetaNote), a ≤ α + ThetaNote.omegaPow β →
      ∀ Z, ThetaNote.adjoin (ThetaNote.Hop a) Y Z ⊆
        ThetaNote.adjoin (ThetaNote.Hop (α + ThetaNote.omegaPow β)) Y Z :=
    fun a Y h Z => ThetaNote.Hop_subset_Hop_of_le h _
  -- a collapsed premise of height `β₀ ≺ β`, with any `X' ⊇ X` satisfying the hypotheses
  have step : ∀ β₀ < β, ∀ (X' : Set ThetaNote) (Δ : Sequent LIinf), (∀ φ ∈ Δ, SigmaOmega φ) →
      α ∈ ThetaNote.Hop α X' → ThetaNote.HullHyp α X' →
      IDerivable A (ThetaNote.Omega + ThetaNote.one) (ThetaNote.adjoin (ThetaNote.Hop α) X') β₀ Δ →
      ThetaNote.theta (α + ThetaNote.omegaPow β₀) < ThetaNote.theta (α + ThetaNote.omegaPow β) ∧
      IDerivable A (ThetaNote.theta (α + ThetaNote.omegaPow β))
        (ThetaNote.adjoin (ThetaNote.Hop (α + ThetaNote.omegaPow β)) X')
        (ThetaNote.theta (α + ThetaNote.omegaPow β₀)) Δ := by
    intro β₀ h0 X' Δ hΔ hα' hX' d0
    have hβ₀ : β₀ ∈ ThetaNote.Hop α X' := by
      have h := d0.height_mem; rwa [adjoin_empty] at h
    have hlt : α + ThetaNote.omegaPow β₀ < α + ThetaNote.omegaPow β :=
      ThetaNote.add_lt_add_left α (ThetaNote.omegaPow_lt_omegaPow h0)
    have hθ : ThetaNote.theta (α + ThetaNote.omegaPow β₀) <
        ThetaNote.theta (α + ThetaNote.omegaPow β) :=
      ThetaNote.theta_lt_theta_of_mem_Hop hX' (le_of_lt (ThetaNote.lt_add_omegaPow_hull α β₀))
        hlt ((ThetaNote.Hop_nice α).add_mem hα' ((ThetaNote.Hop_nice α).omegaPow_mem hβ₀))
    exact ⟨hθ, ((ih β₀ h0 α X' Δ hΔ hα' hX' d0).mono_rank (le_of_lt hθ)).mono_op
      (hopH _ X' (le_of_lt hlt))⟩
  -- the cut on `I t`, both of its premises given
  have cutI : ∀ β₀ < β, ∀ t : SyntacticTerm LIinf,
      IDerivable A (ThetaNote.Omega + ThetaNote.one) (ThetaNote.adjoin (ThetaNote.Hop α) X) β₀
        (IOmegaAt t :: Γ) →
      IDerivable A (ThetaNote.Omega + ThetaNote.one) (ThetaNote.adjoin (ThetaNote.Hop α) X) β₀
        (∼(IOmegaAt t) :: Γ) →
      IDerivable A (ThetaNote.theta (α + ThetaNote.omegaPow β))
        (ThetaNote.adjoin (ThetaNote.Hop (α + ThetaNote.omegaPow β)) X)
        (ThetaNote.theta (α + ThetaNote.omegaPow β)) Γ := by
    intro β₀ h0 t d0 d1
    have hβ₀ : β₀ ∈ ThetaNote.Hop α X := by
      have h := d0.height_mem; rwa [adjoin_empty] at h
    -- `η' = α + ω(β₀)` and `η'' = η' + ω(β₀)`
    have hη₀α : α + ThetaNote.omegaPow β₀ ∈ ThetaNote.Hop α X :=
      (ThetaNote.Hop_nice α).add_mem hα ((ThetaNote.Hop_nice α).omegaPow_mem hβ₀)
    have hη₀ : α + ThetaNote.omegaPow β₀ ∈
        ThetaNote.Hop (α + ThetaNote.omegaPow β₀) X := ThetaNote.add_omegaPow_mem_Hop hα hβ₀
    have hαη₀ : α < α + ThetaNote.omegaPow β₀ := ThetaNote.lt_add_omegaPow_hull α β₀
    have hη₀η₁ : α + ThetaNote.omegaPow β₀ <
        α + ThetaNote.omegaPow β₀ + ThetaNote.omegaPow β₀ :=
      ThetaNote.lt_add_omegaPow_hull _ β₀
    have hη₁η : α + ThetaNote.omegaPow β₀ + ThetaNote.omegaPow β₀ < α + ThetaNote.omegaPow β :=
      ThetaNote.add_omegaPow_add_omegaPow_lt_hull α h0
    have hη₀η : α + ThetaNote.omegaPow β₀ < α + ThetaNote.omegaPow β := lt_trans hη₀η₁ hη₁η
    have hη₁α : α + ThetaNote.omegaPow β₀ + ThetaNote.omegaPow β₀ ∈ ThetaNote.Hop α X :=
      (ThetaNote.Hop_nice α).add_mem hη₀α ((ThetaNote.Hop_nice α).omegaPow_mem hβ₀)
    have hθ₀₁ : ThetaNote.theta (α + ThetaNote.omegaPow β₀) <
        ThetaNote.theta (α + ThetaNote.omegaPow β₀ + ThetaNote.omegaPow β₀) :=
      ThetaNote.theta_lt_theta_of_mem_Hop hX (le_of_lt hαη₀) hη₀η₁ hη₀α
    have hθ₁ : ThetaNote.theta (α + ThetaNote.omegaPow β₀ + ThetaNote.omegaPow β₀) <
        ThetaNote.theta (α + ThetaNote.omegaPow β) :=
      ThetaNote.theta_lt_theta_of_mem_Hop hX (le_of_lt (lt_trans hαη₀ hη₀η₁)) hη₁η hη₁α
    have hθ₀ := lt_trans hθ₀₁ hθ₁
    -- the stage `ϑη'`
    let b : Stage := ⟨ThetaNote.theta (α + ThetaNote.omegaPow β₀),
      le_of_lt (ThetaNote.theta_lt_Omega _)⟩
    have hbΩ : b.1 < ThetaNote.Omega := ThetaNote.theta_lt_Omega _
    have hbH : b.1 ∈ ThetaNote.adjoin (ThetaNote.Hop (α + ThetaNote.omegaPow β₀)) X ∅ := by
      rw [adjoin_empty]; exact ThetaNote.theta_add_omegaPow_mem_Hop hα hβ₀
    have hop₀ := (ThetaNote.Hop_isOperator (α + ThetaNote.omegaPow β₀)).adjoin X
    -- the positive premise: collapse, then bound
    have D0 := boundedness_IOmegaAt hop₀ hbH le_rfl hbΩ
      (ih β₀ h0 α X (IOmegaAt t :: Γ) (sigmaOmega_cons (sigmaOmega_stageAt _ _) hΓ) hα hX d0)
    -- the negative premise: move to `H_{η'}[X]`, Exercise 6.6, collapse with `η'`
    have d1' := neg_stage_bound hop₀ hbH
      (d1.mono_op fun Z => ThetaNote.Hop_subset_Hop hαη₀ _)
    have D1 := ih β₀ h0 (α + ThetaNote.omegaPow β₀) X (nstageAt b t :: Γ)
      (sigmaOmega_cons ((sigmaOmega_nstageAt_iff b t).mpr (Stage.ne_top_of_lt_Omega hbΩ)) hΓ)
      hη₀ (hX.mono (le_of_lt hαη₀)) d1'
    -- the cut on `I^{≺ϑη'} t`, at the height `ϑη''`
    have hθ₁H : ThetaNote.theta (α + ThetaNote.omegaPow β₀ + ThetaNote.omegaPow β₀) ∈
        ThetaNote.adjoin (ThetaNote.Hop (α + ThetaNote.omegaPow β)) X ∅ := by
      rw [adjoin_empty]
      exact ThetaNote.Hop_subset_Hop hη₁η X
        (ThetaNote.theta_add_omegaPow_mem_Hop hη₀ (ThetaNote.Hop_subset_Hop hαη₀ X hβ₀))
    have hrk : rk (stageAt b t) < ThetaNote.theta (α + ThetaNote.omegaPow β) := by
      rw [rk_stageAt, ThetaNote.omegaMul_theta]; exact hθ₀
    refine .cut (ψ := stageAt b t) hθη hΓη hrk hθ₁ ?_ ?_
    · exact ((D0.mono_rank (le_of_lt hθ₀)).mono_op (hopH _ X (le_of_lt hη₀η))).mono_height
        (le_of_lt hθ₀₁) hθ₁H
    · exact (D1.mono_rank (le_of_lt hθ₁)).mono_op (hopH _ X (le_of_lt hη₁η))
  -- the case distinction on the last clause
  generalize hH : ThetaNote.adjoin (ThetaNote.Hop α) X = H at d
  cases d with
  | literal _ _ hφ hm => exact .literal hθη hΓη hφ hm
  | verum _ _ hm => exact .verum hθη hΓη hm
  | idX t _ _ h1 h2 => exact .idX t hθη hΓη h1 h2
  | @and _ _ _ φ ψ α₀ α₁ _ _ hm h0 h1 d0 d1 =>
    subst hH
    have hσ := (sigmaOmega_and φ ψ).mp (hΓ _ hm)
    obtain ⟨l0, D0⟩ := step α₀ h0 X (φ :: Γ) (sigmaOmega_cons hσ.1 hΓ) hα hX d0
    obtain ⟨l1, D1⟩ := step α₁ h1 X (ψ :: Γ) (sigmaOmega_cons hσ.2 hΓ) hα hX d1
    exact .and hθη hΓη hm l0 l1 D0 D1
  | @orL _ _ _ φ ψ α₀ _ _ hm h0 d0 =>
    subst hH
    have hσ := (sigmaOmega_or φ ψ).mp (hΓ _ hm)
    obtain ⟨l0, D0⟩ := step α₀ h0 X (φ :: Γ) (sigmaOmega_cons hσ.1 hΓ) hα hX d0
    exact .orL hθη hΓη hm l0 D0
  | @orR _ _ _ φ ψ α₀ _ _ hm _ h0 d0 =>
    subst hH
    have hσ := (sigmaOmega_or φ ψ).mp (hΓ _ hm)
    obtain ⟨l0, D0⟩ := step α₀ h0 X (ψ :: Γ) (sigmaOmega_cons hσ.2 hΓ) hα hX d0
    exact .orR hθη hΓη hm (ThetaNote.one_lt_prin trivial) l0 D0
  | @all _ _ _ φ f _ _ hm hf d0 =>
    subst hH
    have hσ := (sigmaOmega_all φ).mp (hΓ _ hm)
    have p := fun n => step (f n) (hf n) X (φ/[numI n] :: Γ)
      (sigmaOmega_cons ((sigmaOmega_subst φ _).mpr hσ) hΓ) hα hX (d0 n)
    exact .all (fun n => ThetaNote.theta (α + ThetaNote.omegaPow (f n))) hθη hΓη hm
      (fun n => (p n).1) fun n => (p n).2
  | @exs _ _ _ φ n α₀ _ _ hm _ h0 d0 =>
    subst hH
    have hσ := (sigmaOmega_exs φ).mp (hΓ _ hm)
    obtain ⟨l0, D0⟩ := step α₀ h0 X (φ/[numI n] :: Γ)
      (sigmaOmega_cons ((sigmaOmega_subst φ _).mpr hσ) hΓ) hα hX d0
    exact .exs n hθη hΓη hm
      (ThetaNote.ofNat_lt_prin (p := ThetaNote.theta (α + ThetaNote.omegaPow β)) trivial n) l0 D0
  | @stage _ _ _ a t g α₀ _ _ hm hga _ hgH h0 d0 =>
    subst hH
    rw [adjoin_empty] at hgH
    have hgΩ : g.1 < ThetaNote.Omega := lt_of_lt_of_le hga a.2
    obtain ⟨l0, D0⟩ := step α₀ h0 X (unfold A g t :: Γ)
      (sigmaOmega_cons (sigmaOmega_unfold_of_ne_top A (Stage.ne_top_of_lt hga) t).1 hΓ)
      hα hX d0
    refine .stage g hθη hΓη hm hga (hmem _ hgH hgΩ) ?_ l0 D0
    rw [adjoin_empty]; exact ThetaNote.Hop_subset_Hop hαη X hgH
  | @nstage _ _ _ a t f _ _ hm hf d0 =>
    subst hH
    have haΩ : a.1 < ThetaNote.Omega :=
      Stage.lt_Omega_of_ne_top ((sigmaOmega_nstageAt_iff a t).mp (hΓ _ hm))
    have haH : a.1 ∈ ThetaNote.Hop α X :=
      hΓα (params_subset_paramsList hm (by rw [params_nstageAt]; exact Set.mem_singleton _))
    have p : ∀ g : Stage, g.1 < a.1 →
        ThetaNote.theta (α + ThetaNote.omegaPow (f g)) <
          ThetaNote.theta (α + ThetaNote.omegaPow β) ∧
        IDerivable A (ThetaNote.theta (α + ThetaNote.omegaPow β))
          (ThetaNote.adjoin (ThetaNote.adjoin (ThetaNote.Hop (α + ThetaNote.omegaPow β)) X) {g.1})
          (ThetaNote.theta (α + ThetaNote.omegaPow (f g))) (∼(unfold A g t) :: Γ) := by
      intro g hg
      have d0' := d0 g hg
      rw [ThetaNote.adjoin_adjoin] at d0'
      rw [ThetaNote.adjoin_adjoin]
      exact step (f g) (hf g hg) (X ∪ {g.1}) (∼(unfold A g t) :: Γ)
        (sigmaOmega_cons (sigmaOmega_unfold_of_ne_top A (Stage.ne_top_of_lt hg) t).2 hΓ)
        (ThetaNote.Hop_mono Set.subset_union_left hα) (hX.union_singleton haH haΩ hg) d0'
    exact .nstage (fun g => ThetaNote.theta (α + ThetaNote.omegaPow (f g))) hθη hΓη hm
      (fun g hg => (p g hg).1) fun g hg => (p g hg).2
  | @fix _ _ _ t α₀ _ _ hm _ h0 d0 =>
    subst hH
    have hβ₀ : α₀ ∈ ThetaNote.Hop α X := by
      have h := d0.height_mem; rwa [adjoin_empty] at h
    have hlt : α + ThetaNote.omegaPow α₀ < α + ThetaNote.omegaPow β :=
      ThetaNote.add_lt_add_left α (ThetaNote.omegaPow_lt_omegaPow h0)
    have hθ : ThetaNote.theta (α + ThetaNote.omegaPow α₀) <
        ThetaNote.theta (α + ThetaNote.omegaPow β) :=
      ThetaNote.theta_lt_theta_of_mem_Hop hX (le_of_lt (ThetaNote.lt_add_omegaPow_hull α α₀))
        hlt ((ThetaNote.Hop_nice α).add_mem hα ((ThetaNote.Hop_nice α).omegaPow_mem hβ₀))
    let b : Stage := ⟨ThetaNote.theta (α + ThetaNote.omegaPow α₀),
      le_of_lt (ThetaNote.theta_lt_Omega _)⟩
    have hbΩ : b.1 < ThetaNote.Omega := ThetaNote.theta_lt_Omega _
    have hbH : b.1 ∈ ThetaNote.adjoin (ThetaNote.Hop (α + ThetaNote.omegaPow α₀)) X ∅ := by
      rw [adjoin_empty]; exact ThetaNote.theta_add_omegaPow_mem_Hop hα hβ₀
    have D0 := boundedness_unfold ((ThetaNote.Hop_isOperator _).adjoin X) hbH le_rfl hbΩ
      (ih α₀ h0 α X (unfold A Stage.top t :: Γ)
        (sigmaOmega_cons (sigmaOmega_unfold_top hA t) hΓ) hα hX d0)
    refine .stage (a := Stage.top) b hθη hΓη hm hbΩ hθ ?_ hθ
      ((D0.mono_rank (le_of_lt hθ)).mono_op (hopH _ X (le_of_lt hlt)))
    rw [adjoin_empty] at hbH ⊢
    exact ThetaNote.Hop_subset_Hop hlt X hbH
  | @cut _ _ _ ψ α₀ _ _ hr h0 d0 d1 =>
    subst hH
    rcases rk_le_Omega_cases (rk_le_Omega_of_lt hr) with hlt | ⟨t, rfl⟩ | ⟨t, rfl⟩
    · have hσ := sigmaOmega_of_rk_lt_Omega hlt
      obtain ⟨l0, D0⟩ := step α₀ h0 X (ψ :: Γ) (sigmaOmega_cons hσ.1 hΓ) hα hX d0
      obtain ⟨-, D1⟩ := step α₀ h0 X (∼ψ :: Γ) (sigmaOmega_cons hσ.2 hΓ) hα hX d1
      have hψ : params ψ ⊆ ThetaNote.Hop α X := by
        have h := d0.params_head_subset; rwa [adjoin_empty] at h
      exact .cut hθη hΓη (hmem _ ((ThetaNote.Hop_nice α).rk_mem hψ) hlt) l0 D0 D1
    · exact cutI α₀ h0 t d0 d1
    · exact cutI α₀ h0 t d1 d0

/-- **Freund, Theorem 6.7 (Collapsing)**: for a `Σ(Ω)` sequent `Γ`, a positive operator form
`A`, `α ∈ H_α(X)` and `X ⊆ ⋂ {C^ξ(ϑ ξ) | α ≺ ξ}`,

    `H_α[X] ⊢^β_{Ω+1} Γ  ⇒  H_η[X] ⊢^{ϑη}_{ϑη} Γ`  for  `η = α + ω(β)`. -/
theorem collapsing (hA : Positive A) {α β : ThetaNote} {X : Set ThetaNote} {Γ : Sequent LIinf}
    (hΓ : ∀ φ ∈ Γ, SigmaOmega φ) (hα : α ∈ ThetaNote.Hop α X) (hX : ThetaNote.HullHyp α X)
    (d : IDerivable A (ThetaNote.Omega + ThetaNote.one)
      (ThetaNote.adjoin (ThetaNote.Hop α) X) β Γ) :
    IDerivable A (ThetaNote.theta (α + ThetaNote.omegaPow β))
      (ThetaNote.adjoin (ThetaNote.Hop (α + ThetaNote.omegaPow β)) X)
      (ThetaNote.theta (α + ThetaNote.omegaPow β)) Γ :=
  collapsing_aux hA β α X Γ hΓ hα hX d

/-- Theorem 6.7 for `α = 0` and `X = ∅`, the form used in Freund's Corollary 7.2:
`H_0 ⊢^β_{Ω+1} Γ ⇒ H_η ⊢^{ϑη}_{ϑη} Γ` for `η = ω(β)`. -/
theorem collapsing_zero (hA : Positive A) {β : ThetaNote} {Γ : Sequent LIinf}
    (hΓ : ∀ φ ∈ Γ, SigmaOmega φ)
    (d : IDerivable A (ThetaNote.Omega + ThetaNote.one) (ThetaNote.Hop ThetaNote.zero) β Γ) :
    IDerivable A (ThetaNote.theta (ThetaNote.omegaPow β))
      (ThetaNote.Hop (ThetaNote.omegaPow β))
      (ThetaNote.theta (ThetaNote.omegaPow β)) Γ := by
  have e : ∀ a : ThetaNote, ThetaNote.adjoin (ThetaNote.Hop a) ∅ = ThetaNote.Hop a := fun a => by
    funext Y; simp [ThetaNote.adjoin]
  have h := collapsing (X := ∅) hA hΓ ((ThetaNote.Hop_nice _).zero_mem)
    (Set.empty_subset _) (by rw [e]; exact d)
  rwa [e, ThetaNote.zero_add] at h

end Collapse

end InductiveDef

end OrdinalAnalysis
