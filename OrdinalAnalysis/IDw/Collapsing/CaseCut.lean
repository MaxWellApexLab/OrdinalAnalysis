/-
  Theorem 4.8 for `ID_ω` (`Statement.lean`), the case of the clause (Cut) — proved (no `sorry`),
  for every `m : WithTop ℕ`, including the limit `m = ⊤` (`μ = Ω_ω`).  Transcribed from
  `IDn/Collapsing/CaseCut.lean` (see its header for cases 4.1–4.3 and the step (□)); the only
  place of the whole collapsing proof where `μ` itself is inspected.

  Source: W. Buchholz, *A simplified version of local predicativity* (1992), p. 28 (the step
  (□), cases 4.1, 4.2, 4.3) and p. 29; A. Freund, arXiv:2204.09321, Theorem 6.7 (`cutI`);
  the design notes

  **Where the cut rank sits.**  `rk C ≺ μ = muBarW m`.
  * `m = ↑(m₁ + 1)` (`IDn`): `rk C ⪯ Ω_{m₁+1}`.
  * `m = ⊤`, `μ = Ω_ω`: `rk C ≺ Ω_ω`, so `rk C ≺ Ω_{σ+1}` for some finite `σ`
    (`ThetaVNoteD.exists_Omega_of_lt_OmegaW`, the `CollapsingLimit` window fact of
    `Ordinal/Collapsing/Limit.lean`).  In particular no cut
    formula containing `Jlev ⊤` occurs (`rk (Jlev ⊤ ..) = Ω_ω`).
  In both cases `π := Ω_{p+1}` (Lean `Omega p`) is the least `Omega p ⪰ rk C`, `p` finite, and
  `↑p < m`.  From here on the proof is `IDn`'s, with `μ = muBarW m`:
  * **4.1** `rk C ≺ κ`: side induction hypothesis on both premises and a cut.
  * **4.2** `κ ⪯ rk C ≺ π`: S.I.H. at `π`, then (□).
  * **4.3** `rk C = π`: `±I_{p+1}^{≺0} t` dropped; `±I_p t` with `p = k` (Freund's cut on
    `I_k^{≺β} t`) or `p > k` (S.I.H. at `π`, boundedness, Exercise 6.6, (□) with `C' = I_p^{≺β} t`).
  * **(□)** (`box`, now for `m : WithTop ℕ`, `↑p < m`): predicative cut elimination on
    `(Ω_p, Ω_{p+1})` (`hyp.predCut`), the **main** induction hypothesis at `μ' = Ω̄_p` (`↑p < m`;
    at `m = ⊤`: `μ' ≺ Ω_ω`), and `α* = γ' + ω^{μ'+μ'+β'} ≺ α̂` since `μ' + μ' + β' ≺ Ω_{p+1} ⪯
    μ` (𝒜4) — at `m = ⊤`: `≺ Ω_ω ⪯ Ω_ω·2 + α`, `Ω_ω` additively principal.  `predCut`'s side
    condition `ω^{Ω̄_{p+1}·2} ⪯ γ'` comes from `ω^{μ·2} ⪯ δ`: at `m = ⊤`, `Ω̄_{p+1}·2 ≺ Ω_ω ⪯
    Ω_ω·2` (`muBar_add_muBar_le`).

  The statement of `collapse_case_cut` is `CollapseCases.cut` of `Statement.lean`, verbatim.
-/
import OrdinalAnalysis.IDw.Collapsing.Statement

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Collapsing

open LO LO.FirstOrder

variable {A : FormJ}

/-! ### Small facts -/

theorem rk_mem_of_head {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H)
    {ρ α : ThetaVNoteD} {C : Proposition LIinfW} {Γ : Sequent LIinfW}
    (d : IDwDerivable A ρ H α (C :: Γ)) : rk C ∈ H ∅ :=
  hH.rk_mem' (fun s hs => d.params_head_subset ⟨s, hs, rfl⟩)

theorem params_tail_subset {H : Set ThetaVNoteD → Set ThetaVNoteD} {ρ α : ThetaVNoteD}
    {C : Proposition LIinfW} {Γ : Sequent LIinfW} (d : IDwDerivable A ρ H α (C :: Γ)) :
    paramsVal Γ ⊆ H ∅ := by
  have h := d.params_subset
  rw [paramsVal_cons] at h
  exact Set.subset_union_right.trans h

/-- The rank of `I_k^{≺b} t` for `Ω_k ≺ b`, `b` principal: `Ω_k + ω·b = b`. -/
theorem rk_stageAt_prin {k : ℕ} {b : StageAt k} (hp : ThetaVTerm.IsPrin b.1.1)
    (hb : ThetaVNoteD.OmegaBelow k < b.1) (t : SyntacticTerm LIinfW) :
    rk (stageAt (⟨k, b⟩ : Stage) t) = b.1 := by
  rw [rk_stageAt]
  show ThetaVNoteD.OmegaBelow k + ThetaVNoteD.omegaMul b.1 = b.1
  have e : ThetaVNoteD.omegaPow b.1 = b.1 := ThetaVNoteD.omegaPow_eq_self_iff.mpr hp
  have h1 : ThetaVNoteD.OmegaBelow k + ThetaVNoteD.omegaPow b.1 = ThetaVNoteD.omegaPow b.1 :=
    ThetaVNoteD.add_omegaPow_of_lt (by rw [e]; exact hb)
  rw [ThetaVNoteD.omegaMul_prin hp]
  rw [e] at h1
  exact h1

/-- `Ω_{p+1} ⪯ Ω̄_m` for `↑p < m`: a regular `π ≺ μ` (at `m = ⊤`: `Ω_{p+1} ≺ Ω_ω`). -/
theorem Omega_le_muBarW {p : ℕ} {m : WithTop ℕ} (h : (p : WithTop ℕ) < m) :
    ThetaVNoteD.Omega p ≤ muBarW m := by
  induction m using WithTop.recTopCoe with
  | top => exact le_of_lt (ThetaVNoteD.Omega_lt_OmegaW p)
  | coe m => exact Omega_le_muBar (WithTop.coe_lt_coe.mp h)

/-- `Ω̄_{s+2}·2 ⪯ μ·2` for `↑(s+1) < m` (the side condition of `predCut` in (□)); at `m = ⊤`
since `Ω̄_{s+2}·2 ≺ Ω_ω` (`Ω_ω` additively principal). -/
theorem muBar_add_muBar_le {s : ℕ} {m : WithTop ℕ} (h : ((s + 1 : ℕ) : WithTop ℕ) < m) :
    muBar (s + 2) + muBar (s + 2) ≤ muBarW m + muBarW m := by
  induction m using WithTop.recTopCoe with
  | top =>
    show muBar (s + 2) + muBar (s + 2) ≤ ThetaVNoteD.OmegaW + ThetaVNoteD.OmegaW
    refine le_of_lt (lt_of_lt_of_le ?_ (ThetaVNoteD.le_add_right _ _))
    exact ThetaVNoteD.add_lt_prin ThetaVTerm.isPrin_OmegaW (muBar_lt_OmegaW _) (muBar_lt_OmegaW _)
  | coe m =>
    show muBar (s + 2) + muBar (s + 2) ≤ muBar m + muBar m
    have hm : s + 1 < m := WithTop.coe_lt_coe.mp h
    rcases Nat.lt_or_eq_of_le (show s + 2 ≤ m by omega) with h' | h'
    · refine le_of_lt (lt_of_lt_of_le ?_ (le_trans (Omega_le_muBar h')
        (ThetaVNoteD.le_add_right _ _)))
      exact ThetaVNoteD.add_lt_prin trivial (muBar_lt_Omega _) (muBar_lt_Omega _)
    · rw [h']

/-! ### The step (□) -/

/-- **Buchholz's (□)** (p. 28), for `π = Ω_{p+1}` (Lean `Omega p`), `1 ≤ p`, `k ≤ p`, `↑p < m`
(`m : WithTop ℕ`, so also for `μ = Ω_ω`): `H_{γ'}[Θ] ⊢^β_β Γ, C'` and `H_{γ'}[Θ] ⊢^β_β Γ, ¬C'`
with `γ' = γ + δ`, `ω^{μ+μ} ⪯ δ ≺ ω^{μ+μ+α}`, `γ' ∈ H_{γ'}[Θ]`, `rk C' ≺ π`, `Ω_p ≺ β ≺ π` give
`H_α̂[Θ] ⊢^{ψ_κ α̂}_{ψ_κ α̂} Γ`. -/
theorem box (hyp : CollapseHyps A) {m : WithTop ℕ}
    (mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    {k : ℕ} {γ α : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (hX : ThetaVNoteD.HullHypGe k γ X) (hα : α ∈ ThetaVNoteD.HopS γ X)
    {p : ℕ} (hkp : k ≤ p) (hpm : (p : WithTop ℕ) < m) (hp1 : 1 ≤ p)
    {γ' δ β : ThetaVNoteD} (he : γ' = γ + δ)
    (hδ : δ < ThetaVNoteD.omegaPow (muBarW m + muBarW m + α))
    (hωδ : ThetaVNoteD.omegaPow (muBarW m + muBarW m) ≤ δ) (hγ' : γ' ∈ ThetaVNoteD.HopS γ' X)
    (hβp : ThetaVNoteD.OmegaBelow p < β) (hβΩ : β < ThetaVNoteD.Omega p)
    {C : Proposition LIinfW} (hC : rk C < ThetaVNoteD.Omega p)
    (d0 : IDwDerivable A β (Hg γ' X) β (C :: Γ))
    (d1 : IDwDerivable A β (Hg γ' X) β (∼C :: Γ)) :
    Concl A k γ X m α Γ := by
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  have hγγ' : γ ≤ γ' := he ▸ ThetaVNoteD.le_add_right γ δ
  have hX' : ThetaVNoteD.HullHypGe k γ' X := hX.mono hγγ'
  have hXp : ThetaVNoteD.HullHypGe (s + 1) γ' X := hX'.up hkp
  have hN := Hg_niceS γ' X
  have hβH : β ∈ ThetaVNoteD.HopS γ' X := mem_Hg_empty.mp d0.height_mem
  have hCH : rk C ∈ ThetaVNoteD.HopS γ' X := mem_Hg_empty.mp (rk_mem_of_head hN d0)
  -- the cut, at rank `ρ₀ = max(rk C, β) + 1`
  let ρ₀ := ThetaVNoteD.succ (max (rk C) β)
  have hmaxH : max (rk C) β ∈ ThetaVNoteD.HopS γ' X := by
    rcases le_total (rk C) β with h | h
    · rw [max_eq_right h]; exact hβH
    · rw [max_eq_left h]; exact hCH
  have hρ₀H : ρ₀ ∈ ThetaVNoteD.HopS γ' X := (ThetaVNoteD.HopS_nice γ').succ_mem hmaxH
  have hρ₀Ω : ρ₀ < ThetaVNoteD.Omega (s + 1) :=
    ThetaVNoteD.succ_lt_prin trivial (max_lt hC hβΩ)
  have hμρ₀ : muBar (s + 1) ≤ ρ₀ := by
    rw [muBar_succ, ThetaVNoteD.add_one_eq_succ]
    exact ThetaVNoteD.succ_le_succ (le_trans (le_of_lt hβp) (le_max_right _ _))
  have hβρ₀ : β ≤ ρ₀ := le_trans (le_max_right _ _) (le_of_lt (ThetaVNoteD.lt_succ _))
  have hCρ₀ : rk C < ρ₀ := lt_of_le_of_lt (le_max_left _ _) (ThetaVNoteD.lt_succ _)
  have hsβH : ThetaVNoteD.succ β ∈ ThetaVNoteD.HopS γ' X :=
    (ThetaVNoteD.HopS_nice γ').succ_mem hβH
  have D : IDwDerivable A ρ₀ (Hg γ' X) (ThetaVNoteD.succ β) Γ :=
    .cut (mem_Hg_empty.mpr hsβH) (params_tail_subset d0) hCρ₀ (ThetaVNoteD.lt_succ β)
      (d0.mono_rank hβρ₀) (d1.mono_rank hβρ₀)
  -- predicative cut elimination on `(Ω_p, Ω_{p+1})`
  have hωγ' : ThetaVNoteD.omegaPow (muBar (s + 2) + muBar (s + 2)) ≤ γ' := by
    rw [he]
    exact le_trans (ThetaVNoteD.omegaPow_le_omegaPow (muBar_add_muBar_le hpm))
      (le_trans hωδ (ThetaVNoteD.le_add_left γ δ))
  obtain ⟨β', hβ'H, hβ'Ω, D'⟩ := hyp.predCut s hγ' hXp hωγ' hsβH hρ₀H hμρ₀ hρ₀Ω
    (ThetaVNoteD.succ_lt_prin trivial hβΩ) D
  -- the main induction hypothesis at `μ' = Ω̄_p`, `↑p < m`
  have D'' := mih ((s + 1 : ℕ) : WithTop ℕ) hpm β' k γ' X Γ hΓ hγ' hX' D'
  -- `α* := γ' + ω^{μ'+μ'+β'} ≺ α̂`
  have hexp : muBarW ((s + 1 : ℕ) : WithTop ℕ) + muBarW ((s + 1 : ℕ) : WithTop ℕ) + β' <
      muBarW m + muBarW m + α := by
    have h1 : muBar (s + 1) + muBar (s + 1) + β' < ThetaVNoteD.Omega (s + 1) :=
      ThetaVNoteD.add_lt_prin trivial
        (ThetaVNoteD.add_lt_prin trivial (muBar_lt_Omega _) (muBar_lt_Omega _)) hβ'Ω
    exact lt_of_lt_of_le h1 (le_trans (Omega_le_muBarW hpm)
      (le_trans (ThetaVNoteD.le_add_right _ _) (ThetaVNoteD.le_add_right _ _)))
  have hlt : hat γ' (muBarW ((s + 1 : ℕ) : WithTop ℕ)) β' < hat γ (muBarW m) α := by
    show γ' + ThetaVNoteD.omegaPow (muBarW ((s + 1 : ℕ) : WithTop ℕ) +
      muBarW ((s + 1 : ℕ) : WithTop ℕ) + β') < γ + ThetaVNoteD.omegaPow (muBarW m + muBarW m + α)
    rw [he, ThetaVNoteD.add_assoc]
    exact ThetaVNoteD.add_lt_add_left γ
      (ThetaVNoteD.add_lt_omegaPow hδ (ThetaVNoteD.omegaPow_lt_omegaPow hexp))
  have hψ : psi k (hat γ' (muBarW ((s + 1 : ℕ) : WithTop ℕ)) β') <
      psi k (hat γ (muBarW m) α) :=
    psi_lt_psi hX' (gamma_le_hat γ' _ β') hlt (hat_mem_self hγ' hβ'H) (dom_hat hX' hγ' hβ'H)
      (dom_hat hX hγ hα)
  exact (((D''.mono_rank (le_of_lt hψ)).mono_op (Hg_mono (le_of_lt hlt) X)).mono_height
    (le_of_lt hψ) (mem_Hg_empty.mpr (psi_hat_mem hX hγ hα)))

/-! ### The cut case -/

/-- **Case `cut`**: (Cut) of rank `≺ μ = muBarW m`, `m : WithTop ℕ` (Buchholz case 4: 4.1 rank
`≺ κ`; 4.2 `κ ⪯` rank non-regular, the S.I.H. at the next regular `π` and (□); 4.3 rank `= π`
regular, the cut on `I_p t`).  At `m = ⊤` the next regular `π = Ω_{p+1}` exists because
`rk ψ ≺ Ω_ω` (`ThetaVNoteD.exists_Omega_of_lt_OmegaW`). -/
theorem collapse_case_cut (hyp : CollapseHyps A) {m : WithTop ℕ} {α : ThetaVNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaVNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : ℕ} {γ : ThetaVNoteD} {X : Set ThetaVNoteD} {Γ : Sequent LIinfW}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaVNoteD.HopS γ X)
    (hX : ThetaVNoteD.HullHypGe k γ X)
    {ψ : Proposition LIinfW} {α₀ : ThetaVNoteD}
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅) (hr : rk ψ < muBarW m)
    (h0 : α₀ < α) (d0 : IDwDerivable A (muBarW m) (Hg γ X) α₀ (ψ :: Γ))
    (d1 : IDwDerivable A (muBarW m) (Hg γ X) α₀ (∼ψ :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp hα
  have hα₀ : α₀ ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp d0.height_mem
  have hθ := psi_hat_lt_psi_hat (k := k) (m := m) hX hγ hα₀ hα' h0
  have hop : ∀ Z, Hg (hat γ (muBarW m) α₀) X Z ⊆ Hg (hat γ (muBarW m) α) X Z :=
    Hg_mono (le_of_lt (hat_lt_hat γ _ h0)) X
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBarW m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  have hηH : psi k (hat γ (muBarW m) α) ∈ Hg (hat γ (muBarW m) α) X ∅ :=
    mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')
  have hψH : rk ψ ∈ ThetaVNoteD.HopS γ X := mem_Hg_empty.mp (rk_mem_of_head (Hg_niceS γ X) d0)
  -- the common shape of the conclusion: a collapsed derivation of height `ψ_κ α̂₀`
  have lift : ∀ {H' : Set ThetaVNoteD → Set ThetaVNoteD} {β₀ : ThetaVNoteD},
      β₀ ≤ psi k (hat γ (muBarW m) α) → (∀ Z, H' Z ⊆ Hg (hat γ (muBarW m) α) X Z) →
      IDwDerivable A β₀ H' β₀ Γ → Concl A k γ X m α Γ := fun hle hH' D =>
    ((D.mono_rank hle).mono_op hH').mono_height hle hηH
  -- a finite level `q` with `rk ψ ⪯ Ω_{q+1}`, `↑q < m`: `m = ↑(q + 1)` (`IDn`), or `m = ⊤` and
  -- `rk ψ ≺ Ω_ω`, so `rk ψ ≺ Ω_{q+1}` for some `q` (the limit case)
  have hex : ∃ q : ℕ, rk ψ ≤ ThetaVNoteD.Omega q ∧ (q : WithTop ℕ) < m := by
    clear lift hηH hΓη hop hθ sih mih d0 d1
    induction m using WithTop.recTopCoe with
    | top =>
      obtain ⟨σ, hσ⟩ := ThetaVNoteD.exists_Omega_of_lt_OmegaW (show rk ψ < ThetaVNoteD.OmegaW from hr)
      exact ⟨σ, le_of_lt hσ, WithTop.coe_lt_top σ⟩
    | coe m =>
      cases m with
      | zero => exact absurd hr (not_lt_of_ge (ThetaVNoteD.zero_le' _))
      | succ m₁ =>
        exact ⟨m₁, le_of_lt_add_one_col hr, WithTop.coe_lt_coe.mpr (Nat.lt_succ_self m₁)⟩
  obtain ⟨q₀, hq₀, hq₀m⟩ := hex
  by_cases hκ : rk ψ < ThetaVNoteD.Omega k
  · -- 4.1: `rk ψ ≺ κ`
    have hσ := sigmaW_of_rk_lt_Omega hκ
    have D0 := sih α₀ h0 k γ X _ (sigmaW_cons hσ.1 hΓ) hγ hX d0
    have D1 := sih α₀ h0 k γ X _ (sigmaW_cons hσ.2 hΓ) hγ hX d1
    exact .cut hηH hΓη (lt_psi_hat hX hγ hα' hψH hκ) hθ
      ((D0.mono_rank (le_of_lt hθ)).mono_op hop) ((D1.mono_rank (le_of_lt hθ)).mono_op hop)
  have hκ' : ThetaVNoteD.Omega k ≤ rk ψ := le_of_not_gt hκ
  -- `π = Ω_{p+1}`: the least `Omega p ⪰ rk ψ`
  classical
  have hex' : ∃ p, rk ψ ≤ ThetaVNoteD.Omega p := ⟨q₀, hq₀⟩
  obtain ⟨p, hp, hpmin⟩ : ∃ p, rk ψ ≤ ThetaVNoteD.Omega p ∧ ∀ q, q < p →
      ¬ rk ψ ≤ ThetaVNoteD.Omega q :=
    ⟨Nat.find hex', Nat.find_spec hex', fun q hq => Nat.find_min hex' hq⟩
  have hpq₀ : p ≤ q₀ := by
    by_contra h
    exact hpmin q₀ (by omega) hq₀
  have hpm : (p : WithTop ℕ) < m := lt_of_le_of_lt (WithTop.coe_le_coe.mpr hpq₀) hq₀m
  have hkp : k ≤ p := by
    by_contra h
    have h' : ThetaVNoteD.Omega p < ThetaVNoteD.Omega k :=
      ThetaVNoteD.Omega_lt_Omega_iff.mpr (by omega)
    exact absurd (lt_of_lt_of_le h' (le_trans hκ' hp)) (lt_irrefl _)
  have hΓP : ∀ φ ∈ Γ, SigmaW p φ := sigmaW_mono_seq hkp hΓ
  have hXP : ThetaVNoteD.HullHypGe p γ X := hX.up hkp
  -- `α̂₀`, `α̂₀ + ω^{μ+μ+α₀}` and their memberships
  set μ := muBarW m with hμ
  have hη₀ : hat γ μ α₀ ∈ ThetaVNoteD.HopS (hat γ μ α₀) X := hat_mem hγ hα₀
  have hγη₀ : γ ≤ hat γ μ α₀ := gamma_le_hat γ μ α₀
  have hα₀η₀ : α₀ ∈ ThetaVNoteD.HopS (hat γ μ α₀) X :=
    ThetaVNoteD.HopS_subset_HopS_of_le hγη₀ X hα₀
  have hη₁ : hat (hat γ μ α₀) μ α₀ ∈ ThetaVNoteD.HopS (hat (hat γ μ α₀) μ α₀) X :=
    hat_mem hη₀ hα₀η₀
  have hη₁lt : hat (hat γ μ α₀) μ α₀ < hat γ μ α := by
    show γ + ThetaVNoteD.omegaPow (μ + μ + α₀) + ThetaVNoteD.omegaPow (μ + μ + α₀) <
      γ + ThetaVNoteD.omegaPow (μ + μ + α)
    have h := ThetaVNoteD.omegaPow_lt_omegaPow (ThetaVNoteD.add_lt_add_left (μ + μ) h0)
    rw [ThetaVNoteD.add_assoc]
    exact ThetaVNoteD.add_lt_add_left γ (ThetaVNoteD.add_lt_omegaPow h h)
  have hη₁eq : hat (hat γ μ α₀) μ α₀ =
      γ + (ThetaVNoteD.omegaPow (μ + μ + α₀) + ThetaVNoteD.omegaPow (μ + μ + α₀)) :=
    ThetaVNoteD.add_assoc _ _ _
  have hδ₁ : ThetaVNoteD.omegaPow (μ + μ + α₀) + ThetaVNoteD.omegaPow (μ + μ + α₀) <
      ThetaVNoteD.omegaPow (μ + μ + α) := by
    have h := ThetaVNoteD.omegaPow_lt_omegaPow (ThetaVNoteD.add_lt_add_left (μ + μ) h0)
    exact ThetaVNoteD.add_lt_omegaPow h h
  have hωμ : ThetaVNoteD.omegaPow (μ + μ) ≤ ThetaVNoteD.omegaPow (μ + μ + α₀) :=
    ThetaVNoteD.omegaPow_le_omegaPow (ThetaVNoteD.le_add_right (μ + μ) α₀)
  rcases lt_or_eq_of_le hp with hlt | heq
  · -- 4.2: `κ ⪯ rk ψ ≺ π`, `rk ψ` not regular
    have hkp' : k < p := by
      by_contra h
      have h' : ThetaVNoteD.Omega p ≤ ThetaVNoteD.Omega k := by
        rcases Nat.lt_or_eq_of_le (show p ≤ k by omega) with h'' | h''
        · exact le_of_lt (ThetaVNoteD.Omega_lt_Omega_iff.mpr h'')
        · rw [h'']
      exact absurd (lt_of_lt_of_le hlt h') (not_lt_of_ge hκ')
    have hσ := sigmaW_of_rk_lt_Omega (k := p) hlt
    have D0 := sih α₀ h0 p γ X _ (sigmaW_cons hσ.1 hΓP) hγ hXP d0
    have D1 := sih α₀ h0 p γ X _ (sigmaW_cons hσ.2 hΓP) hγ hXP d1
    exact box hyp (γ' := hat γ μ α₀) (δ := ThetaVNoteD.omegaPow (μ + μ + α₀)) mih hΓ hγ hX
      hα' hkp hpm (by omega) rfl
      (ThetaVNoteD.omegaPow_lt_omegaPow (ThetaVNoteD.add_lt_add_left (μ + μ) h0)) hωμ hη₀
      (OmegaBelow_lt_psi (dom_hat hXP hγ hα₀)) (psi_lt_Omega _ _) hlt D0 D1
  -- 4.3: `rk ψ = π`
  obtain ⟨s, t, hform, hs⟩ := rk_eq_Omega_cases heq
  rcases hs with ⟨hsl, hsv⟩ | ⟨-, hsv⟩
  swap
  · -- `±I_{p+1}^{≺0} t`: the empty disjunction is dropped from its premise
    have dΓ : IDwDerivable A μ (Hg γ X) α₀ Γ := by
      rcases hform with rfl | rfl
      · exact drop_stage_zero hsv (Hg_isOperator γ X) d0
      · exact drop_stage_zero hsv (Hg_isOperator γ X) d1
    exact lift (le_of_lt hθ) hop (sih α₀ h0 k γ X Γ hΓ hγ hX dΓ)
  -- `±I_p t`
  have hsP : s = Stage.top p := (stage_eq_top_iff_of_lvl_eq hsl).mpr hsv
  subst hsP
  -- the cut on `I_p t`, both premises given
  have cutI : IDwDerivable A μ (Hg γ X) α₀ (IOmegaAt p t :: Γ) →
      IDwDerivable A μ (Hg γ X) α₀ (∼(IOmegaAt p t) :: Γ) → Concl A k γ X m α Γ := by
    intro e0 e1
    -- the positive premise: S.I.H. at `π`, boundedness at level `p`, stage `β = ψ_π α̂₀`
    have hσ0 : SigmaW p (IOmegaAt p t) := (sigmaW_stageAt_iff p (Stage.top p) t).mpr le_rfl
    have E0 := sih α₀ h0 p γ X _ (sigmaW_cons hσ0 hΓP) hγ hXP e0
    have hDη₀ := dom_hat (m := m) hXP hγ hα₀
    let b : StageAt p := ⟨psi p (hat γ μ α₀), le_of_lt (psi_lt_Omega _ _)⟩
    have hbΩ : b.1 < ThetaVNoteD.Omega p := psi_lt_Omega _ _
    have hbH : b.1 ∈ Hg (hat γ μ α₀) X ∅ := mem_Hg_empty.mpr (psi_hat_mem hXP hγ hα₀)
    have E0b := hyp.bound p b (Hg_isOperator _ _) hbH le_rfl hbΩ E0
    rw [capAt_IOmegaAt] at E0b
    -- the negative premise: to `H_{α̂₀}[Θ]`, Exercise 6.6, S.I.H. at `π` with `γ := α̂₀`
    have e1' := hyp.negStage p b (Hg_isOperator _ _) hbH (e1.mono_op (Hg_mono hγη₀ X))
    have hσ1 : SigmaW p (nstageAt (⟨p, b⟩ : Stage) t) := by
      refine (sigmaW_nstageAt_iff p _ t).mpr ⟨le_rfl, fun e => ?_⟩
      have := congrArg Stage.val e
      rw [Stage.val_top] at this
      exact absurd this (ne_of_lt hbΩ)
    have hXPη₀ : ThetaVNoteD.HullHypGe p (hat γ μ α₀) X := hXP.mono hγη₀
    have E1 := sih α₀ h0 p (hat γ μ α₀) X _ (sigmaW_cons hσ1 hΓP) hη₀ hXPη₀ e1'
    have hDη₁ := dom_hat (m := m) hXPη₀ hη₀ hα₀η₀
    have hb₁ : psi p (hat γ μ α₀) < psi p (hat (hat γ μ α₀) μ α₀) :=
      psi_lt_psi hXP hγη₀ (gamma_lt_hat _ μ α₀) (hat_mem_self hγ hα₀) hDη₀ hDη₁
    have hb₁H : psi p (hat (hat γ μ α₀) μ α₀) ∈ Hg (hat (hat γ μ α₀) μ α₀) X ∅ :=
      mem_Hg_empty.mpr (psi_hat_mem hXPη₀ hη₀ hα₀η₀)
    have hopη : ∀ Z, Hg (hat γ μ α₀) X Z ⊆ Hg (hat (hat γ μ α₀) μ α₀) X Z :=
      Hg_mono (gamma_le_hat _ μ α₀) X
    -- both premises at height and rank `β₁ = ψ_π(α̂₀ + ω^{μ+μ+α₀})`
    have F0 : IDwDerivable A (psi p (hat (hat γ μ α₀) μ α₀)) (Hg (hat (hat γ μ α₀) μ α₀) X)
        (psi p (hat (hat γ μ α₀) μ α₀)) (stageAt (⟨p, b⟩ : Stage) t :: Γ) :=
      ((E0b.mono_rank (le_of_lt hb₁)).mono_op hopη).mono_height (le_of_lt hb₁) hb₁H
    rcases Nat.lt_or_eq_of_le hkp with hkp' | hkp'
    · -- `p > k`: Buchholz's 4.3, then (□) with `C' = I_p^{≺β} t`
      have hC : rk (stageAt (⟨p, b⟩ : Stage) t) < ThetaVNoteD.Omega p := by
        refine rk_lt_Omega_iff.mpr ⟨(sigmaW_stageAt_iff p _ t).mpr le_rfl, ?_⟩
        rw [neg_stageAt]
        exact hσ1
      exact box hyp
        (δ := ThetaVNoteD.omegaPow (μ + μ + α₀) + ThetaVNoteD.omegaPow (μ + μ + α₀))
        mih hΓ hγ hX hα' hkp hpm (by omega) hη₁eq hδ₁
        (le_trans hωμ (ThetaVNoteD.le_add_right _ _)) hη₁ (OmegaBelow_lt_psi hDη₁)
        (psi_lt_Omega _ _) hC F0 E1
    · -- `p = k`: Freund's cut on `I t`, a cut on `I_k^{≺β} t` of rank `β`
      subst hkp'
      have hDα := dom_hat (m := m) hX hγ hα'
      have hη₁H : hat (hat γ μ α₀) μ α₀ ∈ ThetaVNoteD.HopS γ X :=
        (ThetaVNoteD.HopS_nice γ).add_mem (hat_mem_self hγ hα₀)
          ((ThetaVNoteD.HopS_nice γ).omegaPow_mem (exp_mem hα₀))
      have hb₂' : psi k (hat (hat γ μ α₀) μ α₀) < psi k (hat γ μ α) :=
        psi_lt_psi hX (le_trans hγη₀ (gamma_le_hat _ μ α₀)) hη₁lt hη₁H hDη₁ hDα
      have hrk : rk (stageAt (⟨k, b⟩ : Stage) t) < psi k (hat γ μ α) := by
        have hp' : ThetaVTerm.IsPrin b.1.1 := (Notn.thetaVLevel k).isPrin_theta hDη₀
        rw [rk_stageAt_prin hp' (OmegaBelow_lt_psi hDη₀)]
        exact lt_trans hb₁ hb₂'
      have hop₁ : ∀ Z, Hg (hat (hat γ μ α₀) μ α₀) X Z ⊆ Hg (hat γ μ α) X Z :=
        Hg_mono (le_of_lt hη₁lt) X
      exact .cut (ψ := stageAt (⟨k, b⟩ : Stage) t) hηH hΓη hrk hb₂'
        ((F0.mono_rank (le_of_lt hb₂')).mono_op hop₁)
        ((E1.mono_rank (le_of_lt hb₂')).mono_op hop₁)
  rcases hform with rfl | rfl
  · exact cutI d0 d1
  · exact cutI d1 d0

/-- The case lemma fills `CollapseCases.cut` (statement check against `Statement.lean`). -/
example (hyp : CollapseHyps A) (C : CollapseCases A) : CollapseCases A :=
  { C with cut := collapse_case_cut hyp }

end Collapsing

end IDw

end OrdinalAnalysis
