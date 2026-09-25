/-
  Theorem 4.8 for `ID_n` (`Statement.lean`), the case of the clause (Cut) — proved (no `sorry`).

  Source: W. Buchholz, *A simplified version of local predicativity* (1992), author preprint
  p. 28 (the step (□), cases 4.1, 4.2, 4.3) and p. 29 (end of 4.3); A. Freund,
  arXiv:2204.09321, Theorem 6.7, the two cut cases (`ID1/Collapsing.lean`, `cutI`), Theorem 5.9,
  Exercise 6.6.

  Let the cut formula `C` have rank `≺ μ = Ω̄_m`; so `m = m₁ + 1` and `rk C ⪯ Ω_{m₁+1}`.

  * **4.1, `rk C ≺ κ = Ω_{k+1}`.**  `C, ¬C ∈ Σ(κ)`, `rk C ∈ H_γ[Θ] ∩ κ ⊆ ψ_κ α̂`; the side
    induction hypothesis on both premises and a cut.
  * **4.2, `κ ⪯ rk C` not regular.**  `π := Ω_{p+1}` (Lean `Omega p`), the least `Omega p ⪰ rk C`;
    then `k < p < m`, `C, ¬C ∈ Σ(π)` and `𝒜(Θ; γ, π, μ)`; the side induction hypothesis at `π`
    gives `H_{α̂₀}[Θ] ⊢^{ψ_π α̂₀}_{ψ_π α̂₀} Γ, (¬)C`, and (□) concludes.
  * **4.3, `rk C = π` regular.**  Under `IDn/Rank.lean`'s rank the formulas of rank `Ω_{p+1}` are
    `±I_p t` and `±I_{p+1}^{≺0} t` (`rk_eq_Omega_cases`).
    - `±I_{p+1}^{≺0} t`, the empty disjunction: dropped from its premise (`drop_stage_zero`);
      the side induction hypothesis on that premise alone.  (No counterpart in the print.)
    - `±I_p t`, `p = k`: Freund's case (`ID1/Collapsing.lean` `cutI`): positive premise
      collapsed and bounded to `Γ, I_k^{≺β} t`, `β = ψ_k α̂₀`; negative premise moved to
      `H_{α̂₀}[Θ]`, Exercise 6.6, collapsed with `γ := α̂₀`; a cut on `I_k^{≺β} t` of rank
      `Ω_k + ω·β = β ≺ ψ_k α̂`.
    - `±I_p t`, `p > k`: Buchholz's 4.3: the same two steps at `π = Ω_{p+1}` (S.I.H. at `π`,
      boundedness at level `p`, Exercise 6.6, S.I.H. at `π` with `γ := α̂₀`), then (□) with
      `C' := I_p^{≺β} t`, `rk C' ≺ π`.
  * **(□)** (`box`): from `H_{γ'}[Θ] ⊢^β_β Γ, (¬)C'`, `γ ⪯ γ' = γ + δ`,
    `ω^{μ+μ} ⪯ δ ≺ ω^{μ+μ+α}`,
    `rk C', β ≺ π = Ω_{p+1} ⪯ μ`, `Ω_p ≺ β`: a cut of rank `ρ₀ = max(rk C', β) + 1 ∈ [Ω_p + 1,
    Ω_{p+1})`, predicative cut elimination (hypothesis `predCut`, `σ = p`) down to `μ' = Ω̄_p`
    at a height `β' ∈ H_{γ'}[Θ] ∩ Ω_{p+1}`, the **main** induction hypothesis at `μ' ≺ μ`
    (`p < m`), and `α* := γ' + ω^{μ'+β'} ≺ α̂` since `μ' + β' ≺ π ⪯ μ` (Lemma 4.7 (𝒜4)).
    The print states (□) with the height of the premises equal to their cut rank and
    `σ` with `Ω_σ < ρ < Ω_{σ+1}`; here `σ = p` is forced by `Ω_p ≺ β ≺ Ω_{p+1}` (both uses of (□)
    have `β = ψ_π(…)`), which is what makes `σ ≥ k` (the hull hypothesis at `σ`) and `σ ≥ 1`
    (so `predCut` is used only on the intervals `(Ω_σ, Ω_{σ+1})`, `σ ≥ 1`, never below `Ω_1`).

  The statement of `collapse_case_cut` is `Cases.lean`'s, verbatim.
-/
import OrdinalAnalysis.IDn.Collapsing.Statement

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

namespace Collapsing

open LO LO.FirstOrder

variable {n : ℕ} {A : Fin n → Semisentence (LXIn n) 1}

/-! ### Small facts -/

theorem rk_mem_of_head {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    {ρ α : ThetaWNoteD} {C : Proposition (LIinfN n)} {Γ : Sequent (LIinfN n)}
    (d : IDnDerivable A ρ H α (C :: Γ)) : rk C ∈ H ∅ :=
  hH.rk_mem (fun s hs => d.params_head_subset ⟨s, hs, rfl⟩)

theorem params_tail_subset {H : Set ThetaWNoteD → Set ThetaWNoteD} {ρ α : ThetaWNoteD}
    {C : Proposition (LIinfN n)} {Γ : Sequent (LIinfN n)} (d : IDnDerivable A ρ H α (C :: Γ)) :
    paramsVal Γ ⊆ H ∅ := by
  have h := d.params_subset
  rw [paramsVal_cons] at h
  exact Set.subset_union_right.trans h

/-- The rank of `I_k^{≺b} t` for `Ω_k ≺ b`, `b` principal: `Ω_k + ω·b = b`. -/
theorem rk_stageAt_prin {k : Fin n} {b : StageAt k.val} (hp : ThetaWTerm.IsPrin b.1.1)
    (hb : ThetaWNoteD.OmegaBelow k.val < b.1) (t : SyntacticTerm (LIinfN n)) :
    rk (stageAt (⟨k, b⟩ : Stage n) t) = b.1 := by
  rw [rk_stageAt]
  show ThetaWNoteD.OmegaBelow k.val + ThetaWNoteD.omegaMul b.1 = b.1
  have e : ThetaWNoteD.omegaPow b.1 = b.1 := ThetaWNoteD.omegaPow_eq_self_iff.mpr hp
  have h1 : ThetaWNoteD.OmegaBelow k.val + ThetaWNoteD.omegaPow b.1 = ThetaWNoteD.omegaPow b.1 :=
    ThetaWNoteD.add_omegaPow_of_lt (by rw [e]; exact hb)
  rw [ThetaWNoteD.omegaMul_prin hp]
  rw [e] at h1
  exact h1

/-! ### The step (□) -/

/-- **Buchholz's (□)** (p. 28), for `π = Ω_{p+1}` (Lean `Omega p`), `1 ≤ p`, `k ≤ p < m`:
`H_{γ'}[Θ] ⊢^β_β Γ, C'` and `H_{γ'}[Θ] ⊢^β_β Γ, ¬C'` with `γ' = γ + δ`,
`ω^{μ+μ} ⪯ δ ≺ ω^{μ+μ+α}`,
`γ' ∈ H_{γ'}[Θ]`, `rk C' ≺ π`, `Ω_p ≺ β ≺ π` give `H_α̂[Θ] ⊢^{ψ_κ α̂}_{ψ_κ α̂} Γ`. -/
theorem box (hyp : CollapseHyps A) {m : ℕ} (mih : ∀ m' < m, ∀ α' : ThetaWNoteD, Claim A m' α')
    {k : Fin n} {γ α : ThetaWNoteD} {X : Set ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaWNoteD.HopS γ X)
    (hX : ThetaWNoteD.HullHypGe k.val γ X) (hα : α ∈ ThetaWNoteD.HopS γ X)
    {p : ℕ} (hkp : k.val ≤ p) (hpm : p < m) (hp1 : 1 ≤ p)
    {γ' δ β : ThetaWNoteD} (he : γ' = γ + δ)
    (hδ : δ < ThetaWNoteD.omegaPow (muBar m + muBar m + α))
    (hωδ : ThetaWNoteD.omegaPow (muBar m + muBar m) ≤ δ) (hγ' : γ' ∈ ThetaWNoteD.HopS γ' X)
    (hβp : ThetaWNoteD.OmegaBelow p < β) (hβΩ : β < ThetaWNoteD.Omega p)
    {C : Proposition (LIinfN n)} (hC : rk C < ThetaWNoteD.Omega p)
    (d0 : IDnDerivable A β (Hg γ' X) β (C :: Γ))
    (d1 : IDnDerivable A β (Hg γ' X) β (∼C :: Γ)) :
    Concl A k γ X m α Γ := by
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  have hγγ' : γ ≤ γ' := he ▸ ThetaWNoteD.le_add_right γ δ
  have hX' : ThetaWNoteD.HullHypGe k.val γ' X := hX.mono hγγ'
  have hXp : ThetaWNoteD.HullHypGe (s + 1) γ' X := hX'.up hkp
  have hN := Hg_niceS γ' X
  have hβH : β ∈ ThetaWNoteD.HopS γ' X := mem_Hg_empty.mp d0.height_mem
  have hCH : rk C ∈ ThetaWNoteD.HopS γ' X := mem_Hg_empty.mp (rk_mem_of_head hN d0)
  -- the cut, at rank `ρ₀ = max(rk C, β) + 1`
  let ρ₀ := ThetaWNoteD.succ (max (rk C) β)
  have hmaxH : max (rk C) β ∈ ThetaWNoteD.HopS γ' X := by
    rcases le_total (rk C) β with h | h
    · rw [max_eq_right h]; exact hβH
    · rw [max_eq_left h]; exact hCH
  have hρ₀H : ρ₀ ∈ ThetaWNoteD.HopS γ' X := (ThetaWNoteD.HopS_nice γ').succ_mem hmaxH
  have hρ₀Ω : ρ₀ < ThetaWNoteD.Omega (s + 1) :=
    ThetaWNoteD.succ_lt_prin trivial (max_lt hC hβΩ)
  have hμρ₀ : muBar (s + 1) ≤ ρ₀ := by
    rw [muBar_succ, ThetaWNoteD.add_one_eq_succ]
    exact ThetaWNoteD.succ_le_succ (le_trans (le_of_lt hβp) (le_max_right _ _))
  have hβρ₀ : β ≤ ρ₀ := le_trans (le_max_right _ _) (le_of_lt (ThetaWNoteD.lt_succ _))
  have hCρ₀ : rk C < ρ₀ := lt_of_le_of_lt (le_max_left _ _) (ThetaWNoteD.lt_succ _)
  have hsβH : ThetaWNoteD.succ β ∈ ThetaWNoteD.HopS γ' X := (ThetaWNoteD.HopS_nice γ').succ_mem hβH
  have D : IDnDerivable A ρ₀ (Hg γ' X) (ThetaWNoteD.succ β) Γ :=
    .cut (mem_Hg_empty.mpr hsβH) (params_tail_subset d0) hCρ₀ (ThetaWNoteD.lt_succ β)
      (d0.mono_rank hβρ₀) (d1.mono_rank hβρ₀)
  -- predicative cut elimination on `(Ω_p, Ω_{p+1})`
  have hωγ' : ThetaWNoteD.omegaPow (muBar (s + 2) + muBar (s + 2)) ≤ γ' := by
    rw [he]
    have hle : muBar (s + 2) + muBar (s + 2) ≤ muBar m + muBar m := by
      rcases Nat.lt_or_eq_of_le (show s + 2 ≤ m by omega) with h | h
      · refine le_of_lt (lt_of_lt_of_le ?_ (le_trans (Omega_le_muBar h)
          (ThetaWNoteD.le_add_right _ _)))
        exact ThetaWNoteD.add_lt_prin trivial (muBar_lt_Omega _) (muBar_lt_Omega _)
      · rw [h]
    exact le_trans (ThetaWNoteD.omegaPow_le_omegaPow hle)
      (le_trans hωδ (ThetaWNoteD.le_add_left γ δ))
  obtain ⟨β', hβ'H, hβ'Ω, D'⟩ := hyp.predCut s hγ' hXp hωγ' hsβH hρ₀H hμρ₀ hρ₀Ω
    (ThetaWNoteD.succ_lt_prin trivial hβΩ) D
  -- the main induction hypothesis at `μ' = Ω̄_p ≺ μ`
  have D'' := mih (s + 1) hpm β' k γ' X Γ hΓ hγ' hX' D'
  -- `α* := γ' + ω^{μ'+β'} ≺ α̂`
  have hexp : muBar (s + 1) + muBar (s + 1) + β' < muBar m + muBar m + α := by
    have h1 : muBar (s + 1) + muBar (s + 1) + β' < ThetaWNoteD.Omega (s + 1) :=
      ThetaWNoteD.add_lt_prin trivial
        (ThetaWNoteD.add_lt_prin trivial (muBar_lt_Omega _) (muBar_lt_Omega _)) hβ'Ω
    exact lt_of_lt_of_le h1 (le_trans (Omega_le_muBar hpm)
      (le_trans (ThetaWNoteD.le_add_right _ _) (ThetaWNoteD.le_add_right _ _)))
  have hlt : hat γ' (muBar (s + 1)) β' < hat γ (muBar m) α := by
    show γ' + ThetaWNoteD.omegaPow (muBar (s + 1) + muBar (s + 1) + β') <
      γ + ThetaWNoteD.omegaPow (muBar m + muBar m + α)
    rw [he, ThetaWNoteD.add_assoc]
    exact ThetaWNoteD.add_lt_add_left γ
      (ThetaWNoteD.add_lt_omegaPow hδ (ThetaWNoteD.omegaPow_lt_omegaPow hexp))
  have hψ : psi k.val (hat γ' (muBar (s + 1)) β') < psi k.val (hat γ (muBar m) α) :=
    psi_lt_psi hX' (gamma_le_hat γ' _ β') hlt (hat_mem_self hγ' hβ'H) (dom_hat hX' hγ' hβ'H)
      (dom_hat hX hγ hα)
  exact (((D''.mono_rank (le_of_lt hψ)).mono_op (Hg_mono (le_of_lt hlt) X)).mono_height
    (le_of_lt hψ) (mem_Hg_empty.mpr (psi_hat_mem hX hγ hα)))

/-! ### The cut case -/

/-- **Case `cut`**: (Cut) of rank `≺ μ` (Buchholz case 4: 4.1 rank `≺ κ`; 4.2 `κ ⪯` rank
non-regular, the S.I.H. at the next regular `π` and (□); 4.3 rank `= π` regular, the cut on
`I_p t`). -/
theorem collapse_case_cut (hyp : CollapseHyps A) {m : ℕ} (hm : m ≤ n) {α : ThetaWNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaWNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : Fin n} {γ : ThetaWNoteD} {X : Set ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaWNoteD.HopS γ X)
    (hX : ThetaWNoteD.HullHypGe k.val γ X)
    {ψ : Proposition (LIinfN n)} {α₀ : ThetaWNoteD}
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅) (hr : rk ψ < muBar m)
    (h0 : α₀ < α) (d0 : IDnDerivable A (muBar m) (Hg γ X) α₀ (ψ :: Γ))
    (d1 : IDnDerivable A (muBar m) (Hg γ X) α₀ (∼ψ :: Γ)) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp hα
  have hα₀ : α₀ ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp d0.height_mem
  have hθ := psi_hat_lt_psi_hat (k := k.val) (m := m) hX hγ hα₀ hα' h0
  have hop : ∀ Z, Hg (hat γ (muBar m) α₀) X Z ⊆ Hg (hat γ (muBar m) α) X Z :=
    Hg_mono (le_of_lt (hat_lt_hat γ _ h0)) X
  have hΓη : paramsVal Γ ⊆ Hg (hat γ (muBar m) α) X ∅ :=
    hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)
  have hηH : psi k.val (hat γ (muBar m) α) ∈ Hg (hat γ (muBar m) α) X ∅ :=
    mem_Hg_empty.mpr (psi_hat_mem hX hγ hα')
  have hψH : rk ψ ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp (rk_mem_of_head (Hg_niceS γ X) d0)
  -- the common shape of the conclusion: a collapsed derivation of height `ψ_κ α̂₀`
  have lift : ∀ {H' : Set ThetaWNoteD → Set ThetaWNoteD} {β₀ : ThetaWNoteD},
      β₀ ≤ psi k.val (hat γ (muBar m) α) → (∀ Z, H' Z ⊆ Hg (hat γ (muBar m) α) X Z) →
      IDnDerivable A β₀ H' β₀ Γ → Concl A k γ X m α Γ := fun hle hH' D =>
    ((D.mono_rank hle).mono_op hH').mono_height hle hηH
  -- `μ = Ω̄_{m₁+1}`, `rk ψ ⪯ Ω_{m₁+1}`
  obtain ⟨m₁, rfl⟩ : ∃ m₁, m = m₁ + 1 := by
    cases m with
    | zero => exact absurd hr (not_lt_of_ge (ThetaWNoteD.zero_le' _))
    | succ m₁ => exact ⟨m₁, rfl⟩
  have hrle : rk ψ ≤ ThetaWNoteD.Omega m₁ := le_of_lt_add_one_col hr
  by_cases hκ : rk ψ < ThetaWNoteD.Omega k.val
  · -- 4.1: `rk ψ ≺ κ`
    have hσ := sigmaW_of_rk_lt_Omega hκ
    have D0 := sih α₀ h0 k γ X _ (sigmaW_cons hσ.1 hΓ) hγ hX d0
    have D1 := sih α₀ h0 k γ X _ (sigmaW_cons hσ.2 hΓ) hγ hX d1
    exact .cut hηH hΓη (lt_psi_hat hX hγ hα' hψH hκ) hθ
      ((D0.mono_rank (le_of_lt hθ)).mono_op hop) ((D1.mono_rank (le_of_lt hθ)).mono_op hop)
  have hκ' : ThetaWNoteD.Omega k.val ≤ rk ψ := le_of_not_gt hκ
  -- `π = Ω_{p+1}`: the least `Omega p ⪰ rk ψ`
  classical
  have hex : ∃ p, rk ψ ≤ ThetaWNoteD.Omega p := ⟨m₁, hrle⟩
  obtain ⟨p, hp, hpmin⟩ : ∃ p, rk ψ ≤ ThetaWNoteD.Omega p ∧ ∀ q, q < p →
      ¬ rk ψ ≤ ThetaWNoteD.Omega q :=
    ⟨Nat.find hex, Nat.find_spec hex, fun q hq => Nat.find_min hex hq⟩
  have hpm₁ : p ≤ m₁ := by
    by_contra h
    exact hpmin m₁ (by omega) hrle
  have hkp : k.val ≤ p := by
    by_contra h
    have h' : ThetaWNoteD.Omega p < ThetaWNoteD.Omega k.val :=
      ThetaWNoteD.Omega_lt_Omega_iff.mpr (by omega)
    exact absurd (lt_of_lt_of_le h' (le_trans hκ' hp)) (lt_irrefl _)
  have hpn : p < n := by omega
  let P : Fin n := ⟨p, hpn⟩
  have hPv : P.val = p := rfl
  have hΓP : ∀ φ ∈ Γ, SigmaW P φ := sigmaW_mono_seq (k := k) (p := P) hkp hΓ
  have hXP : ThetaWNoteD.HullHypGe p γ X := hX.up hkp
  -- `α̂₀`, `α̂₀ + ω^{μ+μ+α₀}` and their memberships
  set μ := muBar (m₁ + 1) with hμ
  have hη₀ : hat γ μ α₀ ∈ ThetaWNoteD.HopS (hat γ μ α₀) X := hat_mem hγ hα₀
  have hγη₀ : γ ≤ hat γ μ α₀ := gamma_le_hat γ μ α₀
  have hα₀η₀ : α₀ ∈ ThetaWNoteD.HopS (hat γ μ α₀) X :=
    ThetaWNoteD.HopS_subset_HopS_of_le hγη₀ X hα₀
  have hη₁ : hat (hat γ μ α₀) μ α₀ ∈ ThetaWNoteD.HopS (hat (hat γ μ α₀) μ α₀) X :=
    hat_mem hη₀ hα₀η₀
  have hη₁lt : hat (hat γ μ α₀) μ α₀ < hat γ μ α :=
    ThetaWNoteD.add_omegaPow_add_omegaPow_lt_hull γ (ThetaWNoteD.add_lt_add_left (μ + μ) h0)
  have hη₁eq : hat (hat γ μ α₀) μ α₀ =
      γ + (ThetaWNoteD.omegaPow (μ + μ + α₀) + ThetaWNoteD.omegaPow (μ + μ + α₀)) :=
    ThetaWNoteD.add_assoc _ _ _
  have hδ₁ : ThetaWNoteD.omegaPow (μ + μ + α₀) + ThetaWNoteD.omegaPow (μ + μ + α₀) <
      ThetaWNoteD.omegaPow (μ + μ + α) := by
    have h := ThetaWNoteD.omegaPow_lt_omegaPow (ThetaWNoteD.add_lt_add_left (μ + μ) h0)
    exact ThetaWNoteD.add_lt_omegaPow h h
  have hωμ : ThetaWNoteD.omegaPow (μ + μ) ≤ ThetaWNoteD.omegaPow (μ + μ + α₀) :=
    ThetaWNoteD.omegaPow_le_omegaPow (ThetaWNoteD.le_add_right (μ + μ) α₀)
  rcases lt_or_eq_of_le hp with hlt | heq
  · -- 4.2: `κ ⪯ rk ψ ≺ π`, `rk ψ` not regular
    have hkp' : k.val < p := by
      by_contra h
      have h' : ThetaWNoteD.Omega p ≤ ThetaWNoteD.Omega k.val := by
        rcases Nat.lt_or_eq_of_le (show p ≤ k.val by omega) with h'' | h''
        · exact le_of_lt (ThetaWNoteD.Omega_lt_Omega_iff.mpr h'')
        · rw [h'']
      exact absurd (lt_of_lt_of_le hlt h') (not_lt_of_ge hκ')
    have hσ := sigmaW_of_rk_lt_Omega (k := P) hlt
    have D0 := sih α₀ h0 P γ X _ (sigmaW_cons hσ.1 hΓP) hγ hXP d0
    have D1 := sih α₀ h0 P γ X _ (sigmaW_cons hσ.2 hΓP) hγ hXP d1
    exact box hyp (γ' := hat γ μ α₀) (δ := ThetaWNoteD.omegaPow (μ + μ + α₀)) mih hΓ hγ hX
      hα'
      hkp (by omega) (by omega) rfl
      (ThetaWNoteD.omegaPow_lt_omegaPow (ThetaWNoteD.add_lt_add_left (μ + μ) h0)) hωμ hη₀
      (OmegaBelow_lt_psi (dom_hat hXP hγ hα₀)) (psi_lt_Omega _ _) hlt D0 D1
  -- 4.3: `rk ψ = π`
  obtain ⟨s, t, hform, hs⟩ := rk_eq_Omega_cases heq
  rcases hs with ⟨hsl, hsv⟩ | ⟨-, hsv⟩
  swap
  · -- `±I_{p+1}^{≺0} t`: the empty disjunction is dropped from its premise
    have dΓ : IDnDerivable A μ (Hg γ X) α₀ Γ := by
      rcases hform with rfl | rfl
      · exact drop_stage_zero hsv (Hg_isOperator γ X) d0
      · exact drop_stage_zero hsv (Hg_isOperator γ X) d1
    exact lift (le_of_lt hθ) hop (sih α₀ h0 k γ X Γ hΓ hγ hX dΓ)
  -- `±I_p t`
  have hsP : s = Stage.top P := (stage_eq_top_iff_of_lvl_eq (Fin.ext hsl)).mpr hsv
  subst hsP
  -- the cut on `I_p t`, both premises given
  have cutI : IDnDerivable A μ (Hg γ X) α₀ (IOmegaAt P t :: Γ) →
      IDnDerivable A μ (Hg γ X) α₀ (∼(IOmegaAt P t) :: Γ) → Concl A k γ X (m₁ + 1) α Γ := by
    intro e0 e1
    -- the positive premise: S.I.H. at `π`, boundedness at level `p`, stage `β = ψ_π α̂₀`
    have hσ0 : SigmaW P (IOmegaAt P t) := (sigmaW_stageAt_iff P (Stage.top P) t).mpr le_rfl
    have E0 := sih α₀ h0 P γ X _ (sigmaW_cons hσ0 hΓP) hγ hXP e0
    have hDη₀ := dom_hat (m := m₁ + 1) hXP hγ hα₀
    let b : StageAt P.val := ⟨psi p (hat γ μ α₀), le_of_lt (psi_lt_Omega _ _)⟩
    have hbΩ : b.1 < ThetaWNoteD.Omega p := psi_lt_Omega _ _
    have hbH : b.1 ∈ Hg (hat γ μ α₀) X ∅ := mem_Hg_empty.mpr (psi_hat_mem hXP hγ hα₀)
    have E0b := hyp.bound P b (Hg_isOperator _ _) hbH le_rfl hbΩ E0
    rw [capAt_IOmegaAt] at E0b
    -- the negative premise: to `H_{α̂₀}[Θ]`, Exercise 6.6, S.I.H. at `π` with `γ := α̂₀`
    have e1' := hyp.negStage P b (Hg_isOperator _ _) hbH (e1.mono_op (Hg_mono hγη₀ X))
    have hσ1 : SigmaW P (nstageAt (⟨P, b⟩ : Stage n) t) := by
      refine (sigmaW_nstageAt_iff P _ t).mpr ⟨le_rfl, fun e => ?_⟩
      have := congrArg Stage.val e
      rw [Stage.val_top] at this
      exact absurd this (ne_of_lt hbΩ)
    have hXPη₀ : ThetaWNoteD.HullHypGe p (hat γ μ α₀) X := hXP.mono hγη₀
    have E1 := sih α₀ h0 P (hat γ μ α₀) X _ (sigmaW_cons hσ1 hΓP) hη₀ hXPη₀ e1'
    have hDη₁ := dom_hat (m := m₁ + 1) hXPη₀ hη₀ hα₀η₀
    have hb₁ : psi p (hat γ μ α₀) < psi p (hat (hat γ μ α₀) μ α₀) :=
      psi_lt_psi hXP hγη₀ (gamma_lt_hat _ μ α₀) (hat_mem_self hγ hα₀) hDη₀ hDη₁
    have hb₁H : psi p (hat (hat γ μ α₀) μ α₀) ∈ Hg (hat (hat γ μ α₀) μ α₀) X ∅ :=
      mem_Hg_empty.mpr (psi_hat_mem hXPη₀ hη₀ hα₀η₀)
    have hopη : ∀ Z, Hg (hat γ μ α₀) X Z ⊆ Hg (hat (hat γ μ α₀) μ α₀) X Z :=
      Hg_mono (gamma_le_hat _ μ α₀) X
    -- both premises at height and rank `β₁ = ψ_π(α̂₀ + ω^{μ+μ+α₀})`
    have F0 : IDnDerivable A (psi p (hat (hat γ μ α₀) μ α₀)) (Hg (hat (hat γ μ α₀) μ α₀) X)
        (psi p (hat (hat γ μ α₀) μ α₀)) (stageAt (⟨P, b⟩ : Stage n) t :: Γ) :=
      ((E0b.mono_rank (le_of_lt hb₁)).mono_op hopη).mono_height (le_of_lt hb₁) hb₁H
    rcases Nat.lt_or_eq_of_le hkp with hkp' | hkp'
    · -- `p > k`: Buchholz's 4.3, then (□) with `C' = I_p^{≺β} t`
      have hC : rk (stageAt (⟨P, b⟩ : Stage n) t) < ThetaWNoteD.Omega p := by
        refine (rk_lt_Omega_iff (k := P)).mpr fun s' hs' => ?_
        rw [params_stageAt, Set.mem_singleton_iff] at hs'
        subst hs'
        exact (sigmaW_nstageAt_iff P _ t).mp hσ1
      exact box hyp
        (δ := ThetaWNoteD.omegaPow (μ + μ + α₀) + ThetaWNoteD.omegaPow (μ + μ + α₀))
        mih hΓ hγ hX hα' hkp (by omega) (by omega) hη₁eq hδ₁
        (le_trans hωμ (ThetaWNoteD.le_add_right _ _)) hη₁ (OmegaBelow_lt_psi hDη₁)
        (psi_lt_Omega _ _) hC F0 E1
    · -- `p = k`: Freund's cut on `I t`, a cut on `I_k^{≺β} t` of rank `β`
      subst hkp'
      have hDα := dom_hat (m := m₁ + 1) hX hγ hα'
      have hη₁H : hat (hat γ μ α₀) μ α₀ ∈ ThetaWNoteD.HopS γ X :=
        (ThetaWNoteD.HopS_nice γ).add_mem (hat_mem_self hγ hα₀)
          ((ThetaWNoteD.HopS_nice γ).omegaPow_mem (exp_mem hα₀))
      have hb₂' : psi k.val (hat (hat γ μ α₀) μ α₀) < psi k.val (hat γ μ α) :=
        psi_lt_psi hX (le_trans hγη₀ (gamma_le_hat _ μ α₀)) hη₁lt hη₁H hDη₁ hDα
      have hrk : rk (stageAt (⟨P, b⟩ : Stage n) t) < psi k.val (hat γ μ α) := by
        have hp' : ThetaWTerm.IsPrin b.1.1 := (Notn.thetaWLevel k.val).isPrin_theta hDη₀
        rw [rk_stageAt_prin hp' (OmegaBelow_lt_psi hDη₀)]
        exact lt_trans hb₁ hb₂'
      have hop₁ : ∀ Z, Hg (hat (hat γ μ α₀) μ α₀) X Z ⊆ Hg (hat γ μ α) X Z :=
        Hg_mono (le_of_lt hη₁lt) X
      exact .cut (ψ := stageAt (⟨P, b⟩ : Stage n) t) hηH hΓη hrk hb₂'
        ((F0.mono_rank (le_of_lt hb₂')).mono_op hop₁)
        ((E1.mono_rank (le_of_lt hb₂')).mono_op hop₁)
  rcases hform with rfl | rfl
  · exact cutI d0 d1
  · exact cutI d1 d0

end Collapsing

end IDn

end OrdinalAnalysis
