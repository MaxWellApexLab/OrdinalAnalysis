module

public import OrdinalAnalysis.KPi.RS.StarAxPU

/-!
# The RS calculus, part 17: Theorem 2.9 (a), the axioms (Ext), (Found); (Lim)

* `sim_subset_neg`, `sim_subset_neg2` : `¬(ρ i ⊆ ρ j)` in any context is `Sim` to `Nq1`, `Nq2`;
* `extD`, `star_ext`    : `⊢* (Ext)^λ` (by Lemma 2.7);
* `closeL`, `star_closeL` : closing a formula over `∀z∈L_λ`;
* `foundD`, `star_found_closed` : `⊢*_σ (Found)^λ`, `σ > 0`;
* `limD`, `star_lim`    : `⊢* (Lim)^λ`.
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}} {σ : Ordinal.{1}}

theorem sim_subset_neg {n : ℕ} (i j : Fin n) (ρ : Fin n → T) :
    Sim R (RSS.base (D0.subset i j).neg ρ) (Nq1 (ρ i) (ρ j)) := by
  have h := sim_rename (R := R) (D0.subset 0 1).neg ![i, j] ![0, 1] ρ ![ρ i, ρ j]
    (by intro k; fin_cases k <;> rfl)
  have e1 : D0.rename ![i, j] (D0.subset 0 1).neg = (D0.subset i j).neg := rfl
  have e2 : D0.rename (![0, 1] : Fin 2 → Fin 2) (D0.subset 0 1).neg = (D0.subset 0 1).neg := by
    simp [D0.rename, D0.subset, D0.neg, Bd.rename, liftF]
    decide
  rw [e1, e2] at h
  exact h

theorem sim_subset_neg2 {n : ℕ} (i j : Fin n) (ρ : Fin n → T) :
    Sim R (RSS.base (D0.subset i j).neg ρ) (Nq2 (ρ j) (ρ i)) := by
  have h := sim_rename (R := R) (D0.subset 0 1).neg ![i, j] ![1, 0] ρ ![ρ j, ρ i]
    (by intro k; fin_cases k <;> rfl)
  have e1 : D0.rename ![i, j] (D0.subset 0 1).neg = (D0.subset i j).neg := rfl
  have e2 : D0.rename (![1, 0] : Fin 2 → Fin 2) (D0.subset 0 1).neg = (D0.subset 1 0).neg := by
    simp [D0.rename, D0.subset, D0.neg, Bd.rename, liftF]
    decide
  rw [e1, e2] at h
  exact h


/-! ### (Ext) -/

/-- the matrix of `(Ext)`: `x = y → ((x ∈ z → y ∈ z) ∧ (Ad x → Ad y))`, `x, y, z = 0, 1, 2`. -/
def extBody : D0 3 :=
  D0.or (D0.eqf 0 1).neg
    (D0.and (D0.or (D0.nmem 0 2) (D0.mem 1 2)) (D0.or (D0.nad 0) (D0.ad 1)))

/-- `(Ext)^λ`. -/
def extD (lam : Ordinal.{1}) : D0 0 :=
  D0.ball (Bd.lev lam) (D0.ball (Bd.lev lam) (D0.ball (Bd.lev lam) extBody))

/-- the matrix of `(Ext)` for arbitrary terms (B92: by Lemma 2.7). -/
theorem star_ext_body (ρ : Fin 3 → T) {Δ : Set RSS} (hA : RSS.base extBody ρ ∈ Δ) :
    Star R 0 Δ := by
  refine star_bor_of (X := (D0.eqf 0 1).neg)
    (Y := D0.and (D0.or (D0.nmem 0 2) (D0.mem 1 2)) (D0.or (D0.nad 0) (D0.ad 1))) hA ?_
  refine star_bor_of (X := (D0.subset 0 1).neg) (Y := (D0.subset 1 0).neg) (Set.mem_insert _ _) ?_
  refine star_band_of (X := D0.or (D0.nmem 0 2) (D0.mem 1 2)) (Y := D0.or (D0.nad 0) (D0.ad 1))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert _ _)))) ?_ ?_
  · refine star_bor_of (Set.mem_insert _ _) ?_
    let Δ0 : Set RSS := {Nq1 (ρ 0) (ρ 1), Nq2 (ρ 0) (ρ 1),
      RSS.base (D0.nmem 0 1) ![ρ 0, ρ 2], RSS.base (D0.mem 0 1) ![ρ 1, ρ 2]}
    have h0 : Star R 0 Δ0 :=
      star_eq_lemma (D0.mem 0 1) ![ρ 0, ρ 2] ![ρ 1, ρ 2] (Δ := Δ0) (σ := 0)
        (by simp [Δ0, RSS.neg, D0.neg]) (by simp [Δ0])
        (NeqHyp.pair (fun _ => ⟨by simp [Δ0], by simp [Δ0]⟩) (fun h => absurd rfl h))
    refine Star.sim h0 ?_
    intro x hx
    simp only [Δ0, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, (sim_subset_neg 0 1 ρ).symm⟩
    · exact ⟨_, by simp, (sim_subset_neg2 1 0 ρ).symm⟩
    · exact ⟨_, by simp, sim_nmem_atom 0 1 0 2 _ ρ rfl rfl⟩
    · exact ⟨_, by simp, sim_mem_atom 0 1 1 2 _ ρ rfl rfl⟩
  · refine star_bor_of (Set.mem_insert _ _) ?_
    let Δ0 : Set RSS := {Nq1 (ρ 0) (ρ 1), Nq2 (ρ 0) (ρ 1),
      RSS.base (D0.nad 0) ![ρ 0], RSS.base (D0.ad 0) ![ρ 1]}
    have h0 : Star R 0 Δ0 :=
      star_eq_lemma (D0.ad 0) ![ρ 0] ![ρ 1] (Δ := Δ0) (σ := 0)
        (by simp [Δ0, RSS.neg, D0.neg]) (by simp [Δ0])
        (fun i _ => by fin_cases i; simp [Δ0])
    refine Star.sim h0 ?_
    intro x hx
    simp only [Δ0, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, (sim_subset_neg 0 1 ρ).symm⟩
    · exact ⟨_, by simp, (sim_subset_neg2 1 0 ρ).symm⟩
    · exact ⟨_, by simp, sim_nad_atom 0 0 _ ρ rfl⟩
    · exact ⟨_, by simp, sim_ad_atom 0 1 _ ρ rfl⟩

/-- **B92 Thm 2.9 (a)**: `⊢* (Ext)^λ`. -/
theorem star_ext (lam : Ordinal.{1}) {Δ : Set RSS} (hA : RSS.base (extD lam) Fin.elim0 ∈ Δ) :
    Star R 0 Δ := by
  refine star_ball' hA rfl (fun a ha => ?_)
  refine star_ball' (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) rfl (fun b hb => ?_)
  refine star_ball' (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) rfl (fun c hc => ?_)
  exact star_ext_body _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))


/-! ### closing over `∀z∈L_λ`, and (Found) -/

/-- `∀x₁∈L_λ … ∀x_k∈L_λ φ`. -/
def closeL (lam : Ordinal.{1}) : (k : ℕ) → D0 k → D0 0
  | 0, φ => φ
  | k + 1, φ => closeL lam k (D0.ball (Bd.lev lam) φ)

/-- a closed formula is derivable once all its instances over `𝒯_λ` are, in a sequent
containing the facts `¬(c ∈° L_λ)` about the instantiating terms. -/
theorem star_closeL (lam : Ordinal.{1}) : ∀ (k : ℕ) (φ : D0 k) {Δ : Set RSS},
    (∀ c : Fin k → T, (∀ i, (c i).level < lam) → ∀ Δ' : Set RSS,
      (∀ i, (memInst (c i) (T.L lam)).neg ∈ Δ') → RSS.base φ c ∈ Δ' → Star R σ Δ') →
    RSS.base (closeL lam k φ) Fin.elim0 ∈ Δ → Star R σ Δ := by
  intro k
  induction k with
  | zero =>
    intro φ Δ H hA
    exact H Fin.elim0 (fun i => i.elim0) Δ (fun i => i.elim0) hA
  | succ k ih =>
    intro φ Δ H hA
    refine ih (D0.ball (Bd.lev lam) φ) (fun c' hc' Δ' hmem hA' => ?_) hA
    refine star_ball' hA' rfl (fun t ht => ?_)
    refine H (ext c' t) (fun i => ?_) _ (fun i => ?_) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · induction i using Fin.lastCases with
      | last => simpa [level_L] using ht
      | cast j => simpa using hc' j
    · induction i using Fin.lastCases with
      | last => simp
      | cast j => simp [hmem j]

/-- `(Found)^λ` for `A(x, z⃗)` (`z⃗` the first `k` variables, `x` the last). -/
def foundD (lam : Ordinal.{1}) (k : ℕ) (A : D0 (k + 1)) : D0 0 :=
  closeL lam k (D0.or (foundE lam A) (foundU lam A))

/-- **B92 Thm 2.9 (a)**: `⊢*_σ (Found)^λ` for `σ > 0` (the `(Found)*` axiom). -/
theorem star_found_closed (lam : Ordinal.{1}) (k : ℕ) (A : D0 (k + 1)) (hσ : 0 < σ) {Δ : Set RSS}
    (hA : RSS.base (foundD lam k A) Fin.elim0 ∈ Δ) : Star R σ Δ := by
  refine star_closeL lam k _ (fun c _ Δ' _ hA' => ?_) hA
  refine star_bor_of (X := foundE lam A) (Y := foundU lam A) hA' ?_
  have := Star.found (R := R) lam A c (Γ := Δ') (σ := σ) hσ (Sim.refl _) (Sim.refl _)
  refine Star.mono this ?_
  intro z hz
  simp only [Set.mem_insert_iff] at hz ⊢
  tauto

/-! ### (Lim) -/

/-- `(Lim)^λ`: `∀x∈L_λ ∃y∈L_λ (Ad y ∧ x ∈ y)`. -/
def limD (lam : Ordinal.{1}) : D0 0 :=
  D0.ball (Bd.lev lam) (D0.bex (Bd.lev lam) (D0.and (D0.ad 1) (D0.mem 0 1)))

/-- **B92 Thm 2.9 (c) 4**: `⊢* (Lim)^λ` if `∀α<λ ∃κ∈R (α<κ<λ)`. -/
theorem star_lim (lam : Ordinal.{1}) (hlam : ∀ α < lam, ∃ κ ∈ R, α < κ ∧ κ < lam) {Δ : Set RSS}
    (hA : RSS.base (limD lam) Fin.elim0 ∈ Δ) : Star R σ Δ := by
  refine star_ball' hA rfl (fun a ha => ?_)
  obtain ⟨κ0, hκ0R, h1, h2⟩ := hlam a.level ha
  obtain ⟨hκR, hκgt, -⟩ := powR_spec R a.level ⟨κ0, hκ0R, h1⟩
  have hκlt : powR R a.level < lam :=
    lt_of_le_of_lt ((powR_spec R a.level ⟨κ0, hκ0R, h1⟩).2.2 κ0 hκ0R h1) h2
  have hκ0 : 0 < powR R a.level := lt_of_le_of_lt zero_le hκgt
  refine star_bex' (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) rfl (T.L (powR R a.level))
    hκlt ?_ (star_memInst_L' _ _) ?_
  · intro ξ hξ
    have h : ξ = powR R a.level := hξ
    rw [h]
    refine Or.inr ⟨a.level, ?_, rfl⟩
    exact level_mem_kSeq (A := (memInst a (T.L lam)).neg) (by simp) (k_neg_memInst _ _)
  · refine star_band_of (Set.mem_insert _ _) ?_ ?_
    · exact star_ad_L (i := 1) (κ := powR R a.level) (by simp) hκR hκ0 (Set.mem_insert _ _)
    · refine star_mem_L (β := powR R a.level) (Set.mem_insert _ _) (by simp) ?_
      simpa using hκgt

end OrdinalAnalysis.KPi.RS
