module

public import OrdinalAnalysis.KPi.RS.StarNeq

/-!
# The RS calculus, part 11: the equality lemma 2.7 -- statement and tools

B92 Lemma 2.7: `⊢* [s₁≠t₁],…,[sₙ≠tₙ], ¬A(s⃗), A(t⃗)`.  Because sequents are *sets*, the linearity
hypothesis of B92 (each variable occurs at most once) is not needed: the statement proved is

  `EQ φ ρ ρ₂ := ∀ Δ, ¬φ(ρ) ∈ Δ → φ(ρ₂) ∈ Δ → (∀ i, ρ i ≠ ρ₂ i → [ρ i ≠ ρ₂ i] ⊆ Δ) → ⊢* Δ`

with `[a ≠ b] = {Nq1 a b, Nq2 a b} = {¬a ⊆ b, ¬b ⊆ a}`.

This file: the definitions, monotonicity/extension of the hypothesis, the swap (`eq_dual`), the
`Nq`-items extracted from `(eqS v u)⁻`, and the case of `∧`.
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}}

/-- the items `[ρ i ≠ ρ₂ i]` are in `Δ` wherever `ρ` and `ρ₂` differ. -/
def NeqHyp (Δ : Set RSS) {n : ℕ} (ρ ρ2 : Fin n → T) : Prop :=
  ∀ i, ρ i ≠ ρ2 i → Nq1 (ρ i) (ρ2 i) ∈ Δ ∧ Nq2 (ρ i) (ρ2 i) ∈ Δ

/-- the statement of Lemma 2.7 for `φ`, `ρ`, `ρ₂`. -/
def EQ (R : Set Ordinal.{1}) {n : ℕ} (φ : D0 n) (ρ ρ2 : Fin n → T) : Prop :=
  ∀ Δ : Set RSS, (RSS.base φ ρ).neg ∈ Δ → RSS.base φ ρ2 ∈ Δ → NeqHyp Δ ρ ρ2 → Star R 0 Δ

theorem NeqHyp.mono {Δ Δ' : Set RSS} {n : ℕ} {ρ ρ2 : Fin n → T} (h : NeqHyp Δ ρ ρ2)
    (hs : Δ ⊆ Δ') : NeqHyp Δ' ρ ρ2 :=
  fun i hi => ⟨hs (h i hi).1, hs (h i hi).2⟩

/-- extending both environments by one entry. -/
theorem NeqHyp.ext {Δ : Set RSS} {n : ℕ} {ρ ρ2 : Fin n → T} (h : NeqHyp Δ ρ ρ2) (u v : T)
    (huv : u ≠ v → Nq1 u v ∈ Δ ∧ Nq2 u v ∈ Δ) : NeqHyp Δ (ext ρ u) (ext ρ2 v) := by
  intro i
  induction i using Fin.lastCases with
  | last => simpa using huv
  | cast j => simpa using h j

/-- the two-entry hypothesis. -/
theorem NeqHyp.pair {Δ : Set RSS} {s s1 v t1 : T}
    (h0 : s ≠ v → Nq1 s v ∈ Δ ∧ Nq2 s v ∈ Δ) (h1 : s1 ≠ t1 → Nq1 s1 t1 ∈ Δ ∧ Nq2 s1 t1 ∈ Δ) :
    NeqHyp Δ ![s, s1] ![v, t1] := by
  intro i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- the items `[u ≠ v]` can be extracted from `¬(v = u)`. -/
theorem star_items_of_eqneg {u v : T} {Δ : Set RSS} (hv : (eqS v u).neg ∈ Δ)
    (H : ∀ Δ' : Set RSS, Δ ⊆ Δ' → Nq1 u v ∈ Δ' → Nq2 u v ∈ Δ' → Star R 0 Δ') : Star R 0 Δ := by
  refine star_neq_of hv ?_
  refine Star.sim (H (insert (Nq1 u v) (insert (Nq2 u v) (insert (Nq1 v u) (insert (Nq2 v u) Δ))))
    (by sub_tac) (by simp) (by simp)) ?_
  intro x hx
  rcases hx with rfl | rfl | hx
  · exact ⟨_, by simp, sim_Nq1 u v⟩
  · exact ⟨_, by simp, sim_Nq2 u v⟩
  · exact ⟨x, hx, Sim.refl _⟩

/-- reverse the orientation of the hypothesis. -/
theorem star_swap_hyp {n : ℕ} {ρ ρ2 : Fin n → T} {Δ : Set RSS} (hyp : NeqHyp Δ ρ2 ρ)
    (H : ∀ Δ' : Set RSS, Δ ⊆ Δ' → NeqHyp Δ' ρ ρ2 → Star R 0 Δ') : Star R 0 Δ := by
  let E : Set RSS := {x | ∃ i, ρ i ≠ ρ2 i ∧ (x = Nq1 (ρ i) (ρ2 i) ∨ x = Nq2 (ρ i) (ρ2 i))}
  have hΔ' : NeqHyp (Δ ∪ E) ρ ρ2 := fun i hi =>
    ⟨Or.inr ⟨i, hi, Or.inl rfl⟩, Or.inr ⟨i, hi, Or.inr rfl⟩⟩
  refine Star.sim (H (Δ ∪ E) Set.subset_union_left hΔ') ?_
  intro x hx
  rcases hx with hx | ⟨i, hi, hx | hx⟩
  · exact ⟨x, hx, Sim.refl _⟩
  · subst hx
    exact ⟨_, (hyp i (Ne.symm hi)).2, sim_Nq1 _ _⟩
  · subst hx
    exact ⟨_, (hyp i (Ne.symm hi)).1, sim_Nq2 _ _⟩

/-- duality: `EQ φ ρ ρ₂ → EQ ¬φ ρ₂ ρ`. -/
theorem eq_dual {n : ℕ} {φ : D0 n} {ρ ρ2 : Fin n → T} (h : EQ R φ ρ ρ2) :
    EQ R φ.neg ρ2 ρ := by
  intro Δ h1 h2 hyp
  refine star_swap_hyp hyp (fun Δ' hsub hyp' => h Δ' (hsub h2) ?_ hyp')
  have := hsub h1
  simpa [RSS.neg] using this

/-- the case `∧`. -/
theorem eq_and {n : ℕ} {X Y : D0 n} {ρ ρ2 : Fin n → T} (hX : EQ R X ρ ρ2) (hY : EQ R Y ρ ρ2) :
    EQ R (D0.and X Y) ρ ρ2 := by
  intro Δ h1 h2 hyp
  refine star_bor_of (X := X.neg) (Y := Y.neg) h1 ?_
  have h2' : RSS.base (D0.and X Y) ρ2 ∈
      insert (RSS.base X.neg ρ) (insert (RSS.base Y.neg ρ) Δ) := by simp [h2]
  refine star_band_of h2' ?_ ?_
  · refine hX _ (by simp [RSS.neg]) (by simp) (hyp.mono (by sub_tac))
  · refine hY _ (by simp [RSS.neg]) (by simp) (hyp.mono (by sub_tac))

end OrdinalAnalysis.KPi.RS
