module

public import OrdinalAnalysis.KPi.RS.StarEqCore

/-!
# The RS calculus, part 12: Lemma 2.7, the case `x_i ∈ x_j`

`Low R M` is the induction hypothesis: `EQ` holds for every instance whose two ranks are `< M`.
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}}

/-- the induction hypothesis of Lemma 2.7. -/
def Low (R : Set Ordinal.{1}) (M : Ordinal.{1}) : Prop :=
  ∀ {n : ℕ} (φ : D0 n) (ρ ρ2 : Fin n → T),
    max (RSS.base φ ρ).rk (RSS.base φ ρ2).rk < M → EQ R φ ρ ρ2

theorem rk_eqS_lt_mem {n : ℕ} (ρ : Fin n → T) (i j : Fin n) (s : T) (hs : s.level < (ρ j).level) :
    (eqS s (ρ i)).rk < (RSS.base (D0.mem i j) ρ).rk := by
  have h := rk_mem_child ρ i j ⟨s, hs⟩
  rw [rk_and] at h
  exact lt_of_le_of_lt (le_trans (le_max_right _ _) (le_of_lt (lt_add_one _))) h

/-- use the induction hypothesis for the equation atom. -/
theorem use_eqS {M : Ordinal.{1}} (low : Low R M) {s s1 v t1 : T}
    (hr : max (eqS s s1).rk (eqS v t1).rk < M) {Δ : Set RSS} (hn : (eqS s s1).neg ∈ Δ)
    (hp : eqS v t1 ∈ Δ) (h0 : s ≠ v → Nq1 s v ∈ Δ ∧ Nq2 s v ∈ Δ)
    (h1 : s1 ≠ t1 → Nq1 s1 t1 ∈ Δ ∧ Nq2 s1 t1 ∈ Δ) : Star R 0 Δ :=
  low (D0.eqf 0 1) ![s, s1] ![v, t1] hr Δ hn hp (NeqHyp.pair h0 h1)

/-- the case `x_i ∈ x_j`. -/
theorem eq_mem {M : Ordinal.{1}} (low : Low R M) {n : ℕ} (i j : Fin n) (ρ ρ2 : Fin n → T)
    (hM1 : (RSS.base (D0.mem i j) ρ).rk ≤ M) (hM2 : (RSS.base (D0.mem i j) ρ2).rk ≤ M) :
    EQ R (D0.mem i j) ρ ρ2 := by
  intro Δ hA hA2 hyp
  have hA' : RSS.base (D0.nmem i j) ρ ∈ Δ := hA
  refine star_nmem' (s1 := ρ i) (s2 := ρ j) hA' rfl rfl (fun s hs => ?_)
  have hrs : (eqS s (ρ i)).rk < M := lt_of_lt_of_le (rk_eqS_lt_mem ρ i j s hs) hM1
  have hsub1 : Δ ⊆ insert (memInst s (ρ j)).neg (insert (eqS s (ρ i)).neg Δ) := by sub_tac
  by_cases hjj : ρ j = ρ2 j
  · -- `s₂ = t₂`: the witness is `s`
    have hs2 : s.level < (ρ2 j).level := hjj ▸ hs
    refine star_mem' (s1 := ρ2 i) (s2 := ρ2 j) (hsub1 hA2) rfl rfl s hs2
      (hk_of_mem (A := (memInst s (ρ j)).neg) (by simp) (k_neg_memInst _ _)) ?_ ?_
    · refine star_tnd' (A := memInst s (ρ2 j)) (by simp) ?_
      rw [← hjj]; simp
    · have hr : max (eqS s (ρ i)).rk (eqS s (ρ2 i)).rk < M :=
        max_lt hrs (lt_of_lt_of_le (by simpa [hjj] using rk_eqS_lt_mem ρ2 i j s hs2) hM2)
      refine use_eqS low hr (by simp) (by simp) (fun h => absurd rfl h) (fun h => ?_)
      exact ⟨by simp [(hyp i h).1], by simp [(hyp i h).2]⟩
  · -- `s₂ ≠ t₂`: `s ∉ t₂` from `¬(s₂ ⊆ t₂)`
    have hn := hyp j hjj
    have hn1 : Nq1 (ρ j) (ρ2 j) ∈ insert (memInst s (ρ j)).neg (insert (eqS s (ρ i)).neg Δ) :=
      hsub1 hn.1
    refine star_bex' (b := Bd.var 0) (X := D0.nmem (Fin.last 2) (Fin.castSucc 1))
      (ρ := ![ρ j, ρ2 j]) (s := ρ j) hn1 rfl s hs
      (hk_of_mem (A := (memInst s (ρ j)).neg) (by simp) (k_neg_memInst _ _))
      (star_tnd' (A := memInst s (ρ j)) (by simp) (by simp)) ?_
    refine star_nmem' (Set.mem_insert _ _) (s1 := s) (s2 := ρ2 j) (by simp) (by simp)
      (fun v hv => ?_)
    have hrv : (eqS v (ρ2 i)).rk < M :=
      lt_of_lt_of_le (rk_eqS_lt_mem ρ2 i j v hv) hM2
    have hA2' : RSS.base (D0.mem i j) ρ2 ∈ insert (memInst v (ρ2 j)).neg (insert (eqS v s).neg
        (insert (RSS.base (D0.nmem (Fin.last 2) (Fin.castSucc 1)) (ext ![ρ j, ρ2 j] s))
        (insert (memInst s (ρ j)).neg (insert (eqS s (ρ i)).neg Δ)))) := by simp [hA2]
    refine star_mem' (s1 := ρ2 i) (s2 := ρ2 j) hA2' rfl rfl v hv
      (hk_of_mem (A := (memInst v (ρ2 j)).neg) (by simp) (k_neg_memInst _ _)) ?_ ?_
    · exact star_tnd' (A := memInst v (ρ2 j)) (by simp) (by simp)
    · refine star_items_of_eqneg (u := s) (v := v) (by simp) (fun Δ' hsub hn1' hn2' => ?_)
      refine use_eqS low (max_lt hrs hrv) (hsub (by simp)) (hsub (by simp))
        (fun _ => ⟨hn1', hn2'⟩) (fun h => ?_)
      exact ⟨hsub (by simp [(hyp i h).1]), hsub (by simp [(hyp i h).2])⟩

end OrdinalAnalysis.KPi.RS
