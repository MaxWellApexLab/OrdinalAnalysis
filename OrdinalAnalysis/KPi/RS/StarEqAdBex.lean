module

public import OrdinalAnalysis.KPi.RS.StarEqMem

/-!
# The RS calculus, part 13: Lemma 2.7, the cases `Ad(x_i)` and `∃y∈x B`
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}}

theorem k_L_sub_eqS_neg (κ : Ordinal.{1}) (a : T) :
    ({κ} : Set Ordinal.{1}) ⊆ (eqS (T.L κ) a).neg.k := by
  rw [RSS.k_neg]
  intro ξ hξ
  have h : ξ = κ := hξ
  exact k_eqS_left (T.L κ) a (by simp [T.k, PT.k, T.L, h])

/-- the case `Ad(x_i)`. -/
theorem eq_ad {M : Ordinal.{1}} (low : Low R M) {n : ℕ} (i : Fin n) (ρ ρ2 : Fin n → T)
    (hM1 : (RSS.base (D0.ad i) ρ).rk ≤ M) (hM2 : (RSS.base (D0.ad i) ρ2).rk ≤ M) :
    EQ R (D0.ad i) ρ ρ2 := by
  intro Δ hA hA2 hyp
  have hA' : RSS.base (D0.nad i) ρ ∈ Δ := hA
  refine star_nad' (s := ρ i) hA' rfl (fun κ hκ hκ0 hκle => ?_)
  have hsub1 : Δ ⊆ insert (eqS (T.L κ) (ρ i)).neg Δ := by sub_tac
  by_cases hle : κ ≤ (ρ2 i).level
  · refine star_ad' (s := ρ2 i) (hsub1 hA2) rfl κ hκ hκ0 hle
      (hk_of_mem (A := (eqS (T.L κ) (ρ i)).neg) (by simp) (k_L_sub_eqS_neg κ _)) ?_
    have hr1 : (eqS (T.L κ) (ρ i)).rk < M :=
      lt_of_lt_of_le (rk_eqS_lt_ad hκ0 hκle) hM1
    have hr2 : (eqS (T.L κ) (ρ2 i)).rk < M :=
      lt_of_lt_of_le (rk_eqS_lt_ad hκ0 hle) hM2
    refine use_eqS low (max_lt hr1 hr2) (by simp) (by simp) (fun h => absurd rfl h) (fun h => ?_)
    exact ⟨by simp [(hyp i h).1], by simp [(hyp i h).2]⟩
  · have hne : ρ i ≠ ρ2 i := fun h => hle (h ▸ hκle)
    refine star_neq_of (a := T.L κ) (b := ρ i) (Set.mem_insert _ _) ?_
    exact star_lem26 (a := ρ i) (b := ρ2 i) (γ := κ) (not_le.1 hle)
      (by simp [(hyp i hne).1]) (by simp)

theorem rk_base_lt_bex {n : ℕ} (b : Bd n) (X : D0 (n + 1)) (ρ : Fin n → T) (u : T)
    (hu : u.level < (resBd b ρ).level) :
    (RSS.base X (ext ρ u)).rk < (RSS.base (D0.bex b X) ρ).rk := by
  have h := rk_bex_child b X ρ ⟨u, hu⟩
  rw [rk_and] at h
  exact lt_of_le_of_lt (le_trans (le_max_right _ _) (le_of_lt (lt_add_one _))) h

/-- the case `∃y∈x B(y)`. -/
theorem eq_bex {M : Ordinal.{1}} (low : Low R M) {n : ℕ} (b : Bd n) (X : D0 (n + 1))
    (ρ ρ2 : Fin n → T) (hM1 : (RSS.base (D0.bex b X) ρ).rk ≤ M)
    (hM2 : (RSS.base (D0.bex b X) ρ2).rk ≤ M) : EQ R (D0.bex b X) ρ ρ2 := by
  intro Δ hA hA2 hyp
  have hA' : RSS.base (D0.ball b X.neg) ρ ∈ Δ := hA
  refine star_ball' (s := resBd b ρ) hA' rfl (fun u hu => ?_)
  have hru : (RSS.base X (ext ρ u)).rk < M := lt_of_lt_of_le (rk_base_lt_bex b X ρ u hu) hM1
  have hsub1 : Δ ⊆ insert (memInst u (resBd b ρ)).neg
      (insert (RSS.base X.neg (ext ρ u)) Δ) := by sub_tac
  by_cases hbb : resBd b ρ = resBd b ρ2
  · have hu2 : u.level < (resBd b ρ2).level := hbb ▸ hu
    refine star_bex' (s := resBd b ρ2) (hsub1 hA2) rfl u hu2
      (hk_of_mem (A := (memInst u (resBd b ρ)).neg) (by simp) (k_neg_memInst _ _)) ?_ ?_
    · refine star_tnd' (A := memInst u (resBd b ρ2)) (by simp) ?_
      rw [← hbb]; simp
    · have hr : max (RSS.base X (ext ρ u)).rk (RSS.base X (ext ρ2 u)).rk < M :=
        max_lt hru (lt_of_lt_of_le (rk_base_lt_bex b X ρ2 u hu2) hM2)
      refine low X (ext ρ u) (ext ρ2 u) hr _ (by simp [RSS.neg]) (by simp) ?_
      exact (hyp.mono hsub1 |>.mono (Set.subset_insert _ _)).ext u u (fun h => absurd rfl h)
  · obtain ⟨j, rfl⟩ : ∃ j, b = Bd.var j := by
      cases b with
      | var j => exact ⟨j, rfl⟩
      | lev α => exact absurd rfl hbb
    have hn := hyp j hbb
    have hn1 : Nq1 (ρ j) (ρ2 j) ∈ insert (memInst u (ρ j)).neg
        (insert (RSS.base X.neg (ext ρ u)) Δ) := hsub1 hn.1
    refine star_bex' (b := Bd.var 0) (X := D0.nmem (Fin.last 2) (Fin.castSucc 1))
      (ρ := ![ρ j, ρ2 j]) (s := resBd (Bd.var j) ρ) hn1 rfl u hu
      (hk_of_mem (A := (memInst u (resBd (Bd.var j) ρ)).neg) (by simp) (k_neg_memInst _ _))
      (star_tnd' (A := memInst u (resBd (Bd.var j) ρ)) (by simp) (by simp)) ?_
    refine star_nmem' (Set.mem_insert _ _) (s1 := u) (s2 := ρ2 j) (by simp) (by simp)
      (fun v hv => ?_)
    have hrv : (RSS.base X (ext ρ2 v)).rk < M :=
      lt_of_lt_of_le (rk_base_lt_bex (Bd.var j) X ρ2 v hv) hM2
    have hA2' : RSS.base (D0.bex (Bd.var j) X) ρ2 ∈ insert (memInst v (ρ2 j)).neg
        (insert (eqS v u).neg
        (insert (RSS.base (D0.nmem (Fin.last 2) (Fin.castSucc 1)) (ext ![ρ j, ρ2 j] u))
        (insert (memInst u (ρ j)).neg (insert (RSS.base X.neg (ext ρ u)) Δ)))) := by
      simp [hA2]
    refine star_bex' (s := ρ2 j) hA2' rfl v hv
      (hk_of_mem (A := (memInst v (ρ2 j)).neg) (by simp) (k_neg_memInst _ _))
      (star_tnd' (A := memInst v (ρ2 j)) (by simp) (by simp)) ?_
    refine star_items_of_eqneg (u := u) (v := v) (by simp) (fun Δ' hsub hn1' hn2' => ?_)
    refine low X (ext ρ u) (ext ρ2 v) (max_lt hru hrv) Δ' (hsub (by simp [RSS.neg]))
      (hsub (by simp)) ?_
    have hyp' : NeqHyp Δ' ρ ρ2 := hyp.mono (fun z hz => hsub (by simp [hz]))
    exact hyp'.ext u v (fun _ => ⟨hn1', hn2'⟩)

end OrdinalAnalysis.KPi.RS
