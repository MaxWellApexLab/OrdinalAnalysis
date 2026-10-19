module

public import OrdinalAnalysis.KPi.RS.StarAxSep

/-!
# The RS calculus, part 20: Theorem 2.9 (c): `(Ad.1)`, `(Ad.2)`, `(Ad.3)`

* `ad2D`, `star_ad2`   : `⊢*_λ (Ad.2)^λ` (two applications of `(Ad)*`);
* `ad1D`, `star_ad1`   : `⊢*_λ (Ad.1)^λ` (`tran(L_κ)`, `∃w∈L_κ infinite(w)` by 2.5 f, g);
* `ad3D`, `star_ad3`   : `⊢*_λ (Ad.3)^λ` for an instance `ψ`, from `⊢* ψ^{L_κ}` for all `κ ∈ R`;
  instances for `(Pair)`, `(Union)`, `(Δ₀-Sep)`.

Hypotheses: `ω·λ = λ` (so that `rk(χ(a)) < ω·λ = λ` for `a ∈ 𝒯_λ`), `0 < λ`; the members of `R`
are limit ordinals `> ω`.
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}} {σ : Ordinal.{1}}

/-! ### (Ad.2) -/

/-- `x ∈ y ∨ x = y ∨ y ∈ x`. -/
def trich {n : ℕ} (i j : Fin n) : D0 n :=
  D0.or (D0.mem i j) (D0.or (D0.eqf i j) (D0.mem j i))

/-- `Ad x → (Ad y → x∈y ∨ x=y ∨ y∈x)`. -/
def Ad2Body : D0 2 := D0.or (D0.nad 0) (D0.or (D0.nad 1) (trich 0 1))

/-- `(Ad.2)^λ`. -/
def ad2D (lam : Ordinal.{1}) : D0 0 :=
  D0.ball (Bd.lev lam) (D0.ball (Bd.lev lam) Ad2Body)

theorem levLE_trich {n : ℕ} (i j : Fin n) : D0.LevLE 0 (trich i j) := by
  simp [trich, D0.eqf, D0.subset, D0.LevLE]

theorem levLE_Ad2Body : D0.LevLE 0 Ad2Body := by
  simp [Ad2Body, D0.LevLE, levLE_trich]

theorem star_trich {n : ℕ} {i j : Fin n} {ρ : Fin n → T} {κ κ' : Ordinal.{1}}
    (h0 : ρ i = T.L κ) (h1 : ρ j = T.L κ') {Δ : Set RSS}
    (hA : RSS.base (trich i j) ρ ∈ Δ) : Star R σ Δ := by
  rcases lt_trichotomy κ κ' with hlt | heq | hgt
  · refine star_bor_of (X := D0.mem i j) (Y := D0.or (D0.eqf i j) (D0.mem j i)) hA ?_
    exact star_mem_L (β := κ') (Set.mem_insert _ _) h1 (by rw [h0]; exact hlt)
  · refine star_bor_of (X := D0.mem i j) (Y := D0.or (D0.eqf i j) (D0.mem j i)) hA ?_
    refine star_bor_of (X := D0.eqf i j) (Y := D0.mem j i)
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) ?_
    refine star_band_of (X := D0.subset i j) (Y := D0.subset j i) (Set.mem_insert _ _) ?_ ?_
    · exact star_sub_refl (a := T.L κ) h0 (by rw [h1, heq]) (Set.mem_insert _ _)
    · exact star_sub_refl (a := T.L κ) (by rw [h1, heq]) h0 (Set.mem_insert _ _)
  · refine star_bor_of (X := D0.mem i j) (Y := D0.or (D0.eqf i j) (D0.mem j i)) hA ?_
    refine star_bor_of (X := D0.eqf i j) (Y := D0.mem j i)
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) ?_
    exact star_mem_L (β := κ) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) h0
      (by rw [h1]; exact hgt)

theorem star_ad2_body {lam : Ordinal.{1}} (hlam : ω * lam = lam) (hl : 0 < lam)
    (ρ : Fin 2 → T) (hρ : ∀ i, (ρ i).level < lam) {Δ : Set RSS}
    (hA : RSS.base Ad2Body ρ ∈ Δ) : Star R lam Δ := by
  refine Star.ad' (i := (0 : Fin 2)) (D0.or (D0.nad 1) (trich 0 1)) ρ hA (fun κ => ?_) ?_
  · have hκlt : κ.1 < lam := lt_of_le_of_lt κ.2.2.2 (hρ 0)
    refine Star.ad' (i := (1 : Fin 2)) (trich 0 1) (Function.update ρ 0 (T.L κ.1))
      (Set.mem_insert _ _) (fun κ' => ?_) ?_
    · exact star_trich (i := 0) (j := 1) (κ := κ.1) (κ' := κ'.1) (by simp) (by simp)
        (Set.mem_insert _ _)
    · refine rk_base_lt_lam (trich 0 1) (levLE_trich _ _) _ lam hlam hl (fun i => ?_)
      by_cases hi : i = 0
      · subst hi
        simpa [level_L] using hκlt
      · simpa [Function.update_of_ne hi] using hρ i
  · refine rk_base_lt_lam (D0.or (D0.nad 1) (trich 0 1)) ?_ _ lam hlam hl hρ
    simp [D0.LevLE, levLE_trich]

/-- **B92 Thm 2.9 (c) 3**: `⊢*_λ (Ad.2)^λ`. -/
theorem star_ad2 {lam : Ordinal.{1}} (hlam : ω * lam = lam) (hl : 0 < lam) {Δ : Set RSS}
    (hA : RSS.base (ad2D lam) Fin.elim0 ∈ Δ) : Star R lam Δ := by
  refine star_ball' hA rfl (fun a ha => ?_)
  refine star_ball' (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) rfl (fun b hb => ?_)
  refine star_ad2_body hlam hl _ ?_ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  intro i
  induction i using Fin.lastCases with
  | last => simpa [level_L] using hb
  | cast j =>
    have : j = 0 := Fin.eq_zero j
    subst this
    simpa [level_L] using ha

/-! ### (Ad.3) -/

/-- `(Ad.3)^λ` at `ψ`: `∀x∈L_λ (Ad x → ψ^x)`. -/
def ad3D (lam : Ordinal.{1}) (ψ : D0 1) : D0 0 :=
  D0.ball (Bd.lev lam) (D0.or (D0.nad 0) ψ)

theorem update_ext_zero (a t : T) :
    Function.update (ext (Fin.elim0 : Fin 0 → T) a) 0 t = ext (Fin.elim0 : Fin 0 → T) t := by
  funext i
  have : i = 0 := Fin.eq_zero i
  subst this
  simp

/-- `⊢*_λ (Ad.3)^λ` at `ψ`, from `⊢* ψ^{L_κ}` for all `κ ∈ R`. -/
theorem star_ad3 {lam : Ordinal.{1}} (hlam : ω * lam = lam) (hl : 0 < lam) (ψ : D0 1)
    (hψ : D0.LevLE 0 ψ)
    (H : ∀ κ ∈ R, κ < lam → ∀ Δ' : Set RSS, (0 : Ordinal.{1}) ∈ starK R (kSeq Δ') →
      RSS.base ψ (ext Fin.elim0 (T.L κ)) ∈ Δ' → Star R lam Δ')
    {Δ : Set RSS} (hA : RSS.base (ad3D lam ψ) Fin.elim0 ∈ Δ) : Star R lam Δ := by
  refine star_ball' hA rfl (fun a ha => ?_)
  refine Star.ad' ψ (ext Fin.elim0 a) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (fun κ => ?_) ?_
  · have hκlt : κ.1 < lam := lt_of_le_of_lt κ.2.2.2 (by simpa [level_L] using ha)
    rw [update_ext_zero]
    exact H κ.1 κ.2.1 hκlt _
      (starK_mono R (kSeq_mono (Set.subset_insert _ _))
        (zero_mem_starK_of_memInstL (Set.mem_insert _ _))) (Set.mem_insert _ _)
  · refine rk_base_lt_lam ψ hψ _ lam hlam hl (fun i => ?_)
    have : i = 0 := Fin.eq_zero i
    subst this
    simpa [level_L] using ha

end OrdinalAnalysis.KPi.RS
