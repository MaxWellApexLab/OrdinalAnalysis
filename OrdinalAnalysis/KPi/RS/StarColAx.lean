module

public import OrdinalAnalysis.KPi.RS.StarColSim

/-!
# The RS calculus, part 24: B92 Theorem 2.9 (b) and the `(Δ₀-Col)`-instances of `(Ad.3)`; Theorem 2.9 complete

* `star_col`, `star_col_closed` : `⊢*_σ (Δ₀-Col)^b` for `σ > 0` whenever `b` evaluates to `L_κ`,
  `κ ∈ R`.  The matrix `¬A ∨ C` of the closed sentence is `Sim`-equivalent to the `(Ref)*` leaf of
  `colSigma` (`sim_colInner`), which is an axiom of `RS*` for `σ > 0`.
* `star_ad3_col` : `⊢*_λ (Ad.3)^λ` at a `(Δ₀-Col)`-instance, from `star_col` and `star_ad3`.
* `star_kpi`     : B92 Theorem 2.9 (b), (c) for the whole axiom list of `KPi` (`star_kpl` and the
  `(Δ₀-Col)`-parts).  `(Δ₀-Col)^λ` itself is *not* claimed: `L_λ` is in general not admissible
  (that is exactly why B92's (c) is stated for `KPℓ`, and `(Δ₀-Col)` enters only through `(Ad.3)`).
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}} {σ : Ordinal.{1}}

/-! ### `(Δ₀-Col)^b` -/

/-- `⊢*_σ ∀w∈L_κ [¬A ∨ C]` at the instantiated parameters (the `(Ref)*` step). -/
theorem star_colCore {m k : ℕ} (b : Bd m) (φ : D0 (k + 2)) (hφ : D0.NoLev φ) {κ : Ordinal.{1}}
    (hκ : κ ∈ R) (hσ : 0 < σ) (Cx : Fin (m + k) → T) (c : Fin k → T)
    (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j) (hb : resBd (b.shiftN k) Cx = T.L κ)
    (hc : ∀ i, (c i).level < κ) {Δ : Set RSS} (hA : RSS.base (colCore b k φ) Cx ∈ Δ) :
    Star R σ Δ := by
  refine star_ball' hA hb (fun w hw => ?_)
  have hw' : w.level < κ := hw
  have hsim := sim_colInner (R := R) b φ hφ Cx c hC hb hc w hw'
  have h := Star.ref (R := R) (Γ := Δ) (σ := σ) (colSigma φ hφ c w hc hw') hκ hσ hsim
  exact Star.mono h (Set.subset_insert _ _)

/-- **B92 Thm 2.9 (b)**: `⊢*_σ (Δ₀-Col)^b` (`σ > 0`) when `b` evaluates to `L_κ`, `κ ∈ R`. -/
theorem star_col {m : ℕ} (b : Bd m) (k : ℕ) (φ : D0 (k + 2)) (hφ : D0.NoLev φ)
    {κ : Ordinal.{1}} (hκ : κ ∈ R) (hσ : 0 < σ) (ρ : Fin m → T) (hb : resBd b ρ = T.L κ)
    {Δ : Set RSS} (hA : RSS.base (colD b k φ) ρ ∈ Δ) : Star R σ Δ := by
  refine star_closeB b ρ κ hb k (colCore b k φ) (fun c hc Δ' _ hA' => ?_) hA
  exact star_colCore b φ hφ hκ hσ (ctxK ρ k c) c (ctxK_natAdd ρ k c)
    (by rw [resBd_shiftN, hb]) hc hA'

/-- **B92 Thm 2.9 (b)**, closed form: `⊢*_σ (Δ₀-Col)^κ` for `κ ∈ R`, `σ > 0` (B92: `σ = 1`). -/
theorem star_col_closed {κ : Ordinal.{1}} (hκ : κ ∈ R) (hσ : 0 < σ) (k : ℕ) (φ : D0 (k + 2))
    (hφ : D0.NoLev φ) {Δ : Set RSS}
    (hA : RSS.base (colD (Bd.lev κ) k φ) Fin.elim0 ∈ Δ) : Star R σ Δ :=
  star_col (Bd.lev κ) k φ hφ hκ hσ Fin.elim0 rfl hA

/-! ### `(Ad.3)` at `(Δ₀-Col)` -/

theorem noLev_levLE : ∀ {n : ℕ} (A : D0 n), D0.NoLev A → D0.LevLE 0 A
  | _, .mem _ _, _ => trivial
  | _, .nmem _ _, _ => trivial
  | _, .ad _, _ => trivial
  | _, .nad _, _ => trivial
  | _, .and A B, h => ⟨noLev_levLE A h.1, noLev_levLE B h.2⟩
  | _, .or A B, h => ⟨noLev_levLE A h.1, noLev_levLE B h.2⟩
  | _, .bex (.var _) A, h => noLev_levLE A h
  | _, .bex (.lev _) _, h => h.elim
  | _, .ball (.var _) A, h => noLev_levLE A h
  | _, .ball (.lev _) _, h => h.elim

theorem levLE_colD_var {m : ℕ} (i : Fin m) (k : ℕ) (φ : D0 (k + 2)) (hφ : D0.LevLE 0 φ) :
    D0.LevLE 0 (colD (Bd.var i) k φ) := by
  refine levLE_closeB_var i k _ ?_
  obtain ⟨j, hj⟩ := Bd.shiftN_var i k
  have hA : D0.LevLE 0 (φ.rename (mapA m k)) := levLE_rename _ φ hφ
  have hC : D0.LevLE 0 (φ.rename (mapC m k)) := levLE_rename _ φ hφ
  have hAn : D0.LevLE 0 (φ.rename (mapA m k)).neg := levLE_neg _ hA
  simp [colCore, colInner, colA, colC, D0.neg, hj, Bd.shift, D0.LevLE, hC, hAn]

/-- **B92 Thm 2.9 (c) 2, `(Δ₀-Col)`-instances of `(Ad.3)`**: `⊢*_λ (Ad.3)^λ`. -/
theorem star_ad3_col {lam : Ordinal.{1}} (hlam : ω * lam = lam) (hl : 0 < lam) (k : ℕ)
    (φ : D0 (k + 2)) (hφ : D0.NoLev φ) {Δ : Set RSS}
    (hA : RSS.base (ad3D lam (colD (Bd.var 0) k φ)) Fin.elim0 ∈ Δ) : Star R lam Δ := by
  refine star_ad3 hlam hl _ (levLE_colD_var 0 k φ (noLev_levLE φ hφ))
    (fun κ hκ _ Δ' _ hA' => ?_) hA
  exact star_col (Bd.var 0) k φ hφ hκ hl (ext Fin.elim0 (T.L κ)) (by simp [resBd]) hA'

/-! ### **B92 Theorem 2.9 (b), (c)** for `KPi` -/

/-- **B92 Theorem 2.9 (b), (c)**, the full axiom list of `KPi`:
the conjuncts 1-11 are `star_kpl`; 12 is (b), `⊢*_1 (Δ₀-Col)^κ` for `κ ∈ R`; 13 is the
`(Δ₀-Col)`-instances of `(Ad.3)`, `⊢*_λ (Ad.3)^λ`. -/
theorem star_kpi {lam : Ordinal.{1}} (h : KPlHyp R lam) :
    Star R lam {RSS.base (extD lam) Fin.elim0} ∧
    (∀ (k : ℕ) (A : D0 (k + 1)), Star R lam {RSS.base (foundD lam k A) Fin.elim0}) ∧
    Star R lam {RSS.base (pairD (Bd.lev lam)) Fin.elim0} ∧
    Star R lam {RSS.base (unionD (Bd.lev lam)) Fin.elim0} ∧
    (∀ (k : ℕ) (φ : D0 (k + 1)), D0.LevLE 0 φ →
      Star R lam {RSS.base (sepD (Bd.lev lam) k φ) Fin.elim0}) ∧
    Star R lam {RSS.base (ad1D lam) Fin.elim0} ∧
    Star R lam {RSS.base (ad2D lam) Fin.elim0} ∧
    Star R lam {RSS.base (ad3D lam (pairD (Bd.var 0))) Fin.elim0} ∧
    Star R lam {RSS.base (ad3D lam (unionD (Bd.var 0))) Fin.elim0} ∧
    (∀ (k : ℕ) (φ : D0 (k + 1)), D0.LevLE 0 φ →
      Star R lam {RSS.base (ad3D lam (sepD (Bd.var 0) k φ)) Fin.elim0}) ∧
    Star R lam {RSS.base (limD lam) Fin.elim0} ∧
    (∀ κ ∈ R, ∀ (k : ℕ) (φ : D0 (k + 2)), D0.NoLev φ →
      Star R 1 {RSS.base (colD (Bd.lev κ) k φ) Fin.elim0}) ∧
    (∀ (k : ℕ) (φ : D0 (k + 2)), D0.NoLev φ →
      Star R lam {RSS.base (ad3D lam (colD (Bd.var 0) k φ)) Fin.elim0}) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := star_kpl h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, ?_⟩
  · intro κ hκ k φ hφ
    exact star_col_closed hκ zero_lt_one k φ hφ (Set.mem_singleton _)
  · intro k φ hφ
    exact star_ad3_col h.mul h.pos k φ hφ (Set.mem_singleton _)

end OrdinalAnalysis.KPi.RS
