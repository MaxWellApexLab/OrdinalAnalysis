module

public import OrdinalAnalysis.KPi.RS.StarAxAd

/-!
# The RS calculus, part 21: Theorem 2.9 (c) for `KPℓ`

`KPlHyp R lam` : `λ` is a limit with `ω·λ = λ` and `∀α<λ ∃κ∈R (α<κ<λ)`; the members of `R` are
limits above `ω`.  Under these hypotheses `⊢*_λ φ^λ` for every axiom `φ` of `KPℓ` (= KPi without
`(Δ₀-Col)`; the `(Δ₀-Col)`-instances of `(Ad.3)` are the subject of `StarCol`).
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}} {σ : Ordinal.{1}}

/-- the hypotheses of B92 Theorem 2.9 (c). -/
structure KPlHyp (R : Set Ordinal.{1}) (lam : Ordinal.{1}) : Prop where
  reg : ∀ κ ∈ R, ω < κ ∧ Order.IsSuccLimit κ
  lim : Order.IsSuccLimit lam
  mul : ω * lam = lam
  dense : ∀ α < lam, ∃ κ ∈ R, α < κ ∧ κ < lam

theorem KPlHyp.pos {lam : Ordinal.{1}} (h : KPlHyp R lam) : 0 < lam := by
  simpa using h.lim.bot_lt

/-! ### `LevLE 0` of the instances -/

theorem levLE_tran {n : ℕ} (i : Fin n) : D0.LevLE 0 (D0.tran i) := by
  simp [D0.tran, D0.LevLE]

theorem levLE_infinite {n : ℕ} (i : Fin n) : D0.LevLE 0 (D0.infinite i) := by
  simp [D0.infinite, D0.subset, D0.LevLE]

/-- `χ(x) = tran(x) ∧ ∃w∈x infinite(w)`. -/
def ad1Chi : D0 1 := D0.and (D0.tran 0) (D0.bex (Bd.var 0) (D0.infinite (Fin.last 1)))

theorem levLE_ad1Chi : D0.LevLE 0 ad1Chi := by
  simp [ad1Chi, D0.LevLE, levLE_tran, levLE_infinite]

/-- `(Ad.1)^λ`. -/
def ad1D (lam : Ordinal.{1}) : D0 0 := ad3D lam ad1Chi

theorem Bd.shiftN_var {m : ℕ} (i : Fin m) :
    ∀ k : ℕ, ∃ j : Fin (m + k), (Bd.var i).shiftN k = Bd.var j
  | 0 => ⟨i, rfl⟩
  | k + 1 => by
    obtain ⟨j, hj⟩ := Bd.shiftN_var i k
    exact ⟨j.castSucc, by simp [Bd.shiftN, hj, Bd.shift]⟩

theorem levLE_closeB_var {m : ℕ} (i : Fin m) :
    ∀ (k : ℕ) (φ : D0 (m + k)), D0.LevLE 0 φ → D0.LevLE 0 (closeB (Bd.var i) k φ)
  | 0, φ, h => h
  | k + 1, φ, h => by
    obtain ⟨j, hj⟩ := Bd.shiftN_var i k
    refine levLE_closeB_var i k _ ?_
    simp only [hj]
    exact h

theorem levLE_sepD_var {m : ℕ} (i : Fin m) (k : ℕ) (φ : D0 (k + 1)) (hφ : D0.LevLE 0 φ) :
    D0.LevLE 0 (sepD (Bd.var i) k φ) := by
  refine levLE_closeB_var i k _ ?_
  obtain ⟨j, hj⟩ := Bd.shiftN_var i k
  have h3 : D0.LevLE 0 (sepPlace (m := m) φ) := levLE_rename _ φ hφ
  have h3n : D0.LevLE 0 (sepPlace (m := m) φ).neg := levLE_neg _ h3
  simp [sepCore, sepInner, sepMat, hj, Bd.shift, D0.LevLE, h3, h3n]

/-! ### the instances -/

theorem star_ad1 (hR : ∀ κ ∈ R, ω < κ) {lam : Ordinal.{1}} (hlam : ω * lam = lam)
    (hl : 0 < lam) {Δ : Set RSS} (hA : RSS.base (ad1D lam) Fin.elim0 ∈ Δ) : Star R lam Δ := by
  refine star_ad3 hlam hl ad1Chi levLE_ad1Chi (fun κ hκ _ Δ' h0 hA' => ?_) hA
  refine star_band_of (n := 1) (X := D0.tran 0)
    (Y := D0.bex (Bd.var 0) (D0.infinite (Fin.last 1))) hA' ?_ ?_
  · exact star_tran_L (i := 0) (α := κ) (by simp) (Set.mem_insert _ _)
  · refine star_bex' (s := T.L κ) (Set.mem_insert _ _) (by simp [resBd]) (T.L ω) (hR κ hκ) ?_
      (star_memInst_L' _ _) ?_
    · exact fun ξ hξ => Or.inl (Or.inl (Or.inr hξ))
    · refine star_infinite_L (i := Fin.last 1) (by simp) ?_ (Set.mem_insert _ _)
      exact starK_mono R (kSeq_mono ((Set.subset_insert _ _).trans (Set.subset_insert _ _))) h0

theorem star_ad3_pair (hlim : ∀ κ ∈ R, Order.IsSuccLimit κ) {lam : Ordinal.{1}}
    (hlam : ω * lam = lam) (hl : 0 < lam) {Δ : Set RSS}
    (hA : RSS.base (ad3D lam (pairD (Bd.var 0))) Fin.elim0 ∈ Δ) : Star R lam Δ := by
  refine star_ad3 hlam hl _ (levLE_pairD _ (fun α h => by cases h))
    (fun κ hκ _ Δ' _ hA' => ?_) hA
  exact Star.mono_sigma (star_pair (hlim κ hκ) (by simp [resBd]) hA') zero_le

theorem star_ad3_union {lam : Ordinal.{1}}
    (hlam : ω * lam = lam) (hl : 0 < lam) {Δ : Set RSS}
    (hA : RSS.base (ad3D lam (unionD (Bd.var 0))) Fin.elim0 ∈ Δ) : Star R lam Δ := by
  refine star_ad3 hlam hl _ (levLE_unionD _ (fun α h => by cases h))
    (fun κ hκ _ Δ' _ hA' => ?_) hA
  exact Star.mono_sigma (star_union (lam := κ) (by simp [resBd]) hA') zero_le

theorem star_ad3_sep (hlim : ∀ κ ∈ R, Order.IsSuccLimit κ) {lam : Ordinal.{1}}
    (hlam : ω * lam = lam) (hl : 0 < lam) (k : ℕ) (φ : D0 (k + 1)) (hφ : D0.LevLE 0 φ)
    {Δ : Set RSS} (hA : RSS.base (ad3D lam (sepD (Bd.var 0) k φ)) Fin.elim0 ∈ Δ) :
    Star R lam Δ := by
  refine star_ad3 hlam hl _ (levLE_sepD_var 0 k φ hφ) (fun κ hκ _ Δ' _ hA' => ?_) hA
  exact Star.mono_sigma (star_sep (Bd.var 0) k φ hφ (hlim κ hκ) _ (by simp [resBd]) hA')
    zero_le

/-! ### **B92 Theorem 2.9 (c)** -/

/-- **B92 Theorem 2.9 (c)** for the axioms of `KPℓ` that do not involve `(Δ₀-Col)`:
`⊢*_λ φ^λ`. -/
theorem star_kpl {lam : Ordinal.{1}} (h : KPlHyp R lam) :
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
    Star R lam {RSS.base (limD lam) Fin.elim0} := by
  have hlim : ∀ κ ∈ R, Order.IsSuccLimit κ := fun κ hκ => (h.reg κ hκ).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Star.mono_sigma (star_ext lam (Set.mem_singleton _)) zero_le
  · intro k A
    exact star_found_closed lam k A h.pos (Set.mem_singleton _)
  · exact star_pair h.lim rfl (Set.mem_singleton _)
  · exact star_union rfl (Set.mem_singleton _)
  · intro k φ hφ
    exact Star.mono_sigma (star_sep (Bd.lev lam) k φ hφ h.lim Fin.elim0 rfl (Set.mem_singleton _))
      zero_le
  · exact star_ad1 (fun κ hκ => (h.reg κ hκ).1) h.mul h.pos (Set.mem_singleton _)
  · exact star_ad2 h.mul h.pos (Set.mem_singleton _)
  · exact star_ad3_pair hlim h.mul h.pos (Set.mem_singleton _)
  · exact star_ad3_union h.mul h.pos (Set.mem_singleton _)
  · intro k φ hφ
    exact star_ad3_sep hlim h.mul h.pos k φ hφ (Set.mem_singleton _)
  · exact star_lim lam h.dense (Set.mem_singleton _)

end OrdinalAnalysis.KPi.RS
