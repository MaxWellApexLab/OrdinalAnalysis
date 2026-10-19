module

public import OrdinalAnalysis.KPi.RS.StarCol

/-!
# The RS calculus, part 23: the closed `(Δ₀-Col)^b`, definitions and the `Sim`-link to `(Ref)*`

For `φ(z₁..z_k, x, y) ∈ Δ₀` (a `D0 (k+2)` with context `[z⃗, x, y]`) and a quantifier bound `b` of
`D0 m`:

  `(Δ₀-Col)^b ≡ ∀z⃗∈b ∀w∈b [ ∀x∈w ∃y∈b φ → ∃w₁∈b ∀x∈w ∃y∈w₁ φ ]`

(`colD b k φ`).  After `closeB` the matrix is `colCore`, `∀w∈b (¬A ∨ C)` with `A ≡ ∀x∈w ∃y∈b φ`
(`colA`) and `C ≡ ∃w₁∈b ∀x∈w ∃y∈w₁ φ` (`colC`).  When `b` evaluates to `L_κ` the matrix
`¬A ∨ C` is `Sim`-equivalent to the `(Ref)*` leaf `RSS.or (ψ^{L_κ})^c (∃z∈L_κ ψ^z)` of the `Σ(κ)`-datum
`colSigma` (`ψ = ∀x∈w ∃y∈d φ`): `sim_colInner`.
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}} {σ : Ordinal.{1}}

/-! ### the formulas -/

/-- `φ(c⃗, x, y)` in the context `[ρ, c⃗, w, x, y]`. -/
def mapA (m k : ℕ) : Fin (k + 2) → Fin (m + k + 3) :=
  ext (ext (fun j : Fin k => (Fin.natAdd m j).castSucc.castSucc.castSucc)
    (Fin.castSucc (Fin.last (m + k + 1)))) (Fin.last (m + k + 2))

/-- `φ(c⃗, x, y)` in the context `[ρ, c⃗, w, w₁, x, y]`. -/
def mapC (m k : ℕ) : Fin (k + 2) → Fin (m + k + 4) :=
  ext (ext (fun j : Fin k => (Fin.natAdd m j).castSucc.castSucc.castSucc.castSucc)
    (Fin.castSucc (Fin.last (m + k + 2)))) (Fin.last (m + k + 3))

/-- `φ(c⃗, x, y)` in the context `[c⃗, w, d, x, y]` (the one used by `colPlace`). -/
def mapPsi (k : ℕ) : Fin (k + 2) → Fin (k + 4) :=
  ext (ext (fun j : Fin k => j.castSucc.castSucc.castSucc.castSucc)
    (Fin.castSucc (Fin.last (k + 2)))) (Fin.last (k + 3))

theorem colPlace_eq {k : ℕ} (φ : D0 (k + 2)) : colPlace φ = φ.rename (mapPsi k) := rfl

/-- `∀x∈w ∃y∈b φ` in the context `[ρ, c⃗, w]`. -/
def colA {m : ℕ} (b : Bd m) (k : ℕ) (φ : D0 (k + 2)) : D0 (m + k + 1) :=
  D0.ball (Bd.var (Fin.last (m + k)))
    (D0.bex (((b.shiftN k).shift).shift) (φ.rename (mapA m k)))

/-- `∃w₁∈b ∀x∈w ∃y∈w₁ φ` in the context `[ρ, c⃗, w]`. -/
def colC {m : ℕ} (b : Bd m) (k : ℕ) (φ : D0 (k + 2)) : D0 (m + k + 1) :=
  D0.bex ((b.shiftN k).shift)
    (D0.ball (Bd.var (Fin.castSucc (Fin.last (m + k))))
      (D0.bex (Bd.var (Fin.castSucc (Fin.last (m + k + 1)))) (φ.rename (mapC m k))))

/-- `¬A ∨ C` in the context `[ρ, c⃗, w]`. -/
def colInner {m : ℕ} (b : Bd m) (k : ℕ) (φ : D0 (k + 2)) : D0 (m + k + 1) :=
  D0.or (colA b k φ).neg (colC b k φ)

/-- `∀w∈b (¬A ∨ C)` in the context `[ρ, c⃗]`. -/
def colCore {m : ℕ} (b : Bd m) (k : ℕ) (φ : D0 (k + 2)) : D0 (m + k) :=
  D0.ball (b.shiftN k) (colInner b k φ)

/-- `(Δ₀-Col)^b`. -/
def colD {m : ℕ} (b : Bd m) (k : ℕ) (φ : D0 (k + 2)) : D0 m :=
  closeB b k (colCore b k φ)

/-! ### `k`-lemmas -/

theorem kBd_resBd {n : ℕ} (b : Bd n) (ρ : Fin n → T) :
    kBd b (fun i => (ρ i).k) = (resBd b ρ).k := by
  cases b <;> rfl

theorem kBd_shift {n : ℕ} (b : Bd n) (e : Fin n → Set Ordinal.{1}) (s : Set Ordinal.{1}) :
    kBd b.shift (ext e s) = kBd b e := by
  cases b with
  | var i => simp [Bd.shift, kBd]
  | lev α => rfl

theorem ext_kfun {n : ℕ} (ρ : Fin n → T) (t : T) :
    (fun i => ((ext ρ t) i).k) = ext (fun i => (ρ i).k) t.k := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

theorem kD_rename_agree {m n1 n2 : ℕ} (A : D0 m) (f1 : Fin m → Fin n1) (f2 : Fin m → Fin n2)
    (ε1 : Fin n1 → Set Ordinal.{1}) (ε2 : Fin n2 → Set Ordinal.{1})
    (h : ∀ i, ε1 (f1 i) = ε2 (f2 i)) : kD (A.rename f1) ε1 = kD (A.rename f2) ε2 := by
  rw [kD_rename, kD_rename]
  congr 1
  funext i
  exact h i

/-! ### agreement of the variable maps -/

theorem agreeA {X : Sort _} {m k : ℕ} (Cx : Fin (m + k) → X) (c : Fin k → X)
    (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j) (w x y d : X) :
    ∀ i, (ext (ext (ext Cx w) x) y) (mapA m k i) =
      (ext (ext (ext (ext c w) d) x) y) (mapPsi k i) := by
  intro i
  induction i using Fin.lastCases with
  | last => simp [mapA, mapPsi]
  | cast i =>
    induction i using Fin.lastCases with
    | last => simp [mapA, mapPsi]
    | cast j =>
      simp only [mapA, mapPsi, ext_castSucc]
      exact hC j

theorem agreeC {X : Sort _} {m k : ℕ} (Cx : Fin (m + k) → X) (c : Fin k → X)
    (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j) (w w1 x y : X) :
    ∀ i, (ext (ext (ext (ext Cx w) w1) x) y) (mapC m k i) =
      (ext (ext (ext (ext c w) w1) x) y) (mapPsi k i) := by
  intro i
  induction i using Fin.lastCases with
  | last => simp [mapC, mapPsi]
  | cast i =>
    induction i using Fin.lastCases with
    | last => simp [mapC, mapPsi]
    | cast j =>
      simp only [mapC, mapPsi, ext_castSucc]
      exact hC j

theorem kBd_shiftN_eq {m k : ℕ} (b : Bd m) (Cx : Fin (m + k) → T) {κ : Ordinal.{1}}
    (hb : resBd (b.shiftN k) Cx = T.L κ) : kBd (b.shiftN k) (fun i => (Cx i).k) = {κ} := by
  rw [kBd_resBd, hb]
  rfl

theorem kfun_natAdd {m k : ℕ} (Cx : Fin (m + k) → T) (c : Fin k → T)
    (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j) :
    ∀ j : Fin k, (fun i => (Cx i).k) (Fin.natAdd m j) = (fun j => (c j).k) j := by
  intro j
  show (Cx (Fin.natAdd m j)).k = (c j).k
  rw [hC j]

/-! ### `¬A` against the `Σ(κ)`-sentence -/

theorem kD_colA_inner {m k : ℕ} (b : Bd m) (φ : D0 (k + 2)) (Cx : Fin (m + k) → T)
    (c : Fin k → T) (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j) {κ : Ordinal.{1}}
    (hb : resBd (b.shiftN k) Cx = T.L κ) (w : T) (s : Set Ordinal.{1}) :
    kD (D0.ball ((b.shiftN k).shift.shift) (φ.rename (mapA m k)).neg)
        (ext (ext (fun i => (Cx i).k) w.k) s) =
      kD (D0.ball (Bd.var (Fin.castSucc (Fin.last (k + 1)))) (colPlace φ).neg)
        (ext (ext (ext (fun i => (c i).k) w.k) (T.L κ).k) s) := by
  simp only [kD]
  rw [kBd_shift, kBd_shift, kBd_shiftN_eq b Cx hb]
  have h2 : kBd (Bd.var (Fin.castSucc (Fin.last (k + 1))))
      (ext (ext (ext (fun i => (c i).k) w.k) (T.L κ).k) s) = {κ} := by
    simp [kBd, k_L]
  rw [h2]
  congr 1
  rw [D0.rename_neg, colPlace_eq, D0.rename_neg]
  exact kD_rename_agree φ.neg _ _ _ _
    (agreeA (fun i => (Cx i).k) (fun j => (c j).k) (kfun_natAdd Cx c hC) w.k s ∅ (T.L κ).k)

theorem sim_colA_neg {m k : ℕ} (b : Bd m) (φ : D0 (k + 2)) (Cx : Fin (m + k) → T) (c : Fin k → T)
    (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j) {κ : Ordinal.{1}}
    (hb : resBd (b.shiftN k) Cx = T.L κ) (w : T) :
    Sim R (RSS.base (colA b k φ).neg (ext Cx w))
      (RSS.base (colPsi φ).neg (ext (ext c w) (T.L κ))) := by
  refine sim_bex_gen (Bd.var (Fin.last (m + k))) (Bd.var (Fin.castSucc (Fin.last k)))
    _ _ _ _ (by simp [resBd]) (fun t => ?_) ?_
  · refine sim_ball_gen _ _ _ _ _ _ ?_ (fun t' => ?_) ?_
    · rw [resBd_shift, resBd_shift, hb]
      simp [resBd]
    · show Sim R (RSS.base (φ.rename (mapA m k)).neg _) (RSS.base (φ.rename (mapPsi k)).neg _)
      rw [D0.rename_neg, D0.rename_neg]
      exact sim_rename φ.neg _ _ _ _ (agreeA Cx c hC w t t' (T.L κ))
    · simp only [RSS.k_base, ext_kfun]
      exact kD_colA_inner b φ Cx c hC hb w t.k
  · simp only [RSS.k_base, ext_kfun, kD]
    exact congrArg₂ (· ∪ ·) (by simp [kBd]) (kD_colA_inner b φ Cx c hC hb w ∅)

/-! ### `C` against the `(Ref)*`-reflection -/

theorem kD_colC_in {m k : ℕ} (φ : D0 (k + 2)) (Cx : Fin (m + k) → T) (c : Fin k → T)
    (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j) (w : T) (s1 s2 : Set Ordinal.{1}) :
    kD (D0.bex (Bd.var (Fin.castSucc (Fin.last (m + k + 1)))) (φ.rename (mapC m k)))
        (ext (ext (ext (fun i => (Cx i).k) w.k) s1) s2) =
      kD (D0.bex (Bd.var (Fin.castSucc (Fin.last (k + 1)))) (colPlace φ))
        (ext (ext (ext (fun i => (c i).k) w.k) s1) s2) := by
  simp only [kD]
  refine congrArg₂ (· ∪ ·) (by simp [kBd]) ?_
  rw [colPlace_eq]
  exact kD_rename_agree φ _ _ _ _
    (agreeC (fun i => (Cx i).k) (fun j => (c j).k) (kfun_natAdd Cx c hC) w.k s1 s2 ∅)

theorem kD_colC_mid {m k : ℕ} (φ : D0 (k + 2)) (Cx : Fin (m + k) → T) (c : Fin k → T)
    (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j) (w : T) (s : Set Ordinal.{1}) :
    kD (D0.ball (Bd.var (Fin.castSucc (Fin.last (m + k))))
        (D0.bex (Bd.var (Fin.castSucc (Fin.last (m + k + 1)))) (φ.rename (mapC m k))))
        (ext (ext (fun i => (Cx i).k) w.k) s) =
      kD (colPsi φ) (ext (ext (fun i => (c i).k) w.k) s) := by
  simp only [colPsi, kD]
  exact congrArg₂ (· ∪ ·) (by simp [kBd]) (kD_colC_in φ Cx c hC w s ∅)

theorem sim_colC {m k : ℕ} (b : Bd m) (φ : D0 (k + 2)) (Cx : Fin (m + k) → T) (c : Fin k → T)
    (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j) {κ : Ordinal.{1}}
    (hb : resBd (b.shiftN k) Cx = T.L κ) (w : T) :
    Sim R (RSS.base (colC b k φ) (ext Cx w))
      (RSS.base (D0.bex (Bd.lev κ) (colPsi φ)) (ext c w)) := by
  refine sim_bex_gen _ _ _ _ _ _ (by simp [resBd_shift, hb]) (fun t => ?_) ?_
  · refine sim_ball_gen _ _ _ _ _ _ (by simp [resBd]) (fun t' => ?_) ?_
    · refine sim_bex_gen _ _ _ _ _ _ (by simp [resBd]) (fun t'' => ?_) ?_
      · show Sim R (RSS.base (φ.rename (mapC m k)) _) (RSS.base (φ.rename (mapPsi k)) _)
        exact sim_rename φ _ _ _ _ (agreeC Cx c hC w t t' t'')
      · simp only [RSS.k_base, ext_kfun]
        exact kD_colC_in φ Cx c hC w t.k t'.k
    · simp only [RSS.k_base, ext_kfun]
      exact kD_colC_mid φ Cx c hC w t.k
  · simp only [RSS.k_base, ext_kfun]
    refine congrArg₂ (· ∪ ·) ?_ (kD_colC_mid φ Cx c hC w ∅)
    rw [kBd_shift, kBd_shiftN_eq b Cx hb]
    rfl

/-- the matrix `¬A ∨ C` of `(Δ₀-Col)^b` is the `(Ref)*`-leaf of `colSigma` (up to presentation). -/
theorem sim_colInner {m k : ℕ} (b : Bd m) (φ : D0 (k + 2)) (hφ : D0.NoLev φ)
    (Cx : Fin (m + k) → T) (c : Fin k → T) (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j)
    {κ : Ordinal.{1}} (hb : resBd (b.shiftN k) Cx = T.L κ) (hc : ∀ i, (c i).level < κ)
    (w : T) (hw : w.level < κ) :
    Sim R (RSS.base (colInner b k φ) (ext Cx w))
      (RSS.or (colSigma φ hφ c w hc hw).sentence.neg (colSigma φ hφ c w hc hw).refl) := by
  have h1 := sim_colA_neg (R := R) b φ Cx c hC hb w
  have h2 := sim_colC (R := R) b φ Cx c hC hb w
  have hk : (RSS.base (colInner b k φ) (ext Cx w)).k =
      (RSS.or (colSigma φ hφ c w hc hw).sentence.neg (colSigma φ hφ c w hc hw).refl).k := by
    show (RSS.base (colA b k φ).neg (ext Cx w)).k ∪ (RSS.base (colC b k φ) (ext Cx w)).k =
      (RSS.base (colPsi φ).neg (ext (ext c w) (T.L κ))).k ∪
        (RSS.base (D0.bex (Bd.lev κ) (colPsi φ)) (ext c w)).k
    rw [h1.k_eq, h2.k_eq]
  refine Sim.mk rfl hk id ?_ (fun j => rfl) id ?_ (fun j => rfl)
  · intro j
    rcases j with ⟨b'⟩
    cases b'
    · exact h2
    · exact h1
  · intro j
    rcases j with ⟨b'⟩
    cases b'
    · exact h2
    · exact h1

end OrdinalAnalysis.KPi.RS
