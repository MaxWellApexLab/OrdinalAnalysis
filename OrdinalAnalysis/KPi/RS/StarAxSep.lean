module

public import OrdinalAnalysis.KPi.RS.StarAxSepDefs

/-!
# The RS calculus, part 19: Theorem 2.9 (a), `(Δ₀-Sep)`

For `φ(z₁,…,z_k, x) ∈ Δ₀` (a `D0 (k+1)` without level constants other than `L₀`):

  `(Δ₀-Sep)^b ≡ ∀z⃗∈b ∀w∈b ∃y∈b [∀x∈y (x ∈ w ∧ φ) ∧ ∀x∈w (φ → x ∈ y)]`

is derivable (in `⊢*`) whenever `b` evaluates to `L_λ`, `λ` a limit ordinal.  B92's proof: the witness
is the term `d = [x ∈ L_δ : x ∈ a ∧ φ(x, c⃗)]`, `δ = max(|a|, |c⃗|) + 1`.
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}}

/-! ### the sentence -/

/-- the schema formula `φ(z⃗, x)` placed in the context `[ρ, c⃗, w, y, x]`. -/
def sepPlace {m k : ℕ} (φ : D0 (k + 1)) : D0 (m + k + 3) :=
  φ.rename (ext (fun j : Fin k => (Fin.natAdd m j).castSucc.castSucc.castSucc)
    (Fin.last (m + k + 2)))

/-- `∀x∈y (x ∈ w ∧ φ) ∧ ∀x∈w (φ → x ∈ y)` in the context `[ρ, c⃗, w, y]`. -/
def sepMat {m : ℕ} (k : ℕ) (φ : D0 (k + 1)) : D0 (m + k + 2) :=
  D0.and
    (D0.ball (.var (Fin.last (m + k + 1)))
      (D0.and (D0.mem (Fin.last (m + k + 2)) (Fin.castSucc (Fin.castSucc (Fin.last (m + k)))))
        (sepPlace (m := m) φ)))
    (D0.ball (.var (Fin.castSucc (Fin.last (m + k))))
      (D0.or (sepPlace (m := m) φ).neg
        (D0.mem (Fin.last (m + k + 2)) (Fin.castSucc (Fin.last (m + k + 1))))))

/-- `∃y∈b [...]` in the context `[ρ, c⃗, w]`. -/
def sepInner {m : ℕ} (b : Bd m) (k : ℕ) (φ : D0 (k + 1)) : D0 (m + k + 1) :=
  D0.bex (b.shiftN k).shift (sepMat (m := m) k φ)

/-- `∀w∈b ∃y∈b [...]` in the context `[ρ, c⃗]`. -/
def sepCore {m : ℕ} (b : Bd m) (k : ℕ) (φ : D0 (k + 1)) : D0 (m + k) :=
  D0.ball (b.shiftN k) (sepInner b k φ)

/-- `(Δ₀-Sep)^b`. -/
def sepD {m : ℕ} (b : Bd m) (k : ℕ) (φ : D0 (k + 1)) : D0 m :=
  closeB b k (sepCore b k φ)

/-! ### the witness term -/

/-- the body `x ∈ a ∧ φ(x, c⃗)` of the witness, in the context `[c⃗, a, x]`. -/
def sepBody {k : ℕ} (φ : D0 (k + 1)) : D0 (k + 2) :=
  D0.and (D0.mem (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)))
    (φ.rename (ext (fun j : Fin k => j.castSucc.castSucc) (Fin.last (k + 1))))

/-- `[x ∈ L_δ : x ∈ a ∧ φ(x, c⃗)]` (`e = (c⃗, a)`). -/
def sepTerm {k : ℕ} (φ : D0 (k + 1)) (hφ : D0.LevLE 0 φ) (δ : Ordinal.{1}) (hδ : 0 < δ)
    (e : Fin (k + 1) → T) (he : ∀ i, (e i).level < δ) : T :=
  ⟨.sep δ (sepBody φ) (fun i => (e i).1),
    ⟨hδ, ⟨trivial, levLE_mono _ (levLE_rename _ φ hφ) zero_le⟩, fun i => ⟨(e i).2, he i⟩,
      Or.inl (Or.inl rfl)⟩⟩

theorem sepTerm_level {k : ℕ} (φ : D0 (k + 1)) (hφ : D0.LevLE 0 φ) (δ : Ordinal.{1})
    (hδ : 0 < δ) (e : Fin (k + 1) → T) (he : ∀ i, (e i).level < δ) :
    (sepTerm φ hφ δ hδ e he).level = δ := rfl

theorem memInst_sepTerm {k : ℕ} (φ : D0 (k + 1)) (hφ : D0.LevLE 0 φ) (δ : Ordinal.{1})
    (hδ : 0 < δ) (e : Fin (k + 1) → T) (he : ∀ i, (e i).level < δ) (t : T) :
    memInst t (sepTerm φ hφ δ hδ e he) = RSS.base (sepBody φ) (ext e t) := rfl

theorem levLE_sepBody {k : ℕ} (φ : D0 (k + 1)) (hφ : D0.LevLE 0 φ) :
    D0.LevLE 0 (sepBody φ) :=
  ⟨trivial, levLE_rename _ φ hφ⟩

theorem sepTerm_k {k : ℕ} (φ : D0 (k + 1)) (hφ : D0.LevLE 0 φ) (δ : Ordinal.{1})
    (hδ : 0 < δ) (e : Fin (k + 1) → T) (he : ∀ i, (e i).level < δ) (S : Set Ordinal.{1})
    (hδS : δ ∈ S) (h0 : (0 : Ordinal.{1}) ∈ S) (heS : ∀ i, (e i).k ⊆ S) :
    (sepTerm φ hφ δ hδ e he).k ⊆ S := by
  intro ξ hξ
  rcases hξ with hξ | hξ
  · have : ξ = δ := hξ
    rw [this]; exact hδS
  · refine kD_sub (sepBody φ) _ S ?_ (levLE_sepBody φ hφ) h0 hξ
    intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast j =>
      rw [ext_castSucc]
      exact heS j

/-! ### the equivalence of presentations -/

/-- `t ∈° d` and the matrix `t ∈ w ∧ φ` of `∀x∈y (…)` in the context `[ρ, c⃗, w, y, x]`. -/
theorem sim_sepMem {m k : ℕ} (φ : D0 (k + 1)) (Cx : Fin (m + k) → T) (c : Fin k → T)
    (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j) (a d t : T) :
    Sim R (RSS.base (sepBody φ) (ext (ext c a) t))
      (RSS.base (D0.and (D0.mem (Fin.last (m + k + 2)) (Fin.castSucc (Fin.castSucc (Fin.last (m + k)))))
        (sepPlace (m := m) φ)) (ext (ext (ext Cx a) d) t)) := by
  refine sim_band_gen _ _ _ _ _ _ ?_ ?_
  · exact sim_mem_atom _ _ _ _ _ _ (by simp) (by simp)
  · refine sim_rename φ _ _ _ _ ?_
    intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp only [ext_castSucc, hC j]

theorem sim_sepMem_neg {m k : ℕ} (φ : D0 (k + 1)) (Cx : Fin (m + k) → T) (c : Fin k → T)
    (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j) (a d t : T) :
    Sim R (RSS.base (φ.rename (ext (fun j : Fin k => j.castSucc.castSucc) (Fin.last (k + 1)))).neg
        (ext (ext c a) t))
      (RSS.base (sepPlace (m := m) φ).neg (ext (ext (ext Cx a) d) t)) := by
  unfold sepPlace
  simp only [D0.rename_neg]
  refine sim_rename φ.neg _ _ _ _ ?_
  intro i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp only [ext_castSucc, hC j]

/-! ### the derivation -/

/-- `⊢* t ∈° d` for the witness term `d`, given `t ∈ a` and `φ(t, c⃗)`. -/
theorem star_memInst_sepTerm {k : ℕ} (φ : D0 (k + 1)) (hφ : D0.LevLE 0 φ) (δ : Ordinal.{1})
    (hδ : 0 < δ) (c : Fin k → T) (a : T) (he : ∀ i, (ext c a i).level < δ) (t : T)
    (hta : t.level < a.level) {Δ : Set RSS} (hmem : (memInst t a).neg ∈ Δ)
    (hQ : ∃ y ∈ Δ, Sim R (RSS.base (φ.rename (ext (fun j : Fin k => j.castSucc.castSucc)
      (Fin.last (k + 1)))).neg (ext (ext c a) t)) y) :
    Star R 0 (insert (memInst t (sepTerm φ hφ δ hδ (ext c a) he)) Δ) := by
  refine star_band_of (n := k + 2) (X := D0.mem (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)))
    (Y := φ.rename (ext (fun j : Fin k => j.castSucc.castSucc) (Fin.last (k + 1))))
    (ρ := ext (ext c a) t) (Set.mem_insert _ _) ?_ ?_
  · refine star_mem' (s1 := t) (s2 := a) (Set.mem_insert _ _) (by simp) (by simp) t hta
      (hk_of_mem (A := (memInst t a).neg) (by simp [hmem]) (k_neg_memInst _ _)) ?_ ?_
    · exact star_tnd' (A := memInst t a) (by simp) (by simp [hmem])
    · exact star_eq_refl (Set.mem_insert _ _)
  · obtain ⟨y, hyΔ, hsim⟩ := hQ
    refine Star.sim (star_tnd 0 (RSS.base (φ.rename (ext (fun j : Fin k => j.castSucc.castSucc)
      (Fin.last (k + 1)))) (ext (ext c a) t))) ?_
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨y, by simp [hyΔ], hsim⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨_, Set.mem_insert _ _, Sim.refl _⟩

/-- the matrix for the witness `d`. -/
theorem star_sepMat {m k : ℕ} (φ : D0 (k + 1)) (hφ : D0.LevLE 0 φ)
    (Cx : Fin (m + k) → T) (c : Fin k → T) (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j)
    (a : T) (δ : Ordinal.{1}) (hδ : 0 < δ) (he : ∀ i, (ext c a i).level < δ) {Δ : Set RSS}
    (hA : RSS.base (sepMat (m := m) k φ)
      (ext (ext Cx a) (sepTerm φ hφ δ hδ (ext c a) he)) ∈ Δ) : Star R 0 Δ := by
  refine star_band_of hA ?_ ?_
  · refine star_ball' (Set.mem_insert _ _) (s := sepTerm φ hφ δ hδ (ext c a) he)
      (by simp [resBd]) (fun t ht => ?_)
    refine Star.sim (star_tnd 0 (memInst t (sepTerm φ hφ δ hδ (ext c a) he))) ?_
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨_, Set.mem_insert _ _, Sim.refl _⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨_, Set.mem_insert_of_mem _ (Set.mem_insert _ _),
        sim_sepMem φ Cx c hC a (sepTerm φ hφ δ hδ (ext c a) he) t⟩
  · refine star_ball' (Set.mem_insert _ _) (s := a) (by simp [resBd]) (fun t ht => ?_)
    refine star_bor_of (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) ?_
    have ht' : t.level < δ := by
      have h1 : a.level < δ := by simpa using he (Fin.last k)
      exact lt_trans ht h1
    refine star_mem' (s1 := t) (s2 := sepTerm φ hφ δ hδ (ext c a) he)
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (by simp) (by simp) t ht'
      (hk_of_mem (A := (memInst t a).neg) (by simp) (k_neg_memInst _ _)) ?_
      (star_eq_refl (Set.mem_insert _ _))
    refine star_memInst_sepTerm φ hφ δ hδ c a he t ht (by simp) ?_
    exact ⟨_, Set.mem_insert _ _, sim_sepMem_neg φ Cx c hC a _ t⟩

/-- `∃y∈b [...]` for the instantiated terms. -/
theorem star_sepInner {m k : ℕ} (b : Bd m) (φ : D0 (k + 1)) (hφ : D0.LevLE 0 φ)
    {lam : Ordinal.{1}} (hlam : Order.IsSuccLimit lam)
    (Cx : Fin (m + k) → T) (c : Fin k → T) (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j)
    (hb : resBd (b.shiftN k) Cx = T.L lam) (a : T) (ha : a.level < lam)
    (hc : ∀ i, (c i).level < lam) {Δ : Set RSS}
    (hmem : ∀ i, (memInst (c i) (T.L lam)).neg ∈ Δ) (haΔ : (memInst a (T.L lam)).neg ∈ Δ)
    (hA : RSS.base (sepInner b k φ) (ext Cx a) ∈ Δ) : Star R 0 Δ := by
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i : Fin (k + 1) => (ext c a i).level)
  have hlevΔ : ∀ i, (ext c a i).level ∈ kSeq Δ := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      simpa using level_mem_kSeq (A := (memInst a (T.L lam)).neg) haΔ (k_neg_memInst _ _)
    | cast j =>
      simpa using level_mem_kSeq (A := (memInst (c j) (T.L lam)).neg) (hmem j)
        (k_neg_memInst _ _)
  have hkΔ : ∀ i, (ext c a i).k ⊆ starK R (kSeq Δ) := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      simpa using hk_of_mem (R := R) (A := (memInst a (T.L lam)).neg) haΔ (k_neg_memInst _ _)
    | cast j =>
      simpa using hk_of_mem (R := R) (A := (memInst (c j) (T.L lam)).neg) (hmem j)
        (k_neg_memInst _ _)
  have hlt : ∀ i, (ext c a i).level < lam := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa using ha
    | cast j => simpa using hc j
  have hδlt : (ext c a i0).level + 1 < lam := hlam.succ_lt (hlt i0)
  have he : ∀ i, (ext c a i).level < (ext c a i0).level + 1 :=
    fun i => lt_of_le_of_lt (hi0 i) (lt_add_one _)
  have hδ : 0 < (ext c a i0).level + 1 := lt_of_le_of_lt zero_le (lt_add_one _)
  refine star_bex' hA (s := T.L lam) (by rw [resBd_shift, hb])
    (sepTerm φ hφ _ hδ (ext c a) he) hδlt ?_ (star_memInst_L' _ _) ?_
  · exact sepTerm_k φ hφ _ hδ (ext c a) he (starK R (kSeq Δ)) (kmem_succ (hlevΔ i0))
      (zero_mem_starK_of_memInstL haΔ) hkΔ |> fun h => h
  · refine star_sepMat φ hφ Cx c hC a _ hδ he (Set.mem_insert _ _)

/-- `∀w∈b ∃y∈b [...]` at the instantiated parameters. -/
theorem star_sepCore {m k : ℕ} (b : Bd m) (φ : D0 (k + 1)) (hφ : D0.LevLE 0 φ)
    {lam : Ordinal.{1}} (hlam : Order.IsSuccLimit lam)
    (Cx : Fin (m + k) → T) (c : Fin k → T) (hC : ∀ j : Fin k, Cx (Fin.natAdd m j) = c j)
    (hb : resBd (b.shiftN k) Cx = T.L lam) (hc : ∀ i, (c i).level < lam) {Δ : Set RSS}
    (hmem : ∀ i, (memInst (c i) (T.L lam)).neg ∈ Δ)
    (hA : RSS.base (sepCore b k φ) Cx ∈ Δ) : Star R 0 Δ := by
  refine star_ball' hA hb (fun a ha => ?_)
  refine star_sepInner b φ hφ hlam Cx c hC hb a ha hc (fun i => ?_) (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (hmem i))

/-- **B92 Thm 2.9 (a)**: `⊢* (Δ₀-Sep)^b` when `b` evaluates to `L_λ`, `λ` a limit. -/
theorem star_sep {m : ℕ} (b : Bd m) (k : ℕ) (φ : D0 (k + 1)) (hφ : D0.LevLE 0 φ)
    {lam : Ordinal.{1}} (hlam : Order.IsSuccLimit lam) (ρ : Fin m → T)
    (hb : resBd b ρ = T.L lam) {Δ : Set RSS} (hA : RSS.base (sepD b k φ) ρ ∈ Δ) :
    Star R 0 Δ := by
  refine star_closeB b ρ lam hb k (sepCore b k φ) (fun c hc Δ' hmem hA' => ?_) hA
  exact star_sepCore b φ hφ hlam (ctxK ρ k c) c (ctxK_natAdd ρ k c)
    (by rw [resBd_shiftN, hb]) hc hmem hA'

end OrdinalAnalysis.KPi.RS
