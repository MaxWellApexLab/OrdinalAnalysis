module

public import OrdinalAnalysis.KPi.RS.HNice
public import OrdinalAnalysis.KPi.RS.StarBasic

/-!
# The RS calculus, part 27: `k`, `lvl` and `rk` of the members of a junctor

* `child_k_sub`  : B92 Lemma 1.9 (c), second half: `k(A_ι) ⊆ k(A) ∪ k(ι) ∪ {0}`
                    (`0` because `L_0` occurs in `t ∈° L_β`);
* `ks_sub_k`     : (first half, `StarBasic`);
* `lvl_cases`    : `|ι| = 0` or `|ι| ∈ k(ι)`;
* `RSS.K`        : `β ∈ k(A) ⇒ ω·β ≤ rk A`;
* `lvl_le_rk`    : `|ι| ≤ rk A_ι`;
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}}

/-! ### `kD` is monotone in the environment up to a fixed set -/

theorem kBd_env {n : ℕ} (b : Bd n) (e e0 : Fin n → Set Ordinal.{1}) (X : Set Ordinal.{1})
    (h : ∀ i, e i ⊆ e0 i ∪ X) : kBd b e ⊆ kBd b e0 ∪ X := by
  cases b with
  | var i => exact h i
  | lev α => exact Set.subset_union_left

theorem ext_env_sub {n : ℕ} (e e0 : Fin n → Set Ordinal.{1}) (X : Set Ordinal.{1})
    (h : ∀ i, e i ⊆ e0 i ∪ X) : ∀ i, ext e ∅ i ⊆ ext e0 ∅ i ∪ X := by
  intro i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simpa using h j

theorem kD_env : ∀ {n : ℕ} (φ : D0 n) (e e0 : Fin n → Set Ordinal.{1}) (X : Set Ordinal.{1}),
    (∀ i, e i ⊆ e0 i ∪ X) → kD φ e ⊆ kD φ e0 ∪ X
  | _, .mem i j, e, e0, X, h => by
    simp only [kD]
    refine Set.union_subset ?_ ?_
    · exact (h i).trans (Set.union_subset_union_left _ Set.subset_union_left)
    · exact (h j).trans (Set.union_subset_union_left _ Set.subset_union_right)
  | _, .nmem i j, e, e0, X, h => by
    simp only [kD]
    refine Set.union_subset ?_ ?_
    · exact (h i).trans (Set.union_subset_union_left _ Set.subset_union_left)
    · exact (h j).trans (Set.union_subset_union_left _ Set.subset_union_right)
  | _, .ad i, e, e0, X, h => by simpa only [kD] using h i
  | _, .nad i, e, e0, X, h => by simpa only [kD] using h i
  | _, .and A B, e, e0, X, h => by
    simp only [kD]
    refine Set.union_subset ?_ ?_
    · exact (kD_env A e e0 X h).trans (Set.union_subset_union_left _ Set.subset_union_left)
    · exact (kD_env B e e0 X h).trans (Set.union_subset_union_left _ Set.subset_union_right)
  | _, .or A B, e, e0, X, h => by
    simp only [kD]
    refine Set.union_subset ?_ ?_
    · exact (kD_env A e e0 X h).trans (Set.union_subset_union_left _ Set.subset_union_left)
    · exact (kD_env B e e0 X h).trans (Set.union_subset_union_left _ Set.subset_union_right)
  | _, .bex b A, e, e0, X, h => by
    simp only [kD]
    refine Set.union_subset ?_ ?_
    · exact (kBd_env b e e0 X h).trans (Set.union_subset_union_left _ Set.subset_union_left)
    · exact (kD_env A _ _ X (ext_env_sub e e0 X h)).trans
        (Set.union_subset_union_left _ Set.subset_union_right)
  | _, .ball b A, e, e0, X, h => by
    simp only [kD]
    refine Set.union_subset ?_ ?_
    · exact (kBd_env b e e0 X h).trans (Set.union_subset_union_left _ Set.subset_union_left)
    · exact (kD_env A _ _ X (ext_env_sub e e0 X h)).trans
        (Set.union_subset_union_left _ Set.subset_union_right)

/-! ### `k` of the pieces of a junctor -/

theorem k_L (β : Ordinal.{1}) : (T.L β).k = {β} := rfl

theorem k_eqS_sub (a b : T) : (eqS a b).k ⊆ a.k ∪ b.k := by
  show kD (D0.eqf 0 1) (fun i => (![a, b] i).k) ⊆ _
  intro ξ hξ
  simp [D0.eqf, D0.subset, kD, kBd] at hξ ⊢
  tauto

theorem k_memInst_sub (t b : T) : (memInst t b).k ⊆ b.k ∪ t.k ∪ {0} := by
  rcases b with ⟨b, hb⟩
  cases b with
  | L β =>
    show kD (D0.nmem 0 1) (fun i => (![t, T.L 0] i).k) ⊆ _
    intro ξ hξ
    simp [kD, T.L] at hξ
    rcases hξ with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  | sep β φ a =>
    obtain ⟨h0, hL, ha, hOcc⟩ := hb
    show kD φ (fun i => T.k (ext (fun i => (⟨a i, (ha i).1⟩ : T)) t i)) ⊆ _
    rw [ext_comp T.k]
    have h1 := kD_env φ (ext (fun i => T.k ⟨a i, (ha i).1⟩) t.k)
      (ext (fun i => T.k ⟨a i, (ha i).1⟩) ∅) t.k (by
        intro i
        induction i using Fin.lastCases with
        | last => simp
        | cast j => simp)
    refine h1.trans ?_
    intro ξ hξ
    rcases hξ with hξ | hξ
    · exact Or.inl (Or.inl (Or.inr hξ))
    · exact Or.inl (Or.inr hξ)

theorem k_base_ext_sub {n : ℕ} (φ : D0 (n + 1)) (ρ : Fin n → T) (t : T) :
    (RSS.base φ (ext ρ t)).k ⊆ kD φ (ext (fun i => (ρ i).k) ∅) ∪ t.k := by
  show kD φ (fun i => (ext ρ t i).k) ⊆ _
  rw [ext_comp T.k]
  exact kD_env φ _ _ t.k (by
    intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp)

/-- B92 Lemma 1.9 (c), second half. -/
theorem child_k_sub (A : RSS) (j : (expand R A).J) :
    ((expand R A).child j).k ⊆ A.k ∪ (expand R A).ks j ∪ {0} := by
  cases A with
  | base φ ρ =>
    cases φ with
    | mem i k =>
      show (RSS.and (memInst j.1 (ρ k)) (eqS j.1 (ρ i))).k ⊆ _
      intro ξ hξ
      rcases hξ with hξ | hξ
      · rcases k_memInst_sub j.1 (ρ k) hξ with (h | h) | h
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rcases k_eqS_sub j.1 (ρ i) hξ with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl (Or.inl h))
    | nmem i k =>
      show (RSS.or (memInst j.1 (ρ k)).neg (eqS j.1 (ρ i)).neg).k ⊆ _
      intro ξ hξ
      rcases hξ with hξ | hξ
      · rw [RSS.k_neg] at hξ
        rcases k_memInst_sub j.1 (ρ k) hξ with (h | h) | h
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rw [RSS.k_neg] at hξ
        rcases k_eqS_sub j.1 (ρ i) hξ with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl (Or.inl h))
    | ad i =>
      show (eqS (T.L j.1) (ρ i)).k ⊆ _
      intro ξ hξ
      rcases k_eqS_sub (T.L j.1) (ρ i) hξ with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
    | nad i =>
      show (eqS (T.L j.1) (ρ i)).neg.k ⊆ _
      intro ξ hξ
      rw [RSS.k_neg] at hξ
      rcases k_eqS_sub (T.L j.1) (ρ i) hξ with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
    | and X Y =>
      intro ξ hξ
      rcases j with ⟨b⟩
      cases b
      · exact Or.inl (Or.inl (Or.inr hξ))
      · exact Or.inl (Or.inl (Or.inl hξ))
    | or X Y =>
      intro ξ hξ
      rcases j with ⟨b⟩
      cases b
      · exact Or.inl (Or.inl (Or.inr hξ))
      · exact Or.inl (Or.inl (Or.inl hξ))
    | bex b X =>
      show (RSS.and (memInst j.1 (resBd b ρ)) (RSS.base X (ext ρ j.1))).k ⊆ _
      intro ξ hξ
      rcases hξ with hξ | hξ
      · rcases k_memInst_sub j.1 (resBd b ρ) hξ with (h | h) | h
        · refine Or.inl (Or.inl ?_)
          cases b with
          | var i => exact Or.inl h
          | lev α => exact Or.inl h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rcases k_base_ext_sub X ρ j.1 hξ with h | h
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inl (Or.inr h)
    | ball b X =>
      show (RSS.or (memInst j.1 (resBd b ρ)).neg (RSS.base X (ext ρ j.1))).k ⊆ _
      intro ξ hξ
      rcases hξ with hξ | hξ
      · rw [RSS.k_neg] at hξ
        rcases k_memInst_sub j.1 (resBd b ρ) hξ with (h | h) | h
        · refine Or.inl (Or.inl ?_)
          cases b with
          | var i => exact Or.inl h
          | lev α => exact Or.inl h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rcases k_base_ext_sub X ρ j.1 hξ with h | h
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inl (Or.inr h)
  | and X Y =>
    intro ξ hξ
    rcases j with ⟨b⟩
    cases b
    · exact Or.inl (Or.inl (Or.inr hξ))
    · exact Or.inl (Or.inl (Or.inl hξ))
  | or X Y =>
    intro ξ hξ
    rcases j with ⟨b⟩
    cases b
    · exact Or.inl (Or.inl (Or.inr hξ))
    · exact Or.inl (Or.inl (Or.inl hξ))

/-! ### levels and ranks -/

theorem RSS.K : ∀ (A : RSS) (β : Ordinal.{1}), β ∈ A.k → ω * β ≤ A.rk
  | .base φ ρ, β, hβ =>
    rkD_K φ (fun i => (ρ i).rk) (fun i => (ρ i).k) (fun i β hβ => PT.K (ρ i).1 β hβ) β hβ
  | .and A B, β, hβ => by
    rcases hβ with hβ | hβ
    · exact (RSS.K A β hβ).trans (le_trans (le_max_left _ _) le_self_add)
    · exact (RSS.K B β hβ).trans (le_trans (le_max_right _ _) le_self_add)
  | .or A B, β, hβ => by
    rcases hβ with hβ | hβ
    · exact (RSS.K A β hβ).trans (le_trans (le_max_left _ _) le_self_add)
    · exact (RSS.K B β hβ).trans (le_trans (le_max_right _ _) le_self_add)

theorem lvl_cases (A : RSS) (j : (expand R A).J) :
    (expand R A).lvl j = 0 ∨ (expand R A).lvl j ∈ (expand R A).ks j := by
  cases A with
  | base φ ρ =>
    cases φ with
    | mem i k => exact Or.inr (PT.level_mem_k j.1.1)
    | nmem i k => exact Or.inr (PT.level_mem_k j.1.1)
    | ad i => exact Or.inr rfl
    | nad i => exact Or.inr rfl
    | and X Y => exact Or.inl rfl
    | or X Y => exact Or.inl rfl
    | bex b X => exact Or.inr (PT.level_mem_k j.1.1)
    | ball b X => exact Or.inr (PT.level_mem_k j.1.1)
  | and X Y => exact Or.inl rfl
  | or X Y => exact Or.inl rfl

/-- `|ι| ≤ rk A_ι`. -/
theorem lvl_le_rk (A : RSS) (j : (expand R A).J) :
    (expand R A).lvl j ≤ ((expand R A).child j).rk := by
  rcases lvl_cases A j with h | h
  · rw [h]; exact zero_le
  · have h1 := RSS.K _ _ (ks_sub_k A j h)
    exact (Ordinal.le_mul_right _ omega0_pos).trans h1

end OrdinalAnalysis.KPi.RS
