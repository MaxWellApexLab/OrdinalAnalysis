import OrdinalAnalysis.KPi.RS.StarDefs

/-!
# The RS calculus, part 6: `k`-facts, duality of junctors, and `(TND)` (B92 Lemma 2.4)

* `kD_occ`, `k_memInst`, `ks_sub_k`   : `k(ι) ⊆ k(A_ι)` (B92 Lemma 1.9 (c), first half);
* `expand_neg_isOr`, `expand_neg_child` : the junctor of `¬A` is dual to that of `A`;
* `star_tnd`                          : `⊢* ¬A, A` (by induction on `rk A`).
-/

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}}

/-! ### `k(ι) ⊆ k(A_ι)` (B92 Lemma 1.9 (c), first half) -/

theorem kD_neg : ∀ {n : ℕ} (A : D0 n) (e : Fin n → Set Ordinal.{1}), kD A.neg e = kD A e
  | _, .mem i j, e => by simp [D0.neg, kD]
  | _, .nmem i j, e => by simp [D0.neg, kD]
  | _, .ad i, e => by simp [D0.neg, kD]
  | _, .nad i, e => by simp [D0.neg, kD]
  | _, .and A B, e => by simp [D0.neg, kD, kD_neg A, kD_neg B]
  | _, .or A B, e => by simp [D0.neg, kD, kD_neg A, kD_neg B]
  | _, .bex b A, e => by simp [D0.neg, kD, kD_neg A]
  | _, .ball b A, e => by simp [D0.neg, kD, kD_neg A]

theorem RSS.k_neg : ∀ A : RSS, A.neg.k = A.k
  | .base φ ρ => by simp [RSS.neg, RSS.k, kD_neg]
  | .and A B => by simp [RSS.neg, RSS.k, RSS.k_neg A, RSS.k_neg B]
  | .or A B => by simp [RSS.neg, RSS.k, RSS.k_neg A, RSS.k_neg B]

theorem kD_occ : ∀ {n : ℕ} (A : D0 n) (i : Fin n) (e : Fin n → Set Ordinal.{1}),
    D0.Occ i A → e i ⊆ kD A e
  | _, .mem a b, i, e, h => by
      rcases h with rfl | rfl
      · exact Set.subset_union_left
      · exact Set.subset_union_right
  | _, .nmem a b, i, e, h => by
      rcases h with rfl | rfl
      · exact Set.subset_union_left
      · exact Set.subset_union_right
  | _, .ad a, i, e, h => by
      rcases h; exact le_rfl
  | _, .nad a, i, e, h => by
      rcases h; exact le_rfl
  | _, .and A B, i, e, h => by
      rcases h with h | h
      · exact (kD_occ A i e h).trans Set.subset_union_left
      · exact (kD_occ B i e h).trans Set.subset_union_right
  | _, .or A B, i, e, h => by
      rcases h with h | h
      · exact (kD_occ A i e h).trans Set.subset_union_left
      · exact (kD_occ B i e h).trans Set.subset_union_right
  | _, .bex (.var j) A, i, e, h => by
      rcases h with rfl | h
      · exact Set.subset_union_left
      · have := kD_occ A i.castSucc (ext e ∅) h
        simp only [ext_castSucc] at this
        exact this.trans Set.subset_union_right
  | _, .bex (.lev γ) A, i, e, h => by
      have := kD_occ A i.castSucc (ext e ∅) h
      simp only [ext_castSucc] at this
      exact this.trans Set.subset_union_right
  | _, .ball (.var j) A, i, e, h => by
      rcases h with rfl | h
      · exact Set.subset_union_left
      · have := kD_occ A i.castSucc (ext e ∅) h
        simp only [ext_castSucc] at this
        exact this.trans Set.subset_union_right
  | _, .ball (.lev γ) A, i, e, h => by
      have := kD_occ A i.castSucc (ext e ∅) h
      simp only [ext_castSucc] at this
      exact this.trans Set.subset_union_right

theorem k_memInst (t b : T) : t.k ⊆ (memInst t b).k := by
  rcases b with ⟨b, hb⟩
  cases b with
  | L β =>
    show t.k ⊆ kD (D0.nmem 0 1) (fun i => (![t, T.L 0] i).k)
    intro ξ hξ
    exact Or.inl hξ
  | sep β φ a =>
    obtain ⟨h0, hL, ha, hOcc⟩ := hb
    show t.k ⊆ kD φ (fun i => T.k (ext (fun i => (⟨a i, (ha i).1⟩ : T)) t i))
    rw [ext_comp T.k]
    have := kD_occ φ (Fin.last _) (ext (fun i => T.k ⟨a i, (ha i).1⟩) t.k) hOcc
    simpa using this

theorem k_eqS_left (a b : T) : a.k ⊆ (eqS a b).k := by
  show a.k ⊆ kD (D0.eqf 0 1) (fun i => (![a, b] i).k)
  intro ξ hξ
  exact Or.inl (Or.inl hξ)

theorem ks_sub_k (A : RSS) (j : (expand R A).J) : (expand R A).ks j ⊆ ((expand R A).child j).k := by
  cases A with
  | base φ ρ =>
    cases φ with
    | mem i k => exact (k_memInst j.1 (ρ k)).trans Set.subset_union_left
    | nmem i k =>
      show j.1.k ⊆ (memInst j.1 (ρ k)).neg.k ∪ _
      rw [RSS.k_neg]
      exact (k_memInst j.1 (ρ k)).trans Set.subset_union_left
    | ad i =>
      show ({j.1} : Set Ordinal.{1}) ⊆ (eqS (T.L j.1) (ρ i)).k
      intro ξ hξ
      have h1 : ξ = j.1 := hξ
      exact k_eqS_left (T.L j.1) (ρ i) (by simp [T.k, PT.k, T.L, h1])
    | nad i =>
      show ({j.1} : Set Ordinal.{1}) ⊆ (eqS (T.L j.1) (ρ i)).neg.k
      rw [RSS.k_neg]
      intro ξ hξ
      have h1 : ξ = j.1 := hξ
      exact k_eqS_left (T.L j.1) (ρ i) (by simp [T.k, PT.k, T.L, h1])
    | and X Y => exact Set.empty_subset _
    | or X Y => exact Set.empty_subset _
    | bex b X => exact (k_memInst j.1 _).trans Set.subset_union_left
    | ball b X =>
      show j.1.k ⊆ (memInst j.1 (resBd b ρ)).neg.k ∪ _
      rw [RSS.k_neg]
      exact (k_memInst j.1 _).trans Set.subset_union_left
  | and X Y => exact Set.empty_subset _
  | or X Y => exact Set.empty_subset _

/-! ### duality of junctors -/

theorem expand_neg_isOr (A : RSS) : (expand R A.neg).isOr = !(expand R A).isOr := by
  cases A with
  | base φ ρ => cases φ <;> rfl
  | and X Y => rfl
  | or X Y => rfl

theorem expand_neg_child (A : RSS) (j : (expand R A).J) :
    ∃ j' : (expand R A.neg).J, (expand R A.neg).child j' = ((expand R A).child j).neg ∧
      (expand R A.neg).ks j' = (expand R A).ks j := by
  cases A with
  | base φ ρ =>
    cases φ with
    | mem i k => exact ⟨j, rfl, rfl⟩
    | nmem i k =>
      refine ⟨j, ?_, rfl⟩
      show RSS.and (memInst j.1 (ρ k)) (eqS j.1 (ρ i)) =
        RSS.neg (RSS.or (memInst j.1 (ρ k)).neg (eqS j.1 (ρ i)).neg)
      simp [RSS.neg]
    | ad i => exact ⟨j, rfl, rfl⟩
    | nad i =>
      refine ⟨j, ?_, rfl⟩
      show eqS (T.L j.1) (ρ i) = RSS.neg (eqS (T.L j.1) (ρ i)).neg
      simp
    | and X Y =>
      refine ⟨j, ?_, rfl⟩
      rcases j with ⟨b⟩
      cases b <;> rfl
    | or X Y =>
      refine ⟨j, ?_, rfl⟩
      rcases j with ⟨b⟩
      cases b <;> rfl
    | bex b X => exact ⟨j, rfl, rfl⟩
    | ball b X =>
      refine ⟨j, ?_, rfl⟩
      show RSS.and (memInst j.1 (resBd b ρ)) (RSS.base X.neg (ext ρ j.1)) =
        RSS.neg (RSS.or (memInst j.1 (resBd b ρ)).neg (RSS.base X (ext ρ j.1)))
      simp [RSS.neg]
  | and X Y =>
    refine ⟨j, ?_, rfl⟩
    rcases j with ⟨b⟩
    cases b <;> rfl
  | or X Y =>
    refine ⟨j, ?_, rfl⟩
    rcases j with ⟨b⟩
    cases b <;> rfl

/-! ### (TND): `⊢* ¬A, A` (B92 Lemma 2.4) -/

theorem tnd_of_and (σ : Ordinal.{1}) (A : RSS) (hA : (expand R A).isOr = false)
    (ih : ∀ j, Star R σ {((expand R A).child j).neg, (expand R A).child j}) :
    Star R σ {A.neg, A} := by
  have hB : (expand R A.neg).isOr = true := by rw [expand_neg_isOr, hA]; rfl
  rw [Set.pair_comm]
  refine Star.all (Γ := {A.neg}) hA (fun j => ?_)
  obtain ⟨j', hc, hks⟩ := expand_neg_child (R := R) A j
  rw [Set.pair_comm]
  refine Star.ex (A := A.neg) (Γ := {(expand R A).child j}) {j'} (Set.finite_singleton _) hB ?_ ?_
  · intro j'' hj''
    have : j'' = j' := hj''
    subst this
    rw [hks]
    exact (ks_sub_k A j).trans
      ((k_sub_kSeq (Set.mem_insert_of_mem _ (Set.mem_singleton _))).trans (subset_starK R _))
  · rw [Set.image_singleton, hc, Set.singleton_union, Set.pair_comm]
    exact ih j

theorem star_tnd (σ : Ordinal.{1}) : ∀ A : RSS, Star R σ {A.neg, A} := by
  intro A
  refine rk_ind (P := fun A => Star R σ {A.neg, A}) (fun A ih => ?_) A
  by_cases hA : (expand R A).isOr = true
  · have hB : (expand R A.neg).isOr = false := by rw [expand_neg_isOr, hA]; rfl
    have := tnd_of_and σ A.neg hB (fun j' => by
      refine ih _ ?_
      have := child_rk_lt R A.neg j'
      rwa [RSS.rk_neg] at this)
    rw [RSS.neg_neg, Set.pair_comm] at this
    exact this
  · have hA' : (expand R A).isOr = false := by simpa using hA
    exact tnd_of_and σ A hA' (fun j => ih _ (child_rk_lt R A j))

end OrdinalAnalysis.KPi.RS
