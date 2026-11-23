module

public import OrdinalAnalysis.KPi.RS.HRules
public import OrdinalAnalysis.KPi.RS.StarSim

/-!
# The RS calculus, part 29: `HInf` is invariant under presentation (`Sim`)

B92 identifies sentences up to presentation.  In the de Bruijn presentation the same sentence has several
representatives (`Sim R A B`); `HInf.sim` transports an `H`-controlled derivation along a one-sided
correspondence of sequents:  if every member of `Γ` has a `Sim`-partner in `Γ'` and `k(Γ') ⊆ H`, then
`H ⊢^α_ρ Γ ⇒ H ⊢^α_ρ Γ'`.  (The `(Ref)` rule has its principal formula up to `Sim`, so it is transported;
the levels `|ι|` are determined by the `k`-data, `lvl_eq_of_ks_eq`.)
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}}

/-! ### `|ι|` is the largest element of `k(ι)` -/

theorem kD_le : ∀ {n : ℕ} (φ : D0 n) (α : Ordinal.{1}) (e : Fin n → Set Ordinal.{1}),
    D0.LevLE α φ → (∀ i, ∀ ξ ∈ e i, ξ ≤ α) → ∀ ξ ∈ kD φ e, ξ ≤ α
  | _, .mem i j, α, e, _, he, ξ, hξ => by
    rcases hξ with h | h
    · exact he i ξ h
    · exact he j ξ h
  | _, .nmem i j, α, e, _, he, ξ, hξ => by
    rcases hξ with h | h
    · exact he i ξ h
    · exact he j ξ h
  | _, .ad i, α, e, _, he, ξ, hξ => he i ξ hξ
  | _, .nad i, α, e, _, he, ξ, hξ => he i ξ hξ
  | _, .and A B, α, e, hl, he, ξ, hξ => by
    rcases hξ with h | h
    · exact kD_le A α e hl.1 he ξ h
    · exact kD_le B α e hl.2 he ξ h
  | _, .or A B, α, e, hl, he, ξ, hξ => by
    rcases hξ with h | h
    · exact kD_le A α e hl.1 he ξ h
    · exact kD_le B α e hl.2 he ξ h
  | _, .bex b A, α, e, hl, he, ξ, hξ => by
    have he' : ∀ i, ∀ ξ ∈ ext e ∅ i, ξ ≤ α := by
      intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast j => simpa using he j
    cases b with
    | var i =>
      rcases hξ with h | h
      · exact he i ξ h
      · exact kD_le A α _ hl he' ξ h
    | lev γ =>
      rcases hξ with h | h
      · have : ξ = γ := h
        rw [this]; exact hl.1
      · exact kD_le A α _ hl.2 he' ξ h
  | _, .ball b A, α, e, hl, he, ξ, hξ => by
    have he' : ∀ i, ∀ ξ ∈ ext e ∅ i, ξ ≤ α := by
      intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast j => simpa using he j
    cases b with
    | var i =>
      rcases hξ with h | h
      · exact he i ξ h
      · exact kD_le A α _ hl he' ξ h
    | lev γ =>
      rcases hξ with h | h
      · have : ξ = γ := h
        rw [this]; exact hl.1
      · exact kD_le A α _ hl.2 he' ξ h

theorem PT.k_le_level : ∀ (t : PT), t.Wf → ∀ ξ ∈ t.k, ξ ≤ t.level
  | .L α, _, ξ, hξ => by
    have : ξ = α := hξ
    rw [this]; exact le_rfl
  | .sep α φ a, hw, ξ, hξ => by
    obtain ⟨h0, hL, ha, hOcc⟩ := hw
    rcases hξ with h | h
    · have : ξ = α := h
      rw [this]; exact le_rfl
    · refine kD_le φ α _ hL ?_ ξ h
      intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast j =>
        intro η hη
        have hη' : η ∈ (a j).k := by simpa using hη
        exact (PT.k_le_level (a j) (ha j).1 η hη').trans (ha j).2.le

theorem ks_le_lvl (A : RSS) (j : (expand R A).J) :
    ∀ ξ ∈ (expand R A).ks j, ξ ≤ (expand R A).lvl j := by
  cases A with
  | base φ ρ =>
    cases φ with
    | mem i k => exact fun ξ hξ => PT.k_le_level j.1.1 j.1.2 ξ hξ
    | nmem i k => exact fun ξ hξ => PT.k_le_level j.1.1 j.1.2 ξ hξ
    | ad i => exact fun ξ hξ => le_of_eq (show ξ = j.1 from hξ)
    | nad i => exact fun ξ hξ => le_of_eq (show ξ = j.1 from hξ)
    | and X Y => exact fun ξ hξ => absurd hξ (Set.notMem_empty _)
    | or X Y => exact fun ξ hξ => absurd hξ (Set.notMem_empty _)
    | bex b X => exact fun ξ hξ => PT.k_le_level j.1.1 j.1.2 ξ hξ
    | ball b X => exact fun ξ hξ => PT.k_le_level j.1.1 j.1.2 ξ hξ
  | and X Y => exact fun ξ hξ => absurd hξ (Set.notMem_empty _)
  | or X Y => exact fun ξ hξ => absurd hξ (Set.notMem_empty _)

theorem lvl_eq_of_ks_eq {A B : RSS} (j : (expand R A).J) (j' : (expand R B).J)
    (h : (expand R B).ks j' = (expand R A).ks j) : (expand R B).lvl j' = (expand R A).lvl j := by
  have hA := lvl_cases A j
  have hB := lvl_cases B j'
  have leA := ks_le_lvl A j
  have leB := ks_le_lvl B j'
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · rw [hA, hB]
  · have := leA _ (h ▸ hB)
    rw [hA] at this ⊢
    exact le_antisymm this zero_le
  · have := leB _ (h.symm ▸ hA)
    rw [hB] at this ⊢
    exact (le_antisymm this zero_le).symm
  · exact le_antisymm (leA _ (h ▸ hB)) (leB _ (h.symm ▸ hA))

/-- the `k`-bound for the premise sequents of `(⋀)`: `k(A_ι) ⊆ H[ι]`. -/
theorem kSeq_child_sub {H : Op} (hH : NiceOp H) {A : RSS} {Γ : Set RSS} (hA : A ∈ Γ)
    (hΓ : kSeq Γ ⊆ H ∅) (j : (expand R A).J) :
    kSeq (insert ((expand R A).child j) Γ) ⊆ Hext H ((expand R A).ks j) ∅ := by
  rw [Hext_empty_apply]
  set K := (expand R A).ks j
  refine kSeq_insert_sub ?_ (hΓ.trans (hH.empty_sub K))
  refine (child_k_sub A j).trans ?_
  refine Set.union_subset (Set.union_subset ((k_sub_kSeq hA).trans (hΓ.trans (hH.empty_sub K)))
    (hH.sub K)) ?_
  intro x hx
  have : x = 0 := hx
  subst this
  exact (hH.nice K).1

theorem HInf.sim {H : Op} {Γ : Set RSS} {α ρ : Ordinal.{1}} (h : HInf R H Γ α ρ) :
    NiceOp H → ∀ {Γ' : Set RSS}, (∀ x ∈ Γ, ∃ y ∈ Γ', Sim R x y) → kSeq Γ' ⊆ H ∅ →
      HInf R H Γ' α ρ := by
  induction h with
  | @all H Γ A α ρ hα hk hA α₀ h0 h ih =>
    intro hH Γ' hΓ hk'
    obtain ⟨A', hA'Γ, hsim⟩ := hΓ A (Set.mem_insert _ _)
    have hA'or : (expand R A').isOr = false := by rw [← hsim.isOr_eq]; exact hA
    cases hsim with
    | mk hor hkk f hf hfk g hg hgk =>
      refine HInf.all' hA'Γ hα hk' hA'or (fun j' => α₀ (g j')) (fun j' => h0 (g j')) (fun j' => ?_)
      have hHj : NiceOp (Hext H ((expand R A).ks (g j'))) := hH.ext _
      have key := ih (g j') hHj
        (Γ' := insert ((expand R A').child j') Γ') (by
          intro x hx
          rcases hx with rfl | hx
          · exact ⟨_, Set.mem_insert _ _, hg j'⟩
          · obtain ⟨y, hy, hxy⟩ := hΓ x (Set.mem_insert_of_mem _ hx)
            exact ⟨y, Set.mem_insert_of_mem _ hy, hxy⟩) (by
          rw [hgk j']
          exact kSeq_child_sub hH hA'Γ hk' j')
      rwa [hgk j'] at key
  | @ex H Γ A α ρ α₀ hα hk j hA h0 hl h ih =>
    intro hH Γ' hΓ hk'
    obtain ⟨A', hA'Γ, hsim⟩ := hΓ A (Set.mem_insert _ _)
    have hA'or : (expand R A').isOr = true := by rw [← hsim.isOr_eq]; exact hA
    cases hsim with
    | mk hor hkk f hf hfk g hg hgk =>
      have hl' : (expand R A').lvl (f j) < α := by
        rw [lvl_eq_of_ks_eq j (f j) (hfk j)]; exact hl
      refine HInf.ex1' hA'Γ hα hk' (f j) hA'or h0 hl' ?_
      refine ih hH (Γ' := insert ((expand R A').child (f j)) Γ') (by
          intro x hx
          rcases hx with rfl | hx
          · exact ⟨_, Set.mem_insert _ _, hf j⟩
          · obtain ⟨y, hy, hxy⟩ := hΓ x (Set.mem_insert_of_mem _ hx)
            exact ⟨y, Set.mem_insert_of_mem _ hy, hxy⟩) ?_
      refine kSeq_insert_sub ?_ hk'
      refine (child_k_sub A' (f j)).trans ?_
      refine Set.union_subset (Set.union_subset ((k_sub_kSeq hA'Γ).trans hk') ?_) ?_
      · rw [hfk j]
        exact (ks_sub_k A j).trans (h.k_sub.trans' (by
          intro x hx; exact ⟨_, Set.mem_insert _ _, hx⟩)) |>.trans (subset_rfl)
      · intro x hx
        have : x = 0 := hx
        subst this
        exact (hH.nice ∅).1
  | @cut H Γ C α ρ α₀ hα hk hC h0 h1 h2 ih1 ih2 =>
    intro hH Γ' hΓ hk'
    refine HInf.cut (C := C) hα hk' hC h0 (ih1 hH ?_ (kSeq_insert_sub ?_ hk'))
      (ih2 hH ?_ (kSeq_insert_sub ?_ hk'))
    · intro x hx
      rcases hx with rfl | hx
      · exact ⟨_, Set.mem_insert _ _, Sim.refl _⟩
      · obtain ⟨y, hy, hxy⟩ := hΓ x hx
        exact ⟨y, Set.mem_insert_of_mem _ hy, hxy⟩
    · exact (k_sub_kSeq (Set.mem_insert _ _)).trans h1.k_sub
    · intro x hx
      rcases hx with rfl | hx
      · exact ⟨_, Set.mem_insert _ _, Sim.refl _⟩
      · obtain ⟨y, hy, hxy⟩ := hΓ x hx
        exact ⟨y, Set.mem_insert_of_mem _ hy, hxy⟩
    · exact (k_sub_kSeq (Set.mem_insert _ _)).trans h2.k_sub
  | @ref H Γ α ρ α₀ κ S hκ X hX hα hk h0 h ih =>
    intro hH Γ' hΓ hk'
    obtain ⟨X', hX'Γ, hsim⟩ := hΓ X (Set.mem_insert _ _)
    have hX' : Sim R X' S.refl := hsim.symm.trans hX
    have hkS : S.sentence.k ⊆ H ∅ := (k_sub_kSeq (Set.mem_insert S.sentence Γ)).trans h.k_sub
    have h2 := ih hH (Γ' := insert S.sentence Γ') (by
        intro x hx
        rcases hx with rfl | hx
        · exact ⟨_, Set.mem_insert _ _, Sim.refl _⟩
        · obtain ⟨y, hy, hxy⟩ := hΓ x (Set.mem_insert_of_mem _ hx)
          exact ⟨y, Set.mem_insert_of_mem _ hy, hxy⟩) (kSeq_insert_sub hkS hk')
    have := HInf.ref (Γ := Γ') S hκ hX' hα (by rwa [Set.insert_eq_of_mem hX'Γ]) h0 h2
    rwa [Set.insert_eq_of_mem hX'Γ] at this

end OrdinalAnalysis.KPi.RS
