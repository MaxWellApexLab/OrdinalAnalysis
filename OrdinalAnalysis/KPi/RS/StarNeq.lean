module

public import OrdinalAnalysis.KPi.RS.StarRefl

/-!
# The RS calculus, part 10: B92 Lemma 2.6

`⊢* [a ≠ b], [L_γ ≠ a]` for `|b| < γ`, in the form (only the two members that are used)

  `Nq1 a b = ¬(a ⊆ b)`, `Nq1 (L_γ) a = ¬(L_γ ⊆ a)`.

Induction on `γ`.
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}}

theorem k_Nq1 (a b : T) : (Nq1 a b).k = a.k ∪ b.k := by
  have h1 : ext (fun i => (![a, b] i).k) ∅ (Fin.last 2) = ∅ := ext_last _ _
  have h2 : ext (fun i => (![a, b] i).k) ∅ (Fin.castSucc 1) = b.k := ext_castSucc _ _ _
  show a.k ∪ (ext (fun i => (![a, b] i).k) ∅ (Fin.last 2) ∪
    ext (fun i => (![a, b] i).k) ∅ (Fin.castSucc 1)) = _
  rw [h1, h2]
  simp

theorem k_Nq2 (a b : T) : (Nq2 a b).k = b.k ∪ a.k := by
  have h1 : ext (fun i => (![a, b] i).k) ∅ (Fin.last 2) = ∅ := ext_last _ _
  have h2 : ext (fun i => (![a, b] i).k) ∅ (Fin.castSucc 0) = a.k := ext_castSucc _ _ _
  show b.k ∪ (ext (fun i => (![a, b] i).k) ∅ (Fin.last 2) ∪
    ext (fun i => (![a, b] i).k) ∅ (Fin.castSucc 0)) = _
  rw [h1, h2]
  simp

theorem k_Nq1_left (a b : T) : a.k ⊆ (Nq1 a b).k := by
  rw [k_Nq1]; exact Set.subset_union_left

theorem k_Nq1_right (a b : T) : b.k ⊆ (Nq1 a b).k := by
  rw [k_Nq1]; exact Set.subset_union_right

theorem k_Nq2_left (a b : T) : a.k ⊆ (Nq2 a b).k := by
  rw [k_Nq2]; exact Set.subset_union_right

theorem k_Nq2_right (a b : T) : b.k ⊆ (Nq2 a b).k := by
  rw [k_Nq2]; exact Set.subset_union_left

theorem star_lem26_aux : ∀ γ : Ordinal.{1}, ∀ a b : T, b.level < γ → ∀ Δ : Set RSS,
    Nq1 a b ∈ Δ → Nq1 (T.L γ) a ∈ Δ → Star R 0 Δ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | _ γ ih =>
  intro a b hbγ Δ h1 h2
  -- the witness `L_β` of `¬(L_γ ⊆ a)`, `β = |b|`
  have hk1 : (T.L b.level).k ⊆ starK R (kSeq Δ) := by
    refine hk_of_mem h1 ?_
    intro ξ hξ
    have : ξ = b.level := hξ
    rw [this]
    exact k_Nq1_right a b (PT.level_mem_k b.1)
  refine star_bex' (b := Bd.var 0) (X := D0.nmem (Fin.last 2) (Fin.castSucc 1))
    (ρ := ![T.L γ, a]) (s := T.L γ) h2 rfl (T.L b.level) hbγ hk1 (star_memInst_L' _ _) ?_
  -- `L_β ∉ a`
  refine star_nmem' (Set.mem_insert _ _) (s1 := T.L b.level) (s2 := a) (by simp) (by simp)
    (fun s hs => ?_)
  -- context: `(s ∈° a)⁻, (s = L_β)⁻`
  have hseq : (eqS s (T.L b.level)).neg ∈ insert (memInst s a).neg (insert (eqS s (T.L b.level)).neg
      (insert (RSS.base (D0.nmem (Fin.last 2) (Fin.castSucc 1)) (ext ![T.L γ, a] (T.L b.level))) Δ)) :=
    by sub_tac_mem
  refine star_neq_of hseq ?_
  set Δ2 := insert (Nq1 s (T.L b.level)) (insert (Nq2 s (T.L b.level))
    (insert (memInst s a).neg (insert (eqS s (T.L b.level)).neg
      (insert (RSS.base (D0.nmem (Fin.last 2) (Fin.castSucc 1)) (ext ![T.L γ, a] (T.L b.level)))
        Δ)))) with hΔ2
  -- `s ∉ b` via the witness `s` of `¬(a ⊆ b)`
  have h1' : Nq1 a b ∈ Δ2 := by simp [hΔ2, h1]
  have key : ∀ (s t : T), t.level < b.level → ∀ Δ4 : Set RSS, Nq2 t s ∈ Δ4 →
      Nq2 s (T.L b.level) ∈ Δ4 → Star R 0 Δ4 := by
    intro s t ht Δ4 hn1 hn2
    refine Star.sim (ih b.level hbγ s t ht
      (insert (Nq1 s t) (insert (Nq1 (T.L b.level) s) Δ4)) (Set.mem_insert _ _) (by simp)) ?_
    intro x hx
    rcases hx with rfl | rfl | hx
    · exact ⟨_, hn1, sim_Nq1 s t⟩
    · exact ⟨_, hn2, sim_Nq1 (T.L b.level) s⟩
    · exact ⟨x, hx, Sim.refl _⟩
  refine star_bex' (b := Bd.var 0) (X := D0.nmem (Fin.last 2) (Fin.castSucc 1))
    (ρ := ![a, b]) (s := a) h1' rfl s hs
    (hk_of_mem (A := (memInst s a).neg) (by simp [hΔ2]) (k_neg_memInst s a))
    (star_tnd' (A := memInst s a) (by simp) (by simp [hΔ2])) ?_
  refine star_nmem' (Set.mem_insert _ _) (s1 := s) (s2 := b) (by simp) (by simp) (fun t ht => ?_)
  have hseq2 : (eqS t s).neg ∈ insert (memInst t b).neg (insert (eqS t s).neg
      (insert (RSS.base (D0.nmem (Fin.last 2) (Fin.castSucc 1)) (ext ![a, b] s)) Δ2)) := by simp
  refine star_neq_of hseq2 ?_
  exact key s t ht _ (by simp) (by simp [hΔ2])

/-- **B92 Lemma 2.6**: `⊢* [a ≠ b], [L_γ ≠ a]` for `|b| < γ`. -/
theorem star_lem26 {γ : Ordinal.{1}} {a b : T} (hb : b.level < γ) {Δ : Set RSS}
    (h1 : Nq1 a b ∈ Δ) (h2 : Nq1 (T.L γ) a ∈ Δ) {σ : Ordinal.{1}} : Star R σ Δ :=
  Star.mono_sigma (star_lem26_aux γ a b hb Δ h1 h2) zero_le

end OrdinalAnalysis.KPi.RS
