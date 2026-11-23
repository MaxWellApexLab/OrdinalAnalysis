module

public import OrdinalAnalysis.KPi.RS.HSim

/-!
# The RS calculus, part 32: introduction rules for the sentences of the translation

For sentences `RSS.base (D0.and A B) ρ`, `RSS.base (D0.or A B) ρ`, `∀x∈L_λ A`, `∃x∈L_λ A`:

* `HInf.mono_op`        : `HInf` is monotone in the operator;
* `hleaf`               : `t ∈° L_β` (that is `t ∉ L_0`) is derivable outright;
* `HInf.band_intro` (`+1`), `HInf.bor_intro` (`+2`);
* `HInf.ball_lev_intro` : from `A(t)` for all `t ∈ 𝒯_λ` (each `H[t]`-controlled) to `∀x∈L_λ A(x)` (`+3`);
* `HInf.bex_lev_intro`  : from `A(s)` for one `s ∈ 𝒯_λ` to `∃x∈L_λ A(x)` (`+2`).
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}}

theorem HInf.mono_op {H : Op} {Γ : Set RSS} {α ρ : Ordinal.{1}} (h : HInf R H Γ α ρ) :
    ∀ {H' : Op}, (∀ X, H X ⊆ H' X) → HInf R H' Γ α ρ := by
  induction h with
  | @all H Γ A α ρ hα hk hA α₀ h0 h ih =>
    intro H' hle
    exact HInf.all (hle ∅ hα) (hk.trans (hle ∅)) hA α₀ h0
      (fun j => ih j (H' := Hext H' ((expand R A).ks j)) (fun X => hle _))
  | @ex H Γ A α ρ α₀ hα hk j hA h0 hl h ih =>
    intro H' hle
    exact HInf.ex (hle ∅ hα) (hk.trans (hle ∅)) j hA h0 hl (ih hle)
  | @cut H Γ C α ρ α₀ hα hk hC h0 h1 h2 ih1 ih2 =>
    intro H' hle
    exact HInf.cut (hle ∅ hα) (hk.trans (hle ∅)) hC h0 (ih1 hle) (ih2 hle)
  | @ref H Γ α ρ α₀ κ S hκ X hX hα hk h0 h ih =>
    intro H' hle
    exact HInf.ref S hκ hX (hle ∅ hα) (hk.trans (hle ∅)) h0 (ih hle)

theorem HInf.weaken_sub' {H : Op} (hH : NiceOp H) {Γ Δ : Set RSS} {α α' ρ ρ' : Ordinal.{1}}
    (h : HInf R H Γ α ρ) (hsub : Γ ⊆ Δ) (hαα : α ≤ α') (hα' : α' ∈ H ∅) (hρ : ρ ≤ ρ')
    (hk : kSeq Δ ⊆ H ∅) : HInf R H Δ α' ρ' := by
  have := h.weaken hH (Γ' := Δ) hαα hα' hρ hk
  rwa [Set.union_eq_right.2 hsub] at this

theorem hleaf {H : Op} (s : T) (β : Ordinal.{1}) {Δ : Set RSS} {α ρc : Ordinal.{1}}
    (hα : α ∈ H ∅) (hk : kSeq (insert (memInst s (T.L β)) Δ) ⊆ H ∅) :
    HInf R H (insert (memInst s (T.L β)) Δ) α ρc := by
  refine HInf.all (Γ := Δ) (A := memInst s (T.L β)) hα hk rfl (fun j => ?_) (fun j => ?_)
    (fun j => ?_)
  all_goals exact absurd j.2 (by simp [T.level, T.L, PT.level])

theorem HInf.band_intro {H : Op} {n : ℕ} {A B : D0 n} {ρ : Fin n → T} {Δ : Set RSS}
    {α ρc : Ordinal.{1}} (hH : NiceOp H) (hAΔ : RSS.base (D0.and A B) ρ ∈ Δ)
    (hk : kSeq Δ ⊆ H ∅) (hA : HInf R H (insert (RSS.base A ρ) Δ) α ρc)
    (hB : HInf R H (insert (RSS.base B ρ) Δ) α ρc) : HInf R H Δ (α + 1) ρc := by
  have hα : α + 1 ∈ H ∅ := by simpa using (hH.nice ∅).add_nat hA.alpha_mem 1
  refine HInf.all' (A := RSS.base (D0.and A B) ρ) hAΔ hα hk rfl (fun _ => α)
    (fun _ => lt_add_one α) ?_
  intro j
  rw [show (expand R (RSS.base (D0.and A B) ρ)).ks j = ∅ from rfl, Hext_empty]
  rcases j with ⟨b⟩
  cases b
  · exact hB
  · exact hA

theorem HInf.bor_intro {H : Op} {n : ℕ} {A B : D0 n} {ρ : Fin n → T} {Δ : Set RSS}
    {α ρc : Ordinal.{1}} (hH : NiceOp H) (hAΔ : RSS.base (D0.or A B) ρ ∈ Δ)
    (hk : kSeq Δ ⊆ H ∅)
    (h : HInf R H (insert (RSS.base A ρ) (insert (RSS.base B ρ) Δ)) α ρc) :
    HInf R H Δ (α + 2) ρc := by
  have hα1 : α + 1 ∈ H ∅ := by simpa using (hH.nice ∅).add_nat h.alpha_mem 1
  have hα2 : α + 2 ∈ H ∅ := by simpa using (hH.nice ∅).add_nat h.alpha_mem 2
  have hmem : RSS.base (D0.or A B) ρ ∈ insert (RSS.base B ρ) Δ := Set.mem_insert_of_mem _ hAΔ
  have hpos1 : (0 : Ordinal.{1}) < α + 1 := lt_of_le_of_lt zero_le (lt_add_one α)
  have hlt12 : α + 1 < α + 2 := addL_lt α (by norm_num)
  have hpos2 : (0 : Ordinal.{1}) < α + 2 := lt_trans hpos1 hlt12
  have hk1 : kSeq (insert (RSS.base B ρ) Δ) ⊆ H ∅ :=
    (kSeq_mono (Set.subset_insert _ _)).trans h.k_sub
  have h1 : HInf R H (insert (RSS.base B ρ) Δ) (α + 1) ρc :=
    HInf.ex1' (A := RSS.base (D0.or A B) ρ) hmem hα1 hk1
      (⟨true⟩ : (expand R (RSS.base (D0.or A B) ρ)).J) rfl (lt_add_one α) hpos1 h
  exact HInf.ex1' (A := RSS.base (D0.or A B) ρ) hAΔ hα2 hk
    (⟨false⟩ : (expand R (RSS.base (D0.or A B) ρ)).J) rfl hlt12 hpos2 h1

theorem HInf.ball_lev_intro {H : Op} (hH : NiceOp H) {lam : Ordinal.{1}} {n : ℕ} {A : D0 (n + 1)}
    {ρ : Fin n → T} {Δ : Set RSS} {α ρc : Ordinal.{1}}
    (hS : RSS.base (D0.ball (Bd.lev lam) A) ρ ∈ Δ) (hk : kSeq Δ ⊆ H ∅) (hα : α ∈ H ∅)
    (h : ∀ t : T, t.level < lam →
      HInf R (Hext H t.k) (insert (RSS.base A (ext ρ t)) Δ) α ρc) :
    HInf R H Δ (α + 3) ρc := by
  have hα3 : α + 3 ∈ H ∅ := by simpa using (hH.nice ∅).add_nat hα 3
  refine HInf.all' (A := RSS.base (D0.ball (Bd.lev lam) A) ρ) hS hα3 hk rfl (fun _ => α + 2)
    (fun _ => addL_lt α (by norm_num)) ?_
  rintro ⟨t, ht⟩
  set Ht : Op := Hext H t.k with hHtdef
  have hHt : NiceOp Ht := hH.ext t.k
  have hkc := kSeq_child_sub (R := R) hH hS hk (⟨t, ht⟩ : (expand R (RSS.base (D0.ball (Bd.lev lam) A) ρ)).J)
  have hchild : (expand R (RSS.base (D0.ball (Bd.lev lam) A) ρ)).child ⟨t, ht⟩ =
      RSS.or (memInst t (T.L lam)).neg (RSS.base A (ext ρ t)) := rfl
  rw [hchild] at hkc ⊢
  have hkcc : (RSS.or (memInst t (T.L lam)).neg (RSS.base A (ext ρ t))).k ⊆ Ht ∅ :=
    (k_sub_kSeq (Set.mem_insert _ _)).trans hkc
  have hX : (memInst t (T.L lam)).neg.k ⊆ Ht ∅ := Set.subset_union_left.trans hkcc
  have hY : (RSS.base A (ext ρ t)).k ⊆ Ht ∅ := Set.subset_union_right.trans hkcc
  have hαt : α ∈ Ht ∅ := by
    rw [hHtdef, Hext_empty_apply]; exact hH.empty_sub _ hα
  refine HInf.or_intro hHt (Set.mem_insert _ _) hkc ?_
  refine HInf.weaken_sub hHt (h t ht) ?_ le_rfl hαt
    (kSeq_insert_sub hX (kSeq_insert_sub hY hkc))
  intro x hx
  rcases hx with rfl | hx
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx))

theorem HInf.bex_lev_intro {H : Op} (hH : NiceOp H) {lam : Ordinal.{1}} {n : ℕ} {A : D0 (n + 1)}
    {ρ : Fin n → T} {Δ : Set RSS} {α ρc : Ordinal.{1}}
    (hS : RSS.base (D0.bex (Bd.lev lam) A) ρ ∈ Δ) (hk : kSeq Δ ⊆ H ∅) (hα : α ∈ H ∅)
    (s : T) (hs : s.level < lam) (hsα : s.level < α) (hsk : s.k ⊆ H ∅)
    (h : HInf R H (insert (RSS.base A (ext ρ s)) Δ) α ρc) : HInf R H Δ (α + 2) ρc := by
  have hα1 : α + 1 ∈ H ∅ := by simpa using (hH.nice ∅).add_nat hα 1
  have hα2 : α + 2 ∈ H ∅ := by simpa using (hH.nice ∅).add_nat hα 2
  set S : RSS := RSS.base (D0.bex (Bd.lev lam) A) ρ with hSdef
  set j : (expand R S).J := ⟨s, hs⟩ with hj
  have hchild : (expand R S).child j = RSS.and (memInst s (T.L lam)) (RSS.base A (ext ρ s)) := rfl
  have hkc : kSeq (insert ((expand R S).child j) Δ) ⊆ H ∅ := by
    refine kSeq_insert_sub ?_ hk
    refine (child_k_sub S j).trans ?_
    refine Set.union_subset (Set.union_subset (k_sub_kSeq hS |>.trans hk) hsk) ?_
    intro x hx; have : x = 0 := hx
    subst this; exact (hH.nice ∅).1
  rw [hchild] at hkc
  have hM : (memInst s (T.L lam)).k ⊆ H ∅ :=
    Set.subset_union_left.trans ((k_sub_kSeq (Set.mem_insert _ _)).trans hkc)
  have hY : (RSS.base A (ext ρ s)).k ⊆ H ∅ :=
    Set.subset_union_right.trans ((k_sub_kSeq (Set.mem_insert _ _)).trans hkc)
  have hP : HInf R H (insert (RSS.base A (ext ρ s)) (insert (RSS.and (memInst s (T.L lam))
      (RSS.base A (ext ρ s))) Δ)) α ρc := by
    refine HInf.weaken_sub hH h ?_ le_rfl hα (kSeq_insert_sub hY hkc)
    intro x hx
    rcases hx with rfl | hx
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx)
  have hL : HInf R H (insert (memInst s (T.L lam)) (insert (RSS.and (memInst s (T.L lam))
      (RSS.base A (ext ρ s))) Δ)) α ρc := hleaf s lam hα (kSeq_insert_sub hM hkc)
  have hAnd : HInf R H (insert (RSS.and (memInst s (T.L lam)) (RSS.base A (ext ρ s))) Δ) (α + 1) ρc :=
    HInf.and_intro hH (Set.mem_insert _ _) hkc hL hP
  have h12 : α + 1 < α + 2 := addL_lt α (by norm_num)
  have hlvl : (expand R S).lvl j < α + 2 := lt_trans hsα (lt_trans (lt_add_one α) h12)
  refine HInf.ex1' (A := S) hS hα2 hk j rfl h12 hlvl ?_
  rw [hchild]
  exact hAnd

end OrdinalAnalysis.KPi.RS
