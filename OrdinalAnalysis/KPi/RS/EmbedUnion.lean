module

public import OrdinalAnalysis.KPi.RS.EmbedRules
public import OrdinalAnalysis.KPi.RS.StarAxPU

/-!
# The RS calculus, part 34: the axiom (Union) of `KPi`, derived directly in `RS^∞` (smoke test)

`hinf_union` : `H ⊢^{ω^{ω·λ}+3}_0 (Union)^λ` for every nice operator `H` with `λ ∈ H`, `λ` a limit:
a cut-free `H`-controlled derivation of the `D0`-sentence `unionD (Bd.lev lam)` of B92's reading
(`∀x∈L_λ ∃z∈L_λ ∀y∈x ∀u∈y (u ∈ z)`), by `(⋀)` over `x`, `(⋁)` with `z = L_{|x|}`, `(⋀)` over `y, u`, and
`hmemL` (`u ∈ L_β` for `|u| < β`, from `hrefl`).  It exercises `ball_intro`, `bex_lev_intro`, `hleaf`,
`hrefl` and the `H`-membership bookkeeping, and shows that B92's Theorem 2.9 can be re-derived directly
in `RS^∞` (the route that avoids the retention gap of `Star`, see the notes).
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}}

theorem HInf.bump_ord {H : Op} (hH : NiceOp H) {Γ : Set RSS} {α α' ρ : Ordinal.{1}}
    (h : HInf R H Γ α ρ) (hle : α ≤ α') (hα' : α' ∈ H ∅) : HInf R H Γ α' ρ :=
  HInf.weaken_sub hH h subset_rfl hle hα' h.k_sub

/-- `∀x∈b A` for an arbitrary bound `b` with `resBd b ρ = a`; the continuation also receives the `k`-bound
of its sequent. -/
theorem HInf.ball_intro {H : Op} (hH : NiceOp H) {n : ℕ} (b : Bd n) {A : D0 (n + 1)}
    {ρ : Fin n → T} (a : T) (hb : resBd b ρ = a) {Δ : Set RSS} {α ρc : Ordinal.{1}}
    (hS : RSS.base (D0.ball b A) ρ ∈ Δ) (hk : kSeq Δ ⊆ H ∅) (hα : α ∈ H ∅)
    (h : ∀ t : T, t.level < a.level →
      kSeq (insert (RSS.base A (ext ρ t)) Δ) ⊆ Hext H t.k ∅ →
      HInf R (Hext H t.k) (insert (RSS.base A (ext ρ t)) Δ) α ρc) :
    HInf R H Δ (α + 3) ρc := by
  subst hb
  have hα3 : α + 3 ∈ H ∅ := by simpa using (hH.nice ∅).add_nat hα 3
  refine HInf.all' (A := RSS.base (D0.ball b A) ρ) hS hα3 hk rfl (fun _ => α + 2)
    (fun _ => addL_lt α (by norm_num)) ?_
  rintro ⟨t, ht⟩
  have hlt : t.level < (resBd b ρ).level := ht
  set Ht : Op := Hext H t.k with hHtdef
  have hHt : NiceOp Ht := hH.ext t.k
  have hkc := kSeq_child_sub (R := R) hH hS hk
    (⟨t, ht⟩ : (expand R (RSS.base (D0.ball b A) ρ)).J)
  have hchild : (expand R (RSS.base (D0.ball b A) ρ)).child ⟨t, ht⟩ =
      RSS.or (memInst t (resBd b ρ)).neg (RSS.base A (ext ρ t)) := rfl
  rw [hchild] at hkc ⊢
  have hkcc : (RSS.or (memInst t (resBd b ρ)).neg (RSS.base A (ext ρ t))).k ⊆ Ht ∅ :=
    (k_sub_kSeq (Set.mem_insert _ _)).trans hkc
  have hX : (memInst t (resBd b ρ)).neg.k ⊆ Ht ∅ := Set.subset_union_left.trans hkcc
  have hY : (RSS.base A (ext ρ t)).k ⊆ Ht ∅ := Set.subset_union_right.trans hkcc
  have hαt : α ∈ Ht ∅ := by
    rw [hHtdef, Hext_empty_apply]; exact hH.empty_sub _ hα
  have hΔt : kSeq Δ ⊆ Ht ∅ := by
    rw [hHtdef, Hext_empty_apply]; exact hk.trans (hH.empty_sub _)
  refine HInf.or_intro hHt (Set.mem_insert _ _) hkc ?_
  refine HInf.weaken_sub hHt (h t hlt (kSeq_insert_sub hY hΔt)) ?_ le_rfl hαt
    (kSeq_insert_sub hX (kSeq_insert_sub hY hkc))
  intro x hx
  rcases hx with rfl | hx
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx))

/-- `∃x∈L_λ A` from one witness (with the `k`-bound passed to the continuation). -/
theorem HInf.bex_lev_intro' {H : Op} (hH : NiceOp H) {lam : Ordinal.{1}} {n : ℕ} {A : D0 (n + 1)}
    {ρ : Fin n → T} {Δ : Set RSS} {α ρc : Ordinal.{1}}
    (hS : RSS.base (D0.bex (Bd.lev lam) A) ρ ∈ Δ) (hk : kSeq Δ ⊆ H ∅) (hα : α ∈ H ∅)
    (s : T) (hs : s.level < lam) (hsα : s.level < α) (hsk : s.k ⊆ H ∅)
    (h : kSeq (insert (RSS.base A (ext ρ s)) Δ) ⊆ H ∅ →
      HInf R H (insert (RSS.base A (ext ρ s)) Δ) α ρc) : HInf R H Δ (α + 2) ρc := by
  refine HInf.bex_lev_intro hH hS hk hα s hs hsα hsk (h ?_)
  set S : RSS := RSS.base (D0.bex (Bd.lev lam) A) ρ with hSdef
  set j : (expand R S).J := ⟨s, hs⟩ with hj
  have hchild : (expand R S).child j = RSS.and (memInst s (T.L lam)) (RSS.base A (ext ρ s)) := rfl
  have hkc : ((expand R S).child j).k ⊆ H ∅ := by
    refine (child_k_sub S j).trans ?_
    refine Set.union_subset (Set.union_subset (k_sub_kSeq hS |>.trans hk) hsk) ?_
    intro x hx; have : x = 0 := hx
    subst this; exact (hH.nice ∅).1
  rw [hchild] at hkc
  exact kSeq_insert_sub (Set.subset_union_right.trans hkc) hk

/-- `u ∈ L_β` for `|u| < β` (the atom `u ∈ z` with `z = L_β`). -/
theorem hmemL {H : Op} (hH : NiceOp H) {n : ℕ} (i j : Fin n) (ρ : Fin n → T) (u : T)
    (β : Ordinal.{1}) (hi : ρ i = u) (hj : ρ j = T.L β) (hu : u.level < β) (hku : u.k ⊆ H ∅)
    (hβH : β ∈ H ∅) {Δ : Set RSS} (hΔ : kSeq Δ ⊆ H ∅) {ρc : Ordinal.{1}} :
    HInf R H (insert (RSS.base (D0.mem i j) ρ) Δ) (ω ^ u.rk + 2 + 2) ρc := by
  set Y : RSS := RSS.base (D0.mem i j) ρ with hY
  have h0H : (0 : Ordinal.{1}) ∈ H ∅ := (hH.nice ∅).1
  have hβ : ω ^ u.rk + 2 ∈ H ∅ := by
    simpa using (hH.nice ∅).add_nat ((hH.nice ∅).opow_mem (T.form_mem hH hku)) 2
  have hβ2 : ω ^ u.rk + 2 + 2 ∈ H ∅ := by simpa using (hH.nice ∅).add_nat hβ 2
  have hYk : Y.k ⊆ H ∅ := by
    rw [hY, k_mem_base, hi, hj]
    refine Set.union_subset hku ?_
    intro x hx; have : x = β := hx
    subst this; exact hβH
  have hu' : u.level < (ρ j).level := by rw [hj]; exact hu
  set s : (expand R Y).J := ⟨u, hu'⟩ with hs
  have hchild : (expand R Y).child s = RSS.and (memInst u (T.L β)) (eqS u u) := by
    show RSS.and (memInst u (ρ j)) (eqS u (ρ i)) = _
    rw [hi, hj]
  set M := memInst u (T.L β) with hM
  set E := eqS u u with hE
  have hkM : M.k ⊆ H ∅ := by
    refine (k_memInst_sub u (T.L β)).trans ?_
    refine Set.union_subset (Set.union_subset ?_ hku) ?_
    · intro x hx; have : x = β := hx
      subst this; exact hβH
    · intro x hx; have : x = 0 := hx
      subst this; exact h0H
  have hkE : E.k ⊆ H ∅ := (k_eqS_sub u u).trans (Set.union_subset hku hku)
  set Δ' : Set RSS := insert Y Δ with hΔ'
  have hkΔ' : kSeq Δ' ⊆ H ∅ := kSeq_insert_sub hYk hΔ
  have hkAnd : (RSS.and M E).k ⊆ H ∅ := Set.union_subset hkM hkE
  set Δp : Set RSS := insert (RSS.and M E) Δ' with hΔp
  have hkΔp : kSeq Δp ⊆ H ∅ := kSeq_insert_sub hkAnd hkΔ'
  have hP1 : HInf R H (insert M Δp) (ω ^ u.rk + 2) ρc :=
    hleaf u β hβ (kSeq_insert_sub hkM hkΔp)
  have hP2 : HInf R H (insert E Δp) (ω ^ u.rk + 2) ρc := by
    refine HInf.weaken_sub' hH (hrefl u H hH hku) ?_ le_rfl hβ zero_le (kSeq_insert_sub hkE hkΔp)
    intro x hx
    have : x = E := hx
    subst this; exact Set.mem_insert _ _
  have hP3 : HInf R H Δp (ω ^ u.rk + 2 + 1) ρc :=
    HInf.and_intro hH (Set.mem_insert _ _) hkΔp hP1 hP2
  have h12 : ω ^ u.rk + 2 + 1 < ω ^ u.rk + 2 + 2 := addL_lt _ (by norm_num)
  have hlvl : (expand R Y).lvl s < ω ^ u.rk + 2 + 2 := by
    show u.level < _
    have h1 : u.level ≤ ω ^ u.rk := (T.level_le_rk u).trans (right_le_opow _ one_lt_omega0)
    have h2 : ω ^ u.rk < ω ^ u.rk + 2 := lt_add_of_pos_right _ (by norm_num)
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 le_self_add)
  exact HInf.ex1' (A := Y) (Set.mem_insert _ _) hβ2 hkΔ' s rfl h12 hlvl (by rw [hchild]; exact hP3)


/-! ### `Union` -/

theorem sub_ext {H : Op} (hH : NiceOp H) {S : Set Ordinal.{1}} (h : S ⊆ H ∅) (K : Set Ordinal.{1}) :
    S ⊆ Hext H K ∅ := by
  rw [Hext_empty_apply]; exact h.trans (hH.empty_sub K)

theorem self_sub_ext {H : Op} (hH : NiceOp H) (K : Set Ordinal.{1}) : K ⊆ Hext H K ∅ := by
  rw [Hext_empty_apply]; exact hH.sub K

theorem T.rk_lt_omega_mul {lam : Ordinal.{1}} {x : T} (hx : x.level < lam) (n : ℕ) :
    x.rk + n < ω * lam := by
  have h1 : x.rk + n < ω * (x.level + 1) := lt_omega_mul_of_lt (T.rk_lt x) n
  exact lt_of_lt_of_le h1 (mul_le_mul_right (Order.add_one_le_of_lt hx) ω)

theorem opow_rk_mem {H : Op} (hH : NiceOp H) {t : T} (ht : t.k ⊆ H ∅) : ω ^ t.rk ∈ H ∅ :=
  (hH.nice ∅).opow_mem (T.form_mem hH ht)

theorem opow_rk_add_mem {H : Op} (hH : NiceOp H) {t : T} (ht : t.k ⊆ H ∅) (n : ℕ) :
    ω ^ t.rk + n ∈ H ∅ :=
  (hH.nice ∅).add_nat (opow_rk_mem hH ht) n

theorem hinf_union {H : Op} (hH : NiceOp H) {lam : Ordinal.{1}} (hlamH : lam ∈ H ∅) :
    HInf R H {RSS.base (unionD (Bd.lev lam)) Fin.elim0} (ω ^ (ω * lam) + 3) 0 := by
  set S0 : RSS := RSS.base (unionD (Bd.lev lam)) Fin.elim0 with hS0
  have hk0 : kSeq ({S0} : Set RSS) ⊆ H ∅ := by
    rw [kSeq_singleton]
    intro ξ hξ
    have hξ' : ξ ∈ kD (unionD (Bd.lev lam)) (fun i => (Fin.elim0 i : T).k) := hξ
    simp [unionD, kD, kBd, Bd.shift, ext, Fin.snoc] at hξ'
    rw [hξ']; exact hlamH
  have hαroot : ω ^ (ω * lam) ∈ H ∅ := (hH.nice ∅).opow_mem ((hH.nice ∅).omega_mul hlamH)
  refine HInf.ball_intro hH (Bd.lev lam) (T.L lam) rfl (Set.mem_singleton S0) hk0 hαroot ?_
  intro x hx hkx
  have hx' : x.level < lam := hx
  set Hx : Op := Hext H x.k with hHx_def
  have hHx : NiceOp Hx := hH.ext x.k
  have hxk : x.k ⊆ Hx ∅ := self_sub_ext hH x.k
  have hxlev : x.level ∈ Hx ∅ := hxk (PT.level_mem_k x.1)
  have hrootx : ω ^ (ω * lam) ∈ Hx ∅ := sub_ext hH (Set.singleton_subset_iff.2 hαroot) x.k rfl
  have hα3 : ω ^ x.rk + 3 ∈ Hx ∅ := by simpa using opow_rk_add_mem hHx hxk 3
  have hsα : (T.L x.level).level < ω ^ x.rk + 3 := by
    show x.level < _
    have h1 : x.level ≤ ω ^ x.rk := (T.level_le_rk x).trans (right_le_opow _ one_lt_omega0)
    exact lt_of_le_of_lt h1 (lt_add_of_pos_right _ (by norm_num))
  have hsk : (T.L x.level).k ⊆ Hx ∅ := by
    intro ξ hξ
    have : ξ = x.level := hξ
    rw [this]; exact hxlev
  have hxrk : x.rk + 5 < ω * lam := T.rk_lt_omega_mul hx' 5
  have hle : ω ^ x.rk + 3 + 2 ≤ ω ^ (ω * lam) := by
    have := opow_add_nat_lt (lt_of_le_of_lt le_self_add hxrk) 5
    have e : ω ^ x.rk + 3 + 2 = ω ^ x.rk + ((5 : ℕ) : Ordinal.{1}) := by
      push_cast; rw [add_assoc]; norm_num
    rw [e]; exact this.le
  refine HInf.bump_ord hHx (α := ω ^ x.rk + 3 + 2) ?_ hle hrootx
  refine HInf.bex_lev_intro' hHx (Set.mem_insert _ _) hkx hα3 (T.L x.level) hx' hsα hsk
    (fun hk2 => ?_)
  -- the bounded universal quantifier over `y ∈ x`
  refine HInf.ball_intro hHx (Bd.var (Fin.castSucc (Fin.last 0))) x (by simp [resBd])
    (Set.mem_insert _ _) hk2 (opow_rk_mem hHx hxk) (fun y hy hky => ?_)
  set Hy : Op := Hext Hx y.k with hHy_def
  have hHy : NiceOp Hy := hHx.ext y.k
  have hyk : y.k ⊆ Hy ∅ := self_sub_ext hHx y.k
  have hxky : x.k ⊆ Hy ∅ := sub_ext hHx hxk y.k
  have hxlevy : x.level ∈ Hy ∅ := hxky (PT.level_mem_k x.1)
  have hroot2 : ω ^ x.rk ∈ Hy ∅ := opow_rk_mem hHy hxky
  have hyx : y.rk + 3 < x.rk := lt_of_le_of_lt (by simp) (T.rk_add_lt hy 3)
  refine HInf.bump_ord hHy (α := ω ^ y.rk + 3) ?_ (opow_add_nat_lt (lt_of_le_of_lt le_self_add hyx) 3).le hroot2
  -- the bounded universal quantifier over `u ∈ y`
  refine HInf.ball_intro hHy (Bd.var (Fin.last 2)) y (by exact ext_last _ _) (Set.mem_insert _ _) hky
    (opow_rk_mem hHy hyk) (fun u hu hku => ?_)
  set Hu : Op := Hext Hy u.k with hHu_def
  have hHu : NiceOp Hu := hHy.ext u.k
  have huk : u.k ⊆ Hu ∅ := self_sub_ext hHy u.k
  have hxlevu : x.level ∈ Hu ∅ := sub_ext hHy (Set.singleton_subset_iff.2 hxlevy) u.k rfl
  have hyu : u.rk + 4 < y.rk := lt_of_le_of_lt (by simp) (T.rk_add_lt hu 4)
  have hroot3 : ω ^ y.rk ∈ Hu ∅ := opow_rk_mem hHu (sub_ext hHy hyk u.k)
  refine HInf.bump_ord hHu (α := ω ^ u.rk + 2 + 2) ?_ ?_ hroot3
  · exact hmemL hHu (Fin.last 3) (Fin.castSucc (Fin.castSucc (Fin.last 1))) _ u x.level
      (by exact ext_last _ _) (by rw [ext_castSucc, ext_castSucc, ext_last]) (lt_trans hu hy) huk hxlevu
      ((kSeq_mono (Set.subset_insert _ _)).trans hku)
  · have := opow_add_nat_lt (lt_of_le_of_lt le_self_add hyu) 4
    have e : ω ^ u.rk + 2 + 2 = ω ^ u.rk + ((4 : ℕ) : Ordinal.{1}) := by
      push_cast; rw [add_assoc]; norm_num
    rw [e]; exact this.le

end OrdinalAnalysis.KPi.RS
