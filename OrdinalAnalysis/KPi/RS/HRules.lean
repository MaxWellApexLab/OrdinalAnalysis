module

public import OrdinalAnalysis.KPi.RS.HChild

/-!
# The RS calculus, part 28: derived rules of `HInf` and the excluded middle (B92 Lemma 2.4 in `RS^∞`)

* `Hext_empty`                  : `H[∅] = H`;
* `HInf.all'`, `HInf.ex1'`      : the rules with an ambient sequent;
* `HInf.and_intro`, `HInf.or_intro` : introduction of `A ∧ B` and `A ∨ B` (`or_intro` costs `+2`);
* `opow_add_nat_lt`             : `x < y ⇒ ω^x + n < ω^y`;
* `htnd`                        : **`H ⊢^{ω^{rk A}}_0 ¬A, A`** for every RS-sentence `A` with `k(A) ⊆ H`.
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}}

theorem Hext_empty (H : Op) : Hext H ∅ = H := by
  funext X
  simp [Hext]

theorem opow_add_nat_lt {x y : Ordinal.{1}} (h : x < y) (n : ℕ) : ω ^ x + n < ω ^ y := by
  refine isPrincipal_add_omega0_opow y ((opow_lt_opow_iff_right one_lt_omega0).2 h) ?_
  have hy : 1 ≤ y := by
    rcases eq_zero_or_pos y with rfl | hy
    · exact absurd h (not_lt.2 zero_le)
    · exact Order.one_le_iff_pos.2 hy
  exact lt_of_lt_of_le (natCast_lt_omega0 n)
    (by simpa using (opow_le_opow_right omega0_pos hy))

/-! ### rules with an ambient sequent -/

theorem HInf.all' {H : Op} {Δ : Set RSS} {A : RSS} {α ρ : Ordinal.{1}} (hAΔ : A ∈ Δ)
    (hα : α ∈ H ∅) (hk : kSeq Δ ⊆ H ∅) (hA : (expand R A).isOr = false)
    (α₀ : (expand R A).J → Ordinal.{1}) (h0 : ∀ j, α₀ j < α)
    (h : ∀ j : (expand R A).J,
      HInf R (Hext H ((expand R A).ks j)) (insert ((expand R A).child j) Δ) (α₀ j) ρ) :
    HInf R H Δ α ρ := by
  have := HInf.all (Γ := Δ) hα (by rwa [Set.insert_eq_of_mem hAΔ]) hA α₀ h0 h
  rwa [Set.insert_eq_of_mem hAΔ] at this

theorem HInf.ex1' {H : Op} {Δ : Set RSS} {A : RSS} {α ρ α₀ : Ordinal.{1}} (hAΔ : A ∈ Δ)
    (hα : α ∈ H ∅) (hk : kSeq Δ ⊆ H ∅) (j : (expand R A).J) (hA : (expand R A).isOr = true)
    (h0 : α₀ < α) (hl : (expand R A).lvl j < α)
    (h : HInf R H (insert ((expand R A).child j) Δ) α₀ ρ) : HInf R H Δ α ρ := by
  have := HInf.ex (Γ := Δ) hα (by rwa [Set.insert_eq_of_mem hAΔ]) j hA h0 hl h
  rwa [Set.insert_eq_of_mem hAΔ] at this

theorem HInf.and_intro {H : Op} (hH : NiceOp H) {Δ : Set RSS} {X Y : RSS} {α ρ : Ordinal.{1}}
    (hAΔ : RSS.and X Y ∈ Δ) (hk : kSeq Δ ⊆ H ∅)
    (hX : HInf R H (insert X Δ) α ρ) (hY : HInf R H (insert Y Δ) α ρ) :
    HInf R H Δ (α + 1) ρ := by
  have hα : α + 1 ∈ H ∅ := by simpa using (hH.nice ∅).add_nat hX.alpha_mem 1
  refine HInf.all' (A := RSS.and X Y) hAΔ hα hk rfl (fun _ => α) (fun _ => lt_add_one α) ?_
  intro j
  rw [show (expand R (RSS.and X Y)).ks j = ∅ from rfl, Hext_empty]
  rcases j with ⟨b⟩
  cases b
  · exact hY
  · exact hX

theorem HInf.or_intro {H : Op} (hH : NiceOp H) {Δ : Set RSS} {X Y : RSS} {α ρ : Ordinal.{1}}
    (hAΔ : RSS.or X Y ∈ Δ) (hk : kSeq Δ ⊆ H ∅)
    (h : HInf R H (insert X (insert Y Δ)) α ρ) : HInf R H Δ (α + 2) ρ := by
  have hα1 : α + 1 ∈ H ∅ := by simpa using (hH.nice ∅).add_nat h.alpha_mem 1
  have hα2 : α + 2 ∈ H ∅ := by simpa using (hH.nice ∅).add_nat h.alpha_mem 2
  have hmem : RSS.or X Y ∈ insert Y Δ := Set.mem_insert_of_mem _ hAΔ
  have hpos1 : (0 : Ordinal.{1}) < α + 1 := lt_of_le_of_lt zero_le (lt_add_one α)
  have hlt12 : α + 1 < α + 2 := addL_lt α (by norm_num)
  have hpos2 : (0 : Ordinal.{1}) < α + 2 := lt_trans hpos1 hlt12
  have hk1 : kSeq (insert Y Δ) ⊆ H ∅ :=
    (kSeq_mono (Set.subset_insert _ _)).trans h.k_sub
  have h1 : HInf R H (insert Y Δ) (α + 1) ρ :=
    HInf.ex1' (A := RSS.or X Y) hmem hα1 hk1 (⟨true⟩ : (expand R (RSS.or X Y)).J) rfl
      (lt_add_one α) hpos1 h
  exact HInf.ex1' (A := RSS.or X Y) hAΔ hα2 hk (⟨false⟩ : (expand R (RSS.or X Y)).J) rfl
    hlt12 hpos2 h1


/-! ### (TND) in `RS^∞` -/

theorem kSeq_singleton (A : RSS) : kSeq ({A} : Set RSS) = A.k := by
  ext ξ
  simp [kSeq]

theorem kSeq_pair_neg (A : RSS) : kSeq ({A.neg, A} : Set RSS) = A.k := by
  rw [Set.pair_comm]
  rw [show ({A, A.neg} : Set RSS) = insert A {A.neg} from rfl, kSeq_insert, kSeq_singleton, RSS.k_neg]
  simp

theorem htnd_and (A : RSS) (hA : (expand R A).isOr = false)
    (ih : ∀ (j : (expand R A).J) (H' : Op), NiceOp H' → ((expand R A).child j).k ⊆ H' ∅ →
      HInf R H' {((expand R A).child j).neg, (expand R A).child j}
        (ω ^ ((expand R A).child j).rk) 0) :
    ∀ H : Op, NiceOp H → A.k ⊆ H ∅ → HInf R H {A.neg, A} (ω ^ A.rk) 0 := by
  intro H hH hk
  have hkA : kSeq ({A.neg, A} : Set RSS) ⊆ H ∅ := by rw [kSeq_pair_neg]; exact hk
  have hα : ω ^ A.rk ∈ H ∅ := (hH.nice ∅).opow_mem (hH.rk_mem hk)
  refine HInf.all' (A := A) (by simp) hα hkA hA (fun j => ω ^ ((expand R A).child j).rk + 1)
    (fun j => ?_) (fun j => ?_)
  · simpa using opow_add_nat_lt (child_rk_lt R A j) 1
  · set K := (expand R A).ks j with hK
    have hHj : NiceOp (Hext H K) := hH.ext K
    have hAj : A.k ⊆ Hext H K ∅ := by
      rw [Hext_empty_apply]; exact hk.trans (hH.empty_sub K)
    have hKj : K ⊆ Hext H K ∅ := by
      rw [Hext_empty_apply]; exact hH.sub K
    have hch : ((expand R A).child j).k ⊆ Hext H K ∅ := by
      refine (child_k_sub A j).trans ?_
      refine Set.union_subset (Set.union_subset hAj hKj) ?_
      intro x hx
      have : x = 0 := hx
      subst this
      exact (hHj.nice ∅).1
    have hαj : ω ^ ((expand R A).child j).rk ∈ Hext H K ∅ :=
      (hHj.nice ∅).opow_mem (hHj.rk_mem hch)
    have hαj1 : ω ^ ((expand R A).child j).rk + 1 ∈ Hext H K ∅ := by
      simpa using (hHj.nice ∅).add_nat hαj 1
    obtain ⟨j', hc, hks⟩ := expand_neg_child (R := R) A j
    have hB : (expand R A.neg).isOr = true := by rw [expand_neg_isOr, hA]; rfl
    have hkΔ : kSeq (insert ((expand R A).child j) ({A.neg, A} : Set RSS)) ⊆ Hext H K ∅ := by
      rw [kSeq_insert, kSeq_pair_neg]
      exact Set.union_subset hch hAj
    refine HInf.ex1' (A := A.neg) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hαj1 hkΔ j' hB
      (lt_add_one _) ?_ ?_
    · have h1 := lvl_le_rk (R := R) A.neg j'
      rw [hc, RSS.rk_neg] at h1
      exact lt_of_le_of_lt (h1.trans (right_le_opow _ one_lt_omega0)) (lt_add_one _)
    · rw [hc]
      have h2 := HInf.weaken (ih j (Hext H K) hHj hch) hHj (Γ' := {A.neg, A}) (α' := _) le_rfl hαj
        le_rfl (by rw [kSeq_pair_neg]; exact hAj)
      convert h2 using 1
      ext x
      simp
      tauto

theorem htnd (A : RSS) : ∀ H : Op, NiceOp H → A.k ⊆ H ∅ → HInf R H {A.neg, A} (ω ^ A.rk) 0 := by
  refine rk_ind (P := fun A => ∀ H : Op, NiceOp H → A.k ⊆ H ∅ →
    HInf R H {A.neg, A} (ω ^ A.rk) 0) (fun A ih => ?_) A
  by_cases hA : (expand R A).isOr = true
  · have hB : (expand R A.neg).isOr = false := by rw [expand_neg_isOr, hA]; rfl
    have := htnd_and (R := R) A.neg hB (fun j H' hH' hk' => by
      refine ih _ ?_ H' hH' hk'
      have := child_rk_lt R A.neg j
      rwa [RSS.rk_neg] at this)
    intro H hH hk
    have h2 := this H hH (by rwa [RSS.k_neg])
    rw [RSS.neg_neg, RSS.rk_neg, Set.pair_comm] at h2
    exact h2
  · have hA' : (expand R A).isOr = false := by simpa using hA
    exact htnd_and A hA' (fun j H' hH' hk' => ih _ (child_rk_lt R A j) H' hH' hk')


/-! ### small helpers -/

theorem kSeq_insert_sub {S : Set Ordinal.{1}} {A : RSS} {Γ : Set RSS} (hA : A.k ⊆ S)
    (hΓ : kSeq Γ ⊆ S) : kSeq (insert A Γ) ⊆ S := by
  rw [kSeq_insert]; exact Set.union_subset hA hΓ

/-- weakening to a larger sequent. -/
theorem HInf.weaken_sub {H : Op} (hH : NiceOp H) {Γ Δ : Set RSS} {α α' ρ : Ordinal.{1}}
    (h : HInf R H Γ α ρ) (hsub : Γ ⊆ Δ) (hαα : α ≤ α') (hα' : α' ∈ H ∅) (hk : kSeq Δ ⊆ H ∅) :
    HInf R H Δ α' ρ := by
  have := h.weaken hH (Γ' := Δ) hαα hα' le_rfl hk
  rwa [Set.union_eq_right.2 hsub] at this

theorem T.level_le_rk (t : T) : t.level ≤ t.rk :=
  (Ordinal.le_mul_right _ omega0_pos).trans (T.K t)

theorem T.form_mem {H : Op} (hH : NiceOp H) {X : Set Ordinal.{1}} {t : T} (hk : t.k ⊆ H X) :
    t.rk ∈ H X :=
  Form.mem_of_nice (hH.nice X) hk (T.form t)

theorem k_mem_base {n : ℕ} (i j : Fin n) (ρ : Fin n → T) :
    (RSS.base (D0.mem i j) ρ).k = (ρ i).k ∪ (ρ j).k := rfl

/-! ### `b ∈ a, b ∉° a` (B92 Lemma 2.5 c) -/

/-- the length of the derivation of `b ∈ a, b ∉° a`. -/
noncomputable def memOrd (t a : T) : Ordinal.{1} :=
  max (ω ^ (memInst t a).rk) (ω ^ t.rk + 2) + 2

theorem hmem_core {H : Op} (hH : NiceOp H) {n : ℕ} (i j : Fin n) (ρ : Fin n → T) (t a : T)
    (hi : ρ i = t) (hj : ρ j = a) (hlt : t.level < a.level)
    (hkt : t.k ⊆ H ∅) (hka : a.k ⊆ H ∅) (hrt : HInf R H {eqS t t} (ω ^ t.rk + 2) 0)
    {Δ : Set RSS} (hΔ : kSeq Δ ⊆ H ∅) :
    HInf R H (insert (RSS.base (D0.mem i j) ρ) (insert (memInst t a).neg Δ)) (memOrd t a) 0 := by
  subst hi hj
  set t := ρ i with ht
  set a := ρ j with ha
  set M := memInst t a with hM
  set E := eqS t t with hE
  set Y : RSS := RSS.base (D0.mem i j) ρ with hY
  have h0H : (0 : Ordinal.{1}) ∈ H ∅ := (hH.nice ∅).1
  have hkM : M.k ⊆ H ∅ := by
    refine (k_memInst_sub t a).trans ?_
    refine Set.union_subset (Set.union_subset hka hkt) ?_
    intro x hx; have : x = 0 := hx
    subst this; exact h0H
  have hkE : E.k ⊆ H ∅ := (k_eqS_sub t t).trans (Set.union_subset hkt hkt)
  have hkY : Y.k ⊆ H ∅ := by
    rw [hY, k_mem_base]; exact Set.union_subset hkt hka
  have hkMn : M.neg.k ⊆ H ∅ := by rw [RSS.k_neg]; exact hkM
  set γ : Ordinal.{1} := max (ω ^ M.rk) (ω ^ t.rk + 2) with hγ
  have hγH : γ ∈ H ∅ := by
    rcases max_choice (ω ^ M.rk) (ω ^ t.rk + 2) with h | h
    · rw [hγ, h]; exact (hH.nice ∅).opow_mem (hH.rk_mem hkM)
    · rw [hγ, h]; exact hrt.alpha_mem
  have hγ2 : γ + 2 ∈ H ∅ := by simpa using (hH.nice ∅).add_nat hγH 2
  have hγ1 : γ + 1 ∈ H ∅ := by simpa using (hH.nice ∅).add_nat hγH 1
  -- the sequents
  set Δ' : Set RSS := insert Y (insert M.neg Δ) with hΔ'
  set s : (expand R Y).J := ⟨t, hlt⟩ with hs
  have hchild : (expand R Y).child s = RSS.and M E := rfl
  set Δp : Set RSS := insert (RSS.and M E) Δ' with hΔp
  have hkΔ' : kSeq Δ' ⊆ H ∅ :=
    kSeq_insert_sub hkY (kSeq_insert_sub hkMn hΔ)
  have hkAnd : (RSS.and M E).k ⊆ H ∅ := Set.union_subset hkM hkE
  have hkΔp : kSeq Δp ⊆ H ∅ := kSeq_insert_sub hkAnd hkΔ'
  have hMn_mem : M.neg ∈ Δp := Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hP1 : HInf R H (insert M Δp) γ 0 := by
    refine HInf.weaken_sub hH (htnd M H hH hkM) ?_ (le_max_left _ _) hγH
      (kSeq_insert_sub hkM hkΔp)
    intro x hx
    rcases hx with rfl | rfl
    · exact Set.mem_insert_of_mem _ hMn_mem
    · exact Set.mem_insert _ _
  have hP2 : HInf R H (insert E Δp) γ 0 := by
    refine HInf.weaken_sub hH hrt ?_ (le_max_right _ _) hγH (kSeq_insert_sub hkE hkΔp)
    intro x hx
    have : x = E := hx
    subst this; exact Set.mem_insert _ _
  have hP3 : HInf R H Δp (γ + 1) 0 :=
    HInf.and_intro hH (Set.mem_insert _ _) hkΔp hP1 hP2
  have hlvl : (expand R Y).lvl s < γ + 2 := by
    show t.level < γ + 2
    refine lt_of_le_of_lt ?_ (lt_add_of_pos_right _ (by norm_num))
    refine (T.level_le_rk t).trans ?_
    refine (right_le_opow _ one_lt_omega0).trans ?_
    exact (le_self_add).trans (le_max_right _ _)
  have hmo : memOrd t a = γ + 2 := rfl
  rw [hmo]
  exact HInf.ex1' (A := Y) (Set.mem_insert _ _) hγ2 hkΔ' s rfl (addL_lt γ (by norm_num)) hlvl hP3


/-! ### reflexivity `a = a` -/

theorem memOrd_lt {t a : T} (h : t.level < a.level) : memOrd t a + 2 < ω ^ a.rk := by
  have h1 : (memInst t a).rk < a.rk := lt_of_le_of_lt le_self_add (rk_memInst_lt h)
  have h2 : t.rk < a.rk := lt_of_le_of_lt (by simp) (T.rk_add_lt h 0)
  unfold memOrd
  rcases max_choice (ω ^ (memInst t a).rk) (ω ^ t.rk + 2) with e | e
  · rw [e]
    have := opow_add_nat_lt h1 4
    have e : (2 : Ordinal.{1}) + 2 = 4 := by norm_num
    simpa [add_assoc, e] using this
  · rw [e]
    have := opow_add_nat_lt h2 6
    have e : (2 : Ordinal.{1}) + (2 + 2) = 6 := by norm_num
    simpa [add_assoc, e] using this

theorem hsub_of_refl {H : Op} (hH : NiceOp H) {n : ℕ} (i j : Fin n) (ρ : Fin n → T) (a : T)
    (hi : ρ i = a) (hj : ρ j = a)
    (ihr : ∀ t : T, t.level < a.level → ∀ H' : Op, NiceOp H' → t.k ⊆ H' ∅ →
      HInf R H' {eqS t t} (ω ^ t.rk + 2) 0)
    (hka : a.k ⊆ H ∅) {Γ : Set RSS} (hΓ : kSeq Γ ⊆ H ∅) :
    HInf R H (insert (RSS.base (D0.subset i j) ρ) Γ) (ω ^ a.rk) 0 := by
  set S : RSS := RSS.base (D0.subset i j) ρ with hS
  have hkS : S.k ⊆ a.k := by
    show kD (D0.subset i j) (fun k => (ρ k).k) ⊆ _
    simp only [D0.subset, kD, kBd, ext_last, ext_castSucc]
    rw [hi, hj]
    simp
  have hαH : ω ^ a.rk ∈ H ∅ := (hH.nice ∅).opow_mem (T.form_mem hH hka)
  have hkΔ : kSeq (insert S Γ) ⊆ H ∅ := kSeq_insert_sub (hkS.trans hka) hΓ
  refine HInf.all' (A := S) (Set.mem_insert _ _) hαH hkΔ rfl (fun s => memOrd s.1 a + 2)
    (fun s => ?_) (fun s => ?_)
  · have hlt : s.1.level < a.level := by
      have := s.2
      simpa [resBd, hi] using this
    exact memOrd_lt hlt
  · obtain ⟨t, ht⟩ := s
    have hlt : t.level < a.level := by simpa [resBd, hi] using ht
    set Ht : Op := Hext H t.k with hHtdef
    have hHt : NiceOp Ht := hH.ext t.k
    have hkt : t.k ⊆ Ht ∅ := by rw [hHtdef, Hext_empty_apply]; exact hH.sub _
    have hmono : H ∅ ⊆ Ht ∅ := by rw [hHtdef, Hext_empty_apply]; exact hH.empty_sub _
    have hka' : a.k ⊆ Ht ∅ := hka.trans hmono
    have hΓ' : kSeq Γ ⊆ Ht ∅ := hΓ.trans hmono
    have hkS' : S.k ⊆ Ht ∅ := hkS.trans hka'
    have hchild : (expand R S).child ⟨t, ht⟩ =
        RSS.or (memInst t a).neg (RSS.base (D0.mem (Fin.last n) j.castSucc) (ext ρ t)) := by
      show RSS.or (memInst t (resBd (Bd.var i) ρ)).neg _ = _
      simp [resBd, hi]
    have hkch : ((expand R S).child ⟨t, ht⟩).k ⊆ Ht ∅ := by
      refine (child_k_sub S ⟨t, ht⟩).trans ?_
      refine Set.union_subset (Set.union_subset hkS' hkt) ?_
      intro x hx; have : x = 0 := hx
      subst this; exact (hHt.nice ∅).1
    have hkΔ0 : kSeq (insert ((expand R S).child ⟨t, ht⟩) (insert S Γ)) ⊆ Ht ∅ :=
      kSeq_insert_sub hkch (kSeq_insert_sub hkS' hΓ')
    show HInf R (Hext H t.k) _ (memOrd t a + 2) 0
    rw [← hHtdef]
    rw [hchild] at hkΔ0 ⊢
    refine HInf.or_intro hHt (Set.mem_insert _ _) hkΔ0 ?_
    have hcore := hmem_core (R := R) hHt (Fin.last n) j.castSucc (ext ρ t) t a (by simp)
      (by simp [hj]) hlt hkt hka' (ihr t hlt Ht hHt hkt) (Δ := insert
        (RSS.or (memInst t a).neg (RSS.base (D0.mem (Fin.last n) j.castSucc) (ext ρ t)))
        (insert S Γ)) hkΔ0
    rwa [Set.insert_comm] at hcore

theorem hrefl (a : T) : ∀ H : Op, NiceOp H → a.k ⊆ H ∅ → HInf R H {eqS a a} (ω ^ a.rk + 2) 0 := by
  induction' h : a.level using WellFoundedLT.induction with ξ ih generalizing a
  intro H hH hka
  have hαH : ω ^ a.rk + 2 ∈ H ∅ := by
    simpa using (hH.nice ∅).add_nat ((hH.nice ∅).opow_mem (T.form_mem hH hka)) 2
  have hkE : kSeq ({eqS a a} : Set RSS) ⊆ H ∅ := by
    rw [kSeq_singleton]; exact (k_eqS_sub a a).trans (Set.union_subset hka hka)
  have hihr : ∀ t : T, t.level < a.level → ∀ H' : Op, NiceOp H' → t.k ⊆ H' ∅ →
      HInf R H' {eqS t t} (ω ^ t.rk + 2) 0 :=
    fun t ht H' hH' hk' => ih t.level (h ▸ ht) t rfl H' hH' hk'
  refine HInf.all' (A := eqS a a) (Set.mem_singleton _) hαH hkE rfl (fun _ => ω ^ a.rk)
    (fun _ => lt_add_of_pos_right _ (by norm_num)) ?_
  intro j
  rw [show (expand R (eqS a a)).ks j = ∅ from rfl, Hext_empty]
  rcases j with ⟨b⟩
  cases b
  · exact hsub_of_refl hH 1 0 ![a, a] a rfl rfl hihr hka hkE
  · exact hsub_of_refl hH 0 1 ![a, a] a rfl rfl hihr hka hkE

end OrdinalAnalysis.KPi.RS
