module

public import OrdinalAnalysis.KPi.RS.EmbedWin
public import OrdinalAnalysis.KPi.RS.EmbedRules
public import OrdinalAnalysis.KPi.Theory
public import Foundation.FirstOrder.LK.Simplified

/-!
# The RS calculus, part 33: logical validity in `RS^∞` (B92 Lemma 3.11) and the embedding (Theorem 3.12)

*Uniform reading* (every quantifier of `ℒ_Ad` is restricted to `L_λ`; see `EmbedTr`).

`Emb R H lam Γ` says: there are `m, c < ω` such that for every `N` and every valuation `e` with values in
`𝒯_λ`, `H[ē] ⊢^{ω^{λ+m}}_{λ+c} Γ^λ(ē)` (the operator `H[ē] = Hwin H N e` is `H` extended by the levels of the
values).  `embed_derivation` proves `Emb Γ` for every Foundation `Derivation2 KPi Γ`, assuming `AxHyp`: the
`H`-controlled derivations of the relativised axioms of `KPi`.  `embedding_kpi` is the case of a theorem.
-/

@[expose] public section

open Ordinal FFL FFL.FirstOrder

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

open OrdinalAnalysis.KPi (LAd KPi)

variable {R : Set Ordinal.{1}}

/-- the hypotheses on `H` and `λ` (B92 Theorem 3.12: `λ ∈ H`, `ω·λ = λ` since `λ` is an `ε`-number). -/
structure EmbHyp (H : Op) (lam : Ordinal.{1}) : Prop where
  nice : NiceOp H
  lam_mem : lam ∈ H ∅
  lam_mul : ω * lam = lam
  lam_pos : 0 < lam

/-- the translation of a finite sequent. -/
def trSeq (lam : Ordinal.{1}) (N : ℕ) (e : ℕ → T) (Γ : Finset (Semiformula LAd ℕ 0)) :
    Set RSS := (fun γ => trS lam N e γ) '' (Γ : Set (Semiformula LAd ℕ 0))

theorem trSeq_insert (lam : Ordinal.{1}) (N : ℕ) (e : ℕ → T) (γ : Semiformula LAd ℕ 0)
    (Γ : Finset (Semiformula LAd ℕ 0)) :
    trSeq lam N e (insert γ Γ) = insert (trS lam N e γ) (trSeq lam N e Γ) := by
  simp [trSeq, Finset.coe_insert, Set.image_insert_eq]

theorem mem_trSeq {lam : Ordinal.{1}} {N : ℕ} {e : ℕ → T} {γ : Semiformula LAd ℕ 0}
    {Γ : Finset (Semiformula LAd ℕ 0)} (h : γ ∈ Γ) : trS lam N e γ ∈ trSeq lam N e Γ :=
  ⟨γ, h, rfl⟩

theorem trSeq_mono {lam : Ordinal.{1}} {N : ℕ} {e : ℕ → T} {Γ Δ : Finset (Semiformula LAd ℕ 0)}
    (h : Γ ⊆ Δ) : trSeq lam N e Γ ⊆ trSeq lam N e Δ :=
  Set.image_mono (Finset.coe_subset.2 h)

/-- the operator `H[ē]`. -/
def Hwin (H : Op) (N : ℕ) (e : ℕ → T) : Op := Hext H (Kenv (winRho N e))

/-- `Γ^λ(ē)` is `H[ē]`-derivable with length `ω^{λ+m}` and cut rank `λ+c`. -/
def Emb (R : Set Ordinal.{1}) (H : Op) (lam : Ordinal.{1}) (Γ : Finset (Semiformula LAd ℕ 0)) :
    Prop :=
  ∃ m c : ℕ, ∀ (N : ℕ) (e : ℕ → T), Val lam e →
    HInf R (Hwin H N e) (trSeq lam N e Γ) (ω ^ (lam + m)) (lam + c)

theorem win_empty {H : Op} (N : ℕ) (e : ℕ → T) : Hwin H N e ∅ = H (Kenv (winRho N e)) :=
  Hext_empty_apply _ _

theorem ord_add_nat_lt (lam : Ordinal.{1}) (m k : ℕ) : ω ^ (lam + m) + k < ω ^ (lam + (m + 1 : ℕ)) :=
  opow_add_nat_lt (addL_lt lam (by exact_mod_cast Nat.lt_succ_self m)) k

theorem ord_mono (lam : Ordinal.{1}) {m m' : ℕ} (h : m ≤ m') : ω ^ (lam + m) ≤ ω ^ (lam + m') :=
  opow_le_opow_right omega0_pos (addL_le lam (by exact_mod_cast h))

theorem lam_le_ord (lam : Ordinal.{1}) (m : ℕ) : lam ≤ ω ^ (lam + m) :=
  le_self_add.trans (right_le_opow (lam + m) one_lt_omega0)

namespace EmbHyp

variable {H : Op} {lam : Ordinal.{1}} (hy : EmbHyp H lam)

include hy

theorem win_nice (N : ℕ) (e : ℕ → T) : NiceOp (Hwin H N e) := hy.nice.ext _

theorem base_sub (N : ℕ) (e : ℕ → T) : H ∅ ⊆ Hwin H N e ∅ := by
  rw [win_empty]; exact hy.nice.empty_sub _

theorem lam_win (N : ℕ) (e : ℕ → T) : lam ∈ Hwin H N e ∅ := hy.base_sub N e hy.lam_mem

theorem kenv_win (N : ℕ) (e : ℕ → T) : Kenv (winRho N e) ⊆ Hwin H N e ∅ := by
  rw [win_empty]; exact hy.nice.sub _

theorem zero_win (N : ℕ) (e : ℕ → T) : (0 : Ordinal.{1}) ∈ Hwin H N e ∅ :=
  ((hy.win_nice N e).nice ∅).1

theorem k_win (N : ℕ) (e : ℕ → T) (γ : Semiformula LAd ℕ 0) :
    (trS lam N e γ).k ⊆ Hwin H N e ∅ := by
  intro ξ hξ
  rcases trS_k_sub lam N e γ ξ hξ with h | rfl | rfl
  · exact hy.kenv_win N e h
  · exact hy.lam_win N e
  · exact hy.zero_win N e

theorem kSeq_win (N : ℕ) (e : ℕ → T) (Γ : Finset (Semiformula LAd ℕ 0)) :
    kSeq (trSeq lam N e Γ) ⊆ Hwin H N e ∅ := by
  rintro ξ ⟨A, ⟨γ, hγ, rfl⟩, hξ⟩
  exact hy.k_win N e γ hξ

theorem ord_win (N : ℕ) (e : ℕ → T) (m : ℕ) : ω ^ (lam + m) ∈ Hwin H N e ∅ := by
  have h1 : lam + m ∈ Hwin H N e ∅ := by
    simpa using ((hy.win_nice N e).nice ∅).add_nat (hy.lam_win N e) m
  exact ((hy.win_nice N e).nice ∅).opow_mem h1

end EmbHyp


/-! ### bumping lengths and cut ranks -/

theorem op_sub_win {H : Op} (hH : NiceOp H) (N : ℕ) (e : ℕ → T) (X : Set Ordinal.{1}) :
    H X ⊆ Hwin H N e X :=
  hH.mono' Set.subset_union_right

namespace EmbHyp

variable {H : Op} {lam : Ordinal.{1}} (hy : EmbHyp H lam)

include hy

/-- bump `m` and `c`. -/
theorem bump (N : ℕ) (e : ℕ → T) {Δ : Set RSS} {m m' c c' : ℕ}
    (h : HInf R (Hwin H N e) Δ (ω ^ (lam + m)) (lam + c)) (hmm : m ≤ m') (hcc : c ≤ c') :
    HInf R (Hwin H N e) Δ (ω ^ (lam + m')) (lam + c') :=
  HInf.weaken_sub' (hy.win_nice N e) h subset_rfl (ord_mono lam hmm) (hy.ord_win N e m')
    (addL_le lam (by exact_mod_cast hcc)) h.k_sub

/-- from length `ω^{λ+M} + k` to length `ω^{λ+M+1}`. -/
theorem bump_k (N : ℕ) (e : ℕ → T) {Δ : Set RSS} {M c : ℕ} (k : ℕ)
    (h : HInf R (Hwin H N e) Δ (ω ^ (lam + M) + (k : Ordinal.{1})) (lam + c)) :
    HInf R (Hwin H N e) Δ (ω ^ (lam + (M + 1 : ℕ))) (lam + c) :=
  HInf.weaken_sub' (hy.win_nice N e) h subset_rfl (ord_add_nat_lt lam M k).le
    (hy.ord_win N e (M + 1)) le_rfl h.k_sub

end EmbHyp

/-! ### the rules -/

/-- the relativised axioms of `KPi` are `H`-derivable (B92 Theorem 2.9 + Lemma 3.10 in the final form). -/
def AxHyp (T' : Theory LAd) (R : Set Ordinal.{1}) (H : Op) (lam : Ordinal.{1}) : Prop :=
  ∀ φ : Sentence LAd, φ ∈ T' → ∃ m : ℕ,
    HInf R H {trS lam 0 (fun _ => T.L 0) (Rewriting.emb φ : Semiformula LAd ℕ 0)}
      (ω ^ (lam + m)) (lam + m)

theorem emb_closed {H : Op} {lam : Ordinal.{1}} (hy : EmbHyp H lam) {Γ : Finset (Semiformula LAd ℕ 0)}
    {φ : Semiformula LAd ℕ 0} (h1 : φ ∈ Γ) (h2 : ∼φ ∈ Γ) : Emb R H lam Γ := by
  obtain ⟨n, hn⟩ := rk_trS_le lam hy.lam_mul hy.lam_pos φ
  refine ⟨n, 0, fun N e he => ?_⟩
  have hH := hy.win_nice N e
  have h0 := htnd (R := R) (trS lam N e φ) (Hwin H N e) hH (hy.k_win N e φ)
  refine HInf.weaken_sub' hH h0 ?_ (opow_le_opow_right omega0_pos
    (hn N e he)) (hy.ord_win N e n) (zero_le) (hy.kSeq_win N e Γ)
  intro x hx
  rcases hx with rfl | hx
  · rw [← trS_neg]; exact mem_trSeq h2
  · have : x = trS lam N e φ := hx
    subst this; exact mem_trSeq h1

theorem emb_axm {H : Op} {lam : Ordinal.{1}} {T' : Theory LAd} (hy : EmbHyp H lam)
    (hax : AxHyp T' R H lam)
    {Γ : Finset (Semiformula LAd ℕ 0)} {φ : Sentence LAd} (hT : φ ∈ T')
    (hΓ : (φ : Semiformula LAd ℕ 0) ∈ Γ) : Emb R H lam Γ := by
  obtain ⟨m, hm⟩ := hax φ hT
  refine ⟨m, m, fun N e he => ?_⟩
  have hH := hy.win_nice N e
  have hm' := hm.mono_op (H' := Hwin H N e) (fun X => op_sub_win hy.nice N e X)
  refine hm'.sim hH (Γ' := trSeq lam N e Γ) ?_ (hy.kSeq_win N e Γ)
  intro x hx
  have : x = trS lam 0 (fun _ => T.L 0) (Rewriting.emb φ : Semiformula LAd ℕ 0) := hx
  subst this
  refine ⟨trS lam N e (Rewriting.emb φ : Semiformula LAd ℕ 0), mem_trSeq hΓ, ?_⟩
  exact trD_sim lam _ _ _ _ _ _ _ (fun i => i.elim0) (fun x hx => by simp at hx)

theorem emb_verum {H : Op} {lam : Ordinal.{1}} (hy : EmbHyp H lam)
    {Γ : Finset (Semiformula LAd ℕ 0)} (h : (⊤ : Semiformula LAd ℕ 0) ∈ Γ) : Emb R H lam Γ := by
  refine ⟨1, 0, fun N e he => ?_⟩
  have hH := hy.win_nice N e
  have hS : trS lam N e (⊤ : Semiformula LAd ℕ 0) ∈ trSeq lam N e Γ := mem_trSeq h
  have h0 := HInf.ball_lev_intro (R := R) (lam := 0) (ρc := lam + 0) hH
    (A := D0.mem (Fin.last _) (Fin.last _)) (ρ := winRho N e) (Δ := trSeq lam N e Γ) hS
    (hy.kSeq_win N e Γ) (hy.ord_win N e 0)
    (fun t ht => absurd ht (by simp))
  refine hy.bump_k N e 3 ?_
  simpa using h0


theorem kSeq_of_sim {Γ Γ' : Set RSS} {X : Set Ordinal.{1}} (hk : kSeq Γ ⊆ X)
    (h : ∀ y ∈ Γ', ∃ x ∈ Γ, Sim R x y) : kSeq Γ' ⊆ X := by
  rintro ξ ⟨y, hy, hξ⟩
  obtain ⟨x, hx, hxy⟩ := h y hy
  exact hk ⟨x, hx, by rw [hxy.k_eq]; exact hξ⟩

theorem kenv_cons_sub (N : ℕ) (e : ℕ → T) (t : T) :
    Kenv (winRho (N + 1) (consV t e)) ⊆ Kenv (winRho N e) ∪ t.k := by
  rintro ξ ⟨i, hi⟩
  rcases i with ⟨i, hi'⟩
  cases i with
  | zero =>
    right
    simpa [winRho, truncV, consV] using hi
  | succ j =>
    left
    refine ⟨⟨j, by omega⟩, ?_⟩
    have : winRho N e ⟨j, by omega⟩ = winRho (N + 1) (consV t e) ⟨j + 1, hi'⟩ := by
      simp only [winRho, truncV, consV]
      by_cases h : j < N <;> simp [h]
    rw [this]; exact hi

theorem kenv_shift_sub (N : ℕ) (e : ℕ → T) :
    Kenv (winRho (N - 1) (fun x => e (x + 1))) ⊆ Kenv (winRho N e) := by
  rintro ξ ⟨i, hi⟩
  rcases i with ⟨i, hi'⟩
  by_cases h : i < N - 1
  · refine ⟨⟨i + 1, by omega⟩, ?_⟩
    have : winRho N e ⟨i + 1, by omega⟩ = winRho (N - 1) (fun x => e (x + 1)) ⟨i, hi'⟩ := by
      simp only [winRho, truncV]
      have h1 : i + 1 < N := by omega
      simp [h, h1]
    rw [this]; exact hi
  · refine ⟨⟨N, by omega⟩, ?_⟩
    have : winRho N e ⟨N, by omega⟩ = winRho (N - 1) (fun x => e (x + 1)) ⟨i, hi'⟩ := by
      simp only [winRho, truncV]
      simp [h]
    rw [this]; exact hi

theorem emb_and {H : Op} {lam : Ordinal.{1}} (hy : EmbHyp H lam) {Γ : Finset (Semiformula LAd ℕ 0)}
    {φ ψ : Semiformula LAd ℕ 0} (h : φ ⋏ ψ ∈ Γ) (d1 : Emb R H lam (insert φ Γ))
    (d2 : Emb R H lam (insert ψ Γ)) : Emb R H lam Γ := by
  obtain ⟨m1, c1, h1⟩ := d1
  obtain ⟨m2, c2, h2⟩ := d2
  refine ⟨max m1 m2 + 1, max c1 c2, fun N e he => ?_⟩
  have hH := hy.win_nice N e
  have hA := hy.bump N e (m' := max m1 m2) (c' := max c1 c2) (h1 N e he) (le_max_left _ _)
    (le_max_left _ _)
  have hB := hy.bump N e (m' := max m1 m2) (c' := max c1 c2) (h2 N e he) (le_max_right _ _)
    (le_max_right _ _)
  rw [trSeq_insert] at hA hB
  have hS : trS lam N e (φ ⋏ ψ) ∈ trSeq lam N e Γ := mem_trSeq h
  have := HInf.band_intro (R := R) hH (A := trD lam (Fin.elim0 : Fin 0 → Fin (N + 1)) (winVf N) φ)
    (B := trD lam (Fin.elim0 : Fin 0 → Fin (N + 1)) (winVf N) ψ) (ρ := winRho N e) hS
    (hy.kSeq_win N e Γ) hA hB
  exact hy.bump_k N e 1 (by simpa using this)

theorem emb_or {H : Op} {lam : Ordinal.{1}} (hy : EmbHyp H lam) {Γ : Finset (Semiformula LAd ℕ 0)}
    {φ ψ : Semiformula LAd ℕ 0} (h : φ ⋎ ψ ∈ Γ) (d : Emb R H lam (insert φ (insert ψ Γ))) :
    Emb R H lam Γ := by
  obtain ⟨m, c, h1⟩ := d
  refine ⟨m + 1, c, fun N e he => ?_⟩
  have hH := hy.win_nice N e
  have hA := h1 N e he
  rw [trSeq_insert, trSeq_insert] at hA
  have hS : trS lam N e (φ ⋎ ψ) ∈ trSeq lam N e Γ := mem_trSeq h
  have := HInf.bor_intro (R := R) hH (A := trD lam (Fin.elim0 : Fin 0 → Fin (N + 1)) (winVf N) φ)
    (B := trD lam (Fin.elim0 : Fin 0 → Fin (N + 1)) (winVf N) ψ) (ρ := winRho N e) hS
    (hy.kSeq_win N e Γ) hA
  exact hy.bump_k N e 2 (by simpa using this)

theorem emb_wk {H : Op} {lam : Ordinal.{1}} (hy : EmbHyp H lam) {Γ Δ : Finset (Semiformula LAd ℕ 0)}
    (h : Emb R H lam Δ) (hsub : Δ ⊆ Γ) : Emb R H lam Γ := by
  obtain ⟨m, c, hd⟩ := h
  refine ⟨m, c, fun N e he => ?_⟩
  exact HInf.weaken_sub' (hy.win_nice N e) (hd N e he) (trSeq_mono hsub) le_rfl
    (hy.ord_win N e m) le_rfl (hy.kSeq_win N e Γ)

theorem emb_cut {H : Op} {lam : Ordinal.{1}} (hy : EmbHyp H lam) {Γ : Finset (Semiformula LAd ℕ 0)}
    {φ : Semiformula LAd ℕ 0} (d1 : Emb R H lam (insert φ Γ)) (d2 : Emb R H lam (insert (∼φ) Γ)) :
    Emb R H lam Γ := by
  obtain ⟨m1, c1, h1⟩ := d1
  obtain ⟨m2, c2, h2⟩ := d2
  obtain ⟨n, hn⟩ := rk_trS_le lam hy.lam_mul hy.lam_pos φ
  refine ⟨max m1 m2 + 1, max (max c1 c2) (n + 1), fun N e he => ?_⟩
  have hH := hy.win_nice N e
  have hA := hy.bump N e (m' := max m1 m2) (c' := max (max c1 c2) (n + 1)) (h1 N e he)
    (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hB := hy.bump N e (m' := max m1 m2) (c' := max (max c1 c2) (n + 1)) (h2 N e he)
    (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  rw [trSeq_insert] at hA hB
  rw [trS_neg] at hB
  have hC : (trS lam N e φ).rk < lam + ((max (max c1 c2) (n + 1) : ℕ) : Ordinal.{1}) := by
    have hnn : (n : Ordinal.{1}) < ((n + 1 : ℕ) : Ordinal.{1}) := by
      exact_mod_cast Nat.lt_succ_self n
    have hnc : ((n + 1 : ℕ) : Ordinal.{1}) ≤ ((max (max c1 c2) (n + 1) : ℕ) : Ordinal.{1}) := by
      exact_mod_cast le_max_right _ _
    exact lt_of_le_of_lt (hn N e he) (lt_of_lt_of_le (addL_lt lam hnn) (addL_le lam hnc))
  have := HInf.cut (R := R) (C := trS lam N e φ) (α₀ := ω ^ (lam + (max m1 m2 : ℕ)))
    (hy.ord_win N e (max m1 m2) |> fun hh => by
      simpa using ((hy.win_nice N e).nice ∅).add_nat hh 1) (hy.kSeq_win N e Γ) hC
    (lt_add_one _) hB hA
  exact hy.bump_k N e 1 (by simpa using this)

theorem emb_shift {H : Op} {lam : Ordinal.{1}} (hy : EmbHyp H lam) {Γ : Finset (Semiformula LAd ℕ 0)}
    (h : Emb R H lam Γ) : Emb R H lam (Γ.image Rewriting.shift) := by
  obtain ⟨m, c, hd⟩ := h
  refine ⟨m, c, fun N e he => ?_⟩
  have hH := hy.win_nice N e
  have hprem := hd (N - 1) (fun x => e (x + 1)) (fun x => he (x + 1))
  have hmono : ∀ X, Hwin H (N - 1) (fun x => e (x + 1)) X ⊆ Hwin H N e X := by
    intro X
    exact hy.nice.mono' (Set.union_subset_union_left _ (kenv_shift_sub N e))
  refine (hprem.mono_op hmono).sim hH ?_ (hy.kSeq_win N e _)
  rintro x ⟨γ, hγ, rfl⟩
  exact ⟨trS lam N e (Rewriting.shift γ), ⟨Rewriting.shift γ, Finset.mem_coe.2
    (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hγ)), rfl⟩, trS_shift_sim lam N e γ⟩

theorem emb_all {H : Op} {lam : Ordinal.{1}} (hy : EmbHyp H lam) {Γ : Finset (Semiformula LAd ℕ 0)}
    {φ : Semiformula LAd ℕ 1} (h : ∀¹ φ ∈ Γ)
    (d : Emb R H lam (insert (Rewriting.free φ) (Γ.image Rewriting.shift))) :
    Emb R H lam Γ := by
  obtain ⟨m, c, hd⟩ := d
  refine ⟨m + 1, c, fun N e he => ?_⟩
  have hH := hy.win_nice N e
  have hS : trS lam N e (∀¹ φ) ∈ trSeq lam N e Γ := mem_trSeq h
  have key := HInf.ball_lev_intro (R := R) (lam := lam) (ρc := lam + c) hH
    (A := trD lam (extV (Fin.elim0 : Fin 0 → Fin (N + 1))) (liftVf (winVf N)) φ)
    (ρ := winRho N e) (Δ := trSeq lam N e Γ) (α := ω ^ (lam + m)) hS (hy.kSeq_win N e Γ)
    (hy.ord_win N e m) ?_
  · exact hy.bump_k N e 3 (by simpa using key)
  · intro t ht
    have hprem := hd (N + 1) (consV t e) (he.cons ht)
    have hmono : ∀ X, Hwin H (N + 1) (consV t e) X ⊆ Hext (Hwin H N e) t.k X := by
      intro X
      show H (Kenv (winRho (N + 1) (consV t e)) ∪ X) ⊆ H (Kenv (winRho N e) ∪ (t.k ∪ X))
      refine hy.nice.mono' ?_
      intro ξ hξ
      rcases hξ with hξ | hξ
      · rcases kenv_cons_sub N e t hξ with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr hξ)
    have hcorr1 : ∀ x ∈ trSeq lam (N + 1) (consV t e)
        (insert (Rewriting.free φ) (Γ.image Rewriting.shift)),
        ∃ y ∈ insert (RSS.base (trD lam (extV (Fin.elim0 : Fin 0 → Fin (N + 1))) (liftVf (winVf N)) φ)
          (ext (winRho N e) t)) (trSeq lam N e Γ), Sim R x y := by
      rintro x ⟨δ, hδ, rfl⟩
      rcases Finset.mem_insert.1 (Finset.mem_coe.1 hδ) with rfl | hδ
      · exact ⟨_, Set.mem_insert _ _, trS_free_sim lam N e t φ⟩
      · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hδ
        exact ⟨trS lam N e γ, Set.mem_insert_of_mem _ (mem_trSeq hγ),
          (trS_shift_sim lam (N + 1) (consV t e) γ).symm⟩
    have hcorr2 : ∀ y ∈ insert (RSS.base (trD lam (extV (Fin.elim0 : Fin 0 → Fin (N + 1)))
          (liftVf (winVf N)) φ) (ext (winRho N e) t)) (trSeq lam N e Γ),
        ∃ x ∈ trSeq lam (N + 1) (consV t e)
          (insert (Rewriting.free φ) (Γ.image Rewriting.shift)), Sim R x y := by
      intro y hy'
      rcases hy' with rfl | ⟨γ, hγ, rfl⟩
      · exact ⟨_, mem_trSeq (Finset.mem_insert_self _ _), trS_free_sim lam N e t φ⟩
      · exact ⟨trS lam (N + 1) (consV t e) (Rewriting.shift γ),
          mem_trSeq (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hγ))),
          (trS_shift_sim lam (N + 1) (consV t e) γ).symm⟩
    have hprem' := hprem.mono_op hmono
    exact hprem'.sim (hH.ext t.k) hcorr1
      (kSeq_of_sim (hprem.k_sub.trans (hmono ∅)) hcorr2)

theorem emb_exs {H : Op} {lam : Ordinal.{1}} (hy : EmbHyp H lam) {Γ : Finset (Semiformula LAd ℕ 0)}
    {φ : Semiformula LAd ℕ 1} (h : ∃¹ φ ∈ Γ) (t : Semiterm LAd ℕ 0)
    (d : Emb R H lam (insert (φ ⇜ ![t]) Γ)) : Emb R H lam Γ := by
  cases t with
  | bvar i => exact i.elim0
  | func f v => exact f.elim
  | fvar x =>
    obtain ⟨m, c, hd⟩ := d
    refine ⟨m + 1, c, fun N e he => ?_⟩
    have hH := hy.win_nice N e
    have hS : trS lam N e (∃¹ φ) ∈ trSeq lam N e Γ := mem_trSeq h
    have hs : (truncV N e x).level < lam := Val.trunc hy.lam_pos he N x
    have hprem := hd N e he
    rw [trSeq_insert] at hprem
    have hcorr1 : ∀ z ∈ insert (trS lam N e (φ ⇜ ![(&x : Semiterm LAd ℕ 0)])) (trSeq lam N e Γ),
        ∃ y ∈ insert (RSS.base (trD lam (extV (Fin.elim0 : Fin 0 → Fin (N + 1)))
          (liftVf (winVf N)) φ) (ext (winRho N e) (truncV N e x))) (trSeq lam N e Γ), Sim R z y := by
      intro z hz
      rcases hz with rfl | hz
      · exact ⟨_, Set.mem_insert _ _, trS_subst_sim lam N e x φ⟩
      · exact ⟨z, Set.mem_insert_of_mem _ hz, Sim.refl _⟩
    have hcorr2 : ∀ y ∈ insert (RSS.base (trD lam (extV (Fin.elim0 : Fin 0 → Fin (N + 1)))
          (liftVf (winVf N)) φ) (ext (winRho N e) (truncV N e x))) (trSeq lam N e Γ),
        ∃ z ∈ insert (trS lam N e (φ ⇜ ![(&x : Semiterm LAd ℕ 0)])) (trSeq lam N e Γ),
          Sim R z y := by
      intro y hy'
      rcases hy' with rfl | hy'
      · exact ⟨_, Set.mem_insert _ _, trS_subst_sim lam N e x φ⟩
      · exact ⟨y, Set.mem_insert_of_mem _ hy', Sim.refl _⟩
    have hprem' := hprem.sim hH hcorr1 (kSeq_of_sim hprem.k_sub hcorr2)
    have hsk : (truncV N e x).k ⊆ Hwin H N e ∅ := by
      intro ξ hξ
      refine hy.kenv_win N e ⟨winVf N x, ?_⟩
      rw [winRho_vf]; exact hξ
    have key := HInf.bex_lev_intro (R := R) hH (lam := lam)
      (A := trD lam (extV (Fin.elim0 : Fin 0 → Fin (N + 1))) (liftVf (winVf N)) φ)
      (ρ := winRho N e) (Δ := trSeq lam N e Γ) (α := ω ^ (lam + m)) (ρc := lam + c) hS
      (hy.kSeq_win N e Γ) (hy.ord_win N e m) (truncV N e x) hs
      (lt_of_lt_of_le hs (lam_le_ord lam m)) hsk hprem'
    exact hy.bump_k N e 2 (by simpa using key)

theorem embed_derivation {H : Op} {lam : Ordinal.{1}} {T' : Theory LAd} (hy : EmbHyp H lam)
    (hax : AxHyp T' R H lam) :
    ∀ {Γ : Finset (Semiformula LAd ℕ 0)}, (T' ⟹₂ Γ) → Emb R H lam Γ := by
  intro Γ d
  induction d with
  | closed Γ φ h1 h2 => exact emb_closed hy h1 h2
  | axm φ hT hΓ => exact emb_axm hy hax hT hΓ
  | verum h => exact emb_verum hy h
  | and h d1 d2 ih1 ih2 => exact emb_and hy h ih1 ih2
  | or h d ih => exact emb_or hy h ih
  | all h d ih => exact emb_all hy h ih
  | exs h t d ih => exact emb_exs hy h t ih
  | wk d hsub ih => exact emb_wk hy ih hsub
  | shift d ih => exact emb_shift hy ih
  | cut d1 d2 ih1 ih2 => exact emb_cut hy ih1 ih2

/-- **B92 Theorem 3.12 (Embedding), uniform reading, for an arbitrary theory `T'` whose relativised
axioms are `H`-derivable:** every theorem `θ` of `T'` has an `H`-controlled `RS^∞`-derivation of `θ^λ` of length
`ω^{λ+m}` and cut rank `λ+c`. -/
theorem embedding {H : Op} {lam : Ordinal.{1}} {T' : Theory LAd} (hy : EmbHyp H lam)
    (hax : AxHyp T' R H lam) {θ : Sentence LAd} (hθ : T' ⊢ θ) :
    ∃ m c : ℕ, HInf R (Hwin H 0 (fun _ => T.L 0))
      {trS lam 0 (fun _ => T.L 0) (Rewriting.emb θ : Semiformula LAd ℕ 0)}
      (ω ^ (lam + m)) (lam + c) := by
  obtain ⟨d⟩ := provable_iff_derivable2.1 hθ
  obtain ⟨m, c, h⟩ := embed_derivation hy hax d
  refine ⟨m, c, ?_⟩
  have := h 0 (fun _ => T.L 0) (fun _ => hy.lam_pos)
  simpa [trSeq] using this

/-- **Theorem 3.12 for `KPi`** (uniform reading), relative to the relativised axioms. -/
theorem embedding_kpi {H : Op} {lam : Ordinal.{1}} (hy : EmbHyp H lam)
    (hax : AxHyp (KPi : Theory LAd) R H lam) {θ : Sentence LAd} (hθ : KPi ⊢ θ) :
    ∃ m c : ℕ, HInf R (Hwin H 0 (fun _ => T.L 0))
      {trS lam 0 (fun _ => T.L 0) (Rewriting.emb θ : Semiformula LAd ℕ 0)}
      (ω ^ (lam + m)) (lam + c) :=
  embedding hy hax hθ

/-- **Lemma 3.11 / Theorem 3.12 for pure logic (no hypotheses):** every logically valid sentence
`θ` of `ℒ_Ad` has a cut-bounded `H`-controlled `RS^∞`-derivation of `θ^λ` of length `ω^{λ+m}`. -/
theorem embedding_logic {H : Op} {lam : Ordinal.{1}} (hy : EmbHyp H lam) {θ : Sentence LAd}
    (hθ : (∅ : Theory LAd) ⊢ θ) :
    ∃ m c : ℕ, HInf R (Hwin H 0 (fun _ => T.L 0))
      {trS lam 0 (fun _ => T.L 0) (Rewriting.emb θ : Semiformula LAd ℕ 0)}
      (ω ^ (lam + m)) (lam + c) :=
  embedding hy (fun φ hφ => absurd hφ (Set.notMem_empty φ)) hθ

end OrdinalAnalysis.KPi.RS
