module

public import OrdinalAnalysis.KPi.RS.StarAxBase

/-!
# The RS calculus, part 16: Theorem 2.9 (a), the axioms (Pair) and (Union)

The axioms are D0-sentences relative to a *bound* `b : Bd m`, i.e. `A^b` where every unrestricted
quantifier is restricted to `b`.  With `b = lev λ` (context `m = 0`) this is `A^λ`; with `b = var 0`
and `ρ = ![L_κ]` this is `A^{L_κ}`, the instance needed for `(Ad.3)`.  The derivation only uses
`resBd b ρ = L_λ` for a limit ordinal `λ`.
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}} {σ : Ordinal.{1}}

/-- `(Pair)^b`: `∀x∈b ∀y∈b ∃z∈b (x ∈ z ∧ y ∈ z)`. -/
def pairD {m : ℕ} (b : Bd m) : D0 m :=
  .ball b (.ball b.shift (.bex b.shift.shift
    (.and (.mem (Fin.castSucc (Fin.castSucc (Fin.last m))) (Fin.last (m + 2)))
          (.mem (Fin.castSucc (Fin.last (m + 1))) (Fin.last (m + 2))))))

/-- `(Union)^b`: `∀x∈b ∃z∈b ∀y∈x ∀u∈y (u ∈ z)`. -/
def unionD {m : ℕ} (b : Bd m) : D0 m :=
  .ball b (.bex b.shift (.ball (.var (Fin.castSucc (Fin.last m))) (.ball (.var (Fin.last (m + 2)))
    (.mem (Fin.last (m + 3)) (Fin.castSucc (Fin.castSucc (Fin.last (m + 1))))))))

theorem levLE_pairD {m : ℕ} (b : Bd m) (hb : ∀ α, b = Bd.lev α → False) : D0.LevLE 0 (pairD b) := by
  cases b with
  | lev α => exact absurd rfl (hb α)
  | var i => simp [pairD, Bd.shift, D0.LevLE]

theorem levLE_unionD {m : ℕ} (b : Bd m) (hb : ∀ α, b = Bd.lev α → False) :
    D0.LevLE 0 (unionD b) := by
  cases b with
  | lev α => exact absurd rfl (hb α)
  | var i => simp [unionD, Bd.shift, D0.LevLE]

/-- `⊢* (Pair)^λ` (B92 Thm 2.9 (a)). -/
theorem star_pair {m : ℕ} {b : Bd m} {ρ : Fin m → T} {Δ : Set RSS} {lam : Ordinal.{1}}
    (hlam : Order.IsSuccLimit lam) (hb : resBd b ρ = T.L lam)
    (hA : RSS.base (pairD b) ρ ∈ Δ) : Star R σ Δ := by
  refine star_ball' hA hb (fun x hx => ?_)
  refine star_ball' (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (by rw [resBd_shift, hb]) (fun y hy => ?_)
  refine star_bex' (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (by rw [resBd_shift, resBd_shift, hb]) (T.L (max x.level y.level + 1)) ?_ ?_
    (star_memInst_L' _ _) ?_
  · show max x.level y.level + 1 < lam
    exact hlam.succ_lt (max_lt hx hy)
  · refine fun ξ hξ => ?_
    have h : ξ = max x.level y.level + 1 := hξ
    rw [h]
    refine starK_max_succ ?_ ?_
    · exact level_mem_kSeq (A := (memInst x (T.L lam)).neg) (by simp) (k_neg_memInst _ _)
    · exact level_mem_kSeq (A := (memInst y (T.L lam)).neg) (by simp) (k_neg_memInst _ _)
  · refine star_band_of (Set.mem_insert _ _) ?_ ?_
    · refine star_mem_L (β := max x.level y.level + 1) (Set.mem_insert _ _) (by simp) ?_
      have h : x.level < max x.level y.level + 1 :=
        lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
      simp
    · refine star_mem_L (β := max x.level y.level + 1) (Set.mem_insert _ _) (by simp) ?_
      have h : y.level < max x.level y.level + 1 :=
        lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
      simp

/-- `⊢* (Union)^λ` (B92 Thm 2.9 (a)). -/
theorem star_union {m : ℕ} {b : Bd m} {ρ : Fin m → T} {Δ : Set RSS} {lam : Ordinal.{1}}
    (hb : resBd b ρ = T.L lam) (hA : RSS.base (unionD b) ρ ∈ Δ) : Star R σ Δ := by
  refine star_ball' hA hb (fun x hx => ?_)
  refine star_bex' (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (by rw [resBd_shift, hb]) (T.L x.level) hx ?_ (star_memInst_L' _ _) ?_
  · refine fun ξ hξ => ?_
    have h : ξ = x.level := hξ
    rw [h]
    exact subset_starK R _ (level_mem_kSeq (A := (memInst x (T.L lam)).neg) (by simp)
      (k_neg_memInst _ _))
  · refine star_ball' (Set.mem_insert _ _) (s := x) (by simp [resBd]) (fun y hy => ?_)
    refine star_ball' (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (s := y)
      (by simp [resBd]) (fun u hu => ?_)
    refine star_mem_L (β := x.level) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      (by simp) ?_
    have h : u.level < x.level := lt_trans hu hy
    simpa using h

end OrdinalAnalysis.KPi.RS
