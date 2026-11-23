/-
  Frontier track: two small instances of the finite-function layer (`FinFun.lean`).

  1. `Nmodel` : a *lawful* instance (`ThetaLaws`, `ThetaInvLaws` are proved) on `ι = α = ℕ`.  It is
     tiny, but it satisfies every law the proofs of `FinFun.lean` use.  In it the relation `<_lx`
     of A4 Def 3.25 has a 3-cycle among irreducible (single-support) functions:
       `{2 ↦ 1} <_lx {0 ↦ 5} <_lx {1 ↦ 3} <_lx {2 ↦ 1}`
     (points of the model: 1 = 1, 2 = K, 3 = K+1, 4 = K^K, 5 = K^(K+1)).  So transitivity of
     `<_lx` does NOT follow from the laws (and not from irreducibility): Lemma 3.37 / Lemma LX
     needs more than the printed Def 3.25.  The same cycle exists in the base-K Cantor-normal-form
     model (python).
  2. `Lexmodel` : values `K·b + c` as `ℕ ×ₗ ℕ`, with `θ̃` capped at "≥ K²".  It is used only to
     compare `lxL` with the python reference implementation (`lx_lt`) on the 25
     root-type functions (supp ≤ 1, value `K·b + c` with `b ≤ 3`, `c ≤ 2`, index `0,1,2`).
-/
module

public import OrdinalAnalysis.Frontier.FinFun
public import Mathlib.Order.Lex
public import Mathlib.Data.Prod.Lex

@[expose] public section

set_option autoImplicit false

namespace OrdinalAnalysis.Frontier.FinFun

/-! ### 1. A lawful model on `ℕ` -/

namespace Nmodel

/-- the "successor of exponent" map: `1 ↦ K`, `K ↦ K^K`, `K+1 ↦ K^(K+1)` -/
def mF : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | n + 4 => n + 6

theorem mF_mono : Monotone mF := by
  intro x y h
  unfold mF
  split <;> split <;> omega

theorem le_mF (x : ℕ) : x ≤ mF x := by
  unfold mF
  split <;> omega

theorem le_iter (n x : ℕ) : x ≤ mF^[n] x := by
  induction n generalizing x with
  | zero => exact le_refl _
  | succ n ih => rw [Function.iterate_succ_apply]; exact le_trans (le_mF x) (ih _)

instance : ThetaVal ℕ where
  oadd := max
  lam := 2
  tl := fun x => if x = 3 then 1 else x
  segs := fun x => if x = 3 then [2, 3] else [x]
  lamPred := fun _ => none
  omegaMul := id

instance : ThetaShift ℕ ℕ where
  th := fun c c' x => mF^[c' - c] x
  thInv := fun _ _ _ => 0

theorem th_def (c c' x : ℕ) : ThetaShift.th c c' x = mF^[c' - c] x := rfl

instance : ThetaLaws ℕ ℕ where
  zero_le := fun _ => Nat.zero_le _
  th_mono := fun c c' x y h => Monotone.iterate mF_mono _ h
  th_comp := fun c c' c'' x h1 h2 => by
    simp only [th_def]
    rw [show c'' - c = (c' - c) + (c'' - c') by omega, Function.iterate_add_apply]
  le_oadd_left := fun x y => le_max_left x y
  le_oadd_right := fun x y => le_max_right x y
  self_mem_segs := fun x => by
    by_cases h : x = 3 <;> simp [ThetaVal.segs, h]
  tl_le_of_mem_segs := fun x m h => by
    by_cases hx : x = 3
    · subst hx
      simp [ThetaVal.segs] at h
      rcases h with rfl | rfl <;> simp [ThetaVal.tl]
    · simp [ThetaVal.segs, hx] at h
      subst h
      exact le_refl _
  lam_le_th := fun c c' v hv hc => by
    simp only [th_def]
    obtain ⟨e, he⟩ : ∃ e, c' - c = e + 1 := ⟨c' - c - 1, by omega⟩
    rw [he, Function.iterate_succ_apply]
    have h2 : 2 ≤ mF v := by
      have : mF 1 ≤ mF v := mF_mono (by omega)
      simpa [mF] using this
    exact le_trans h2 (le_iter e _)

instance : ThetaInvLaws ℕ ℕ where
  thInv_mono := fun _ _ _ _ _ => le_refl _
  th_thInv_le := fun c c' x => by
    simp only [ThetaShift.thInv, th_def]
    have : ∀ n, mF^[n] 0 = 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply, show mF 0 = 0 from rfl, ih]
    rw [this]
    exact Nat.zero_le _
  segs_ext := fun x z m hxz hm => by
    by_cases hx : x = 3
    · subst hx
      simp [ThetaVal.segs] at hm
      by_cases hz : z = 3
      · subst hz
        refine ⟨m, ?_, le_refl _, le_refl _⟩
        rcases hm with rfl | rfl <;> simp [ThetaVal.segs]
      · refine ⟨z, by simp [ThetaVal.segs, hz], ?_, ?_⟩
        · rcases hm with rfl | rfl <;> omega
        · rcases hm with rfl | rfl <;> simp [ThetaVal.tl, hz] <;> omega
    · simp [ThetaVal.segs, hx] at hm
      subst hm
      by_cases hz : z = 3
      · subst hz
        refine ⟨2, by simp [ThetaVal.segs], by omega, ?_⟩
        simp [ThetaVal.tl, hx]
        omega
      · refine ⟨z, by simp [ThetaVal.segs, hz], hxz, ?_⟩
        simp [ThetaVal.tl, hx, hz]
        exact hxz

/-- the three functions of the cycle -/
def g1 : List (ℕ × ℕ) := [(2, 1)]
def g2 : List (ℕ × ℕ) := [(0, 5)]
def g3 : List (ℕ × ℕ) := [(1, 3)]

theorem g1_g2 : lxL g1 g2 = true := by decide
theorem g2_g3 : lxL g2 g3 = true := by decide
theorem g3_g1 : lxL g3 g1 = true := by decide
theorem g1_g3 : lxL g1 g3 = false := by decide

theorem g_irr : irrB g1 = true ∧ irrB g2 = true ∧ irrB g3 = true := by decide

/-- `<_lx` is not transitive on irreducible functions in this lawful model: the laws of
`ThetaLaws` (even with `ThetaInvLaws`) together with irreducibility do not give Lemma 3.37. -/
theorem lx_not_transitive :
    ¬ ∀ F G H : List (ℕ × ℕ), Srt F → Srt G → Srt H → NZ F → NZ G → NZ H →
      irrB F = true → irrB G = true → irrB H = true →
      lxL F G = true → lxL G H = true → lxL F H = true := by
  intro h
  have s1 : ∀ x : ℕ × ℕ, Srt [x] := fun x => List.pairwise_singleton _ _
  have n1 : ∀ x : ℕ × ℕ, x.2 ≠ 0 → NZ [x] := fun x hx p hp => by
    simp at hp; subst hp; exact hx
  have := h g1 g2 g3 (s1 _) (s1 _) (s1 _) (n1 _ (by decide)) (n1 _ (by decide))
    (n1 _ (by decide)) g_irr.1 g_irr.2.1 g_irr.2.2 g1_g2 g2_g3
  rw [g1_g3] at this
  exact Bool.false_ne_true this

/-- consistent with the proven asymmetry: the cycle is exactly the failure of transitivity. -/
theorem cycle_vs_asymm : lxL g1 g3 = false ∧ lxL g3 g1 = true := ⟨g1_g3, g3_g1⟩

end Nmodel

/-! ### 2. Comparison with the python reference (`lx_lt`) -/

namespace Lexmodel

/-- `K·b + c` -/
abbrev V := ℕ ×ₗ ℕ

instance : Zero V := ⟨toLex (0, 0)⟩

instance : ThetaVal V where
  oadd := fun x y =>
    if (ofLex y).1 > 0 then toLex ((ofLex x).1 + (ofLex y).1, (ofLex y).2)
    else toLex ((ofLex x).1, (ofLex x).2 + (ofLex y).2)
  lam := toLex (1, 0)
  tl := fun x => if (ofLex x).2 > 0 then toLex (0, 1) else if (ofLex x).1 > 0 then toLex (1, 0) else 0
  segs := fun x =>
    if (ofLex x).1 > 0 ∧ (ofLex x).2 > 0 then [toLex ((ofLex x).1, 0), x] else [x]
  lamPred := fun _ => none
  omegaMul := id

/-- `θ̃_d` capped: any non-zero value is sent above every tested value (`≥ K²`) -/
instance : ThetaShift ℕ V where
  th := fun _ _ x => if x = 0 then 0 else toLex (1000, 0)
  thInv := fun _ _ _ => 0

/-- the 25 test functions, in the order of the python table (empty, then index 0,1,2 × values) -/
def vals : List V :=
  [toLex (0, 1), toLex (0, 2), toLex (1, 0), toLex (1, 1), toLex (1, 2), toLex (2, 0),
    toLex (2, 1), toLex (3, 0)]

def testFns : List (List (ℕ × V)) :=
  [] :: ([0, 1, 2].flatMap fun i => vals.map fun v => [(i, v)])

/-- the python table: row `i`, column `j` is `lx_lt(f_i, f_j)` (it is the strict upper triangle:
`<_lx` is the lexicographic order on (support point, value), empty least). -/
def refRows : List String :=
  ["0111111111111111111111111", "0011111111111111111111111", "0001111111111111111111111",
   "0000111111111111111111111", "0000011111111111111111111", "0000001111111111111111111",
   "0000000111111111111111111", "0000000011111111111111111", "0000000001111111111111111",
   "0000000000111111111111111", "0000000000011111111111111", "0000000000001111111111111",
   "0000000000000111111111111", "0000000000000011111111111", "0000000000000001111111111",
   "0000000000000000111111111", "0000000000000000011111111", "0000000000000000001111111",
   "0000000000000000000111111", "0000000000000000000011111", "0000000000000000000001111",
   "0000000000000000000000111", "0000000000000000000000011", "0000000000000000000000001",
   "0000000000000000000000000"]

def leanRows : List String :=
  testFns.map fun f =>
    String.ofList (testFns.map fun g => if lxL f g then '1' else '0')

theorem matches_reference : leanRows = refRows := by decide

end Lexmodel

end OrdinalAnalysis.Frontier.FinFun
