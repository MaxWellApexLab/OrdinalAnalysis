import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import OrdinalAnalysis.KPi.RS.Defs

/-!
# The RS calculus, part 2: rank facts and B92 Lemma 1.9 (b)

`child_rk_lt` is B92 Lemma 1.9 (b): `rk A_i < rk A` for every member `A_i` of the junctor of `A`.
The proof runs through the environment-of-ranks presentation of `rk`: `rk (A(c))` depends on `c` only
through `rk c` (`rkD_dom`), the rank of a term satisfies `rk t < omega * (|t| + 1)` (`PT.rk_lt`) and
`omega * b <= rk t` for `b` in `k t` (`PT.K`).  Further B92 numbers: `rk_eqS` is (5), `rk_memInst_lt`
is (3), `RSS.rk_neg` is Lemma 1.9 (e).
-/

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

/-! ### ordinal helpers -/

/-- (right addition is monotone) -/
theorem addR_le {a b : Ordinal.{1}} (h : a ≤ b) (c : Ordinal.{1}) : a + c ≤ b + c := add_le_add_left h c

/-- (left addition is monotone) -/
theorem addL_le (c : Ordinal.{1}) {a b : Ordinal.{1}} (h : a ≤ b) : c + a ≤ c + b := add_le_add_right h c

theorem max_add' (a b c : Ordinal.{1}) : max a b + c = max (a + c) (b + c) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (addR_le h c)]
  · rw [max_eq_left h, max_eq_left (addR_le h c)]

theorem lt_omega_mul_of_lt {x γ : Ordinal.{1}} (h : x < ω * γ) (n : ℕ) : x + n < ω * γ := by
  have hγ : 0 < γ := by
    rcases eq_zero_or_pos γ with h0 | h0
    · subst h0; simp at h
    · exact h0
  exact (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hγ).add_natCast_lt h n

/-- (left addition is strictly monotone) -/
theorem addL_lt (c : Ordinal.{1}) {a b : Ordinal.{1}} (h : a < b) : c + a < c + b := add_lt_add_right h c

theorem omega_mul_lt_succ (α : Ordinal.{1}) : ω * α < ω * (α + 1) := by
  rw [mul_add_one]
  exact lt_add_of_pos_right _ omega0_pos

/-! ### environments -/

theorem ext_le_ext {n : ℕ} {e e' : Fin n → Ordinal.{1}} {x x' : Ordinal.{1}}
    (h : ∀ i, e i ≤ e' i) (hx : x ≤ x') (i : Fin (n + 1)) : ext e x i ≤ ext e' x' i := by
  induction i using Fin.lastCases with
  | last => simpa using hx
  | cast j => simpa using h j

theorem ext_comp {X Y : Sort*} {n : ℕ} (f : X → Y) (e : Fin n → X) (x : X) :
    (fun i => f (ext e x i)) = ext (fun i => f (e i)) (f x) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

/-! ### monotonicity -/

theorem rkBd_mono {n : ℕ} (b : Bd n) {e e' : Fin n → Ordinal.{1}} (h : ∀ i, e i ≤ e' i) :
    rkBd b e ≤ rkBd b e' := by
  cases b with
  | var i => exact h i
  | lev α => exact le_rfl

theorem rkD_mono : ∀ {n : ℕ} (A : D0 n) {e e' : Fin n → Ordinal.{1}}, (∀ i, e i ≤ e' i) →
    rkD A e ≤ rkD A e'
  | _, .mem i j, e, e', h => by
      simp only [rkD]
      exact max_le_max (addR_le (h i) _) (addR_le (h j) _)
  | _, .nmem i j, e, e', h => by
      simp only [rkD]
      exact max_le_max (addR_le (h i) _) (addR_le (h j) _)
  | _, .ad i, e, e', h => by
      simp only [rkD]
      exact addR_le (h i) _
  | _, .nad i, e, e', h => by
      simp only [rkD]
      exact addR_le (h i) _
  | _, .and A B, e, e', h => by
      simp only [rkD]
      exact addR_le (max_le_max (rkD_mono A h) (rkD_mono B h)) _
  | _, .or A B, e, e', h => by
      simp only [rkD]
      exact addR_le (max_le_max (rkD_mono A h) (rkD_mono B h)) _
  | _, .bex b A, e, e', h => by
      simp only [rkD]
      exact max_le_max (rkBd_mono b h)
        (addR_le (rkD_mono A (ext_le_ext h le_rfl)) _)
  | _, .ball b A, e, e', h => by
      simp only [rkD]
      exact max_le_max (rkBd_mono b h)
        (addR_le (rkD_mono A (ext_le_ext h le_rfl)) _)

/-! ### domination: replacing an entry by something larger costs a bounded constant -/

/-- a constant bounding the effect of a bigger environment entry. -/
def mA : {n : ℕ} → D0 n → ℕ
  | _, .mem _ _ => 6
  | _, .nmem _ _ => 6
  | _, .ad _ => 5
  | _, .nad _ => 5
  | _, .and A B => max (mA A) (mA B) + 1
  | _, .or A B => max (mA A) (mA B) + 1
  | _, .bex _ A => mA A + 2
  | _, .ball _ A => mA A + 2

theorem le_max_add {x y r : Ordinal.{1}} (c : ℕ) (h : x ≤ max y r) :
    x + c ≤ max (y + c) (r + c) := by
  calc x + c ≤ max y r + c := addR_le h c
    _ = max (y + c) (r + c) := max_add' _ _ _

theorem rkBd_dom {n : ℕ} (b : Bd n) {e e0 : Fin n → Ordinal.{1}} {r : Ordinal.{1}}
    (hd : ∀ i, e i ≤ max (e0 i) r) : rkBd b e ≤ max (rkBd b e0) r := by
  cases b with
  | var i => exact hd i
  | lev α => exact le_max_left _ _

/-- the shape `max (rkBd b e) (rkD A (ext e 0) + 2)` of the two quantifier cases. -/
theorem dom_bind {n : ℕ} (b : Bd n) (A : D0 (n + 1)) {e e0 : Fin n → Ordinal.{1}} {r : Ordinal.{1}}
    (hd : ∀ i, e i ≤ max (e0 i) r)
    (IH : rkD A (ext e 0) ≤ max (rkD A (ext e0 0)) (r + ((mA A : ℕ) : Ordinal.{1}))) :
    max (rkBd b e) (rkD A (ext e 0) + 2) ≤
      max (max (rkBd b e0) (rkD A (ext e0 0) + 2)) (r + (((mA A + 2 : ℕ)) : Ordinal.{1})) := by
  have hb := rkBd_dom b hd
  have hA : rkD A (ext e 0) + 2 ≤ max (rkD A (ext e0 0) + 2) (r + (((mA A + 2 : ℕ)) : Ordinal.{1})) := by
    have := le_max_add 2 IH
    push_cast
    simpa [add_assoc] using this
  refine max_le (le_trans hb (max_le_max (le_max_left _ _) ?_)) ?_
  · exact le_self_add
  · exact le_trans hA (max_le (le_max_of_le_left (le_max_right _ _)) (le_max_right _ _))

theorem rkD_dom : ∀ {n : ℕ} (A : D0 n) {e e0 : Fin n → Ordinal.{1}} {r : Ordinal.{1}},
    (∀ i, e i ≤ max (e0 i) r) → rkD A e ≤ max (rkD A e0) (r + (mA A : ℕ))
  | _, .mem i j, e, e0, r, hd => by
      simp only [rkD, mA, Nat.cast_ofNat]
      have h1 : e i + 6 ≤ max (e0 i + 6) (r + 6) := by simpa using le_max_add 6 (hd i)
      have h2 : e j + 1 ≤ max (e0 j + 1) (r + 1) := by simpa using le_max_add 1 (hd j)
      have h3 : r + 1 ≤ r + 6 := addL_le r (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 6))
      refine max_le ?_ ?_
      · exact le_trans h1 (max_le (le_max_of_le_left (le_max_left _ _)) (le_max_right _ _))
      · exact le_trans h2 (max_le (le_max_of_le_left (le_max_right _ _)) (le_max_of_le_right h3))
  | _, .nmem i j, e, e0, r, hd => by
      simp only [rkD, mA, Nat.cast_ofNat]
      have h1 : e i + 6 ≤ max (e0 i + 6) (r + 6) := by simpa using le_max_add 6 (hd i)
      have h2 : e j + 1 ≤ max (e0 j + 1) (r + 1) := by simpa using le_max_add 1 (hd j)
      have h3 : r + 1 ≤ r + 6 := addL_le r (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 6))
      refine max_le ?_ ?_
      · exact le_trans h1 (max_le (le_max_of_le_left (le_max_left _ _)) (le_max_right _ _))
      · exact le_trans h2 (max_le (le_max_of_le_left (le_max_right _ _)) (le_max_of_le_right h3))
  | _, .ad i, e, e0, r, hd => by
      simp only [rkD, mA, Nat.cast_ofNat]
      simpa using le_max_add 5 (hd i)
  | _, .nad i, e, e0, r, hd => by
      simp only [rkD, mA, Nat.cast_ofNat]
      simpa using le_max_add 5 (hd i)
  | _, .and A B, e, e0, r, hd => by
      simp only [rkD, mA]
      have hM : ∀ m : ℕ, m ≤ max (mA A) (mA B) →
          r + (m : Ordinal.{1}) ≤ r + ((max (mA A) (mA B) : ℕ) : Ordinal.{1}) :=
        fun m hm => addL_le r (by exact_mod_cast hm)
      have hA' : rkD A e ≤ max (rkD A e0) (r + ((max (mA A) (mA B) : ℕ) : Ordinal.{1})) :=
        le_trans (rkD_dom A hd) (max_le_max le_rfl (hM _ (le_max_left _ _)))
      have hB' : rkD B e ≤ max (rkD B e0) (r + ((max (mA A) (mA B) : ℕ) : Ordinal.{1})) :=
        le_trans (rkD_dom B hd) (max_le_max le_rfl (hM _ (le_max_right _ _)))
      have h0 : max (rkD A e) (rkD B e) ≤
          max (max (rkD A e0) (rkD B e0)) (r + ((max (mA A) (mA B) : ℕ) : Ordinal.{1})) :=
        max_le (le_trans hA' (max_le_max (le_max_left _ _) le_rfl))
          (le_trans hB' (max_le_max (le_max_right _ _) le_rfl))
      have h := le_max_add 1 h0
      push_cast
      simpa [add_assoc] using h
  | _, .or A B, e, e0, r, hd => by
      simp only [rkD, mA]
      have hM : ∀ m : ℕ, m ≤ max (mA A) (mA B) →
          r + (m : Ordinal.{1}) ≤ r + ((max (mA A) (mA B) : ℕ) : Ordinal.{1}) :=
        fun m hm => addL_le r (by exact_mod_cast hm)
      have hA' : rkD A e ≤ max (rkD A e0) (r + ((max (mA A) (mA B) : ℕ) : Ordinal.{1})) :=
        le_trans (rkD_dom A hd) (max_le_max le_rfl (hM _ (le_max_left _ _)))
      have hB' : rkD B e ≤ max (rkD B e0) (r + ((max (mA A) (mA B) : ℕ) : Ordinal.{1})) :=
        le_trans (rkD_dom B hd) (max_le_max le_rfl (hM _ (le_max_right _ _)))
      have h0 : max (rkD A e) (rkD B e) ≤
          max (max (rkD A e0) (rkD B e0)) (r + ((max (mA A) (mA B) : ℕ) : Ordinal.{1})) :=
        max_le (le_trans hA' (max_le_max (le_max_left _ _) le_rfl))
          (le_trans hB' (max_le_max (le_max_right _ _) le_rfl))
      have h := le_max_add 1 h0
      push_cast
      simpa [add_assoc] using h
  | _, .bex b A, e, e0, r, hd => by
      simp only [rkD, mA]
      have hd' : ∀ i, ext e 0 i ≤ max (ext e0 0 i) r := by
        intro i
        induction i using Fin.lastCases with
        | last => simp
        | cast j => simpa using hd j
      exact dom_bind b A hd (rkD_dom A hd')
  | _, .ball b A, e, e0, r, hd => by
      simp only [rkD, mA]
      have hd' : ∀ i, ext e 0 i ≤ max (ext e0 0 i) r := by
        intro i
        induction i using Fin.lastCases with
        | last => simp
        | cast j => simpa using hd j
      exact dom_bind b A hd (rkD_dom A hd')

/-! ### `ω·β ≤ rk` for `β ∈ k`  -/

theorem rkBd_K {n : ℕ} (b : Bd n) {e : Fin n → Ordinal.{1}} {ek : Fin n → Set Ordinal.{1}}
    (h : ∀ i, ∀ β ∈ ek i, ω * β ≤ e i) {β : Ordinal.{1}} (hβ : β ∈ kBd b ek) :
    ω * β ≤ rkBd b e := by
  cases b with
  | var i => exact h i β hβ
  | lev γ =>
    simp only [kBd, Set.mem_singleton_iff] at hβ
    subst hβ
    exact le_rfl

theorem ext_K {n : ℕ} {e : Fin n → Ordinal.{1}} {ek : Fin n → Set Ordinal.{1}}
    (h : ∀ i, ∀ β ∈ ek i, ω * β ≤ e i) :
    ∀ i, ∀ β ∈ ext ek ∅ i, ω * β ≤ ext e 0 i := by
  intro i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simpa using h j

theorem rkD_K : ∀ {n : ℕ} (A : D0 n) (e : Fin n → Ordinal.{1}) (ek : Fin n → Set Ordinal.{1}),
    (∀ i, ∀ β ∈ ek i, ω * β ≤ e i) → ∀ β ∈ kD A ek, ω * β ≤ rkD A e
  | _, .mem i j, e, ek, h, β, hβ => by
      simp only [kD, Set.mem_union] at hβ
      simp only [rkD]
      rcases hβ with hβ | hβ
      · exact le_max_of_le_left (le_trans (h i β hβ) le_self_add)
      · exact le_max_of_le_right (le_trans (h j β hβ) le_self_add)
  | _, .nmem i j, e, ek, h, β, hβ => by
      simp only [kD, Set.mem_union] at hβ
      simp only [rkD]
      rcases hβ with hβ | hβ
      · exact le_max_of_le_left (le_trans (h i β hβ) le_self_add)
      · exact le_max_of_le_right (le_trans (h j β hβ) le_self_add)
  | _, .ad i, e, ek, h, β, hβ => by
      simp only [kD] at hβ
      simp only [rkD]
      exact le_trans (h i β hβ) le_self_add
  | _, .nad i, e, ek, h, β, hβ => by
      simp only [kD] at hβ
      simp only [rkD]
      exact le_trans (h i β hβ) le_self_add
  | _, .and A B, e, ek, h, β, hβ => by
      simp only [kD, Set.mem_union] at hβ
      simp only [rkD]
      rcases hβ with hβ | hβ
      · exact le_trans (rkD_K A e ek h β hβ) (le_trans (le_max_left _ _) le_self_add)
      · exact le_trans (rkD_K B e ek h β hβ) (le_trans (le_max_right _ _) le_self_add)
  | _, .or A B, e, ek, h, β, hβ => by
      simp only [kD, Set.mem_union] at hβ
      simp only [rkD]
      rcases hβ with hβ | hβ
      · exact le_trans (rkD_K A e ek h β hβ) (le_trans (le_max_left _ _) le_self_add)
      · exact le_trans (rkD_K B e ek h β hβ) (le_trans (le_max_right _ _) le_self_add)
  | _, .bex b A, e, ek, h, β, hβ => by
      simp only [kD, Set.mem_union] at hβ
      simp only [rkD]
      rcases hβ with hβ | hβ
      · exact le_max_of_le_left (rkBd_K b h hβ)
      · exact le_max_of_le_right (le_trans (rkD_K A _ _ (ext_K h) β hβ) le_self_add)
  | _, .ball b A, e, ek, h, β, hβ => by
      simp only [kD, Set.mem_union] at hβ
      simp only [rkD]
      rcases hβ with hβ | hβ
      · exact le_max_of_le_left (rkBd_K b h hβ)
      · exact le_max_of_le_right (le_trans (rkD_K A _ _ (ext_K h) β hβ) le_self_add)

theorem PT.K : ∀ (t : PT) (β : Ordinal.{1}), β ∈ t.k → ω * β ≤ t.rk
  | .L α, β, hβ => by
      simp only [PT.k, Set.mem_singleton_iff] at hβ
      subst hβ
      simp [PT.rk]
  | .sep α φ a, β, hβ => by
      simp only [PT.k, Set.mem_union, Set.mem_singleton_iff] at hβ
      simp only [PT.rk]
      rcases hβ with hβ | hβ
      · subst hβ; exact le_max_of_le_left le_self_add
      · have h : ∀ i, ∀ β ∈ ext (fun i => (a i).k) ∅ i, ω * β ≤ ext (fun i => (a i).rk) 0 i := by
          intro i
          induction i using Fin.lastCases with
          | last => simp
          | cast j => simpa using fun β hβ => PT.K (a j) β hβ
        exact le_max_of_le_right (le_trans (rkD_K φ _ _ h β hβ) le_self_add)

theorem PT.level_mem_k : ∀ t : PT, t.level ∈ t.k
  | .L α => by simp [PT.level, PT.k]
  | .sep α φ a => by simp [PT.level, PT.k]

theorem T.K (t : T) : ω * t.level ≤ t.rk := PT.K t.1 _ (PT.level_mem_k t.1)

/-! ### the upper bound `rk t < ω·(|t|+1)` -/

theorem omul_le {a b : Ordinal.{1}} (h : a ≤ b) : ω * a ≤ ω * b := mul_le_mul_right h ω

theorem ext_zero_le {n : ℕ} {e : Fin n → Ordinal.{1}} {B : Ordinal.{1}} (he : ∀ i, e i ≤ B) :
    ∀ i, ext e 0 i ≤ B := by
  intro i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simpa using he j

theorem rkD_U : ∀ {n : ℕ} (A : D0 n) (α : Ordinal.{1}), D0.LevLE α A →
    ∃ m : ℕ, ∀ (e : Fin n → Ordinal.{1}) (B : Ordinal.{1}), ω * α ≤ B → (∀ i, e i ≤ B) →
      rkD A e ≤ B + (m : Ordinal.{1}) := by
  intro n A
  induction A with
  | mem i j =>
      intro α _
      refine ⟨6, fun e B _ he => ?_⟩
      simp only [rkD, Nat.cast_ofNat]
      refine max_le (addR_le (he i) 6) (le_trans (addR_le (he j) 1) (addL_le B ?_))
      exact_mod_cast (by norm_num : (1 : ℕ) ≤ 6)
  | nmem i j =>
      intro α _
      refine ⟨6, fun e B _ he => ?_⟩
      simp only [rkD, Nat.cast_ofNat]
      refine max_le (addR_le (he i) 6) (le_trans (addR_le (he j) 1) (addL_le B ?_))
      exact_mod_cast (by norm_num : (1 : ℕ) ≤ 6)
  | ad i =>
      intro α _
      refine ⟨5, fun e B _ he => ?_⟩
      simp only [rkD, Nat.cast_ofNat]
      exact addR_le (he i) 5
  | nad i =>
      intro α _
      refine ⟨5, fun e B _ he => ?_⟩
      simp only [rkD, Nat.cast_ofNat]
      exact addR_le (he i) 5
  | and A B ihA ihB =>
      intro α hL
      simp only [D0.LevLE] at hL
      obtain ⟨m1, h1⟩ := ihA α hL.1
      obtain ⟨m2, h2⟩ := ihB α hL.2
      refine ⟨max m1 m2 + 1, fun e Bx hB he => ?_⟩
      simp only [rkD]
      have hA : rkD A e ≤ Bx + ((max m1 m2 : ℕ) : Ordinal.{1}) :=
        le_trans (h1 e Bx hB he) (addL_le Bx (by exact_mod_cast le_max_left m1 m2))
      have hB2 : rkD B e ≤ Bx + ((max m1 m2 : ℕ) : Ordinal.{1}) :=
        le_trans (h2 e Bx hB he) (addL_le Bx (by exact_mod_cast le_max_right m1 m2))
      have := addR_le (max_le hA hB2) 1
      push_cast
      simpa [add_assoc] using this
  | or A B ihA ihB =>
      intro α hL
      simp only [D0.LevLE] at hL
      obtain ⟨m1, h1⟩ := ihA α hL.1
      obtain ⟨m2, h2⟩ := ihB α hL.2
      refine ⟨max m1 m2 + 1, fun e Bx hB he => ?_⟩
      simp only [rkD]
      have hA : rkD A e ≤ Bx + ((max m1 m2 : ℕ) : Ordinal.{1}) :=
        le_trans (h1 e Bx hB he) (addL_le Bx (by exact_mod_cast le_max_left m1 m2))
      have hB2 : rkD B e ≤ Bx + ((max m1 m2 : ℕ) : Ordinal.{1}) :=
        le_trans (h2 e Bx hB he) (addL_le Bx (by exact_mod_cast le_max_right m1 m2))
      have := addR_le (max_le hA hB2) 1
      push_cast
      simpa [add_assoc] using this
  | bex b A ih =>
      intro α hL
      cases b with
      | var j =>
        simp only [D0.LevLE] at hL
        obtain ⟨m, h⟩ := ih α hL
        refine ⟨m + 2, fun e B hB he => ?_⟩
        simp only [rkD, rkBd]
        refine max_le (le_trans (he j) le_self_add) ?_
        have := addR_le (h (ext e 0) B hB (ext_zero_le he)) 2
        push_cast
        simpa [add_assoc] using this
      | lev γ =>
        simp only [D0.LevLE] at hL
        obtain ⟨m, h⟩ := ih α hL.2
        refine ⟨m + 2, fun e B hB he => ?_⟩
        simp only [rkD, rkBd]
        refine max_le (le_trans (omul_le hL.1) (le_trans hB le_self_add)) ?_
        have := addR_le (h (ext e 0) B hB (ext_zero_le he)) 2
        push_cast
        simpa [add_assoc] using this
  | ball b A ih =>
      intro α hL
      cases b with
      | var j =>
        simp only [D0.LevLE] at hL
        obtain ⟨m, h⟩ := ih α hL
        refine ⟨m + 2, fun e B hB he => ?_⟩
        simp only [rkD, rkBd]
        refine max_le (le_trans (he j) le_self_add) ?_
        have := addR_le (h (ext e 0) B hB (ext_zero_le he)) 2
        push_cast
        simpa [add_assoc] using this
      | lev γ =>
        simp only [D0.LevLE] at hL
        obtain ⟨m, h⟩ := ih α hL.2
        refine ⟨m + 2, fun e B hB he => ?_⟩
        simp only [rkD, rkBd]
        refine max_le (le_trans (omul_le hL.1) (le_trans hB le_self_add)) ?_
        have := addR_le (h (ext e 0) B hB (ext_zero_le he)) 2
        push_cast
        simpa [add_assoc] using this

theorem PT.rk_lt : ∀ t : PT, t.Wf → t.rk < ω * (t.level + 1)
  | .L α, _ => by
      simp only [PT.rk, PT.level]
      exact omega_mul_lt_succ α
  | .sep α φ a, hw => by
      obtain ⟨h0, hL, ha, _⟩ := hw
      obtain ⟨m, hm⟩ := rkD_U φ α hL
      have he : ∀ i, ext (fun i => (a i).rk) 0 i ≤ ω * α := by
        intro i
        induction i using Fin.lastCases with
        | last => simp
        | cast j =>
          simp only [ext_castSucc]
          have h1 := PT.rk_lt (a j) (ha j).1
          have h2 : (a j).level + 1 ≤ α := Order.add_one_le_of_lt (ha j).2
          exact le_trans h1.le (omul_le h2)
      have hb := hm _ (ω * α) le_rfl he
      simp only [PT.rk, PT.level]
      rw [mul_add_one]
      refine max_lt ?_ ?_
      · exact addL_lt _ (one_lt_omega0)
      · have h3 : rkD φ (ext (fun i => (a i).rk) 0) + 2 ≤ ω * α + ((m + 2 : ℕ) : Ordinal.{1}) := by
          have := addR_le hb 2
          push_cast
          simpa [add_assoc] using this
        exact lt_of_le_of_lt h3 (addL_lt _ (natCast_lt_omega0 _))

theorem T.rk_lt (t : T) : t.rk < ω * (t.level + 1) := PT.rk_lt t.1 t.2

/-! ### negation preserves rank (B92 Lemma 1.9 e) -/

theorem rkD_neg : ∀ {n : ℕ} (A : D0 n) (e : Fin n → Ordinal.{1}), rkD A.neg e = rkD A e
  | _, .mem i j, e => by simp [D0.neg, rkD]
  | _, .nmem i j, e => by simp [D0.neg, rkD]
  | _, .ad i, e => by simp [D0.neg, rkD]
  | _, .nad i, e => by simp [D0.neg, rkD]
  | _, .and A B, e => by simp [D0.neg, rkD, rkD_neg A, rkD_neg B]
  | _, .or A B, e => by simp [D0.neg, rkD, rkD_neg A, rkD_neg B]
  | _, .bex b A, e => by simp [D0.neg, rkD, rkD_neg A]
  | _, .ball b A, e => by simp [D0.neg, rkD, rkD_neg A]

theorem RSS.rk_neg : ∀ A : RSS, A.neg.rk = A.rk
  | .base φ ρ => by simp [RSS.neg, RSS.rk, rkD_neg]
  | .and A B => by simp [RSS.neg, RSS.rk, RSS.rk_neg A, RSS.rk_neg B]
  | .or A B => by simp [RSS.neg, RSS.rk, RSS.rk_neg A, RSS.rk_neg B]

/-! ### the rank of `a = b` (B92 Lemma 1.9 (5)) -/

theorem rk_eqS (a b : T) : (eqS a b).rk = max (max a.rk b.rk + 4) 9 := by
  have h : (fun i => ((![a, b] : Fin 2 → T) i).rk) = ![a.rk, b.rk] := by
    funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
  simp only [eqS, RSS.rk, h, D0.eqf, D0.subset, rkD, rkBd]
  simp only [ext_last, ext_castSucc]
  simp
  have e1 : ∀ x : Ordinal.{1}, max 6 (x + 1) + 2 = max 8 (x + 3) := by
    intro x; rw [max_add']; norm_num [add_assoc]
  rw [e1, e1]
  have hp : a.rk ≤ a.rk + 3 := le_self_add
  have hq : b.rk ≤ b.rk + 3 := le_self_add
  have h1 : max (max a.rk (max 8 (b.rk + 3))) (max b.rk (max 8 (a.rk + 3))) =
      max 8 (max (a.rk + 3) (b.rk + 3)) := by
    apply le_antisymm
    · exact max_le
        (max_le (le_trans hp (le_max_of_le_right (le_max_left _ _)))
          (max_le (le_max_left _ _) (le_max_of_le_right (le_max_right _ _))))
        (max_le (le_trans hq (le_max_of_le_right (le_max_right _ _)))
          (max_le (le_max_left _ _) (le_max_of_le_right (le_max_left _ _))))
    · exact max_le (le_max_of_le_left (le_max_of_le_right (le_max_left _ _)))
        (max_le (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
          (le_max_of_le_left (le_max_of_le_right (le_max_right _ _))))
  rw [h1, max_add', max_add' (a.rk + 3) (b.rk + 3) 1, max_add' a.rk b.rk 4]
  norm_num [add_assoc]
  rw [max_comm]

/-! ### `t ∈° b` has smaller rank than `b` (B92 Lemma 1.9 (3)) -/

theorem T.rk_lt_mul {t : T} {β : Ordinal.{1}} (h : t.level < β) : t.rk < ω * β :=
  lt_of_lt_of_le (T.rk_lt t) (omul_le (Order.add_one_le_of_lt h))

theorem T.rk_add_lt {t b : T} (h : t.level < b.level) (n : ℕ) : t.rk + n < b.rk :=
  lt_of_lt_of_le (lt_omega_mul_of_lt (T.rk_lt_mul h) n) (T.K b)

theorem T.omega_le_rk {t b : T} (h : t.level < b.level) : (ω : Ordinal.{1}) ≤ b.rk := by
  have hpos : 0 < b.level := lt_of_le_of_lt zero_le h
  exact le_trans (le_mul_left ω hpos) (T.K b)

theorem T.nat_lt_rk {t b : T} (h : t.level < b.level) (n : ℕ) : (n : Ordinal.{1}) < b.rk :=
  lt_of_lt_of_le (natCast_lt_omega0 n) (T.omega_le_rk h)

theorem rkEnv_ext {n : ℕ} (ρ : Fin n → T) (s : T) :
    (fun i => (ext ρ s i).rk) = ext (fun i => (ρ i).rk) s.rk :=
  ext_comp T.rk ρ s

theorem rk_memInst_lt {t b : T} (h : t.level < b.level) : (memInst t b).rk + 1 < b.rk := by
  rcases b with ⟨b, hb⟩
  cases b with
  | L β =>
    have h1 : t.rk + 6 + 1 < (T.L β).rk := by
      have := T.rk_add_lt (b := T.L β) h 7
      refine lt_of_le_of_lt (le_of_eq ?_) this
      norm_num [add_assoc]
    have h2 : (0 : Ordinal.{1}) + 1 + 1 < T.rk ⟨PT.L β, hb⟩ := by
      have := T.nat_lt_rk (b := T.L β) h 2
      refine lt_of_le_of_lt (le_of_eq ?_) this
      norm_num
    have h3 : (T.L 0).rk = 0 := by simp [T.rk, PT.rk, T.L]
    simp only [memInst, RSS.rk, rkD]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h3]
    rw [max_add']
    exact max_lt h1 h2
  | sep β φ a =>
    obtain ⟨h0, hL, ha, hOcc⟩ := hb
    simp only [memInst, RSS.rk]
    rw [rkEnv_ext]
    have hd : ∀ i, ext (fun i => (a i).rk) t.rk i ≤
        max (ext (fun i => (a i).rk) 0 i) t.rk := by
      intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast j => simp only [ext_castSucc]; exact le_max_left _ _
    have hdom := rkD_dom φ (e := ext (fun i => (a i).rk) t.rk) (e0 := ext (fun i => (a i).rk) 0)
      (r := t.rk) hd
    have hlev : t.level < β := h
    have hbig : t.rk + ((mA φ + 1 : ℕ) : Ordinal.{1}) < ω * β := by
      have := lt_omega_mul_of_lt (T.rk_lt_mul hlev) (mA φ + 1)
      simpa using this
    have hb2 : (T.rk ⟨.sep β φ a, ⟨h0, hL, ha, hOcc⟩⟩) = max (ω * β + 1) (rkD φ (ext (fun i => (a i).rk) 0) + 2) := rfl
    show rkD φ (ext (fun i => (a i).rk) t.rk) + 1 < T.rk ⟨.sep β φ a, ⟨h0, hL, ha, hOcc⟩⟩
    rw [hb2]
    refine lt_of_le_of_lt (addR_le hdom 1) ?_
    rw [max_add']
    have hbig' : t.rk + ((mA φ : ℕ) : Ordinal.{1}) + 1 < ω * β := by
      simpa [add_assoc] using hbig
    have hx : rkD φ (ext (fun i => (a i).rk) 0) + 1 < rkD φ (ext (fun i => (a i).rk) 0) + 2 :=
      addL_lt _ (by exact_mod_cast (by norm_num : (1 : ℕ) < 2))
    exact max_lt (lt_of_lt_of_le hx (le_max_right _ _))
      (lt_of_lt_of_le hbig' (le_trans le_self_add (le_max_left _ _)))

/-! ### B92 Lemma 1.9 (b): every member of a junctor has smaller rank -/

theorem rk_base {n : ℕ} (φ : D0 n) (ρ : Fin n → T) :
    (RSS.base φ ρ).rk = rkD φ (fun i => (ρ i).rk) := rfl

theorem rk_and (A B : RSS) : (RSS.and A B).rk = max A.rk B.rk + 1 := rfl

theorem rk_or (A B : RSS) : (RSS.or A B).rk = max A.rk B.rk + 1 := rfl

theorem rkBd_res {n : ℕ} (b : Bd n) (ρ : Fin n → T) :
    rkBd b (fun i => (ρ i).rk) = (resBd b ρ).rk := by
  cases b with
  | var i => rfl
  | lev α => simp [rkBd, resBd, T.rk, PT.rk, T.L]

/-- the shared inequality for the children `t ∈° b ∧ t = a`. -/
theorem and_child_lt {X Y : RSS} {a b t : T} (ht : t.level < b.level)
    (hX : X.rk + 1 < b.rk) (hY : Y.rk ≤ max (max t.rk a.rk + 4) 9) :
    max X.rk Y.rk + 1 < max (a.rk + 6) (b.rk + 1) := by
  rw [max_add']
  refine max_lt ?_ ?_
  · exact lt_of_lt_of_le hX (le_trans le_self_add (le_max_right _ _))
  · have h0 : Y.rk + 1 ≤ max (max t.rk a.rk + 4) 9 + 1 := addR_le hY 1
    have h5 : max (max t.rk a.rk + 4) 9 + 1 = max (max (t.rk + 5) (a.rk + 5)) 10 := by
      rw [max_add', max_add' t.rk a.rk 4, max_add']
      norm_num [add_assoc]
    rw [h5] at h0
    refine lt_of_le_of_lt h0 ?_
    refine max_lt (max_lt ?_ ?_) ?_
    · exact lt_of_lt_of_le (T.rk_add_lt ht 5) (le_trans le_self_add (le_max_right _ _))
    · exact lt_of_lt_of_le (addL_lt _ (by exact_mod_cast (by norm_num : (5 : ℕ) < 6)))
        (le_max_left _ _)
    · exact lt_of_lt_of_le (by simpa using T.nat_lt_rk ht 10)
        (le_trans le_self_add (le_max_right _ _))

theorem rk_mem_child {n : ℕ} (ρ : Fin n → T) (i j : Fin n) (t : Tlt (ρ j).level) :
    (RSS.and (memInst t.1 (ρ j)) (eqS t.1 (ρ i))).rk < (RSS.base (D0.mem i j) ρ).rk := by
  rw [rk_and, rk_base]
  simp only [rkD]
  exact and_child_lt t.2 (rk_memInst_lt t.2) (le_of_eq (rk_eqS _ _))

theorem rk_nmem_child {n : ℕ} (ρ : Fin n → T) (i j : Fin n) (t : Tlt (ρ j).level) :
    (RSS.or (memInst t.1 (ρ j)).neg (eqS t.1 (ρ i)).neg).rk < (RSS.base (D0.nmem i j) ρ).rk := by
  rw [rk_or, rk_base, RSS.rk_neg, RSS.rk_neg]
  simp only [rkD]
  exact and_child_lt t.2 (rk_memInst_lt t.2) (le_of_eq (rk_eqS _ _))

theorem rk_eqS_lt_ad {a : T} {κ : Ordinal.{1}} (hκ : 0 < κ) (hle : κ ≤ a.level) :
    (eqS (T.L κ) a).rk < a.rk + 5 := by
  rw [rk_eqS]
  have h1 : (T.L κ).rk ≤ a.rk := by
    have : (T.L κ).rk = ω * κ := by simp [T.rk, PT.rk, T.L]
    rw [this]
    exact le_trans (omul_le hle) (T.K a)
  have hom : (ω : Ordinal.{1}) ≤ a.rk := by
    have : (T.L κ).rk = ω * κ := by simp [T.rk, PT.rk, T.L]
    exact le_trans (le_mul_left ω hκ) (le_trans (le_of_eq this.symm) h1)
  rw [max_eq_right h1]
  refine max_lt (addL_lt _ (by exact_mod_cast (by norm_num : (4 : ℕ) < 5))) ?_
  exact lt_of_lt_of_le (by simpa using natCast_lt_omega0 9) (le_trans hom le_self_add)

theorem rk_bex_child {n : ℕ} (b : Bd n) (A : D0 (n + 1)) (ρ : Fin n → T)
    (s : Tlt (resBd b ρ).level) :
    (RSS.and (memInst s.1 (resBd b ρ)) (RSS.base A (ext ρ s.1))).rk <
      (RSS.base (D0.bex b A) ρ).rk := by
  rw [rk_and, rk_base, rk_base]
  simp only [rkD]
  rw [rkBd_res, rkEnv_ext]
  have hd : ∀ i, ext (fun i => (ρ i).rk) s.1.rk i ≤ max (ext (fun i => (ρ i).rk) 0 i) s.1.rk := by
    intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp only [ext_castSucc]; exact le_max_left _ _
  have hdom := rkD_dom A hd
  have h1 := rk_memInst_lt s.2
  have h2 : s.1.rk + ((mA A : ℕ) + 1 : ℕ) < (resBd b ρ).rk := T.rk_add_lt s.2 _
  rw [max_add']
  refine max_lt ?_ ?_
  · exact lt_of_lt_of_le h1 (le_max_left _ _)
  · refine lt_of_le_of_lt (addR_le hdom 1) ?_
    rw [max_add']
    have hx : rkD A (ext (fun i => (ρ i).rk) 0) + 1 < rkD A (ext (fun i => (ρ i).rk) 0) + 2 :=
      addL_lt _ (by exact_mod_cast (by norm_num : (1 : ℕ) < 2))
    refine max_lt (lt_of_lt_of_le hx (le_max_right _ _)) ?_
    refine lt_of_lt_of_le ?_ (le_max_left _ _)
    simpa [add_assoc] using h2

theorem rk_ball_child {n : ℕ} (b : Bd n) (A : D0 (n + 1)) (ρ : Fin n → T)
    (s : Tlt (resBd b ρ).level) :
    (RSS.or (memInst s.1 (resBd b ρ)).neg (RSS.base A (ext ρ s.1))).rk <
      (RSS.base (D0.ball b A) ρ).rk := by
  rw [rk_or, rk_base, rk_base, RSS.rk_neg]
  simp only [rkD]
  rw [rkBd_res, rkEnv_ext]
  have hd : ∀ i, ext (fun i => (ρ i).rk) s.1.rk i ≤ max (ext (fun i => (ρ i).rk) 0 i) s.1.rk := by
    intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp only [ext_castSucc]; exact le_max_left _ _
  have hdom := rkD_dom A hd
  have h1 := rk_memInst_lt s.2
  have h2 : s.1.rk + ((mA A : ℕ) + 1 : ℕ) < (resBd b ρ).rk := T.rk_add_lt s.2 _
  rw [max_add']
  refine max_lt ?_ ?_
  · exact lt_of_lt_of_le h1 (le_max_left _ _)
  · refine lt_of_le_of_lt (addR_le hdom 1) ?_
    rw [max_add']
    have hx : rkD A (ext (fun i => (ρ i).rk) 0) + 1 < rkD A (ext (fun i => (ρ i).rk) 0) + 2 :=
      addL_lt _ (by exact_mod_cast (by norm_num : (1 : ℕ) < 2))
    refine max_lt (lt_of_lt_of_le hx (le_max_right _ _)) ?_
    refine lt_of_lt_of_le ?_ (le_max_left _ _)
    simpa [add_assoc] using h2

theorem rk_cond_lt (A B : RSS) (j : Two) : (cond j.down A B).rk < max A.rk B.rk + 1 := by
  rcases j with ⟨b⟩
  cases b
  · exact lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  · exact lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)

/-- **B92 Lemma 1.9 (b).** -/
theorem child_rk_lt (R : Set Ordinal.{1}) (A : RSS)
    (j : (expand R A).J) : ((expand R A).child j).rk < A.rk := by
  cases A with
  | base φ ρ =>
    cases φ with
    | mem i k => exact rk_mem_child ρ i k j
    | nmem i k => exact rk_nmem_child ρ i k j
    | ad i =>
      obtain ⟨κ, hκR, hκ0, hκ⟩ := (show {κ : Ordinal.{1} // κ ∈ R ∧ 0 < κ ∧ κ ≤ (ρ i).level} from j)
      exact rk_eqS_lt_ad hκ0 hκ
    | nad i =>
      obtain ⟨κ, hκR, hκ0, hκ⟩ := (show {κ : Ordinal.{1} // κ ∈ R ∧ 0 < κ ∧ κ ≤ (ρ i).level} from j)
      have := rk_eqS_lt_ad hκ0 hκ
      show (eqS (T.L κ) (ρ i)).neg.rk < _
      rw [RSS.rk_neg]
      exact this
    | and A B => exact rk_cond_lt (RSS.base A ρ) (RSS.base B ρ) j
    | or A B => exact rk_cond_lt (RSS.base A ρ) (RSS.base B ρ) j
    | bex b A => exact rk_bex_child b A ρ j
    | ball b A => exact rk_ball_child b A ρ j
  | and A B => exact rk_cond_lt A B j
  | or A B => exact rk_cond_lt A B j

end OrdinalAnalysis.KPi.RS
