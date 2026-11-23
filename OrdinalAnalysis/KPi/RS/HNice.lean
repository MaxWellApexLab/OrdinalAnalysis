module

public import OrdinalAnalysis.KPi.RS.Hcontrol

/-!
# The RS calculus, part 26: arithmetic of nice sets, and `rk A ∈ H` (B92 Lemma 3.6 (d), Lemma 1.9 (a))

* `NiceSet.opow_mem`, `.add`, `.omega_mul`, `.nat_mem` : a nice set contains `0`, `n`, and is closed
  under `ξ ↦ ω^ξ`, `+` and `ξ ↦ ω·ξ` (B92 Lemma 3.6 (d));
* `RSS.rk_form`            : `rk A = ω·ξ + n` with `ξ = 0` or `ξ ∈ k(A)` and `n < ω` (B92 Lemma 1.9 (a));
* `NiceOp.rk_mem`          : consequently `k(A) ⊆ H(X) ⇒ rk A ∈ H(X)`.
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

/-! ### sums of `ω`-powers: addition and `ω·` -/

/-- `Ord.pw l + ω^e` is again a sorted sum, with exponents among those of `l` and `e`. -/
theorem pw_add_single : ∀ (l : List Ordinal.{1}), Ord.Srt l → ∀ e : Ordinal.{1},
    ∃ l1 : List Ordinal.{1}, Ord.Srt l1 ∧ Ord.pw l + ω ^ e = Ord.pw l1 ∧
      ∀ x ∈ l1, x ∈ l ∨ x = e
  | [], _, e => ⟨[e], by simp [Ord.Srt], by simp, by simp⟩
  | a :: l₀, hl, e => by
    rw [Ord.Srt, List.pairwise_cons] at hl
    by_cases hea : e ≤ a
    · obtain ⟨l1, hs1, he1, hm1⟩ := pw_add_single l₀ hl.2 e
      refine ⟨a :: l1, ?_, ?_, ?_⟩
      · rw [Ord.Srt, List.pairwise_cons]
        refine ⟨fun b hb => ?_, hs1⟩
        rcases hm1 b hb with hb | rfl
        · exact hl.1 b hb
        · exact hea
      · rw [Ord.pw_cons, Ord.pw_cons, add_assoc, he1]
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inl (List.mem_cons_self ..)
        · rcases hm1 x hx with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr h
    · replace hea := not_le.1 hea
      have hlt : Ord.pw (a :: l₀) < ω ^ e := by
        refine Ord.pw_lt_of_lt (fun ξ hξ => ?_)
        rcases List.mem_cons.1 hξ with rfl | hξ
        · exact hea
        · exact lt_of_le_of_lt (hl.1 ξ hξ) hea
      refine ⟨[e], by simp [Ord.Srt], ?_, by simp⟩
      simp only [Ord.pw_cons, Ord.pw_nil, add_zero]
      exact Ordinal.add_of_omega0_opow_le hlt le_rfl

theorem pw_add_pw : ∀ (m : List Ordinal.{1}), Ord.Srt m → ∀ l : List Ordinal.{1}, Ord.Srt l →
    ∃ l' : List Ordinal.{1}, Ord.Srt l' ∧ Ord.pw l + Ord.pw m = Ord.pw l' ∧
      ∀ x ∈ l', x ∈ l ∨ x ∈ m
  | [], _, l, hl => ⟨l, hl, by simp, fun x hx => Or.inl hx⟩
  | e :: m', hm, l, hl => by
    rw [Ord.Srt, List.pairwise_cons] at hm
    obtain ⟨l1, hs1, he1, hm1⟩ := pw_add_single l hl e
    obtain ⟨l2, hs2, he2, hm2⟩ := pw_add_pw m' hm.2 l1 hs1
    refine ⟨l2, hs2, ?_, ?_⟩
    · rw [Ord.pw_cons, ← add_assoc, he1, he2]
    · intro x hx
      rcases hm2 x hx with h | h
      · rcases hm1 x h with h | rfl
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem omega_mul_pw (l : List Ordinal.{1}) :
    ω * Ord.pw l = Ord.pw (l.map (fun a => 1 + a)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [Ord.pw_cons, List.map_cons, mul_add, ih]
    congr 1
    rw [Ordinal.opow_add, Ordinal.opow_one]

/-! ### nice sets -/

namespace NiceSet

variable {X : Set Ordinal.{1}}

theorem exps_mem (h : NiceSet X) {l : List Ordinal.{1}} (hs : Ord.Srt l) (hx : Ord.pw l ∈ X) :
    ∀ ξ ∈ l, ξ ∈ X := (h.2 l hs).1 hx

theorem opow_mem (h : NiceSet X) {ξ : Ordinal.{1}} (hξ : ξ ∈ X) : ω ^ ξ ∈ X := by
  have := (h.2 [ξ] (by simp [Ord.Srt])).2 (by simpa using hξ)
  simpa using this

theorem one_mem (h : NiceSet X) : (1 : Ordinal.{1}) ∈ X := by
  simpa using h.opow_mem h.1

theorem add (h : NiceSet X) {x y : Ordinal.{1}} (hx : x ∈ X) (hy : y ∈ X) : x + y ∈ X := by
  obtain ⟨l, hl, rfl⟩ := Ord.exists_pw x
  obtain ⟨m, hm, rfl⟩ := Ord.exists_pw y
  obtain ⟨l', hl', he, hmem⟩ := pw_add_pw m hm l hl
  rw [he]
  refine (h.2 l' hl').2 (fun ξ hξ => ?_)
  rcases hmem ξ hξ with h1 | h1
  · exact h.exps_mem hl hx ξ h1
  · exact h.exps_mem hm hy ξ h1

theorem omega_mul (h : NiceSet X) {x : Ordinal.{1}} (hx : x ∈ X) : ω * x ∈ X := by
  obtain ⟨l, hl, rfl⟩ := Ord.exists_pw x
  rw [omega_mul_pw]
  have hs : Ord.Srt (l.map (fun a => 1 + a)) := by
    rw [Ord.Srt, List.pairwise_map]
    refine List.Pairwise.imp (fun {a b} hab => ?_) hl
    exact add_le_add_right hab 1
  refine (h.2 _ hs).2 (fun ξ hξ => ?_)
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hξ
  exact h.add h.one_mem (h.exps_mem hl hx a ha)

theorem nat_mem (h : NiceSet X) : ∀ n : ℕ, (n : Ordinal.{1}) ∈ X
  | 0 => by simpa using h.1
  | n + 1 => by
    have := h.add (h.nat_mem n) h.one_mem
    simpa using this

theorem add_nat (h : NiceSet X) {x : Ordinal.{1}} (hx : x ∈ X) (n : ℕ) : x + n ∈ X :=
  h.add hx (h.nat_mem n)

end NiceSet

/-! ### the form `rk A = ω·ξ + n` -/

/-- `x = ω·ξ + n` with `ξ = 0` or `ξ ∈ S`, `n < ω`. -/
def Form (S : Set Ordinal.{1}) (x : Ordinal.{1}) : Prop :=
  ∃ (ξ : Ordinal.{1}) (n : ℕ), (ξ = 0 ∨ ξ ∈ S) ∧ x = ω * ξ + n

theorem Form.mono {S S' : Set Ordinal.{1}} (h : S ⊆ S') {x : Ordinal.{1}} (hx : Form S x) :
    Form S' x := by
  obtain ⟨ξ, n, hξ, rfl⟩ := hx
  exact ⟨ξ, n, hξ.imp_right (fun h' => h h'), rfl⟩

theorem Form.add_nat {S : Set Ordinal.{1}} {x : Ordinal.{1}} (hx : Form S x) (c : ℕ) :
    Form S (x + c) := by
  obtain ⟨ξ, n, hξ, rfl⟩ := hx
  exact ⟨ξ, n + c, hξ, by rw [add_assoc, Nat.cast_add]⟩

theorem Form.add_one {S : Set Ordinal.{1}} {x : Ordinal.{1}} (hx : Form S x) : Form S (x + 1) := by
  simpa using hx.add_nat 1

theorem Form.add_two {S : Set Ordinal.{1}} {x : Ordinal.{1}} (hx : Form S x) : Form S (x + 2) := by
  simpa using hx.add_nat 2

theorem Form.add_five {S : Set Ordinal.{1}} {x : Ordinal.{1}} (hx : Form S x) : Form S (x + 5) := by
  simpa using hx.add_nat 5

theorem Form.add_six {S : Set Ordinal.{1}} {x : Ordinal.{1}} (hx : Form S x) : Form S (x + 6) := by
  simpa using hx.add_nat 6

theorem form_lt {ξ η : Ordinal.{1}} (h : ξ < η) (n : ℕ) : ω * ξ + n < ω * η := by
  have h1 : ω * ξ + n < ω * (ξ + 1) := by
    rw [mul_add_one]
    exact addL_lt _ (natCast_lt_omega0 n)
  have h2 : ω * (ξ + 1) ≤ ω * η :=
    mul_le_mul_right (Order.add_one_le_of_lt h) ω
  exact lt_of_lt_of_le h1 h2

theorem Form.max {S : Set Ordinal.{1}} {x y : Ordinal.{1}} (hx : Form S x) (hy : Form S y) :
    Form S (max x y) := by
  obtain ⟨ξ, n, hξ, rfl⟩ := hx
  obtain ⟨η, m, hη, rfl⟩ := hy
  rcases lt_trichotomy ξ η with h | rfl | h
  · rw [max_eq_right ((form_lt h n).le.trans le_self_add)]
    exact ⟨η, m, hη, rfl⟩
  · rcases le_total n m with hnm | hnm
    · have h1 : (n : Ordinal.{1}) ≤ m := by exact_mod_cast hnm
      rw [max_eq_right (addL_le _ h1)]
      exact ⟨ξ, m, hξ, rfl⟩
    · have h1 : (m : Ordinal.{1}) ≤ n := by exact_mod_cast hnm
      rw [max_eq_left (addL_le _ h1)]
      exact ⟨ξ, n, hξ, rfl⟩
  · rw [max_eq_left ((form_lt h m).le.trans le_self_add)]
    exact ⟨ξ, n, hξ, rfl⟩

theorem Form.zero (S : Set Ordinal.{1}) : Form S 0 := ⟨0, 0, Or.inl rfl, by simp⟩

theorem form_ext {n : ℕ} {e : Fin n → Ordinal.{1}} {ek : Fin n → Set Ordinal.{1}}
    (h : ∀ i, Form (ek i) (e i)) : ∀ i, Form (ext ek ∅ i) (ext e 0 i) := by
  intro i
  induction i using Fin.lastCases with
  | last => simpa using Form.zero _
  | cast j => simpa using h j

theorem rkD_form : ∀ {n : ℕ} (A : D0 n) (e : Fin n → Ordinal.{1}) (ek : Fin n → Set Ordinal.{1}),
    (∀ i, Form (ek i) (e i)) → Form (kD A ek) (rkD A e)
  | _, .mem i j, e, ek, h => by
    simp only [rkD, kD]
    exact Form.max (((h i).add_six).mono Set.subset_union_left)
      (((h j).add_one).mono Set.subset_union_right)
  | _, .nmem i j, e, ek, h => by
    simp only [rkD, kD]
    exact Form.max (((h i).add_six).mono Set.subset_union_left)
      (((h j).add_one).mono Set.subset_union_right)
  | _, .ad i, e, ek, h => by
    simp only [rkD, kD]
    exact (h i).add_five
  | _, .nad i, e, ek, h => by
    simp only [rkD, kD]
    exact (h i).add_five
  | _, .and A B, e, ek, h => by
    simp only [rkD, kD]
    exact (Form.max ((rkD_form A e ek h).mono Set.subset_union_left)
      ((rkD_form B e ek h).mono Set.subset_union_right)).add_one
  | _, .or A B, e, ek, h => by
    simp only [rkD, kD]
    exact (Form.max ((rkD_form A e ek h).mono Set.subset_union_left)
      ((rkD_form B e ek h).mono Set.subset_union_right)).add_one
  | _, .bex b A, e, ek, h => by
    simp only [rkD, kD]
    have hb : Form (kBd b ek) (rkBd b e) := by
      cases b with
      | var i => exact h i
      | lev α => exact ⟨α, 0, Or.inr rfl, by simp [rkBd]⟩
    exact Form.max (hb.mono Set.subset_union_left)
      (((rkD_form A _ _ (form_ext h)).add_two).mono Set.subset_union_right)
  | _, .ball b A, e, ek, h => by
    simp only [rkD, kD]
    have hb : Form (kBd b ek) (rkBd b e) := by
      cases b with
      | var i => exact h i
      | lev α => exact ⟨α, 0, Or.inr rfl, by simp [rkBd]⟩
    exact Form.max (hb.mono Set.subset_union_left)
      (((rkD_form A _ _ (form_ext h)).add_two).mono Set.subset_union_right)

theorem PT.rk_form (t : T) : ∃ n : ℕ, t.rk = ω * t.level + n := by
  have h1 : ω * t.level ≤ t.rk := T.K t
  have h2 : t.rk < ω * t.level + ω := by
    have := T.rk_lt t
    rwa [mul_add_one] at this
  have h3 : t.rk - ω * t.level < ω := by
    rw [Ordinal.sub_lt_of_le h1]
    exact h2
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 h3
  exact ⟨n, by rw [← hn, Ordinal.add_sub_cancel_of_le h1]⟩

theorem T.form (t : T) : Form t.k t.rk := by
  obtain ⟨n, hn⟩ := PT.rk_form t
  exact ⟨t.level, n, Or.inr (PT.level_mem_k t.1), hn⟩

/-- B92 Lemma 1.9 (a): `rk A = ω·ξ + n`, `ξ ∈ k(A) ∪ {0}`. -/
theorem RSS.rk_form : ∀ A : RSS, Form A.k A.rk
  | .base φ ρ => by
    simp only [RSS.rk, RSS.k]
    exact rkD_form φ _ _ (fun i => T.form (ρ i))
  | .and A B => by
    simp only [RSS.rk, RSS.k]
    exact (Form.max ((RSS.rk_form A).mono Set.subset_union_left)
      ((RSS.rk_form B).mono Set.subset_union_right)).add_one
  | .or A B => by
    simp only [RSS.rk, RSS.k]
    exact (Form.max ((RSS.rk_form A).mono Set.subset_union_left)
      ((RSS.rk_form B).mono Set.subset_union_right)).add_one

theorem Form.mem_of_nice {X S : Set Ordinal.{1}} (hX : NiceSet X) (hS : S ⊆ X) {x : Ordinal.{1}}
    (hx : Form S x) : x ∈ X := by
  obtain ⟨ξ, n, hξ, rfl⟩ := hx
  have hξX : ξ ∈ X := by
    rcases hξ with rfl | h
    · exact hX.1
    · exact hS h
  exact hX.add_nat (hX.omega_mul hξX) n

/-- `k(A) ⊆ H(X) ⇒ rk A ∈ H(X)`. -/
theorem NiceOp.rk_mem {H : Op} (hH : NiceOp H) {X : Set Ordinal.{1}} {A : RSS}
    (hA : A.k ⊆ H X) : A.rk ∈ H X :=
  Form.mem_of_nice (hH.nice X) hA (RSS.rk_form A)

end OrdinalAnalysis.KPi.RS
