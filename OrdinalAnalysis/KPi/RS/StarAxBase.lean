module

public import OrdinalAnalysis.KPi.RS.StarEq
public import Mathlib.Data.Fintype.Lattice

/-!
# The RS calculus, part 15: tools for Theorem 2.9

* `Star.ad'`            : `(Ad)*` in ambient form;
* `Bd.shift`, `resBd_shift` : shifting a quantifier bound under a binder;
* `kmem_succ`, `starK_max_succ` : `ξ + 1 ∈ X*`;
* rank bounds below `λ = ω·λ` (`rkD_lt_of_lt`, `T.rk_lt_lam`, `rk_L_lt_lam`);
* `powR_spec`.
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}} {σ : Ordinal.{1}}

/-- `(Ad)*` in ambient form. -/
theorem Star.ad' {n : ℕ} {i : Fin n} (B : D0 n) {Δ : Set RSS} (ρ : Fin n → T)
    (hA : RSS.base (D0.or (D0.nad i) B) ρ ∈ Δ)
    (h : ∀ κ : AdIdx R (ρ i),
      Star R σ (insert (RSS.base B (Function.update ρ i (T.L κ.1))) Δ))
    (hr : (RSS.base B ρ).rk < σ) : Star R σ Δ := by
  have := Star.ad (Γ := Δ) B ρ h hr
  rwa [Set.insert_eq_of_mem hA] at this

/-! ### shifting a bound -/

/-- the same bound, seen under one more binder. -/
def Bd.shift : {n : ℕ} → Bd n → Bd (n + 1)
  | _, .var i => .var i.castSucc
  | _, .lev α => .lev α

theorem resBd_shift {n : ℕ} (b : Bd n) (ρ : Fin n → T) (t : T) :
    resBd b.shift (ext ρ t) = resBd b ρ := by
  cases b with
  | var i => simp [Bd.shift, resBd]
  | lev α => rfl

@[simp] theorem resBd_lev {n : ℕ} (α : Ordinal.{1}) (ρ : Fin n → T) :
    resBd (Bd.lev α) ρ = T.L α := rfl

@[simp] theorem resBd_var {n : ℕ} (i : Fin n) (ρ : Fin n → T) :
    resBd (Bd.var i) ρ = ρ i := rfl

@[simp] theorem ext_one_zero {X : Sort*} (e : Fin 0 → X) (x : X) : ext e x (0 : Fin 1) = x := rfl

@[simp] theorem ext_two_zero {X : Sort*} (e : Fin 1 → X) (x : X) : ext e x (0 : Fin 2) = e 0 :=
  rfl

@[simp] theorem ext_two_one {X : Sort*} (e : Fin 1 → X) (x : X) : ext e x (1 : Fin 2) = x := rfl

theorem level_L (α : Ordinal.{1}) : (T.L α).level = α := rfl

theorem k_L (α : Ordinal.{1}) : (T.L α).k = {α} := rfl

/-! ### `ξ + 1 ∈ X*` -/

theorem kmem_succ {X : Set Ordinal.{1}} {x : Ordinal.{1}} (hx : x ∈ X) :
    x + 1 ∈ starK R X :=
  Or.inl (Or.inr ⟨x, hx, rfl⟩)

theorem starK_max_succ {X : Set Ordinal.{1}} {x y : Ordinal.{1}} (hx : x ∈ X) (hy : y ∈ X) :
    max x y + 1 ∈ starK R X := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]; exact kmem_succ hy
  · rw [max_eq_left h]; exact kmem_succ hx

theorem level_mem_kSeq {t : T} {A : RSS} {Δ : Set RSS} (hA : A ∈ Δ) (h : t.k ⊆ A.k) :
    t.level ∈ kSeq Δ :=
  k_sub_kSeq hA (h (PT.level_mem_k t.1))

theorem omega_mem_starK (X : Set Ordinal.{1}) : (ω : Ordinal.{1}) ∈ starK R X :=
  Or.inl (Or.inl (Or.inr rfl))

theorem zero_mem_starK_of {Δ : Set RSS} {t : T} (hA : (memInst t (T.L 0)).neg ∈ Δ) :
    (0 : Ordinal.{1}) ∈ starK R (kSeq Δ) := by
  refine subset_starK R _ (k_sub_kSeq hA ?_)
  rw [RSS.k_neg]
  show (0 : Ordinal.{1}) ∈ t.k ∪ (T.L 0).k
  exact Or.inr (by simp [k_L])

/-- `¬(t ∈° L_β)` carries the constant `0`. -/
theorem zero_mem_starK_of_memInstL {Δ : Set RSS} {t : T} {β : Ordinal.{1}}
    (hA : (memInst t (T.L β)).neg ∈ Δ) : (0 : Ordinal.{1}) ∈ starK R (kSeq Δ) := by
  refine subset_starK R _ (k_sub_kSeq hA ?_)
  rw [RSS.k_neg]
  show (0 : Ordinal.{1}) ∈ t.k ∪ (T.L 0).k
  exact Or.inr (by simp [k_L])

/-! ### ranks below `λ = ω·λ` -/

theorem exists_bound_lt {n : ℕ} (e : Fin n → Ordinal.{1}) (lam : Ordinal.{1}) (hl : 0 < lam)
    (he : ∀ i, e i < lam) : ∃ B < lam, ∀ i, e i ≤ B := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨0, hl, fun i => (h.false i).elim⟩
  · obtain ⟨i0, hi0⟩ := Finite.exists_max e
    exact ⟨e i0, he i0, hi0⟩

theorem rkD_lt_of_lt {n : ℕ} (A : D0 n) (hA : D0.LevLE 0 A) (e : Fin n → Ordinal.{1})
    (lam : Ordinal.{1}) (hlam : ω * lam = lam) (hl : 0 < lam) (he : ∀ i, e i < lam) :
    rkD A e < lam := by
  obtain ⟨m, hm⟩ := rkD_U A 0 hA
  obtain ⟨B, hBl, hB⟩ := exists_bound_lt e lam hl he
  have h1 := hm e B (by simp) hB
  refine lt_of_le_of_lt h1 ?_
  have := lt_omega_mul_of_lt (show B < ω * lam by rw [hlam]; exact hBl) m
  rwa [hlam] at this

theorem T.rk_lt_lam (a : T) {lam : Ordinal.{1}} (ha : a.level < lam) (hlam : ω * lam = lam) :
    a.rk < lam := by
  have h1 : a.rk < ω * (a.level + 1) := T.rk_lt a
  have h2 : ω * (a.level + 1) ≤ ω * lam := omul_le (Order.add_one_le_of_lt ha)
  rw [hlam] at h2
  exact lt_of_lt_of_le h1 h2

theorem rk_L_lt_lam {κ lam : Ordinal.{1}} (h : κ < lam) (hlam : ω * lam = lam) :
    (T.L κ).rk < lam := by
  have h1 : (T.L κ).rk = ω * κ := by simp [T.rk, PT.rk, T.L]
  rw [h1]
  have h2 : ω * κ < ω * (κ + 1) := omega_mul_lt_succ κ
  have h3 : ω * (κ + 1) ≤ ω * lam := omul_le (Order.add_one_le_of_lt h)
  rw [hlam] at h3
  exact lt_of_lt_of_le h2 h3

/-- the rank of an instance below `λ` whose entries have levels below `λ`. -/
theorem rk_base_lt_lam {n : ℕ} (A : D0 n) (hA : D0.LevLE 0 A) (ρ : Fin n → T)
    (lam : Ordinal.{1}) (hlam : ω * lam = lam) (hl : 0 < lam) (hρ : ∀ i, (ρ i).level < lam) :
    (RSS.base A ρ).rk < lam :=
  rkD_lt_of_lt A hA _ lam hlam hl (fun i => T.rk_lt_lam (ρ i) (hρ i) hlam)

/-! ### `ξ^R` -/

theorem powR_spec (R : Set Ordinal.{1}) (ξ : Ordinal.{1}) (h : ∃ κ ∈ R, ξ < κ) :
    powR R ξ ∈ R ∧ ξ < powR R ξ ∧ ∀ κ ∈ R, ξ < κ → powR R ξ ≤ κ := by
  have hne : {κ | κ ∈ R ∧ ξ < κ}.Nonempty := by
    obtain ⟨κ, h1, h2⟩ := h
    exact ⟨κ, h1, h2⟩
  have hp : powR R ξ = sInf {κ | κ ∈ R ∧ ξ < κ} := by simp [powR, h]
  have hmem := csInf_mem hne
  rw [← hp] at hmem
  exact ⟨hmem.1, hmem.2, fun κ h1 h2 => by rw [hp]; exact csInf_le' ⟨h1, h2⟩⟩

end OrdinalAnalysis.KPi.RS
