module

public import OrdinalAnalysis.KPi.RS.StarEqAdBex

/-!
# The RS calculus, part 14: B92 Lemma 2.7 (equality), its corollary, and Lemma 2.8

* `eq_lemma`        : `EQ R φ ρ ρ₂` for every `φ`, `ρ`, `ρ₂` (induction on `max (rk φ(ρ)) (rk φ(ρ₂))`);
* `star_eq_lemma`   : the form `⊢* [ρ i ≠ ρ₂ i]_i, ¬φ(ρ), φ(ρ₂)`;
* `star_subst_eq`   : the Corollary `⊢* s ≠ t, ¬A(s), A(t)`;
* `star_subst_last` : the same for the last variable of a formula with parameters;
* `star_lem28`      : `⊢* b ∉ a, b ∈° a`.
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}}

theorem rkb_neg {n : ℕ} (φ : D0 n) (ρ : Fin n → T) :
    (RSS.base φ.neg ρ).rk = (RSS.base φ ρ).rk := RSS.rk_neg (RSS.base φ ρ)

theorem rk_bex_neg_ball {n : ℕ} (b : Bd n) (X : D0 (n + 1)) (ρ : Fin n → T) :
    (RSS.base (D0.bex b X.neg) ρ).rk = (RSS.base (D0.ball b X) ρ).rk := by
  simp only [RSS.rk, rkD, rkD_neg]

theorem eq_of_neg {n : ℕ} {φ : D0 n} {ρ ρ2 : Fin n → T} (h : EQ R φ.neg ρ2 ρ) : EQ R φ ρ ρ2 := by
  have := eq_dual h
  rwa [D0.neg_neg] at this

theorem eq_lemma_aux : ∀ M : Ordinal.{1}, ∀ {n : ℕ} (φ : D0 n) (ρ ρ2 : Fin n → T),
    max (RSS.base φ ρ).rk (RSS.base φ ρ2).rk = M → EQ R φ ρ ρ2 := by
  intro M
  induction M using WellFoundedLT.induction with
  | _ M ih =>
  have low : Low R M := fun φ ρ ρ2 h => ih _ h φ ρ ρ2 rfl
  intro n φ ρ ρ2 hM
  have hM1 : (RSS.base φ ρ).rk ≤ M := hM ▸ le_max_left _ _
  have hM2 : (RSS.base φ ρ2).rk ≤ M := hM ▸ le_max_right _ _
  cases φ with
  | mem i j => exact eq_mem low i j ρ ρ2 hM1 hM2
  | nmem i j =>
    refine eq_of_neg (eq_mem low i j ρ2 ρ ?_ ?_)
    · exact le_trans (le_of_eq (rkb_neg (D0.mem i j) ρ2).symm) hM2
    · exact le_trans (le_of_eq (rkb_neg (D0.mem i j) ρ).symm) hM1
  | ad i => exact eq_ad low i ρ ρ2 hM1 hM2
  | nad i =>
    refine eq_of_neg (eq_ad low i ρ2 ρ ?_ ?_)
    · exact le_trans (le_of_eq (rkb_neg (D0.ad i) ρ2).symm) hM2
    · exact le_trans (le_of_eq (rkb_neg (D0.ad i) ρ).symm) hM1
  | and X Y =>
    have hX1 : max (RSS.base X ρ).rk (RSS.base X ρ2).rk < M := by
      refine max_lt (lt_of_lt_of_le ?_ hM1) (lt_of_lt_of_le ?_ hM2) <;>
        exact lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
    have hY1 : max (RSS.base Y ρ).rk (RSS.base Y ρ2).rk < M := by
      refine max_lt (lt_of_lt_of_le ?_ hM1) (lt_of_lt_of_le ?_ hM2) <;>
        exact lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
    exact eq_and (low X ρ ρ2 hX1) (low Y ρ ρ2 hY1)
  | or X Y =>
    have hX1 : max (RSS.base X.neg ρ2).rk (RSS.base X.neg ρ).rk < M := by
      rw [rkb_neg, rkb_neg]
      refine max_lt (lt_of_lt_of_le ?_ hM2) (lt_of_lt_of_le ?_ hM1) <;>
        exact lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
    have hY1 : max (RSS.base Y.neg ρ2).rk (RSS.base Y.neg ρ).rk < M := by
      rw [rkb_neg, rkb_neg]
      refine max_lt (lt_of_lt_of_le ?_ hM2) (lt_of_lt_of_le ?_ hM1) <;>
        exact lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
    exact eq_of_neg (eq_and (low X.neg ρ2 ρ hX1) (low Y.neg ρ2 ρ hY1))
  | bex b X => exact eq_bex low b X ρ ρ2 hM1 hM2
  | ball b X =>
    refine eq_of_neg (eq_bex low b X.neg ρ2 ρ ?_ ?_)
    · exact le_trans (le_of_eq (rk_bex_neg_ball b X ρ2)) hM2
    · exact le_trans (le_of_eq (rk_bex_neg_ball b X ρ)) hM1

/-- **B92 Lemma 2.7** (without the linearity hypothesis, sequents being sets). -/
theorem eq_lemma {n : ℕ} (φ : D0 n) (ρ ρ2 : Fin n → T) : EQ R φ ρ ρ2 :=
  eq_lemma_aux _ φ ρ ρ2 rfl

/-- **B92 Lemma 2.7**: `⊢* [ρ i ≠ ρ₂ i]_i, ¬φ(ρ), φ(ρ₂)`. -/
theorem star_eq_lemma {n : ℕ} (φ : D0 n) (ρ ρ2 : Fin n → T) {Δ : Set RSS} {σ : Ordinal.{1}}
    (h1 : (RSS.base φ ρ).neg ∈ Δ) (h2 : RSS.base φ ρ2 ∈ Δ) (hyp : NeqHyp Δ ρ ρ2) :
    Star R σ Δ :=
  Star.mono_sigma (eq_lemma φ ρ ρ2 Δ h1 h2 hyp) zero_le

/-- **Corollary of B92 Lemma 2.7**: `⊢* s ≠ t, ¬A(s), A(t)` (all entries of the environment
equal to `s`, resp. `t`). -/
theorem star_subst_eq {n : ℕ} (φ : D0 n) (s t : T) {Δ : Set RSS} {σ : Ordinal.{1}}
    (h1 : (RSS.base φ (fun _ => s)).neg ∈ Δ) (h2 : RSS.base φ (fun _ => t) ∈ Δ)
    (hn1 : Nq1 s t ∈ Δ) (hn2 : Nq2 s t ∈ Δ) : Star R σ Δ :=
  star_eq_lemma φ (fun _ => s) (fun _ => t) h1 h2 (fun _ _ => ⟨hn1, hn2⟩)

/-- the Corollary for the last variable, with parameters `ρ`. -/
theorem star_subst_last {n : ℕ} (φ : D0 (n + 1)) (ρ : Fin n → T) (s t : T) {Δ : Set RSS}
    {σ : Ordinal.{1}} (h1 : (RSS.base φ (ext ρ s)).neg ∈ Δ) (h2 : RSS.base φ (ext ρ t) ∈ Δ)
    (hn1 : Nq1 s t ∈ Δ) (hn2 : Nq2 s t ∈ Δ) : Star R σ Δ := by
  refine star_eq_lemma φ (ext ρ s) (ext ρ t) h1 h2 ?_
  intro i
  induction i using Fin.lastCases with
  | last => intro _; simpa using And.intro hn1 hn2
  | cast j => intro h; exact absurd (by simp) h

/-- `⊢* [s ≠ t], ¬(t' ∈° a)(s), (t' ∈° a)(t)`: the corollary for `memInst`. -/
theorem star_memInst_eq (a : T) (s t : T) {Δ : Set RSS} {σ : Ordinal.{1}}
    (h1 : (memInst s a).neg ∈ Δ) (h2 : memInst t a ∈ Δ) (hn1 : Nq1 s t ∈ Δ) (hn2 : Nq2 s t ∈ Δ) :
    Star R σ Δ := by
  rcases a with ⟨a, ha⟩
  cases a with
  | L β =>
    refine star_eq_lemma (D0.nmem 0 1) ![s, T.L 0] ![t, T.L 0] h1 h2 ?_
    intro i
    fin_cases i
    · intro _; simpa using And.intro hn1 hn2
    · intro h; exact absurd rfl h
  | sep β φ a' =>
    refine star_eq_lemma φ _ _ h1 h2 ?_
    intro i
    induction i using Fin.lastCases with
    | last => intro _; simpa using And.intro hn1 hn2
    | cast j => intro h; exact absurd (by simp) h

/-- **B92 Lemma 2.8**: `⊢* b ∉ a, b ∈° a`, in the form: `ρ i = b ∉ ρ j = a` and `b ∈° a` are in `Δ`. -/
theorem star_lem28 {n : ℕ} {i j : Fin n} {ρ : Fin n → T} {Δ : Set RSS} {σ : Ordinal.{1}}
    {a b : T} (hi : ρ i = b) (hj : ρ j = a) (hA : RSS.base (D0.nmem i j) ρ ∈ Δ)
    (hB : memInst b a ∈ Δ) : Star R σ Δ := by
  refine star_nmem' hA hi hj (fun t ht => ?_)
  refine star_neq_of (a := t) (b := b) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) ?_
  refine star_memInst_eq a t b (by simp) (by simp [hB]) (by simp) (by simp)

end OrdinalAnalysis.KPi.RS
