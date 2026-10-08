import OrdinalAnalysis.KPi.RS.Rank

/-!
# The RS calculus, part 3: truth by rank recursion

`RSTrue R A` is defined by well-founded recursion on `rk A` through `expand R A` (B92 Lemma 1.7 (i),(ii)
taken as the definition; no set structure is needed).  It is total because `child_rk_lt`
(B92 Lemma 1.9 (b)) is the termination proof.  The unfolding lemmas `RSTrue_*` give one equation per
shape, and `RSTrue_neg` says that the defined negation is classical negation.
-/

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable (R : Set Ordinal.{1})

/-- **Truth of RS-sentences**, by recursion on the rank through the junctor. -/
noncomputable def RSTrue (A : RSS) : Prop :=
  if (expand R A).isOr = true then ∃ j : (expand R A).J, RSTrue ((expand R A).child j)
  else ∀ j : (expand R A).J, RSTrue ((expand R A).child j)
termination_by A.rk
decreasing_by all_goals exact child_rk_lt R A j

theorem RSTrue_of_or (A : RSS) (h : (expand R A).isOr = true) :
    RSTrue R A ↔ ∃ j : (expand R A).J, RSTrue R ((expand R A).child j) := by
  rw [RSTrue]; simp [h]

theorem RSTrue_of_and (A : RSS) (h : (expand R A).isOr = false) :
    RSTrue R A ↔ ∀ j : (expand R A).J, RSTrue R ((expand R A).child j) := by
  rw [RSTrue]; simp [h]

/-! ### unfolding equations, one per shape -/

theorem RSTrue_and (A B : RSS) : RSTrue R (RSS.and A B) ↔ RSTrue R A ∧ RSTrue R B := by
  rw [RSTrue_of_and R _ rfl]
  constructor
  · intro h; exact ⟨h ⟨true⟩, h ⟨false⟩⟩
  · rintro ⟨h1, h2⟩ ⟨b⟩
    cases b
    · exact h2
    · exact h1

theorem RSTrue_or (A B : RSS) : RSTrue R (RSS.or A B) ↔ RSTrue R A ∨ RSTrue R B := by
  rw [RSTrue_of_or R _ rfl]
  constructor
  · rintro ⟨⟨b⟩, h⟩
    cases b
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact ⟨⟨true⟩, h⟩
    · exact ⟨⟨false⟩, h⟩

theorem RSTrue_band {n : ℕ} (A B : D0 n) (ρ : Fin n → T) :
    RSTrue R (RSS.base (D0.and A B) ρ) ↔ RSTrue R (RSS.base A ρ) ∧ RSTrue R (RSS.base B ρ) := by
  rw [RSTrue_of_and R _ rfl]
  constructor
  · intro h; exact ⟨h ⟨true⟩, h ⟨false⟩⟩
  · rintro ⟨h1, h2⟩ ⟨b⟩
    cases b
    · exact h2
    · exact h1

theorem RSTrue_bor {n : ℕ} (A B : D0 n) (ρ : Fin n → T) :
    RSTrue R (RSS.base (D0.or A B) ρ) ↔ RSTrue R (RSS.base A ρ) ∨ RSTrue R (RSS.base B ρ) := by
  rw [RSTrue_of_or R _ rfl]
  constructor
  · rintro ⟨⟨b⟩, h⟩
    cases b
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact ⟨⟨true⟩, h⟩
    · exact ⟨⟨false⟩, h⟩

theorem RSTrue_mem {n : ℕ} (i j : Fin n) (ρ : Fin n → T) :
    RSTrue R (RSS.base (D0.mem i j) ρ) ↔
      ∃ t : Tlt (ρ j).level, RSTrue R (memInst t.1 (ρ j)) ∧ RSTrue R (eqS t.1 (ρ i)) := by
  rw [RSTrue_of_or R _ rfl]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨t, (RSTrue_and R _ _).1 ht⟩
  · rintro ⟨t, ht⟩; exact ⟨t, (RSTrue_and R _ _).2 ht⟩

theorem RSTrue_nmem {n : ℕ} (i j : Fin n) (ρ : Fin n → T) :
    RSTrue R (RSS.base (D0.nmem i j) ρ) ↔
      ∀ t : Tlt (ρ j).level, RSTrue R (memInst t.1 (ρ j)).neg ∨ RSTrue R (eqS t.1 (ρ i)).neg := by
  rw [RSTrue_of_and R _ rfl]
  constructor
  · intro h t; exact (RSTrue_or R _ _).1 (h t)
  · intro h t; exact (RSTrue_or R _ _).2 (h t)

theorem RSTrue_ad {n : ℕ} (i : Fin n) (ρ : Fin n → T) :
    RSTrue R (RSS.base (D0.ad i) ρ) ↔
      ∃ κ : AdIdx R (ρ i), RSTrue R (eqS (T.L κ.1) (ρ i)) := by
  rw [RSTrue_of_or R _ rfl]
  exact Iff.rfl

theorem RSTrue_nad {n : ℕ} (i : Fin n) (ρ : Fin n → T) :
    RSTrue R (RSS.base (D0.nad i) ρ) ↔
      ∀ κ : AdIdx R (ρ i), RSTrue R (eqS (T.L κ.1) (ρ i)).neg := by
  rw [RSTrue_of_and R _ rfl]
  exact Iff.rfl

theorem RSTrue_bex {n : ℕ} (b : Bd n) (A : D0 (n + 1)) (ρ : Fin n → T) :
    RSTrue R (RSS.base (D0.bex b A) ρ) ↔
      ∃ t : Tlt (resBd b ρ).level,
        RSTrue R (memInst t.1 (resBd b ρ)) ∧ RSTrue R (RSS.base A (ext ρ t.1)) := by
  rw [RSTrue_of_or R _ rfl]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨t, (RSTrue_and R _ _).1 ht⟩
  · rintro ⟨t, ht⟩; exact ⟨t, (RSTrue_and R _ _).2 ht⟩

theorem RSTrue_ball {n : ℕ} (b : Bd n) (A : D0 (n + 1)) (ρ : Fin n → T) :
    RSTrue R (RSS.base (D0.ball b A) ρ) ↔
      ∀ t : Tlt (resBd b ρ).level,
        RSTrue R (memInst t.1 (resBd b ρ)).neg ∨ RSTrue R (RSS.base A (ext ρ t.1)) := by
  rw [RSTrue_of_and R _ rfl]
  constructor
  · intro h t; exact (RSTrue_or R _ _).1 (h t)
  · intro h t; exact (RSTrue_or R _ _).2 (h t)

/-! ### induction on the rank -/

theorem rk_ind {P : RSS → Prop} (H : ∀ A, (∀ B, B.rk < A.rk → P B) → P A) (A : RSS) : P A :=
  (InvImage.wf RSS.rk Ordinal.lt_wf).induction A H

theorem rk_lt_and_left (X Y : RSS) : X.rk < (RSS.and X Y).rk :=
  lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)

theorem rk_lt_and_right (X Y : RSS) : Y.rk < (RSS.and X Y).rk :=
  lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)

theorem rk_lt_or_left (X Y : RSS) : X.rk < (RSS.or X Y).rk :=
  lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)

theorem rk_lt_or_right (X Y : RSS) : Y.rk < (RSS.or X Y).rk :=
  lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)

/-- **Negation is classical negation.** -/
theorem RSTrue_neg : ∀ A : RSS, RSTrue R A.neg ↔ ¬ RSTrue R A := by
  intro A
  refine rk_ind (P := fun A => RSTrue R A.neg ↔ ¬ RSTrue R A) (fun A ih => ?_) A
  cases A with
  | and X Y =>
    show RSTrue R (RSS.or X.neg Y.neg) ↔ _
    rw [RSTrue_or, RSTrue_and, ih X (rk_lt_and_left X Y), ih Y (rk_lt_and_right X Y)]
    exact not_and_or.symm
  | or X Y =>
    show RSTrue R (RSS.and X.neg Y.neg) ↔ _
    rw [RSTrue_and, RSTrue_or, ih X (rk_lt_or_left X Y), ih Y (rk_lt_or_right X Y)]
    exact not_or.symm
  | base φ ρ =>
    cases φ with
    | mem i j =>
      show RSTrue R (RSS.base (D0.nmem i j) ρ) ↔ _
      rw [RSTrue_nmem, RSTrue_mem]
      have hm : ∀ t : Tlt (ρ j).level, (memInst t.1 (ρ j)).rk < (RSS.base (D0.mem i j) ρ).rk :=
        fun t => lt_trans (rk_lt_and_left _ (eqS t.1 (ρ i))) (rk_mem_child ρ i j t)
      have he : ∀ t : Tlt (ρ j).level, (eqS t.1 (ρ i)).rk < (RSS.base (D0.mem i j) ρ).rk :=
        fun t => lt_trans (rk_lt_and_right (memInst t.1 (ρ j)) _) (rk_mem_child ρ i j t)
      simp only [fun t => ih _ (hm t), fun t => ih _ (he t), not_exists]
      exact forall_congr' fun t => not_and_or.symm
    | nmem i j =>
      show RSTrue R (RSS.base (D0.mem i j) ρ) ↔ _
      rw [RSTrue_nmem, RSTrue_mem]
      have hm : ∀ t : Tlt (ρ j).level, (memInst t.1 (ρ j)).rk < (RSS.base (D0.nmem i j) ρ).rk :=
        fun t => lt_trans (rk_lt_and_left _ (eqS t.1 (ρ i))) (rk_mem_child ρ i j t)
      have he : ∀ t : Tlt (ρ j).level, (eqS t.1 (ρ i)).rk < (RSS.base (D0.nmem i j) ρ).rk :=
        fun t => lt_trans (rk_lt_and_right (memInst t.1 (ρ j)) _) (rk_mem_child ρ i j t)
      simp only [fun t => ih _ (hm t), fun t => ih _ (he t)]
      simp only [not_forall, not_or, not_not]
    | ad i =>
      show RSTrue R (RSS.base (D0.nad i) ρ) ↔ _
      rw [RSTrue_nad, RSTrue_ad]
      have hk : ∀ κ : AdIdx R (ρ i), (eqS (T.L κ.1) (ρ i)).rk < (RSS.base (D0.ad i) ρ).rk :=
        fun κ => rk_eqS_lt_ad κ.2.2.1 κ.2.2.2
      simp only [fun κ => ih _ (hk κ), not_exists]
    | nad i =>
      show RSTrue R (RSS.base (D0.ad i) ρ) ↔ _
      rw [RSTrue_nad, RSTrue_ad]
      have hk : ∀ κ : AdIdx R (ρ i), (eqS (T.L κ.1) (ρ i)).rk < (RSS.base (D0.nad i) ρ).rk :=
        fun κ => rk_eqS_lt_ad κ.2.2.1 κ.2.2.2
      simp only [fun κ => ih _ (hk κ), not_forall, not_not]
    | and X Y =>
      show RSTrue R (RSS.base (D0.or X.neg Y.neg) ρ) ↔ _
      have hX : (RSS.base X ρ).rk < (RSS.base (D0.and X Y) ρ).rk :=
        lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
      have hY : (RSS.base Y ρ).rk < (RSS.base (D0.and X Y) ρ).rk :=
        lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
      rw [RSTrue_bor, RSTrue_band]
      exact (or_congr (ih _ hX) (ih _ hY)).trans not_and_or.symm
    | or X Y =>
      show RSTrue R (RSS.base (D0.and X.neg Y.neg) ρ) ↔ _
      have hX : (RSS.base X ρ).rk < (RSS.base (D0.or X Y) ρ).rk :=
        lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
      have hY : (RSS.base Y ρ).rk < (RSS.base (D0.or X Y) ρ).rk :=
        lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
      rw [RSTrue_band, RSTrue_bor]
      exact (and_congr (ih _ hX) (ih _ hY)).trans not_or.symm
    | bex b X =>
      show RSTrue R (RSS.base (D0.ball b X.neg) ρ) ↔ _
      have hm : ∀ t : Tlt (resBd b ρ).level, (memInst t.1 (resBd b ρ)).rk < (RSS.base (D0.bex b X) ρ).rk :=
        fun t => lt_trans (rk_lt_and_left _ (RSS.base X (ext ρ t.1))) (rk_bex_child b X ρ t)
      have hb : ∀ t : Tlt (resBd b ρ).level, (RSS.base X (ext ρ t.1)).rk < (RSS.base (D0.bex b X) ρ).rk :=
        fun t => lt_trans (rk_lt_and_right (memInst t.1 (resBd b ρ)) _) (rk_bex_child b X ρ t)
      have hb' : ∀ t : Tlt (resBd b ρ).level, RSTrue R (RSS.base X.neg (ext ρ t.1)) ↔
          ¬ RSTrue R (RSS.base X (ext ρ t.1)) := fun t => ih _ (hb t)
      rw [RSTrue_ball, RSTrue_bex]
      simp only [fun t => ih _ (hm t), hb', not_exists]
      exact forall_congr' fun t => not_and_or.symm
    | ball b X =>
      show RSTrue R (RSS.base (D0.bex b X.neg) ρ) ↔ _
      have hm : ∀ t : Tlt (resBd b ρ).level, (memInst t.1 (resBd b ρ)).rk < (RSS.base (D0.ball b X) ρ).rk :=
        fun t => lt_of_eq_of_lt (RSS.rk_neg (memInst t.1 (resBd b ρ))).symm
          (lt_trans (rk_lt_or_left (memInst t.1 (resBd b ρ)).neg (RSS.base X (ext ρ t.1)))
            (rk_ball_child b X ρ t))
      have hb : ∀ t : Tlt (resBd b ρ).level, (RSS.base X (ext ρ t.1)).rk < (RSS.base (D0.ball b X) ρ).rk :=
        fun t => lt_trans (rk_lt_or_right (memInst t.1 (resBd b ρ)).neg _) (rk_ball_child b X ρ t)
      have hb' : ∀ t : Tlt (resBd b ρ).level, RSTrue R (RSS.base X.neg (ext ρ t.1)) ↔
          ¬ RSTrue R (RSS.base X (ext ρ t.1)) := fun t => ih _ (hb t)
      rw [RSTrue_ball, RSTrue_bex]
      simp only [fun t => ih _ (hm t), hb', not_forall, not_or, not_not]

end OrdinalAnalysis.KPi.RS
