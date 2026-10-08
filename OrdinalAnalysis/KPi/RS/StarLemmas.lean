import OrdinalAnalysis.KPi.RS.StarSim

/-!
# The RS calculus, part 8: derived rules of `RS*` (B92 Lemma 2.4)

The rules are used in *ambient form*: `Star R σ Δ` with a principal sentence `A ∈ Δ`; premises are
sequents `insert (child) Δ` (weakening is free, the principal sentence stays in the context).

* `star_or_of`, `star_and_of`, `star_bor_of`, `star_band_of` : the propositional rules;
* `star_mem_of`, `star_nmem_of`, `star_ad_of`, `star_nad_of`, `star_bex_of`, `star_ball_of` :
  the atomic and bounded-quantifier rules, i.e. `(⋀)*`, `(⋁)*` read through the junctor;
* `star_tnd'` : (TND), `star_bex_lev`, `star_ball_lev` : `(∃^β)`, `(∀^β)` of Lemma 2.4;
* `star_tnd_and` : (TND').
-/

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}} {σ : Ordinal.{1}}

/-- prove `Δ₁ ⊆ Δ₂` for sets built from `insert`, `∪`, singletons. -/
macro "sub_tac" : tactic =>
  `(tactic| (intro z hz; simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff] at hz ⊢; tauto))

/-! ### propositional rules -/

theorem star_and_of {X Y : RSS} {Δ : Set RSS} (hA : RSS.and X Y ∈ Δ)
    (hX : Star R σ (insert X Δ)) (hY : Star R σ (insert Y Δ)) : Star R σ Δ := by
  refine Star.all' hA rfl (fun j => ?_)
  rcases j with ⟨b⟩
  cases b
  · exact Star.mono hY (by sub_tac)
  · exact Star.mono hX (by sub_tac)

theorem star_or_of {X Y : RSS} {Δ : Set RSS} (hA : RSS.or X Y ∈ Δ)
    (h : Star R σ (insert X (insert Y Δ))) : Star R σ Δ := by
  refine Star.ex' hA Set.univ (Set.finite_univ : (Set.univ : Set Two).Finite) rfl
    (fun j _ => Set.empty_subset _) ?_
  refine Star.mono h ?_
  intro Z hZ
  rcases hZ with rfl | rfl | hZ
  · exact Or.inr ⟨⟨true⟩, trivial, rfl⟩
  · exact Or.inr ⟨⟨false⟩, trivial, rfl⟩
  · exact Or.inl hZ

theorem star_or_l {X Y : RSS} {Δ : Set RSS} (hA : RSS.or X Y ∈ Δ)
    (h : Star R σ (insert X Δ)) : Star R σ Δ :=
  star_or_of hA (Star.mono h (fun z hz => by
    rcases hz with rfl | hz
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hz)))

theorem star_or_r {X Y : RSS} {Δ : Set RSS} (hA : RSS.or X Y ∈ Δ)
    (h : Star R σ (insert Y Δ)) : Star R σ Δ :=
  star_or_of hA (Star.mono h (fun z hz => by
    rcases hz with rfl | hz
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hz)))

theorem star_band_of {n : ℕ} {X Y : D0 n} {ρ : Fin n → T} {Δ : Set RSS}
    (hA : RSS.base (D0.and X Y) ρ ∈ Δ)
    (hX : Star R σ (insert (RSS.base X ρ) Δ)) (hY : Star R σ (insert (RSS.base Y ρ) Δ)) :
    Star R σ Δ := by
  refine Star.all' hA rfl (fun j => ?_)
  rcases j with ⟨b⟩
  cases b
  · exact Star.mono hY (by sub_tac)
  · exact Star.mono hX (by sub_tac)

theorem star_bor_of {n : ℕ} {X Y : D0 n} {ρ : Fin n → T} {Δ : Set RSS}
    (hA : RSS.base (D0.or X Y) ρ ∈ Δ)
    (h : Star R σ (insert (RSS.base X ρ) (insert (RSS.base Y ρ) Δ))) : Star R σ Δ := by
  refine Star.ex' hA Set.univ (Set.finite_univ : (Set.univ : Set Two).Finite) rfl
    (fun j _ => Set.empty_subset _) ?_
  refine Star.mono h ?_
  intro Z hZ
  rcases hZ with rfl | rfl | hZ
  · exact Or.inr ⟨⟨true⟩, trivial, rfl⟩
  · exact Or.inr ⟨⟨false⟩, trivial, rfl⟩
  · exact Or.inl hZ

theorem star_bor_l {n : ℕ} {X Y : D0 n} {ρ : Fin n → T} {Δ : Set RSS}
    (hA : RSS.base (D0.or X Y) ρ ∈ Δ) (h : Star R σ (insert (RSS.base X ρ) Δ)) : Star R σ Δ :=
  star_bor_of hA (Star.mono h (fun z hz => by
    rcases hz with rfl | hz
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hz)))

theorem star_bor_r {n : ℕ} {X Y : D0 n} {ρ : Fin n → T} {Δ : Set RSS}
    (hA : RSS.base (D0.or X Y) ρ ∈ Δ) (h : Star R σ (insert (RSS.base Y ρ) Δ)) : Star R σ Δ :=
  star_bor_of hA (Star.mono h (fun z hz => by
    rcases hz with rfl | hz
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hz)))

/-! ### (TND) -/

theorem star_tnd' {A : RSS} {Δ : Set RSS} (h1 : A ∈ Δ) (h2 : A.neg ∈ Δ) : Star R σ Δ := by
  refine Star.mono (star_tnd σ A) ?_
  intro z hz
  rcases hz with rfl | hz
  · exact h2
  · rw [Set.mem_singleton_iff] at hz
    rw [hz]; exact h1

/-- (TND'): `⊢ Γ, B ⇒ ⊢ Γ, ¬A, A ∧ B`. -/
theorem star_tnd_and {A B : RSS} {Δ : Set RSS} (hA : A.neg ∈ Δ) (hAB : RSS.and A B ∈ Δ)
    (h : Star R σ (insert B Δ)) : Star R σ Δ :=
  star_and_of hAB (star_tnd' (Set.mem_insert _ _) (Set.mem_insert_of_mem _ hA)) h

/-! ### atoms and bounded quantifiers -/

theorem star_mem_of {n : ℕ} {i j : Fin n} {ρ : Fin n → T} {Δ : Set RSS}
    (hA : RSS.base (D0.mem i j) ρ ∈ Δ) (t : T) (ht : t.level < (ρ j).level)
    (hk : t.k ⊆ starK R (kSeq Δ))
    (h1 : Star R σ (insert (memInst t (ρ j)) Δ)) (h2 : Star R σ (insert (eqS t (ρ i)) Δ)) :
    Star R σ Δ := by
  refine Star.ex1' hA (⟨t, ht⟩ : Tlt (ρ j).level) rfl hk ?_
  show Star R σ (insert (RSS.and (memInst t (ρ j)) (eqS t (ρ i))) Δ)
  exact star_and_of (Set.mem_insert _ _)
    (Star.mono h1 (by sub_tac))
    (Star.mono h2 (by sub_tac))

theorem star_nmem_of {n : ℕ} {i j : Fin n} {ρ : Fin n → T} {Δ : Set RSS}
    (hA : RSS.base (D0.nmem i j) ρ ∈ Δ)
    (h : ∀ t : T, t.level < (ρ j).level →
      Star R σ (insert (memInst t (ρ j)).neg (insert (eqS t (ρ i)).neg Δ))) : Star R σ Δ := by
  refine Star.all' hA rfl (fun t => ?_)
  show Star R σ (insert (RSS.or (memInst t.1 (ρ j)).neg (eqS t.1 (ρ i)).neg) Δ)
  exact star_or_of (Set.mem_insert _ _) (Star.mono (h t.1 t.2) (by sub_tac))

theorem star_ad_of {n : ℕ} {i : Fin n} {ρ : Fin n → T} {Δ : Set RSS}
    (hA : RSS.base (D0.ad i) ρ ∈ Δ) (κ : Ordinal.{1}) (hκ : κ ∈ R) (hκ0 : 0 < κ)
    (hle : κ ≤ (ρ i).level) (hk : ({κ} : Set Ordinal.{1}) ⊆ starK R (kSeq Δ))
    (h : Star R σ (insert (eqS (T.L κ) (ρ i)) Δ)) : Star R σ Δ :=
  Star.ex1' hA (⟨κ, hκ, hκ0, hle⟩ : AdIdx R (ρ i)) rfl hk h

theorem star_nad_of {n : ℕ} {i : Fin n} {ρ : Fin n → T} {Δ : Set RSS}
    (hA : RSS.base (D0.nad i) ρ ∈ Δ)
    (h : ∀ κ : Ordinal.{1}, κ ∈ R → 0 < κ → κ ≤ (ρ i).level →
      Star R σ (insert (eqS (T.L κ) (ρ i)).neg Δ)) : Star R σ Δ :=
  Star.all' hA rfl (fun κ => h κ.1 κ.2.1 κ.2.2.1 κ.2.2.2)

theorem star_bex_of {n : ℕ} {b : Bd n} {X : D0 (n + 1)} {ρ : Fin n → T} {Δ : Set RSS}
    (hA : RSS.base (D0.bex b X) ρ ∈ Δ) (t : T) (ht : t.level < (resBd b ρ).level)
    (hk : t.k ⊆ starK R (kSeq Δ))
    (h1 : Star R σ (insert (memInst t (resBd b ρ)) Δ))
    (h2 : Star R σ (insert (RSS.base X (ext ρ t)) Δ)) : Star R σ Δ := by
  refine Star.ex1' hA (⟨t, ht⟩ : Tlt (resBd b ρ).level) rfl hk ?_
  show Star R σ (insert (RSS.and (memInst t (resBd b ρ)) (RSS.base X (ext ρ t))) Δ)
  exact star_and_of (Set.mem_insert _ _) (Star.mono h1 (by sub_tac)) (Star.mono h2 (by sub_tac))

theorem star_ball_of {n : ℕ} {b : Bd n} {X : D0 (n + 1)} {ρ : Fin n → T} {Δ : Set RSS}
    (hA : RSS.base (D0.ball b X) ρ ∈ Δ)
    (h : ∀ t : T, t.level < (resBd b ρ).level →
      Star R σ (insert (memInst t (resBd b ρ)).neg (insert (RSS.base X (ext ρ t)) Δ))) :
    Star R σ Δ := by
  refine Star.all' hA rfl (fun t => ?_)
  show Star R σ (insert (RSS.or (memInst t.1 (resBd b ρ)).neg (RSS.base X (ext ρ t.1))) Δ)
  exact star_or_of (Set.mem_insert _ _) (Star.mono (h t.1 t.2) (by sub_tac))

/-- `t ∉ L_0`: an empty conjunction. -/
theorem star_memInst_L' (t : T) (β : Ordinal.{1}) {Δ : Set RSS} :
    Star R σ (insert (memInst t (T.L β)) Δ) :=
  Star.all' (Set.mem_insert _ _) rfl (fun j => absurd j.2 (not_lt_of_ge zero_le))

/-- (∃^β) of Lemma 2.4. -/
theorem star_bex_lev {n : ℕ} {β : Ordinal.{1}} {X : D0 (n + 1)} {ρ : Fin n → T} {Δ : Set RSS}
    (hA : RSS.base (D0.bex (Bd.lev β) X) ρ ∈ Δ) (t : T) (ht : t.level < β)
    (hk : t.k ⊆ starK R (kSeq Δ)) (h : Star R σ (insert (RSS.base X (ext ρ t)) Δ)) :
    Star R σ Δ :=
  star_bex_of hA t ht hk (star_memInst_L' t β) h

/-- (∀^β) of Lemma 2.4. -/
theorem star_ball_lev {n : ℕ} {β : Ordinal.{1}} {X : D0 (n + 1)} {ρ : Fin n → T} {Δ : Set RSS}
    (hA : RSS.base (D0.ball (Bd.lev β) X) ρ ∈ Δ)
    (h : ∀ t : T, t.level < β → Star R σ (insert (RSS.base X (ext ρ t)) Δ)) : Star R σ Δ :=
  star_ball_of hA (fun t ht => Star.mono (h t ht) (by sub_tac))

/-! ### `a ≠ b` -/

/-- the two members `¬ a ⊆ b`, `¬ b ⊆ a` of `[a ≠ b]`, in the form in which they occur as the
members of the junctor of `¬(a = b)`. -/
def Nq1 (a b : T) : RSS := RSS.base (D0.subset 0 1).neg ![a, b]
def Nq2 (a b : T) : RSS := RSS.base (D0.subset 1 0).neg ![a, b]

theorem star_neq_of {a b : T} {Δ : Set RSS} (hA : (eqS a b).neg ∈ Δ)
    (h : Star R σ (insert (Nq1 a b) (insert (Nq2 a b) Δ))) : Star R σ Δ :=
  star_bor_of (n := 2) (X := (D0.subset 0 1).neg) (Y := (D0.subset 1 0).neg) hA h

theorem sim_Nq1 (a b : T) : Sim R (Nq1 a b) (Nq2 b a) := by
  have h := sim_rename (R := R) (D0.subset 0 1).neg ![0, 1] ![1, 0] ![a, b] ![b, a]
    (by intro i; fin_cases i <;> rfl)
  exact h

theorem sim_Nq2 (a b : T) : Sim R (Nq2 a b) (Nq1 b a) := by
  have h := sim_rename (R := R) (D0.subset 1 0).neg ![0, 1] ![1, 0] ![a, b] ![b, a]
    (by intro i; fin_cases i <;> rfl)
  exact h

end OrdinalAnalysis.KPi.RS
