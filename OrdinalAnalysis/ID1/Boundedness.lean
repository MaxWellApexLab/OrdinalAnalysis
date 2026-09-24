/-
  Boundedness in the operator-controlled calculus `ID₁^∞`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Theorem 5.9 and Exercise 6.6 (after Buchholz 1992,
  Lemma 3.17).

  **Theorem 5.9 (Boundedness).**  `H ⊢^α_ρ Γ, ψ` gives `H ⊢^α_ρ Γ, ψ^β` for every
  `β ∈ H(∅)` with `α ⪯ β ≺ Ω`, where `ψ^β` replaces every literal `I^{≺Ω} t`, `¬I^{≺Ω} t`
  by `I^{≺β} t`, `¬I^{≺β} t` (`cap`).

  The proof is Freund's.  Clause (Fix) cannot occur below `Ω`.  A disjunction
  `I^{≺Ω} t ≃ ⋁_{γ≺Ω} A(t, I^{≺γ})` introduced by (W) with a witness `γ ≺ α ⪯ β` becomes the
  disjunction `I^{≺β} t ≃ ⋁_{γ≺β} A(t, I^{≺γ})` with the same witness and the same premise
  (`A(t, I^{≺γ})^β = A(t, I^{≺γ})` for `γ ≺ Ω`); a conjunction `¬I^{≺Ω} t` introduced by (V)
  becomes `¬I^{≺β} t`, a conjunction over fewer premises.  Every other formula commutes
  with bounding.  Freund argues by induction on the height and applies the induction
  hypothesis twice, once to `ψ` and once to the premise's minor formula `ψ_γ`.  Here the
  induction is on the derivation, and the statement is generalised to bound a whole list `Θ`
  of formulas at once (`bound_aux`): the minor formula of a principal formula in `Θ` is
  added to `Θ`, and the minor formula of any other principal formula is kept unbounded.

  **Exercise 6.6.**  `H ⊢^α_ρ Γ, ¬I^{≺Ω} t` gives `H ⊢^α_ρ Γ, ¬I^{≺δ} t` for every
  `δ ∈ H(∅)`: the conjunction `¬I^{≺Ω} t ≃ ⋀_{γ≺Ω} ¬A(t, I^{≺γ})` is only introduced by (V),
  and restricting its premises to `γ ≺ δ` gives `¬I^{≺δ} t`.  Freund states it for `δ ≺ Ω`;
  the proof works for every stage `δ ⪯ Ω`.

  Both results need of the operator only that it is an operator (monotone), for the
  premises of (V) at `¬I^{≺γ}`, which carry the operator `H[{γ}]`.
-/
import OrdinalAnalysis.ID1.Calculus

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

open LO LO.FirstOrder

/-! ### Bounding of stage atoms -/

/-- The stage that bounding at `β` gives to the stage `α`: `β` if `α = Ω`, else `α`. -/
def capStage (b a : Stage) : Stage := if a = Stage.top then b else a

theorem cap_stageAt' (b a : Stage) {ξ : Type*} {n : ℕ} (t : Semiterm LIinf ξ n) :
    cap b (stageAt a t) = stageAt (capStage b a) t := rfl

theorem cap_nstageAt' (b a : Stage) {ξ : Type*} {n : ℕ} (t : Semiterm LIinf ξ n) :
    cap b (nstageAt a t) = nstageAt (capStage b a) t := rfl

theorem capStage_le (b a : Stage) : (capStage b a).1 ≤ a.1 := by
  unfold capStage
  split_ifs with h
  · rw [h]; exact b.2
  · exact le_rfl

/-- A witness `γ ≺ α` with `α ⪯ β` stays a witness after bounding at `β`. -/
theorem lt_capStage {b a : Stage} {g α : ThetaNote} (hga : g < a.1) (hgα : g < α)
    (hαb : α ≤ b.1) : g < (capStage b a).1 := by
  unfold capStage
  split_ifs
  · exact lt_of_lt_of_le hgα hαb
  · exact hga

theorem Stage.ne_top_of_lt {g a : Stage} (h : g.1 < a.1) : g ≠ Stage.top :=
  Stage.ne_top_of_lt_Omega (lt_of_lt_of_le h a.2)

theorem cap_XinfAt (b : Stage) {ξ : Type*} {n : ℕ} (t : Semiterm LIinf ξ n) :
    cap b (XinfAt t) = XinfAt t := rfl

theorem cap_neg_XinfAt (b : Stage) {ξ : Type*} {n : ℕ} (t : Semiterm LIinf ξ n) :
    cap b (∼(XinfAt t)) = ∼(XinfAt t) := rfl

/-- `k(Θ^β) ⊆ k(Θ) ∪ {β}`. -/
theorem paramsList_map_cap (b : Stage) (Θ : Sequent LIinf) :
    paramsList (Θ.map (cap b)) ⊆ paramsList Θ ∪ {b.1} := by
  rintro x ⟨φ, hφ, hx⟩
  obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hφ
  rcases params_cap b χ hx with h | h
  · exact Or.inl ⟨χ, hχ, h⟩
  · exact Or.inr h

/-! ### Theorem 5.9 -/

section Bound

variable {A : Semisentence LXI 1} {ρ : ThetaNote}

/-- The statement of Theorem 5.9 for a derivation of `Δ`, bounding a list `Θ` of formulas at
the stage `β`. -/
def BoundClaim (A : Semisentence LXI 1) (ρ : ThetaNote) (b : Stage)
    (H : Set ThetaNote → Set ThetaNote) (α : ThetaNote) (Δ : Sequent LIinf) : Prop :=
  ThetaNote.IsOperator H → b.1 ∈ H ∅ → α ≤ b.1 →
    ∀ Θ Γ : Sequent LIinf, Δ ⊆ Θ ++ Γ → paramsList (Θ ++ Γ) ⊆ H ∅ →
      IDerivable A ρ H α (Θ.map (cap b) ++ Γ)

theorem paramsList_capSeq {b : Stage} {H : Set ThetaNote → Set ThetaNote} {Θ Γ : Sequent LIinf}
    (hb : b.1 ∈ H ∅) (hP : paramsList (Θ ++ Γ) ⊆ H ∅) :
    paramsList (Θ.map (cap b) ++ Γ) ⊆ H ∅ := by
  rw [paramsList_append] at hP ⊢
  refine Set.union_subset ((paramsList_map_cap b Θ).trans (Set.union_subset ?_ ?_)) ?_
  · exact Set.subset_union_left.trans hP
  · exact Set.singleton_subset_iff.mpr hb
  · exact Set.subset_union_right.trans hP

theorem mem_capSeq_of_mem_left {b : Stage} {Θ Γ : Sequent LIinf} {χ : Proposition LIinf}
    (h : χ ∈ Θ) : cap b χ ∈ Θ.map (cap b) ++ Γ :=
  List.mem_append_left _ (List.mem_map_of_mem h)

theorem mem_capSeq_of_mem_right {b : Stage} {Θ Γ : Sequent LIinf} {χ : Proposition LIinf}
    (h : χ ∈ Γ) : χ ∈ Θ.map (cap b) ++ Γ :=
  List.mem_append_right _ h

/-- A formula fixed by bounding stays in the sequent. -/
theorem mem_capSeq_of_cap_eq {b : Stage} {Δ Θ Γ : Sequent LIinf} {χ : Proposition LIinf}
    (hχ : χ ∈ Δ) (hΔ : Δ ⊆ Θ ++ Γ) (he : cap b χ = χ) : χ ∈ Θ.map (cap b) ++ Γ := by
  rcases List.mem_append.mp (hΔ hχ) with h | h
  · exact he ▸ mem_capSeq_of_mem_left h
  · exact mem_capSeq_of_mem_right h

/-- The premises: from the claim for a premise `φ :: Δ`, the premise with `φ` unbounded and
with `φ` bounded. -/
theorem bound_prem {b : Stage} {H : Set ThetaNote → Set ThetaNote} {α₀ : ThetaNote}
    {φ : Proposition LIinf} {Δ Θ Γ : Sequent LIinf} (hH : ThetaNote.IsOperator H)
    (hb : b.1 ∈ H ∅) (hα₀ : α₀ ≤ b.1) (d₀ : IDerivable A ρ H α₀ (φ :: Δ))
    (ih₀ : BoundClaim A ρ b H α₀ (φ :: Δ)) (hΔ : Δ ⊆ Θ ++ Γ)
    (hP : paramsList (Θ ++ Γ) ⊆ H ∅) :
    IDerivable A ρ H α₀ (φ :: (Θ.map (cap b) ++ Γ)) ∧
      IDerivable A ρ H α₀ (cap b φ :: (Θ.map (cap b) ++ Γ)) := by
  have hφ : params φ ⊆ H ∅ := d₀.params_head_subset
  constructor
  · have h1 := ih₀ hH hb hα₀ Θ (φ :: Γ)
      (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_append_right _ List.mem_cons_self
        · rcases List.mem_append.mp (hΔ hx) with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))
      (by
        rw [paramsList_append, paramsList_cons]
        rw [paramsList_append] at hP
        exact Set.union_subset (Set.subset_union_left.trans hP)
          (Set.union_subset hφ (Set.subset_union_right.trans hP)))
    refine h1.weaken_seq hH ?_ ?_
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)
    · rw [paramsList_cons]
      exact Set.union_subset hφ (paramsList_capSeq hb hP)
  · exact ih₀ hH hb hα₀ (φ :: Θ) Γ
      (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hΔ hx))
      (by
        show paramsList (φ :: (Θ ++ Γ)) ⊆ H ∅
        rw [paramsList_cons]
        exact Set.union_subset hφ hP)

/-- **Theorem 5.9, generalised to a list `Θ` of bounded formulas.** -/
theorem bound_aux {b : Stage} (hbΩ : b.1 < ThetaNote.Omega) {H : Set ThetaNote → Set ThetaNote}
    {α : ThetaNote} {Δ : Sequent LIinf} (d : IDerivable A ρ H α Δ) :
    BoundClaim A ρ b H α Δ := by
  induction d with
  | literal hα _ hφ hm =>
    intro hH hb hαb Θ Γ hΔ hP
    exact .literal hα (paramsList_capSeq hb hP) hφ
      (mem_capSeq_of_cap_eq hm hΔ (hφ.1.cap_eq b))
  | verum hα _ hm =>
    intro hH hb hαb Θ Γ hΔ hP
    exact .verum hα (paramsList_capSeq hb hP) (mem_capSeq_of_cap_eq hm hΔ rfl)
  | idX t hα _ h1 h2 =>
    intro hH hb hαb Θ Γ hΔ hP
    exact .idX t hα (paramsList_capSeq hb hP) (mem_capSeq_of_cap_eq h1 hΔ (cap_XinfAt b t))
      (mem_capSeq_of_cap_eq h2 hΔ (cap_neg_XinfAt b t))
  | and hα _ hm h0 h1 d0 d1 ih0 ih1 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    have p1 := bound_prem hH hb (le_trans (le_of_lt h1) hαb) d1 ih1 hΔ hP
    rcases List.mem_append.mp (hΔ hm) with h | h
    · exact .and hα (paramsList_capSeq hb hP) (mem_capSeq_of_mem_left (b := b) (Γ := Γ) h)
        h0 h1 p0.2 p1.2
    · exact .and hα (paramsList_capSeq hb hP) (mem_capSeq_of_mem_right h) h0 h1 p0.1 p1.1
  | orL hα _ hm h0 d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    rcases List.mem_append.mp (hΔ hm) with h | h
    · exact .orL hα (paramsList_capSeq hb hP) (mem_capSeq_of_mem_left (b := b) (Γ := Γ) h)
        h0 p0.2
    · exact .orL hα (paramsList_capSeq hb hP) (mem_capSeq_of_mem_right h) h0 p0.1
  | orR hα _ hm h1 h0 d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    rcases List.mem_append.mp (hΔ hm) with h | h
    · exact .orR hα (paramsList_capSeq hb hP) (mem_capSeq_of_mem_left (b := b) (Γ := Γ) h)
        h1 h0 p0.2
    · exact .orR hα (paramsList_capSeq hb hP) (mem_capSeq_of_mem_right h) h1 h0 p0.1
  | @all H α Δ φ f hα _ hm hf d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := fun n => bound_prem hH hb (le_trans (le_of_lt (hf n)) hαb) (d0 n) (ih0 n) hΔ hP
    rcases List.mem_append.mp (hΔ hm) with h | h
    · refine .all (φ := cap b φ) f hα (paramsList_capSeq hb hP)
        (mem_capSeq_of_mem_left (b := b) (Γ := Γ) h) hf fun n => ?_
      have := (p0 n).2
      rwa [cap_subst] at this
    · exact .all f hα (paramsList_capSeq hb hP) (mem_capSeq_of_mem_right h) hf fun n => (p0 n).1
  | @exs H α Δ φ n α₀ hα _ hm hn h0 d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    rcases List.mem_append.mp (hΔ hm) with h | h
    · refine .exs (φ := cap b φ) n hα (paramsList_capSeq hb hP)
        (mem_capSeq_of_mem_left (b := b) (Γ := Γ) h) hn h0 ?_
      have := p0.2
      rwa [cap_subst] at this
    · exact .exs n hα (paramsList_capSeq hb hP) (mem_capSeq_of_mem_right h) hn h0 p0.1
  | @stage H α Δ a t g α₀ hα _ hm hga hgα hgH h0 d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    rcases List.mem_append.mp (hΔ hm) with h | h
    · have hm' := mem_capSeq_of_mem_left (b := b) (Γ := Γ) h
      rw [cap_stageAt'] at hm'
      have hp := p0.2
      rw [cap_unfold_of_ne_top b A (Stage.ne_top_of_lt hga)] at hp
      exact .stage g hα (paramsList_capSeq hb hP) hm' (lt_capStage hga hgα hαb) hgα hgH h0 hp
    · exact .stage g hα (paramsList_capSeq hb hP) (mem_capSeq_of_mem_right h) hga hgα hgH h0
        p0.1
  | @nstage H α Δ a t f hα _ hm hf d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 : ∀ g : Stage, g.1 < a.1 →
        IDerivable A ρ (ThetaNote.adjoin H {g.1}) (f g)
            (∼(unfold A g t) :: (Θ.map (cap b) ++ Γ)) ∧
          IDerivable A ρ (ThetaNote.adjoin H {g.1}) (f g)
            (cap b (∼(unfold A g t)) :: (Θ.map (cap b) ++ Γ)) := by
      intro g hg
      have hsub : H ∅ ⊆ ThetaNote.adjoin H {g.1} ∅ := hH.mono (Set.empty_subset _)
      exact bound_prem (hH.adjoin {g.1}) (hsub hb) (le_trans (le_of_lt (hf g hg)) hαb)
        (d0 g hg) (ih0 g hg) hΔ (hP.trans hsub)
    rcases List.mem_append.mp (hΔ hm) with h | h
    · have hm' := mem_capSeq_of_mem_left (b := b) (Γ := Γ) h
      rw [cap_nstageAt'] at hm'
      refine .nstage f hα (paramsList_capSeq hb hP) hm'
        (fun g hg => hf g (lt_of_lt_of_le hg (capStage_le b a))) fun g hg => ?_
      have hga := lt_of_lt_of_le hg (capStage_le b a)
      have hp := (p0 g hga).2
      rwa [cap_neg, cap_unfold_of_ne_top b A (Stage.ne_top_of_lt hga)] at hp
    · exact .nstage f hα (paramsList_capSeq hb hP) (mem_capSeq_of_mem_right h) hf
        fun g hg => (p0 g hg).1
  | fix _ _ _ hΩ _ _ _ =>
    intro _ _ hαb
    exact absurd (lt_of_le_of_lt (le_trans hΩ hαb) hbΩ) (lt_irrefl _)
  | cut hα _ hr h0 d0 d1 ih0 ih1 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    have p1 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d1 ih1 hΔ hP
    exact .cut hα (paramsList_capSeq hb hP) hr h0 p0.1 p1.1

/-- **Freund, Theorem 5.9 (Boundedness)**: `H ⊢^α_ρ Γ, ψ` gives `H ⊢^α_ρ Γ, ψ^β` for every
`β ∈ H(∅)` with `α ⪯ β ≺ Ω`.  (`H` an operator.) -/
theorem boundedness {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.IsOperator H)
    {α : ThetaNote} {ψ : Proposition LIinf} {Γ : Sequent LIinf} {b : Stage}
    (hbH : b.1 ∈ H ∅) (hαb : α ≤ b.1) (hbΩ : b.1 < ThetaNote.Omega)
    (d : IDerivable A ρ H α (ψ :: Γ)) : IDerivable A ρ H α (cap b ψ :: Γ) :=
  bound_aux hbΩ d hH hbH hαb [ψ] Γ (List.Subset.refl _) d.params_subset

/-- Theorem 5.9 for the formula `A(t, I^{≺Ω})`: it bounds to `A(t, I^{≺β})` (the case used
for clause (Fix) in the proof of Theorem 6.7). -/
theorem boundedness_unfold {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.IsOperator H)
    {α : ThetaNote} {t : SyntacticTerm LIinf} {Γ : Sequent LIinf} {b : Stage}
    (hbH : b.1 ∈ H ∅) (hαb : α ≤ b.1) (hbΩ : b.1 < ThetaNote.Omega)
    (d : IDerivable A ρ H α (unfold A Stage.top t :: Γ)) :
    IDerivable A ρ H α (unfold A b t :: Γ) := by
  have h := boundedness hH hbH hαb hbΩ d
  rwa [cap_unfold_top] at h

/-- Theorem 5.9 for the formula `I t = I^{≺Ω} t`: it bounds to `I^{≺β} t` (the case used for
the cut of rank `Ω` in the proof of Theorem 6.7). -/
theorem boundedness_IOmegaAt {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.IsOperator H)
    {α : ThetaNote} {t : SyntacticTerm LIinf} {Γ : Sequent LIinf} {b : Stage}
    (hbH : b.1 ∈ H ∅) (hαb : α ≤ b.1) (hbΩ : b.1 < ThetaNote.Omega)
    (d : IDerivable A ρ H α (IOmegaAt t :: Γ)) : IDerivable A ρ H α (stageAt b t :: Γ) := by
  have h := boundedness hH hbH hαb hbΩ d
  rwa [cap_IOmegaAt] at h

end Bound

/-! ### Exercise 6.6 -/

section NegStage

variable {A : Semisentence LXI 1} {ρ : ThetaNote}

/-- The statement of Exercise 6.6 for a derivation of `Δ`: the occurrence of `¬I^{≺Ω} t` is
replaced by `¬I^{≺δ} t`. -/
def NegClaim (A : Semisentence LXI 1) (ρ : ThetaNote) (δ : Stage) (t : SyntacticTerm LIinf)
    (H : Set ThetaNote → Set ThetaNote) (α : ThetaNote) (Δ : Sequent LIinf) : Prop :=
  ThetaNote.IsOperator H → δ.1 ∈ H ∅ →
    ∀ Γ : Sequent LIinf, Δ ⊆ nstageAt Stage.top t :: Γ → paramsList Γ ⊆ H ∅ →
      IDerivable A ρ H α (nstageAt δ t :: Γ)

theorem paramsList_negSeq {δ : Stage} {t : SyntacticTerm LIinf}
    {H : Set ThetaNote → Set ThetaNote} {Γ : Sequent LIinf} (hδ : δ.1 ∈ H ∅)
    (hP : paramsList Γ ⊆ H ∅) : paramsList (nstageAt δ t :: Γ) ⊆ H ∅ := by
  rw [paramsList_cons, params_nstageAt]
  exact Set.union_subset (Set.singleton_subset_iff.mpr hδ) hP

theorem neg_prem {δ : Stage} {t : SyntacticTerm LIinf} {H : Set ThetaNote → Set ThetaNote}
    {α₀ : ThetaNote} {φ : Proposition LIinf} {Δ Γ : Sequent LIinf}
    (hH : ThetaNote.IsOperator H) (hδ : δ.1 ∈ H ∅) (d₀ : IDerivable A ρ H α₀ (φ :: Δ))
    (ih₀ : NegClaim A ρ δ t H α₀ (φ :: Δ)) (hΔ : Δ ⊆ nstageAt Stage.top t :: Γ)
    (hP : paramsList Γ ⊆ H ∅) : IDerivable A ρ H α₀ (φ :: nstageAt δ t :: Γ) := by
  have hφ : params φ ⊆ H ∅ := d₀.params_head_subset
  have h1 := ih₀ hH hδ (φ :: Γ)
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · rcases List.mem_cons.mp (hΔ hx) with h | h
        · exact h ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    (by rw [paramsList_cons]; exact Set.union_subset hφ hP)
  refine h1.weaken_seq hH ?_ ?_
  · intro x hx
    simp only [List.mem_cons] at hx ⊢
    tauto
  · rw [paramsList_cons]
    exact Set.union_subset hφ (paramsList_negSeq hδ hP)

/-- A principal formula other than `¬I^{≺Ω} t` stays in the sequent. -/
theorem mem_negSeq {δ : Stage} {t : SyntacticTerm LIinf} {Δ Γ : Sequent LIinf}
    {χ : Proposition LIinf} (hχ : χ ∈ Δ) (hΔ : Δ ⊆ nstageAt Stage.top t :: Γ)
    (hne : negHeadStage χ = none) : χ ∈ nstageAt δ t :: Γ := by
  rcases List.mem_cons.mp (hΔ hχ) with h | h
  · rw [h, negHeadStage_nstageAt] at hne
    exact absurd hne (by simp)
  · exact List.mem_cons_of_mem _ h

theorem neg_aux {δ : Stage} {t : SyntacticTerm LIinf} {H : Set ThetaNote → Set ThetaNote}
    {α : ThetaNote} {Δ : Sequent LIinf} (d : IDerivable A ρ H α Δ) :
    NegClaim A ρ δ t H α Δ := by
  induction d with
  | literal hα _ hφ hm =>
    intro hH hδ Γ hΔ hP
    exact .literal hα (paramsList_negSeq hδ hP) hφ
      (mem_negSeq hm hΔ hφ.1.negHeadStage)
  | verum hα _ hm =>
    intro hH hδ Γ hΔ hP
    exact .verum hα (paramsList_negSeq hδ hP) (mem_negSeq hm hΔ rfl)
  | idX s hα _ h1 h2 =>
    intro hH hδ Γ hΔ hP
    exact .idX s hα (paramsList_negSeq hδ hP) (mem_negSeq h1 hΔ rfl)
      (mem_negSeq h2 hΔ rfl)
  | and hα _ hm h0 h1 d0 d1 ih0 ih1 =>
    intro hH hδ Γ hΔ hP
    exact .and hα (paramsList_negSeq hδ hP) (mem_negSeq hm hΔ rfl) h0 h1
      (neg_prem hH hδ d0 ih0 hΔ hP) (neg_prem hH hδ d1 ih1 hΔ hP)
  | orL hα _ hm h0 d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .orL hα (paramsList_negSeq hδ hP) (mem_negSeq hm hΔ rfl) h0
      (neg_prem hH hδ d0 ih0 hΔ hP)
  | orR hα _ hm h1 h0 d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .orR hα (paramsList_negSeq hδ hP) (mem_negSeq hm hΔ rfl) h1 h0
      (neg_prem hH hδ d0 ih0 hΔ hP)
  | all f hα _ hm hf d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .all f hα (paramsList_negSeq hδ hP) (mem_negSeq hm hΔ rfl) hf
      fun n => neg_prem hH hδ (d0 n) (ih0 n) hΔ hP
  | exs n hα _ hm hn h0 d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .exs n hα (paramsList_negSeq hδ hP) (mem_negSeq hm hΔ rfl) hn h0
      (neg_prem hH hδ d0 ih0 hΔ hP)
  | stage g hα _ hm hga hgα hgH h0 d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .stage g hα (paramsList_negSeq hδ hP) (mem_negSeq hm hΔ rfl) hga hgα
      hgH h0 (neg_prem hH hδ d0 ih0 hΔ hP)
  | @nstage H α Δ a s f hα _ hm hf d0 ih0 =>
    intro hH hδ Γ hΔ hP
    have p0 : ∀ g : Stage, g.1 < a.1 →
        IDerivable A ρ (ThetaNote.adjoin H {g.1}) (f g)
          (∼(unfold A g s) :: nstageAt δ t :: Γ) := by
      intro g hg
      have hsub : H ∅ ⊆ ThetaNote.adjoin H {g.1} ∅ := hH.mono (Set.empty_subset _)
      exact neg_prem (hH.adjoin {g.1}) (hsub hδ) (d0 g hg) (ih0 g hg) hΔ (hP.trans hsub)
    rcases List.mem_cons.mp (hΔ hm) with h | h
    · obtain ⟨rfl, rfl⟩ := nstageAt_inj h
      refine .nstage f hα (paramsList_negSeq hδ hP) List.mem_cons_self
        (fun g hg => hf g (lt_of_lt_of_le hg δ.2)) fun g hg => ?_
      exact p0 g (lt_of_lt_of_le hg δ.2)
    · exact .nstage f hα (paramsList_negSeq hδ hP) (List.mem_cons_of_mem _ h) hf p0
  | fix hα _ hm hΩ h0 d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .fix hα (paramsList_negSeq hδ hP) (mem_negSeq hm hΔ rfl) hΩ h0
      (neg_prem hH hδ d0 ih0 hΔ hP)
  | cut hα _ hr h0 d0 d1 ih0 ih1 =>
    intro hH hδ Γ hΔ hP
    exact .cut hα (paramsList_negSeq hδ hP) hr h0 (neg_prem hH hδ d0 ih0 hΔ hP)
      (neg_prem hH hδ d1 ih1 hΔ hP)

/-- **Freund, Exercise 6.6**: `H ⊢^α_ρ Γ, ¬I^{≺Ω} t` gives `H ⊢^α_ρ Γ, ¬I^{≺δ} t` for every
stage `δ` with `δ ∈ H(∅)` (the source states it for `δ ≺ Ω`).  (`H` an operator.) -/
theorem neg_stage_bound {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.IsOperator H)
    {α : ThetaNote} {t : SyntacticTerm LIinf} {Γ : Sequent LIinf} {δ : Stage}
    (hδ : δ.1 ∈ H ∅) (d : IDerivable A ρ H α (∼(IOmegaAt t) :: Γ)) :
    IDerivable A ρ H α (nstageAt δ t :: Γ) :=
  neg_aux d hH hδ Γ (List.Subset.refl _)
    ((paramsList_mono (List.subset_cons_self _ _)).trans d.params_subset)

end NegStage

end InductiveDef

end OrdinalAnalysis
