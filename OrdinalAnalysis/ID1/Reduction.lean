/-
  The reduction lemma for the operator-controlled calculus `ID₁^∞`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Exercise 7.1 (b), with Definition 5.1 (disjunctive
  formulas), Definition 5.6 (the calculus) and Exercise 7.1 (a) (inversion).

  **Exercise 7.1 (b).**  Let `H` be nice and let `ψ ≃ ⋁_{γ≺δ} ψ_γ` be disjunctive of rank
  `rk(ψ) = ρ ≠ Ω`.  Then

      H ⊢^α_ρ Γ, ¬ψ   and   H ⊢^β_ρ Γ, ψ   ⇒   H ⊢^{α+β}_ρ Γ.

  The proof is by induction on the derivation of `Γ, ψ`.  If `ψ` is not the principal
  formula of its last clause, the induction hypothesis is applied to the premises and the
  clause is repeated at the height `α + β`; for (V) the premise for `γ` carries the operator
  `H[{γ}]`, to which the derivation of `Γ, ¬ψ` is carried over.  If `ψ` is principal, the
  clause is (W) with a component `ψ_γ` and `γ ∈ H(∅)`; the induction hypothesis gives
  `H ⊢^{α+β₀}_ρ Γ, ψ_γ`, inversion (Exercise 7.1 (a)) gives `H ⊢^α_ρ Γ, ¬ψ_γ`, and a cut on
  `ψ_γ`, of rank `≺ rk(ψ) = ρ`, concludes.  The condition `ρ ≠ Ω` excludes `ψ = I^{≺Ω} t`,
  the principal formula of (Fix), which is disjunctive but has no premise of the form (W).

  **The shape of the cut formula.**  The induction uses only the following properties of
  `ψ` (`RedShape`): `ψ` is not a true literal, not `⊤`, not a conjunction, not a universal
  formula, not `¬I^{≺δ} t`, and not `I^{≺Ω} t`; so `ψ` is never the principal formula of a
  clause (V) or of (Fix).  Every disjunctive formula of rank `≠ Ω` has this shape
  (`Disjunctive.redShape`).  So does each of the literals `X t` and `¬X t` of the free
  predicate, which are neither conjunctive nor disjunctive: when the identity clause for `X`
  has `ψ` as one of its two literals, the other one is `¬ψ ∈ Γ` and the derivation of
  `Γ, ¬ψ` is already a derivation of `Γ`.  Hence for every formula `ψ` of rank `≠ Ω` one of
  `ψ` and `¬ψ` has the shape (`redShape_or_neg`), which is what cut elimination needs
  (`reduction_cut`).

  **Contents.**

    `headKind`, `RedShape`, `Disjunctive`        the shapes of the cut formula
    `IDerivable.red_aux`                         the induction
    `IDerivable.reduction_of_shape`              the reduction lemma for `RedShape ψ`
    `IDerivable.reduction`                       Exercise 7.1 (b)
    `IDerivable.reduction_cut`                   a cut of rank `ρ ≠ Ω` at the height `α + α`
-/
import OrdinalAnalysis.ID1.ReductionAux

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

open LO LO.FirstOrder

/-! ### The shapes of the cut formula -/

/-- The kind of a relation symbol: `none` for arithmetic, `some none` for `X`, and
`some (some α)` for `I^{≺α}`. -/
def relKind : {k : ℕ} → LIinf.Rel k → Option (Option Stage)
  | _, Sum.inl _ => none
  | _, Sum.inr IInfRel.X => some none
  | _, Sum.inr (IInfRel.stage a) => some (some a)

/-- The outermost symbol of a formula, with the kind of its relation symbol. -/
def headKind {ξ : Type*} : {n : ℕ} → Semiformula LIinf ξ n → ℕ × Option (Option Stage)
  | _, .verum => (0, none)
  | _, .falsum => (1, none)
  | _, .rel r _ => (2, relKind r)
  | _, .nrel r _ => (3, relKind r)
  | _, .and _ _ => (4, none)
  | _, .or _ _ => (5, none)
  | _, .all _ => (6, none)
  | _, .exs _ => (7, none)

/-- A true literal is an atom or negated atom of arithmetic. -/
theorem TrueLit.headKind {φ : Proposition LIinf} (h : TrueLit φ) :
    InductiveDef.headKind φ = (2, none) ∨ InductiveDef.headKind φ = (3, none) := by
  obtain ⟨⟨k, r, v, (rfl | rfl), -⟩, -⟩ := h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The shape of the cut formula** in the reduction lemma: `ψ` is never the principal
formula of a clause (V) or of (Fix). -/
structure RedShape (ψ : Proposition LIinf) : Prop where
  not_lit : ¬TrueLit ψ
  ne_verum : ψ ≠ ⊤
  ne_and : ∀ φ₀ φ₁ : Proposition LIinf, ψ ≠ φ₀ ⋏ φ₁
  ne_all : ∀ φ : Semiproposition LIinf 1, ψ ≠ ∀¹ φ
  ne_nstage : ∀ (a : Stage) (t : SyntacticTerm LIinf), ψ ≠ nstageAt a t
  ne_IOmega : ∀ t : SyntacticTerm LIinf, ψ ≠ IOmegaAt t

/-- The shape is read off the outermost symbol. -/
theorem RedShape.of_headKind {ψ : Proposition LIinf} (hl : ¬TrueLit ψ)
    (h0 : headKind ψ ≠ (0, none)) (h4 : (headKind ψ).1 ≠ 4) (h6 : (headKind ψ).1 ≠ 6)
    (hn : ∀ a : Stage, headKind ψ ≠ (3, some (some a)))
    (hI : headKind ψ ≠ (2, some (some Stage.top))) : RedShape ψ where
  not_lit := hl
  ne_verum := fun h => h0 (by rw [h]; rfl)
  ne_and := fun _ _ h => h4 (by rw [h]; rfl)
  ne_all := fun _ h => h6 (by rw [h]; rfl)
  ne_nstage := fun a _ h => hn a (by rw [h]; rfl)
  ne_IOmega := fun _ h => hI (by rw [h]; rfl)

/-- **The disjunctive formulas** of Freund, Definition 5.1: the false literals of arithmetic
(the empty disjunctions, also `⊥`), `ψ₀ ∨ ψ₁ ≃ ⋁_{i≺2} ψ_i`, `∃x ψ(x) ≃ ⋁_{n≺ω} ψ(n̄)` and
`I^{≺δ} t ≃ ⋁_{γ≺δ} A(t, I^{≺γ})`. -/
def Disjunctive (ψ : Proposition LIinf) : Prop :=
  (IsArithLit ψ ∧ ¬TrueN ψ) ∨ ψ = ⊥ ∨ (∃ φ₀ φ₁ : Proposition LIinf, ψ = φ₀ ⋎ φ₁) ∨
    (∃ φ : Semiproposition LIinf 1, ψ = ∃¹ φ) ∨
    (∃ (a : Stage) (t : SyntacticTerm LIinf), ψ = stageAt a t)

/-- **A disjunctive formula of rank `≠ Ω` has the shape of the reduction lemma**: it is not
`I^{≺Ω} t`, and no disjunctive formula is conjunctive. -/
theorem Disjunctive.redShape {ψ : Proposition LIinf} (h : Disjunctive ψ)
    (hΩ : rk ψ ≠ ThetaNote.Omega) : RedShape ψ := by
  rcases h with ⟨hl, hT⟩ | rfl | ⟨φ₀, φ₁, rfl⟩ | ⟨φ, rfl⟩ | ⟨a, t, rfl⟩
  · obtain ⟨k, r, v, (rfl | rfl), -⟩ := hl
    · exact RedShape.of_headKind (fun h => hT h.2) (by simp [headKind, relKind])
        (by simp [headKind]) (by simp [headKind]) (by simp [headKind])
        (by simp [headKind, relKind])
    · exact RedShape.of_headKind (fun h => hT h.2) (by simp [headKind, relKind])
        (by simp [headKind]) (by simp [headKind]) (by simp [headKind, relKind])
        (by simp [headKind])
  · refine RedShape.of_headKind ?_ (by simp [headKind]) (by simp [headKind])
      (by simp [headKind]) (by simp [headKind]) (by simp [headKind])
    intro h; rcases h.headKind with h | h <;> simp [headKind] at h
  · refine RedShape.of_headKind ?_ (by simp [headKind]) (by simp [headKind])
      (by simp [headKind]) (by simp [headKind]) (by simp [headKind])
    intro h; rcases h.headKind with h | h <;> simp [headKind] at h
  · refine RedShape.of_headKind ?_ (by simp [headKind]) (by simp [headKind])
      (by simp [headKind]) (by simp [headKind]) (by simp [headKind])
    intro h; rcases h.headKind with h | h <;> simp [headKind] at h
  · have ha : a ≠ Stage.top := by
      rintro rfl; exact hΩ (rk_IOmegaAt t)
    refine RedShape.of_headKind ?_ (by simp [headKind, stageAt, relKind])
      (by simp [headKind, stageAt]) (by simp [headKind, stageAt])
      (by simp [headKind, stageAt, relKind]) (by simp [headKind, stageAt, relKind, ha])
    intro h; rcases h.headKind with h | h <;> simp [headKind, stageAt, relKind] at h

/-- **For a formula of rank `≠ Ω`, the formula or its negation has the shape of the
reduction lemma.** -/
theorem redShape_or_neg (ψ : Proposition LIinf) (hΩ : rk ψ ≠ ThetaNote.Omega) :
    RedShape ψ ∨ RedShape (∼ψ) := by
  have nl : ∀ φ : Proposition LIinf, (headKind φ).2 ≠ none → ¬TrueLit φ := by
    intro φ h hT
    rcases hT.headKind with e | e <;> rw [e] at h <;> exact h rfl
  cases ψ with
  | verum =>
    right
    change RedShape (⊥ : Proposition LIinf)
    refine RedShape.of_headKind ?_ (by simp [headKind]) (by simp [headKind])
      (by simp [headKind]) (by simp [headKind]) (by simp [headKind])
    intro h; rcases h.headKind with h | h <;> simp [headKind] at h
  | falsum =>
    left
    refine RedShape.of_headKind ?_ (by simp [headKind]) (by simp [headKind])
      (by simp [headKind]) (by simp [headKind]) (by simp [headKind])
    intro h; rcases h.headKind with h | h <;> simp [headKind] at h
  | rel r v =>
    rcases r with r | r
    · by_cases hT : TrueLit (Semiformula.rel (Sum.inl r : LIinf.Rel _) v)
      · right
        change RedShape (Semiformula.nrel (Sum.inl r : LIinf.Rel _) v)
        exact RedShape.of_headKind hT.not_neg (by simp [headKind, relKind])
          (by simp [headKind]) (by simp [headKind]) (by simp [headKind, relKind])
          (by simp [headKind])
      · left
        exact RedShape.of_headKind hT (by simp [headKind, relKind])
          (by simp [headKind]) (by simp [headKind]) (by simp [headKind])
          (by simp [headKind, relKind])
    · cases r with
      | X =>
        left
        exact RedShape.of_headKind (nl _ (by simp [headKind, relKind]))
          (by simp [headKind, relKind]) (by simp [headKind]) (by simp [headKind])
          (by simp [headKind]) (by simp [headKind, relKind])
      | stage a =>
        have ha : a ≠ Stage.top := by
          rintro rfl
          exact hΩ ((rk_rel _ v).trans ThetaNote.omegaMul_Omega)
        left
        exact RedShape.of_headKind (nl _ (by simp [headKind, relKind]))
          (by simp [headKind, relKind]) (by simp [headKind]) (by simp [headKind])
          (by simp [headKind]) (by simp [headKind, relKind, ha])
  | nrel r v =>
    rcases r with r | r
    · by_cases hT : TrueLit (Semiformula.nrel (Sum.inl r : LIinf.Rel _) v)
      · right
        change RedShape (Semiformula.rel (Sum.inl r : LIinf.Rel _) v)
        exact RedShape.of_headKind hT.not_neg (by simp [headKind, relKind])
          (by simp [headKind]) (by simp [headKind]) (by simp [headKind])
          (by simp [headKind, relKind])
      · left
        exact RedShape.of_headKind hT (by simp [headKind, relKind])
          (by simp [headKind]) (by simp [headKind]) (by simp [headKind, relKind])
          (by simp [headKind])
    · cases r with
      | X =>
        left
        exact RedShape.of_headKind (nl _ (by simp [headKind, relKind]))
          (by simp [headKind, relKind]) (by simp [headKind]) (by simp [headKind])
          (by simp [headKind, relKind]) (by simp [headKind])
      | stage a =>
        have ha : a ≠ Stage.top := by
          rintro rfl
          exact hΩ ((rk_nrel _ v).trans ThetaNote.omegaMul_Omega)
        right
        change RedShape (Semiformula.rel (Sum.inr (IInfRel.stage a) : LIinf.Rel _) v)
        exact RedShape.of_headKind (nl _ (by simp [headKind, relKind]))
          (by simp [headKind, relKind]) (by simp [headKind]) (by simp [headKind])
          (by simp [headKind]) (by simp [headKind, relKind, ha])
  | and φ₀ φ₁ =>
    right
    change RedShape (∼φ₀ ⋎ ∼φ₁)
    refine RedShape.of_headKind ?_ (by simp [headKind]) (by simp [headKind])
      (by simp [headKind]) (by simp [headKind]) (by simp [headKind])
    intro h; rcases h.headKind with h | h <;> simp [headKind] at h
  | or φ₀ φ₁ =>
    left
    refine RedShape.of_headKind ?_ (by simp [headKind]) (by simp [headKind])
      (by simp [headKind]) (by simp [headKind]) (by simp [headKind])
    intro h; rcases h.headKind with h | h <;> simp [headKind] at h
  | all φ =>
    right
    change RedShape (∃¹ ∼φ)
    refine RedShape.of_headKind ?_ (by simp [headKind]) (by simp [headKind])
      (by simp [headKind]) (by simp [headKind]) (by simp [headKind])
    intro h; rcases h.headKind with h | h <;> simp [headKind] at h
  | exs φ =>
    left
    refine RedShape.of_headKind ?_ (by simp [headKind]) (by simp [headKind])
      (by simp [headKind]) (by simp [headKind]) (by simp [headKind])
    intro h; rcases h.headKind with h | h <;> simp [headKind] at h

theorem XinfAt_ne_neg (t : SyntacticTerm LIinf) : XinfAt t ≠ ∼(XinfAt t) := by
  intro h
  have e : ∼(XinfAt t) = Semiformula.nrel (Sum.inr IInfRel.X : LIinf.Rel 1) ![t] :=
    Semiformula.neg_rel _ _
  rw [e] at h
  cases h

/-! ### Exercise 7.1 (b) -/

namespace IDerivable

variable {A : Semisentence LXI 1} {ρ : ThetaNote}

theorem mem_of_mem_ne {θ ψ : Proposition LIinf} {Δ Γ : Sequent LIinf} (hθ : θ ∈ Δ)
    (hΔ : Δ ⊆ ψ :: Γ) (hne : θ ≠ ψ) : θ ∈ Γ := by
  rcases List.mem_cons.mp (hΔ hθ) with h | h
  · exact absurd h hne
  · exact h

theorem params_tail_subset {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote}
    {φ : Proposition LIinf} {Γ : Sequent LIinf} (d : IDerivable A ρ H α (φ :: Γ)) :
    paramsList Γ ⊆ H ∅ := by
  have h := d.params_subset
  rw [paramsList_cons] at h
  exact Set.subset_union_right.trans h

/-- The statement of the reduction lemma for a derivation of `Δ ⊆ Γ, ψ`, with the
derivation of `Γ, ¬ψ` of height `α`. -/
def RedClaim (A : Semisentence LXI 1) (ρ : ThetaNote) (ψ : Proposition LIinf) (α : ThetaNote)
    (H : Set ThetaNote → Set ThetaNote) (β : ThetaNote) (Δ : Sequent LIinf) : Prop :=
  ThetaNote.Nice H → ∀ Γ : Sequent LIinf, Δ ⊆ ψ :: Γ → IDerivable A ρ H α (∼ψ :: Γ) →
    IDerivable A ρ H (α + β) Γ

/-- A premise `Δ, φ` of height `β₀` becomes `Γ, φ` of height `α + β₀`. -/
theorem red_prem {ψ φ : Proposition LIinf} {H : Set ThetaNote → Set ThetaNote}
    {α β₀ : ThetaNote} {Δ Γ : Sequent LIinf} (hH : ThetaNote.Nice H)
    (d₀ : IDerivable A ρ H β₀ (φ :: Δ)) (ih₀ : RedClaim A ρ ψ α H β₀ (φ :: Δ))
    (hΔ : Δ ⊆ ψ :: Γ) (e : IDerivable A ρ H α (∼ψ :: Γ)) :
    IDerivable A ρ H (α + β₀) (φ :: Γ) := by
  refine ih₀ hH (φ :: Γ) ?_ ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rcases List.mem_cons.mp (hΔ hx) with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  · refine e.weaken_seq hH.isOperator ?_ ?_
    · intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
    · have h := e.params_subset
      rw [paramsList_cons] at h
      rw [paramsList_cons, paramsList_cons]
      exact Set.union_subset (Set.subset_union_left.trans h)
        (Set.union_subset d₀.params_head_subset (Set.subset_union_right.trans h))

/-- The principal case: a cut on the component `χ = ψ_γ`, of rank `≺ ρ`. -/
theorem red_cut {χ : Proposition LIinf} {H : Set ThetaNote → Set ThetaNote}
    {α β β₀ : ThetaNote} {Γ : Sequent LIinf} (hH : ThetaNote.Nice H) (hr : rk χ < ρ)
    (hβ : β₀ < β) (hβH : β ∈ H ∅) (d : IDerivable A ρ H (α + β₀) (χ :: Γ))
    (e : IDerivable A ρ H α (∼χ :: Γ)) : IDerivable A ρ H (α + β) Γ :=
  .cut (hH.add_mem e.height_mem hβH) e.params_tail_subset hr
    (ThetaNote.add_lt_add_left α hβ) d
    (e.mono_height (ThetaNote.le_self_add_red α β₀) d.height_mem)

/-- **Exercise 7.1 (b), the induction** on the derivation of `Δ ⊆ Γ, ψ`. -/
theorem red_aux {ψ : Proposition LIinf} (hs : RedShape ψ) (hρ : rk ψ ≤ ρ) {α : ThetaNote}
    {H : Set ThetaNote → Set ThetaNote} {β : ThetaNote} {Δ : Sequent LIinf}
    (d : IDerivable A ρ H β Δ) : RedClaim A ρ ψ α H β Δ := by
  induction d with
  | literal hβ _ hφ hm =>
    intro hH Γ hΔ e
    exact .literal (hH.add_mem e.height_mem hβ) e.params_tail_subset hφ
      (mem_of_mem_ne hm hΔ fun h => hs.not_lit (h ▸ hφ))
  | verum hβ _ hm =>
    intro hH Γ hΔ e
    exact .verum (hH.add_mem e.height_mem hβ) e.params_tail_subset
      (mem_of_mem_ne hm hΔ fun h => hs.ne_verum h.symm)
  | @idX H' β' Δ' t hβ _ h1 h2 =>
    intro hH Γ hΔ e
    have hαβ := hH.add_mem e.height_mem hβ
    by_cases e1 : XinfAt t = ψ
    · subst e1
      have hm : ∼(XinfAt t) ∈ Γ := mem_of_mem_ne h2 hΔ (XinfAt_ne_neg t).symm
      exact e.weaken hH.isOperator (ThetaNote.le_self_add_red α _)
        (List.cons_subset.mpr ⟨hm, List.Subset.refl _⟩) hαβ e.params_tail_subset
    · by_cases e2 : ∼(XinfAt t) = ψ
      · subst e2
        have hm : XinfAt t ∈ Γ := mem_of_mem_ne h1 hΔ (XinfAt_ne_neg t)
        have e : IDerivable A ρ H' α (XinfAt t :: Γ) := by simpa using e
        exact e.weaken hH.isOperator (ThetaNote.le_self_add_red α _)
          (List.cons_subset.mpr ⟨hm, List.Subset.refl _⟩) hαβ e.params_tail_subset
      · exact .idX t hαβ e.params_tail_subset (mem_of_mem_ne h1 hΔ e1)
          (mem_of_mem_ne h2 hΔ e2)
  | and hβ _ hm h0 h1 d0 d1 ih0 ih1 =>
    intro hH Γ hΔ e
    exact .and (hH.add_mem e.height_mem hβ) e.params_tail_subset
      (mem_of_mem_ne hm hΔ fun h => hs.ne_and _ _ h.symm)
      (ThetaNote.add_lt_add_left α h0) (ThetaNote.add_lt_add_left α h1)
      (red_prem hH d0 ih0 hΔ e) (red_prem hH d1 ih1 hΔ e)
  | @orL H β Δ φ₀ φ₁ β₀ hβ _ hm h0 d0 ih0 =>
    intro hH Γ hΔ e
    have p0 := red_prem hH d0 ih0 hΔ e
    by_cases he : φ₀ ⋎ φ₁ = ψ
    · subst he
      have e' : IDerivable A ρ H α (∼φ₀ ⋏ ∼φ₁ :: Γ) := by simpa using e
      exact red_cut hH (lt_of_lt_of_le (rk_left_lt_or φ₀ φ₁) hρ) h0 hβ p0
        (inv_and_left hH.isOperator e')
    · exact .orL (hH.add_mem e.height_mem hβ) e.params_tail_subset (mem_of_mem_ne hm hΔ he)
        (ThetaNote.add_lt_add_left α h0) p0
  | @orR H β Δ φ₀ φ₁ β₀ hβ _ hm h1 h0 d0 ih0 =>
    intro hH Γ hΔ e
    have p0 := red_prem hH d0 ih0 hΔ e
    by_cases he : φ₀ ⋎ φ₁ = ψ
    · subst he
      have e' : IDerivable A ρ H α (∼φ₀ ⋏ ∼φ₁ :: Γ) := by simpa using e
      exact red_cut hH (lt_of_lt_of_le (rk_right_lt_or φ₀ φ₁) hρ) h0 hβ p0
        (inv_and_right hH.isOperator e')
    · exact .orR (hH.add_mem e.height_mem hβ) e.params_tail_subset (mem_of_mem_ne hm hΔ he)
        (lt_of_lt_of_le h1 (ThetaNote.le_add_left α β)) (ThetaNote.add_lt_add_left α h0) p0
  | all f hβ _ hm hf d0 ih0 =>
    intro hH Γ hΔ e
    exact .all (fun n => α + f n) (hH.add_mem e.height_mem hβ) e.params_tail_subset
      (mem_of_mem_ne hm hΔ fun h => hs.ne_all _ h.symm)
      (fun n => ThetaNote.add_lt_add_left α (hf n)) fun n => red_prem hH (d0 n) (ih0 n) hΔ e
  | @exs H β Δ φ n β₀ hβ _ hm hn h0 d0 ih0 =>
    intro hH Γ hΔ e
    have p0 := red_prem hH d0 ih0 hΔ e
    by_cases he : (∃¹ φ) = ψ
    · subst he
      have e' : IDerivable A ρ H α ((∀¹ ∼φ) :: Γ) := by simpa using e
      have e'' : IDerivable A ρ H α (∼(φ/[numI n]) :: Γ) := by
        simpa using inv_all hH.isOperator n e'
      exact red_cut hH (lt_of_lt_of_le (rk_subst_lt_exs φ (numI n)) hρ) h0 hβ p0 e''
    · exact .exs n (hH.add_mem e.height_mem hβ) e.params_tail_subset (mem_of_mem_ne hm hΔ he)
        (lt_of_lt_of_le hn (ThetaNote.le_add_left α β)) (ThetaNote.add_lt_add_left α h0) p0
  | @stage H β Δ a t g β₀ hβ _ hm hga hgβ hgH h0 d0 ih0 =>
    intro hH Γ hΔ e
    have p0 := red_prem hH d0 ih0 hΔ e
    by_cases he : stageAt a t = ψ
    · subst he
      have e' : IDerivable A ρ H α (nstageAt a t :: Γ) := by simpa using e
      exact red_cut hH (lt_of_lt_of_le (rk_unfold_lt_stageAt A hga t t) hρ) h0 hβ p0
        (inv_nstage hH.isOperator hga hgH e')
    · exact .stage g (hH.add_mem e.height_mem hβ) e.params_tail_subset
        (mem_of_mem_ne hm hΔ he) hga (lt_of_lt_of_le hgβ (ThetaNote.le_add_left α β)) hgH
        (ThetaNote.add_lt_add_left α h0) p0
  | nstage f hβ _ hm hf d0 ih0 =>
    intro hH Γ hΔ e
    exact .nstage (fun g => α + f g) (hH.add_mem e.height_mem hβ) e.params_tail_subset
      (mem_of_mem_ne hm hΔ fun h => hs.ne_nstage _ _ h.symm)
      (fun g hg => ThetaNote.add_lt_add_left α (hf g hg)) fun g hg =>
        red_prem (hH.adjoin {g.1}) (d0 g hg) (ih0 g hg) hΔ (e.adjoin hH.isOperator {g.1})
  | fix hβ _ hm hΩ h0 d0 ih0 =>
    intro hH Γ hΔ e
    exact .fix (hH.add_mem e.height_mem hβ) e.params_tail_subset
      (mem_of_mem_ne hm hΔ fun h => hs.ne_IOmega _ h.symm)
      (le_trans hΩ (ThetaNote.le_add_left α _)) (ThetaNote.add_lt_add_left α h0)
      (red_prem hH d0 ih0 hΔ e)
  | cut hβ _ hr h0 d0 d1 ih0 ih1 =>
    intro hH Γ hΔ e
    exact .cut (hH.add_mem e.height_mem hβ) e.params_tail_subset hr
      (ThetaNote.add_lt_add_left α h0) (red_prem hH d0 ih0 hΔ e) (red_prem hH d1 ih1 hΔ e)

/-- **The reduction lemma** for a cut formula of the shape `RedShape`, of rank `⪯ ρ`. -/
theorem reduction_of_shape {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.Nice H)
    {ψ : Proposition LIinf} (hs : RedShape ψ) (hρ : rk ψ ≤ ρ) {α β : ThetaNote}
    {Γ : Sequent LIinf} (e : IDerivable A ρ H α (∼ψ :: Γ))
    (d : IDerivable A ρ H β (ψ :: Γ)) : IDerivable A ρ H (α + β) Γ :=
  red_aux hs hρ d hH Γ (List.Subset.refl _) e

/-- **Freund, Exercise 7.1 (b) (Reduction)**: for a nice operator `H` and a disjunctive
formula `ψ` of rank `rk(ψ) = ρ ≠ Ω`,

    `H ⊢^α_ρ Γ, ¬ψ` and `H ⊢^β_ρ Γ, ψ` give `H ⊢^{α+β}_ρ Γ`. -/
theorem reduction {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.Nice H)
    {ψ : Proposition LIinf} (hψ : Disjunctive ψ) (hrk : rk ψ = ρ) (hρ : ρ ≠ ThetaNote.Omega)
    {α β : ThetaNote} {Γ : Sequent LIinf} (e : IDerivable A ρ H α (∼ψ :: Γ))
    (d : IDerivable A ρ H β (ψ :: Γ)) : IDerivable A ρ H (α + β) Γ :=
  reduction_of_shape hH (hψ.redShape (hrk ▸ hρ)) (le_of_eq hrk) e d

/-- **A cut of rank `ρ ≠ Ω` is reduced** (Exercise 7.1 (b), applied to `ψ` or to `¬ψ`,
whichever has the shape of the reduction lemma): `H ⊢^α_ρ Γ, ψ` and `H ⊢^α_ρ Γ, ¬ψ` with
`rk(ψ) = ρ ≠ Ω` give `H ⊢^{α+α}_ρ Γ`. -/
theorem reduction_cut {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.Nice H)
    {ψ : Proposition LIinf} (hrk : rk ψ = ρ) (hρ : ρ ≠ ThetaNote.Omega) {α : ThetaNote}
    {Γ : Sequent LIinf} (d₀ : IDerivable A ρ H α (ψ :: Γ))
    (d₁ : IDerivable A ρ H α (∼ψ :: Γ)) : IDerivable A ρ H (α + α) Γ := by
  rcases redShape_or_neg ψ (hrk ▸ hρ) with hs | hs
  · exact reduction_of_shape hH hs (le_of_eq hrk) d₁ d₀
  · refine reduction_of_shape hH hs (by rw [rk_neg]; exact le_of_eq hrk) ?_ d₁
    simpa using d₀

end IDerivable

end InductiveDef

end OrdinalAnalysis
