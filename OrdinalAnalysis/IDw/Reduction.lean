/- Source: OrdinalAnalysis\IDn\Reduction.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.Calculus
import OrdinalAnalysis.IDw.ReductionAux
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
    `IDwDerivable.red_aux`                         the induction
    `IDwDerivable.reduction_of_shape`              the reduction lemma for `RedShape ψ`
    `IDwDerivable.reduction`                       Exercise 7.1 (b)
    `IDwDerivable.reduction_jlev`                  the same for a cut formula `Jlev ℓ (s,t)`
    `IDwDerivable.reduction_cut`                   a cut of rank `ρ ≠ Ω` at the height `α + α`
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder

/-! ### The shapes of the cut formula -/

/-- The kind of a relation symbol: `none` for arithmetic, `some none` for `X`, and
`some (some α)` for `I^{≺α}`. -/
def relKind : {k : ℕ} → (LIinfW).Rel k → Option (Option Stage)
  | _, Sum.inl _ => none
  | _, Sum.inr IInfRelW.X => some none
  | _, Sum.inr (IInfRelW.stage a) => some (some a)
  | _, Sum.inr (IInfRelW.jlev _) => some none

/-- `6` on the new relation symbols `Jlev ℓ`, `0` otherwise: `headKind` uses the codes `8`, `9`
for `Jlev ℓ (s,t)`, `¬Jlev ℓ (s,t)`, so the shape `ne_njlev` can be read off the first component. -/
@[simp] def relTag : {k : ℕ} → (LIinfW).Rel k → ℕ
  | _, Sum.inl _ => 0
  | _, Sum.inr IInfRelW.X => 0
  | _, Sum.inr (IInfRelW.stage _) => 0
  | _, Sum.inr (IInfRelW.jlev _) => 6

/-- The outermost symbol of a formula, with the kind of its relation symbol. -/
def headKind {ξ : Type*} : {m : ℕ} → Semiformula (LIinfW) ξ m → ℕ × Option (Option Stage)
  | _, .verum => (0, none)
  | _, .falsum => (1, none)
  | _, .rel r _ => (2 + relTag r, relKind r)
  | _, .nrel r _ => (3 + relTag r, relKind r)
  | _, .and _ _ => (4, none)
  | _, .or _ _ => (5, none)
  | _, .all _ => (6, none)
  | _, .exs _ => (7, none)

/-- A true literal is an atom or negated atom of arithmetic. -/
theorem TrueLit.headKind {φ : Proposition (LIinfW)} (h : TrueLit φ) :
    IDw.headKind φ = (2, none) ∨ IDw.headKind φ = (3, none) := by
  obtain ⟨⟨k, r, v, (rfl | rfl), -⟩, -⟩ := h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The shape of the cut formula** in the reduction lemma, Freund's remark preceding
Exercise 7.1 (b), read for `IDn`: `ψ` is not a true literal, not `⊤`, not a conjunction, not a
universal formula, not `¬I_k^{≺δ} t` at any level `k`, and not `I_k t` (the `Fix`-principal
`I_k^{≺Ω_{k+1}} t`) at any level `k` — so `ψ` is never the principal formula of a clause (V)
or of `Fix`, at whichever level (V)/`Fix` last fired. Unlike the one-level source, `ne_IOmega`
must quantify over every level: a single formula `ψ` is checked against clauses at every level
in the course of the induction (`red_aux`), not just one fixed level. -/
structure RedShape (ψ : Proposition (LIinfW)) : Prop where
  not_lit : ¬TrueLit ψ
  ne_verum : ψ ≠ ⊤
  ne_and : ∀ φ₀ φ₁ : Proposition (LIinfW), ψ ≠ φ₀ ⋏ φ₁
  ne_all : ∀ φ : Semiproposition (LIinfW) 1, ψ ≠ ∀¹ φ
  ne_nstage : ∀ (a : Stage) (t : SyntacticTerm (LIinfW)), ψ ≠ nstageAt a t
  ne_IOmega : ∀ (k : ℕ) (t : SyntacticTerm (LIinfW)), ψ ≠ IOmegaAt k t
  ne_njlev : ∀ (ℓ : WithTop ℕ) (s t : SyntacticTerm (LIinfW)), ψ ≠ njlevAt ℓ s t

/-- The shape is read off the outermost symbol. -/
theorem RedShape.of_headKind {ψ : Proposition (LIinfW)} (hl : ¬TrueLit ψ)
    (h0 : headKind ψ ≠ (0, none)) (h4 : (headKind ψ).1 ≠ 4) (h6 : (headKind ψ).1 ≠ 6)
    (hn : ∀ a : Stage, headKind ψ ≠ (3, some (some a)))
    (hI : ∀ k : ℕ, headKind ψ ≠ (2, some (some (Stage.top k))))
    (hJ : (headKind ψ).1 ≠ 9 := by simp [headKind, relKind, stageAt, jlevAt]) : RedShape ψ where
  not_lit := hl
  ne_verum := fun h => h0 (by rw [h]; rfl)
  ne_and := fun _ _ h => h4 (by rw [h]; rfl)
  ne_all := fun _ h => h6 (by rw [h]; rfl)
  ne_nstage := fun a _ h => hn a (by rw [h]; rfl)
  ne_IOmega := fun k _ h => hI k (by rw [h]; rfl)
  ne_njlev := fun _ _ _ h => hJ (by rw [h]; rfl)

/-- `Jlev ℓ (s,t)` has the shape (no rank hypothesis: `Jlev` is never `Fix`-principal, and its
principal clause `jlev` is handled by a cut on `I_{val s} t`). -/
theorem RedShape.of_jlevAt (ℓ : WithTop ℕ) (s t : SyntacticTerm (LIinfW)) :
    RedShape (jlevAt ℓ s t) := by
  refine RedShape.of_headKind ?_ (by simp [headKind, jlevAt, relKind])
    (by simp [headKind, jlevAt]) (by simp [headKind, jlevAt]) (by simp [headKind, jlevAt])
    (by simp [headKind, jlevAt])
  intro h; rcases h.headKind with h | h <;> simp [headKind, jlevAt, relKind] at h

/-- **The disjunctive formulas** of Freund, Definition 5.1: the false literals of arithmetic
(the empty disjunctions, also `⊥`), `ψ₀ ∨ ψ₁ ≃ ⋁_{i≺2} ψ_i`, `∃x ψ(x) ≃ ⋁_{m≺ω} ψ(m̄)` and
`I^{≺δ} t ≃ ⋁_{γ≺δ} A(t, I^{≺γ})`, and (new for `IDw`) `Jlev ℓ (s,t)`, the disjunction
over the levels `j < ℓ`. -/
def Disjunctive (ψ : Proposition (LIinfW)) : Prop :=
  (IsArithLit ψ ∧ ¬TrueN ψ) ∨ ψ = ⊥ ∨ (∃ φ₀ φ₁ : Proposition (LIinfW), ψ = φ₀ ⋎ φ₁) ∨
    (∃ φ : Semiproposition (LIinfW) 1, ψ = ∃¹ φ) ∨
    (∃ (a : Stage) (t : SyntacticTerm (LIinfW)), ψ = stageAt a t) ∨
    (∃ (ℓ : WithTop ℕ) (s t : SyntacticTerm (LIinfW)), ψ = jlevAt ℓ s t)

/-- **A disjunctive formula whose rank avoids every level's `Ω` has the shape of the reduction
lemma**: it is not `I_k t` at any level `k`, and no disjunctive formula is conjunctive. Unlike
the one-level source, the side condition is `∀ k, rk ψ ≠ Ω_{k+1}` — a formula of rank `ρ` can
only fail to have this shape by equalling `Ω_{k+1}` of the *particular* level `k` its own
`I_k t` disjunct belongs to, which is not fixed in advance (`a : Stage` below carries its own
level `a.lvl`, unlike the one-level source's fixed `Stage.top`). -/
theorem Disjunctive.redShape {ψ : Proposition (LIinfW)} (h : Disjunctive ψ)
    (hΩ : ∀ k : ℕ, rk ψ ≠ ThetaVNoteD.Omega k) : RedShape ψ := by
  rcases h with ⟨hl, hT⟩ | rfl | ⟨φ₀, φ₁, rfl⟩ | ⟨φ, rfl⟩ | ⟨a, t, rfl⟩ | ⟨ℓ, s, t, rfl⟩
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
  · have ha : ∀ k : ℕ, a ≠ (Stage.top k) := by
      intro k; rintro rfl; exact hΩ k (rk_IOmegaAt k t)
    refine RedShape.of_headKind ?_ (by simp [headKind, stageAt, relKind])
      (by simp [headKind, stageAt]) (by simp [headKind, stageAt])
      (by simp [headKind, stageAt, relKind])
      (fun k => by simpa [headKind, stageAt, relKind] using ha k)
    intro h; rcases h.headKind with h | h <;> simp [headKind, stageAt, relKind] at h
  · exact RedShape.of_jlevAt ℓ s t

/-- **For a formula whose rank avoids every level's `Ω`, the formula or its negation has the
shape of the reduction lemma.** -/
theorem redShape_or_neg (ψ : Proposition (LIinfW))
    (hΩ : ∀ k : ℕ, rk ψ ≠ ThetaVNoteD.Omega k) :
    RedShape ψ ∨ RedShape (∼ψ) := by
  have nl : ∀ φ : Proposition (LIinfW), (headKind φ).2 ≠ none → ¬TrueLit φ := by
    intro φ h hT
    rcases hT.headKind with e | e <;> rw [e] at h <;> exact h rfl
  cases ψ with
  | verum =>
    right
    change RedShape (⊥ : Proposition (LIinfW))
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
    · by_cases hT : TrueLit (Semiformula.rel (Sum.inl r : (LIinfW).Rel _) v)
      · right
        change RedShape (Semiformula.nrel (Sum.inl r : (LIinfW).Rel _) v)
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
        have ha : ∀ k : ℕ, a ≠ (Stage.top k) := by
          intro k; rintro rfl
          exact hΩ k ((rk_rel _ v).trans (atomRkStage_top k))
        left
        exact RedShape.of_headKind (nl _ (by simp [headKind, relKind]))
          (by simp [headKind, relKind]) (by simp [headKind]) (by simp [headKind])
          (by simp [headKind]) (fun k => by simp [headKind, relKind, ha k])
      | jlev ℓ =>
        left
        exact RedShape.of_headKind (nl _ (by simp [headKind, relKind]))
          (by simp [headKind, relKind]) (by simp [headKind]) (by simp [headKind])
          (by simp [headKind]) (by simp [headKind, relKind])
  | nrel r v =>
    rcases r with r | r
    · by_cases hT : TrueLit (Semiformula.nrel (Sum.inl r : (LIinfW).Rel _) v)
      · right
        change RedShape (Semiformula.rel (Sum.inl r : (LIinfW).Rel _) v)
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
        have ha : ∀ k : ℕ, a ≠ (Stage.top k) := by
          intro k; rintro rfl
          exact hΩ k ((rk_nrel _ v).trans (atomRkStage_top k))
        right
        change RedShape (Semiformula.rel (Sum.inr (IInfRelW.stage a) : (LIinfW).Rel _) v)
        exact RedShape.of_headKind (nl _ (by simp [headKind, relKind]))
          (by simp [headKind, relKind]) (by simp [headKind]) (by simp [headKind])
          (by simp [headKind]) (fun k => by simp [headKind, relKind, ha k])
      | jlev ℓ =>
        right
        change RedShape (Semiformula.rel (Sum.inr (IInfRelW.jlev ℓ) : (LIinfW).Rel _) v)
        exact RedShape.of_headKind (nl _ (by simp [headKind, relKind]))
          (by simp [headKind, relKind]) (by simp [headKind]) (by simp [headKind])
          (by simp [headKind]) (by simp [headKind, relKind])
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

theorem XinfAt_ne_neg (t : SyntacticTerm (LIinfW)) : XinfAt t ≠ ∼(XinfAt t) := by
  intro h
  have e : ∼(XinfAt t) = Semiformula.nrel (Sum.inr IInfRelW.X : (LIinfW).Rel 1) ![t] :=
    Semiformula.neg_rel _ _
  rw [e] at h
  cases h

/-! ### Exercise 7.1 (b) -/

namespace IDwDerivable

variable {A : Semisentence LForm 2} {ρ : ThetaVNoteD}

theorem mem_of_mem_ne {θ ψ : Proposition (LIinfW)} {Δ Γ : Sequent (LIinfW)} (hθ : θ ∈ Δ)
    (hΔ : Δ ⊆ ψ :: Γ) (hne : θ ≠ ψ) : θ ∈ Γ := by
  rcases List.mem_cons.mp (hΔ hθ) with h | h
  · exact absurd h hne
  · exact h

theorem params_tail_subset {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD}
    {φ : Proposition (LIinfW)} {Γ : Sequent (LIinfW)} (d : IDwDerivable A ρ H α (φ :: Γ)) :
    paramsVal Γ ⊆ H ∅ := by
  have h := d.params_subset
  rw [paramsVal_cons] at h
  exact Set.subset_union_right.trans h

/-- The statement of the reduction lemma for a derivation of `Δ ⊆ Γ, ψ`, with the
derivation of `Γ, ¬ψ` of height `α`. -/
def RedClaim (A : Semisentence LForm 2) (ρ : ThetaVNoteD) (ψ : Proposition (LIinfW)) (α : ThetaVNoteD)
    (H : Set ThetaVNoteD → Set ThetaVNoteD) (β : ThetaVNoteD) (Δ : Sequent (LIinfW)) : Prop :=
  ThetaVNoteD.NiceS H → ∀ Γ : Sequent (LIinfW), Δ ⊆ ψ :: Γ → IDwDerivable A ρ H α (∼ψ :: Γ) →
    IDwDerivable A ρ H (α + β) Γ

/-- A premise `Δ, φ` of height `β₀` becomes `Γ, φ` of height `α + β₀`. -/
theorem red_prem {ψ φ : Proposition (LIinfW)} {H : Set ThetaVNoteD → Set ThetaVNoteD}
    {α β₀ : ThetaVNoteD} {Δ Γ : Sequent (LIinfW)} (hH : ThetaVNoteD.NiceS H)
    (d₀ : IDwDerivable A ρ H β₀ (φ :: Δ)) (ih₀ : RedClaim A ρ ψ α H β₀ (φ :: Δ))
    (hΔ : Δ ⊆ ψ :: Γ) (e : IDwDerivable A ρ H α (∼ψ :: Γ)) :
    IDwDerivable A ρ H (α + β₀) (φ :: Γ) := by
  refine ih₀ hH (φ :: Γ) ?_ ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rcases List.mem_cons.mp (hΔ hx) with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  · refine e.weaken_seq hH.1 ?_ ?_
    · intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
    · have h := e.params_subset
      rw [paramsVal_cons] at h
      rw [paramsVal_cons, paramsVal_cons]
      exact Set.union_subset (Set.subset_union_left.trans h)
        (Set.union_subset d₀.params_head_subset (Set.subset_union_right.trans h))

/-- The principal case: a cut on the component `χ = ψ_γ`, of rank `≺ ρ`. -/
theorem red_cut {χ : Proposition (LIinfW)} {H : Set ThetaVNoteD → Set ThetaVNoteD}
    {α β β₀ : ThetaVNoteD} {Γ : Sequent (LIinfW)} (hH : ThetaVNoteD.NiceS H) (hr : rk χ < ρ)
    (hβ : β₀ < β) (hβH : β ∈ H ∅) (d : IDwDerivable A ρ H (α + β₀) (χ :: Γ))
    (e : IDwDerivable A ρ H α (∼χ :: Γ)) : IDwDerivable A ρ H (α + β) Γ :=
  .cut (hH.add_mem e.height_mem hβH) e.params_tail_subset hr
    (ThetaVNoteD.add_lt_add_left α hβ) d
    (e.mono_height (ThetaVNoteD.le_self_add_red α β₀) d.height_mem)

/-- **Exercise 7.1 (b), the induction** on the derivation of `Δ ⊆ Γ, ψ`.
(In `IDn` this needed `hAb : FamilyLevelBounded A` for `rk_unfold_lt_stageAt`; the `IDw`
version of that lemma holds for every `A : FormJ`, so the hypothesis is gone.) The two new
clauses: for `njlev` the shape `ne_njlev` rules out `ψ` principal; for `jlev` with `ψ = Jlev ℓ (s,t)`
principal, inversion (`inv_njlev`) turns `Γ, ¬ψ` into `Γ, ¬I_{val s} t` and a cut on `I_{val s} t`
finishes, of rank `Ω_{val s+1} ≺ rk ψ ≤ ρ` (`rk_IOmegaAt_lt_jlevAt`). -/
theorem red_aux {ψ : Proposition (LIinfW)} (hs : RedShape ψ)
    (hρ : rk ψ ≤ ρ) {α : ThetaVNoteD}
    {H : Set ThetaVNoteD → Set ThetaVNoteD} {β : ThetaVNoteD} {Δ : Sequent (LIinfW)}
    (d : IDwDerivable A ρ H β Δ) : RedClaim A ρ ψ α H β Δ := by
  induction d with
  | @jlev H β Δ ℓ s t β₀ hβ _ hm hs' ht hl h0 d0 ih0 =>
    intro hH Γ hΔ e
    have p0 := red_prem hH d0 ih0 hΔ e
    by_cases he : jlevAt ℓ s t = ψ
    · subst he
      have e' : IDwDerivable A ρ H α (njlevAt ℓ s t :: Γ) := e
      exact red_cut hH (lt_of_lt_of_le (rk_IOmegaAt_lt_jlevAt hl t s t) hρ) h0 hβ p0
        (inv_njlev hH hl e')
    · exact .jlev (hH.add_mem e.height_mem hβ) e.params_tail_subset (mem_of_mem_ne hm hΔ he)
        hs' ht hl (ThetaVNoteD.add_lt_add_left α h0) p0
  | njlev hβ _ hm hs' ht h0 d0 ih0 =>
    intro hH Γ hΔ e
    exact .njlev (hH.add_mem e.height_mem hβ) e.params_tail_subset
      (mem_of_mem_ne hm hΔ fun h => hs.ne_njlev _ _ _ h.symm) hs' ht
      (fun hl => ThetaVNoteD.add_lt_add_left α (h0 hl))
      (fun hl => red_prem hH (d0 hl) (ih0 hl) hΔ e)
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
      exact e.weaken hH.1 (ThetaVNoteD.le_self_add_red α _)
        (List.cons_subset.mpr ⟨hm, List.Subset.refl _⟩) hαβ e.params_tail_subset
    · by_cases e2 : ∼(XinfAt t) = ψ
      · subst e2
        have hm : XinfAt t ∈ Γ := mem_of_mem_ne h1 hΔ (XinfAt_ne_neg t)
        have e : IDwDerivable A ρ H' α (XinfAt t :: Γ) := by simpa using e
        exact e.weaken hH.1 (ThetaVNoteD.le_self_add_red α _)
          (List.cons_subset.mpr ⟨hm, List.Subset.refl _⟩) hαβ e.params_tail_subset
      · exact .idX t hαβ e.params_tail_subset (mem_of_mem_ne h1 hΔ e1)
          (mem_of_mem_ne h2 hΔ e2)
  | and hβ _ hm h0 h1 d0 d1 ih0 ih1 =>
    intro hH Γ hΔ e
    exact .and (hH.add_mem e.height_mem hβ) e.params_tail_subset
      (mem_of_mem_ne hm hΔ fun h => hs.ne_and _ _ h.symm)
      (ThetaVNoteD.add_lt_add_left α h0) (ThetaVNoteD.add_lt_add_left α h1)
      (red_prem hH d0 ih0 hΔ e) (red_prem hH d1 ih1 hΔ e)
  | @orL H β Δ φ₀ φ₁ β₀ hβ _ hm h0 d0 ih0 =>
    intro hH Γ hΔ e
    have p0 := red_prem hH d0 ih0 hΔ e
    by_cases he : φ₀ ⋎ φ₁ = ψ
    · subst he
      have e' : IDwDerivable A ρ H α (∼φ₀ ⋏ ∼φ₁ :: Γ) := by simpa using e
      exact red_cut hH (lt_of_lt_of_le (rk_left_lt_or φ₀ φ₁) hρ) h0 hβ p0
        (inv_and_left hH.1 e')
    · exact .orL (hH.add_mem e.height_mem hβ) e.params_tail_subset (mem_of_mem_ne hm hΔ he)
        (ThetaVNoteD.add_lt_add_left α h0) p0
  | @orR H β Δ φ₀ φ₁ β₀ hβ _ hm h1 h0 d0 ih0 =>
    intro hH Γ hΔ e
    have p0 := red_prem hH d0 ih0 hΔ e
    by_cases he : φ₀ ⋎ φ₁ = ψ
    · subst he
      have e' : IDwDerivable A ρ H α (∼φ₀ ⋏ ∼φ₁ :: Γ) := by simpa using e
      exact red_cut hH (lt_of_lt_of_le (rk_right_lt_or φ₀ φ₁) hρ) h0 hβ p0
        (inv_and_right hH.1 e')
    · exact .orR (hH.add_mem e.height_mem hβ) e.params_tail_subset (mem_of_mem_ne hm hΔ he)
        (lt_of_lt_of_le h1 (ThetaVNoteD.le_add_left α β)) (ThetaVNoteD.add_lt_add_left α h0) p0
  | all f hβ _ hm hf d0 ih0 =>
    intro hH Γ hΔ e
    exact .all (fun m => α + f m) (hH.add_mem e.height_mem hβ) e.params_tail_subset
      (mem_of_mem_ne hm hΔ fun h => hs.ne_all _ h.symm)
      (fun m => ThetaVNoteD.add_lt_add_left α (hf m)) fun m => red_prem hH (d0 m) (ih0 m) hΔ e
  | @exs H β Δ φ m β₀ hβ _ hm hn h0 d0 ih0 =>
    intro hH Γ hΔ e
    have p0 := red_prem hH d0 ih0 hΔ e
    by_cases he : (∃¹ φ) = ψ
    · subst he
      have e' : IDwDerivable A ρ H α ((∀¹ ∼φ) :: Γ) := by simpa using e
      have e'' : IDwDerivable A ρ H α (∼(φ/[numI m]) :: Γ) := by
        simpa using inv_all hH.1 m e'
      exact red_cut hH (lt_of_lt_of_le (rk_subst_lt_exs φ (numI m)) hρ) h0 hβ p0 e''
    · exact .exs m (hH.add_mem e.height_mem hβ) e.params_tail_subset (mem_of_mem_ne hm hΔ he)
        (lt_of_lt_of_le hn (ThetaVNoteD.le_add_left α β)) (ThetaVNoteD.add_lt_add_left α h0) p0
  | @stage H β Δ k a t g β₀ hβ _ hm hga hgβ hgH h0 d0 ih0 =>
    intro hH Γ hΔ e
    have p0 := red_prem hH d0 ih0 hΔ e
    by_cases he : stageAt (⟨k, a⟩ : Stage) t = ψ
    · subst he
      have e' : IDwDerivable A ρ H α (nstageAt (⟨k, a⟩ : Stage) t :: Γ) := by simpa using e
      exact red_cut hH (lt_of_lt_of_le (rk_unfold_lt_stageAt A hga t t) hρ) h0 hβ p0
        (inv_nstage hH hga hgH e')
    · exact .stage g (hH.add_mem e.height_mem hβ) e.params_tail_subset
        (mem_of_mem_ne hm hΔ he) hga (lt_of_lt_of_le hgβ (ThetaVNoteD.le_add_left α β)) hgH
        (ThetaVNoteD.add_lt_add_left α h0) p0
  | nstage f hβ _ hm hf d0 ih0 =>
    intro hH Γ hΔ e
    exact .nstage (fun g => α + f g) (hH.add_mem e.height_mem hβ) e.params_tail_subset
      (mem_of_mem_ne hm hΔ fun h => hs.ne_nstage _ _ h.symm)
      (fun g hg => ThetaVNoteD.add_lt_add_left α (hf g hg)) fun g hg =>
        red_prem (hH.adjoin {g.1}) (d0 g hg) (ih0 g hg) hΔ (e.adjoin hH.1 {g.1})
  | fix hβ _ hm hΩ h0 d0 ih0 =>
    intro hH Γ hΔ e
    exact .fix (hH.add_mem e.height_mem hβ) e.params_tail_subset
      (mem_of_mem_ne hm hΔ fun h => hs.ne_IOmega _ _ h.symm)
      (le_trans hΩ (ThetaVNoteD.le_add_left α _)) (ThetaVNoteD.add_lt_add_left α h0)
      (red_prem hH d0 ih0 hΔ e)
  | cut hβ _ hr h0 d0 d1 ih0 ih1 =>
    intro hH Γ hΔ e
    exact .cut (hH.add_mem e.height_mem hβ) e.params_tail_subset hr
      (ThetaVNoteD.add_lt_add_left α h0) (red_prem hH d0 ih0 hΔ e) (red_prem hH d1 ih1 hΔ e)

/-- **The reduction lemma** for a cut formula of the shape `RedShape`, of rank `⪯ ρ`. -/
theorem reduction_of_shape {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H)
    {ψ : Proposition (LIinfW)} (hs : RedShape ψ) (hρ : rk ψ ≤ ρ)
    {α β : ThetaVNoteD}
    {Γ : Sequent (LIinfW)} (e : IDwDerivable A ρ H α (∼ψ :: Γ))
    (d : IDwDerivable A ρ H β (ψ :: Γ)) : IDwDerivable A ρ H (α + β) Γ :=
  red_aux hs hρ d hH Γ (List.Subset.refl _) e

/-- **Freund, Exercise 7.1 (b) (Reduction)**: for a nice operator `H` and a disjunctive
formula `ψ` of rank `rk(ψ) = ρ ≠ Ω`,

    `H ⊢^α_ρ Γ, ¬ψ` and `H ⊢^β_ρ Γ, ψ` give `H ⊢^{α+β}_ρ Γ`. -/
theorem reduction {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H)
    {ψ : Proposition (LIinfW)} (hψ : Disjunctive ψ) (hrk : rk ψ = ρ)
    (hρ : ∀ k : ℕ, ρ ≠ ThetaVNoteD.Omega k)
    {α β : ThetaVNoteD} {Γ : Sequent (LIinfW)} (e : IDwDerivable A ρ H α (∼ψ :: Γ))
    (d : IDwDerivable A ρ H β (ψ :: Γ)) : IDwDerivable A ρ H (α + β) Γ :=
  reduction_of_shape hH (hψ.redShape (fun k => hrk ▸ hρ k)) (le_of_eq hrk) e d

/-- **The reduction lemma for a cut formula `Jlev ℓ (s,t)`** (new in `IDw`): `H ⊢^α_ρ Γ, ¬Jlev ℓ (s,t)`
and `H ⊢^β_ρ Γ, Jlev ℓ (s,t)` with `rk (Jlev ℓ (s,t)) ⪯ ρ` give `H ⊢^{α+β}_ρ Γ`. The principal
case is the (jlev) clause: inversion (`inv_njlev`) gives `Γ, ¬I_{val s} t` and the cut is on
`I_{val s} t`, of rank `Ω_{val s+1} ≺ rk (Jlev ℓ (s,t))` (`rk_IOmegaAt_lt_jlevAt`). -/
theorem reduction_jlev {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H)
    {ℓ : WithTop ℕ} {s t : SyntacticTerm (LIinfW)} (hρ : rk (jlevAt ℓ s t) ≤ ρ)
    {α β : ThetaVNoteD} {Γ : Sequent (LIinfW)} (e : IDwDerivable A ρ H α (njlevAt ℓ s t :: Γ))
    (d : IDwDerivable A ρ H β (jlevAt ℓ s t :: Γ)) : IDwDerivable A ρ H (α + β) Γ :=
  reduction_of_shape hH (RedShape.of_jlevAt ℓ s t) hρ e d

/-- **A cut of rank `ρ ≠ Ω` is reduced** (Exercise 7.1 (b), applied to `ψ` or to `¬ψ`,
whichever has the shape of the reduction lemma): `H ⊢^α_ρ Γ, ψ` and `H ⊢^α_ρ Γ, ¬ψ` with
`rk(ψ) = ρ`, `ρ` avoiding every level's `Ω`, give `H ⊢^{α+α}_ρ Γ`. -/
theorem reduction_cut {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H)
    {ψ : Proposition (LIinfW)} (hrk : rk ψ = ρ) (hρ : ∀ k : ℕ, ρ ≠ ThetaVNoteD.Omega k)
    {α : ThetaVNoteD}
    {Γ : Sequent (LIinfW)} (d₀ : IDwDerivable A ρ H α (ψ :: Γ))
    (d₁ : IDwDerivable A ρ H α (∼ψ :: Γ)) : IDwDerivable A ρ H (α + α) Γ := by
  rcases redShape_or_neg ψ (fun k => hrk ▸ hρ k) with hs | hs
  · exact reduction_of_shape hH hs (le_of_eq hrk) d₁ d₀
  · refine reduction_of_shape hH hs (by rw [rk_neg]; exact le_of_eq hrk) ?_ d₁
    simpa using d₀

end IDwDerivable

end IDw

end OrdinalAnalysis
