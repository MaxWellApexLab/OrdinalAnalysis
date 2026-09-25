/- Source: OrdinalAnalysis\ID1\Reduction.lean (one-level `Omega`/`Stage` generalised to level `k : Fin n`). -/

import OrdinalAnalysis.IDn.Calculus
import OrdinalAnalysis.IDn.ReductionAux
import OrdinalAnalysis.Ordinal.ThetaW.HullCofinal
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
    `IDnDerivable.red_aux`                         the induction
    `IDnDerivable.reduction_of_shape`              the reduction lemma for `RedShape ψ`
    `IDnDerivable.reduction`                       Exercise 7.1 (b)
    `IDnDerivable.reduction_cut`                   a cut of rank `ρ ≠ Ω` at the height `α + α`
-/

set_option autoImplicit false

namespace OrdinalAnalysis
variable {n : ℕ}

namespace IDn

open LO LO.FirstOrder

/-! ### The shapes of the cut formula -/

/-- The kind of a relation symbol: `none` for arithmetic, `some none` for `X`, and
`some (some α)` for `I^{≺α}`. -/
def relKind : {k : ℕ} → (LIinfN n).Rel k → Option (Option (Stage n))
  | _, Sum.inl _ => none
  | _, Sum.inr IInfRelN.X => some none
  | _, Sum.inr (IInfRelN.stage a) => some (some a)

/-- The outermost symbol of a formula, with the kind of its relation symbol. -/
def headKind {ξ : Type*} : {m : ℕ} → Semiformula (LIinfN n) ξ m → ℕ × Option (Option (Stage n))
  | _, .verum => (0, none)
  | _, .falsum => (1, none)
  | _, .rel r _ => (2, relKind r)
  | _, .nrel r _ => (3, relKind r)
  | _, .and _ _ => (4, none)
  | _, .or _ _ => (5, none)
  | _, .all _ => (6, none)
  | _, .exs _ => (7, none)

/-- A true literal is an atom or negated atom of arithmetic. -/
theorem TrueLit.headKind {φ : Proposition (LIinfN n)} (h : TrueLit φ) :
    IDn.headKind φ = (2, none) ∨ IDn.headKind φ = (3, none) := by
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
structure RedShape (ψ : Proposition (LIinfN n)) : Prop where
  not_lit : ¬TrueLit ψ
  ne_verum : ψ ≠ ⊤
  ne_and : ∀ φ₀ φ₁ : Proposition (LIinfN n), ψ ≠ φ₀ ⋏ φ₁
  ne_all : ∀ φ : Semiproposition (LIinfN n) 1, ψ ≠ ∀¹ φ
  ne_nstage : ∀ (a : Stage n) (t : SyntacticTerm (LIinfN n)), ψ ≠ nstageAt a t
  ne_IOmega : ∀ (k : Fin n) (t : SyntacticTerm (LIinfN n)), ψ ≠ IOmegaAt k t

/-- The shape is read off the outermost symbol. -/
theorem RedShape.of_headKind {ψ : Proposition (LIinfN n)} (hl : ¬TrueLit ψ)
    (h0 : headKind ψ ≠ (0, none)) (h4 : (headKind ψ).1 ≠ 4) (h6 : (headKind ψ).1 ≠ 6)
    (hn : ∀ a : (Stage n), headKind ψ ≠ (3, some (some a)))
    (hI : ∀ k : Fin n, headKind ψ ≠ (2, some (some (Stage.top k)))) : RedShape ψ where
  not_lit := hl
  ne_verum := fun h => h0 (by rw [h]; rfl)
  ne_and := fun _ _ h => h4 (by rw [h]; rfl)
  ne_all := fun _ h => h6 (by rw [h]; rfl)
  ne_nstage := fun a _ h => hn a (by rw [h]; rfl)
  ne_IOmega := fun k _ h => hI k (by rw [h]; rfl)

/-- **The disjunctive formulas** of Freund, Definition 5.1: the false literals of arithmetic
(the empty disjunctions, also `⊥`), `ψ₀ ∨ ψ₁ ≃ ⋁_{i≺2} ψ_i`, `∃x ψ(x) ≃ ⋁_{m≺ω} ψ(m̄)` and
`I^{≺δ} t ≃ ⋁_{γ≺δ} A(t, I^{≺γ})`. -/
def Disjunctive (ψ : Proposition (LIinfN n)) : Prop :=
  (IsArithLit ψ ∧ ¬TrueN ψ) ∨ ψ = ⊥ ∨ (∃ φ₀ φ₁ : Proposition (LIinfN n), ψ = φ₀ ⋎ φ₁) ∨
    (∃ φ : Semiproposition (LIinfN n) 1, ψ = ∃¹ φ) ∨
    (∃ (a : (Stage n)) (t : SyntacticTerm (LIinfN n)), ψ = stageAt a t)

/-- **A disjunctive formula whose rank avoids every level's `Ω` has the shape of the reduction
lemma**: it is not `I_k t` at any level `k`, and no disjunctive formula is conjunctive. Unlike
the one-level source, the side condition is `∀ k, rk ψ ≠ Ω_{k+1}` — a formula of rank `ρ` can
only fail to have this shape by equalling `Ω_{k+1}` of the *particular* level `k` its own
`I_k t` disjunct belongs to, which is not fixed in advance (`a : Stage n` below carries its own
level `a.lvl`, unlike the one-level source's fixed `Stage.top`). -/
theorem Disjunctive.redShape {ψ : Proposition (LIinfN n)} (h : Disjunctive ψ)
    (hΩ : ∀ k : Fin n, rk ψ ≠ ThetaWNoteD.Omega k.val) : RedShape ψ := by
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
  · have ha : ∀ k : Fin n, a ≠ (Stage.top k) := by
      intro k; rintro rfl; exact hΩ k (rk_IOmegaAt k t)
    refine RedShape.of_headKind ?_ (by simp [headKind, stageAt, relKind])
      (by simp [headKind, stageAt]) (by simp [headKind, stageAt])
      (by simp [headKind, stageAt, relKind])
      (fun k => by simpa [headKind, stageAt, relKind] using ha k)
    intro h; rcases h.headKind with h | h <;> simp [headKind, stageAt, relKind] at h

/-- **For a formula whose rank avoids every level's `Ω`, the formula or its negation has the
shape of the reduction lemma.** -/
theorem redShape_or_neg (ψ : Proposition (LIinfN n))
    (hΩ : ∀ k : Fin n, rk ψ ≠ ThetaWNoteD.Omega k.val) :
    RedShape ψ ∨ RedShape (∼ψ) := by
  have nl : ∀ φ : Proposition (LIinfN n), (headKind φ).2 ≠ none → ¬TrueLit φ := by
    intro φ h hT
    rcases hT.headKind with e | e <;> rw [e] at h <;> exact h rfl
  cases ψ with
  | verum =>
    right
    change RedShape (⊥ : Proposition (LIinfN n))
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
    · by_cases hT : TrueLit (Semiformula.rel (Sum.inl r : (LIinfN n).Rel _) v)
      · right
        change RedShape (Semiformula.nrel (Sum.inl r : (LIinfN n).Rel _) v)
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
        have ha : ∀ k : Fin n, a ≠ (Stage.top k) := by
          intro k; rintro rfl
          exact hΩ k ((rk_rel _ v).trans (atomRkStage_top k))
        left
        exact RedShape.of_headKind (nl _ (by simp [headKind, relKind]))
          (by simp [headKind, relKind]) (by simp [headKind]) (by simp [headKind])
          (by simp [headKind]) (fun k => by simp [headKind, relKind, ha k])
  | nrel r v =>
    rcases r with r | r
    · by_cases hT : TrueLit (Semiformula.nrel (Sum.inl r : (LIinfN n).Rel _) v)
      · right
        change RedShape (Semiformula.rel (Sum.inl r : (LIinfN n).Rel _) v)
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
        have ha : ∀ k : Fin n, a ≠ (Stage.top k) := by
          intro k; rintro rfl
          exact hΩ k ((rk_nrel _ v).trans (atomRkStage_top k))
        right
        change RedShape (Semiformula.rel (Sum.inr (IInfRelN.stage a) : (LIinfN n).Rel _) v)
        exact RedShape.of_headKind (nl _ (by simp [headKind, relKind]))
          (by simp [headKind, relKind]) (by simp [headKind]) (by simp [headKind])
          (by simp [headKind]) (fun k => by simp [headKind, relKind, ha k])
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

theorem XinfAt_ne_neg (t : SyntacticTerm (LIinfN n)) : XinfAt t ≠ ∼(XinfAt t) := by
  intro h
  have e : ∼(XinfAt t) = Semiformula.nrel (Sum.inr IInfRelN.X : (LIinfN n).Rel 1) ![t] :=
    Semiformula.neg_rel _ _
  rw [e] at h
  cases h

/-! ### Exercise 7.1 (b) -/

namespace IDnDerivable

variable {A : Fin n → Semisentence (LXIn n) 1} {ρ : ThetaWNoteD}

theorem mem_of_mem_ne {θ ψ : Proposition (LIinfN n)} {Δ Γ : Sequent (LIinfN n)} (hθ : θ ∈ Δ)
    (hΔ : Δ ⊆ ψ :: Γ) (hne : θ ≠ ψ) : θ ∈ Γ := by
  rcases List.mem_cons.mp (hΔ hθ) with h | h
  · exact absurd h hne
  · exact h

theorem params_tail_subset {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD}
    {φ : Proposition (LIinfN n)} {Γ : Sequent (LIinfN n)} (d : IDnDerivable A ρ H α (φ :: Γ)) :
    paramsVal Γ ⊆ H ∅ := by
  have h := d.params_subset
  rw [paramsVal_cons] at h
  exact Set.subset_union_right.trans h

/-- The statement of the reduction lemma for a derivation of `Δ ⊆ Γ, ψ`, with the
derivation of `Γ, ¬ψ` of height `α`. -/
def RedClaim (A : Fin n → Semisentence (LXIn n) 1) (ρ : ThetaWNoteD) (ψ : Proposition (LIinfN n)) (α : ThetaWNoteD)
    (H : Set ThetaWNoteD → Set ThetaWNoteD) (β : ThetaWNoteD) (Δ : Sequent (LIinfN n)) : Prop :=
  ThetaWNoteD.NiceS H → ∀ Γ : Sequent (LIinfN n), Δ ⊆ ψ :: Γ → IDnDerivable A ρ H α (∼ψ :: Γ) →
    IDnDerivable A ρ H (α + β) Γ

/-- A premise `Δ, φ` of height `β₀` becomes `Γ, φ` of height `α + β₀`. -/
theorem red_prem {ψ φ : Proposition (LIinfN n)} {H : Set ThetaWNoteD → Set ThetaWNoteD}
    {α β₀ : ThetaWNoteD} {Δ Γ : Sequent (LIinfN n)} (hH : ThetaWNoteD.NiceS H)
    (d₀ : IDnDerivable A ρ H β₀ (φ :: Δ)) (ih₀ : RedClaim A ρ ψ α H β₀ (φ :: Δ))
    (hΔ : Δ ⊆ ψ :: Γ) (e : IDnDerivable A ρ H α (∼ψ :: Γ)) :
    IDnDerivable A ρ H (α + β₀) (φ :: Γ) := by
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
theorem red_cut {χ : Proposition (LIinfN n)} {H : Set ThetaWNoteD → Set ThetaWNoteD}
    {α β β₀ : ThetaWNoteD} {Γ : Sequent (LIinfN n)} (hH : ThetaWNoteD.NiceS H) (hr : rk χ < ρ)
    (hβ : β₀ < β) (hβH : β ∈ H ∅) (d : IDnDerivable A ρ H (α + β₀) (χ :: Γ))
    (e : IDnDerivable A ρ H α (∼χ :: Γ)) : IDnDerivable A ρ H (α + β) Γ :=
  .cut (hH.add_mem e.height_mem hβH) e.params_tail_subset hr
    (ThetaWNoteD.add_lt_add_left α hβ) d
    (e.mono_height (ThetaWNoteD.le_self_add_red α β₀) d.height_mem)

/-- **Exercise 7.1 (b), the induction** on the derivation of `Δ ⊆ Γ, ψ`. The hypothesis
`hAb : FamilyLevelBounded A` (absent from the one-level source: at a single level there is
nothing to bound) is what lets the (stage) case call `rk_unfold_lt_stageAt`, whose multi-level
form needs `A`'s formula at the case's own level `k` to be `LevelBounded k`. -/
theorem red_aux {ψ : Proposition (LIinfN n)} (hAb : FamilyLevelBounded A) (hs : RedShape ψ)
    (hρ : rk ψ ≤ ρ) {α : ThetaWNoteD}
    {H : Set ThetaWNoteD → Set ThetaWNoteD} {β : ThetaWNoteD} {Δ : Sequent (LIinfN n)}
    (d : IDnDerivable A ρ H β Δ) : RedClaim A ρ ψ α H β Δ := by
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
      exact e.weaken hH.1 (ThetaWNoteD.le_self_add_red α _)
        (List.cons_subset.mpr ⟨hm, List.Subset.refl _⟩) hαβ e.params_tail_subset
    · by_cases e2 : ∼(XinfAt t) = ψ
      · subst e2
        have hm : XinfAt t ∈ Γ := mem_of_mem_ne h1 hΔ (XinfAt_ne_neg t)
        have e : IDnDerivable A ρ H' α (XinfAt t :: Γ) := by simpa using e
        exact e.weaken hH.1 (ThetaWNoteD.le_self_add_red α _)
          (List.cons_subset.mpr ⟨hm, List.Subset.refl _⟩) hαβ e.params_tail_subset
      · exact .idX t hαβ e.params_tail_subset (mem_of_mem_ne h1 hΔ e1)
          (mem_of_mem_ne h2 hΔ e2)
  | and hβ _ hm h0 h1 d0 d1 ih0 ih1 =>
    intro hH Γ hΔ e
    exact .and (hH.add_mem e.height_mem hβ) e.params_tail_subset
      (mem_of_mem_ne hm hΔ fun h => hs.ne_and _ _ h.symm)
      (ThetaWNoteD.add_lt_add_left α h0) (ThetaWNoteD.add_lt_add_left α h1)
      (red_prem hH d0 ih0 hΔ e) (red_prem hH d1 ih1 hΔ e)
  | @orL H β Δ φ₀ φ₁ β₀ hβ _ hm h0 d0 ih0 =>
    intro hH Γ hΔ e
    have p0 := red_prem hH d0 ih0 hΔ e
    by_cases he : φ₀ ⋎ φ₁ = ψ
    · subst he
      have e' : IDnDerivable A ρ H α (∼φ₀ ⋏ ∼φ₁ :: Γ) := by simpa using e
      exact red_cut hH (lt_of_lt_of_le (rk_left_lt_or φ₀ φ₁) hρ) h0 hβ p0
        (inv_and_left hH.1 e')
    · exact .orL (hH.add_mem e.height_mem hβ) e.params_tail_subset (mem_of_mem_ne hm hΔ he)
        (ThetaWNoteD.add_lt_add_left α h0) p0
  | @orR H β Δ φ₀ φ₁ β₀ hβ _ hm h1 h0 d0 ih0 =>
    intro hH Γ hΔ e
    have p0 := red_prem hH d0 ih0 hΔ e
    by_cases he : φ₀ ⋎ φ₁ = ψ
    · subst he
      have e' : IDnDerivable A ρ H α (∼φ₀ ⋏ ∼φ₁ :: Γ) := by simpa using e
      exact red_cut hH (lt_of_lt_of_le (rk_right_lt_or φ₀ φ₁) hρ) h0 hβ p0
        (inv_and_right hH.1 e')
    · exact .orR (hH.add_mem e.height_mem hβ) e.params_tail_subset (mem_of_mem_ne hm hΔ he)
        (lt_of_lt_of_le h1 (ThetaWNoteD.le_add_left α β)) (ThetaWNoteD.add_lt_add_left α h0) p0
  | all f hβ _ hm hf d0 ih0 =>
    intro hH Γ hΔ e
    exact .all (fun m => α + f m) (hH.add_mem e.height_mem hβ) e.params_tail_subset
      (mem_of_mem_ne hm hΔ fun h => hs.ne_all _ h.symm)
      (fun m => ThetaWNoteD.add_lt_add_left α (hf m)) fun m => red_prem hH (d0 m) (ih0 m) hΔ e
  | @exs H β Δ φ m β₀ hβ _ hm hn h0 d0 ih0 =>
    intro hH Γ hΔ e
    have p0 := red_prem hH d0 ih0 hΔ e
    by_cases he : (∃¹ φ) = ψ
    · subst he
      have e' : IDnDerivable A ρ H α ((∀¹ ∼φ) :: Γ) := by simpa using e
      have e'' : IDnDerivable A ρ H α (∼(φ/[numI m]) :: Γ) := by
        simpa using inv_all hH.1 m e'
      exact red_cut hH (lt_of_lt_of_le (rk_subst_lt_exs φ (numI m)) hρ) h0 hβ p0 e''
    · exact .exs m (hH.add_mem e.height_mem hβ) e.params_tail_subset (mem_of_mem_ne hm hΔ he)
        (lt_of_lt_of_le hn (ThetaWNoteD.le_add_left α β)) (ThetaWNoteD.add_lt_add_left α h0) p0
  | @stage H β Δ k a t g β₀ hβ _ hm hga hgβ hgH h0 d0 ih0 =>
    intro hH Γ hΔ e
    have p0 := red_prem hH d0 ih0 hΔ e
    by_cases he : stageAt (⟨k, a⟩ : Stage n) t = ψ
    · subst he
      have e' : IDnDerivable A ρ H α (nstageAt (⟨k, a⟩ : Stage n) t :: Γ) := by simpa using e
      exact red_cut hH (lt_of_lt_of_le (rk_unfold_lt_stageAt (hAb k) hga t t) hρ) h0 hβ p0
        (inv_nstage hH hga hgH e')
    · exact .stage g (hH.add_mem e.height_mem hβ) e.params_tail_subset
        (mem_of_mem_ne hm hΔ he) hga (lt_of_lt_of_le hgβ (ThetaWNoteD.le_add_left α β)) hgH
        (ThetaWNoteD.add_lt_add_left α h0) p0
  | nstage f hβ _ hm hf d0 ih0 =>
    intro hH Γ hΔ e
    exact .nstage (fun g => α + f g) (hH.add_mem e.height_mem hβ) e.params_tail_subset
      (mem_of_mem_ne hm hΔ fun h => hs.ne_nstage _ _ h.symm)
      (fun g hg => ThetaWNoteD.add_lt_add_left α (hf g hg)) fun g hg =>
        red_prem (hH.adjoin {g.1}) (d0 g hg) (ih0 g hg) hΔ (e.adjoin hH.1 {g.1})
  | fix hβ _ hm hΩ h0 d0 ih0 =>
    intro hH Γ hΔ e
    exact .fix (hH.add_mem e.height_mem hβ) e.params_tail_subset
      (mem_of_mem_ne hm hΔ fun h => hs.ne_IOmega _ _ h.symm)
      (le_trans hΩ (ThetaWNoteD.le_add_left α _)) (ThetaWNoteD.add_lt_add_left α h0)
      (red_prem hH d0 ih0 hΔ e)
  | cut hβ _ hr h0 d0 d1 ih0 ih1 =>
    intro hH Γ hΔ e
    exact .cut (hH.add_mem e.height_mem hβ) e.params_tail_subset hr
      (ThetaWNoteD.add_lt_add_left α h0) (red_prem hH d0 ih0 hΔ e) (red_prem hH d1 ih1 hΔ e)

/-- **The reduction lemma** for a cut formula of the shape `RedShape`, of rank `⪯ ρ`. -/
theorem reduction_of_shape {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    (hAb : FamilyLevelBounded A) {ψ : Proposition (LIinfN n)} (hs : RedShape ψ) (hρ : rk ψ ≤ ρ)
    {α β : ThetaWNoteD}
    {Γ : Sequent (LIinfN n)} (e : IDnDerivable A ρ H α (∼ψ :: Γ))
    (d : IDnDerivable A ρ H β (ψ :: Γ)) : IDnDerivable A ρ H (α + β) Γ :=
  red_aux hAb hs hρ d hH Γ (List.Subset.refl _) e

/-- **Freund, Exercise 7.1 (b) (Reduction)**: for a nice operator `H` and a disjunctive
formula `ψ` of rank `rk(ψ) = ρ ≠ Ω`,

    `H ⊢^α_ρ Γ, ¬ψ` and `H ⊢^β_ρ Γ, ψ` give `H ⊢^{α+β}_ρ Γ`. -/
theorem reduction {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    (hAb : FamilyLevelBounded A)
    {ψ : Proposition (LIinfN n)} (hψ : Disjunctive ψ) (hrk : rk ψ = ρ)
    (hρ : ∀ k : Fin n, ρ ≠ ThetaWNoteD.Omega k.val)
    {α β : ThetaWNoteD} {Γ : Sequent (LIinfN n)} (e : IDnDerivable A ρ H α (∼ψ :: Γ))
    (d : IDnDerivable A ρ H β (ψ :: Γ)) : IDnDerivable A ρ H (α + β) Γ :=
  reduction_of_shape hH hAb (hψ.redShape (fun k => hrk ▸ hρ k)) (le_of_eq hrk) e d

/-- **A cut of rank `ρ ≠ Ω` is reduced** (Exercise 7.1 (b), applied to `ψ` or to `¬ψ`,
whichever has the shape of the reduction lemma): `H ⊢^α_ρ Γ, ψ` and `H ⊢^α_ρ Γ, ¬ψ` with
`rk(ψ) = ρ`, `ρ` avoiding every level's `Ω`, give `H ⊢^{α+α}_ρ Γ`. -/
theorem reduction_cut {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    (hAb : FamilyLevelBounded A)
    {ψ : Proposition (LIinfN n)} (hrk : rk ψ = ρ) (hρ : ∀ k : Fin n, ρ ≠ ThetaWNoteD.Omega k.val)
    {α : ThetaWNoteD}
    {Γ : Sequent (LIinfN n)} (d₀ : IDnDerivable A ρ H α (ψ :: Γ))
    (d₁ : IDnDerivable A ρ H α (∼ψ :: Γ)) : IDnDerivable A ρ H (α + α) Γ := by
  rcases redShape_or_neg ψ (fun k => hrk ▸ hρ k) with hs | hs
  · exact reduction_of_shape hH hAb hs (le_of_eq hrk) d₁ d₀
  · refine reduction_of_shape hH hAb hs (by rw [rk_neg]; exact le_of_eq hrk) ?_ d₁
    simpa using d₀

end IDnDerivable

end IDn

end OrdinalAnalysis
