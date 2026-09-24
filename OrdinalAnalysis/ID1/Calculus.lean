/-
  The operator-controlled infinitary calculus `ID₁^∞`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §5: Definition 5.1 (the assignment of infinite
  disjunctions and conjunctions), Definition 5.4 (operators, `H[Z]`), Exercise 5.5 (e),
  Definition 5.6 (the calculus) and Exercise 5.7 (weakening).  After Buchholz, *A simplified
  version of local predicativity* (1992), Theorem 3.8 and Lemma 3.9.

  **The relation.**  `IDerivable A ρ H α Γ` is Freund's `H ⊢^α_ρ Γ` for the operator form `A`:
  the conclusion always satisfies the initial condition `{α} ∪ k(Γ) ⊆ H(∅)`, and one of the
  clauses of Definition 5.6 applies.  The clauses (V) and (W) are stated for the formulas
  they concern, according to Definition 5.1:

    * a true literal of arithmetic is the empty conjunction, a false one the empty
      disjunction (`literal`, and `verum` for `⊤`);
    * `ψ₀ ∧ ψ₁ ≃ ⋀_{i≺2} ψ_i` (`and`) and `ψ₀ ∨ ψ₁ ≃ ⋁_{i≺2} ψ_i` (`orL`, `orR`);
    * `∀x ψ(x) ≃ ⋀_{n≺ω} ψ(n̄)` (`all`, the ω-rule) and `∃x ψ(x) ≃ ⋁_{n≺ω} ψ(n̄)` (`exs`);
    * `I^{≺δ} t ≃ ⋁_{γ≺δ} A(t, I^{≺γ})` (`stage`) and `¬I^{≺δ} t ≃ ⋀_{γ≺δ} ¬A(t, I^{≺γ})`
      (`nstage`);

  together with (Cut) (`cut`) and (Fix) (`fix`).  The side conditions are those of
  Definition 5.6: in (W) the index `γ` satisfies `γ ≺ α` and `γ ∈ H(∅)`, in (V) the premise
  for `γ` is derived with the operator `H[{γ}]`, in (Cut) the cut formula has rank `≺ ρ`
  and both premises have the same height, and (Fix) requires `Ω ⪯ α`.

  **Deviations from Definition 5.6, and why they are harmless.**

    * Freund's sequents are finite sets; here they are lists.  As in the source, the
      principal formula of a clause stays in the premises (`Γ, ψ_γ` with `ψ ∈ Γ`); no
      structural rule is added, and weakening (Exercise 5.7 (b)) is proved (`weaken`), which
      also covers the reordering and duplication of formulas.
    * For the indices `i ≺ 2` of `∧`/`∨` and `n ≺ ω` of `∀`/`∃` the conditions
      `γ ∈ H(∅)` of (W) and the operator `H[{γ}]` of (V) are left out: a finite notation lies
      in `H(X)` for every nice `H` (Exercise 5.5 (d)), so `H[{n}] = H` (Exercise 5.5 (c)).
      The conditions `γ ≺ α` on these indices are kept: `1 ≺ α` for the right disjunct and
      `n ≺ α` for the witness `n̄` of `∃`.  For the stage clauses all side conditions are as
      in the source.
    * Formulas are Foundation's syntactic formulas (free variables allowed); Freund's
      formulas are closed.  The truth value needed for Definition 5.1 is only asked of
      closed literals of arithmetic (`TrueLit`), and quantifier instances are taken at the
      numerals.
    * The language has the free predicate `X` of the theory `ID1 A`, which Freund's `L^Ω_ID`
      does not.  Its literals are neither conjunctive nor disjunctive (rank `0`, no
      parameters); the clause `idX` derives every sequent containing `X t` and `¬X t`.
    * The operator is not required to be nice in the definition; the lemmas that need
      properties of the operator take them as hypotheses (`IsOperator`, `Nice`).  Freund's
      relation is the restriction to nice operators.

  **Contents.**

    `stdInf`, `TrueN`, `IsArithLit`, `TrueLit`      the true closed literals of arithmetic
    `numI`                                          the numerals
    `IDerivable`                                    Definition 5.6
    `IDerivable.control`                            the initial condition
    `IDerivable.mono_rank`, `mono_height`, `weaken` Exercise 5.7 (b)
    `IDerivable.mono_op`                            Exercise 5.7 (a)
    `IDerivable.adjoin`, `weaken_adjoin`            `H ⊢ Γ` gives `H[k(Δ)] ⊢ Γ, Δ`
    `IDerivable.inv_and_left`, `inv_and_right`,
    `IDerivable.inv_all`, `inv_nstage`              Exercise 7.1 (a), inversion
    `ThetaNote.Nice.rk_mem`, `rk_mem_params`        Exercise 5.5 (e), formula half
-/
import OrdinalAnalysis.ID1.Rank
import OrdinalAnalysis.Ordinal.Theta.Hull

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

open LO LO.FirstOrder

/-! ### The true literals of arithmetic -/

/-- The fresh symbols read as empty; only the arithmetic part matters for the literals
below. -/
@[instance_reducible]
def iinfFalse : Structure IInfLang ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ _ _ => False

/-- The standard structure: arithmetic standard, `X` and every stage empty. -/
@[instance_reducible]
def stdInf : Structure LIinf ℕ := Structure.add ℒₒᵣ IInfLang ℕ (str₂ := iinfFalse)

/-- Truth of a formula in `stdInf` under the zero assignment; for closed formulas of
arithmetic this is truth in `ℕ`. -/
def TrueN (φ : Proposition LIinf) : Prop :=
  Semiformula.Eval (s := stdInf) ![] (fun _ => 0) φ

@[simp] theorem trueN_neg (φ : Proposition LIinf) : TrueN (∼φ) ↔ ¬TrueN φ := by
  simp [TrueN]

/-- A literal of arithmetic with closed arguments. -/
def IsArithLit (φ : Proposition LIinf) : Prop :=
  ∃ (k : ℕ) (r : Language.Rel ℒₒᵣ k) (v : Fin k → SyntacticTerm LIinf),
    (φ = Semiformula.rel (Sum.inl r : LIinf.Rel k) v ∨
      φ = Semiformula.nrel (Sum.inl r : LIinf.Rel k) v) ∧
    ∀ i, (v i).freeVariables = ∅

/-- **A true literal of arithmetic**: the empty conjunctions of Definition 5.1 (the false
ones are the empty disjunctions). -/
def TrueLit (φ : Proposition LIinf) : Prop := IsArithLit φ ∧ TrueN φ

theorem IsArithLit.neg {φ : Proposition LIinf} (h : IsArithLit φ) : IsArithLit (∼φ) := by
  obtain ⟨k, r, v, (rfl | rfl), hv⟩ := h
  · exact ⟨k, r, v, Or.inr (Semiformula.neg_rel _ _), hv⟩
  · exact ⟨k, r, v, Or.inl (Semiformula.neg_nrel _ _), hv⟩

/-- No literal is true together with its negation. -/
theorem TrueLit.not_neg {φ : Proposition LIinf} (h : TrueLit φ) : ¬TrueLit (∼φ) :=
  fun h' => (trueN_neg φ).mp h'.2 h.2

theorem IsArithLit.params_eq {φ : Proposition LIinf} (h : IsArithLit φ) : params φ = ∅ := by
  obtain ⟨k, r, v, (rfl | rfl), -⟩ := h <;> rfl

theorem IsArithLit.sigmaOmega {φ : Proposition LIinf} (h : IsArithLit φ) : SigmaOmega φ := by
  obtain ⟨k, r, v, (rfl | rfl), -⟩ := h <;> trivial

theorem IsArithLit.cap_eq (b : Stage) {φ : Proposition LIinf} (h : IsArithLit φ) :
    cap b φ = φ := by
  obtain ⟨k, r, v, (rfl | rfl), -⟩ := h <;> rfl

theorem IsArithLit.rk_eq {φ : Proposition LIinf} (h : IsArithLit φ) : rk φ = ThetaNote.zero := by
  obtain ⟨k, r, v, (rfl | rfl), -⟩ := h
  · exact rk_rel _ _
  · exact rk_nrel _ _

/-! ### Head symbols -/

/-- The stage of a negated stage atom `¬I^{≺α} t`, and `none` for every other formula. -/
def negHeadStage {ξ : Type*} {n : ℕ} : Semiformula LIinf ξ n → Option Stage
  | .nrel r _ => relStage r
  | _ => none

@[simp] theorem negHeadStage_nstageAt {ξ : Type*} {n : ℕ} (a : Stage) (t : Semiterm LIinf ξ n) :
    negHeadStage (nstageAt a t) = some a := rfl

theorem IsArithLit.negHeadStage {φ : Proposition LIinf} (h : IsArithLit φ) :
    negHeadStage φ = none := by
  obtain ⟨k, r, v, (rfl | rfl), -⟩ := h <;> rfl

theorem nstageAt_inj {ξ : Type*} {n : ℕ} {a a' : Stage} {t t' : Semiterm LIinf ξ n}
    (h : nstageAt a t = nstageAt a' t') : a = a' ∧ t = t' := by
  obtain ⟨-, h1, h2⟩ := Semiformula.nrel.inj h
  exact ⟨IInfRel.stage.inj (Sum.inr_injective (eq_of_heq h1)), congrFun (eq_of_heq h2) 0⟩

theorem stageAt_inj {ξ : Type*} {n : ℕ} {a a' : Stage} {t t' : Semiterm LIinf ξ n}
    (h : stageAt a t = stageAt a' t') : a = a' ∧ t = t' := by
  obtain ⟨-, h1, h2⟩ := Semiformula.rel.inj h
  exact ⟨IInfRel.stage.inj (Sum.inr_injective (eq_of_heq h1)), congrFun (eq_of_heq h2) 0⟩

/-! ### The parameters of a sequent -/

section ParamsList

variable {ξ : Type*} {n : ℕ}

@[simp] theorem paramsList_nil : paramsList ([] : List (Semiformula LIinf ξ n)) = ∅ := by
  ext; simp [paramsList]

@[simp] theorem paramsList_cons (φ : Semiformula LIinf ξ n) (Γ : List (Semiformula LIinf ξ n)) :
    paramsList (φ :: Γ) = params φ ∪ paramsList Γ := by
  ext; simp [paramsList]

@[simp] theorem paramsList_append (Γ Δ : List (Semiformula LIinf ξ n)) :
    paramsList (Γ ++ Δ) = paramsList Γ ∪ paramsList Δ := by
  ext; simp only [paramsList, List.mem_append, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨φ, (h | h), ha⟩
    · exact Or.inl ⟨φ, h, ha⟩
    · exact Or.inr ⟨φ, h, ha⟩
  · rintro (⟨φ, h, ha⟩ | ⟨φ, h, ha⟩)
    · exact ⟨φ, Or.inl h, ha⟩
    · exact ⟨φ, Or.inr h, ha⟩

theorem paramsList_mono {Γ Δ : List (Semiformula LIinf ξ n)} (h : Γ ⊆ Δ) :
    paramsList Γ ⊆ paramsList Δ :=
  fun _ ⟨φ, hφ, ha⟩ => ⟨φ, h hφ, ha⟩

theorem params_subset_paramsList {φ : Semiformula LIinf ξ n} {Γ : List (Semiformula LIinf ξ n)}
    (h : φ ∈ Γ) : params φ ⊆ paramsList Γ :=
  fun _ ha => ⟨φ, h, ha⟩

end ParamsList

/-! ### The numerals -/

/-- The numeral `n̄`. -/
abbrev numI (n : ℕ) : SyntacticTerm LIinf := Semiterm.numeral n

/-! ### The calculus (Definition 5.6) -/

/-- **Freund, Definition 5.6**: `IDerivable A ρ H α Γ` is `H ⊢^α_ρ Γ`, for the operator
form `A`.  Every clause carries the initial condition `α ∈ H(∅)` and `k(Γ) ⊆ H(∅)`. -/
inductive IDerivable (A : Semisentence LXI 1) (ρ : ThetaNote) :
    (Set ThetaNote → Set ThetaNote) → ThetaNote → Sequent LIinf → Prop
  /-- (V) for a true literal of arithmetic, the empty conjunction. -/
  | literal {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote} {Γ : Sequent LIinf}
      {φ : Proposition LIinf} :
      α ∈ H ∅ → paramsList Γ ⊆ H ∅ → TrueLit φ → φ ∈ Γ → IDerivable A ρ H α Γ
  /-- (V) for `⊤`, the empty conjunction. -/
  | verum {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote} {Γ : Sequent LIinf} :
      α ∈ H ∅ → paramsList Γ ⊆ H ∅ → ⊤ ∈ Γ → IDerivable A ρ H α Γ
  /-- The identity axiom of the free predicate `X`. -/
  | idX {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote} {Γ : Sequent LIinf}
      (t : SyntacticTerm LIinf) :
      α ∈ H ∅ → paramsList Γ ⊆ H ∅ → XinfAt t ∈ Γ → ∼(XinfAt t) ∈ Γ → IDerivable A ρ H α Γ
  /-- (V) for `ψ₀ ∧ ψ₁ ≃ ⋀_{i≺2} ψ_i`. -/
  | and {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote} {Γ : Sequent LIinf}
      {φ ψ : Proposition LIinf} {α₀ α₁ : ThetaNote} :
      α ∈ H ∅ → paramsList Γ ⊆ H ∅ → φ ⋏ ψ ∈ Γ → α₀ < α → α₁ < α →
      IDerivable A ρ H α₀ (φ :: Γ) → IDerivable A ρ H α₁ (ψ :: Γ) → IDerivable A ρ H α Γ
  /-- (W) for `ψ₀ ∨ ψ₁ ≃ ⋁_{i≺2} ψ_i`, index `0`. -/
  | orL {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote} {Γ : Sequent LIinf}
      {φ ψ : Proposition LIinf} {α₀ : ThetaNote} :
      α ∈ H ∅ → paramsList Γ ⊆ H ∅ → φ ⋎ ψ ∈ Γ → α₀ < α →
      IDerivable A ρ H α₀ (φ :: Γ) → IDerivable A ρ H α Γ
  /-- (W) for `ψ₀ ∨ ψ₁ ≃ ⋁_{i≺2} ψ_i`, index `1` (so `1 ≺ α`). -/
  | orR {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote} {Γ : Sequent LIinf}
      {φ ψ : Proposition LIinf} {α₀ : ThetaNote} :
      α ∈ H ∅ → paramsList Γ ⊆ H ∅ → φ ⋎ ψ ∈ Γ → ThetaNote.one < α → α₀ < α →
      IDerivable A ρ H α₀ (ψ :: Γ) → IDerivable A ρ H α Γ
  /-- (V) for `∀x ψ(x) ≃ ⋀_{n≺ω} ψ(n̄)`: the ω-rule. -/
  | all {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote} {Γ : Sequent LIinf}
      {φ : Semiproposition LIinf 1} (f : ℕ → ThetaNote) :
      α ∈ H ∅ → paramsList Γ ⊆ H ∅ → (∀¹ φ) ∈ Γ → (∀ n, f n < α) →
      (∀ n, IDerivable A ρ H (f n) (φ/[numI n] :: Γ)) → IDerivable A ρ H α Γ
  /-- (W) for `∃x ψ(x) ≃ ⋁_{n≺ω} ψ(n̄)`, with the witness `n ≺ α`. -/
  | exs {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote} {Γ : Sequent LIinf}
      {φ : Semiproposition LIinf 1} (n : ℕ) {α₀ : ThetaNote} :
      α ∈ H ∅ → paramsList Γ ⊆ H ∅ → (∃¹ φ) ∈ Γ → ThetaNote.ofNat n < α → α₀ < α →
      IDerivable A ρ H α₀ (φ/[numI n] :: Γ) → IDerivable A ρ H α Γ
  /-- (W) for `I^{≺δ} t ≃ ⋁_{γ≺δ} A(t, I^{≺γ})`, with `γ ≺ α` and `γ ∈ H(∅)`. -/
  | stage {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote} {Γ : Sequent LIinf}
      {a : Stage} {t : SyntacticTerm LIinf} (g : Stage) {α₀ : ThetaNote} :
      α ∈ H ∅ → paramsList Γ ⊆ H ∅ → stageAt a t ∈ Γ → g.1 < a.1 → g.1 < α → g.1 ∈ H ∅ →
      α₀ < α → IDerivable A ρ H α₀ (unfold A g t :: Γ) → IDerivable A ρ H α Γ
  /-- (V) for `¬I^{≺δ} t ≃ ⋀_{γ≺δ} ¬A(t, I^{≺γ})`, the premise for `γ` with `H[{γ}]`. -/
  | nstage {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote} {Γ : Sequent LIinf}
      {a : Stage} {t : SyntacticTerm LIinf} (f : Stage → ThetaNote) :
      α ∈ H ∅ → paramsList Γ ⊆ H ∅ → nstageAt a t ∈ Γ → (∀ g : Stage, g.1 < a.1 → f g < α) →
      (∀ g : Stage, g.1 < a.1 →
        IDerivable A ρ (ThetaNote.adjoin H {g.1}) (f g) (∼(unfold A g t) :: Γ)) →
      IDerivable A ρ H α Γ
  /-- (Fix): `Ω ⪯ α`, `I t = I^{≺Ω} t ∈ Γ`, premise `Γ, A(t, I^{≺Ω})`. -/
  | fix {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote} {Γ : Sequent LIinf}
      {t : SyntacticTerm LIinf} {α₀ : ThetaNote} :
      α ∈ H ∅ → paramsList Γ ⊆ H ∅ → IOmegaAt t ∈ Γ → ThetaNote.Omega ≤ α → α₀ < α →
      IDerivable A ρ H α₀ (unfold A Stage.top t :: Γ) → IDerivable A ρ H α Γ
  /-- (Cut): a cut formula of rank `≺ ρ`, both premises of the same height. -/
  | cut {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote} {Γ : Sequent LIinf}
      {ψ : Proposition LIinf} {α₀ : ThetaNote} :
      α ∈ H ∅ → paramsList Γ ⊆ H ∅ → rk ψ < ρ → α₀ < α →
      IDerivable A ρ H α₀ (ψ :: Γ) → IDerivable A ρ H α₀ (∼ψ :: Γ) → IDerivable A ρ H α Γ

namespace IDerivable

variable {A : Semisentence LXI 1} {ρ : ThetaNote} {H : Set ThetaNote → Set ThetaNote}
  {α : ThetaNote} {Γ : Sequent LIinf}

/-- **The initial condition** of Definition 5.6: `{α} ∪ k(Γ) ⊆ H(∅)`. -/
theorem control (d : IDerivable A ρ H α Γ) : α ∈ H ∅ ∧ paramsList Γ ⊆ H ∅ := by
  cases d <;> exact ⟨by assumption, by assumption⟩

theorem height_mem (d : IDerivable A ρ H α Γ) : α ∈ H ∅ := d.control.1

theorem params_subset (d : IDerivable A ρ H α Γ) : paramsList Γ ⊆ H ∅ := d.control.2

/-- The head formula of a derivable sequent has its parameters in `H(∅)`. -/
theorem params_head_subset {φ : Proposition LIinf} (d : IDerivable A ρ H α (φ :: Γ)) :
    params φ ⊆ H ∅ :=
  (params_subset_paramsList List.mem_cons_self).trans d.params_subset

/-- **Exercise 5.7 (b), cut rank**: `ρ ⪯ ρ'` gives `H ⊢^α_{ρ'} Γ`. -/
theorem mono_rank {ρ' : ThetaNote} (hρ : ρ ≤ ρ') (d : IDerivable A ρ H α Γ) :
    IDerivable A ρ' H α Γ := by
  induction d with
  | literal hα hΓ hφ hm => exact .literal hα hΓ hφ hm
  | verum hα hΓ hm => exact .verum hα hΓ hm
  | idX t hα hΓ h1 h2 => exact .idX t hα hΓ h1 h2
  | and hα hΓ hm h0 h1 _ _ ih0 ih1 => exact .and hα hΓ hm h0 h1 ih0 ih1
  | orL hα hΓ hm h0 _ ih => exact .orL hα hΓ hm h0 ih
  | orR hα hΓ hm h1 h0 _ ih => exact .orR hα hΓ hm h1 h0 ih
  | all f hα hΓ hm hf _ ih => exact .all f hα hΓ hm hf ih
  | exs n hα hΓ hm hn h0 _ ih => exact .exs n hα hΓ hm hn h0 ih
  | stage g hα hΓ hm hga hgα hgH h0 _ ih => exact .stage g hα hΓ hm hga hgα hgH h0 ih
  | nstage f hα hΓ hm hf _ ih => exact .nstage f hα hΓ hm hf ih
  | fix hα hΓ hm hΩ h0 _ ih => exact .fix hα hΓ hm hΩ h0 ih
  | cut hα hΓ hr h0 _ _ ih0 ih1 => exact .cut hα hΓ (lt_of_lt_of_le hr hρ) h0 ih0 ih1

/-- **Exercise 5.7 (b), height**: `α ⪯ α'` and `α' ∈ H(∅)` give `H ⊢^{α'}_ρ Γ`.  Only the
last inference changes. -/
theorem mono_height {α' : ThetaNote} (hα : α ≤ α') (hα' : α' ∈ H ∅)
    (d : IDerivable A ρ H α Γ) : IDerivable A ρ H α' Γ := by
  cases d with
  | literal _ hΓ hφ hm => exact .literal hα' hΓ hφ hm
  | verum _ hΓ hm => exact .verum hα' hΓ hm
  | idX t _ hΓ h1 h2 => exact .idX t hα' hΓ h1 h2
  | and _ hΓ hm h0 h1 d0 d1 =>
    exact .and hα' hΓ hm (lt_of_lt_of_le h0 hα) (lt_of_lt_of_le h1 hα) d0 d1
  | orL _ hΓ hm h0 d0 => exact .orL hα' hΓ hm (lt_of_lt_of_le h0 hα) d0
  | orR _ hΓ hm h1 h0 d0 =>
    exact .orR hα' hΓ hm (lt_of_lt_of_le h1 hα) (lt_of_lt_of_le h0 hα) d0
  | all f _ hΓ hm hf d0 => exact .all f hα' hΓ hm (fun n => lt_of_lt_of_le (hf n) hα) d0
  | exs n _ hΓ hm hn h0 d0 =>
    exact .exs n hα' hΓ hm (lt_of_lt_of_le hn hα) (lt_of_lt_of_le h0 hα) d0
  | stage g _ hΓ hm hga hgα hgH h0 d0 =>
    exact .stage g hα' hΓ hm hga (lt_of_lt_of_le hgα hα) hgH (lt_of_lt_of_le h0 hα) d0
  | nstage f _ hΓ hm hf d0 =>
    exact .nstage f hα' hΓ hm (fun g hg => lt_of_lt_of_le (hf g hg) hα) d0
  | fix _ hΓ hm hΩ h0 d0 => exact .fix hα' hΓ hm (le_trans hΩ hα) (lt_of_lt_of_le h0 hα) d0
  | cut _ hΓ hr h0 d0 d1 => exact .cut hα' hΓ hr (lt_of_lt_of_le h0 hα) d0 d1

/-- **Exercise 5.7 (a)**: `H(X) ⊆ H'(X)` for all `X` gives `H' ⊢^α_ρ Γ`. -/
theorem mono_op {H' : Set ThetaNote → Set ThetaNote} (hH : ∀ X, H X ⊆ H' X)
    (d : IDerivable A ρ H α Γ) : IDerivable A ρ H' α Γ := by
  induction d generalizing H' with
  | literal hα hΓ hφ hm => exact .literal (hH _ hα) (hΓ.trans (hH _)) hφ hm
  | verum hα hΓ hm => exact .verum (hH _ hα) (hΓ.trans (hH _)) hm
  | idX t hα hΓ h1 h2 => exact .idX t (hH _ hα) (hΓ.trans (hH _)) h1 h2
  | and hα hΓ hm h0 h1 _ _ ih0 ih1 =>
    exact .and (hH _ hα) (hΓ.trans (hH _)) hm h0 h1 (ih0 hH) (ih1 hH)
  | orL hα hΓ hm h0 _ ih => exact .orL (hH _ hα) (hΓ.trans (hH _)) hm h0 (ih hH)
  | orR hα hΓ hm h1 h0 _ ih => exact .orR (hH _ hα) (hΓ.trans (hH _)) hm h1 h0 (ih hH)
  | all f hα hΓ hm hf _ ih => exact .all f (hH _ hα) (hΓ.trans (hH _)) hm hf (fun n => ih n hH)
  | exs n hα hΓ hm hn h0 _ ih => exact .exs n (hH _ hα) (hΓ.trans (hH _)) hm hn h0 (ih hH)
  | stage g hα hΓ hm hga hgα hgH h0 _ ih =>
    exact .stage g (hH _ hα) (hΓ.trans (hH _)) hm hga hgα (hH _ hgH) h0 (ih hH)
  | nstage f hα hΓ hm hf _ ih =>
    exact .nstage f (hH _ hα) (hΓ.trans (hH _)) hm hf
      (fun g hg => ih g hg (H' := ThetaNote.adjoin H' {g.1}) (fun X => hH _))
  | fix hα hΓ hm hΩ h0 _ ih => exact .fix (hH _ hα) (hΓ.trans (hH _)) hm hΩ h0 (ih hH)
  | cut hα hΓ hr h0 _ _ ih0 ih1 =>
    exact .cut (hH _ hα) (hΓ.trans (hH _)) hr h0 (ih0 hH) (ih1 hH)

/-- **Exercise 5.7 (b)**: `H ⊢^α_ρ Γ` gives `H ⊢^{α'}_ρ Γ'` for `α ⪯ α'`, `Γ ⊆ Γ'` and
`{α'} ∪ k(Γ') ⊆ H(∅)`.  Together with `mono_rank` this is the full exercise; it also covers
the reordering and the duplication of formulas. -/
theorem weaken (hH : ThetaNote.IsOperator H) (d : IDerivable A ρ H α Γ) {α' : ThetaNote}
    {Γ' : Sequent LIinf} (hα : α ≤ α') (hΓ : Γ ⊆ Γ') (hα' : α' ∈ H ∅)
    (hΓ' : paramsList Γ' ⊆ H ∅) : IDerivable A ρ H α' Γ' := by
  induction d generalizing α' Γ' with
  | literal _ _ hφ hm => exact .literal hα' hΓ' hφ (hΓ hm)
  | verum _ _ hm => exact .verum hα' hΓ' (hΓ hm)
  | idX t _ _ h1 h2 => exact .idX t hα' hΓ' (hΓ h1) (hΓ h2)
  | and _ _ hm h0 h1 d0 d1 ih0 ih1 =>
    exact .and hα' hΓ' (hΓ hm) (lt_of_lt_of_le h0 hα) (lt_of_lt_of_le h1 hα)
      (ih0 hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsList_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
      (ih1 hH le_rfl (List.cons_subset_cons _ hΓ) d1.height_mem
        (by rw [paramsList_cons]; exact Set.union_subset d1.params_head_subset hΓ'))
  | orL _ _ hm h0 d0 ih =>
    exact .orL hα' hΓ' (hΓ hm) (lt_of_lt_of_le h0 hα)
      (ih hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsList_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
  | orR _ _ hm h1 h0 d0 ih =>
    exact .orR hα' hΓ' (hΓ hm) (lt_of_lt_of_le h1 hα) (lt_of_lt_of_le h0 hα)
      (ih hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsList_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
  | all f _ _ hm hf d0 ih =>
    exact .all f hα' hΓ' (hΓ hm) (fun n => lt_of_lt_of_le (hf n) hα) fun n =>
      ih n hH le_rfl (List.cons_subset_cons _ hΓ) (d0 n).height_mem
        (by rw [paramsList_cons]; exact Set.union_subset (d0 n).params_head_subset hΓ')
  | exs n _ _ hm hn h0 d0 ih =>
    exact .exs n hα' hΓ' (hΓ hm) (lt_of_lt_of_le hn hα) (lt_of_lt_of_le h0 hα)
      (ih hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsList_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
  | stage g _ _ hm hga hgα hgH h0 d0 ih =>
    exact .stage g hα' hΓ' (hΓ hm) hga (lt_of_lt_of_le hgα hα) hgH (lt_of_lt_of_le h0 hα)
      (ih hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsList_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
  | nstage f _ _ hm hf d0 ih =>
    refine .nstage f hα' hΓ' (hΓ hm) (fun g hg => lt_of_lt_of_le (hf g hg) hα) fun g hg => ?_
    have hH' := hH.adjoin {g.1}
    exact ih g hg hH' le_rfl (List.cons_subset_cons _ hΓ) (d0 g hg).height_mem
      (by
        rw [paramsList_cons]
        exact Set.union_subset (d0 g hg).params_head_subset
          (hΓ'.trans (hH.mono (Set.empty_subset _))))
  | fix _ _ hm hΩ h0 d0 ih =>
    exact .fix hα' hΓ' (hΓ hm) (le_trans hΩ hα) (lt_of_lt_of_le h0 hα)
      (ih hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsList_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
  | cut _ _ hr h0 d0 d1 ih0 ih1 =>
    exact .cut hα' hΓ' hr (lt_of_lt_of_le h0 hα)
      (ih0 hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsList_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
      (ih1 hH le_rfl (List.cons_subset_cons _ hΓ) d1.height_mem
        (by rw [paramsList_cons]; exact Set.union_subset d1.params_head_subset hΓ'))

/-- Weakening of the sequent alone. -/
theorem weaken_seq (hH : ThetaNote.IsOperator H) (d : IDerivable A ρ H α Γ) {Γ' : Sequent LIinf}
    (hΓ : Γ ⊆ Γ') (hΓ' : paramsList Γ' ⊆ H ∅) : IDerivable A ρ H α Γ' :=
  d.weaken hH le_rfl hΓ d.height_mem hΓ'

/-- `H ⊢ Γ` gives `H[Z] ⊢ Γ` (Exercise 5.7 (a) with `H(X) ⊆ H(Z ∪ X)`). -/
theorem adjoin (hH : ThetaNote.IsOperator H) (Z : Set ThetaNote) (d : IDerivable A ρ H α Γ) :
    IDerivable A ρ (ThetaNote.adjoin H Z) α Γ :=
  d.mono_op fun _ => hH.mono Set.subset_union_right

/-- **`H ⊢^α_ρ Γ` weakens to `H[k(Δ)] ⊢^α_ρ Γ, Δ`** (Freund, after Definition 5.6). -/
theorem weaken_adjoin (hH : ThetaNote.IsOperator H) (d : IDerivable A ρ H α Γ)
    (Δ : Sequent LIinf) : IDerivable A ρ (ThetaNote.adjoin H (paramsList Δ)) α (Γ ++ Δ) := by
  have hH' := hH.adjoin (paramsList Δ)
  have hsub : H ∅ ⊆ ThetaNote.adjoin H (paramsList Δ) ∅ := hH.mono (Set.empty_subset _)
  refine (d.adjoin hH (paramsList Δ)).weaken_seq hH' (List.subset_append_left _ _) ?_
  rw [paramsList_append]
  exact Set.union_subset (d.params_subset.trans hsub)
    (Set.subset_union_left.trans (hH.subset _))

end IDerivable

/-! ### Inversion (Exercise 7.1 (a))

For a conjunctive formula `ψ ≃ ⋀_{γ≺δ} ψ_γ`, `H ⊢^α_ρ Γ, ψ` gives `H ⊢^α_ρ Γ, ψ_γ` for every
`γ ≺ δ` with `γ ∈ H(∅)` (Freund, Exercise 7.1 (a)).  The conjunctive formulas with premises
are `ψ₀ ∧ ψ₁`, `∀x ψ(x)` and `¬I^{≺δ} t`; none of them is the principal formula of a
disjunctive clause or of (Fix), whose principal formula `I^{≺Ω} t` is disjunctive.  For
`¬I^{≺δ} t` the premise for `γ` carries `H[{γ}]`, which is `H` when `γ ∈ H(∅)`
(Exercise 5.5 (c)).

The three cases share one induction (`inv_aux`): `InvShape A G ψ χ` says that `χ` is a
component of the conjunctive formula `ψ`, that `ψ` has no other shape, and, for `¬I^{≺δ} t`,
that the index of the component satisfies `G` (the index is not determined by the
component when `A` does not mention `I`). -/

/-- `χ` is a component `ψ_γ` of the conjunctive formula `ψ`, and `ψ` is not the principal
formula of any other clause; a stage index of the component satisfies `G`. -/
structure InvShape (A : Semisentence LXI 1) (G : Stage → Prop) (ψ χ : Proposition LIinf) :
    Prop where
  not_lit : ¬TrueLit ψ
  ne_verum : ψ ≠ ⊤
  ne_X : ∀ t : SyntacticTerm LIinf, ψ ≠ XinfAt t
  ne_nX : ∀ t : SyntacticTerm LIinf, ψ ≠ ∼(XinfAt t)
  ne_or : ∀ φ₀ φ₁ : Proposition LIinf, ψ ≠ φ₀ ⋎ φ₁
  ne_exs : ∀ φ : Semiproposition LIinf 1, ψ ≠ ∃¹ φ
  ne_stage : ∀ (a : Stage) (t : SyntacticTerm LIinf), ψ ≠ stageAt a t
  of_and : ∀ φ₀ φ₁ : Proposition LIinf, ψ = φ₀ ⋏ φ₁ → χ = φ₀ ∨ χ = φ₁
  of_all : ∀ φ : Semiproposition LIinf 1, ψ = ∀¹ φ → ∃ n : ℕ, χ = φ/[numI n]
  of_nstage : ∀ (a : Stage) (t : SyntacticTerm LIinf), ψ = nstageAt a t →
    ∃ g : Stage, g.1 < a.1 ∧ χ = ∼(unfold A g t) ∧ G g

namespace IDerivable

variable {A : Semisentence LXI 1} {ρ : ThetaNote}

/-- The statement of inversion for a derivation of `Δ`. -/
def InvClaim (A : Semisentence LXI 1) (ρ : ThetaNote) (G : Stage → Prop)
    (ψ χ : Proposition LIinf) (H : Set ThetaNote → Set ThetaNote) (α : ThetaNote)
    (Δ : Sequent LIinf) : Prop :=
  ThetaNote.IsOperator H → (∀ g : Stage, G g → g.1 ∈ H ∅) →
    ∀ Γ : Sequent LIinf, Δ ⊆ ψ :: Γ → paramsList (χ :: Γ) ⊆ H ∅ →
      IDerivable A ρ H α (χ :: Γ)

theorem mem_inv {ψ χ θ : Proposition LIinf} {Δ Γ : Sequent LIinf} (hθ : θ ∈ Δ)
    (hΔ : Δ ⊆ ψ :: Γ) (hne : θ ≠ ψ) : θ ∈ χ :: Γ := by
  rcases List.mem_cons.mp (hΔ hθ) with h | h
  · exact absurd h hne
  · exact List.mem_cons_of_mem _ h

theorem inv_prem {G : Stage → Prop} {ψ χ φ : Proposition LIinf}
    {H : Set ThetaNote → Set ThetaNote} {α₀ : ThetaNote} {Δ Γ : Sequent LIinf}
    (hH : ThetaNote.IsOperator H) (hγ : ∀ g : Stage, G g → g.1 ∈ H ∅)
    (d₀ : IDerivable A ρ H α₀ (φ :: Δ)) (ih₀ : InvClaim A ρ G ψ χ H α₀ (φ :: Δ))
    (hΔ : Δ ⊆ ψ :: Γ) (hP : paramsList (χ :: Γ) ⊆ H ∅) :
    IDerivable A ρ H α₀ (φ :: χ :: Γ) := by
  have hφ : params φ ⊆ H ∅ := d₀.params_head_subset
  rw [paramsList_cons] at hP
  have h1 := ih₀ hH hγ (φ :: Γ)
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · rcases List.mem_cons.mp (hΔ hx) with h | h
        · exact h ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    (by
      rw [paramsList_cons, paramsList_cons]
      exact Set.union_subset (Set.subset_union_left.trans hP)
        (Set.union_subset hφ (Set.subset_union_right.trans hP)))
  refine h1.weaken_seq hH ?_ ?_
  · intro x hx
    simp only [List.mem_cons] at hx ⊢
    tauto
  · rw [paramsList_cons, paramsList_cons]
    exact Set.union_subset hφ hP

/-- The principal case: the component was derived, as the head of `χ :: χ :: Γ`, at a
height below `α`. -/
theorem inv_principal {χ : Proposition LIinf} {H : Set ThetaNote → Set ThetaNote}
    {α α₀ : ThetaNote} {Γ : Sequent LIinf} (hH : ThetaNote.IsOperator H) (hα : α ∈ H ∅)
    (h0 : α₀ < α) (d : IDerivable A ρ H α₀ (χ :: χ :: Γ)) (hP : paramsList (χ :: Γ) ⊆ H ∅) :
    IDerivable A ρ H α (χ :: Γ) :=
  d.weaken hH (le_of_lt h0)
    (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hα hP

theorem inv_aux {G : Stage → Prop} {ψ χ : Proposition LIinf} (hs : InvShape A G ψ χ)
    {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote} {Δ : Sequent LIinf}
    (d : IDerivable A ρ H α Δ) : InvClaim A ρ G ψ χ H α Δ := by
  induction d with
  | literal hα _ hφ hm =>
    intro hH hγ Γ hΔ hP
    exact .literal hα hP hφ (mem_inv hm hΔ fun h => hs.not_lit (h ▸ hφ))
  | verum hα _ hm =>
    intro hH hγ Γ hΔ hP
    exact .verum hα hP (mem_inv hm hΔ fun h => hs.ne_verum h.symm)
  | idX t hα _ h1 h2 =>
    intro hH hγ Γ hΔ hP
    exact .idX t hα hP (mem_inv h1 hΔ fun h => hs.ne_X t h.symm)
      (mem_inv h2 hΔ fun h => hs.ne_nX t h.symm)
  | @and H α Δ φ₀ φ₁ α₀ α₁ hα _ hm h0 h1 d0 d1 ih0 ih1 =>
    intro hH hγ Γ hΔ hP
    have p0 := inv_prem hH hγ d0 ih0 hΔ hP
    have p1 := inv_prem hH hγ d1 ih1 hΔ hP
    by_cases he : φ₀ ⋏ φ₁ = ψ
    · rcases hs.of_and φ₀ φ₁ he.symm with rfl | rfl
      · exact inv_principal hH hα h0 p0 hP
      · exact inv_principal hH hα h1 p1 hP
    · exact .and hα hP (mem_inv hm hΔ he) h0 h1 p0 p1
  | orL hα _ hm h0 d0 ih0 =>
    intro hH hγ Γ hΔ hP
    exact .orL hα hP (mem_inv hm hΔ fun h => hs.ne_or _ _ h.symm) h0
      (inv_prem hH hγ d0 ih0 hΔ hP)
  | orR hα _ hm h1 h0 d0 ih0 =>
    intro hH hγ Γ hΔ hP
    exact .orR hα hP (mem_inv hm hΔ fun h => hs.ne_or _ _ h.symm) h1 h0
      (inv_prem hH hγ d0 ih0 hΔ hP)
  | @all H α Δ φ f hα _ hm hf d0 ih0 =>
    intro hH hγ Γ hΔ hP
    have p0 := fun n => inv_prem hH hγ (d0 n) (ih0 n) hΔ hP
    by_cases he : (∀¹ φ) = ψ
    · obtain ⟨n, rfl⟩ := hs.of_all φ he.symm
      exact inv_principal hH hα (hf n) (p0 n) hP
    · exact .all f hα hP (mem_inv hm hΔ he) hf p0
  | exs n hα _ hm hn h0 d0 ih0 =>
    intro hH hγ Γ hΔ hP
    exact .exs n hα hP (mem_inv hm hΔ fun h => hs.ne_exs _ h.symm) hn h0
      (inv_prem hH hγ d0 ih0 hΔ hP)
  | stage g hα _ hm hga hgα hgH h0 d0 ih0 =>
    intro hH hγ Γ hΔ hP
    exact .stage g hα hP (mem_inv hm hΔ fun h => hs.ne_stage _ _ h.symm) hga hgα hgH h0
      (inv_prem hH hγ d0 ih0 hΔ hP)
  | @nstage H α Δ a t f hα _ hm hf d0 ih0 =>
    intro hH hγ Γ hΔ hP
    have p0 : ∀ g : Stage, g.1 < a.1 →
        IDerivable A ρ (ThetaNote.adjoin H {g.1}) (f g) (∼(unfold A g t) :: χ :: Γ) := by
      intro g hg
      have hsub : H ∅ ⊆ ThetaNote.adjoin H {g.1} ∅ := hH.mono (Set.empty_subset _)
      exact inv_prem (hH.adjoin {g.1}) (fun g' hg' => hsub (hγ g' hg'))
        (d0 g hg) (ih0 g hg) hΔ (hP.trans hsub)
    by_cases he : nstageAt a t = ψ
    · obtain ⟨g, hg, rfl, hG⟩ := hs.of_nstage a t he.symm
      have e : ThetaNote.adjoin H {g.1} = H :=
        ThetaNote.adjoin_eq_self hH (Set.singleton_subset_iff.mpr (hγ g hG))
      have p := p0 g hg
      rw [e] at p
      exact inv_principal hH hα (hf g hg) p hP
    · exact .nstage f hα hP (mem_inv hm hΔ he) hf p0
  | fix hα _ hm hΩ h0 d0 ih0 =>
    intro hH hγ Γ hΔ hP
    exact .fix hα hP (mem_inv hm hΔ fun h => hs.ne_stage _ _ h.symm) hΩ h0
      (inv_prem hH hγ d0 ih0 hΔ hP)
  | cut hα _ hr h0 d0 d1 ih0 ih1 =>
    intro hH hγ Γ hΔ hP
    exact .cut hα hP hr h0 (inv_prem hH hγ d0 ih0 hΔ hP) (inv_prem hH hγ d1 ih1 hΔ hP)

variable {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote} {Γ : Sequent LIinf}

theorem inv_of_shape {G : Stage → Prop} {ψ χ : Proposition LIinf} (hs : InvShape A G ψ χ)
    (hH : ThetaNote.IsOperator H) (hγ : ∀ g : Stage, G g → g.1 ∈ H ∅)
    (hχ : params χ ⊆ H ∅) (d : IDerivable A ρ H α (ψ :: Γ)) :
    IDerivable A ρ H α (χ :: Γ) := by
  refine inv_aux hs d hH hγ Γ (List.Subset.refl _) ?_
  have h := d.params_subset
  rw [paramsList_cons] at h ⊢
  exact Set.union_subset hχ (Set.subset_union_right.trans h)

/-- **Exercise 7.1 (a) for `∧`**, left component. -/
theorem inv_and_left (hH : ThetaNote.IsOperator H) {φ₀ φ₁ : Proposition LIinf}
    (d : IDerivable A ρ H α (φ₀ ⋏ φ₁ :: Γ)) : IDerivable A ρ H α (φ₀ :: Γ) :=
  inv_of_shape (G := fun _ => False) (ψ := φ₀ ⋏ φ₁)
    ⟨(fun h => by obtain ⟨⟨k, r, v, (h | h), -⟩, -⟩ := h <;> exact nomatch h),
      (fun h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ h => by cases h; exact Or.inl rfl), (fun _ h => nomatch h),
      (fun _ _ h => nomatch h)⟩
    hH (fun _ h => h.elim) (Set.subset_union_left.trans d.params_head_subset) d

/-- **Exercise 7.1 (a) for `∧`**, right component. -/
theorem inv_and_right (hH : ThetaNote.IsOperator H) {φ₀ φ₁ : Proposition LIinf}
    (d : IDerivable A ρ H α (φ₀ ⋏ φ₁ :: Γ)) : IDerivable A ρ H α (φ₁ :: Γ) :=
  inv_of_shape (G := fun _ => False) (ψ := φ₀ ⋏ φ₁)
    ⟨(fun h => by obtain ⟨⟨k, r, v, (h | h), -⟩, -⟩ := h <;> exact nomatch h),
      (fun h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ h => by cases h; exact Or.inr rfl), (fun _ h => nomatch h),
      (fun _ _ h => nomatch h)⟩
    hH (fun _ h => h.elim) (Set.subset_union_right.trans d.params_head_subset) d

/-- **Exercise 7.1 (a) for `∀`**: `H ⊢^α_ρ Γ, ∀x φ(x)` gives `H ⊢^α_ρ Γ, φ(n̄)`. -/
theorem inv_all (hH : ThetaNote.IsOperator H) {φ : Semiproposition LIinf 1} (n : ℕ)
    (d : IDerivable A ρ H α ((∀¹ φ) :: Γ)) : IDerivable A ρ H α (φ/[numI n] :: Γ) :=
  inv_of_shape (G := fun _ => False) (ψ := ∀¹ φ)
    ⟨(fun h => by obtain ⟨⟨k, r, v, (h | h), -⟩, -⟩ := h <;> exact nomatch h),
      (fun h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => by cases h; exact ⟨n, rfl⟩),
      (fun _ _ h => nomatch h)⟩
    hH (fun _ h => h.elim) ((le_of_eq (params_subst φ _)).trans d.params_head_subset) d

/-- **Exercise 7.1 (a) for `¬I^{≺δ} t`**: `H ⊢^α_ρ Γ, ¬I^{≺δ} t` gives
`H ⊢^α_ρ Γ, ¬A(t, I^{≺γ})` for `γ ≺ δ` with `γ ∈ H(∅)`. -/
theorem inv_nstage (hH : ThetaNote.IsOperator H) {a g : Stage} {t : SyntacticTerm LIinf}
    (hg : g.1 < a.1) (hgH : g.1 ∈ H ∅) (d : IDerivable A ρ H α (nstageAt a t :: Γ)) :
    IDerivable A ρ H α (∼(unfold A g t) :: Γ) :=
  inv_of_shape (G := fun g' => g' = g) (ψ := nstageAt a t)
    ⟨(fun h => by
        obtain ⟨⟨k, r, v, (h | h), -⟩, -⟩ := h
        · exact nomatch h
        · have := congrArg negHeadStage h
          exact nomatch this),
      (fun h => nomatch h), (fun _ h => nomatch h),
      (fun _ h => by have := congrArg negHeadStage h; exact nomatch this),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h),
      fun a' t' h => by
        obtain ⟨rfl, rfl⟩ := nstageAt_inj h
        exact ⟨g, hg, rfl, rfl⟩⟩
    hH (fun g' h => h ▸ hgH)
    (by
      rw [params_neg]
      exact (params_unfold A g t).trans (Set.singleton_subset_iff.mpr hgH)) d

end IDerivable

/-! ### Exercise 5.5 (e), formula half -/

section Rank

variable {H : Set ThetaNote → Set ThetaNote} {ξ : Type*} {n : ℕ}

/-- **Freund, Exercise 5.5 (e)**: for a nice operator, `k(ψ) ⊆ H(X)` gives
`rk(ψ) ∈ H(X)`. -/
theorem _root_.OrdinalAnalysis.ThetaNote.Nice.rk_mem (hH : ThetaNote.Nice H)
    {X : Set ThetaNote} {φ : Semiformula LIinf ξ n} (h : params φ ⊆ H X) : rk φ ∈ H X :=
  rk_mem_of_closed hH.zero_mem (fun _ hx => hH.omegaMul_mem hx) (fun _ hx => hH.succ_mem hx) h

/-- **Freund, Exercise 5.5 (e)**: `rk(ψ) ∈ H(k(ψ))` for a nice operator. -/
theorem _root_.OrdinalAnalysis.ThetaNote.Nice.rk_mem_params (hH : ThetaNote.Nice H)
    (φ : Semiformula LIinf ξ n) : rk φ ∈ H (params φ) :=
  hH.rk_mem (hH.isOperator.subset _)

end Rank

end InductiveDef

end OrdinalAnalysis
