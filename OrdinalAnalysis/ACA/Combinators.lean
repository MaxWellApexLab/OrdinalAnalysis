/-
  Propositional and quantifier combinators for
  `Provable`, built on a **sequent-level** provability predicate `PSeq`.

  Why `PSeq`.  `Toolkit.lean` works one formula at a time (`mp`, `cutP`,
  `spec₁/₂`, `gen₁/₂`), which is enough for "apply an axiom" but painful for
  everything propositional: a one-sided calculus proves *sequents*, and each
  derived rule stated at the level of a single `Provable` formula has to
  re-do the same weakening/`cut` bookkeeping by hand.  `PSeq 𝓢 Γ` ("the sequent
  `Γ` is derivable from finitely many axioms of `𝓢`") absorbs that bookkeeping
  once: it satisfies every rule of the calculus plus the *invertibility* rules
  for `⋏`/`⋎`, and `Provable 𝓢 φ ↔ PSeq 𝓢 [φ]`.  Every combinator below is then
  three or four lines.

  Nothing here adds a `Derivation` constructor — 2e replays the primitive
  constructors of `LK.lean`, and this file must not add to their number.
-/
import OrdinalAnalysis.ACA.Toolkit

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder

variable {𝓢 : Set (Proposition ℒₒᵣ)}

/-! ### Provability of a sequent -/

/-- **`𝓢 ⊢ Γ`**: the sequent `Γ` is derivable from finitely many instances of
the schema `𝓢`.  `Provable 𝓢 φ` is the one-formula case (`provable_iff_pseq`). -/
def PSeq (𝓢 : Set (Proposition ℒₒᵣ)) (Γ : SecondOrder.Sequent ℒₒᵣ) : Prop :=
  ∃ Δ : SecondOrder.Sequent ℒₒᵣ, (∀ χ ∈ Δ, χ ∈ 𝓢) ∧ Nonempty (Derivation (Γ ++ ∼Δ))

theorem provable_iff_pseq {φ : Proposition ℒₒᵣ} : Provable 𝓢 φ ↔ PSeq 𝓢 [φ] := by
  constructor
  · intro h
    obtain ⟨Δ, hΔ, ⟨d⟩⟩ := provable_iff.mp h
    exact ⟨Δ, hΔ, ⟨d⟩⟩
  · rintro ⟨Δ, hΔ, ⟨d⟩⟩
    exact provable_iff.mpr ⟨Δ, hΔ, ⟨d⟩⟩

/-- A provable formula, as a one-element sequent. -/
theorem PSeq.of_provable {φ : Proposition ℒₒᵣ} (h : Provable 𝓢 φ) : PSeq 𝓢 [φ] :=
  provable_iff_pseq.mp h

/-- A one-element sequent, as a provable formula. -/
theorem PSeq.to_provable {φ : Proposition ℒₒᵣ} (h : PSeq 𝓢 [φ]) : Provable 𝓢 φ :=
  provable_iff_pseq.mpr h

/-! #### The rules of the calculus, at the `PSeq` level -/

theorem PSeq.wk {Γ Γ' : SecondOrder.Sequent ℒₒᵣ} (hsub : Γ ⊆ Γ') (h : PSeq 𝓢 Γ) : PSeq 𝓢 Γ' := by
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := h
  refine ⟨Δ, hΔ, ⟨Derivation.wk d ?_⟩⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  exacts [List.mem_append_left _ (hsub hx), List.mem_append_right _ hx]

/-- **A provable formula may be inserted anywhere.** -/
theorem PSeq.ofProvable {φ : Proposition ℒₒᵣ} (h : Provable 𝓢 φ)
    (Γ : SecondOrder.Sequent ℒₒᵣ) : PSeq 𝓢 (φ :: Γ) :=
  PSeq.wk (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
    (PSeq.of_provable h)

/-- **`identity`, in an arbitrary context.** -/
theorem PSeq.id {Γ : SecondOrder.Sequent ℒₒᵣ} {φ : Proposition ℒₒᵣ} (hφ : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    PSeq 𝓢 Γ :=
  ⟨[], by simp, ⟨Derivation.wk (Derivation.identity (φ := φ)) (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [SecondOrder.Sequent.tilde_nil, List.append_nil]
    rcases hx with rfl | rfl
    exacts [hφ, hn])⟩⟩

/-- **`verum`, in an arbitrary context.** -/
theorem PSeq.verum {Γ : SecondOrder.Sequent ℒₒᵣ} (h : (⊤ : Proposition ℒₒᵣ) ∈ Γ) : PSeq 𝓢 Γ :=
  ⟨[], by simp, ⟨Derivation.wk Derivation.verum (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [SecondOrder.Sequent.tilde_nil, List.append_nil]
    rcases hx with rfl
    exact h)⟩⟩

/-- **`cut`.** -/
theorem PSeq.cut {Γ : SecondOrder.Sequent ℒₒᵣ} (φ : Proposition ℒₒᵣ)
    (hp : PSeq 𝓢 (φ :: Γ)) (hn : PSeq 𝓢 (∼φ :: Γ)) : PSeq 𝓢 Γ := by
  obtain ⟨Δ₁, hΔ₁, ⟨d₁⟩⟩ := hp
  obtain ⟨Δ₂, hΔ₂, ⟨d₂⟩⟩ := hn
  refine ⟨Δ₁ ++ Δ₂, ?_, ⟨?_⟩⟩
  · intro χ hχ
    rcases List.mem_append.mp hχ with h | h
    exacts [hΔ₁ _ h, hΔ₂ _ h]
  · have htl : (∼(Δ₁ ++ Δ₂) : SecondOrder.Sequent ℒₒᵣ) = (∼Δ₁) ++ (∼Δ₂) := by simp
    rw [htl]
    have hsub₁ : φ :: (Γ ++ ∼Δ₁) ⊆ φ :: (Γ ++ ((∼Δ₁) ++ (∼Δ₂))) := by
      intro x hx; simp only [List.mem_cons, List.mem_append] at hx ⊢; tauto
    have hsub₂ : (∼φ) :: (Γ ++ ∼Δ₂) ⊆ (∼φ) :: (Γ ++ ((∼Δ₁) ++ (∼Δ₂))) := by
      intro x hx; simp only [List.mem_cons, List.mem_append] at hx ⊢; tauto
    exact Derivation.cut (Derivation.wk d₁ hsub₁) (Derivation.wk d₂ hsub₂)

/-- **`and`.** -/
theorem PSeq.and {Γ : SecondOrder.Sequent ℒₒᵣ} {φ χ : Proposition ℒₒᵣ}
    (hp : PSeq 𝓢 (φ :: Γ)) (hq : PSeq 𝓢 (χ :: Γ)) : PSeq 𝓢 ((φ ⋏ χ) :: Γ) := by
  obtain ⟨Δ₁, hΔ₁, ⟨d₁⟩⟩ := hp
  obtain ⟨Δ₂, hΔ₂, ⟨d₂⟩⟩ := hq
  refine ⟨Δ₁ ++ Δ₂, ?_, ⟨?_⟩⟩
  · intro ρ hρ
    rcases List.mem_append.mp hρ with h | h
    exacts [hΔ₁ _ h, hΔ₂ _ h]
  · have htl : (∼(Δ₁ ++ Δ₂) : SecondOrder.Sequent ℒₒᵣ) = (∼Δ₁) ++ (∼Δ₂) := by simp
    rw [htl]
    have hsub₁ : φ :: (Γ ++ ∼Δ₁) ⊆ φ :: (Γ ++ ((∼Δ₁) ++ (∼Δ₂))) := by
      intro x hx; simp only [List.mem_cons, List.mem_append] at hx ⊢; tauto
    have hsub₂ : χ :: (Γ ++ ∼Δ₂) ⊆ χ :: (Γ ++ ((∼Δ₁) ++ (∼Δ₂))) := by
      intro x hx; simp only [List.mem_cons, List.mem_append] at hx ⊢; tauto
    exact Derivation.and (Derivation.wk d₁ hsub₁) (Derivation.wk d₂ hsub₂)

/-- **`or`.** -/
theorem PSeq.or {Γ : SecondOrder.Sequent ℒₒᵣ} {φ χ : Proposition ℒₒᵣ}
    (h : PSeq 𝓢 (φ :: χ :: Γ)) : PSeq 𝓢 ((φ ⋎ χ) :: Γ) := by
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := h
  exact ⟨Δ, hΔ, ⟨Derivation.or d⟩⟩

/-- **`exs₁`.** -/
theorem PSeq.exs₁ {Γ : SecondOrder.Sequent ℒₒᵣ} {φ : Semiproposition ℒₒᵣ 0 1}
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ 0) (h : PSeq 𝓢 ((φ/[t]) :: Γ)) : PSeq 𝓢 ((∃¹ φ) :: Γ) := by
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := h
  exact ⟨Δ, hΔ, ⟨Derivation.exs₁ d⟩⟩

/-- **`exs₂` — arithmetical comprehension.** -/
theorem PSeq.exs₂ {Γ : SecondOrder.Sequent ℒₒᵣ} {φ : Semiproposition ℒₒᵣ 1 0}
    {χ : Semiformula ℒₒᵣ ℕ ℕ 0 1} (hχ : Arith χ) (h : PSeq 𝓢 ((φ/⟦χ⟧) :: Γ)) :
    PSeq 𝓢 ((∃² φ) :: Γ) := by
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := h
  exact ⟨Δ, hΔ, ⟨Derivation.exs₂ hχ d⟩⟩

private theorem shift₀_tilde {Δ : SecondOrder.Sequent ℒₒᵣ}
    (h : ∀ χ ∈ Δ, Semiproposition.shift₀ χ = χ) :
    List.map Semiproposition.shift₀ (∼Δ) = ∼Δ := by
  induction Δ with
  | nil => rfl
  | cons a l ih =>
      have ha : Semiproposition.shift₀ a = a := h a List.mem_cons_self
      have hl : List.map Semiproposition.shift₀ (∼l) = ∼l :=
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      simp [LogicalConnective.HomClass.map_neg, ha, hl]

private theorem shift₁_tilde {Δ : SecondOrder.Sequent ℒₒᵣ}
    (h : ∀ χ ∈ Δ, Semiproposition.shift₁ χ = χ) :
    List.map Semiproposition.shift₁ (∼Δ) = ∼Δ := by
  induction Δ with
  | nil => rfl
  | cons a l ih =>
      have ha : Semiproposition.shift₁ a = a := h a List.mem_cons_self
      have hl : List.map Semiproposition.shift₁ (∼l) = ∼l :=
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      simp [LogicalConnective.HomClass.map_neg, ha, hl]

/-- **`all₁`.**  Needs every axiom of `𝓢` to be `shift₀`-fixed
(`ACA_shift₀_invariant`). -/
theorem PSeq.all₁ (h𝓢 : ∀ χ ∈ 𝓢, Semiproposition.shift₀ χ = χ)
    {Γ : SecondOrder.Sequent ℒₒᵣ} {φ : Semiproposition ℒₒᵣ 0 1}
    (h : PSeq 𝓢 (φ.free₀ :: SecondOrder.Sequent.shift₀ Γ)) : PSeq 𝓢 ((∀¹ φ) :: Γ) := by
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := h
  refine ⟨Δ, hΔ, ⟨Derivation.all₁ (Derivation.cast d ?_)⟩⟩
  show (φ.free₀ :: SecondOrder.Sequent.shift₀ Γ) ++ ∼Δ =
    φ.free₀ :: SecondOrder.Sequent.shift₀ (Γ ++ ∼Δ)
  simp only [SecondOrder.Sequent.shift₀, List.cons_append, List.map_append,
    shift₀_tilde (fun x hx => h𝓢 x (hΔ x hx))]

/-- **`all₂`.**  Needs every axiom of `𝓢` to be `shift₁`-fixed
(`ACA_shift₁_invariant`). -/
theorem PSeq.all₂ (h𝓢 : ∀ χ ∈ 𝓢, Semiproposition.shift₁ χ = χ)
    {Γ : SecondOrder.Sequent ℒₒᵣ} {φ : Semiproposition ℒₒᵣ 1 0}
    (h : PSeq 𝓢 (φ.free₁ :: SecondOrder.Sequent.shift₁ Γ)) : PSeq 𝓢 ((∀² φ) :: Γ) := by
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := h
  refine ⟨Δ, hΔ, ⟨Derivation.all₂ (Derivation.cast d ?_)⟩⟩
  show (φ.free₁ :: SecondOrder.Sequent.shift₁ Γ) ++ ∼Δ =
    φ.free₁ :: SecondOrder.Sequent.shift₁ (Γ ++ ∼Δ)
  simp only [SecondOrder.Sequent.shift₁, List.cons_append, List.map_append,
    shift₁_tilde (fun x hx => h𝓢 x (hΔ x hx))]

/-! #### Invertibility

The two rules a one-sided calculus does *not* have as constructors, and the
reason `PSeq` is worth having: they turn a hypothesis `Provable 𝓢 (φ ⋎ χ)`
(in particular `Provable 𝓢 (φ 🡒 χ)`) into usable sequent material. -/

/-- **`⋎` is invertible.** -/
theorem PSeq.orInv {Γ : SecondOrder.Sequent ℒₒᵣ} {φ χ : Proposition ℒₒᵣ}
    (h : PSeq 𝓢 ((φ ⋎ χ) :: Γ)) : PSeq 𝓢 (φ :: χ :: Γ) := by
  refine PSeq.cut (φ ⋎ χ) (PSeq.wk ?_ h) ?_
  · intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  · exact PSeq.and (PSeq.id (φ := φ) (by simp) List.mem_cons_self)
      (PSeq.id (φ := χ) (by simp) List.mem_cons_self)

/-- **`⋏` is invertible** (left component). -/
theorem PSeq.andInvL {Γ : SecondOrder.Sequent ℒₒᵣ} {φ χ : Proposition ℒₒᵣ}
    (h : PSeq 𝓢 ((φ ⋏ χ) :: Γ)) : PSeq 𝓢 (φ :: Γ) := by
  refine PSeq.cut (φ ⋏ χ) (PSeq.wk ?_ h) ?_
  · intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  · exact PSeq.or (PSeq.id (φ := φ) (by simp) List.mem_cons_self)

/-- **`⋏` is invertible** (right component). -/
theorem PSeq.andInvR {Γ : SecondOrder.Sequent ℒₒᵣ} {φ χ : Proposition ℒₒᵣ}
    (h : PSeq 𝓢 ((φ ⋏ χ) :: Γ)) : PSeq 𝓢 (χ :: Γ) := by
  refine PSeq.cut (φ ⋏ χ) (PSeq.wk ?_ h) ?_
  · intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  · exact PSeq.or (PSeq.id (φ := χ) (by simp)
      (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **Using a provable disjunction.** -/
theorem PSeq.ofProvableOr {φ χ : Proposition ℒₒᵣ} (h : Provable 𝓢 (φ ⋎ χ))
    (Γ : SecondOrder.Sequent ℒₒᵣ) : PSeq 𝓢 (φ :: χ :: Γ) :=
  PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
    (PSeq.orInv (PSeq.ofProvable h (φ :: χ :: Γ)))

/-- **Using a provable implication.**  `φ 🡒 χ` *is* `∼φ ⋎ χ`. -/
theorem PSeq.ofProvableImp {φ χ : Proposition ℒₒᵣ} (h : Provable 𝓢 (φ 🡒 χ))
    (Γ : SecondOrder.Sequent ℒₒᵣ) : PSeq 𝓢 ((∼φ) :: χ :: Γ) :=
  PSeq.ofProvableOr h Γ

/-! ### The propositional combinators -/

/-- `⊢ φ 🡒 φ`. -/
theorem impId (φ : Proposition ℒₒᵣ) : Provable 𝓢 (φ 🡒 φ) :=
  PSeq.to_provable (PSeq.or (PSeq.id (φ := φ) (by simp) List.mem_cons_self))

/-- **Weakening an implication's hypothesis away.** -/
theorem impIntro {φ χ : Proposition ℒₒᵣ} (h : Provable 𝓢 χ) : Provable 𝓢 (φ 🡒 χ) := by
  have h1 : PSeq 𝓢 (χ :: [(∼φ : Proposition ℒₒᵣ)]) := PSeq.ofProvable h _
  exact PSeq.to_provable (PSeq.or
    (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h1))

/-- **Chaining implications.** -/
theorem impTrans {φ χ θ : Proposition ℒₒᵣ} (h₁ : Provable 𝓢 (φ 🡒 χ)) (h₂ : Provable 𝓢 (χ 🡒 θ)) :
    Provable 𝓢 (φ 🡒 θ) := by
  have e₁ : PSeq 𝓢 ((∼φ) :: χ :: [θ]) := PSeq.ofProvableImp h₁ [θ]
  have e₂ : PSeq 𝓢 ((∼χ) :: θ :: [(∼φ : Proposition ℒₒᵣ)]) := PSeq.ofProvableImp h₂ [∼φ]
  refine PSeq.to_provable (PSeq.or (PSeq.cut χ ?_ ?_))
  · exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) e₁
  · exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) e₂

/-- **Conjunction introduction.** -/
theorem andIntro {φ χ : Proposition ℒₒᵣ} (h₁ : Provable 𝓢 φ) (h₂ : Provable 𝓢 χ) :
    Provable 𝓢 (φ ⋏ χ) :=
  PSeq.to_provable (PSeq.and (PSeq.of_provable h₁) (PSeq.of_provable h₂))

/-- **Conjunction elimination** (left). -/
theorem andElimL {φ χ : Proposition ℒₒᵣ} (h : Provable 𝓢 (φ ⋏ χ)) : Provable 𝓢 φ :=
  PSeq.to_provable (PSeq.andInvL (PSeq.of_provable h))

/-- **Conjunction elimination** (right). -/
theorem andElimR {φ χ : Proposition ℒₒᵣ} (h : Provable 𝓢 (φ ⋏ χ)) : Provable 𝓢 χ :=
  PSeq.to_provable (PSeq.andInvR (PSeq.of_provable h))

/-- **Disjunction introduction** (left). -/
theorem orIntroL {φ χ : Proposition ℒₒᵣ} (h : Provable 𝓢 φ) : Provable 𝓢 (φ ⋎ χ) :=
  PSeq.to_provable (PSeq.or (PSeq.ofProvable h [χ]))

/-- **Disjunction introduction** (right). -/
theorem orIntroR {φ χ : Proposition ℒₒᵣ} (h : Provable 𝓢 χ) : Provable 𝓢 (φ ⋎ χ) := by
  have h1 : PSeq 𝓢 (χ :: [φ]) := PSeq.ofProvable h _
  exact PSeq.to_provable (PSeq.or
    (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h1))

/-- **Disjunction elimination.** -/
theorem orElim {φ χ θ : Proposition ℒₒᵣ} (h : Provable 𝓢 (φ ⋎ χ))
    (h₁ : Provable 𝓢 (φ 🡒 θ)) (h₂ : Provable 𝓢 (χ 🡒 θ)) : Provable 𝓢 θ := by
  have e₀ : PSeq 𝓢 (φ :: χ :: [θ]) := PSeq.ofProvableOr h [θ]
  have e₁ : PSeq 𝓢 ((∼φ) :: θ :: [χ, θ]) := PSeq.ofProvableImp h₁ [χ, θ]
  have e₂ : PSeq 𝓢 ((∼χ) :: θ :: [θ]) := PSeq.ofProvableImp h₂ [θ]
  refine PSeq.to_provable (PSeq.cut χ (PSeq.cut φ e₀ ?_) ?_)
  · exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) e₁
  · exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) e₂

/-- **Currying, at the sequent level** — a pure propositional tautology, and the
shape `allNums_curry` feeds to `allNums_mono`. -/
theorem curryTaut (Z S A : Proposition ℒₒᵣ) :
    PSeq 𝓢 [∼((Z ⋏ S) 🡒 A), Z 🡒 (S 🡒 A)] := by
  have hneg : (∼((Z ⋏ S) 🡒 A) : Proposition ℒₒᵣ) = (Z ⋏ S) ⋏ ∼A := by
    show (∼(∼(Z ⋏ S))) ⋏ (∼A) = _
    rw [Semiformula.neg_neg]
  have base : PSeq 𝓢 [(Z ⋏ S) ⋏ ∼A, ∼S, A, ∼Z] :=
    PSeq.and (PSeq.and (PSeq.id (φ := Z) (by simp) (by simp))
      (PSeq.id (φ := S) (by simp) (by simp))) (PSeq.id (φ := A) (by simp) (by simp))
  have h1 : PSeq 𝓢 [∼((Z ⋏ S) 🡒 A), ∼S, A, ∼Z] := by rw [hneg]; exact base
  have h2 : PSeq 𝓢 [S 🡒 A, ∼Z, ∼((Z ⋏ S) 🡒 A)] :=
    PSeq.or (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h1)
  have h3 : PSeq 𝓢 [Z 🡒 (S 🡒 A), ∼((Z ⋏ S) 🡒 A)] :=
    PSeq.or (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h2)
  exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h3

/-- **Uncurrying, at the sequent level.** -/
theorem uncurryTaut (Z S A : Proposition ℒₒᵣ) :
    PSeq 𝓢 [∼(Z 🡒 (S 🡒 A)), (Z ⋏ S) 🡒 A] := by
  have hneg : (∼(Z 🡒 (S 🡒 A)) : Proposition ℒₒᵣ) = Z ⋏ (S ⋏ ∼A) := by
    show (∼(∼Z)) ⋏ ((∼(∼S)) ⋏ (∼A)) = _
    rw [Semiformula.neg_neg, Semiformula.neg_neg]
  have base : PSeq 𝓢 [Z ⋏ (S ⋏ ∼A), ∼Z, ∼S, A] :=
    PSeq.and (PSeq.id (φ := Z) (by simp) (by simp))
      (PSeq.and (PSeq.id (φ := S) (by simp) (by simp))
        (PSeq.id (φ := A) (by simp) (by simp)))
  have h1 : PSeq 𝓢 [∼(Z 🡒 (S 🡒 A)), ∼Z, ∼S, A] := by rw [hneg]; exact base
  have h2 : PSeq 𝓢 [∼(Z ⋏ S), A, ∼(Z 🡒 (S 🡒 A))] :=
    PSeq.or (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h1)
  have h3 : PSeq 𝓢 [(Z ⋏ S) 🡒 A, ∼(Z 🡒 (S 🡒 A))] :=
    PSeq.or (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h2)
  exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h3

/-- **Currying**: `(φ ⋏ χ) 🡒 θ` gives `φ 🡒 (χ 🡒 θ)`.  The shape mismatch
between `LK.lean`'s `indBody` (a conjunctive hypothesis) and Foundation's
`succInd` (two nested implications) is exactly this. -/
theorem andImpCurry {φ χ θ : Proposition ℒₒᵣ} (h : Provable 𝓢 ((φ ⋏ χ) 🡒 θ)) :
    Provable 𝓢 (φ 🡒 (χ 🡒 θ)) :=
  PSeq.to_provable
    (PSeq.cut ((φ ⋏ χ) 🡒 θ) (PSeq.ofProvable h [φ 🡒 (χ 🡒 θ)]) (curryTaut φ χ θ))

/-- **Uncurrying**: the converse of `andImpCurry`. -/
theorem andImpUncurry {φ χ θ : Proposition ℒₒᵣ} (h : Provable 𝓢 (φ 🡒 (χ 🡒 θ))) :
    Provable 𝓢 ((φ ⋏ χ) 🡒 θ) :=
  PSeq.to_provable
    (PSeq.cut (φ 🡒 (χ 🡒 θ)) (PSeq.ofProvable h [(φ ⋏ χ) 🡒 θ]) (uncurryTaut φ χ θ))

/-! ### The quantifier combinators -/

/-- Substituting `&0` after a `shift₀` is `free₀`. -/
theorem subst_bar_shift₀ {N : ℕ} (φ : Semiproposition ℒₒᵣ N 1) :
    (Semiproposition.shift₀ φ)/[(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)] =
      FirstOrder.Rewriting.free φ := by
  show FirstOrder.Rew.subst ![&0] ▹ (FirstOrder.Rew.shift ▹ φ) = _
  rw [← FirstOrder.TransitiveRewriting.comp_app,
    FirstOrder.Rew.subst_mbar_zero_comp_shift_eq_free]

/-- Substituting the canonical arithmetical witness `#0 ∈& 0` after a `shift₁`
is `free₁`. -/
theorem subst₂_shift₁ (φ : Semiproposition ℒₒᵣ 1 0) :
    (Semiproposition.shift₁ φ)/⟦freeWitness⟧ = Semiproposition.free₁ φ := by
  have he : (SecondOrder.Rew.subst ![freeWitness]).comp
      (SecondOrder.Rew.shift : SecondOrder.Rew ℒₒᵣ ℕ 1 ℕ 1 ℕ) = SecondOrder.Rew.free := by
    ext X
    · cases X using Fin.cases with
      | zero =>
          show (SecondOrder.Rew.subst ![freeWitness]).app
            ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)) = _
          simp only [SecondOrder.Rew.app_bvar, SecondOrder.Rew.subst_bv,
            Matrix.cons_val_fin_one]
          rw [FirstOrder.Rewriting.subst1_bvar0_eq]
          simp [freeWitness, SecondOrder.Rew.free]
      | succ Y => exact Y.elim0
    · show (SecondOrder.Rew.subst ![freeWitness]).app
        ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& (X + 1)) = _
      simp only [SecondOrder.Rew.app_fvar, SecondOrder.Rew.subst_fv]
      rw [FirstOrder.Rewriting.subst1_bvar0_eq]
      simp [SecondOrder.Rew.free]
  show (SecondOrder.Rew.subst ![freeWitness]).app (SecondOrder.Rew.shift.app φ) = _
  rw [← SecondOrder.Rew.app_comp, he]

/-- **`∀¹` is monotone.**  From the eigenvariable form of an implication, the
implication between the two `∀¹`s. -/
theorem all₁_mono (h𝓢 : ∀ χ ∈ 𝓢, Semiproposition.shift₀ χ = χ)
    {φ χ : Semiproposition ℒₒᵣ 0 1}
    (h : Provable 𝓢 (φ.free₀ 🡒 χ.free₀)) : Provable 𝓢 ((∀¹ φ) 🡒 (∀¹ χ)) := by
  have hsh : Semiproposition.shift₀ (∃¹ (∼φ)) = ∃¹ (Semiproposition.shift₀ (∼φ)) := by
    show FirstOrder.Rew.shift ▹ (∃¹ (∼φ)) = _
    rw [Semiformula.rew_exs₀, FirstOrder.Rew.q_shift]
  have hfn : FirstOrder.Rewriting.free (∼φ) = ∼(φ.free₀) :=
    LogicalConnective.HomClass.map_neg _ _
  have h1 : PSeq 𝓢 [(Semiproposition.shift₀ (∼φ))/[(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)],
      χ.free₀] := by
    rw [subst_bar_shift₀, hfn]
    exact PSeq.ofProvableImp h []
  have h2 : PSeq 𝓢 [∃¹ (Semiproposition.shift₀ (∼φ)), χ.free₀] := PSeq.exs₁ (&0) h1
  have h3 : PSeq 𝓢 (χ.free₀ :: SecondOrder.Sequent.shift₀ [∃¹ (∼φ)]) := by
    show PSeq 𝓢 (χ.free₀ :: [Semiproposition.shift₀ (∃¹ (∼φ))])
    rw [hsh]
    exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h2
  have h4 : PSeq 𝓢 [∀¹ χ, ∃¹ (∼φ)] := PSeq.all₁ h𝓢 h3
  exact PSeq.to_provable (PSeq.or
    (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h4))

/-- **`∀²` is monotone.**  The set-variable analogue, instantiating the
existential half at the canonical arithmetical witness `#0 ∈& 0`. -/
theorem all₂_mono (h𝓢 : ∀ χ ∈ 𝓢, Semiproposition.shift₁ χ = χ)
    {φ χ : Semiproposition ℒₒᵣ 1 0}
    (h : Provable 𝓢 (φ.free₁ 🡒 χ.free₁)) : Provable 𝓢 ((∀² φ) 🡒 (∀² χ)) := by
  have hsh : Semiproposition.shift₁ (∃² (∼φ)) = ∃² (Semiproposition.shift₁ (∼φ)) := by
    show SecondOrder.Rew.shift.app (∃² (∼φ)) = _
    rw [SecondOrder.Rew.app_exs₁, SecondOrder.Rew.q_shift]
  have hfn : Semiproposition.free₁ (∼φ) = ∼(φ.free₁) :=
    LogicalConnective.HomClass.map_neg _ _
  have h1 : PSeq 𝓢 [(Semiproposition.shift₁ (∼φ))/⟦freeWitness⟧, χ.free₁] := by
    rw [subst₂_shift₁, hfn]
    exact PSeq.ofProvableImp h []
  have h2 : PSeq 𝓢 [∃² (Semiproposition.shift₁ (∼φ)), χ.free₁] :=
    PSeq.exs₂ arith_freeWitness h1
  have h3 : PSeq 𝓢 (χ.free₁ :: SecondOrder.Sequent.shift₁ [∃² (∼φ)]) := by
    show PSeq 𝓢 (χ.free₁ :: [Semiproposition.shift₁ (∃² (∼φ))])
    rw [hsh]
    exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h2
  have h4 : PSeq 𝓢 [∀² χ, ∃² (∼φ)] := PSeq.all₂ h𝓢 h3
  exact PSeq.to_provable (PSeq.or
    (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h4))

/-! ### Working under a `∀¹`-closure

`ACA`'s schemes are universally closed over their number parameters
(`allNums`), so every propositional manipulation of a scheme instance has to
happen *under* the closure.  `allNums_mono` does that once: the hypothesis is
the sequent form of the implication under an **arbitrary** substitution of the
`n` parameters, which is exactly what survives the eigenvariable step. -/

/-- **Transporting a provable `∀¹`-closure along a uniformly derivable
implication.**  The hypothesis must hold for every rewriting `ω` of the `n`
parameters — that is what makes the induction go through, and it is free in
practice, since the implications that arise are homomorphic images. -/
theorem allNums_mono (h𝓢 : ∀ χ ∈ 𝓢, Semiproposition.shift₀ χ = χ) :
    ∀ {n : ℕ} {P Q : Semiproposition ℒₒᵣ 0 n},
      (∀ ω : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0, PSeq 𝓢 [∼(ω ▹ P), ω ▹ Q]) →
        Provable 𝓢 (allNums P) → Provable 𝓢 (allNums Q)
  | 0, P, Q, himp, h => by
      have h0 := himp FirstOrder.Rew.id
      rw [show (FirstOrder.Rew.id ▹ P : Proposition ℒₒᵣ) = P from by simp,
        show (FirstOrder.Rew.id ▹ Q : Proposition ℒₒᵣ) = Q from by simp] at h0
      exact PSeq.to_provable (PSeq.cut P (PSeq.ofProvable h [Q])
        (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h0))
  | (n + 1), P, Q, himp, h => by
      refine allNums_mono h𝓢 (P := ∀¹ P) (Q := ∀¹ Q) (fun ω => ?_) h
      have hnP : ∼(ω ▹ (∀¹ P)) = ∃¹ (∼(ω.q ▹ P)) := by rw [Semiformula.rew_all₀]; rfl
      have hQ : ω ▹ (∀¹ Q) = ∀¹ (ω.q ▹ Q) := Semiformula.rew_all₀ _ _
      rw [hnP, hQ]
      have hsh : Semiproposition.shift₀ (∃¹ (∼(ω.q ▹ P))) =
          ∃¹ (Semiproposition.shift₀ (∼(ω.q ▹ P))) := by
        show FirstOrder.Rew.shift ▹ (∃¹ (∼(ω.q ▹ P))) = _
        rw [Semiformula.rew_exs₀, FirstOrder.Rew.q_shift]
      have hfn : FirstOrder.Rewriting.free (∼(ω.q ▹ P)) =
          ∼(FirstOrder.Rewriting.free (ω.q ▹ P)) := LogicalConnective.HomClass.map_neg _ _
      have hcP : FirstOrder.Rewriting.free (ω.q ▹ P) = (FirstOrder.Rew.free.comp ω.q) ▹ P := by
        show FirstOrder.Rew.free ▹ (ω.q ▹ P) = _
        rw [← FirstOrder.TransitiveRewriting.comp_app]
      have hcQ : FirstOrder.Rewriting.free (ω.q ▹ Q) = (FirstOrder.Rew.free.comp ω.q) ▹ Q := by
        show FirstOrder.Rew.free ▹ (ω.q ▹ Q) = _
        rw [← FirstOrder.TransitiveRewriting.comp_app]
      have h1 : PSeq 𝓢 [(Semiproposition.shift₀ (∼(ω.q ▹ P)))/[(&0 :
          FirstOrder.Semiterm ℒₒᵣ ℕ 0)], FirstOrder.Rewriting.free (ω.q ▹ Q)] := by
        rw [subst_bar_shift₀, hfn, hcP, hcQ]
        exact himp (FirstOrder.Rew.free.comp ω.q)
      have h2 : PSeq 𝓢 [∃¹ (Semiproposition.shift₀ (∼(ω.q ▹ P))),
          FirstOrder.Rewriting.free (ω.q ▹ Q)] := PSeq.exs₁ (&0) h1
      have h3 : PSeq 𝓢 (FirstOrder.Rewriting.free (ω.q ▹ Q) ::
          SecondOrder.Sequent.shift₀ [∃¹ (∼(ω.q ▹ P))]) := by
        show PSeq 𝓢 (FirstOrder.Rewriting.free (ω.q ▹ Q) ::
          [Semiproposition.shift₀ (∃¹ (∼(ω.q ▹ P)))])
        rw [hsh]
        exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h2
      have h4 : PSeq 𝓢 [∀¹ (ω.q ▹ Q), ∃¹ (∼(ω.q ▹ P))] := PSeq.all₁ h𝓢 h3
      exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h4

/-- **Currying under a `∀¹`-closure** — the form `Lift.lean` needs to turn
`LK.lean`'s `indBody` (conjunctive hypothesis, closed over the parameters) into
Foundation's `succInd` shape (two nested implications). -/
theorem allNums_curry (h𝓢 : ∀ χ ∈ 𝓢, Semiproposition.shift₀ χ = χ) {n : ℕ}
    {Z S A : Semiproposition ℒₒᵣ 0 n} (h : Provable 𝓢 (allNums ((Z ⋏ S) 🡒 A))) :
    Provable 𝓢 (allNums (Z 🡒 (S 🡒 A))) := by
  refine allNums_mono h𝓢 (fun ω => ?_) h
  have e1 : ω ▹ ((Z ⋏ S) 🡒 A) = ((ω ▹ Z) ⋏ (ω ▹ S)) 🡒 (ω ▹ A) := by
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and]
  have e2 : ω ▹ (Z 🡒 (S 🡒 A)) = (ω ▹ Z) 🡒 ((ω ▹ S) 🡒 (ω ▹ A)) := by
    simp only [LogicalConnective.HomClass.map_imply]
  rw [e1, e2]
  exact curryTaut _ _ _

end OrdinalAnalysis.ACA
