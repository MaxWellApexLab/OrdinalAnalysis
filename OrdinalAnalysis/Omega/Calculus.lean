/-
  The infinitary calculus.

  Cut elimination for first-order logic does not give consistency of arithmetic,
  because the induction axioms are not logical validities: they enter a
  derivation as extra hypotheses, and cut elimination does not remove them.
  Gentzen's answer is to replace the induction schema by a rule with infinitely
  many premises, so that arithmetic becomes *logic* over the standard model and
  the only remaining axioms are true atomic sentences.

  That rule is the ω-rule: to conclude `∀x φ(x)` it is enough to have derived
  `φ(n̄)` for every numeral `n̄`.  Its dual is that `∃x φ(x)` may only be
  concluded from a numeral instance, not from an arbitrary term.  The two
  together make the quantifier cases of the reduction lemma trivial — the
  existential side hands over a numeral, and the universal side already has that
  very premise — which is why this file does not need, and does not have, a
  substitution lemma, a context shift, or an inversion lemma.  Those were the
  three most painful parts of the finitary development.

  Three things about the shape.

  * How a quantifier is instantiated is a parameter `I : Instantiation L` — a
    family of numerals together with a normaliser that is applied after
    substitution — not something the rule picks.  If each application could
    choose its own family the rule would be unsound outright: take the constant
    family and every `∀x φ(x)` follows from `φ(0)`.

    The normaliser is Buchholz's convention that closed terms are identified
    with their values, made explicit.  It is not decoration.  With plain
    substitution the ω-rule's premises for `∀x X(x + 1)` are the formulas
    `X(n̄ + 1)`, which are unrelated atoms to `X(n+1‾)`; an embedding of PA[X]
    that evaluates closed terms then has nothing to feed the rule, and one that
    does not evaluate them cannot replay an existential inference whose witness
    is a compound term, because the calculus has no equality reasoning about
    `X`.  Requiring only two laws of the normaliser — it commutes with negation
    and preserves complexity — keeps every proof in this directory unchanged,
    and plain substitution is the instance `Instantiation.raw`.

  * The ω-rule's premises get *individual* ordinals `β n`, not one shared bound.
    This is not fussiness.  The whole point of the rule is to derive the
    induction axiom, and the derivation of `φ(n̄)` from the induction step is `n`
    inferences long, so its height grows with `n`.  A shared bound would make
    the induction axiom underivable and the entire construction pointless.

  * The finitary calculus is not superseded.  It carries cut elimination with an
    explicit ordinal bound for pure first-order logic, which is a separate
    result, and `Bridge.lean` connects it to Foundation's semantics.

  * The heights are an arbitrary `[OrdinalNotation O]` (`Ordinal/Notation.lean`),
    not `NONote`.  Nothing in this directory uses anything about `NONote` beyond
    the order arithmetic that class collects, and the results above `ε₀` need
    larger notation systems; taking `O := NONote` gives back exactly what was
    here before, which is what the `Gentzen/` files still do.
-/
import Foundation.FirstOrder.Basic.CutFree
import OrdinalAnalysis.Ordinal.Notation

namespace OrdinalAnalysis

open LO LO.FirstOrder LO.FirstOrder.Derivation
open ONote

variable {L : Language}

/-- The atomic axioms of the infinitary calculus: a set of closed literals,
consistent, and containing nothing but literals.

This is the third thing the ω-calculus needs beyond logic, and the one the
first version omitted.  The identity rule derives `φ, ∼φ` for any atom, but
nothing derives a *true* closed atom such as `0 + 0 = 0` on its own — and the
axioms of `PA⁻`, once the universal quantifiers have been discharged by the
ω-rule, are exactly such atoms.  Without them arithmetic cannot be embedded.

Consistency is what the reduction lemma consumes: a cut on an atomic formula
whose two premises are both axioms is the one case that cannot be reduced, and
consistency says it does not arise.  Literal-only is what keeps every other case
of the reduction lemma unchanged: an axiom is never the principal formula of a
propositional or quantifier rule. -/
structure Literals (L : Language) where
  /-- The axioms. -/
  T : Proposition L → Prop
  /-- Every axiom is an atom or a negated atom. -/
  literal : ∀ φ, T φ →
    ∃ (k : ℕ) (rl : L.Rel k) (v : Fin k → SyntacticTerm L),
      φ = Semiformula.rel rl v ∨ φ = Semiformula.nrel rl v
  /-- No axiom is asserted together with its negation. -/
  consistent : ∀ φ, T φ → T (∼φ) → False

namespace Literals

variable {A : Literals L}

theorem ne_verum {φ : Proposition L} (h : A.T φ) : φ ≠ ⊤ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem ne_falsum {φ : Proposition L} (h : A.T φ) : φ ≠ ⊥ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem ne_or {φ ψ₁ ψ₂ : Proposition L} (h : A.T φ) : φ ≠ ψ₁ ⋎ ψ₂ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem ne_and {φ ψ₁ ψ₂ : Proposition L} (h : A.T φ) : φ ≠ ψ₁ ⋏ ψ₂ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem ne_all {φ : Proposition L} {ψ : Semiproposition L 1} (h : A.T φ) : φ ≠ ∀¹ ψ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem ne_exs {φ : Proposition L} {ψ : Semiproposition L 1} (h : A.T φ) : φ ≠ ∃¹ ψ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

/-- The negation of an axiom is a literal too, so it is never `⊤`. -/
theorem neg_ne_verum {φ : Proposition L} (h : A.T φ) : ∼φ ≠ ⊤ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem neg_ne_or {φ ψ₁ ψ₂ : Proposition L} (h : A.T φ) : ∼φ ≠ ψ₁ ⋎ ψ₂ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem neg_ne_and {φ ψ₁ ψ₂ : Proposition L} (h : A.T φ) : ∼φ ≠ ψ₁ ⋏ ψ₂ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem neg_ne_all {φ : Proposition L} {ψ : Semiproposition L 1} (h : A.T φ) :
    ∼φ ≠ ∀¹ ψ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

theorem neg_ne_exs {φ : Proposition L} {ψ : Semiproposition L 1} (h : A.T φ) :
    ∼φ ≠ ∃¹ ψ := by
  obtain ⟨k, rl, v, rfl | rfl⟩ := A.literal φ h <;> simp

end Literals

/-- How the quantifier rules instantiate: a family of numerals, and a
normaliser applied to the result of substituting one.  The two laws are exactly
what the reduction lemma consumes in its quantifier cases: the cut formula
produced there is an instance, so its complexity must be that of the body, and
the instance of a negated body must be the negated instance. -/
structure Instantiation (L : Language) where
  /-- The numerals. -/
  num : ℕ → SyntacticTerm L
  /-- The normaliser. -/
  nf : Proposition L → Proposition L
  /-- The normaliser commutes with negation. -/
  nf_neg : ∀ φ : Proposition L, nf (∼φ) = ∼nf φ
  /-- The normaliser preserves complexity. -/
  complexity_nf : ∀ φ : Proposition L, (nf φ).complexity = φ.complexity

namespace Instantiation

variable (I : Instantiation L)

/-- The `n`-th instance of a body: substitute the numeral, then normalise. -/
def inst (φ : Semiproposition L 1) (n : ℕ) : Proposition L := I.nf (φ/[I.num n])

@[simp] theorem inst_neg (φ : Semiproposition L 1) (n : ℕ) : I.inst (∼φ) n = ∼I.inst φ n := by
  simp only [inst]
  rw [← I.nf_neg]
  congr 1
  simp

@[simp] theorem complexity_inst (φ : Semiproposition L 1) (n : ℕ) :
    (I.inst φ n).complexity = φ.complexity := by
  simp only [inst, I.complexity_nf, Semiformula.complexity_rew]

/-- Plain substitution, with no normalisation. -/
def raw (num : ℕ → SyntacticTerm L) : Instantiation L :=
  ⟨num, id, fun _ => rfl, fun _ => rfl⟩

@[simp] theorem raw_num (num : ℕ → SyntacticTerm L) : (raw num).num = num := by
  simp [raw]

@[simp] theorem raw_inst (num : ℕ → SyntacticTerm L) (φ : Semiproposition L 1) (n : ℕ) :
    (raw num).inst φ n = φ/[num n] := by
  simp [inst, raw]

end Instantiation

/-- Derivability in the infinitary calculus, at cut rank `r`, of height below
`α`, with quantifier instances supplied by `I` and atomic axioms by `A`. -/
inductive OmegaDerivable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
    (A : Literals L) (I : Instantiation L) (r : ℕ) : O → Sequent L → Prop
  | atom {α : O} {φ : Proposition L} :
      A.T φ → OmegaDerivable A I r α [φ]
  | identity {α : O} {k : ℕ} (rl : L.Rel k) (v) :
      OmegaDerivable A I r α [.rel rl v, .nrel rl v]
  | verum {α : O} :
      OmegaDerivable A I r α [⊤]
  | or {α β : O} {φ ψ : Proposition L} {Γ : Sequent L} :
      β < α → OmegaDerivable A I r β (φ :: ψ :: Γ) →
      OmegaDerivable A I r α (φ ⋎ ψ :: Γ)
  | and {α β γ : O} {φ ψ : Proposition L} {Γ : Sequent L} :
      β < α → γ < α →
      OmegaDerivable A I r β (φ :: Γ) → OmegaDerivable A I r γ (ψ :: Γ) →
      OmegaDerivable A I r α (φ ⋏ ψ :: Γ)
  | omegaRule {α : O} {φ : Semiproposition L 1} {Γ : Sequent L}
      (β : ℕ → O) :
      (∀ n, β n < α) →
      (∀ n : ℕ, OmegaDerivable A I r (β n) (I.inst φ n :: Γ)) →
      OmegaDerivable A I r α ((∀¹ φ) :: Γ)
  | exs {α β : O} {φ : Semiproposition L 1} {Γ : Sequent L} (n : ℕ) :
      β < α → OmegaDerivable A I r β (I.inst φ n :: Γ) →
      OmegaDerivable A I r α ((∃¹ φ) :: Γ)
  | contraction {α : O} {Δ Γ : Sequent L} :
      Δ ⊆ Γ → OmegaDerivable A I r α Δ →
      OmegaDerivable A I r α Γ
  | cut {α β γ : O} {φ : Proposition L} {Γ Δ : Sequent L} :
      φ.complexity < r → β < α → γ < α →
      OmegaDerivable A I r β (φ :: Γ) → OmegaDerivable A I r γ (∼φ :: Δ) →
      OmegaDerivable A I r α (Γ ++ Δ)

namespace OmegaDerivable

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals L} {I : Instantiation L}

/-- Weakening in the ordinal index. -/
theorem mono_ord {r : ℕ} {α β : O} {Γ : Sequent L}
    (h : OmegaDerivable A I r α Γ) (hab : α ≤ β) : OmegaDerivable A I r β Γ := by
  induction h generalizing β with
  | identity rl v => exact .identity rl v
  | verum => exact .verum
  | or hlt _ ih => exact .or (lt_of_lt_of_le hlt hab) (ih le_rfl)
  | and h₁ h₂ _ _ ih₁ ih₂ =>
      exact .and (lt_of_lt_of_le h₁ hab) (lt_of_lt_of_le h₂ hab) (ih₁ le_rfl) (ih₂ le_rfl)
  | omegaRule f hf _ ih =>
      exact .omegaRule f (fun n => lt_of_lt_of_le (hf n) hab) (fun n => ih n le_rfl)
  | exs n hlt _ ih => exact .exs n (lt_of_lt_of_le hlt hab) (ih le_rfl)
  | atom h => exact .atom h
  | contraction ss _ ih => exact .contraction ss (ih hab)
  | cut hc h₁ h₂ _ _ ih₁ ih₂ =>
      exact .cut hc (lt_of_lt_of_le h₁ hab) (lt_of_lt_of_le h₂ hab) (ih₁ le_rfl) (ih₂ le_rfl)

/-- Weakening in the cut rank. -/
theorem mono_rank {r s : ℕ} {α : O} {Γ : Sequent L}
    (h : OmegaDerivable A I r α Γ) (hrs : r ≤ s) : OmegaDerivable A I s α Γ := by
  induction h with
  | identity rl v => exact .identity rl v
  | verum => exact .verum
  | or hlt _ ih => exact .or hlt ih
  | and h₁ h₂ _ _ ih₁ ih₂ => exact .and h₁ h₂ ih₁ ih₂
  | omegaRule f hf _ ih => exact .omegaRule f hf ih
  | exs n hlt _ ih => exact .exs n hlt ih
  | atom h => exact .atom h
  | contraction ss _ ih => exact .contraction ss ih
  | cut hc h₁ h₂ _ _ ih₁ ih₂ => exact .cut (lt_of_lt_of_le hc hrs) h₁ h₂ ih₁ ih₂

/-- A sequent carrying an atom together with its negation is derivable outright. -/
theorem of_mem_identity {r : ℕ} {α : O} {Θ : Sequent L} {k : ℕ}
    (rl : L.Rel k) (v) (hp : Semiformula.rel rl v ∈ Θ)
    (hn : Semiformula.nrel rl v ∈ Θ) : OmegaDerivable A I r α Θ := by
  refine .contraction ?_ (.identity rl v)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hp
  · exact hn

/-- `⊤` in a sequent makes it derivable outright. -/
theorem of_mem_verum {r : ℕ} {α : O} {Θ : Sequent L}
    (h : (⊤ : Proposition L) ∈ Θ) : OmegaDerivable A I r α Θ := by
  refine .contraction ?_ .verum
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl
  exact h

/-- If the head of a derivable sequent already occurs in its tail, drop it. -/
theorem drop_head {r : ℕ} {α : O} {ψ : Proposition L} {Θ : Sequent L}
    (h : OmegaDerivable A I r α (ψ :: Θ)) (hmem : ψ ∈ Θ) : OmegaDerivable A I r α Θ := by
  refine .contraction ?_ h
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hmem
  · exact hx

/-- `⊥` is a passenger: no rule introduces it, so it can only have entered by
weakening and can be dropped again.

Needed because the cut formula `⊤` has `∼⊤ = ⊥`, and the reduction lemma then
has to discharge a sequent carrying one. -/
theorem drop_falsum {r : ℕ} :
    ∀ {α : O} {Γ : Sequent L}, OmegaDerivable A I r α Γ →
      ∀ {Θ : Sequent L}, Γ ⊆ (⊥ : Proposition L) :: Θ →
        OmegaDerivable A I r α Θ := by
  intro α Γ h
  induction h with
  | identity rl v =>
      intro Θ hss
      refine of_mem_identity rl v ?_ ?_
      · have := hss (by simp : Semiformula.rel rl v ∈ [_, _])
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      · have := hss (by simp : Semiformula.nrel rl v ∈ [_, _])
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
  | verum =>
      intro Θ hss
      refine of_mem_verum ?_
      have := hss (by simp : (⊤ : Proposition L) ∈ [(⊤ : Proposition L)])
      simp only [List.mem_cons] at this
      rcases this with hbot | hm
      · exact absurd hbot (by simp)
      · exact hm
  | @or α' β' χ ρ Γ' hlt _ ih =>
      intro Θ hss
      have hmem : (χ ⋎ ρ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have key := ih (Θ := χ :: ρ :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · rcases hx with rfl | hx
          · tauto
          · have := hss (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto)
      exact drop_head (OmegaDerivable.or hlt key) hmem
  | @and α' β' γ' χ ρ Γ' hb hc _ _ ihp ihq =>
      intro Θ hss
      have hmem : (χ ⋏ ρ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have hsub : ∀ ζ : Proposition L, (ζ :: Γ') ⊆ (⊥ : Proposition L) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto
      exact drop_head
        (OmegaDerivable.and hb hc (ihp (hsub χ)) (ihq (hsub ρ))) hmem
  | @omegaRule α' χ Γ' f hf _ ih =>
      intro Θ hss
      have hmem : (∀¹ χ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      refine drop_head (OmegaDerivable.omegaRule f hf (fun n => ih n ?_)) hmem
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · tauto
      · have := hss (List.mem_cons_of_mem _ hx)
        simp only [List.mem_cons] at this
        tauto
  | @exs α' β' χ Γ' n hlt _ ih =>
      intro Θ hss
      have hmem : (∃¹ χ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have key := ih (Θ := I.inst χ n :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto)
      exact drop_head (OmegaDerivable.exs n hlt key) hmem
  | @atom α' φ hφ =>
      intro Θ hss
      have hm := hss List.mem_cons_self
      simp only [List.mem_cons] at hm
      rcases hm with hbot | hm
      · exact absurd hbot (Literals.ne_falsum hφ)
      · refine .contraction ?_ (.atom hφ)
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rw [hx]; exact hm
  | contraction ss _ ih =>
      intro Θ hss
      exact ih (fun x hx => hss (ss hx))
  | @cut α' β' γ' χ Γ₁ Γ₂ hc hb1 hb2 _ _ ihp ihn =>
      intro Θ hss
      have kp := ihp (Θ := χ :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_append_left _ hx)
          simp only [List.mem_cons] at this
          tauto)
      have kn := ihn (Θ := ∼χ :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_append_right _ hx)
          simp only [List.mem_cons] at this
          tauto)
      refine OmegaDerivable.contraction ?_ (OmegaDerivable.cut hc hb1 hb2 kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto

end OmegaDerivable

end OrdinalAnalysis
