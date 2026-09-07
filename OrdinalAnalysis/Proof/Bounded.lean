/-
  Bounded derivability:  `⊢^α_r Γ`  — "Γ has a derivation of ordinal height at
  most α using no cut on a formula of complexity ≥ r".

  Assigning an ordinal to a *concrete* derivation (`OrdinalAnalysis.ord`) is
  enough to state things but awkward to work with, because every lemma then has
  to produce a specific derivation term.  The standard vehicle is instead this
  Prop-valued judgement, which builds weakening into the index: if `⊢^α_r Γ`
  and `α ≤ β` then `⊢^β_r Γ`.

  `contraction` — which is subset-based, and so does weakening, contraction and
  exchange at once — does **not** raise the ordinal.  Structural rules add no
  logical content, and if they cost an ordinal step then the inversion lemmas
  cannot preserve their index: their induction permutes the context several
  times per logical rule.

  Indexed by `NONote` — Cantor normal forms that are actually in normal form.
  Two reasons.  The natural sum the reduction lemma needs exists on normal forms
  and not on abstract ordinals, so `Ordinal` is out; and the order on raw `ONote`
  goes through `repr`, which is meaningless for a term whose exponents are out of
  order, so every ordinal fact used downstream — monotonicity above all — would
  otherwise carry a normal-form hypothesis.  `NONote` also supplies `LinearOrder`
  and `WellFoundedLT`, both of which the elimination lemma will want.
-/
import OrdinalAnalysis.Ordinal.NONatSum
import OrdinalAnalysis.Proof.CutRank

namespace OrdinalAnalysis

open LO LO.FirstOrder LO.FirstOrder.Derivation
open ONote

variable {L : Language}

/-- `BoundedDerivable r α Γ` is Gentzen's `⊢^α_r Γ`: the sequent `Γ` is
derivable with ordinal height at most `α`, using only cuts on formulas of
complexity strictly below `r`. -/
inductive BoundedDerivable (r : ℕ) : NONote → Sequent L → Prop
  | identity {α : NONote} {k : ℕ} (rl : L.Rel k) (v) :
      BoundedDerivable r α [.rel rl v, .nrel rl v]
  | verum {α : NONote} :
      BoundedDerivable r α [⊤]
  | or {α β : NONote} {φ ψ : Proposition L} {Γ : Sequent L} :
      β < α → BoundedDerivable r β (φ :: ψ :: Γ) →
      BoundedDerivable r α (φ ⋎ ψ :: Γ)
  | and {α β γ : NONote} {φ ψ : Proposition L} {Γ : Sequent L} :
      β < α → γ < α →
      BoundedDerivable r β (φ :: Γ) → BoundedDerivable r γ (ψ :: Γ) →
      BoundedDerivable r α (φ ⋏ ψ :: Γ)
  | all {α β : NONote} {φ : Semiproposition L 1} {Γ : Sequent L} :
      β < α → BoundedDerivable r β (φ.free :: Γ⁺) →
      BoundedDerivable r α ((∀¹ φ) :: Γ)
  | exs {α β : NONote} {φ : Semiproposition L 1} {Γ : Sequent L} (t) :
      β < α → BoundedDerivable r β (φ/[t] :: Γ) →
      BoundedDerivable r α ((∃¹ φ) :: Γ)
  | contraction {α : NONote} {Δ Γ : Sequent L} :
      Δ ⊆ Γ → BoundedDerivable r α Δ →
      BoundedDerivable r α Γ
  | cut {α β γ : NONote} {φ : Proposition L} {Γ Δ : Sequent L} :
      φ.complexity < r → β < α → γ < α →
      BoundedDerivable r β (φ :: Γ) → BoundedDerivable r γ (∼φ :: Δ) →
      BoundedDerivable r α (Γ ++ Δ)

@[inherit_doc] notation:45 "⊢^[" α "]_[" r "] " Γ => BoundedDerivable r α Γ

namespace BoundedDerivable

/-- Weakening in the ordinal index: the whole point of indexing by an ordinal
bound rather than assigning an exact height. -/
theorem mono_ord {r : ℕ} {α β : NONote} {Γ : Sequent L}
    (h : BoundedDerivable r α Γ) (hab : α ≤ β) : BoundedDerivable r β Γ := by
  induction h generalizing β with
  | identity rl v => exact .identity rl v
  | verum => exact .verum
  | or hlt _ ih => exact .or (lt_of_lt_of_le hlt hab) (ih le_rfl)
  | and h₁ h₂ _ _ ih₁ ih₂ =>
      exact .and (lt_of_lt_of_le h₁ hab) (lt_of_lt_of_le h₂ hab) (ih₁ le_rfl) (ih₂ le_rfl)
  | all hlt _ ih => exact .all (lt_of_lt_of_le hlt hab) (ih le_rfl)
  | exs t hlt _ ih => exact .exs t (lt_of_lt_of_le hlt hab) (ih le_rfl)
  | contraction ss _ ih => exact .contraction ss (ih hab)
  | cut hc h₁ h₂ _ _ ih₁ ih₂ =>
      exact .cut hc (lt_of_lt_of_le h₁ hab) (lt_of_lt_of_le h₂ hab) (ih₁ le_rfl) (ih₂ le_rfl)

/-- Weakening in the cut rank. -/
theorem mono_rank {r s : ℕ} {α : NONote} {Γ : Sequent L}
    (h : BoundedDerivable r α Γ) (hrs : r ≤ s) : BoundedDerivable s α Γ := by
  induction h with
  | identity rl v => exact .identity rl v
  | verum => exact .verum
  | or hlt _ ih => exact .or hlt ih
  | and h₁ h₂ _ _ ih₁ ih₂ => exact .and h₁ h₂ ih₁ ih₂
  | all hlt _ ih => exact .all hlt ih
  | exs t hlt _ ih => exact .exs t hlt ih
  | contraction ss _ ih => exact .contraction ss ih
  | cut hc h₁ h₂ _ _ ih₁ ih₂ => exact .cut (lt_of_lt_of_le hc hrs) h₁ h₂ ih₁ ih₂

end BoundedDerivable

end OrdinalAnalysis
