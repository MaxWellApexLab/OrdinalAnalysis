/-
  Cut elimination with an explicit ordinal bound.

  Iterating the elimination lemma `r` times drives the cut rank to zero, at the
  cost of an `r`-fold tower of `ω`-powers over the original height.  At rank
  zero the cut rule is unavailable — it would need a formula of complexity
  strictly below `0` — so a rank-zero derivation is cut free by construction,
  and any induction over one discharges the cut case with `Nat.not_lt_zero`.

  Two things are worth saying about the bound.

  It stays below `ε₀`, and that is free rather than proved.  `NONote` is the
  type of ordinal notations in Cantor normal form, which is to say exactly the
  ordinals below `ε₀`; the tower is built inside that type, so the statement
  "the bound is below `ε₀`" is discharged by the type of the bound.  This is the
  payoff for indexing the calculus by notations rather than by `Ordinal`.

  And it is a genuine bound, not merely an existence claim.  Foundation proves a
  Hauptsatz for the same calculus by the algebraic route — a negative
  translation into minimal logic and a Kripke-style forcing argument — which
  establishes that a cut-free derivation exists but tracks no height at all.
  The bound is the whole content of the ordinal analysis, so the two results are
  not interchangeable.
-/
import OrdinalAnalysis.Proof.Elimination

namespace OrdinalAnalysis

open LO LO.FirstOrder LO.FirstOrder.Derivation

variable {L : Language}


namespace BoundedDerivable

/-- **Cut elimination.**  Every derivation of cut rank `r` and height below `α`
becomes a cut-free one of height below the `r`-fold `ω`-tower over `α`. -/
theorem cutElimination :
    ∀ (r : ℕ) {α : NONote} {Γ : Sequent L}, BoundedDerivable r α Γ →
      BoundedDerivable 0 (NONote.omegaTower r α) Γ := by
  intro r
  induction r with
  | zero => intro α Γ h; exact h
  | succ r ih => intro α Γ h; exact ih (elimination h)

/-- At rank `0` the cut rule cannot fire, because its side condition asks for a
formula of complexity strictly below `0`.

Every induction over a rank-zero derivation therefore has a vacuous cut case,
and this is the lemma that closes it. -/
theorem no_cut_at_rank_zero {φ : Proposition L} (h : φ.complexity < 0) : False :=
  Nat.not_lt_zero _ h

/-- A rank-zero derivation really is cut free: an induction principle with no
cut case at all.

Stated as a recursor rather than left implicit, because everything downstream —
the subformula property, and the reflection argument that turns a cut-free proof
of a false sentence into a contradiction — is an induction over exactly this. -/
theorem cutFree_induction {motive : NONote → Sequent L → Prop}
    (hidentity : ∀ {α : NONote} {k : ℕ} (rl : L.Rel k) (v),
      motive α [Semiformula.rel rl v, Semiformula.nrel rl v])
    (hverum : ∀ {α : NONote}, motive α [⊤])
    (hor : ∀ {α β : NONote} {φ ψ : Proposition L} {Γ : Sequent L},
      β < α → BoundedDerivable 0 β (φ :: ψ :: Γ) → motive β (φ :: ψ :: Γ) →
      motive α (φ ⋎ ψ :: Γ))
    (hand : ∀ {α β γ : NONote} {φ ψ : Proposition L} {Γ : Sequent L},
      β < α → γ < α →
      BoundedDerivable 0 β (φ :: Γ) → BoundedDerivable 0 γ (ψ :: Γ) →
      motive β (φ :: Γ) → motive γ (ψ :: Γ) → motive α (φ ⋏ ψ :: Γ))
    (hall : ∀ {α β : NONote} {φ : Semiproposition L 1} {Γ : Sequent L},
      β < α → BoundedDerivable 0 β (Semiformula.free φ :: Γ⁺) →
      motive β (Semiformula.free φ :: Γ⁺) → motive α ((∀¹ φ) :: Γ))
    (hexs : ∀ {α β : NONote} {φ : Semiproposition L 1} {Γ : Sequent L} (t),
      β < α → BoundedDerivable 0 β (φ/[t] :: Γ) →
      motive β (φ/[t] :: Γ) → motive α ((∃¹ φ) :: Γ))
    (hcontraction : ∀ {α : NONote} {Δ Γ : Sequent L},
      Δ ⊆ Γ → BoundedDerivable 0 α Δ → motive α Δ → motive α Γ) :
    ∀ {α : NONote} {Γ : Sequent L}, BoundedDerivable 0 α Γ → motive α Γ := by
  intro α Γ h
  induction h with
  | identity rl v => exact hidentity rl v
  | verum => exact hverum
  | or hlt hd ih => exact hor hlt hd ih
  | and hb hc hp hq ihp ihq => exact hand hb hc hp hq ihp ihq
  | all hlt hd ih => exact hall hlt hd ih
  | exs t hlt hd ih => exact hexs t hlt hd ih
  | contraction ss hd ih => exact hcontraction ss hd ih
  | cut hcomp _ _ _ _ _ _ => exact absurd hcomp (Nat.not_lt_zero _)

end BoundedDerivable

end OrdinalAnalysis
