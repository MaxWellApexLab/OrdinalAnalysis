/-
  Structural facts about `⊢^α_r Γ`.

  Foundation's calculus has one structural rule, `contraction`, which is
  subset-based: from a derivation of `Δ` and `Δ ⊆ Γ` it derives `Γ`.  That
  single rule does the work of weakening, contraction and exchange at once, and
  it does not raise the ordinal index.
-/
import OrdinalAnalysis.Proof.Bounded

namespace OrdinalAnalysis

open LO LO.FirstOrder LO.FirstOrder.Derivation
open ONote

variable {L : Language}

namespace BoundedDerivable

/-- Weakening: anything derivable from a sub-sequent is derivable, at the cost
of one ordinal step. -/
theorem weakening {r : ℕ} {α : NONote} {Δ Γ : Sequent L}
    (h : BoundedDerivable r α Δ) (hss : Δ ⊆ Γ) :
    BoundedDerivable r α Γ :=
  .contraction hss h

/-- Exchange is a special case of weakening, since a permutation is a subset
in both directions. -/
theorem exchange {r : ℕ} {α : NONote} {Δ Γ : Sequent L}
    (h : BoundedDerivable r α Δ) (hperm : Δ.Perm Γ) :
    BoundedDerivable r α Γ :=
  .contraction hperm.subset h

/-- Adding a formula to the right of the sequent. -/
theorem cons {r : ℕ} {α : NONote} {φ : Proposition L} {Γ : Sequent L}
    (h : BoundedDerivable r α Γ) :
    BoundedDerivable r α (φ :: Γ) :=
  .contraction (List.subset_cons_self _ _) h

/-- Appending on the right. -/
theorem append_right {r : ℕ} {α : NONote} {Γ Δ : Sequent L}
    (h : BoundedDerivable r α Γ) :
    BoundedDerivable r α (Γ ++ Δ) :=
  .contraction (List.subset_append_left _ _) h

/-- Appending on the left. -/
theorem append_left {r : ℕ} {α : NONote} {Γ Δ : Sequent L}
    (h : BoundedDerivable r α Δ) :
    BoundedDerivable r α (Γ ++ Δ) :=
  .contraction (List.subset_append_right _ _) h

end BoundedDerivable

end OrdinalAnalysis
