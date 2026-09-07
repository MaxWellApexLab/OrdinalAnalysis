/-
  The cut rank of an LK derivation.

  `Foundation` supplies the Tait-style one-sided calculus and the predicate
  `Derivation.IsCutFree`, but no numerical measure of how much cutting a
  derivation does.  Gentzen's argument needs one: the elimination lemma peels
  off cuts one rank at a time, and the ordinal bound is a tower whose height is
  the rank.

  `cutRank d` is `0` when `d` uses no cut, and otherwise one more than the
  complexity of the most complex cut formula in `d`.
-/
import Foundation.FirstOrder.Basic.CutFree

namespace OrdinalAnalysis

open LO LO.FirstOrder LO.FirstOrder.Derivation

variable {L : Language}

/-- The cut rank of a derivation: `0` if it is cut free, otherwise one more
than the largest complexity of a cut formula occurring in it. -/
def cutRank {Δ : Sequent L} : ⊢ᴸᴷ¹ Δ → ℕ
  | Derivation.identity _ _ => 0
  | Derivation.verum => 0
  | @Derivation.cut _ φ _ _ dp dn =>
      max (φ.complexity + 1) (max (cutRank dp) (cutRank dn))
  | Derivation.contraction d _ => cutRank d
  | Derivation.or d => cutRank d
  | Derivation.and dp dq => max (cutRank dp) (cutRank dq)
  | Derivation.all d => cutRank d
  | Derivation.exs d => cutRank d

@[simp] theorem cutRank_identity {k : ℕ} (r : L.Rel k) (v) :
    cutRank (Derivation.identity r v) = 0 := by simp [cutRank]

@[simp] theorem cutRank_verum :
    cutRank (Derivation.verum : ⊢ᴸᴷ¹ ([⊤] : Sequent L)) = 0 := by simp [cutRank]

@[simp] theorem cutRank_contraction {Δ Γ : Sequent L} (d : ⊢ᴸᴷ¹ Δ) (ss : Δ ⊆ Γ) :
    cutRank (d.contraction ss) = cutRank d := by simp [cutRank]

@[simp] theorem cutRank_or {φ ψ : Proposition L} {Γ : Sequent L}
    (d : ⊢ᴸᴷ¹ φ :: ψ :: Γ) : cutRank d.or = cutRank d := by simp [cutRank]

@[simp] theorem cutRank_and {φ ψ : Proposition L} {Γ : Sequent L}
    (dp : ⊢ᴸᴷ¹ φ :: Γ) (dq : ⊢ᴸᴷ¹ ψ :: Γ) :
    cutRank (dp.and dq) = max (cutRank dp) (cutRank dq) := by simp [cutRank]

@[simp] theorem cutRank_cut {φ : Proposition L} {Γ Δ : Sequent L}
    (dp : ⊢ᴸᴷ¹ φ :: Γ) (dn : ⊢ᴸᴷ¹ ∼φ :: Δ) :
    cutRank (dp.cut dn) = max (φ.complexity + 1) (max (cutRank dp) (cutRank dn)) := by
  simp [cutRank]

/-- A cut always forces the rank above zero. -/
theorem cutRank_cut_pos {φ : Proposition L} {Γ Δ : Sequent L}
    (dp : ⊢ᴸᴷ¹ φ :: Γ) (dn : ⊢ᴸᴷ¹ ∼φ :: Δ) : 0 < cutRank (dp.cut dn) := by
  simp only [cutRank_cut]
  omega

/-- The bridge to `Foundation`'s own predicate: a derivation has rank zero
exactly when it is cut free.  This is what makes the ordinal analysis compose
with the existing library rather than duplicate it. -/
theorem cutRank_eq_zero_iff {Δ : Sequent L} (d : ⊢ᴸᴷ¹ Δ) :
    cutRank d = 0 ↔ IsCutFree d := by
  induction d with
  | identity r v => simp [IsCutFree.identity]
  | verum => simp [IsCutFree.verum]
  | cut dp dn _ _ =>
      simp only [cutRank_cut, Nat.max_eq_zero_iff]
      constructor
      · intro h; omega
      · intro h; exact absurd h (IsCutFree.not_cut dp dn)
  | contraction d ss ih =>
      rw [cutRank_contraction, ih]
      exact ⟨fun h => h.contraction ss, fun h => by cases h; assumption⟩
  | or d ih =>
      rw [cutRank_or, ih]
      exact ⟨fun h => h.or, fun h => by simpa using h⟩
  | and dp dq ihp ihq =>
      rw [cutRank_and, Nat.max_eq_zero_iff, ihp, ihq]
      exact ⟨fun h => h.1.and h.2, fun h => by simpa using h⟩
  | all d ih =>
      rw [cutRank, ih]
      exact ⟨fun h => h.all, fun h => by simpa using h⟩
  | exs d ih =>
      rw [cutRank, ih]
      exact ⟨fun h => h.exs _, fun h => by simpa using h⟩

end OrdinalAnalysis
