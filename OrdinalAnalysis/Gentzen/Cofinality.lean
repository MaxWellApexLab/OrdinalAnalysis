/-
  The finite omega towers are cofinal in the external normal-form notations,
  and their external structural codes coincide with the internal tower codes.
-/
import OrdinalAnalysis.Gentzen.OmegaTower
import OrdinalAnalysis.Gentzen.NotationBridge

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.Cofinality

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote

/-- External notation for `0, 1, ω, ω^ω, ...`, indexed exactly as
`OmegaTower.towerCode`. -/
def onoteTower : ℕ → ONote
  | 0 => 0
  | n + 1 => .oadd (onoteTower n) 1 0

/-- Every finite external omega tower is in Cantor normal form. -/
theorem onoteTower_nf : ∀ n : ℕ, ONote.NF (onoteTower n)
  | 0 => ONote.NF.zero
  | n + 1 => ONote.NF.oadd (onoteTower_nf n) 1 ONote.NFBelow.zero

/-- The corresponding subtype of normal-form notations. -/
def nonoteTower (n : ℕ) : NONote := ⟨onoteTower n, onoteTower_nf n⟩

@[simp] theorem onoteTower_zero : onoteTower 0 = 0 := rfl

@[simp] theorem onoteTower_succ (n : ℕ) :
    onoteTower (n + 1) = .oadd (onoteTower n) 1 0 := rfl

@[simp] theorem onoteTower_one : onoteTower 1 = 1 := rfl

/-- The external structural code is exactly the code used by the PA[X] tower. -/
theorem code_onoteTower : ∀ n : ℕ,
    NotationBridge.code (onoteTower n) = OmegaTower.towerCode n := by
  intro n
  induction n with
  | zero =>
      simp [onoteTower, NotationBridge.code, OmegaTower.towerCode]
  | succ n ih =>
      rw [onoteTower_succ, OmegaTower.towerCode]
      simp only [NotationBridge.code]
      rw [ih]
      simp [ocOadd, nat_pair_eq]

/-- Subtype-flavoured version of `code_onoteTower`. -/
theorem nonoteCode_tower (n : ℕ) :
    NotationBridge.nonoteCode (nonoteTower n) =
      OmegaTower.towerCode n :=
  code_onoteTower n

/-- The code identification after insertion into any model of IΣ₁. -/
@[simp] theorem nonoteModelCode_tower {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (n : ℕ) :
    NotationBridge.nonoteModelCode (V := V) (nonoteTower n) =
      ((OmegaTower.towerCode n : ℕ) : V) := by
  simp [NotationBridge.nonoteModelCode, nonoteCode_tower]

/-- Every external normal notation lies below a finite omega tower. -/
theorem exists_lt_onoteTower (a : ONote) (ha : ONote.NF a) :
    ∃ n : ℕ, a < onoteTower n := by
  induction a with
  | zero =>
      exact ⟨1, ONote.oadd_pos 0 1 0⟩
  | oadd e k r ihe ihr =>
      rcases ihe ha.fst with ⟨n, hn⟩
      refine ⟨n + 1, ?_⟩
      rw [onoteTower_succ]
      exact ONote.oadd_lt_oadd_1 ha hn

/-- Cofinality of the finite omega tower in all normal-form notations. -/
theorem exists_lt_nonoteTower (a : NONote) :
    ∃ n : ℕ, a < nonoteTower n := by
  rcases exists_lt_onoteTower a.1 a.2 with ⟨n, hn⟩
  exact ⟨n, hn⟩

end OrdinalAnalysis.Gentzen.Cofinality
