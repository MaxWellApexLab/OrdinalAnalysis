/-
  The order type of the coded ordering `≺` is exactly `ε₀`.

  `gentzen_theorem` is stated about the coded ordering `≺ = CodedNotation.precCode`,
  which in the standard model `ℕ` reads as `PrecStandard.precN`.  This file pins down
  what that ordering *is*, as a well-order in mathlib's sense: restricted to its field,
  the normal-form codes, it has order type `ε₀ : Ordinal`.

  The argument has two halves.

  * Coded side.  `CodeSurj.isNF_iff_exists_nonote` says the field of `≺` in `ℕ` is the
    range of `nonoteCode`, and `PrecStandard.precN_code_iff` says `nonoteCode` is
    order-preserving and reflecting.  So `nonoteCode` is an order isomorphism from
    mathlib's `NONote` onto the field of `≺` (`codeIso`), and the two have the same order
    type.
  * Ordinal side.  `ONoteEps.type_lt_NONote` (`Ordinal/ONoteEpsilon0.lean`): the normal-form
    notations have order type `ε₀`.

  Everything is a proof about ordinals and about the numbers `nonoteCode` produces; no
  formula of the object language is unfolded (`precN_iff`, `precN_code_iff` and
  `eval_precAt_numeral` are used as black boxes), so the kernel work is small.
-/
import Mathlib.SetTheory.Ordinal.Veblen
import OrdinalAnalysis.Gentzen.CodeSurj
import OrdinalAnalysis.Gentzen.GentzenTheorem
import OrdinalAnalysis.Ordinal.ONoteEpsilon0

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.OrderType

open Ordinal
open scoped Ordinal
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.NotationBridge
open OrdinalAnalysis.Gentzen.PrecStandard
open OrdinalAnalysis.Gentzen.CodeSurj
open OrdinalAnalysis.Gentzen.CodedNotation
open OrdinalAnalysis.Gentzen.Order
open OrdinalAnalysis.Gentzen.UpperBound
open OrdinalAnalysis.Gentzen.StandardLX
open LO LO.FirstOrder


/-! ### The field of `≺` and its order type -/

/-- The field of the coded ordering in `ℕ`: the numbers the internal recogniser accepts. -/
abbrev NFCode : Type := {n : ℕ // InternalONote.isNF (V := ℕ) n}

/-- The coded ordering `≺`, restricted to its field. -/
def precNF (m n : NFCode) : Prop := precN m.1 n.1

/-- The code of a notation, as a point of the field of `≺`. -/
def toNFCode (o : NONote) : NFCode :=
  ⟨nonoteCode o, (isNF_iff_exists_nonote _).mpr ⟨o, rfl⟩⟩

theorem toNFCode_injective : Function.Injective toNFCode := by
  intro a b h
  have hc : nonoteCode a = nonoteCode b := congrArg Subtype.val h
  refine le_antisymm (not_lt.1 fun hlt => ?_) (not_lt.1 fun hlt => ?_)
  · have h1 := precN_code_of_lt hlt
    rw [hc] at h1
    exact lt_irrefl _ ((precN_code_iff b b).1 h1)
  · have h1 := precN_code_of_lt hlt
    rw [← hc] at h1
    exact lt_irrefl _ ((precN_code_iff a a).1 h1)

theorem toNFCode_surjective : Function.Surjective toNFCode := by
  intro n
  obtain ⟨o, ho⟩ := (isNF_iff_exists_nonote n.1).1 n.2
  exact ⟨o, Subtype.ext ho⟩

/-- **`nonoteCode` is an order isomorphism from `NONote` onto the field of `≺`.** -/
noncomputable def codeIso : ((· < ·) : NONote → NONote → Prop) ≃r precNF where
  toEquiv := Equiv.ofBijective toNFCode ⟨toNFCode_injective, toNFCode_surjective⟩
  map_rel_iff' := fun {a b} => precN_code_iff a b

/-- The coded ordering is a well-order on its field. -/
instance precNF_isWellOrder : IsWellOrder NFCode precNF :=
  RelEmbedding.isWellOrder codeIso.symm.toRelEmbedding

/-- **The coded ordering `≺` has order type exactly `ε₀`.** -/
theorem type_precNF : Ordinal.type precNF = ε₀ := by
  rw [← OrdinalAnalysis.ONoteEps.type_lt_NONote]
  exact Ordinal.type_eq.2 ⟨codeIso.symm⟩

/-- `precNF` is the coded ordering in the spelling `gentzen_theorem` quantifies over:
on the field, `m ≺ n` holds exactly when `precAt precCode` at the two numerals holds in
the standard structure, whatever the value of `X`. -/
theorem precNF_iff_eval_precAt (P : ℕ → Prop) (m n : NFCode) (f : ℕ → ℕ) :
    precNF m n ↔ Semiformula.Eval (s := stdLX P) ![] f
      (precAt CodedNotation.precCode (LowerSyntax.numLX m.1) (LowerSyntax.numLX n.1)) :=
  (eval_precAt_numeral P m.1 n.1 f).symm

/-- Gentzen's theorem together with the order type of the ordering it is about. -/
theorem gentzen_theorem_with_order_type :
    Ordinal.type precNF = ε₀ ∧
      ((∀ (φ : Semiformula LX ℕ 1) (a : ONote) (ha : ONote.NF a),
          paLX ⊢ closedTI φ (notationTerm ⟨a, ha⟩)) ∧
        paLX ⊬ (TI CodedNotation.precCode).univCl) :=
  ⟨type_precNF, gentzen_theorem⟩

end OrdinalAnalysis.Gentzen.OrderType
