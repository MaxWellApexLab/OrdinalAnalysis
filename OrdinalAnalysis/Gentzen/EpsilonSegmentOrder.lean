/-
  The `ε_a`-segment of the coded Veblen ordering, for an arbitrary `ε`-number
  `ε_a` (`a : Gamma0Note`).

  This is `Epsilon1Order.lean` with the numeral `ε₁̄` (`gamma0Code (epsilonNote 1)`)
  everywhere replaced by the numeral of an arbitrary `ε_a` (`gamma0Code
  (epsilonNote a)`).  Nothing in `Epsilon1Order.lean` used more of `1` than
  that it names some `Gamma0Note`, so every definition and proof there carries
  over verbatim with `a` in place of `1`:

      x ≺ₐ' y  :≡  x ≺₁ y ∧ y ≺₁ ε_a̅.

  As with `epsilon1Order`, the four facts a `CodedOrder` asks for follow from
  the ones `gamma0Order` already has, plus `a.2 : a.1 < ε_a` for the elements
  of the segment `Gamma0Note.EpsilonBelow a`.  Taking `a := 1` recovers
  `epsilon1Order` on the nose (`epsilonOrder_one`), and `Boundedness.not_derivable_TI`
  instantiated at `epsilonOrder a` gives the lower bound at every ε-number,
  not just `ε₁`.
-/
import OrdinalAnalysis.Gentzen.Epsilon1Order
import OrdinalAnalysis.Gentzen.Boundedness

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.EpsilonSegmentOrder

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.LowerSyntax
open OrdinalAnalysis.Gentzen.CodedVeblen OrdinalAnalysis.Gentzen.VNoteBridge
open OrdinalAnalysis.Gentzen.StandardLX (stdLX trueArithLits)
open OrdinalAnalysis.Gentzen.Evaluate (ev)
open OrdinalAnalysis.Gentzen.EvInst (evInst)
open OrdinalAnalysis.Gamma0Note
open OrdinalAnalysis.Gentzen.Epsilon1Order (epsilon1Order)

/-! ### The formula -/

/-- The code of `ε_a`, as a numeral in two variables. -/
def epsilonNumeral (a : Gamma0Note) : Semiterm LX ℕ 2 :=
  Semiterm.numeral (gamma0Code (epsilonNote a))

/-- **The `ε_a`-segment of `≺₁`**: `x ≺₁ y ∧ y ≺₁ ε_a̅`, in two variables. -/
def precCodeSeg (a : Gamma0Note) : Semiformula LX ℕ 2 :=
  precCode₁ ⋏ precAt precCode₁ (#1 : Semiterm LX ℕ 2) (epsilonNumeral a)

theorem XFree_precCodeSeg (a : Gamma0Note) : LowerClass.XFree (precCodeSeg a) := by
  refine ⟨XFree_precCode₁, ?_⟩
  simp only [precAt, LowerClass.XFree_rew]
  exact XFree_precCode₁

theorem freeVariables_precCodeSeg (a : Gamma0Note) : (precCodeSeg a).freeVariables = ∅ := by
  have h : (precAt precCode₁ (#1 : Semiterm LX ℕ 2) (epsilonNumeral a)).freeVariables = ∅ :=
    freeVariables_precAt_eq_empty freeVariables_precCode₁ (by simp)
      (by simp [epsilonNumeral])
  simp [precCodeSeg, h]

/-! ### The reading in `ℕ` -/

/-- `m ≺ₐ' n`: `m ≺₁ n` and `n ≺₁ code ε_a`. -/
def precNSeg (a : Gamma0Note) (m n : ℕ) : Prop :=
  precN₁ m n ∧ precN₁ n (gamma0Code (epsilonNote a))

/-- At a pair of numerals, `≺ₐ'` is the conjunction of two instances of `≺₁`. -/
theorem precAt_precCodeSeg (a : Gamma0Note) (m n : ℕ) :
    precAt (precCodeSeg a) (numLX m) (numLX n)
      = precAt precCode₁ (numLX m) (numLX n)
        ⋏ precAt precCode₁ (numLX n) (numLX (gamma0Code (epsilonNote a))) := by
  show Rew.subst ![numLX m, numLX n] ▹ (precCode₁ ⋏ precAt precCode₁ #1 (epsilonNumeral a)) = _
  rw [LogicalConnective.HomClass.map_and, subst_precAt]
  simp only [epsilonNumeral, numLX, rew_numeral, Rew.subst_bvar, Matrix.cons_val_one]
  rfl

/-- **The syntactic bridge** for the segment. -/
theorem eval_precAtSeg_numeral (a : Gamma0Note) (P : ℕ → Prop) (m n : ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := stdLX P) ![] f
      (precAt (precCodeSeg a) (LowerSyntax.numLX m) (LowerSyntax.numLX n)) ↔ precNSeg a m n := by
  rw [precAt_precCodeSeg]
  simp only [LogicalConnective.HomClass.map_and, eval_precAt₁_numeral]
  rfl

/-- **The semantic bridge** for the segment: on codes of elements below `ε_a`,
`≺ₐ'` is the order of the segment. -/
theorem precNSeg_code_iff (a : Gamma0Note) (x y : Gamma0Note.EpsilonBelow a) :
    precNSeg a (gamma0Code x.1) (gamma0Code y.1) ↔ x < y := by
  unfold precNSeg
  rw [precN₁_code_iff, precN₁_code_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩

/-! ### The coded ordering of the segment -/

/-- **The coded ordering of the notations below `ε_a`.**  The `ε_a` lower
bound is the statement that `paLX₁` does not prove `TI` along it. -/
def epsilonOrder (a : Gamma0Note) : CodedOrder (Gamma0Note.EpsilonBelow a) where
  prec := precCodeSeg a
  xfree_prec := XFree_precCodeSeg a
  freeVariables_prec := freeVariables_precCodeSeg a
  code := fun x => gamma0Code x.1
  precN := precNSeg a
  eval_precAt_numeral := eval_precAtSeg_numeral a
  precN_code_iff := precNSeg_code_iff a

@[simp] theorem epsilonOrder_prec (a : Gamma0Note) : (epsilonOrder a).prec = precCodeSeg a := rfl

@[simp] theorem epsilonOrder_code (a : Gamma0Note) (x : Gamma0Note.EpsilonBelow a) :
    (epsilonOrder a).code x = gamma0Code x.1 := rfl

@[simp] theorem epsilonOrder_precN (a : Gamma0Note) : (epsilonOrder a).precN = precNSeg a := rfl

/-- **At `a = 1` this is exactly `epsilon1Order`.**  Every field of `epsilonOrder 1`
unfolds to the corresponding field of `epsilon1Order` on the nose. -/
theorem epsilonOrder_one : epsilonOrder 1 = epsilon1Order := rfl

/-! ### The lower bound at every `ε`-number -/

/-- **`ε_a` is a lower bound, for every `ε`-number `ε_a`.**  `TI` along the
coded ordering of the notations below `ε_a` has no cut-free derivation at any
height.  The `a := 1` case is `|PA + TI(ε₀)| ≥ ε₁`; the general statement is
the same argument run on `epsilonOrder a` instead of `epsilon1Order`. -/
theorem not_derivable_TI_epsilon (a : Gamma0Note) (α : Gamma0Note.EpsilonBelow a) :
    ¬ OmegaDerivable trueArithLits evInst 0 α [ev (TI (epsilonOrder a).prec)] :=
  Boundedness.not_derivable_TI (epsilonOrder a) α

end OrdinalAnalysis.Gentzen.EpsilonSegmentOrder
