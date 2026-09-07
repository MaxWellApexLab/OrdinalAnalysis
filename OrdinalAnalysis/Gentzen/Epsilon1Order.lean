/-
  The `ε₁`-segment of the coded Veblen ordering.

  The lower bound `|PA + TI(ε₀)| ≥ ε₁` is the statement that `PA + TI(ε₀)`
  does not prove transfinite induction along the notations below `ε₁`.  The
  boundedness lemma refutes `TI` along *all* of the coded ordering of its
  notation system, so that system has to be exactly the notations below `ε₁`
  — `Gamma0Note.EpsilonBelow 1` — and the coded ordering has to say so:

      x ≺₁' y  :≡  x ≺₁ y ∧ y ≺₁ ε₁̄.

  The second conjunct is what cuts the ordering off: a code with no
  `≺₁'`-successor below `ε₁̄` has no `≺₁'`-predecessors worth mentioning
  either, and every code that *is* below `ε₁̄` codes an element of the
  segment.  The four facts a `CodedOrder` asks for follow from the ones
  `gamma0Order` already has, plus `a.2 : a.1 < ε₁` for the elements of the
  segment.
-/
import OrdinalAnalysis.Gentzen.CodedVeblen
import OrdinalAnalysis.Ordinal.Veblen.EpsilonBelow

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.Epsilon1Order

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.LowerSyntax
open OrdinalAnalysis.Gentzen.CodedVeblen OrdinalAnalysis.Gentzen.VNoteBridge
open OrdinalAnalysis.Gentzen.StandardLX (stdLX)
open OrdinalAnalysis.Gamma0Note

/-! ### The formula -/

/-- The code of `ε₁`, as a numeral in two variables. -/
def epsilon1Numeral : Semiterm LX ℕ 2 := Semiterm.numeral (gamma0Code (epsilonNote 1))

/-- **The `ε₁`-segment of `≺₁`**: `x ≺₁ y ∧ y ≺₁ ε₁̄`, in two variables. -/
def precCode₁' : Semiformula LX ℕ 2 :=
  precCode₁ ⋏ precAt precCode₁ (#1 : Semiterm LX ℕ 2) epsilon1Numeral

theorem XFree_precCode₁' : LowerClass.XFree precCode₁' := by
  refine ⟨XFree_precCode₁, ?_⟩
  simp only [precAt, LowerClass.XFree_rew]
  exact XFree_precCode₁

theorem freeVariables_precCode₁' : precCode₁'.freeVariables = ∅ := by
  have h : (precAt precCode₁ (#1 : Semiterm LX ℕ 2) epsilon1Numeral).freeVariables = ∅ :=
    freeVariables_precAt_eq_empty freeVariables_precCode₁ (by simp)
      (by simp [epsilon1Numeral])
  simp [precCode₁', h]

/-! ### The reading in `ℕ` -/

/-- `m ≺₁' n`: `m ≺₁ n` and `n ≺₁ code ε₁`. -/
def precN₁' (m n : ℕ) : Prop := precN₁ m n ∧ precN₁ n (gamma0Code (epsilonNote 1))

/-- At a pair of numerals, `≺₁'` is the conjunction of two instances of `≺₁`. -/
theorem precAt_precCode₁' (m n : ℕ) :
    precAt precCode₁' (numLX m) (numLX n)
      = precAt precCode₁ (numLX m) (numLX n)
        ⋏ precAt precCode₁ (numLX n) (numLX (gamma0Code (epsilonNote 1))) := by
  show Rew.subst ![numLX m, numLX n] ▹ (precCode₁ ⋏ precAt precCode₁ #1 epsilon1Numeral) = _
  rw [LogicalConnective.HomClass.map_and, subst_precAt]
  simp only [epsilon1Numeral, numLX, rew_numeral, Rew.subst_bvar, Matrix.cons_val_one]
  rfl

/-- **The syntactic bridge** for the segment. -/
theorem eval_precAt₁'_numeral (P : ℕ → Prop) (m n : ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := stdLX P) ![] f
      (precAt precCode₁' (LowerSyntax.numLX m) (LowerSyntax.numLX n)) ↔ precN₁' m n := by
  rw [precAt_precCode₁']
  simp only [LogicalConnective.HomClass.map_and, eval_precAt₁_numeral]
  rfl

/-- **The semantic bridge** for the segment: on codes of elements below `ε₁`,
`≺₁'` is the order of the segment. -/
theorem precN₁'_code_iff (a b : EpsilonBelow 1) :
    precN₁' (gamma0Code a.1) (gamma0Code b.1) ↔ a < b := by
  unfold precN₁'
  rw [precN₁_code_iff, precN₁_code_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, b.2⟩⟩

/-! ### The coded ordering of the segment -/

/-- **The coded ordering of the notations below `ε₁`.**  The `ε₁` lower bound
is the statement that `paLX₁` does not prove `TI` along it. -/
def epsilon1Order : CodedOrder (EpsilonBelow 1) where
  prec := precCode₁'
  xfree_prec := XFree_precCode₁'
  freeVariables_prec := freeVariables_precCode₁'
  code := fun a => gamma0Code a.1
  precN := precN₁'
  eval_precAt_numeral := eval_precAt₁'_numeral
  precN_code_iff := precN₁'_code_iff

@[simp] theorem epsilon1Order_prec : epsilon1Order.prec = precCode₁' := rfl

@[simp] theorem epsilon1Order_code (a : EpsilonBelow 1) :
    epsilon1Order.code a = gamma0Code a.1 := rfl

@[simp] theorem epsilon1Order_precN : epsilon1Order.precN = precN₁' := rfl

end OrdinalAnalysis.Gentzen.Epsilon1Order
