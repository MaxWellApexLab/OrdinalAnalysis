/-
  The arithmetic of the coded ϑ-notation as formulas of `ℒₒᵣ`.

  Each operation of `Arith` is a `Σ₁` semisentence in result-first form (the convention of
  `Gentzen/Jump.lean`: `Add(z, x, y)` means `z = x + y`, `OmegaPow(z, x)` means `z = ω^x`):
  `thAddDef`, `thNaddDef`, `thOmegaPowDef`, `thOmegaMulDef`, `thNumDef`, `thSuccDef`,
  `thOneDef`.  For each there are

  * the evaluation in an arbitrary model of `IΣ₁` (`eval_thAddDef`, …),
  * the evaluation at standard codes in an arbitrary model (`eval_thAddDef_mc`, …), and
  * the evaluation at codes in `ℕ` (`eval_thAddDef_code`, …).

  The ordinal sum and `ω^·` are also transported into the language `LX` (`addCodeTheta`,
  `omegaPowCodeTheta`), as the order is in `Standard`.
-/
import OrdinalAnalysis.ID1.Internal.ArithBridge
import OrdinalAnalysis.ID1.Internal.Standard

set_option autoImplicit false

namespace OrdinalAnalysis.ID1.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.CodedNotation (liftCode)
open OrdinalAnalysis.ThetaTerm

/-! ### The formulas -/

/-- `z` is the ordinal sum of `x` and `y`. -/
def thAddDef : 𝚺₁.Semisentence 3 := .mkSigma “z x y. !iaddDef z x y”

/-- `z` is the natural sum of `x` and `y`. -/
def thNaddDef : 𝚺₁.Semisentence 3 := .mkSigma “z x y. !inaddDef z x y”

/-- `z` is `ω^x`. -/
def thOmegaPowDef : 𝚺₁.Semisentence 2 := .mkSigma “z x. !iomegaPowDef z x”

/-- `z` is `ω · x`. -/
def thOmegaMulDef : 𝚺₁.Semisentence 2 := .mkSigma “z x. !iomegaMulDef z x”

/-- `z` is the code of the numeral `n`. -/
def thNumDef : 𝚺₁.Semisentence 2 := .mkSigma “z n. !inumDef z n”

/-- `z` is the successor of `x`. -/
def thSuccDef : 𝚺₁.Semisentence 2 := .mkSigma “z x. !isuccDef z x”

/-- `z` is the code of `1`. -/
def thOneDef : 𝚺₁.Semisentence 1 := .mkSigma “z. !ioneDef z”

/-- The ordinal sum as a formula of `ℒₒᵣ`. -/
def addC : Semisentence ℒₒᵣ 3 := thAddDef.val

/-- `ω^·` as a formula of `ℒₒᵣ`. -/
def omegaPowC : Semisentence ℒₒᵣ 2 := thOmegaPowDef.val

/-! ### Evaluation in models of `IΣ₁` -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem eval_thAddDef (z x y : V) : thAddDef.val.Evalb ![z, x, y] ↔ z = iadd x y := by
  simp [thAddDef, iadd_defined.iff]

@[simp] theorem eval_thNaddDef (z x y : V) :
    thNaddDef.val.Evalb ![z, x, y] ↔ z = inadd x y := by
  simp [thNaddDef, inadd_defined.iff]

@[simp] theorem eval_thOmegaPowDef (z x : V) :
    thOmegaPowDef.val.Evalb ![z, x] ↔ z = iomegaPow x := by
  simp [thOmegaPowDef, iomegaPow_defined.iff]

@[simp] theorem eval_thOmegaMulDef (z x : V) :
    thOmegaMulDef.val.Evalb ![z, x] ↔ z = iomegaMul x := by
  simp [thOmegaMulDef, iomegaMul_defined.iff]

@[simp] theorem eval_thNumDef (z n : V) : thNumDef.val.Evalb ![z, n] ↔ z = inum n := by
  simp [thNumDef, inum_defined.iff]

@[simp] theorem eval_thSuccDef (z x : V) : thSuccDef.val.Evalb ![z, x] ↔ z = isucc x := by
  simp [thSuccDef, isucc_defined.iff]

@[simp] theorem eval_thOneDef (z : V) : thOneDef.val.Evalb ![z] ↔ z = ione := by
  simp [thOneDef, ioneDef, ione, tcCons_defined.iff]

/-! ### Evaluation at standard codes -/

theorem eval_thAddDef_mc (z : V) (a b : ThetaNote) :
    thAddDef.val.Evalb ![z, mc a.1, mc b.1] ↔ z = mc (a + b).1 := by
  rw [eval_thAddDef, iadd_mc]

theorem eval_thNaddDef_mc (z : V) (a b : ThetaNote) :
    thNaddDef.val.Evalb ![z, mc a.1, mc b.1] ↔ z = mc (ThetaNote.nadd a b).1 := by
  rw [eval_thNaddDef, inadd_mc]

theorem eval_thOmegaPowDef_mc (z : V) (a : ThetaNote) :
    thOmegaPowDef.val.Evalb ![z, mc a.1] ↔ z = mc (ThetaNote.omegaPow a).1 := by
  rw [eval_thOmegaPowDef, iomegaPow_mc]

theorem eval_thOmegaMulDef_mc (z : V) (a : ThetaNote) :
    thOmegaMulDef.val.Evalb ![z, mc a.1] ↔ z = mc (ThetaNote.omegaMul a).1 := by
  rw [eval_thOmegaMulDef, iomegaMul_mc]

theorem eval_thNumDef_mc (z : V) (n : ℕ) :
    thNumDef.val.Evalb ![z, (n : V)] ↔ z = mc (ThetaNote.ofNat n).1 := by
  rw [eval_thNumDef, inum_mc]

theorem eval_thSuccDef_mc (z : V) (a : ThetaNote) :
    thSuccDef.val.Evalb ![z, mc a.1] ↔ z = mc (ThetaNote.succ a).1 := by
  rw [eval_thSuccDef, isucc_mc]

theorem eval_thOneDef_mc (z : V) : thOneDef.val.Evalb ![z] ↔ z = mc ThetaNote.one.1 := by
  rw [eval_thOneDef, ione_mc]

end Model

/-! ### Evaluation in `ℕ` -/

theorem eval_thAddDef_code (z : ℕ) (a b : ThetaNote) :
    thAddDef.val.Evalb ![z, codeNote a, codeNote b] ↔ z = codeNote (a + b) := by
  simpa [codeNote] using eval_thAddDef_mc (V := ℕ) z a b

theorem eval_thNaddDef_code (z : ℕ) (a b : ThetaNote) :
    thNaddDef.val.Evalb ![z, codeNote a, codeNote b] ↔ z = codeNote (ThetaNote.nadd a b) := by
  simpa [codeNote] using eval_thNaddDef_mc (V := ℕ) z a b

theorem eval_thOmegaPowDef_code (z : ℕ) (a : ThetaNote) :
    thOmegaPowDef.val.Evalb ![z, codeNote a] ↔ z = codeNote (ThetaNote.omegaPow a) := by
  simpa [codeNote] using eval_thOmegaPowDef_mc (V := ℕ) z a

theorem eval_thOmegaMulDef_code (z : ℕ) (a : ThetaNote) :
    thOmegaMulDef.val.Evalb ![z, codeNote a] ↔ z = codeNote (ThetaNote.omegaMul a) := by
  simpa [codeNote] using eval_thOmegaMulDef_mc (V := ℕ) z a

theorem eval_thNumDef_code (z n : ℕ) :
    thNumDef.val.Evalb ![z, n] ↔ z = codeNote (ThetaNote.ofNat n) := by
  simpa [codeNote] using eval_thNumDef_mc (V := ℕ) z n

theorem eval_thSuccDef_code (z : ℕ) (a : ThetaNote) :
    thSuccDef.val.Evalb ![z, codeNote a] ↔ z = codeNote (ThetaNote.succ a) := by
  simpa [codeNote] using eval_thSuccDef_mc (V := ℕ) z a

theorem eval_thOneDef_code (z : ℕ) : thOneDef.val.Evalb ![z] ↔ z = codeNote ThetaNote.one := by
  simpa [codeNote] using eval_thOneDef_mc (V := ℕ) z

/-! ### The formulas in `LX` -/

/-- The ordinal sum as a formula of `LX` (result first). -/
def addCodeTheta : Semiformula LX ℕ 3 := liftCode thAddDef.val

/-- `ω^·` as a formula of `LX` (result first). -/
def omegaPowCodeTheta : Semiformula LX ℕ 2 := liftCode thOmegaPowDef.val

@[simp] theorem XFree_addCodeTheta : LowerClass.XFree addCodeTheta :=
  LowerClass.XFree_lMap_toLX _

@[simp] theorem XFree_omegaPowCodeTheta : LowerClass.XFree omegaPowCodeTheta :=
  LowerClass.XFree_lMap_toLX _

@[simp] theorem freeVariables_addCodeTheta : addCodeTheta.freeVariables = ∅ := by
  simp [addCodeTheta, liftCode]

@[simp] theorem freeVariables_omegaPowCodeTheta : omegaPowCodeTheta.freeVariables = ∅ := by
  simp [omegaPowCodeTheta, liftCode]

end OrdinalAnalysis.ID1.Internal
