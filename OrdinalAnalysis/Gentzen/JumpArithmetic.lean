/-
  Concrete arithmetic laws for Gentzen's jump.

  The addition used by the finite iteration is totalized outside the coded
  normal forms.  This lets the primitive-recursive iteration graph have no
  side-condition: its zero and successor equations hold in every model of
  IΣ₁.  Normal-form restrictions remain confined to the notation relations
  used by the jump itself.
-/
import OrdinalAnalysis.Gentzen.CodedNotation

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.JumpArithmetic

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.CodedNotation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Totalized coded addition -/

/-- Ordinary coded ordinal addition on normal forms, and the left input otherwise. -/
noncomputable def safeIadd (a b : V) : V :=
  if isNF a then iadd a b else a

/-- A Σ₁ graph for `safeIadd`, with result-first argument order. -/
def safeIaddDef : 𝚺₁.Semisentence 3 := .mkSigma
  “z a b. ∃ q, !isNFbDef q a ∧
    ((q = 1 ∧ !iaddDef z a b) ∨ (q ≠ 1 ∧ z = a))”

instance safeIadd_defined : 𝚺₁-Function₂ (safeIadd : V → V → V) via safeIaddDef := .mk fun v ↦ by
  simp [safeIaddDef, safeIadd, isNF, isNFb_defined.iff, iadd_defined.iff]
  by_cases h : isNFb (v 1) = 1 <;> simp [h]

instance safeIadd_definable : 𝚺₁-Function₂ (safeIadd : V → V → V) :=
  safeIadd_defined.to_definable

@[simp] theorem safeIadd_of_nf {a b : V} (ha : isNF a) :
    safeIadd a b = iadd a b := by simp [safeIadd, ha]

@[simp] theorem safeIadd_of_not_nf {a b : V} (ha : ¬isNF a) :
    safeIadd a b = a := by simp [safeIadd, ha]

@[simp] theorem safeIadd_zero_left (b : V) : safeIadd 0 b = b := by
  simp [safeIadd]

/-! ### Unguarded finite iteration -/

def safeIterBlueprint : PR.Blueprint 2 where
  zero := .mkSigma “y b w. y = b”
  succ := .mkSigma “y ih k b w. !safeIaddDef y ih w”

noncomputable def safeIterConstruction {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : PR.Construction V safeIterBlueprint where
  zero := fun v ↦ v 0
  succ := fun v _ ih ↦ safeIadd ih (v 1)
  zero_defined := .mk fun v ↦ by simp [safeIterBlueprint]
  succ_defined := .mk fun v ↦ by
    simp [safeIterBlueprint, safeIadd_defined.iff]

/-- Result-first graph of `k` successive safe additions of `w` to `b`. -/
def safeIterDef : 𝚺₁.Semisentence 4 :=
  safeIterBlueprint.resultDef.rew (Rew.subst ![#0, #3, #1, #2])

@[simp] theorem eval_safeIterDef (z b w k : V) :
    safeIterDef.val.Evalb ![z, b, w, k] ↔
      z = (safeIterConstruction (V := V)).result ![b, w] k := by
  simp [safeIterDef, safeIterConstruction.result_defined_iff]

def safeAddCode : Semiformula LX ℕ 3 := liftCode safeIaddDef

def safeIterCode : Semiformula LX ℕ 4 := liftCode safeIterDef

/-! ### Pure-arithmetic closed statements -/

private def arithAddAt {n : ℕ} (z x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, x, y] ▹ Rewriting.emb safeIaddDef.val

private def arithIterAt {n : ℕ} (z b w k : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, b, w, k] ▹ Rewriting.emb safeIterDef.val

private def arithPrecAt {n : ℕ} (x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![x, y] ▹ Rewriting.emb precDef.val

/-- Arithmetic version of the zero-step law. -/
def arithmeticIterZeroStatement : Sentence ℒₒᵣ :=
  (∀¹ ∀¹ ∀¹
    (∼(arithIterAt #0 #2 #1 ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 3)) ⋎
      (“#0 = #2” : Semiformula ℒₒᵣ ℕ 3))).univCl

/-- Arithmetic version of the successor-step factorization law. -/
def arithmeticIterSuccStatement : Sentence ℒₒᵣ :=
  (∀¹ ∀¹ ∀¹ ∀¹
    (∼(arithIterAt #0 #3 #2 (‘(#1 + 1)’ : Semiterm ℒₒᵣ ℕ 4)) ⋎
      (∃¹ (arithIterAt #0 #4 #3 #2 ⋏ arithAddAt #1 #0 #3)))).univCl

/-- Arithmetic statement that zero has no coded-notation predecessor. -/
def arithmeticNoPredZeroStatement : Sentence ℒₒᵣ :=
  (∀¹ ∼(arithPrecAt (#0 : Semiterm ℒₒᵣ ℕ 1)
    ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 1))).univCl

/-- Arithmetic statement `SafeAdd(u, 0, u)`. -/
def arithmeticZeroAddStatement : Sentence ℒₒᵣ :=
  (∀¹ arithAddAt (#0 : Semiterm ℒₒᵣ ℕ 1)
    ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 1) #0).univCl

private lemma lMap_zero {n : ℕ} :
    Semiterm.lMap toLX ((0 : ℕ) : ArithmeticSemiterm ℕ n) =
      ((0 : ℕ) : Semiterm LX ℕ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, toLX]

private lemma lMap_succ_four :
    Semiterm.lMap toLX (‘(#1 + 1)’ : ArithmeticSemiterm ℕ 4) =
      (‘(#1 + 1)’ : Semiterm LX ℕ 4) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, Semiterm.Operator.Add.term_eq, toLX]
  apply funext
  rw [Fin.forall_fin_two]
  constructor
  · simp [Function.comp_def]
  · simp [Function.comp_def]
    exact Matrix.empty_eq _

private lemma map_iterZero_body :
    Semiformula.lMap toLX
        (∀¹ ∀¹ ∀¹
          (∼(arithIterAt #0 #2 #1 ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 3)) ⋎
            (“#0 = #2” : Semiformula ℒₒᵣ ℕ 3))) =
      (∀¹ ∀¹ ∀¹
        (∼(iterAt safeIterCode #0 #2 #1 ((0 : ℕ) : Semiterm LX ℕ 3)) ⋎
          (“#0 = #2” : Semiformula LX ℕ 3))) := by
  simp [arithIterAt, iterAt, safeIterCode, liftCode,
    Semiformula.lMap_subst]
  constructor
  · rw [lMap_zero]
  · simp [Semiformula.Operator.operator,
      Semiformula.Operator.Eq.sentence_eq, toLX]
    apply funext
    rw [Fin.forall_fin_two]
    exact ⟨rfl, rfl⟩

private lemma map_iterSucc_body :
    Semiformula.lMap toLX
        (∀¹ ∀¹ ∀¹ ∀¹
          (∼(arithIterAt #0 #3 #2 (‘(#1 + 1)’ : Semiterm ℒₒᵣ ℕ 4)) ⋎
            (∃¹ (arithIterAt #0 #4 #3 #2 ⋏ arithAddAt #1 #0 #3)))) =
      (∀¹ ∀¹ ∀¹ ∀¹
        (∼(iterAt safeIterCode #0 #3 #2 (‘(#1 + 1)’ : Semiterm LX ℕ 4)) ⋎
          (∃¹ (iterAt safeIterCode #0 #4 #3 #2 ⋏
            addAt safeAddCode #1 #0 #3)))) := by
  simp [arithIterAt, arithAddAt, iterAt, addAt, safeAddCode,
    safeIterCode, liftCode, Semiformula.lMap_subst]
  rw [lMap_succ_four]

private lemma map_noPredZero_body :
    Semiformula.lMap toLX
        (∀¹ ∼(arithPrecAt (#0 : Semiterm ℒₒᵣ ℕ 1)
          ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 1))) =
      (∀¹ ∼(precAt precCode (#0 : Semiterm LX ℕ 1)
        ((0 : ℕ) : Semiterm LX ℕ 1))) := by
  simp [arithPrecAt, precAt, precCode, liftCode,
    Semiformula.lMap_subst]
  rw [lMap_zero]

private lemma map_zeroAdd_body :
    Semiformula.lMap toLX
        (∀¹ arithAddAt (#0 : Semiterm ℒₒᵣ ℕ 1)
          ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 1) #0) =
      (∀¹ addAt safeAddCode (#0 : Semiterm LX ℕ 1)
        ((0 : ℕ) : Semiterm LX ℕ 1) #0) := by
  simp [arithAddAt, addAt, safeAddCode, liftCode,
    Semiformula.lMap_subst]
  rw [lMap_zero]

/-! ### IΣ₁ proofs of the iteration equations -/

theorem arithmetic_iterZero : 𝗜𝚺₁ ⊢ arithmeticIterZeroStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simp [models_iff, arithmeticIterZeroStatement, arithIterAt,
    eval_safeIterDef, safeIterConstruction]
  intro x x'
  exact ne_or_eq x' x

theorem arithmetic_iterSucc : 𝗜𝚺₁ ⊢ arithmeticIterSuccStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simp [models_iff, arithmeticIterSuccStatement, arithIterAt, arithAddAt,
    eval_safeIterDef, safeIadd_defined.iff, safeIterConstruction]
  intro b w k z
  exact ne_or_eq z (safeIadd ((safeIterConstruction (V := M)).result ![b, w] k) w)

private lemma icmp_ne_zero_right (x : V) : icmp x 0 ≠ 0 := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [icmp_pos_zero hx]
    simp

theorem arithmetic_noPredZero : 𝗜𝚺₁ ⊢ arithmeticNoPredZeroStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simp [models_iff, arithmeticNoPredZeroStatement, arithPrecAt, precDef,
    isNFb_defined.iff, icmp_defined.iff]
  intro x
  exact Or.inr (Ne.symm (icmp_ne_zero_right x))

theorem arithmetic_zeroAdd : 𝗜𝚺₁ ⊢ arithmeticZeroAddStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp only [arithmeticZeroAddStatement, Semiformula.eval_univCl,
    Semiformula.eval_all]
  intro f u
  simp [arithAddAt, safeIadd_defined.iff]

/-! ### Transport to PA[X] -/

lemma models_iterZero_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ iterZeroStatement safeIterCode ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticIterZeroStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [iterZeroStatement, arithmeticIterZeroStatement,
    Semiformula.eval_univCl]
  rw [← map_iterZero_body]
  simp [Semiformula.eval_lMap]

lemma models_iterSucc_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ iterSuccStatement safeAddCode safeIterCode ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticIterSuccStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [iterSuccStatement, arithmeticIterSuccStatement,
    Semiformula.eval_univCl]
  rw [← map_iterSucc_body]
  simp [Semiformula.eval_lMap]

lemma models_noPredZero_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ noPredZeroStatement precCode ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticNoPredZeroStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [noPredZeroStatement, arithmeticNoPredZeroStatement,
    Semiformula.eval_univCl]
  rw [← map_noPredZero_body]
  simp [Semiformula.eval_lMap]

lemma models_zeroAdd_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ zeroAddStatement safeAddCode ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticZeroAddStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [zeroAddStatement, arithmeticZeroAddStatement,
    Semiformula.eval_univCl]
  rw [← map_zeroAdd_body]
  simp [Semiformula.eval_lMap]

/-- Concrete zero-step premise for Gentzen's Lemma A. -/
theorem concrete_iterZero :
    paLX ⊢ iterZeroStatement safeIterCode := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_iterZero)
  intro M _ _
  exact models_iterZero_iff_arithmetic

/-- Concrete successor-step premise for Gentzen's Lemma A. -/
theorem concrete_iterSucc :
    paLX ⊢ iterSuccStatement safeAddCode safeIterCode := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_iterSucc)
  intro M _ _
  exact models_iterSucc_iff_arithmetic

/-- Concrete no-predecessor-of-zero premise for Gentzen's Lemma B. -/
theorem concrete_noPredZero :
    paLX ⊢ noPredZeroStatement precCode := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_noPredZero)
  intro M _ _
  exact models_noPredZero_iff_arithmetic

/-- Concrete zero-addition premise for Gentzen's Lemma B. -/
theorem concrete_zeroAdd :
    paLX ⊢ zeroAddStatement safeAddCode := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_zeroAdd)
  intro M _ _
  exact models_zeroAdd_iff_arithmetic

end OrdinalAnalysis.Gentzen.JumpArithmetic
