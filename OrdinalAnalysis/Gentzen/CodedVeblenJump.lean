/-
  Gentzen's jump over the coded Veblen ordering: the `LX` graph formulas of the
  internal operations of `InternalVNoteJump`, and the three `paLX` derivations that
  `Jump.jump_B` consumes for `precCode₁` — Lemma A, the absence of predecessors of `0`,
  and the left-zero law of the addition graph.

  This is `JumpArithmetic.lean` + `OmegaCover.lean` one notation system up.  Every
  statement is first proved in `IΣ₁` semantically, in an arbitrary model, from the
  internal lemmas, and then moved to `PA[X]` by `paLX_of_peano_semantic` exactly as
  `UpperBound.lean` does for the Cantor-normal-form versions.

  The graph formulas follow the result-first convention of `Jump.lean`:
  `addCode₁ (z, x, y)` says `z = x + y` (totalised outside the normal forms, as
  `safeAddCode`), and `omegaPowCode₁ (u, a)` says `a` is normal and `u = ω ^ a`.
-/
import OrdinalAnalysis.Gentzen.InternalVNoteJump
import OrdinalAnalysis.Gentzen.CodedVeblen

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OrdinalAnalysis.Gentzen.CodedVeblenJump

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.InternalVNote
open OrdinalAnalysis.Gentzen.InternalVNoteOrder
open OrdinalAnalysis.Gentzen.InternalVNoteJump
open OrdinalAnalysis.Gentzen.CodedNotation (liftCode paLX_of_peano_semantic)
open OrdinalAnalysis.Gentzen.CodedVeblen

/-! ## The arithmetic graph formulas -/

/-- `u = ω ^ a`, for normal `a`. -/
def omegaPowDef₁ : 𝚺₁.Semisentence 2 := .mkSigma
  “z a. !isNFb₁Def 1 a ∧ !iomegaPowDef z a”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem eval_omegaPowDef₁ (z a : V) :
    omegaPowDef₁.val.Evalb ![z, a] ↔ isNF₁ a ∧ z = iomegaPow a := by
  simp [omegaPowDef₁, isNF₁, isNFb₁_defined.iff, iomegaPow_defined.iff, eq_comm]

/-! ## The formulas, in `LX` -/

/-- The result-first addition graph on Veblen codes (totalised outside normal forms). -/
def addCode₁ : Semiformula LX ℕ 3 := liftCode safeIadd₁Def

/-- The result-first ω-power graph on Veblen codes. -/
def omegaPowCode₁ : Semiformula LX ℕ 2 := liftCode omegaPowDef₁

/-- The result-first finite-iteration graph on Veblen codes. -/
def iterCode₁ : Semiformula LX ℕ 4 := liftCode safeIter₁Def

/-! ## Pure-arithmetic closed statements -/

private def arithAddAt {n : ℕ} (z x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, x, y] ▹ Rewriting.emb safeIadd₁Def.val

private def arithIterAt {n : ℕ} (z b w k : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, b, w, k] ▹ Rewriting.emb safeIter₁Def.val

private def arithPrecAt {n : ℕ} (x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![x, y] ▹ Rewriting.emb precDef₁.val

private def arithOmegaPowAt {n : ℕ} (z a : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, a] ▹ Rewriting.emb omegaPowDef₁.val

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

/-- The omega-cover premise, stated wholly in the language of arithmetic. -/
def arithmeticOmegaCoverStatement : Sentence ℒₒᵣ :=
  (∀¹ ∀¹ ∀¹ ∀¹ ∀¹
    (∼(arithOmegaPowAt #2 #4) ⋎
      (∼(arithAddAt #1 #3 #2) ⋎
        (∼(arithPrecAt #0 #1) ⋎
          (arithPrecAt #0 #3 ⋎
            ((“#0 = #3” : Semiformula ℒₒᵣ ℕ 5) ⋎
              (∃¹ ∃¹ ∃¹ ∃¹
                (arithPrecAt #3 #8 ⋏
                  (arithOmegaPowAt #2 #3 ⋏
                    (arithIterAt #0 #7 #2 #1 ⋏
                      arithPrecAt #4 #0)))))))))).univCl

/-! ## `IΣ₁` proofs -/

theorem arithmetic_iterZero : 𝗜𝚺₁ ⊢ arithmeticIterZeroStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simp [models_iff, arithmeticIterZeroStatement, arithIterAt,
    eval_safeIter₁Def, safeIter₁Construction]
  intro x x'
  exact ne_or_eq x' x

theorem arithmetic_iterSucc : 𝗜𝚺₁ ⊢ arithmeticIterSuccStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simp [models_iff, arithmeticIterSuccStatement, arithIterAt, arithAddAt,
    eval_safeIter₁Def, safeIadd₁_defined.iff, safeIter₁Construction]
  intro b w k z
  exact ne_or_eq z (safeIadd₁ ((safeIter₁Construction (V := M)).result ![b, w] k) w)

theorem arithmetic_noPredZero : 𝗜𝚺₁ ⊢ arithmeticNoPredZeroStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simp [models_iff, arithmeticNoPredZeroStatement, arithPrecAt, eval_precDef₁]
  intro x _ h
  exact icmp₁_right_zero_ne_zero x h

theorem arithmetic_zeroAdd : 𝗜𝚺₁ ⊢ arithmeticZeroAddStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp only [arithmeticZeroAddStatement, Semiformula.eval_univCl,
    Semiformula.eval_all]
  intro f u
  simp [arithAddAt, safeIadd₁_defined.iff]

/-- `IΣ₁` proves the omega-cover law for the internal Veblen codes. -/
theorem arithmetic_omegaCover : 𝗜𝚺₁ ⊢ arithmeticOmegaCoverStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simp [models_iff, arithmeticOmegaCoverStatement, arithOmegaPowAt,
    arithAddAt, arithPrecAt, arithIterAt, eval_safeIter₁Def, safeIadd₁_defined.iff,
    eval_precDef₁, eval_omegaPowDef₁]
  intro a b u z g
  by_cases hω : isNF₁ a ∧ u = iomegaPow a
  · right
    by_cases hadd : z = safeIadd₁ b u
    · right
      by_cases hprec : isNF₁ g ∧ isNF₁ z ∧ icmp₁ g z = 0
      · right
        rcases hω with ⟨ha, hu⟩
        rcases hprec with ⟨hg, hz, hgz⟩
        have hb : isNF₁ b := by
          by_contra hb
          have hzb : z = b := by
            calc
              z = safeIadd₁ b u := hadd
              _ = b := safeIadd₁_of_not_nf hb
          exact hb (hzb ▸ hz)
        have hzi : z = iadd₁ b (iomegaPow a) := by
          calc
            z = safeIadd₁ b u := hadd
            _ = safeIadd₁ b (iomegaPow a) := by rw [hu]
            _ = iadd₁ b (iomegaPow a) := safeIadd₁_of_nf hb
        rw [hzi] at hgz
        by_cases hgb : icmp₁ g b = 0
        · exact Or.inl ⟨hg, hb, hgb⟩
        · right
          by_cases hEq : g = b
          · exact Or.inl hEq
          · right
            obtain ⟨d, k, hd, hda, hgk⟩ :=
              iadd₁_omegaPow_cover ha hb hg hgb hEq hgz
            refine ⟨d, ⟨hd, ha, hda⟩, hd, hg, k + 1, ?_, ?_⟩
            · rw [safeIter₁_omegaBlock_succ b d k hb hd]
              exact isNF₁_iadd₁_block (isNF₁_iomegaPow hd) (by simp) b hb
            · rw [safeIter₁_omegaBlock_succ b d k hb hd]
              exact hgk
      · left
        intro hg hz hgz
        exact hprec ⟨hg, hz, hgz⟩
    · left
      exact hadd
  · left
    intro ha hu
    exact hω ⟨ha, hu⟩

/-! ## Transport to `PA[X]` -/

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
        (∼(iterAt iterCode₁ #0 #2 #1 ((0 : ℕ) : Semiterm LX ℕ 3)) ⋎
          (“#0 = #2” : Semiformula LX ℕ 3))) := by
  simp [arithIterAt, iterAt, iterCode₁, liftCode,
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
        (∼(iterAt iterCode₁ #0 #3 #2 (‘(#1 + 1)’ : Semiterm LX ℕ 4)) ⋎
          (∃¹ (iterAt iterCode₁ #0 #4 #3 #2 ⋏
            addAt addCode₁ #1 #0 #3)))) := by
  simp [arithIterAt, arithAddAt, iterAt, addAt, addCode₁,
    iterCode₁, liftCode, Semiformula.lMap_subst]
  rw [lMap_succ_four]

private lemma map_noPredZero_body :
    Semiformula.lMap toLX
        (∀¹ ∼(arithPrecAt (#0 : Semiterm ℒₒᵣ ℕ 1)
          ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 1))) =
      (∀¹ ∼(precAt precCode₁ (#0 : Semiterm LX ℕ 1)
        ((0 : ℕ) : Semiterm LX ℕ 1))) := by
  simp [arithPrecAt, precAt, precCode₁, liftCode,
    Semiformula.lMap_subst]
  rw [lMap_zero]

private lemma map_zeroAdd_body :
    Semiformula.lMap toLX
        (∀¹ arithAddAt (#0 : Semiterm ℒₒᵣ ℕ 1)
          ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 1) #0) =
      (∀¹ addAt addCode₁ (#0 : Semiterm LX ℕ 1)
        ((0 : ℕ) : Semiterm LX ℕ 1) #0) := by
  simp [arithAddAt, addAt, addCode₁, liftCode,
    Semiformula.lMap_subst]
  rw [lMap_zero]

lemma models_iterZero_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ iterZeroStatement iterCode₁ ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticIterZeroStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [iterZeroStatement, arithmeticIterZeroStatement,
    Semiformula.eval_univCl]
  rw [← map_iterZero_body]
  simp [Semiformula.eval_lMap]

lemma models_iterSucc_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ iterSuccStatement addCode₁ iterCode₁ ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticIterSuccStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [iterSuccStatement, arithmeticIterSuccStatement,
    Semiformula.eval_univCl]
  rw [← map_iterSucc_body]
  simp [Semiformula.eval_lMap]

lemma models_noPredZero_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ noPredZeroStatement precCode₁ ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticNoPredZeroStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [noPredZeroStatement, arithmeticNoPredZeroStatement,
    Semiformula.eval_univCl]
  rw [← map_noPredZero_body]
  simp [Semiformula.eval_lMap]

lemma models_zeroAdd_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ zeroAddStatement addCode₁ ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticZeroAddStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [zeroAddStatement, arithmeticZeroAddStatement,
    Semiformula.eval_univCl]
  rw [← map_zeroAdd_body]
  simp [Semiformula.eval_lMap]

lemma models_omegaCover_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ omegaCoverStatement precCode₁ addCode₁ omegaPowCode₁ iterCode₁ ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticOmegaCoverStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  simp [models_iff, omegaCoverStatement, arithmeticOmegaCoverStatement,
    arithOmegaPowAt, arithAddAt, arithPrecAt, arithIterAt,
    omegaPowAt, addAt, precAt, iterAt, precCode₁, addCode₁,
    omegaPowCode₁, iterCode₁, liftCode, Semiformula.eval_lMap]
  rfl

/-! ## The `paLX` derivations -/

/-- Zero-step premise for Gentzen's Lemma A over the Veblen codes. -/
theorem concrete_iterZero₁ :
    paLX ⊢ iterZeroStatement iterCode₁ := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_iterZero)
  intro M _ _
  exact models_iterZero_iff_arithmetic

/-- Successor-step premise for Gentzen's Lemma A over the Veblen codes. -/
theorem concrete_iterSucc₁ :
    paLX ⊢ iterSuccStatement addCode₁ iterCode₁ := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_iterSucc)
  intro M _ _
  exact models_iterSucc_iff_arithmetic

/-- **Zero has no predecessor in the coded Veblen ordering.** -/
theorem noPredZero₁ :
    paLX ⊢ noPredZeroStatement precCode₁ := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_noPredZero)
  intro M _ _
  exact models_noPredZero_iff_arithmetic

/-- **The left-zero law of the Veblen addition graph.** -/
theorem zeroAdd₁ :
    paLX ⊢ zeroAddStatement addCode₁ := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_zeroAdd)
  intro M _ _
  exact models_zeroAdd_iff_arithmetic

/-- The omega-cover premise for Gentzen's Lemma A over the Veblen codes. -/
theorem concrete_omegaCover₁ :
    paLX ⊢ omegaCoverStatement precCode₁ addCode₁ omegaPowCode₁ iterCode₁ := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_omegaCover)
  intro M _ _
  exact models_omegaCover_iff_arithmetic

/-- **Gentzen's Lemma A over the Veblen codes.** -/
theorem jumpA₁ (φ : Semiformula LX ℕ 1) :
    paLX ⊢ jumpAStatement precCode₁ addCode₁ omegaPowCode₁ φ :=
  jump_A precCode₁ addCode₁ omegaPowCode₁ iterCode₁ φ
    concrete_iterZero₁ concrete_iterSucc₁ concrete_omegaCover₁

/-- **Gentzen's Lemma B over the Veblen codes.** -/
theorem jumpB₁ (φ : Semiformula LX ℕ 1) :
    paLX ⊢ jumpBStatement precCode₁ addCode₁ omegaPowCode₁ φ :=
  jump_B precCode₁ addCode₁ omegaPowCode₁ φ (jumpA₁ φ) noPredZero₁ zeroAdd₁

end OrdinalAnalysis.Gentzen.CodedVeblenJump
