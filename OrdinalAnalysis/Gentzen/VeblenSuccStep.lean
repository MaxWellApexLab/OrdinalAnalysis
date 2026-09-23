/-
  The successor step of the Veblen ordering, at a *variable* base.

  `Epsilon1UpperBound.concrete_succ` says: below the code of `ε₀ + 1` a normal code is below
  the code of `ε₀` or equal to it.  Both endpoints there are closed numerals.  The ACA upper
  bound runs the same step at the ε-number `ε_h` produced by the internal cover, i.e. at a
  variable, so the statement has to quantify over the base.

  The base is guarded by `Base(e)`: `e` is a normal code which is either `0` or a single
  Veblen term `φ_p(q)` with `p ≠ 0` — that is, `0` or an ε-number.  Those are exactly the
  codes `InternalVNoteOrder.{eq_zero_of_lt_one, lt_or_eq_of_lt_term_succ}` handle, and exactly
  the values the internal ε-logarithm of `InternalEpsCover` returns.  On them the successor is
  the ordinary coded sum `e + 1`, so the step is stated with the addition graph `addCode₁` and
  the closed numeral for the code of `1`, with no new arithmetic function.
-/
import OrdinalAnalysis.Gentzen.VeblenTower

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OrdinalAnalysis.Gentzen.VeblenSuccStep

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.InternalVNote
open OrdinalAnalysis.Gentzen.InternalVNoteOrder
open OrdinalAnalysis.Gentzen.InternalVNoteJump
open OrdinalAnalysis.Gentzen.CodedNotation (liftCode paLX_of_peano_semantic)
open OrdinalAnalysis.Gentzen.CodedVeblen
open OrdinalAnalysis.Gentzen.CodedVeblenJump
open OrdinalAnalysis.Gentzen.VNoteBridge
open OrdinalAnalysis.Gentzen.OmegaTower (lMap_numeral)
open OrdinalAnalysis.Gentzen.Epsilon1UpperBound
  (gamma0Term closedTI₁ closedPrec₁ vmodelCode_one)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The code of `1`, and the successor of an ε-number -/

lemma modelCode_one : gamma0ModelCode (V := V) (1 : Gamma0Note) = vcVadd 0 0 1 0 := by
  rw [gamma0ModelCode_eq]
  exact vmodelCode_one

/-- A single term `φ_p(q)` with `p ≠ 0` is above the code of `1`. -/
lemma term_gt_one {p q : V} (hp : p ≠ 0) :
    icmp₁ (vcVadd p q 1 0) (vcVadd 0 0 1 0) = 2 := by
  rw [icmp₁_lead_lead, icmp₁_pos_zero hp, leadV_two, icmp₁_vcVadd_zero]

/-- The coded successor of a single term `φ_p(q)` with `p ≠ 0` is the term with tail `1`. -/
lemma iadd₁_term_one {p q : V} (hp : p ≠ 0) :
    iadd₁ (vcVadd p q 1 0) (vcVadd 0 0 1 0) = vcVadd p q 1 (vcVadd 0 0 1 0) := by
  rw [iadd₁_vcVadd, if_neg (vcVadd_ne_zero 0 0 1 0), vcLead_vcVadd,
    if_neg (by rw [term_gt_one hp]; exact _root_.two_ne_zero),
    if_neg (by rw [term_gt_one hp]; exact (one_lt_two).ne'), iadd₁_zero_left]

/-! ## The guard `Base(e)` -/

/-- `Base(e)`: `e` is a normal code which is `0` or a single Veblen term `φ_p(q)` with
`p ≠ 0`, i.e. `0` or an ε-number. -/
def baseDef₁ : 𝚺₁.Semisentence 1 := .mkSigma
  “e. !isNFb₁Def 1 e ∧ (e = 0 ∨ !fixIndicDef 1 e)”

@[simp] theorem eval_baseDef₁ (e : V) :
    baseDef₁.val.Evalb ![e] ↔ isNF₁ e ∧ (e = 0 ∨ fixIndic e = 1) := by
  simp [baseDef₁, isNF₁, isNFb₁_defined.iff, fixIndic_defined.iff, eq_comm]

/-- The guard, in `LX`. -/
def baseCode₁ : Semiformula LX ℕ 1 := liftCode baseDef₁

/-! ## The statement -/

/--
**The successor step at a variable base.**

`∀ e ∀ s ∀ y (Base(e) → Add(s, e, 1̄) → y ≺₁ s → (y ≺₁ e ∨ y = e))`.
-/
noncomputable def succGeneralStatement : Sentence LX :=
  (∀¹ ∀¹ ∀¹
    (∼(formulaAt baseCode₁ (#2 : Semiterm LX ℕ 3)) ⋎
      (∼(addAt addCode₁ #1 #2 ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 3)) ⋎
        (∼(precAt precCode₁ #0 #1) ⋎
          (precAt precCode₁ #0 #2 ⋎
            (“#0 = #2” : Semiformula LX ℕ 3)))))).univCl

private def arithBaseAt {n : ℕ} (e : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![e] ▹ Rewriting.emb baseDef₁.val

private def arithAddAt {n : ℕ} (z x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, x, y] ▹ Rewriting.emb safeIadd₁Def.val

private def arithPrecAt {n : ℕ} (x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![x, y] ▹ Rewriting.emb precDef₁.val

noncomputable def arithmeticSuccGeneralStatement : ArithmeticSentence :=
  (∀¹ ∀¹ ∀¹
    (∼(arithBaseAt (#2 : Semiterm ℒₒᵣ ℕ 3)) ⋎
      (∼(arithAddAt #1 #2 ((gamma0Code 1 : ℕ) : Semiterm ℒₒᵣ ℕ 3)) ⋎
        (∼(arithPrecAt #0 #1) ⋎
          (arithPrecAt #0 #2 ⋎
            (“#0 = #2” : Semiformula ℒₒᵣ ℕ 3)))))).univCl

/-! ## The `IΣ₁` proof -/

/-- The mathematical content: below `e + 1` a normal code is below `e` or equal to it, for
`e` zero or a single Veblen term. -/
theorem lt_or_eq_of_lt_succ {e y : V} (he : isNF₁ e)
    (hbase : e = 0 ∨ fixIndic e = 1) (hy : isNF₁ y)
    (hlt : icmp₁ y (iadd₁ e (vcVadd 0 0 1 0)) = 0) :
    icmp₁ y e = 0 ∨ y = e := by
  rcases hbase with rfl | hfix
  · rw [iadd₁_zero_left] at hlt
    exact Or.inr (eq_zero_of_lt_one hy hlt)
  · obtain ⟨p, q, rfl, hp⟩ := fix_destruct hfix
    rw [iadd₁_term_one hp] at hlt
    exact lt_or_eq_of_lt_term_succ hy he hlt

theorem arithmetic_succGeneral : 𝗜𝚺₁ ⊢ arithmeticSuccGeneralStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp [arithmeticSuccGeneralStatement, arithBaseAt, arithAddAt, arithPrecAt,
    eval_baseDef₁, eval_precDef₁, safeIadd₁_defined.iff,
    Structure.numeral_eq_numeral, numeral_eq_natCast]
  intro e s y
  have hone : ((gamma0Code 1 : ℕ) : M) = vcVadd 0 0 1 0 := modelCode_one
  have key :
      (isNF₁ e ∧ (e = 0 ∨ fixIndic e = 1)) →
      s = safeIadd₁ e ((gamma0Code 1 : ℕ) : M) →
      (isNF₁ y ∧ isNF₁ s ∧ icmp₁ y s = 0) →
      ((isNF₁ y ∧ isNF₁ e ∧ icmp₁ y e = 0) ∨ y = e) := by
    rintro ⟨he, hbase⟩ hs ⟨hy, -, hys⟩
    rw [hs, safeIadd₁_of_nf he, hone] at hys
    rcases lt_or_eq_of_lt_succ he hbase hy hys with h | h
    · exact Or.inl ⟨hy, he, h⟩
    · exact Or.inr h
  tauto

/-! ## Transport to `PA[X]` -/

private lemma map_succGeneral_body :
    Semiformula.lMap toLX
        (∀¹ ∀¹ ∀¹
          (∼(arithBaseAt (#2 : Semiterm ℒₒᵣ ℕ 3)) ⋎
            (∼(arithAddAt #1 #2 ((gamma0Code 1 : ℕ) : Semiterm ℒₒᵣ ℕ 3)) ⋎
              (∼(arithPrecAt #0 #1) ⋎
                (arithPrecAt #0 #2 ⋎
                  (“#0 = #2” : Semiformula ℒₒᵣ ℕ 3)))))) =
      (∀¹ ∀¹ ∀¹
        (∼(formulaAt baseCode₁ (#2 : Semiterm LX ℕ 3)) ⋎
          (∼(addAt addCode₁ #1 #2 ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 3)) ⋎
            (∼(precAt precCode₁ #0 #1) ⋎
              (precAt precCode₁ #0 #2 ⋎
                (“#0 = #2” : Semiformula LX ℕ 3)))))) := by
  simp [arithBaseAt, arithAddAt, arithPrecAt, formulaAt, addAt, precAt,
    baseCode₁, addCode₁, precCode₁, liftCode, Semiformula.lMap_subst]
  refine ⟨?_, ?_⟩
  · rw [lMap_numeral (gamma0Code 1)]
  · simp [Semiformula.Operator.operator,
      Semiformula.Operator.Eq.sentence_eq, toLX]
    apply funext
    rw [Fin.forall_fin_two]
    exact ⟨rfl, rfl⟩

lemma models_succGeneral_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ succGeneralStatement ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticSuccGeneralStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [succGeneralStatement, arithmeticSuccGeneralStatement,
    Semiformula.eval_univCl]
  rw [← map_succGeneral_body]
  simp [Semiformula.eval_lMap]

/-- **The successor step of `Epsilon1UpperBound` with the `ε₀` numeral replaced by a
variable.** -/
theorem concrete_succ_general : paLX ⊢ succGeneralStatement := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_succGeneral)
  intro M _ _
  exact models_succGeneral_iff_arithmetic

/-! ## Semantic form, and the `closedTI₁` lifting -/

theorem models_succGeneralStatement {M : Type*} [Nonempty M] [Structure LX M]
    [Structure.Eq LX M] :
    M↓[LX] ⊧ succGeneralStatement ↔
      ∀ f : ℕ → M, ∀ e s y : M,
        baseCode₁.Eval ![e] f →
        addCode₁.Eval ![s, e, ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 0).val ![] f] f →
        precCode₁.Eval ![y, s] f →
        precCode₁.Eval ![y, e] f ∨ y = e := by
  classical
  simp [models_iff, succGeneralStatement]
  constructor
  · intro h f e s y hb ha hp
    rcases h f e s y with hnb | hna | hnp | hgoal
    · exact (hnb (by simpa using hb)).elim
    · exact (hna (by simpa using ha)).elim
    · exact (hnp hp).elim
    · exact hgoal
  · intro h f e s y
    by_cases hb : baseCode₁.Eval ![e] f
    · right
      by_cases ha : addCode₁.Eval
          ![s, e, ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 0).val ![] f] f
      · right
        by_cases hp : precCode₁.Eval ![y, s] f
        · exact Or.inr (h f e s y hb (by simpa using ha) hp)
        · exact Or.inl hp
      · exact Or.inl (by simpa using ha)
    · exact Or.inl (by simpa using hb)

/--
**The `closedTI₁` lifting of the successor step.**  If `a` is a closed term satisfying the
guard and `b` is its coded successor, transfinite induction below `a` gives it below `b`.
-/
theorem closedTI₁_succ_general (φ : Semiformula LX ℕ 1) (a b : Semiterm LX ℕ 0)
    (hBase : paLX ⊢ (formulaAt baseCode₁ a).univCl)
    (hAdd : paLX ⊢
      (addAt addCode₁ b a ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 0)).univCl)
    (hTI : paLX ⊢ closedTI₁ φ a) :
    paLX ⊢ closedTI₁ φ b := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  have hS : M↓[LX] ⊧ succGeneralStatement :=
    consequence_iff_eq'.mp (Theory.Proof.sound concrete_succ_general) M
  have hBaseM : M↓[LX] ⊧ (formulaAt baseCode₁ a).univCl :=
    consequence_iff_eq'.mp (Theory.Proof.sound hBase) M
  have hAddM : M↓[LX] ⊧
      (addAt addCode₁ b a ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 0)).univCl :=
    consequence_iff_eq'.mp (Theory.Proof.sound hAdd) M
  have hTIM : M↓[LX] ⊧ closedTI₁ φ a :=
    consequence_iff_eq'.mp (Theory.Proof.sound hTI) M
  have hS' := models_succGeneralStatement.mp hS
  rw [models_iff] at hBaseM hAddM hTIM ⊢
  simp only [closedTI₁, Semiformula.eval_univCl, eval_tiUptoAt] at hTIM ⊢
  simp only [Semiformula.eval_univCl, eval_formulaAt, eval_addAt] at hBaseM hAddM
  intro f hProg y hy
  rcases hS' f (a.val ![] f) (b.val ![] f) y (hBaseM f) (hAddM f) hy with hlt | heq
  · exact hTIM f hProg y hlt
  · rw [heq]
    exact hProg _ (hTIM f hProg)

end OrdinalAnalysis.Gentzen.VeblenSuccStep
