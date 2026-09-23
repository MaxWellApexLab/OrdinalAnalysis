/-
  The internal finite ω-tower over a *variable* base, on the Veblen codes.

  `Epsilon1UpperBound.etower` and `VeblenEpsilon0UpperBound.vtower` are external towers:
  one closed numeral per stage, one `PA[X]` derivation per stage.  The ACA upper bound needs
  the tower *inside* arithmetic, as a single ternary graph `Tower(u, n, c)` saying "`u` is the
  `n`-th ω-tower stage over the base `c`", so that the tower induction

      `ACA ⊢ ∀c ∀n ∀u (Tower(u,n,c) → (∀²X TI(c,X)) → (∀²X TI(u,X)))`

  can be run as a single application of the second-order induction scheme on `n`.

  The construction is `CodedNotation.iterBlueprint` with `iadd` replaced by
  `InternalVNoteJump.iomegaPow`.  The two laws exported to the ACA layer are exactly the ones
  that induction consumes: a zero-step tower is its base, and a successor-step tower factors
  through an ω-power edge, which is what `CodedVeblenJump.jumpB₁` climbs.
-/
import OrdinalAnalysis.Gentzen.VeblenEpsilon0UpperBound

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OrdinalAnalysis.Gentzen.VeblenTower

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.InternalVNote
open OrdinalAnalysis.Gentzen.InternalVNoteOrder
open OrdinalAnalysis.Gentzen.InternalVNoteJump
open OrdinalAnalysis.Gentzen.CodedNotation (liftCode paLX_of_peano_semantic)
open OrdinalAnalysis.Gentzen.CodedVeblen
open OrdinalAnalysis.Gentzen.CodedVeblenJump

/-! ## The primitive-recursive tower -/

/-- `Tower(c, 0) = c`, `Tower(c, n+1) = ω ^ Tower(c, n)`: `iterBlueprint` with `iadd`
replaced by `iomegaPow`. -/
def towerBlueprint : PR.Blueprint 1 where
  zero := .mkSigma “y c. y = c”
  succ := .mkSigma “y ih k c. !iomegaPowDef y ih”

noncomputable def towerConstruction {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : PR.Construction V towerBlueprint where
  zero := fun v ↦ v 0
  succ := fun _ _ ih ↦ iomegaPow ih
  zero_defined := .mk fun v ↦ by simp [towerBlueprint]
  succ_defined := .mk fun v ↦ by
    simp [towerBlueprint, iomegaPow_defined.iff]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The internal ω-tower**: `itower c n = ω ^ ω ^ … ^ c` with `n` exponentiations. -/
noncomputable def itower (c n : V) : V := towerConstruction.result ![c] n

@[simp] lemma itower_zero (c : V) : itower c 0 = c := by
  simp [itower, towerConstruction]

@[simp] lemma itower_succ (c n : V) :
    itower c (n + 1) = iomegaPow (itower c n) := by
  simp [itower, towerConstruction]

/-- Result-first graph of the internal tower, argument order `(y, c, n)`. -/
def _root_.LO.FirstOrder.Arithmetic.itowerDef : 𝚺₁.Semisentence 3 :=
  towerBlueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance itower_defined : 𝚺₁-Function₂ (itower : V → V → V) via itowerDef := .mk
  fun v ↦ by simp [towerConstruction.result_defined_iff, itowerDef]; rfl

instance itower_definable : 𝚺₁-Function₂ (itower : V → V → V) :=
  itower_defined.to_definable

instance itower_definable' (Γ) (m : ℕ) :
    Γ-[m + 1]-Function₂ (itower : V → V → V) :=
  itower_definable.of_sigmaOne

/-- The tower stays inside the normal forms. -/
lemma isNF₁_itower {c : V} (hc : isNF₁ c) : ∀ n : V, isNF₁ (itower c n) := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using hc
  case succ n ih =>
      rw [itower_succ]
      exact isNF₁_iomegaPow ih

/-! ## The graph formula `Tower(u, n, c)` -/

/-- `Tower(u, n, c)`: `c` is a normal code and `u` is the `n`-th ω-tower stage over it. -/
def towerDef₁ : 𝚺₁.Semisentence 3 := .mkSigma
  “u k c. !isNFb₁Def 1 c ∧ !itowerDef u c k”

@[simp] theorem eval_towerDef₁ (u k c : V) :
    towerDef₁.val.Evalb ![u, k, c] ↔ isNF₁ c ∧ u = itower c k := by
  simp [towerDef₁, isNF₁, isNFb₁_defined.iff, itower_defined.iff, eq_comm]

/-- The tower graph in `LX`. -/
def towerCode₁ : Semiformula LX ℕ 3 := liftCode towerDef₁

/-! ## Generic object-language shape of a tower graph -/

/-- Apply a result-first three-place tower graph: `Tower(u, k, c)`. -/
def towerAt (towerCode : Semiformula LX ℕ 3) {n : ℕ}
    (u k c : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  Rew.subst ![u, k, c] ▹ towerCode

@[simp] theorem eval_towerAt {M : Type*} [Structure LX M]
    (towerCode : Semiformula LX ℕ 3) {n : ℕ}
    (u k c : Semiterm LX ℕ n) (e : Fin n → M) (f : ℕ → M) :
    (towerAt towerCode u k c).Eval e f ↔
      towerCode.Eval ![u.val e f, k.val e f, c.val e f] f := by
  simp [towerAt]

/-- A zero-step tower is its own base. -/
def towerZeroStatement (towerCode : Semiformula LX ℕ 3) : Sentence LX :=
  (∀¹ ∀¹
    (∼(towerAt towerCode #0 ((0 : ℕ) : Semiterm LX ℕ 2) #1) ⋎
      (“#0 = #1” : Semiformula LX ℕ 2))).univCl

/-- A successor-step tower factors through an ω-power edge. -/
def towerSuccStatement (omegaPowCode : Semiformula LX ℕ 2)
    (towerCode : Semiformula LX ℕ 3) : Sentence LX :=
  (∀¹ ∀¹ ∀¹
    (∼(towerAt towerCode #0 (‘(#1 + 1)’ : Semiterm LX ℕ 3) #2) ⋎
      (∃¹ (towerAt towerCode #0 #2 #3 ⋏
        omegaPowAt omegaPowCode #1 #0)))).univCl

/-! ### Semantic forms, for the second-order layer -/

theorem models_towerZeroStatement {M : Type*} [Nonempty M] [Structure LX M]
    [Structure.Eq LX M] (towerCode : Semiformula LX ℕ 3) :
    M↓[LX] ⊧ towerZeroStatement towerCode ↔
      ∀ f : ℕ → M, ∀ c u : M,
        towerCode.Eval
          ![u, ((0 : ℕ) : Semiterm LX ℕ 0).val ![] f, c] f →
        u = c := by
  classical
  simp [models_iff, towerZeroStatement]
  constructor
  · intro h f c u hiter
    rcases h f c u with hnot | hu
    · exact (hnot (by simpa using hiter)).elim
    · exact hu
  · intro h f c u
    by_cases hiter :
        towerCode.Eval ![u, ((0 : ℕ) : Semiterm LX ℕ 0).val ![] f, c] f
    · exact Or.inr (h f c u (by simpa using hiter))
    · exact Or.inl (by simpa using hiter)

theorem models_towerSuccStatement {M : Type*} [Nonempty M] [Structure LX M]
    (omegaPowCode : Semiformula LX ℕ 2) (towerCode : Semiformula LX ℕ 3) :
    M↓[LX] ⊧ towerSuccStatement omegaPowCode towerCode ↔
      ∀ f : ℕ → M, ∀ c k u : M,
        towerCode.Eval
          ![u, (‘(#0 + 1)’ : Semiterm LX ℕ 1).val ![k] f, c] f →
        ∃ v : M,
          towerCode.Eval ![v, k, c] f ∧
          omegaPowCode.Eval ![u, v] f := by
  classical
  simp [models_iff, towerSuccStatement]
  constructor
  · intro h f c k u hiter
    rcases h f c k u with hnot | hv
    · exact (hnot (by simpa using hiter)).elim
    · exact hv
  · intro h f c k u
    by_cases hiter :
        towerCode.Eval ![u, (‘(#0 + 1)’ : Semiterm LX ℕ 1).val ![k] f, c] f
    · exact Or.inr (h f c k u (by simpa using hiter))
    · exact Or.inl (by simpa using hiter)

/-! ## The pure-arithmetic statements -/

private def arithTowerAt {n : ℕ}
    (u k c : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![u, k, c] ▹ Rewriting.emb towerDef₁.val

private def arithOmegaPowAt {n : ℕ}
    (z a : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, a] ▹ Rewriting.emb omegaPowDef₁.val

def arithmeticTowerZeroStatement : Sentence ℒₒᵣ :=
  (∀¹ ∀¹
    (∼(arithTowerAt #0 ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 2) #1) ⋎
      (“#0 = #1” : Semiformula ℒₒᵣ ℕ 2))).univCl

def arithmeticTowerSuccStatement : Sentence ℒₒᵣ :=
  (∀¹ ∀¹ ∀¹
    (∼(arithTowerAt #0 (‘(#1 + 1)’ : Semiterm ℒₒᵣ ℕ 3) #2) ⋎
      (∃¹ (arithTowerAt #0 #2 #3 ⋏ arithOmegaPowAt #1 #0)))).univCl

theorem arithmetic_towerZero : 𝗜𝚺₁ ⊢ arithmeticTowerZeroStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simp [models_iff, arithmeticTowerZeroStatement, arithTowerAt, eval_towerDef₁]
  intro c u
  tauto

theorem arithmetic_towerSucc : 𝗜𝚺₁ ⊢ arithmeticTowerSuccStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simp [models_iff, arithmeticTowerSuccStatement, arithTowerAt, arithOmegaPowAt,
    eval_towerDef₁, eval_omegaPowDef₁]
  intro c k u
  have key : isNF₁ c → u = iomegaPow (itower c k) →
      isNF₁ c ∧ isNF₁ (itower c k) ∧ u = iomegaPow (itower c k) :=
    fun hc hu ↦ ⟨hc, isNF₁_itower hc k, hu⟩
  tauto

/-! ## Transport to `PA[X]` -/

private lemma lMap_zero {n : ℕ} :
    Semiterm.lMap toLX ((0 : ℕ) : ArithmeticSemiterm ℕ n) =
      ((0 : ℕ) : Semiterm LX ℕ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, toLX]

private lemma lMap_succ_three :
    Semiterm.lMap toLX (‘(#1 + 1)’ : ArithmeticSemiterm ℕ 3) =
      (‘(#1 + 1)’ : Semiterm LX ℕ 3) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, Semiterm.Operator.Add.term_eq, toLX]
  apply funext
  rw [Fin.forall_fin_two]
  constructor
  · simp [Function.comp_def]
  · simp [Function.comp_def]
    exact Matrix.empty_eq _

private lemma map_towerZero_body :
    Semiformula.lMap toLX
        (∀¹ ∀¹
          (∼(arithTowerAt #0 ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 2) #1) ⋎
            (“#0 = #1” : Semiformula ℒₒᵣ ℕ 2))) =
      (∀¹ ∀¹
        (∼(towerAt towerCode₁ #0 ((0 : ℕ) : Semiterm LX ℕ 2) #1) ⋎
          (“#0 = #1” : Semiformula LX ℕ 2))) := by
  simp [arithTowerAt, towerAt, towerCode₁, liftCode, Semiformula.lMap_subst]
  constructor
  · rw [lMap_zero]
  · simp [Semiformula.Operator.operator,
      Semiformula.Operator.Eq.sentence_eq, toLX]
    apply funext
    rw [Fin.forall_fin_two]
    exact ⟨rfl, rfl⟩

private lemma map_towerSucc_body :
    Semiformula.lMap toLX
        (∀¹ ∀¹ ∀¹
          (∼(arithTowerAt #0 (‘(#1 + 1)’ : Semiterm ℒₒᵣ ℕ 3) #2) ⋎
            (∃¹ (arithTowerAt #0 #2 #3 ⋏ arithOmegaPowAt #1 #0)))) =
      (∀¹ ∀¹ ∀¹
        (∼(towerAt towerCode₁ #0 (‘(#1 + 1)’ : Semiterm LX ℕ 3) #2) ⋎
          (∃¹ (towerAt towerCode₁ #0 #2 #3 ⋏
            omegaPowAt omegaPowCode₁ #1 #0)))) := by
  simp [arithTowerAt, arithOmegaPowAt, towerAt, omegaPowAt, towerCode₁,
    omegaPowCode₁, liftCode, Semiformula.lMap_subst]
  rw [lMap_succ_three]

lemma models_towerZero_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ towerZeroStatement towerCode₁ ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticTowerZeroStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [towerZeroStatement, arithmeticTowerZeroStatement,
    Semiformula.eval_univCl]
  rw [← map_towerZero_body]
  simp [Semiformula.eval_lMap]

lemma models_towerSucc_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ towerSuccStatement omegaPowCode₁ towerCode₁ ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticTowerSuccStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [towerSuccStatement, arithmeticTowerSuccStatement,
    Semiformula.eval_univCl]
  rw [← map_towerSucc_body]
  simp [Semiformula.eval_lMap]

/-- **The zero step of the internal tower, in `PA[X]`.** -/
theorem concrete_towerZero : paLX ⊢ towerZeroStatement towerCode₁ := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_towerZero)
  intro M _ _
  exact models_towerZero_iff_arithmetic

/-- **The successor step of the internal tower, in `PA[X]`.** -/
theorem concrete_towerSucc :
    paLX ⊢ towerSuccStatement omegaPowCode₁ towerCode₁ := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_towerSucc)
  intro M _ _
  exact models_towerSucc_iff_arithmetic

end OrdinalAnalysis.Gentzen.VeblenTower
