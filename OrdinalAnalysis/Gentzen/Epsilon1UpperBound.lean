/-
  The upper bound `|PA + TI(ε₀)| ≤ ε₁` (Avigad 2002, Thm 9.8): for every Veblen notation
  `a` below `ε₁` and every formula `φ`, `PA[X] + TI(≺₁ ↾ ε₀)` proves transfinite induction
  for `φ` along the coded Veblen ordering below the code of `a`.

  The theory.  `paLX₁` is `paLX` together with the *scheme* `TI(≺₁ ↾ ε₀, φ)` for every
  formula `φ` of `LX`.  This is what Avigad's `PA + TI(≺α)` means, and it is forced: with
  the single instance for the fresh predicate `X` alone the statement below is false — read
  `X` as the whole model in a model of `PA` that refutes some arithmetic instance of
  `TI(≺ε₀)` (such models exist by Gentzen's lower bound); it satisfies `paLX + TI(≺ε₀, X)`
  and refutes that instance.  The single instance `TI₀` is of course a member of the scheme.

  The route.  From the scheme one gets `TI(φ, ε₀ + 1)` for every `φ` (the successor step
  is a two-case argument on the coded ordering, `lt_or_eq_of_lt_term_succ`), then Gentzen's
  jump `jumpB₁` climbs the tower `ε₀ + 1, ω^(ε₀+1), ω^ω^(ε₀+1), …` — each edge is certified
  by the ω-power graph, and none of these is an ε-number, so the graph is the plain
  `φ_0(·)` all the way up — and every notation below `ε₁` lies below some stage of that
  tower (`Ordinal.lt_nfp_iff` at `ε₁ = nfp (ω ^ ·) (ε₀ + 1)`).  Downward closure of
  transfinite induction along a transitive ordering finishes.
-/
import OrdinalAnalysis.Gentzen.CodedVeblenJump
import OrdinalAnalysis.Gentzen.OmegaTower
import OrdinalAnalysis.Gentzen.Order
import OrdinalAnalysis.Ordinal.Veblen.Epsilon

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OrdinalAnalysis.Gentzen.Epsilon1UpperBound

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
open OrdinalAnalysis.Gentzen.Order (precTransStatement models_precTransStatement)
open OrdinalAnalysis.Gamma0Note (epsilonNote)

/-! ## Terms, sentences, the theory -/

/-- The closed `PA[X]` numeral for an external Veblen normal form. -/
noncomputable def gamma0Term (a : Gamma0Note) : Semiterm LX ℕ 0 :=
  ((gamma0Code a : ℕ) : Semiterm LX ℕ 0)

/-- Universal closure of generic transfinite induction along `≺₁` below a closed term. -/
def closedTI₁ (φ : Semiformula LX ℕ 1) (a : Semiterm LX ℕ 0) : Sentence LX :=
  (tiUptoAt precCode₁ φ a).univCl

/-- Universal closure of a concrete `≺₁`-comparison. -/
def closedPrec₁ (a b : Semiterm LX ℕ 0) : Sentence LX :=
  (precAt precCode₁ a b).univCl

/-- Transfinite induction for the fresh predicate `X` along `≺₁` below the code of `ε₀`. -/
noncomputable def TI₀ : Sentence LX :=
  (TIupto precCode₁ (gamma0Term (epsilonNote 0))).univCl

/-- The scheme `TI(≺₁ ↾ ε₀, φ)`, `φ` any formula of `LX`. -/
def tiScheme₀ : Theory LX :=
  {σ | ∃ φ : Semiformula LX ℕ 1, σ = closedTI₁ φ (gamma0Term (epsilonNote 0))}

/-- **`PA[X] + TI(ε₀)`**: `PA[X]` with transfinite induction below `ε₀` for every formula. -/
def paLX₁ : Theory LX := paLX ∪ tiScheme₀

private lemma formulaAt_X_eq {n : ℕ} (x : Semiterm LX ℕ n) :
    formulaAt (Xat (#0 : Semiterm LX ℕ 1)) x = Xat x := by
  unfold formulaAt Xat
  change Semiformula.rel (Sum.inr XRel.X)
      ((Rew.subst ![x]) ∘ ![(#0 : Semiterm LX ℕ 1)]) =
    Semiformula.rel (Sum.inr XRel.X) ![x]
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp

/-- The generic induction formula specialised to `X` is the `TIupto` sentence of the
setup layer, for any coded ordering. -/
lemma tiUptoAt_X_eq' (prec : Semiformula LX ℕ 2) (t : Semiterm LX ℕ 0) :
    tiUptoAt prec (Xat (#0 : Semiterm LX ℕ 1)) t = TIupto prec t := by
  simp [tiUptoAt, TIupto, progAt, Prog, belowAt, below, formulaAt_X_eq]

/-- The single instance for `X` is one of the scheme's axioms. -/
theorem TI₀_mem_tiScheme₀ : TI₀ ∈ tiScheme₀ :=
  ⟨Xat (#0 : Semiterm LX ℕ 1), by
    simp only [TI₀, closedTI₁, tiUptoAt_X_eq']⟩

theorem TI₀_mem_paLX₁ : TI₀ ∈ paLX₁ := Or.inr TI₀_mem_tiScheme₀

theorem insert_TI₀_subset : insert TI₀ paLX ⊆ paLX₁ := by
  intro σ hσ
  rcases hσ with rfl | h
  · exact TI₀_mem_paLX₁
  · exact Or.inl h

instance paLX_weakerThan_paLX₁ : paLX ⪯ paLX₁ :=
  Entailment.WeakerThan.ofSubset Set.subset_union_left

instance paLX₁_eqTheory : 𝗘𝗤 LX ⪯ paLX₁ := by
  apply Entailment.WeakerThan.ofSubset
  intro σ hσ
  change σ ∈ (𝗘𝗤 LX ∪ (Theory.lMap toLX 𝗣𝗔⁻ ∪ InductionScheme LX Set.univ)) ∪ tiScheme₀
  exact Or.inl (Or.inl hσ)

/-- Everything `PA[X]` proves, `PA[X] + TI(ε₀)` proves. -/
theorem paLX₁_of_paLX {σ : Sentence LX} (h : paLX ⊢ σ) : paLX₁ ⊢ σ :=
  Entailment.WeakerThan.pbl h

/-- The scheme's instances, as derivations. -/
theorem paLX₁_ti_eps0 (φ : Semiformula LX ℕ 1) :
    paLX₁ ⊢ closedTI₁ φ (gamma0Term (epsilonNote 0)) := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  letI : M↓[LX] ⊧* paLX₁ := hM
  exact Theory.models (T := paLX₁) M (Or.inr ⟨φ, rfl⟩)

/-! ## Standard-code comparisons in `PA[X]` -/

private def arithPrecAt {n : ℕ}
    (a b : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![a, b] ▹ Rewriting.emb precDef₁.val

/-- Pure-arithmetic comparison of two fixed standard Veblen codes. -/
noncomputable def arithmeticGamma0PrecStatement (a b : Gamma0Note) :
    ArithmeticSentence :=
  (arithPrecAt
    ((gamma0Code a : ℕ) : Semiterm ℒₒᵣ ℕ 0)
    ((gamma0Code b : ℕ) : Semiterm ℒₒᵣ ℕ 0)).univCl

/-- Every true comparison of two Veblen normal forms is provable in `IΣ₁` after replacing
the notations by their standard codes. -/
theorem arithmetic_gamma0_prec {a b : Gamma0Note} (h : a < b) :
    𝗜𝚺₁ ⊢ arithmeticGamma0PrecStatement a b := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp [arithmeticGamma0PrecStatement, arithPrecAt, eval_precDef₁,
    Structure.numeral_eq_numeral, numeral_eq_natCast]
  change isNF₁ (gamma0ModelCode (V := M) a) ∧
    isNF₁ (gamma0ModelCode (V := M) b) ∧
      icmp₁ (gamma0ModelCode (V := M) a) (gamma0ModelCode (V := M) b) = 0
  exact ⟨isNF₁_gamma0ModelCode a, isNF₁_gamma0ModelCode b,
    (gamma0_lt_iff_icmp₁_eq_zero a b).mp h⟩

private lemma map_gamma0_prec_body (a b : Gamma0Note) :
    Semiformula.lMap toLX
        (arithPrecAt
          ((gamma0Code a : ℕ) : Semiterm ℒₒᵣ ℕ 0)
          ((gamma0Code b : ℕ) : Semiterm ℒₒᵣ ℕ 0)) =
      precAt precCode₁ (gamma0Term a) (gamma0Term b) := by
  simp [arithPrecAt, precAt, precCode₁, liftCode, gamma0Term,
    Semiformula.lMap_subst]
  rw [lMap_numeral (gamma0Code a), lMap_numeral (gamma0Code b)]

lemma models_gamma0_prec_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] (a b : Gamma0Note) :
    M↓[LX] ⊧ closedPrec₁ (gamma0Term a) (gamma0Term b) ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticGamma0PrecStatement a b := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [closedPrec₁, arithmeticGamma0PrecStatement,
    Semiformula.eval_univCl]
  constructor
  · intro h f
    apply Semiformula.eval_lMap.mp
    rw [map_gamma0_prec_body]
    exact h f
  · intro h f
    rw [← map_gamma0_prec_body]
    exact Semiformula.eval_lMap.mpr (h f)

/-- `PA[X]` proves every true comparison between two fixed standard Veblen codes. -/
theorem concrete_gamma0_prec {a b : Gamma0Note} (h : a < b) :
    paLX ⊢ closedPrec₁ (gamma0Term a) (gamma0Term b) := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl (arithmetic_gamma0_prec h))
  intro M _ _
  exact models_gamma0_prec_iff_arithmetic a b

/-! ## Transitivity of `≺₁` and downward closure -/

/-- Pure-arithmetic transitivity of the coded Veblen order. -/
def arithmeticPrecTransStatement : ArithmeticSentence :=
  (∀¹ ∀¹ ∀¹
    (∼(arithPrecAt (#2 : Semiterm ℒₒᵣ ℕ 3) #1) ⋎
      (∼(arithPrecAt #1 #0) ⋎ arithPrecAt #2 #0))).univCl

theorem arithmetic_precTrans : 𝗜𝚺₁ ⊢ arithmeticPrecTransStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simp [models_iff, arithmeticPrecTransStatement, arithPrecAt, eval_precDef₁]
  intro a b c
  by_cases hab : isNF₁ a ∧ isNF₁ b ∧ icmp₁ a b = 0
  · right
    by_cases hbc : isNF₁ b ∧ isNF₁ c ∧ icmp₁ b c = 0
    · right
      exact ⟨hab.1, hbc.2.1, icmp₁_trans hab.1 hab.2.1 hbc.2.1 hab.2.2 hbc.2.2⟩
    · left
      intro hb hc hcmp
      exact hbc ⟨hb, hc, hcmp⟩
  · left
    intro ha hb hcmp
    exact hab ⟨ha, hb, hcmp⟩

lemma models_precTrans_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ precTransStatement precCode₁ ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticPrecTransStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  simp [models_iff, precTransStatement, arithmeticPrecTransStatement,
    arithPrecAt, precAt, precCode₁, liftCode, Semiformula.eval_lMap]

/-- `PA[X]` proves transitivity of the coded Veblen order. -/
theorem concrete_precTrans₁ : paLX ⊢ precTransStatement precCode₁ := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_precTrans)
  intro M _ _
  exact models_precTrans_iff_arithmetic

/-- Transfinite induction along `≺₁` is downward closed, over `PA[X] + TI(ε₀)`. -/
theorem concrete_tiUpto_downward₁
    (φ : Semiformula LX ℕ 1) (a b : Semiterm LX ℕ 0)
    (hab : paLX ⊢ closedPrec₁ a b)
    (hTIb : paLX₁ ⊢ closedTI₁ φ b) :
    paLX₁ ⊢ closedTI₁ φ a := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  haveI : M↓[LX] ⊧* paLX := Semantics.ModelsSet.of_subset hM Set.subset_union_left
  have hTransM : M↓[LX] ⊧ precTransStatement precCode₁ :=
    consequence_iff_eq'.mp (Theory.Proof.sound concrete_precTrans₁) M
  have habM : M↓[LX] ⊧ closedPrec₁ a b :=
    consequence_iff_eq'.mp (Theory.Proof.sound hab) M
  have hTIbM : M↓[LX] ⊧ closedTI₁ φ b :=
    consequence_iff_eq'.mp (Theory.Proof.sound hTIb) M
  have hTrans := (models_precTransStatement precCode₁).mp hTransM
  rw [models_iff] at habM hTIbM ⊢
  simp only [closedPrec₁, closedTI₁, Semiformula.eval_univCl,
    eval_precAt, eval_tiUptoAt] at habM hTIbM ⊢
  intro f hProg y hya
  exact hTIbM f hProg y
    (hTrans f y (a.val ![] f) (b.val ![] f) hya (habM f))

/-! ## The successor step `ε₀ ↦ ε₀ + 1` -/

/-- The notation `ε₀ + 1 = φ_1(0) + 1`. -/
def eps0succ : Gamma0Note :=
  ⟨VNote.vadd 1 0 1 1, by
    refine VNote.NF.vadd VNote.nf_one VNote.NF.zero VNote.nf_one ?_ ?_
    · rw [VNote.repr_zero]
      exact Ordinal.veblen_pos
    · rw [VNote.repr_one, VNote.repr_zero]
      exact_mod_cast Ordinal.natCast_lt_epsilon 1 0⟩

lemma epsilonNote_zero_val : (epsilonNote 0).1 = VNote.vadd 1 0 1 0 := rfl

lemma eps0succ_val : eps0succ.1 = VNote.vadd 1 0 1 1 := rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma vmodelCode_one : vmodelCode (V := V) (1 : VNote) = vcVadd 0 0 1 0 := by
  rw [VNote.one_def, vmodelCode_vadd, vmodelCode_zero]
  simp

lemma modelCode_eps0 :
    gamma0ModelCode (V := V) (epsilonNote 0) = vcVadd (vcVadd 0 0 1 0) 0 1 0 := by
  rw [gamma0ModelCode_eq, epsilonNote_zero_val, vmodelCode_vadd, vmodelCode_zero, vmodelCode_one]
  simp

lemma modelCode_eps0succ :
    gamma0ModelCode (V := V) eps0succ = vcVadd (vcVadd 0 0 1 0) 0 1 (vcVadd 0 0 1 0) := by
  rw [gamma0ModelCode_eq, eps0succ_val, vmodelCode_vadd, vmodelCode_zero, vmodelCode_one]
  simp

/-- Pure-arithmetic: below the code of `ε₀ + 1` a code is below the code of `ε₀` or equal
to it. -/
noncomputable def arithmeticSuccStatement : ArithmeticSentence :=
  (∀¹ (∼(arithPrecAt (#0 : Semiterm ℒₒᵣ ℕ 1)
        ((gamma0Code eps0succ : ℕ) : Semiterm ℒₒᵣ ℕ 1)) ⋎
      (arithPrecAt (#0 : Semiterm ℒₒᵣ ℕ 1)
        ((gamma0Code (epsilonNote 0) : ℕ) : Semiterm ℒₒᵣ ℕ 1) ⋎
        (“#0 = !!((gamma0Code (epsilonNote 0) : ℕ) : Semiterm ℒₒᵣ ℕ 1)” :
          Semiformula ℒₒᵣ ℕ 1)))).univCl

theorem arithmetic_succ : 𝗜𝚺₁ ⊢ arithmeticSuccStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp [arithmeticSuccStatement, arithPrecAt, eval_precDef₁,
    Structure.numeral_eq_numeral, numeral_eq_natCast]
  intro y
  change (isNF₁ y → isNF₁ (gamma0ModelCode (V := M) eps0succ) →
      ¬ icmp₁ y (gamma0ModelCode (V := M) eps0succ) = 0) ∨
    ((isNF₁ y ∧ isNF₁ (gamma0ModelCode (V := M) (epsilonNote 0)) ∧
      icmp₁ y (gamma0ModelCode (V := M) (epsilonNote 0)) = 0) ∨
    y = gamma0ModelCode (V := M) (epsilonNote 0))
  by_cases hlt : isNF₁ y ∧ isNF₁ (gamma0ModelCode (V := M) eps0succ) ∧
      icmp₁ y (gamma0ModelCode (V := M) eps0succ) = 0
  · right
    obtain ⟨hy, -, hlt⟩ := hlt
    have hE : isNF₁ (gamma0ModelCode (V := M) (epsilonNote 0)) :=
      isNF₁_gamma0ModelCode (epsilonNote 0)
    rw [modelCode_eps0succ] at hlt
    rw [modelCode_eps0] at hE ⊢
    rcases lt_or_eq_of_lt_term_succ hy hE hlt with h | h
    · exact Or.inl ⟨hy, hE, h⟩
    · exact Or.inr h
  · left
    intro hy hE' h
    exact hlt ⟨hy, hE', h⟩

/-- The same statement in `LX`. -/
noncomputable def succStatement : Sentence LX :=
  (∀¹ (∼(precAt precCode₁ (#0 : Semiterm LX ℕ 1)
        ((gamma0Code eps0succ : ℕ) : Semiterm LX ℕ 1)) ⋎
      (precAt precCode₁ (#0 : Semiterm LX ℕ 1)
        ((gamma0Code (epsilonNote 0) : ℕ) : Semiterm LX ℕ 1) ⋎
        (“#0 = !!((gamma0Code (epsilonNote 0) : ℕ) : Semiterm LX ℕ 1)” :
          Semiformula LX ℕ 1)))).univCl

private lemma map_succ_body :
    Semiformula.lMap toLX
        (∀¹ (∼(arithPrecAt (#0 : Semiterm ℒₒᵣ ℕ 1)
            ((gamma0Code eps0succ : ℕ) : Semiterm ℒₒᵣ ℕ 1)) ⋎
          (arithPrecAt (#0 : Semiterm ℒₒᵣ ℕ 1)
            ((gamma0Code (epsilonNote 0) : ℕ) : Semiterm ℒₒᵣ ℕ 1) ⋎
            (“#0 = !!((gamma0Code (epsilonNote 0) : ℕ) : Semiterm ℒₒᵣ ℕ 1)” :
              Semiformula ℒₒᵣ ℕ 1)))) =
      (∀¹ (∼(precAt precCode₁ (#0 : Semiterm LX ℕ 1)
            ((gamma0Code eps0succ : ℕ) : Semiterm LX ℕ 1)) ⋎
          (precAt precCode₁ (#0 : Semiterm LX ℕ 1)
            ((gamma0Code (epsilonNote 0) : ℕ) : Semiterm LX ℕ 1) ⋎
            (“#0 = !!((gamma0Code (epsilonNote 0) : ℕ) : Semiterm LX ℕ 1)” :
              Semiformula LX ℕ 1)))) := by
  simp [arithPrecAt, precAt, precCode₁, liftCode, Semiformula.lMap_subst]
  refine ⟨?_, ?_, ?_⟩
  · rw [lMap_numeral]
  · rw [lMap_numeral]
  · simp [Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq, toLX]
    apply funext
    rw [Fin.forall_fin_two]
    constructor
    · simp [Function.comp_def]
    · simp [Function.comp_def]
      exact lMap_numeral _

lemma models_succ_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ succStatement ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticSuccStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [succStatement, arithmeticSuccStatement, Semiformula.eval_univCl]
  rw [← map_succ_body]
  simp [Semiformula.eval_lMap]

theorem concrete_succ : paLX ⊢ succStatement := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_succ)
  intro M _ _
  exact models_succ_iff_arithmetic

/-- **The successor step.**  Transfinite induction below `ε₀` for `φ` gives it below
`ε₀ + 1`. -/
theorem closedTI₁_succ (φ : Semiformula LX ℕ 1)
    (h : paLX₁ ⊢ closedTI₁ φ (gamma0Term (epsilonNote 0))) :
    paLX₁ ⊢ closedTI₁ φ (gamma0Term eps0succ) := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  haveI : M↓[LX] ⊧* paLX := Semantics.ModelsSet.of_subset hM Set.subset_union_left
  have hTI : M↓[LX] ⊧ closedTI₁ φ (gamma0Term (epsilonNote 0)) :=
    consequence_iff_eq'.mp (Theory.Proof.sound h) M
  have hS : M↓[LX] ⊧ succStatement :=
    consequence_iff_eq'.mp (Theory.Proof.sound concrete_succ) M
  rw [models_iff] at hTI hS ⊢
  simp only [closedTI₁, Semiformula.eval_univCl, eval_tiUptoAt] at hTI ⊢
  simp only [succStatement, Semiformula.eval_univCl, Semiformula.eval_all,
    LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, eval_precAt] at hS
  intro f hProg y hy
  have hS' := hS f y
  simp only [gamma0Term] at hy hTI ⊢
  simp at hS' hy hTI ⊢
  rcases hS' with hne | hlt | heq
  · exact (hne hy).elim
  · exact hTI f hProg y hlt
  · rw [heq]
    exact hProg _ (hTI f hProg)

/-- The scheme lifted to `ε₀ + 1`, for every formula. -/
theorem paLX₁_ti_eps0succ (φ : Semiformula LX ℕ 1) :
    paLX₁ ⊢ closedTI₁ φ (gamma0Term eps0succ) :=
  closedTI₁_succ φ (paLX₁_ti_eps0 φ)

/-! ## The tower over `ε₀ + 1` -/

/-- `ε₀ + 1, ω ^ (ε₀ + 1), ω ^ ω ^ (ε₀ + 1), …` -/
def etower : ℕ → Gamma0Note
  | 0 => eps0succ
  | n + 1 => Gamma0Note.omegaPow (etower n)

@[simp] lemma etower_zero : etower 0 = eps0succ := rfl

lemma etower_succ (n : ℕ) : etower (n + 1) = Gamma0Note.omegaPow (etower n) := rfl

/-- `φ_0(b) = ω ^ b` is the plain term `vadd 0 b 1 0` whenever `b` is not an ε-number
in the syntactic sense. -/
lemma VNote_veblenNote_zero_of {b₁ b₂ : VNote} {m : ℕ+} {c : VNote}
    (h : b₁ = 0 ∨ c ≠ 0) :
    VNote.veblenNote 0 (VNote.vadd b₁ b₂ m c) = VNote.vadd 0 (VNote.vadd b₁ b₂ m c) 1 0 := by
  rw [VNote.veblenNote]
  rw [if_neg]
  rintro ⟨-, hc, hcmp⟩
  rcases h with rfl | hc'
  · rw [VNote.cmp_zero_zero] at hcmp
    exact absurd hcmp (by decide)
  · exact hc' hc

/-- Every stage of the tower is the plain ω-power term of the previous one. -/
lemma etower_succ_val : ∀ n : ℕ, (etower (n + 1)).1 = VNote.vadd 0 (etower n).1 1 0
  | 0 => by
      rw [etower_succ, etower_zero]
      show VNote.veblenNote 0 (VNote.vadd 1 0 1 1) = VNote.vadd 0 (VNote.vadd 1 0 1 1) 1 0
      exact VNote_veblenNote_zero_of (Or.inr (by decide))
  | n + 1 => by
      rw [etower_succ (n + 1)]
      show VNote.veblenNote 0 (etower (n + 1)).1 = VNote.vadd 0 (etower (n + 1)).1 1 0
      rw [etower_succ_val n]
      exact VNote_veblenNote_zero_of (Or.inl rfl)

lemma modelCode_etower_succ (n : ℕ) :
    gamma0ModelCode (V := V) (etower (n + 1)) =
      vcVadd 0 (gamma0ModelCode (V := V) (etower n)) 1 0 := by
  rw [gamma0ModelCode_eq, gamma0ModelCode_eq, etower_succ_val, vmodelCode_vadd, vmodelCode_zero]
  simp

/-- No stage of the tower is fixed-point-shaped. -/
lemma fixIndic_etower_ne_one (n : ℕ) :
    fixIndic (gamma0ModelCode (V := V) (etower n)) ≠ 1 := by
  cases n with
  | zero =>
      rw [etower_zero, modelCode_eps0succ, Ne, fixIndic_vcVadd]
      rintro ⟨-, h, -⟩
      exact vcVadd_ne_zero _ _ _ _ h
  | succ n =>
      rw [modelCode_etower_succ, Ne, fixIndic_vcVadd]
      rintro ⟨-, -, h⟩
      exact h rfl

/-- The ω-power graph certifies every tower edge. -/
lemma iomegaPow_etower (n : ℕ) :
    iomegaPow (gamma0ModelCode (V := V) (etower n)) = gamma0ModelCode (V := V) (etower (n + 1)) := by
  rw [iomegaPow_of_not_fix (fixIndic_etower_ne_one n), modelCode_etower_succ]

private def arithOmegaPowAt {n : ℕ}
    (z a : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, a] ▹ Rewriting.emb omegaPowDef₁.val

noncomputable def arithmeticTowerOmegaPowStatement (n : ℕ) : Sentence ℒₒᵣ :=
  (arithOmegaPowAt
    ((gamma0Code (etower (n + 1)) : ℕ) : Semiterm ℒₒᵣ ℕ 0)
    ((gamma0Code (etower n) : ℕ) : Semiterm ℒₒᵣ ℕ 0)).univCl

theorem arithmetic_tower_omegaPow (n : ℕ) :
    𝗜𝚺₁ ⊢ arithmeticTowerOmegaPowStatement n := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp [arithmeticTowerOmegaPowStatement, arithOmegaPowAt,
    eval_omegaPowDef₁, Structure.numeral_eq_numeral, numeral_eq_natCast]
  change isNF₁ (gamma0ModelCode (V := M) (etower n)) ∧
    gamma0ModelCode (V := M) (etower (n + 1)) = iomegaPow (gamma0ModelCode (V := M) (etower n))
  exact ⟨isNF₁_gamma0ModelCode _, (iomegaPow_etower n).symm⟩

private lemma map_tower_omegaPow_body (n : ℕ) :
    Semiformula.lMap toLX
        (arithOmegaPowAt
          ((gamma0Code (etower (n + 1)) : ℕ) : Semiterm ℒₒᵣ ℕ 0)
          ((gamma0Code (etower n) : ℕ) : Semiterm ℒₒᵣ ℕ 0)) =
      omegaPowAt omegaPowCode₁ (gamma0Term (etower (n + 1))) (gamma0Term (etower n)) := by
  simp [arithOmegaPowAt, omegaPowAt, omegaPowCode₁, liftCode,
    gamma0Term, Semiformula.lMap_subst]
  rw [lMap_numeral (gamma0Code (etower (n + 1))), lMap_numeral (gamma0Code (etower n))]

lemma models_tower_omegaPow_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] (n : ℕ) :
    M↓[LX] ⊧ (omegaPowAt omegaPowCode₁ (gamma0Term (etower (n + 1)))
      (gamma0Term (etower n))).univCl ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticTowerOmegaPowStatement n := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [arithmeticTowerOmegaPowStatement,
    Semiformula.eval_univCl]
  constructor
  · intro h f
    apply Semiformula.eval_lMap.mp
    rw [map_tower_omegaPow_body]
    exact h f
  · intro h f
    rw [← map_tower_omegaPow_body]
    exact Semiformula.eval_lMap.mpr (h f)

/-- `PA[X]` proves every tower edge of the ω-power graph. -/
theorem concrete_tower_omegaPow (n : ℕ) :
    paLX ⊢ (omegaPowAt omegaPowCode₁ (gamma0Term (etower (n + 1)))
      (gamma0Term (etower n))).univCl := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl (arithmetic_tower_omegaPow n))
  intro M _ _
  exact models_tower_omegaPow_iff_arithmetic n

/-- A certified ω-power edge lifts induction from its exponent to its value, over
`PA[X] + TI(ε₀)`. -/
theorem concrete_ti_omegaPow₁
    (φ : Semiformula LX ℕ 1) (a u : Semiterm LX ℕ 0)
    (hPow : paLX ⊢ (omegaPowAt omegaPowCode₁ u a).univCl)
    (hTI : paLX₁ ⊢
      (tiUptoAt precCode₁ (jump precCode₁ addCode₁ omegaPowCode₁ φ) a).univCl) :
    paLX₁ ⊢ (tiUptoAt precCode₁ φ u).univCl := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  haveI : M↓[LX] ⊧* paLX := Semantics.ModelsSet.of_subset hM Set.subset_union_left
  have hB : M↓[LX] ⊧
      jumpBStatement precCode₁ addCode₁ omegaPowCode₁ φ :=
    consequence_iff_eq'.mp (Theory.Proof.sound (jumpB₁ φ)) M
  have hPowM : M↓[LX] ⊧ (omegaPowAt omegaPowCode₁ u a).univCl :=
    consequence_iff_eq'.mp (Theory.Proof.sound hPow) M
  have hTIM : M↓[LX] ⊧
      (tiUptoAt precCode₁ (jump precCode₁ addCode₁ omegaPowCode₁ φ) a).univCl :=
    consequence_iff_eq'.mp (Theory.Proof.sound hTI) M
  rw [models_iff] at hB hPowM hTIM ⊢
  simp only [jumpBStatement, Semiformula.eval_univCl,
    Semiformula.eval_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq, eval_omegaPowAt, eval_tiUptoAt] at hB
  simp only [Semiformula.eval_univCl] at hPowM hTIM ⊢
  intro f
  have hp := eval_omegaPowAt omegaPowCode₁ u a ![] f |>.mp (hPowM f)
  have ht := eval_tiUptoAt precCode₁
    (jump precCode₁ addCode₁ omegaPowCode₁ φ) a ![] f |>.mp (hTIM f)
  have h := hB f (a.val ![] f) (u.val ![] f)
  rcases h with hnp | hnt | hgoal
  · exact (hnp hp).elim
  · exact (hnt ht).elim
  · exact (eval_tiUptoAt precCode₁ φ u ![] f).mpr hgoal

/-- One derivation in `PA[X] + TI(ε₀)` for each stage of the tower, for every formula. -/
theorem concrete_etower_ti (n : ℕ) (φ : Semiformula LX ℕ 1) :
    paLX₁ ⊢ closedTI₁ φ (gamma0Term (etower n)) := by
  induction n generalizing φ with
  | zero => exact paLX₁_ti_eps0succ φ
  | succ n ih =>
      exact concrete_ti_omegaPow₁ φ (gamma0Term (etower n)) (gamma0Term (etower (n + 1)))
        (concrete_tower_omegaPow n)
        (ih (jump precCode₁ addCode₁ omegaPowCode₁ φ))

/-! ## Cofinality of the tower below `ε₁` -/

open Ordinal in
lemma repr_etower : ∀ n : ℕ,
    Gamma0Note.repr (etower n) = (fun x : Ordinal => ω ^ x)^[n] (Order.succ (ε_ 0))
  | 0 => by
      rw [etower_zero, Function.iterate_zero, id]
      show VNote.repr (VNote.vadd 1 0 1 1) = _
      rw [VNote.repr_vadd, VNote.repr_one, VNote.repr_zero, Order.succ_eq_add_one]
      simp
  | n + 1 => by
      rw [etower_succ, Gamma0Note.repr_omegaPow, repr_etower n, Function.iterate_succ_apply']

open Ordinal in
/-- Every Veblen notation below `ε₁` lies below some stage of the tower. -/
theorem exists_lt_etower (a : Gamma0Note) (ha : a < epsilonNote 1) :
    ∃ n : ℕ, a < etower n := by
  have h1 : (1 : Ordinal) = Order.succ 0 := by rw [Order.succ_eq_add_one, zero_add]
  have ha' : Gamma0Note.repr a < ε_ (Order.succ 0) := by
    have := ha
    rw [Gamma0Note.lt_def, Gamma0Note.repr_epsilonNote, Gamma0Note.repr_one] at this
    rw [← h1]
    exact this
  rw [Ordinal.epsilon_succ_eq_nfp, Ordinal.lt_nfp_iff] at ha'
  obtain ⟨n, hn⟩ := ha'
  refine ⟨n, ?_⟩
  rw [Gamma0Note.lt_def, repr_etower]
  exact hn

/-! ## The upper bound -/

/-- **The ε₁ upper bound.**  For every formula `φ` and every Veblen notation `a < ε₁`,
`PA[X] + TI(ε₀)` proves transfinite induction for `φ` along `≺₁` below the code of `a`. -/
theorem epsilon1_upper_bound (φ : Semiformula LX ℕ 1) (a : Gamma0Note)
    (ha : a < epsilonNote 1) :
    paLX₁ ⊢ closedTI₁ φ (gamma0Term a) := by
  obtain ⟨n, han⟩ := exists_lt_etower a ha
  exact concrete_tiUpto_downward₁ φ (gamma0Term a) (gamma0Term (etower n))
    (concrete_gamma0_prec han) (concrete_etower_ti n φ)

/-- The concrete `X`-predicate form of the upper bound. -/
theorem epsilon1_upper_bound_TIupto (a : Gamma0Note) (ha : a < epsilonNote 1) :
    paLX₁ ⊢ (TIupto precCode₁ (gamma0Term a)).univCl := by
  rw [← tiUptoAt_X_eq']
  exact epsilon1_upper_bound (Xat (#0 : Semiterm LX ℕ 1)) a ha

end OrdinalAnalysis.Gentzen.Epsilon1UpperBound
