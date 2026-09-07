/-
  X-free arithmetic graph formulas for the coded ordinal operations used by
  Gentzen's jump.  Every formula is first defined in the pure arithmetic
  language and only then transported to LX, so the fresh predicate cannot
  occur in the notation layer.
-/
import OrdinalAnalysis.Gentzen.InternalONote
import OrdinalAnalysis.Gentzen.JumpProgressive

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.CodedNotation

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote

def nfDef : 𝚺₁.Semisentence 1 := .mkSigma
  “x. !isNFbDef 1 x”

def precDef : 𝚺₁.Semisentence 2 := .mkSigma
  “x y. !isNFbDef 1 x ∧ !isNFbDef 1 y ∧ !icmpDef 0 x y”

def addDef : 𝚺₁.Semisentence 3 := .mkSigma
  “z x y. !isNFbDef 1 x ∧ !iaddDef z x y”

def omegaPowDef : 𝚺₁.Semisentence 2 := .mkSigma
  “z a. !isNFbDef 1 a ∧ !ocOaddDef z a 1 0”

def iterBlueprint : PR.Blueprint 2 where
  zero := .mkSigma “y b w. y = b”
  succ := .mkSigma “y ih k b w. !iaddDef y ih w”

noncomputable def iterConstruction {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : PR.Construction V iterBlueprint where
  zero := fun v ↦ v 0
  succ := fun v _ ih ↦ iadd ih (v 1)
  zero_defined := .mk fun v ↦ by simp [iterBlueprint]
  succ_defined := .mk fun v ↦ by
    simp [iterBlueprint, iadd_defined.iff]

def rawIterDef : 𝚺₁.Semisentence 4 :=
  iterBlueprint.resultDef.rew (Rew.subst ![#0, #3, #1, #2])

def iterDef : 𝚺₁.Semisentence 4 := .mkSigma
  “z b w k. !isNFbDef 1 b ∧ !isNFbDef 1 w ∧ !rawIterDef z b w k”

def liftCode {n : ℕ} (σ : ArithmeticSemisentence n) :
    Semiformula LX ℕ n :=
  Semiformula.lMap toLX (Rewriting.emb σ)

def precCode : Semiformula LX ℕ 2 := liftCode precDef

def addCode : Semiformula LX ℕ 3 := liftCode addDef

def omegaPowCode : Semiformula LX ℕ 2 := liftCode omegaPowDef

def iterCode : Semiformula LX ℕ 4 := liftCode iterDef

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem eval_nfDef (x : V) :
    nfDef.val.Evalb ![x] ↔ isNF x := by
  simp [nfDef, isNF, isNFb_defined.iff, eq_comm]

@[simp] theorem eval_precDef (x y : V) :
    precDef.val.Evalb ![x, y] ↔ isNF x ∧ isNF y ∧ icmp x y = 0 := by
  simp [precDef, isNF, isNFb_defined.iff, icmp_defined.iff, eq_comm]

@[simp] theorem eval_addDef (z x y : V) :
    addDef.val.Evalb ![z, x, y] ↔ isNF x ∧ z = iadd x y := by
  simp [addDef, isNF, isNFb_defined.iff, iadd_defined.iff, eq_comm]

@[simp] theorem eval_omegaPowDef (z a : V) :
    omegaPowDef.val.Evalb ![z, a] ↔ isNF a ∧ z = ocOadd a 1 0 := by
  simp [omegaPowDef, isNF, isNFb_defined.iff, ocOadd_defined.iff, eq_comm]

@[simp] theorem eval_rawIterDef (z b w k : V) :
    rawIterDef.val.Evalb ![z, b, w, k] ↔
      z = (iterConstruction (V := V)).result ![b, w] k := by
  simp [rawIterDef, iterConstruction.result_defined_iff]

@[simp] theorem eval_iterDef (z b w k : V) :
    iterDef.val.Evalb ![z, b, w, k] ↔
      isNF b ∧ isNF w ∧
        z = (iterConstruction (V := V)).result ![b, w] k := by
  simp [iterDef, isNF, isNFb_defined.iff, eq_comm]

/-! ### Transport from arithmetic PA to PA[X] -/

private lemma lMap_zero {n : ℕ} :
    Semiterm.lMap toLX ((0 : ℕ) : ArithmeticSemiterm ℕ n) =
      ((0 : ℕ) : Semiterm LX ℕ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, toLX]

private lemma lMap_succ :
    Semiterm.lMap toLX (‘(#0 + 1)’ : ArithmeticSemiterm ℕ 1) =
      (‘(#0 + 1)’ : Semiterm LX ℕ 1) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, Semiterm.Operator.Add.term_eq, toLX]
  apply funext
  rw [Fin.forall_fin_two]
  constructor
  · simp [Function.comp_def]
  · simp [Function.comp_def]
    exact Matrix.empty_eq _

private lemma map_succInd (φ : ArithmeticSemiformula ℕ 1) :
    Semiformula.lMap toLX (succInd φ) =
      succInd (Semiformula.lMap toLX φ) := by
  simp [succInd, Semiformula.lMap_subst]
  exact ⟨by congr; exact lMap_zero, by congr; exact lMap_succ⟩

/-- Every PA[X] model has a PA model as its arithmetic reduct. -/
lemma paLX_models_peano_reduct {M : Type*} [Nonempty M]
    [sLX : Structure LX M] [M↓[LX] ⊧* paLX] :
    (sLX.lMap toLX).toStruc ⊧* 𝗣𝗔 := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  refine ⟨?_⟩
  intro σ hσ
  rcases hσ with hpa | hind
  · have hmap : M↓[LX] ⊧ Semiformula.lMap toLX σ :=
      Theory.models (T := paLX) M
        (Set.mem_union_right _ (Set.mem_union_left _ ⟨σ, hpa, rfl⟩))
    exact Semiformula.models_lMap.mp hmap
  · rcases hind with ⟨φ, hφ, rfl⟩
    have hInd : M↓[LX] ⊧
        (succInd (Semiformula.lMap toLX φ)).univCl :=
      Theory.models (T := paLX) M
        (Set.mem_union_right _ (Set.mem_union_right _
          ⟨Semiformula.lMap toLX φ, trivial, rfl⟩))
    rw [models_iff, Semiformula.eval_univCl] at hInd ⊢
    intro f
    rw [← map_succInd] at hInd
    exact Semiformula.eval_lMap.mp (hInd f)

/-- The arithmetic reduct of every PA[X] model satisfies IΣ₁. -/
lemma paLX_models_ISigmaOne_reduct {M : Type*} [Nonempty M]
    [sLX : Structure LX M] [M↓[LX] ⊧* paLX] :
    (sLX.lMap toLX).toStruc ⊧* 𝗜𝚺₁ :=
  Semantics.ModelsSet.of_subset paLX_models_peano_reduct
    (Set.union_subset_union_right _
      (InductionScheme_subset (by intros; trivial)))

/-- Transport an arithmetic PA derivation into the X-free fragment of PA[X]. -/
theorem paLX_of_peano {σ : ArithmeticSentence} (h : 𝗣𝗔 ⊢ σ) :
    paLX ⊢ Semiformula.lMap toLX σ := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ sLX _ hM
  letI : M↓[LX] ⊧* paLX := hM
  have hPA : (sLX.lMap toLX).toStruc ⊧* 𝗣𝗔 :=
    paLX_models_peano_reduct
  exact Semiformula.models_lMap.mpr ((Theory.Proof.sound h) hPA)

/--
Transport a PA theorem to any semantically equivalent sentence of `PA[X]`.
This form is convenient when universal closure changes its syntax under the
language map even though its interpretation is unchanged.
-/
lemma paLX_of_peano_semantic {σ : ArithmeticSentence} {τ : Sentence LX}
    (h : 𝗣𝗔 ⊢ σ)
    (hsem : ∀ (M : Type) [Nonempty M] [sLX : Structure LX M],
      M↓[LX] ⊧ τ ↔ (sLX.lMap toLX).toStruc ⊧ σ) :
    paLX ⊢ τ := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ sLX _ hM
  letI : M↓[LX] ⊧* paLX := hM
  apply (hsem M).mpr
  exact (Theory.Proof.sound h) paLX_models_peano_reduct


end OrdinalAnalysis.Gentzen.CodedNotation
