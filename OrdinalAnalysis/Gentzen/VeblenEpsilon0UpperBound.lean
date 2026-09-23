/-
  Gentzen's `ε₀` upper bound over the *Veblen* coding, in plain `PA[X]`.

  `OmegaTower.lean` proves exactly this over the Cantor-normal-form coding of
  `InternalONote`: `PA[X] ⊢ TI(≺, ā)` for every `a < ε₀`.  The ACA upper bound needs the
  same statement one notation system up, over `≺₁` (the coded Veblen ordering of
  `InternalVNote`), because that is the ordering in which the heights above `ε₀` live.

  Nothing here is new mathematics.  The tower is `0, 1, ω, ω^ω, …`; each edge is certified
  by the ω-power graph `omegaPowCode₁` (no stage is an ε-number, so the graph is the plain
  `φ_0(·)` all the way up), Gentzen's Lemma B `jumpB₁` climbs it, and mathlib's
  `Ordinal.lt_epsilon_zero` says the tower is cofinal in `ε₀`.  Everything is generic in the
  induction formula `φ`, which is what the parametric lifting of the ACA bridge consumes.
-/
import OrdinalAnalysis.Gentzen.Epsilon1UpperBound

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OrdinalAnalysis.Gentzen.VeblenEpsilon0UpperBound

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
open OrdinalAnalysis.Gentzen.Epsilon1UpperBound
open OrdinalAnalysis.Gamma0Note (epsilonNote)

/-! ## The two structural steps, over plain `PA[X]` -/

/-- Transfinite induction below the code of zero is vacuous, for every formula. -/
theorem concrete_ti_zero₁ (φ : Semiformula LX ℕ 1) :
    paLX ⊢ closedTI₁ φ ((0 : ℕ) : Semiterm LX ℕ 0) := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  have hZero : M↓[LX] ⊧ noPredZeroStatement precCode₁ :=
    consequence_iff_eq'.mp (Theory.Proof.sound noPredZero₁) M
  rw [models_iff] at hZero ⊢
  simp only [noPredZeroStatement, Semiformula.eval_univCl] at hZero
  simp [precAt] at hZero
  simp [closedTI₁, tiUptoAt]
  intro f
  right
  intro y hy
  exact (hZero f y hy).elim

/-- A certified ω-power edge lifts induction from its exponent to its value, over plain
`PA[X]`.  (`Epsilon1UpperBound.concrete_ti_omegaPow₁` is the same step over `PA[X] + TI(ε₀)`.) -/
theorem concrete_ti_omegaPow₀
    (φ : Semiformula LX ℕ 1) (a u : Semiterm LX ℕ 0)
    (hPow : paLX ⊢ (omegaPowAt omegaPowCode₁ u a).univCl)
    (hTI : paLX ⊢
      (tiUptoAt precCode₁ (jump precCode₁ addCode₁ omegaPowCode₁ φ) a).univCl) :
    paLX ⊢ (tiUptoAt precCode₁ φ u).univCl := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
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

/-- Transfinite induction along `≺₁` is downward closed, over plain `PA[X]`. -/
theorem concrete_tiUpto_downward₀
    (φ : Semiformula LX ℕ 1) (a b : Semiterm LX ℕ 0)
    (hab : paLX ⊢ closedPrec₁ a b)
    (hTIb : paLX ⊢ closedTI₁ φ b) :
    paLX ⊢ closedTI₁ φ a := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
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

/-! ## The tower `0, 1, ω, ω^ω, …` -/

/-- The Veblen notations `0, 1, ω, ω^ω, …`; stage `n + 1` is `ω` to stage `n`. -/
def vtower : ℕ → Gamma0Note
  | 0 => 0
  | n + 1 => Gamma0Note.omegaPow (vtower n)

@[simp] lemma vtower_zero : vtower 0 = 0 := rfl

lemma vtower_succ (n : ℕ) : vtower (n + 1) = Gamma0Note.omegaPow (vtower n) := rfl

lemma gamma0Code_zero : gamma0Code 0 = 0 := rfl

@[simp] lemma gamma0Term_vtower_zero :
    gamma0Term (vtower 0) = ((0 : ℕ) : Semiterm LX ℕ 0) := by
  rw [vtower_zero]
  rfl

/-- Every stage of the tower is the plain ω-power term of the previous one: no stage is an
ε-number, so `veblenNote 0` never collapses. -/
lemma vtower_succ_val : ∀ n : ℕ, (vtower (n + 1)).1 = VNote.vadd 0 (vtower n).1 1 0
  | 0 => rfl
  | n + 1 => by
      rw [vtower_succ (n + 1)]
      show VNote.veblenNote 0 (vtower (n + 1)).1 = VNote.vadd 0 (vtower (n + 1)).1 1 0
      rw [vtower_succ_val n]
      exact VNote_veblenNote_zero_of (Or.inl rfl)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma modelCode_vtower_succ (n : ℕ) :
    gamma0ModelCode (V := V) (vtower (n + 1)) =
      vcVadd 0 (gamma0ModelCode (V := V) (vtower n)) 1 0 := by
  rw [gamma0ModelCode_eq, gamma0ModelCode_eq, vtower_succ_val, vmodelCode_vadd,
    vmodelCode_zero]
  simp

lemma modelCode_vtower_zero :
    gamma0ModelCode (V := V) (vtower 0) = 0 := by
  rw [vtower_zero, gamma0ModelCode_eq]
  exact vmodelCode_zero

/-- No stage of the tower is fixed-point-shaped. -/
lemma fixIndic_vtower_ne_one (n : ℕ) :
    fixIndic (gamma0ModelCode (V := V) (vtower n)) ≠ 1 := by
  cases n with
  | zero =>
      rw [modelCode_vtower_zero]
      exact fixIndic_zero_ne_one
  | succ n =>
      rw [modelCode_vtower_succ, Ne, fixIndic_vcVadd]
      rintro ⟨-, -, h⟩
      exact h rfl

/-- The ω-power graph certifies every tower edge. -/
lemma iomegaPow_vtower (n : ℕ) :
    iomegaPow (gamma0ModelCode (V := V) (vtower n)) =
      gamma0ModelCode (V := V) (vtower (n + 1)) := by
  rw [iomegaPow_of_not_fix (fixIndic_vtower_ne_one n), modelCode_vtower_succ]

/-! ## The tower edges in `PA[X]` -/

private def arithOmegaPowAt {n : ℕ}
    (z a : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, a] ▹ Rewriting.emb omegaPowDef₁.val

noncomputable def arithmeticVTowerOmegaPowStatement (n : ℕ) : Sentence ℒₒᵣ :=
  (arithOmegaPowAt
    ((gamma0Code (vtower (n + 1)) : ℕ) : Semiterm ℒₒᵣ ℕ 0)
    ((gamma0Code (vtower n) : ℕ) : Semiterm ℒₒᵣ ℕ 0)).univCl

theorem arithmetic_vtower_omegaPow (n : ℕ) :
    𝗜𝚺₁ ⊢ arithmeticVTowerOmegaPowStatement n := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp [arithmeticVTowerOmegaPowStatement, arithOmegaPowAt,
    eval_omegaPowDef₁, Structure.numeral_eq_numeral, numeral_eq_natCast]
  change isNF₁ (gamma0ModelCode (V := M) (vtower n)) ∧
    gamma0ModelCode (V := M) (vtower (n + 1)) =
      iomegaPow (gamma0ModelCode (V := M) (vtower n))
  exact ⟨isNF₁_gamma0ModelCode _, (iomegaPow_vtower n).symm⟩

private lemma map_vtower_omegaPow_body (n : ℕ) :
    Semiformula.lMap toLX
        (arithOmegaPowAt
          ((gamma0Code (vtower (n + 1)) : ℕ) : Semiterm ℒₒᵣ ℕ 0)
          ((gamma0Code (vtower n) : ℕ) : Semiterm ℒₒᵣ ℕ 0)) =
      omegaPowAt omegaPowCode₁ (gamma0Term (vtower (n + 1)))
        (gamma0Term (vtower n)) := by
  simp [arithOmegaPowAt, omegaPowAt, omegaPowCode₁, liftCode,
    gamma0Term, Semiformula.lMap_subst]
  rw [lMap_numeral (gamma0Code (vtower (n + 1))), lMap_numeral (gamma0Code (vtower n))]

lemma models_vtower_omegaPow_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] (n : ℕ) :
    M↓[LX] ⊧ (omegaPowAt omegaPowCode₁ (gamma0Term (vtower (n + 1)))
      (gamma0Term (vtower n))).univCl ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticVTowerOmegaPowStatement n := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [arithmeticVTowerOmegaPowStatement, Semiformula.eval_univCl]
  constructor
  · intro h f
    apply Semiformula.eval_lMap.mp
    rw [map_vtower_omegaPow_body]
    exact h f
  · intro h f
    rw [← map_vtower_omegaPow_body]
    exact Semiformula.eval_lMap.mpr (h f)

/-- `PA[X]` proves every tower edge of the ω-power graph. -/
theorem concrete_vtower_omegaPow (n : ℕ) :
    paLX ⊢ (omegaPowAt omegaPowCode₁ (gamma0Term (vtower (n + 1)))
      (gamma0Term (vtower n))).univCl := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl (arithmetic_vtower_omegaPow n))
  intro M _ _
  exact models_vtower_omegaPow_iff_arithmetic n

/-- **One `PA[X]` derivation for each stage of the tower, for every formula.** -/
theorem concrete_vtower_ti (n : ℕ) (φ : Semiformula LX ℕ 1) :
    paLX ⊢ closedTI₁ φ (gamma0Term (vtower n)) := by
  induction n generalizing φ with
  | zero =>
      rw [gamma0Term_vtower_zero]
      exact concrete_ti_zero₁ φ
  | succ n ih =>
      exact concrete_ti_omegaPow₀ φ (gamma0Term (vtower n))
        (gamma0Term (vtower (n + 1)))
        (concrete_vtower_omegaPow n)
        (ih (jump precCode₁ addCode₁ omegaPowCode₁ φ))

/-! ## Cofinality of the tower below `ε₀` -/

open Ordinal in
lemma repr_vtower : ∀ n : ℕ,
    Gamma0Note.repr (vtower n) = (fun x : Ordinal => ω ^ x)^[n] 0
  | 0 => by
      rw [vtower_zero, Function.iterate_zero, id]
      exact Gamma0Note.repr_zero
  | n + 1 => by
      rw [vtower_succ, Gamma0Note.repr_omegaPow, repr_vtower n,
        Function.iterate_succ_apply']

open Ordinal in
/-- Every Veblen notation below `ε₀` lies below some stage of the tower. -/
theorem exists_lt_vtower (a : Gamma0Note) (ha : a < epsilonNote 0) :
    ∃ n : ℕ, a < vtower n := by
  have ha' : Gamma0Note.repr a < ε₀ := by
    have h := ha
    rw [Gamma0Note.lt_def, Gamma0Note.epsilonNote_zero_repr] at h
    exact h
  rw [Ordinal.lt_epsilon_zero] at ha'
  obtain ⟨n, hn⟩ := ha'
  refine ⟨n, ?_⟩
  rw [Gamma0Note.lt_def, repr_vtower]
  exact hn

/-! ## The bound -/

/--
**Gentzen's `ε₀` bound over the Veblen coding.**  For every formula `φ` and every Veblen
notation `c < ε₀`, plain `PA[X]` proves transfinite induction for `φ` along `≺₁` below the
code of `c`.
-/
theorem concrete_eps0_ti (c : Gamma0Note) (hc : c < epsilonNote 0)
    (φ : Semiformula LX ℕ 1) :
    paLX ⊢ closedTI₁ φ (gamma0Term c) := by
  obtain ⟨n, hcn⟩ := exists_lt_vtower c hc
  exact concrete_tiUpto_downward₀ φ (gamma0Term c) (gamma0Term (vtower n))
    (concrete_gamma0_prec hcn) (concrete_vtower_ti n φ)

/-- The concrete `X`-predicate form. -/
theorem concrete_eps0_TIupto (c : Gamma0Note) (hc : c < epsilonNote 0) :
    paLX ⊢ (TIupto precCode₁ (gamma0Term c)).univCl := by
  rw [← tiUptoAt_X_eq']
  exact concrete_eps0_ti c hc (Xat (#0 : Semiterm LX ℕ 1))

end OrdinalAnalysis.Gentzen.VeblenEpsilon0UpperBound
