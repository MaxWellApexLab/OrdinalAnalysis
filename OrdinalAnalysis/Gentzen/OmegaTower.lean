/-
  Finite omega towers and their PA[X] transfinite-induction proofs.

  Every tower edge is certified by the arithmetized omega-power graph.  The
  jump lemma then turns the proof at one stage into a proof at the next stage.
  The final theorem specializes the generic predicate to the fresh predicate
  `X`, yielding the concrete `TIupto` sentence used by the upper bound.
-/
import OrdinalAnalysis.Gentzen.OmegaCover

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OrdinalAnalysis.Gentzen.OmegaTower

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.CodedNotation
open OrdinalAnalysis.Gentzen.JumpArithmetic
open OrdinalAnalysis.Gentzen.OmegaCover

/-- Transfinite induction below zero is vacuous. -/
theorem concrete_ti_zero (φ : Semiformula LX ℕ 1) :
    paLX ⊢ (tiUptoAt precCode φ
      ((0 : ℕ) : Semiterm LX ℕ 0)).univCl := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  have hZero : M↓[LX] ⊧ noPredZeroStatement precCode :=
    consequence_iff_eq'.mp (Theory.Proof.sound concrete_noPredZero) M
  rw [models_iff] at hZero ⊢
  simp only [noPredZeroStatement, Semiformula.eval_univCl] at hZero
  simp [precAt] at hZero
  simp [tiUptoAt]
  intro f
  right
  intro y hy
  exact (hZero f y hy).elim

/-- A certified omega-power edge lifts induction from its exponent to its value. -/
theorem concrete_ti_omegaPow
    (φ : Semiformula LX ℕ 1) (a u : Semiterm LX ℕ 0)
    (hPow : paLX ⊢ (omegaPowAt omegaPowCode u a).univCl)
    (hTI : paLX ⊢
      (tiUptoAt precCode (jump precCode safeAddCode omegaPowCode φ) a).univCl) :
    paLX ⊢ (tiUptoAt precCode φ u).univCl := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  have hB : M↓[LX] ⊧
      jumpBStatement precCode safeAddCode omegaPowCode φ :=
    consequence_iff_eq'.mp (Theory.Proof.sound (concrete_jump_B φ)) M
  have hPowM : M↓[LX] ⊧ (omegaPowAt omegaPowCode u a).univCl :=
    consequence_iff_eq'.mp (Theory.Proof.sound hPow) M
  have hTIM : M↓[LX] ⊧
      (tiUptoAt precCode (jump precCode safeAddCode omegaPowCode φ) a).univCl :=
    consequence_iff_eq'.mp (Theory.Proof.sound hTI) M
  rw [models_iff] at hB hPowM hTIM ⊢
  simp only [jumpBStatement, Semiformula.eval_univCl,
    Semiformula.eval_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq, eval_omegaPowAt, eval_tiUptoAt] at hB
  simp only [Semiformula.eval_univCl] at hPowM hTIM ⊢
  intro f
  have hp := eval_omegaPowAt omegaPowCode u a ![] f |>.mp (hPowM f)
  have ht := eval_tiUptoAt precCode
    (jump precCode safeAddCode omegaPowCode φ) a ![] f |>.mp (hTIM f)
  have h := hB f (a.val ![] f) (u.val ![] f)
  rcases h with hnp | hnt | hgoal
  · exact (hnp hp).elim
  · exact (hnt ht).elim
  · exact (eval_tiUptoAt precCode φ u ![] f).mpr hgoal

/-- Codes for `0, 1, ω, ω^ω, ...`; stage `n + 1` is `ω` to stage `n`. -/
noncomputable def towerCode : ℕ → ℕ
  | 0 => 0
  | n + 1 => ocOadd (towerCode n) 1 0

/-- The closed PA[X] numeral denoting a finite omega-tower code. -/
noncomputable def towerTerm (n : ℕ) : Semiterm LX ℕ 0 :=
  ((towerCode n : ℕ) : Semiterm LX ℕ 0)

@[simp] lemma natCast_ocOadd {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e n r : ℕ) :
    ((ocOadd e n r : ℕ) : V) = ocOadd (e : V) (n : V) (r : V) := by
  simp [ocOadd, nat_cast_pair]

@[simp] lemma towerTerm_zero :
    towerTerm 0 = ((0 : ℕ) : Semiterm LX ℕ 0) := by
  simp [towerTerm, towerCode]

/-- Every standard finite tower code is an internal normal-form code. -/
lemma towerCode_nf {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (n : ℕ) :
    isNF ((towerCode n : ℕ) : V) := by
  induction n with
  | zero => simp [towerCode]
  | succ n ih =>
      rw [towerCode, natCast_ocOadd]
      exact isNF_omegaBlock ih (by simp)

private def arithOmegaPowAtTower {n : ℕ}
    (z a : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, a] ▹ Rewriting.emb omegaPowDef.val

/-- Pure-arithmetic assertion that two adjacent standard tower codes form an
omega-power edge. -/
noncomputable def arithmeticTowerOmegaPowStatement (n : ℕ) : Sentence ℒₒᵣ :=
  (arithOmegaPowAtTower
    ((towerCode (n + 1) : ℕ) : Semiterm ℒₒᵣ ℕ 0)
    ((towerCode n : ℕ) : Semiterm ℒₒᵣ ℕ 0)).univCl

theorem arithmetic_tower_omegaPow (n : ℕ) :
    𝗜𝚺₁ ⊢ arithmeticTowerOmegaPowStatement n := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp [arithmeticTowerOmegaPowStatement, arithOmegaPowAtTower,
    eval_omegaPowDef, Structure.numeral_eq_numeral, numeral_eq_natCast,
    towerCode, towerCode_nf]

/-- Arithmetic numerals are preserved by the language embedding into LX. -/
lemma lMap_numeral {k : ℕ} (m : ℕ) :
    Semiterm.lMap toLX ((m : ℕ) : Semiterm ℒₒᵣ ℕ k) =
      ((m : ℕ) : Semiterm LX ℕ k) := by
  induction m using Nat.twoStepInduction with
  | zero =>
      simp [Semiterm.Operator.operator, Semiterm.Operator.numeral_zero,
        Semiterm.Operator.Zero.term_eq, toLX]
  | one =>
      simp [Semiterm.Operator.operator, Semiterm.Operator.numeral_one,
        Semiterm.Operator.One.term_eq, toLX]
  | more m hm hm1 =>
      change Semiterm.lMap toLX
          ((Semiterm.Operator.numeral ℒₒᵣ (m + 2)).operator ![]) =
        (Semiterm.Operator.numeral LX (m + 2)).operator ![]
      rw [Semiterm.Operator.numeral_add_two,
        Semiterm.Operator.numeral_add_two]
      rw [Semiterm.Operator.operator_comp,
        Semiterm.Operator.operator_comp]
      simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, toLX]
      apply funext
      rw [Fin.forall_fin_two]
      constructor
      · change Semiterm.lMap toLX
          ((m + 1 : ℕ) : Semiterm ℒₒᵣ ℕ k) =
            ((m + 1 : ℕ) : Semiterm LX ℕ k)
        exact hm1
      · change Semiterm.lMap toLX
          ((1 : ℕ) : Semiterm ℒₒᵣ ℕ k) =
            ((1 : ℕ) : Semiterm LX ℕ k)
        simp [Semiterm.Operator.operator, Semiterm.Operator.numeral_one,
          Semiterm.Operator.One.term_eq, toLX]

private lemma map_tower_omegaPow_body (n : ℕ) :
    Semiformula.lMap toLX
        (arithOmegaPowAtTower
          ((towerCode (n + 1) : ℕ) : Semiterm ℒₒᵣ ℕ 0)
          ((towerCode n : ℕ) : Semiterm ℒₒᵣ ℕ 0)) =
      omegaPowAt omegaPowCode (towerTerm (n + 1)) (towerTerm n) := by
  simp [arithOmegaPowAtTower, omegaPowAt, omegaPowCode, liftCode,
    towerTerm, Semiformula.lMap_subst]
  rw [lMap_numeral (towerCode (n + 1)), lMap_numeral (towerCode n)]

lemma models_tower_omegaPow_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] (n : ℕ) :
    M↓[LX] ⊧ (omegaPowAt omegaPowCode (towerTerm (n + 1))
      (towerTerm n)).univCl ↔
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

/-- PA[X] proves every adjacent finite-tower omega-power edge. -/
theorem concrete_tower_omegaPow (n : ℕ) :
    paLX ⊢ (omegaPowAt omegaPowCode (towerTerm (n + 1))
      (towerTerm n)).univCl := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl (arithmetic_tower_omegaPow n))
  intro M _ _
  exact models_tower_omegaPow_iff_arithmetic n

/-- One PA[X] derivation for each finite stage of the omega tower. -/
theorem concrete_tower_ti (n : ℕ) (φ : Semiformula LX ℕ 1) :
    paLX ⊢ (tiUptoAt precCode φ (towerTerm n)).univCl := by
  induction n generalizing φ with
  | zero =>
      simpa [towerTerm_zero] using concrete_ti_zero φ
  | succ n ih =>
      exact concrete_ti_omegaPow φ (towerTerm n) (towerTerm (n + 1))
        (concrete_tower_omegaPow n)
        (ih (jump precCode safeAddCode omegaPowCode φ))

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

/-- The generic induction formula specialized to the fresh predicate is the
public `TIupto` formula from the setup layer. -/
lemma tiUptoAt_X_eq (t : Semiterm LX ℕ 0) :
    tiUptoAt precCode (Xat (#0 : Semiterm LX ℕ 1)) t =
      TIupto precCode t := by
  simp [tiUptoAt, TIupto, progAt, Prog, belowAt, below, formulaAt_X_eq]

/-- PA[X] proves its concrete transfinite-induction sentence below every finite
omega tower. -/
theorem concrete_tower_TIupto (n : ℕ) :
    paLX ⊢ (TIupto precCode (towerTerm n)).univCl := by
  rw [← tiUptoAt_X_eq]
  exact concrete_tower_ti n (Xat (#0 : Semiterm LX ℕ 1))

end OrdinalAnalysis.Gentzen.OmegaTower
