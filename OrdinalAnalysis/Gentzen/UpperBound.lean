/-
  Gentzen's 1943 upper bound.

  For each external Cantor-normal-form notation below epsilon zero, this file
  constructs a separate PA[X] derivation of transfinite induction below its
  standard code.  The quantification over notations is deliberately in Lean's
  metalanguage: there is no single PA proof asserting all of these instances.
-/
import OrdinalAnalysis.Gentzen.OmegaTower
import OrdinalAnalysis.Gentzen.NotationBridge
import OrdinalAnalysis.Gentzen.Order
import OrdinalAnalysis.Gentzen.Cofinality

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OrdinalAnalysis.Gentzen.UpperBound

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.CodedNotation
open OrdinalAnalysis.Gentzen.OmegaTower
open OrdinalAnalysis.Gentzen.NotationBridge
open OrdinalAnalysis.Gentzen.Order
open OrdinalAnalysis.Gentzen.Cofinality

/-- The closed PA[X] numeral for an external normal notation. -/
noncomputable def notationTerm (a : NONote) : Semiterm LX ℕ 0 :=
  ((nonoteCode a : ℕ) : Semiterm LX ℕ 0)

private def arithPrecAt {n : ℕ}
    (a b : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![a, b] ▹ Rewriting.emb precDef.val

/-- Pure-arithmetic comparison of two fixed standard notation codes. -/
noncomputable def arithmeticNonotePrecStatement (a b : NONote) :
    ArithmeticSentence :=
  (arithPrecAt
    ((nonoteCode a : ℕ) : Semiterm ℒₒᵣ ℕ 0)
    ((nonoteCode b : ℕ) : Semiterm ℒₒᵣ ℕ 0)).univCl

/-- Every true comparison of two external normal notations is provable in
IΣ₁ after replacing the notations by their standard codes. -/
theorem arithmetic_nonote_prec {a b : NONote} (h : a < b) :
    𝗜𝚺₁ ⊢ arithmeticNonotePrecStatement a b := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp [arithmeticNonotePrecStatement, arithPrecAt, eval_precDef,
    Structure.numeral_eq_numeral, numeral_eq_natCast]
  change isNF (nonoteModelCode (V := M) a) ∧
    isNF (nonoteModelCode (V := M) b) ∧
      icmp (nonoteModelCode (V := M) a)
        (nonoteModelCode (V := M) b) = 0
  exact ⟨isNF_nonoteModelCode a, isNF_nonoteModelCode b,
    (nonote_lt_iff_icmpModelCode_eq_zero a b).mp h⟩

private lemma map_nonote_prec_body (a b : NONote) :
    Semiformula.lMap toLX
        (arithPrecAt
          ((nonoteCode a : ℕ) : Semiterm ℒₒᵣ ℕ 0)
          ((nonoteCode b : ℕ) : Semiterm ℒₒᵣ ℕ 0)) =
      precAt precCode (notationTerm a) (notationTerm b) := by
  simp [arithPrecAt, precAt, precCode, liftCode, notationTerm,
    Semiformula.lMap_subst]
  rw [lMap_numeral (nonoteCode a), lMap_numeral (nonoteCode b)]

lemma models_nonote_prec_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] (a b : NONote) :
    M↓[LX] ⊧ closedPrec (notationTerm a) (notationTerm b) ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticNonotePrecStatement a b := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [closedPrec, arithmeticNonotePrecStatement,
    Semiformula.eval_univCl]
  constructor
  · intro h f
    apply Semiformula.eval_lMap.mp
    rw [map_nonote_prec_body]
    exact h f
  · intro h f
    rw [← map_nonote_prec_body]
    exact Semiformula.eval_lMap.mpr (h f)

/-- PA[X] proves every true comparison between two fixed standard notation
codes. -/
theorem concrete_nonote_prec {a b : NONote} (h : a < b) :
    paLX ⊢ closedPrec (notationTerm a) (notationTerm b) := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl (arithmetic_nonote_prec h))
  intro M _ _
  exact models_nonote_prec_iff_arithmetic a b

/-- Generic Gentzen upper bound: for every formula and every external normal
notation, PA[X] proves transfinite induction below its standard code. -/
theorem concrete_nonote_ti (φ : Semiformula LX ℕ 1) (a : NONote) :
    paLX ⊢ closedTI φ (notationTerm a) := by
  obtain ⟨n, han⟩ := exists_lt_nonoteTower a
  apply concrete_tiUpto_downward φ (notationTerm a) (towerTerm n)
  · simpa [notationTerm, nonoteCode_tower, towerTerm] using
      concrete_nonote_prec han
  · exact concrete_tower_ti n φ

/-- The concrete `X`-predicate form of the upper bound. -/
theorem concrete_nonote_TIupto (a : NONote) :
    paLX ⊢ (TIupto precCode (notationTerm a)).univCl := by
  rw [← tiUptoAt_X_eq]
  exact concrete_nonote_ti (Xat (#0 : Semiterm LX ℕ 1)) a

/-- The requested metalanguage-quantified form, with the normal-form witness
supplied explicitly rather than packaged as a subtype. -/
theorem gentzen_upper_bound (φ : Semiformula LX ℕ 1)
    (a : ONote) (ha : ONote.NF a) :
    paLX ⊢ closedTI φ (notationTerm ⟨a, ha⟩) :=
  concrete_nonote_ti φ ⟨a, ha⟩

end OrdinalAnalysis.Gentzen.UpperBound
