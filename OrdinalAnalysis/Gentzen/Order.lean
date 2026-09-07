/-
  Transitivity of the arithmetized notation order and downward closure of
  transfinite induction.
-/
import OrdinalAnalysis.Gentzen.CodedNotation

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.Order

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.CodedNotation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private lemma icmp_transitive {a b c : V}
    (hab : icmp a b = 0) (hbc : icmp b c = 0) :
    icmp a c = 0 :=
  icmp_trans (max a (max b c)) a (le_max_left _ _)
    b (le_trans (le_max_left _ _) (le_max_right _ _))
    c (le_trans (le_max_right _ _) (le_max_right _ _)) hab hbc

private def arithPrecAt {n : ℕ}
    (a b : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![a, b] ▹ Rewriting.emb precDef.val

/-- Pure-arithmetic transitivity of the coded notation order. -/
def arithmeticPrecTransStatement : ArithmeticSentence :=
  (∀¹ ∀¹ ∀¹
    (∼(arithPrecAt (#2 : Semiterm ℒₒᵣ ℕ 3) #1) ⋎
      (∼(arithPrecAt #1 #0) ⋎ arithPrecAt #2 #0))).univCl

theorem arithmetic_precTrans : 𝗜𝚺₁ ⊢ arithmeticPrecTransStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simp [models_iff, arithmeticPrecTransStatement, arithPrecAt,
    eval_precDef]
  intro a b c
  by_cases hab : isNF a ∧ isNF b ∧ icmp a b = 0
  · right
    by_cases hbc : isNF b ∧ isNF c ∧ icmp b c = 0
    · right
      exact ⟨hab.1, hbc.2.1, icmp_transitive hab.2.2 hbc.2.2⟩
    · left
      intro hb hc hcmp
      exact hbc ⟨hb, hc, hcmp⟩
  · left
    intro ha hb hcmp
    exact hab ⟨ha, hb, hcmp⟩

/-- Language-independent statement that `prec` is transitive. -/
def precTransStatement (prec : Semiformula LX ℕ 2) : Sentence LX :=
  (∀¹ ∀¹ ∀¹
    (∼(precAt prec (#2 : Semiterm LX ℕ 3) #1) ⋎
      (∼(precAt prec #1 #0) ⋎ precAt prec #2 #0))).univCl

lemma models_precTrans_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ precTransStatement precCode ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticPrecTransStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  simp [models_iff, precTransStatement, arithmeticPrecTransStatement,
    arithPrecAt, precAt, precCode, liftCode, Semiformula.eval_lMap]

/-- PA[X] proves transitivity of the concrete coded notation order. -/
theorem concrete_precTrans : paLX ⊢ precTransStatement precCode := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_precTrans)
  intro M _ _
  exact models_precTrans_iff_arithmetic

theorem models_precTransStatement {M : Type*} [Nonempty M]
    [Structure LX M] (prec : Semiformula LX ℕ 2) :
    M↓[LX] ⊧ precTransStatement prec ↔
      ∀ f : ℕ → M, ∀ a b c : M,
        prec.Eval ![a, b] f → prec.Eval ![b, c] f →
          prec.Eval ![a, c] f := by
  classical
  simp [models_iff, precTransStatement]
  constructor
  · intro h f a b c hab hbc
    rcases h f a b c with hnab | hnbc | hac
    · exact (hnab hab).elim
    · exact (hnbc hbc).elim
    · exact hac
  · intro h f a b c
    by_cases hab : prec.Eval ![a, b] f
    · right
      by_cases hbc : prec.Eval ![b, c] f
      · exact Or.inr (h f a b c hab hbc)
      · exact Or.inl hbc
    · exact Or.inl hab

/-- Universal closure of a concrete comparison. -/
def closedPrec (a b : Semiterm LX ℕ 0) : Sentence LX :=
  (precAt precCode a b).univCl

/-- Universal closure of generic transfinite induction below a closed term. -/
def closedTI (φ : Semiformula LX ℕ 1)
    (a : Semiterm LX ℕ 0) : Sentence LX :=
  (tiUptoAt precCode φ a).univCl

/-- Transfinite induction up to the concrete coded order is downward closed. -/
theorem concrete_tiUpto_downward
    (φ : Semiformula LX ℕ 1) (a b : Semiterm LX ℕ 0)
    (hab : paLX ⊢ closedPrec a b)
    (hTIb : paLX ⊢ closedTI φ b) :
    paLX ⊢ closedTI φ a := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  have hTransM : M↓[LX] ⊧ precTransStatement precCode :=
    consequence_iff_eq'.mp (Theory.Proof.sound concrete_precTrans) M
  have habM : M↓[LX] ⊧ closedPrec a b :=
    consequence_iff_eq'.mp (Theory.Proof.sound hab) M
  have hTIbM : M↓[LX] ⊧ closedTI φ b :=
    consequence_iff_eq'.mp (Theory.Proof.sound hTIb) M
  have hTrans := (models_precTransStatement precCode).mp hTransM
  rw [models_iff] at habM hTIbM ⊢
  simp only [closedPrec, closedTI, Semiformula.eval_univCl,
    eval_precAt, eval_tiUptoAt] at habM hTIbM ⊢
  intro f hProg y hya
  exact hTIbM f hProg y
    (hTrans f y (a.val ![] f) (b.val ![] f) hya (habM f))

end OrdinalAnalysis.Gentzen.Order
