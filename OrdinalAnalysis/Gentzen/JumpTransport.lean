/-
  Transport of the iteration laws from `ℒₒᵣ` to `LX`, generic in the `Σ₁` definition.

  The concrete statements of `JumpArithmetic`, `CodedVeblenJump` and `Epsilon1UpperBound`
  are the substitution instances of large `PR`-generated formulas.  Proving the
  `lMap` / evaluation lemmas directly on those formulas makes a kernel that reduces
  `subst`/`lMap` structurally (nanoda) unfold them.  Here the lemmas are proved once for an
  abstract `Σ₁` definition (`σ`, `α`, `π`), and each concrete lemma is an instance whose
  only kernel obligation is delta-unfolding the wrappers.
-/
import OrdinalAnalysis.Gentzen.CodedNotation

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.JumpTransport

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.CodedNotation

lemma lMap_zero {n : ℕ} :
    Semiterm.lMap toLX ((0 : ℕ) : ArithmeticSemiterm ℕ n) =
      ((0 : ℕ) : Semiterm LX ℕ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, toLX]

lemma lMap_succ_four :
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

lemma map_iterZero_gen (σ : 𝚺₁.Semisentence 4) :
    Semiformula.lMap toLX
        (∀¹ ∀¹ ∀¹
          (∼(Rew.subst ![#0, #2, #1, ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 3)] ▹
              Rewriting.emb σ.val) ⋎
            (“#0 = #2” : Semiformula ℒₒᵣ ℕ 3))) =
      (∀¹ ∀¹ ∀¹
        (∼(iterAt (liftCode σ) #0 #2 #1 ((0 : ℕ) : Semiterm LX ℕ 3)) ⋎
          (“#0 = #2” : Semiformula LX ℕ 3))) := by
  simp [iterAt, liftCode, Semiformula.lMap_subst]
  constructor
  · rw [lMap_zero]
  · simp [Semiformula.Operator.operator,
      Semiformula.Operator.Eq.sentence_eq, toLX]
    apply funext
    rw [Fin.forall_fin_two]
    exact ⟨rfl, rfl⟩

lemma map_iterSucc_gen (σ : 𝚺₁.Semisentence 4) (α : 𝚺₁.Semisentence 3) :
    Semiformula.lMap toLX
        (∀¹ ∀¹ ∀¹ ∀¹
          (∼(Rew.subst ![#0, #3, #2, (‘(#1 + 1)’ : Semiterm ℒₒᵣ ℕ 4)] ▹
              Rewriting.emb σ.val) ⋎
            (∃¹ ((Rew.subst ![#0, #4, #3, #2] ▹ Rewriting.emb σ.val) ⋏
              (Rew.subst ![#1, #0, #3] ▹ Rewriting.emb α.val))))) =
      (∀¹ ∀¹ ∀¹ ∀¹
        (∼(iterAt (liftCode σ) #0 #3 #2 (‘(#1 + 1)’ : Semiterm LX ℕ 4)) ⋎
          (∃¹ (iterAt (liftCode σ) #0 #4 #3 #2 ⋏
            addAt (liftCode α) #1 #0 #3)))) := by
  simp [iterAt, addAt, liftCode, Semiformula.lMap_subst]
  rw [lMap_succ_four]

lemma map_noPredZero_gen (π : 𝚺₁.Semisentence 2) :
    Semiformula.lMap toLX
        (∀¹ ∼(Rew.subst ![(#0 : Semiterm ℒₒᵣ ℕ 1),
              ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 1)] ▹ Rewriting.emb π.val)) =
      (∀¹ ∼(precAt (liftCode π) (#0 : Semiterm LX ℕ 1)
        ((0 : ℕ) : Semiterm LX ℕ 1))) := by
  simp [precAt, liftCode, Semiformula.lMap_subst]
  rw [lMap_zero]

lemma models_iterSucc_gen {M : Type*} [Nonempty M]
    [sLX : Structure LX M] (σ : 𝚺₁.Semisentence 4) (α : 𝚺₁.Semisentence 3) :
    M↓[LX] ⊧ iterSuccStatement (liftCode α) (liftCode σ) ↔
      (sLX.lMap toLX).toStruc ⊧
        ((∀¹ ∀¹ ∀¹ ∀¹
          (∼(Rew.subst ![#0, #3, #2, (‘(#1 + 1)’ : Semiterm ℒₒᵣ ℕ 4)] ▹
              Rewriting.emb σ.val) ⋎
            (∃¹ ((Rew.subst ![#0, #4, #3, #2] ▹ Rewriting.emb σ.val) ⋏
              (Rew.subst ![#1, #0, #3] ▹ Rewriting.emb α.val))))).univCl :
          Sentence ℒₒᵣ) := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [iterSuccStatement, Semiformula.eval_univCl]
  rw [← map_iterSucc_gen]
  simp [Semiformula.eval_lMap]

end OrdinalAnalysis.Gentzen.JumpTransport
