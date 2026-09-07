/-
  Gentzen's Lemma A: the jump of a progressive formula is progressive.

  The proof is independent of a particular coding of ordinal notations.  Its
  three arithmetic premises describe only what the argument uses:

    * a zero-step iteration ends at its base;
    * a successor-step iteration has a preceding step;
    * every point below `b + omega ^ a` is either below `b`, is `b`, or lies
      below a finite iteration by some `omega ^ d` with `d < a`.

  `Iter(z, b, w, k)` follows the same result-first convention as the graph
  formulas in `Jump.lean`: it says that `z` is obtained from `b` after `k`
  additions of `w`.  The concrete arithmetization will supply this graph and
  prove the three premises in `PA[X]`.  Those intended graph instances are
  X-free arithmetic formulas transported into `LX`; the generic theorem keeps
  them as `LX` formulas only so that it does not commit to one representation.
-/
import OrdinalAnalysis.Gentzen.Jump

namespace OrdinalAnalysis

namespace Gentzen

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### Finite iteration and its arithmetic laws -/

/-- Apply a result-first four-place finite-iteration graph. -/
def iterAt (iterCode : Semiformula LX ℕ 4) {n : ℕ}
    (z b w k : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  Rew.subst ![z, b, w, k] ▹ iterCode

private def shiftTwice {n : ℕ}
    (φ : Semiformula LX ℕ n) : Semiformula LX ℕ n :=
  Rew.shift ▹ (Rew.shift ▹ φ)

/--
The induction formula saying that every endpoint of a `k`-step iteration from
`b` by `w` satisfies `Below(φ, ·)`.  Its first two free-variable slots reserve
the parameters `b` and `w` while preserving every free parameter of the graph
and formula codes.
-/
private def iterBelowFormula (prec : Semiformula LX ℕ 2)
    (iterCode : Semiformula LX ℕ 4) (φ : Semiformula LX ℕ 1) :
    Semiformula LX ℕ 1 :=
  ∀¹
    (∼(iterAt (shiftTwice iterCode) #0
        (&0 : Semiterm LX ℕ 2) (&1 : Semiterm LX ℕ 2) #1) ⋎
      belowAt (shiftTwice prec) (shiftTwice φ) #0)

@[simp] private theorem eval_shiftTwice {M : Type*} [Structure LX M]
    {n : ℕ} (φ : Semiformula LX ℕ n) (e : Fin n → M) (f : ℕ → M)
    (b w : M) :
    (shiftTwice φ).Eval e (b :>ₙ (w :>ₙ f)) ↔ φ.Eval e f := by
  simp [shiftTwice]

@[simp] theorem eval_iterAt {M : Type*} [Structure LX M]
    (iterCode : Semiformula LX ℕ 4) {n : ℕ}
    (z b w k : Semiterm LX ℕ n) (e : Fin n → M) (f : ℕ → M) :
    (iterAt iterCode z b w k).Eval e f ↔
      iterCode.Eval ![z.val e f, b.val e f, w.val e f, k.val e f] f := by
  simp [iterAt]

@[simp] private theorem eval_iterBelowFormula {M : Type*} [Structure LX M]
    (prec : Semiformula LX ℕ 2) (iterCode : Semiformula LX ℕ 4)
    (φ : Semiformula LX ℕ 1) (f : ℕ → M) (b w k : M) :
    (iterBelowFormula prec iterCode φ).Eval ![k] (b :>ₙ (w :>ₙ f)) ↔
      ∀ z : M,
        iterCode.Eval ![z, b, w, k] f →
        ∀ y : M, prec.Eval ![y, z] f → φ.Eval ![y] f := by
  simp [iterBelowFormula]
  constructor
  · intro h z hiter
    rcases h z with hnot | hbelow
    · exact (hnot hiter).elim
    · exact hbelow
  · intro h z
    by_cases hiter : iterCode.Eval ![z, b, w, k] f
    · exact Or.inr (h z hiter)
    · exact Or.inl hiter

/-- A zero-step iteration has its base as endpoint. -/
def iterZeroStatement (iterCode : Semiformula LX ℕ 4) : Sentence LX :=
  (∀¹ ∀¹ ∀¹
    (∼(iterAt iterCode #0 #2 #1 ((0 : ℕ) : Semiterm LX ℕ 3)) ⋎
      (“#0 = #2” : Semiformula LX ℕ 3))).univCl

/--
A successor-step iteration factors through an endpoint of the preceding step.
-/
def iterSuccStatement (addCode : Semiformula LX ℕ 3)
    (iterCode : Semiformula LX ℕ 4) : Sentence LX :=
  (∀¹ ∀¹ ∀¹ ∀¹
    (∼(iterAt iterCode #0 #3 #2
        (‘(#1 + 1)’ : Semiterm LX ℕ 4)) ⋎
      (∃¹ (iterAt iterCode #0 #4 #3 #2 ⋏ addAt addCode #1 #0 #3)))).univCl

/--
The cofinal decomposition used at the limit step of Lemma A.

For `OmegaPow(u,a)`, `Add(z,b,u)`, and `g ≺ z`, either `g ≺ b`, `g = b`, or
there are `d,w,k,v` with `d ≺ a`, `OmegaPow(w,d)`, `Iter(v,b,w,k)`, and
`g ≺ v`.
-/
def omegaCoverStatement (prec : Semiformula LX ℕ 2)
    (addCode : Semiformula LX ℕ 3) (omegaPowCode : Semiformula LX ℕ 2)
    (iterCode : Semiformula LX ℕ 4) : Sentence LX :=
  (∀¹ ∀¹ ∀¹ ∀¹ ∀¹
    (∼(omegaPowAt omegaPowCode #2 #4) ⋎
      (∼(addAt addCode #1 #3 #2) ⋎
        (∼(precAt prec #0 #1) ⋎
          (precAt prec #0 #3 ⋎
            ((“#0 = #3” : Semiformula LX ℕ 5) ⋎
              (∃¹ ∃¹ ∃¹ ∃¹
                (precAt prec #3 #8 ⋏
                  (omegaPowAt omegaPowCode #2 #3 ⋏
                    (iterAt iterCode #0 #7 #2 #1 ⋏
                      precAt prec #4 #0)))))))))).univCl

/-! ### Semantic forms of the laws -/

private lemma paLX_induction_eval {M : Type*} [Nonempty M] [Structure LX M]
    [M↓[LX] ⊧* paLX] (ψ : Semiformula LX ℕ 1) (f : ℕ → M) :
    ψ.Eval ![((0 : ℕ) : Semiterm LX ℕ 0).val ![] f] f →
    (∀ x : M,
      ψ.Eval ![x] f →
      ψ.Eval ![(‘(#0 + 1)’ : Semiterm LX ℕ 1).val ![x] f] f) →
    ∀ x : M, ψ.Eval ![x] f := by
  have hInd : M↓[LX] ⊧ (succInd ψ).univCl :=
    Theory.models (T := paLX) M (by
      change (succInd ψ).univCl ∈
        𝗘𝗤 LX ∪ (Theory.lMap toLX 𝗣𝗔⁻ ∪ InductionScheme LX Set.univ)
      exact Set.mem_union_right _ (Set.mem_union_right _
        (show (succInd ψ).univCl ∈ InductionScheme LX Set.univ from
          ⟨ψ, trivial, rfl⟩)))
  revert f
  simpa [models_iff, Semiformula.eval_univCl, succInd,
    Semiformula.eval_substs, Matrix.constant_eq_singleton] using hInd

theorem models_iterZeroStatement {M : Type*} [Nonempty M] [Structure LX M]
    [Structure.Eq LX M] (iterCode : Semiformula LX ℕ 4) :
    M↓[LX] ⊧ iterZeroStatement iterCode ↔
      ∀ f : ℕ → M, ∀ b w z : M,
        iterCode.Eval
          ![z, b, w, ((0 : ℕ) : Semiterm LX ℕ 0).val ![] f] f →
        z = b := by
  classical
  simp [models_iff, iterZeroStatement]
  constructor
  · intro h f b w z hiter
    rcases h f b w z with hnot | hz
    · exact (hnot (by simpa using hiter)).elim
    · exact hz
  · intro h f b w z
    by_cases hiter :
        iterCode.Eval
          ![z, b, w, ((0 : ℕ) : Semiterm LX ℕ 0).val ![] f] f
    · exact Or.inr (h f b w z (by simpa using hiter))
    · exact Or.inl (by simpa using hiter)

theorem models_iterSuccStatement {M : Type*} [Nonempty M] [Structure LX M]
    (addCode : Semiformula LX ℕ 3) (iterCode : Semiformula LX ℕ 4) :
    M↓[LX] ⊧ iterSuccStatement addCode iterCode ↔
      ∀ f : ℕ → M, ∀ b w k z : M,
        iterCode.Eval
          ![z, b, w, (‘(#0 + 1)’ : Semiterm LX ℕ 1).val ![k] f] f →
        ∃ v : M,
          iterCode.Eval ![v, b, w, k] f ∧
          addCode.Eval ![z, v, w] f := by
  classical
  simp [models_iff, iterSuccStatement]
  constructor
  · intro h f b w k z hiter
    rcases h f b w k z with hnot | hv
    · exact (hnot (by simpa using hiter)).elim
    · exact hv
  · intro h f b w k z
    by_cases hiter :
        iterCode.Eval
          ![z, b, w, (‘(#0 + 1)’ : Semiterm LX ℕ 1).val ![k] f] f
    · exact Or.inr (h f b w k z (by simpa using hiter))
    · exact Or.inl (by simpa using hiter)

theorem models_omegaCoverStatement {M : Type*} [Nonempty M]
    [Structure LX M] [Structure.Eq LX M]
    (prec : Semiformula LX ℕ 2) (addCode : Semiformula LX ℕ 3)
    (omegaPowCode : Semiformula LX ℕ 2) (iterCode : Semiformula LX ℕ 4) :
    M↓[LX] ⊧ omegaCoverStatement prec addCode omegaPowCode iterCode ↔
      ∀ f : ℕ → M, ∀ a b u z g : M,
        omegaPowCode.Eval ![u, a] f →
        addCode.Eval ![z, b, u] f →
        prec.Eval ![g, z] f →
        prec.Eval ![g, b] f ∨ g = b ∨
          ∃ d w k v : M,
            prec.Eval ![d, a] f ∧
            omegaPowCode.Eval ![w, d] f ∧
            iterCode.Eval ![v, b, w, k] f ∧
            prec.Eval ![g, v] f := by
  classical
  simp [models_iff, omegaCoverStatement]
  constructor
  · intro h f a b u z g hω hadd hprec
    rcases h f a b u z g with
      hnotω | hnotadd | hnotprec | hbelow | heq | hwitness
    · exact (hnotω hω).elim
    · exact (hnotadd hadd).elim
    · exact (hnotprec hprec).elim
    · exact Or.inl hbelow
    · exact Or.inr (Or.inl heq)
    · rcases hwitness with ⟨d, hd, w, hpow, k, v, hiter, hgv⟩
      exact Or.inr (Or.inr ⟨d, hd, w, hpow, k, v, hiter, hgv⟩)
  · intro h f a b u z g
    by_cases hω : omegaPowCode.Eval ![u, a] f
    · right
      by_cases hadd : addCode.Eval ![z, b, u] f
      · right
        by_cases hprec : prec.Eval ![g, z] f
        · right
          rcases h f a b u z g hω hadd hprec with
            hbelow | heq | hwitness
          · exact Or.inl hbelow
          · right
            exact Or.inl heq
          · right
            right
            rcases hwitness with ⟨d, hd, w, hpow, k, v, hiter, hgv⟩
            exact ⟨d, hd, w, hpow, k, v, hiter, hgv⟩
        · left
          exact hprec
      · left
        exact hadd
    · left
      exact hω

/-! ### Lemma A -/

private theorem model_iter_preserves_below {M : Type*} [Nonempty M]
    [Structure LX M] [Structure.Eq LX M] [M↓[LX] ⊧* paLX]
    (prec : Semiformula LX ℕ 2) (addCode : Semiformula LX ℕ 3)
    (omegaPowCode : Semiformula LX ℕ 2) (iterCode : Semiformula LX ℕ 4)
    (φ : Semiformula LX ℕ 1) (f : ℕ → M)
    (hZero : M↓[LX] ⊧ iterZeroStatement iterCode)
    (hSucc : M↓[LX] ⊧ iterSuccStatement addCode iterCode)
    (q w b : M)
    (hPow : omegaPowCode.Eval ![w, q] f)
    (hJump : (jump prec addCode omegaPowCode φ).Eval ![q] f)
    (hBelow : ∀ y : M, prec.Eval ![y, b] f → φ.Eval ![y] f) :
    ∀ k v : M,
      iterCode.Eval ![v, b, w, k] f →
      ∀ y : M, prec.Eval ![y, v] f → φ.Eval ![y] f := by
  have hZero' := (models_iterZeroStatement iterCode).mp hZero
  have hSucc' := (models_iterSuccStatement addCode iterCode).mp hSucc
  have hJump' := (eval_jump prec addCode omegaPowCode φ q f).mp hJump
  have hAll :
      ∀ k : M,
        (iterBelowFormula prec iterCode φ).Eval ![k]
          (b :>ₙ (w :>ₙ f)) := by
    apply paLX_induction_eval (ψ := iterBelowFormula prec iterCode φ)
      (f := b :>ₙ (w :>ₙ f))
    · rw [eval_iterBelowFormula]
      intro v hiter
      have hv : v = b := hZero' f b w v (by simpa using hiter)
      subst v
      exact hBelow
    · intro k hk
      rw [eval_iterBelowFormula] at hk ⊢
      intro z hiter
      rcases hSucc' f b w k z (by simpa using hiter) with
        ⟨v, hvIter, hzAdd⟩
      exact hJump' v w z hPow hzAdd (hk v hvIter)
  intro k v hiter
  exact (eval_iterBelowFormula prec iterCode φ f b w k).mp (hAll k) v hiter

/--
Gentzen's Lemma A, isolated from the concrete coding of ordinal operations.

The hypotheses are derivations in `paLX` of the two finite-iteration laws and
the omega-cover law above.  Under precisely those arithmetic obligations, the
jump of every progressive formula is progressive.  In the concrete use of the
theorem, all four graph formulas are X-free arithmetic formulas.
-/
theorem jump_A (prec : Semiformula LX ℕ 2) (addCode : Semiformula LX ℕ 3)
    (omegaPowCode : Semiformula LX ℕ 2) (iterCode : Semiformula LX ℕ 4)
    (φ : Semiformula LX ℕ 1)
    (hZero : paLX ⊢ iterZeroStatement iterCode)
    (hSucc : paLX ⊢ iterSuccStatement addCode iterCode)
    (hCover : paLX ⊢ omegaCoverStatement prec addCode omegaPowCode iterCode) :
    paLX ⊢ jumpAStatement prec addCode omegaPowCode φ := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  have hZeroM : M↓[LX] ⊧ iterZeroStatement iterCode :=
    consequence_iff_eq'.mp (Theory.Proof.sound hZero) M
  have hSuccM : M↓[LX] ⊧ iterSuccStatement addCode iterCode :=
    consequence_iff_eq'.mp (Theory.Proof.sound hSucc) M
  have hCoverM :
      M↓[LX] ⊧ omegaCoverStatement prec addCode omegaPowCode iterCode :=
    consequence_iff_eq'.mp (Theory.Proof.sound hCover) M
  have hCover' :=
    (models_omegaCoverStatement prec addCode omegaPowCode iterCode).mp hCoverM
  rw [models_iff]
  simp only [
    jumpAStatement,
    Semiformula.eval_univCl,
    LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq,
    eval_progAt
  ]
  intro f
  by_cases hProg :
      ∀ x : M,
        (∀ y : M, prec.Eval ![y, x] f → φ.Eval ![y] f) →
          φ.Eval ![x] f
  · refine Or.inr ?_
    intro a hBelowJump
    rw [eval_jump]
    intro b u z hPow hadd hBelow g hgz
    rcases hCover' f a b u z g hPow hadd hgz with
      hgb | hgb | ⟨d, w, k, v, hd, hPow', hIter, hgv⟩
    · exact hBelow g hgb
    · subst g
      exact hProg b hBelow
    · have hJumpD := hBelowJump d hd
      have hBelowV :=
        model_iter_preserves_below prec addCode omegaPowCode iterCode φ f
          hZeroM hSuccM d w b hPow' hJumpD hBelow k v hIter
      exact hBelowV g hgv
  · exact Or.inl hProg

end Gentzen

end OrdinalAnalysis
