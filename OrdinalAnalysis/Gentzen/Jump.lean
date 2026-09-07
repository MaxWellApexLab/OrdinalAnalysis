/-
  Gentzen's jump construction, separated from the arithmetization of ordinal
  notations.

  The graph formulas in this file use the result-first convention:

    Add(z, x, y)       means z = x + y,
    OmegaPow(z, x)     means z = omega ^ x.

  No particular coding of ordinal notations is assumed.  The theorem `jump_B`
  isolates the purely logical content of Gentzen's Lemma B: once Lemma A, the
  absence of predecessors of zero, and the left-zero law for the addition graph
  have been proved in `PA[X]`, transfinite induction for the jump up to `a`
  yields transfinite induction for the original predicate up to `omega ^ a`.
-/
import OrdinalAnalysis.Gentzen.Setup
import Foundation.FirstOrder.Completeness

namespace OrdinalAnalysis

namespace Gentzen

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### Generic progressiveness -/

/-- Apply a unary object-language formula to a term. -/
def formulaAt (φ : Semiformula LX ℕ 1) {n : ℕ}
    (x : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  Rew.subst ![x] ▹ φ

/-- Apply a result-first graph for ordinal addition: `Add(z, x, y)`. -/
def addAt (addCode : Semiformula LX ℕ 3) {n : ℕ}
    (z x y : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  Rew.subst ![z, x, y] ▹ addCode

/-- Apply a result-first graph for exponentiation by omega: `OmegaPow(z, x)`. -/
def omegaPowAt (omegaPowCode : Semiformula LX ℕ 2) {n : ℕ}
    (z x : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  Rew.subst ![z, x] ▹ omegaPowCode

/-- `Below(φ, b) :≡ ∀ y, y ≺ b → φ(y)`. -/
def belowAt (prec : Semiformula LX ℕ 2) (φ : Semiformula LX ℕ 1) {n : ℕ}
    (b : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  ∀¹ (∼(precAt prec (#0 : Semiterm LX ℕ (n + 1)) (Rew.bShift b)) ⋎
    formulaAt φ #0)

/-- `Prog(φ) :≡ ∀ x, Below(φ, x) → φ(x)`. -/
def progAt (prec : Semiformula LX ℕ 2) (φ : Semiformula LX ℕ 1) {n : ℕ} :
    Semiformula LX ℕ n :=
  ∀¹ (∼(belowAt prec φ (#0 : Semiterm LX ℕ (n + 1))) ⋎ formulaAt φ #0)

/-- `TI(φ, a) :≡ Prog(φ) → Below(φ, a)`. -/
def tiUptoAt (prec : Semiformula LX ℕ 2) (φ : Semiformula LX ℕ 1) {n : ℕ}
    (a : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  ∼(progAt prec φ) ⋎ belowAt prec φ a

/-! ### The jump -/

/--
`Jump(φ, a)` in relational graph form:

  `∀ b u z, OmegaPow(u, a) → Add(z, b, u) → Below(φ, b) → Below(φ, z)`.

For total functional graphs this is precisely the usual assertion that every
initial segment satisfying `φ` can be extended from `b` to `b + omega ^ a`.
-/
def jumpAt (prec : Semiformula LX ℕ 2) (addCode : Semiformula LX ℕ 3)
    (omegaPowCode : Semiformula LX ℕ 2) (φ : Semiformula LX ℕ 1) {n : ℕ}
    (a : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  ∀¹ ∀¹ ∀¹
    (∼(omegaPowAt omegaPowCode (#1 : Semiterm LX ℕ (n + 3))
        (Rew.bShift (Rew.bShift (Rew.bShift a)))) ⋎
      (∼(addAt addCode #0 #2 #1) ⋎
        (∼(belowAt prec φ #2) ⋎ belowAt prec φ #0)))

/-- The unary formula `a ↦ Jump(φ, a)`. -/
def jump (prec : Semiformula LX ℕ 2) (addCode : Semiformula LX ℕ 3)
    (omegaPowCode : Semiformula LX ℕ 2) (φ : Semiformula LX ℕ 1) :
    Semiformula LX ℕ 1 :=
  jumpAt prec addCode omegaPowCode φ #0

/-! ### Closed statements used by the jump lemmas -/

/-- Gentzen's Lemma A, packaged as a closed object-language statement. -/
def jumpAStatement (prec : Semiformula LX ℕ 2) (addCode : Semiformula LX ℕ 3)
    (omegaPowCode : Semiformula LX ℕ 2) (φ : Semiformula LX ℕ 1) :
    Sentence LX :=
  (∼(progAt prec φ) ⋎ progAt prec (jump prec addCode omegaPowCode φ)).univCl

/-- Zero has no predecessor in the notation ordering. -/
def noPredZeroStatement (prec : Semiformula LX ℕ 2) : Sentence LX :=
  (∀¹ ∼(precAt prec (#0 : Semiterm LX ℕ 1) ((0 : ℕ) : Semiterm LX ℕ 1))).univCl

/-- The result-first addition graph proves `Add(u, 0, u)`. -/
def zeroAddStatement (addCode : Semiformula LX ℕ 3) : Sentence LX :=
  (∀¹ addAt addCode (#0 : Semiterm LX ℕ 1)
    ((0 : ℕ) : Semiterm LX ℕ 1) #0).univCl

/--
The relational form of Gentzen's Lemma B:

  `∀ a u, OmegaPow(u, a) → TI(Jump φ, a) → TI(φ, u)`.
-/
def jumpBStatement (prec : Semiformula LX ℕ 2) (addCode : Semiformula LX ℕ 3)
    (omegaPowCode : Semiformula LX ℕ 2) (φ : Semiformula LX ℕ 1) :
    Sentence LX :=
  (∀¹ ∀¹
    (∼(omegaPowAt omegaPowCode (#0 : Semiterm LX ℕ 2) #1) ⋎
      (∼(tiUptoAt prec (jump prec addCode omegaPowCode φ) #1) ⋎
        tiUptoAt prec φ #0))).univCl

/-! ### Evaluation lemmas -/

@[simp] theorem eval_precAt {M : Type*} [Structure LX M]
    (prec : Semiformula LX ℕ 2) {n : ℕ} (y x : Semiterm LX ℕ n)
    (e : Fin n → M) (f : ℕ → M) :
    (precAt prec y x).Eval e f ↔ prec.Eval ![y.val e f, x.val e f] f := by
  simp [precAt]

@[simp] theorem eval_formulaAt {M : Type*} [Structure LX M]
    (φ : Semiformula LX ℕ 1) {n : ℕ} (x : Semiterm LX ℕ n)
    (e : Fin n → M) (f : ℕ → M) :
    (formulaAt φ x).Eval e f ↔ φ.Eval ![x.val e f] f := by
  simp [formulaAt]

@[simp] theorem eval_addAt {M : Type*} [Structure LX M]
    (addCode : Semiformula LX ℕ 3) {n : ℕ} (z x y : Semiterm LX ℕ n)
    (e : Fin n → M) (f : ℕ → M) :
    (addAt addCode z x y).Eval e f ↔
      addCode.Eval ![z.val e f, x.val e f, y.val e f] f := by
  simp [addAt]

@[simp] theorem eval_omegaPowAt {M : Type*} [Structure LX M]
    (omegaPowCode : Semiformula LX ℕ 2) {n : ℕ} (z x : Semiterm LX ℕ n)
    (e : Fin n → M) (f : ℕ → M) :
    (omegaPowAt omegaPowCode z x).Eval e f ↔
      omegaPowCode.Eval ![z.val e f, x.val e f] f := by
  simp [omegaPowAt]

@[simp] theorem eval_belowAt {M : Type*} [Structure LX M]
    (prec : Semiformula LX ℕ 2) (φ : Semiformula LX ℕ 1) {n : ℕ}
    (b : Semiterm LX ℕ n) (e : Fin n → M) (f : ℕ → M) :
    (belowAt prec φ b).Eval e f ↔
      ∀ y : M, prec.Eval ![y, b.val e f] f → φ.Eval ![y] f := by
  simp [belowAt]
  constructor
  · intro h y hy
    rcases h y with hnot | hφ
    · exact (hnot hy).elim
    · exact hφ
  · intro h y
    by_cases hy : prec.Eval ![y, b.val e f] f
    · exact Or.inr (h y hy)
    · exact Or.inl hy

@[simp] theorem eval_progAt {M : Type*} [Structure LX M]
    (prec : Semiformula LX ℕ 2) (φ : Semiformula LX ℕ 1) {n : ℕ}
    (e : Fin n → M) (f : ℕ → M) :
    (progAt (n := n) prec φ).Eval e f ↔
      ∀ x : M,
        (∀ y : M, prec.Eval ![y, x] f → φ.Eval ![y] f) →
          φ.Eval ![x] f := by
  classical
  simp [progAt]
  constructor
  · intro h x hx
    rcases h x with hcounter | hx'
    · rcases hcounter with ⟨y, hy, hny⟩
      exact (hny (hx y hy)).elim
    · exact hx'
  · intro h x
    by_cases hx : ∀ y : M, prec.Eval ![y, x] f → φ.Eval ![y] f
    · exact Or.inr (h x hx)
    · left
      push Not at hx
      exact hx

@[simp] theorem eval_tiUptoAt {M : Type*} [Structure LX M]
    (prec : Semiformula LX ℕ 2) (φ : Semiformula LX ℕ 1) {n : ℕ}
    (a : Semiterm LX ℕ n) (e : Fin n → M) (f : ℕ → M) :
    (tiUptoAt prec φ a).Eval e f ↔
      (∀ x : M,
          (∀ y : M, prec.Eval ![y, x] f → φ.Eval ![y] f) →
            φ.Eval ![x] f) →
        ∀ y : M, prec.Eval ![y, a.val e f] f → φ.Eval ![y] f := by
  classical
  simp [tiUptoAt]
  constructor
  · intro h hprog
    rcases h with hcounter | hbelow
    · rcases hcounter with ⟨x, hbelowx, hnotx⟩
      exact (hnotx (hprog x hbelowx)).elim
    · exact hbelow
  · intro h
    by_cases hprog :
        ∀ x : M,
          (∀ y : M, prec.Eval ![y, x] f → φ.Eval ![y] f) →
            φ.Eval ![x] f
    · exact Or.inr (h hprog)
    · left
      push Not at hprog
      exact hprog

@[simp] theorem eval_jumpAt {M : Type*} [Structure LX M]
    (prec : Semiformula LX ℕ 2) (addCode : Semiformula LX ℕ 3)
    (omegaPowCode : Semiformula LX ℕ 2) (φ : Semiformula LX ℕ 1) {n : ℕ}
    (a : Semiterm LX ℕ n) (e : Fin n → M) (f : ℕ → M) :
    (jumpAt prec addCode omegaPowCode φ a).Eval e f ↔
      ∀ b u z : M,
        omegaPowCode.Eval ![u, a.val e f] f →
        addCode.Eval ![z, b, u] f →
        (∀ y : M, prec.Eval ![y, b] f → φ.Eval ![y] f) →
        ∀ y : M, prec.Eval ![y, z] f → φ.Eval ![y] f := by
  classical
  simp [jumpAt]
  constructor
  · intro h b u z hω hadd hbelow
    rcases h b u z with hnotω | hnotadd | hnotbelow | hbelowz
    · exact (hnotω hω).elim
    · exact (hnotadd hadd).elim
    · rcases hnotbelow with ⟨y, hy, hny⟩
      exact (hny (hbelow y hy)).elim
    · exact hbelowz
  · intro h b u z
    by_cases hω : omegaPowCode.Eval ![u, a.val e f] f
    · right
      by_cases hadd : addCode.Eval ![z, b, u] f
      · right
        by_cases hbelow :
            ∀ y : M, prec.Eval ![y, b] f → φ.Eval ![y] f
        · right
          exact h b u z hω hadd hbelow
        · left
          push Not at hbelow
          exact hbelow
      · left
        exact hadd
    · left
      exact hω

@[simp] theorem eval_jump {M : Type*} [Structure LX M]
    (prec : Semiformula LX ℕ 2) (addCode : Semiformula LX ℕ 3)
    (omegaPowCode : Semiformula LX ℕ 2) (φ : Semiformula LX ℕ 1)
    (a : M) (f : ℕ → M) :
    (jump prec addCode omegaPowCode φ).Eval ![a] f ↔
      ∀ b u z : M,
        omegaPowCode.Eval ![u, a] f →
        addCode.Eval ![z, b, u] f →
        (∀ y : M, prec.Eval ![y, b] f → φ.Eval ![y] f) →
        ∀ y : M, prec.Eval ![y, z] f → φ.Eval ![y] f := by
  simp [jump]

/-! ### Lemma B -/

/--
The logical core of Gentzen's Lemma B.

The three hypotheses deliberately remain proofs in `paLX`.  A concrete
arithmetization later supplies them for its notation ordering and graph
formulas; this theorem then returns the required `paLX` derivation without
depending on how those graphs were implemented.
-/
theorem jump_B (prec : Semiformula LX ℕ 2) (addCode : Semiformula LX ℕ 3)
    (omegaPowCode : Semiformula LX ℕ 2) (φ : Semiformula LX ℕ 1)
    (hA : paLX ⊢ jumpAStatement prec addCode omegaPowCode φ)
    (hZero : paLX ⊢ noPredZeroStatement prec)
    (hZeroAdd : paLX ⊢ zeroAddStatement addCode) :
    paLX ⊢ jumpBStatement prec addCode omegaPowCode φ := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff']
  intro M _ _ hM
  have hA' :
      M↓[LX] ⊧ jumpAStatement prec addCode omegaPowCode φ :=
    consequence_iff'.mp (Theory.Proof.sound hA) M
  have hZero' : M↓[LX] ⊧ noPredZeroStatement prec :=
    consequence_iff'.mp (Theory.Proof.sound hZero) M
  have hZeroAdd' : M↓[LX] ⊧ zeroAddStatement addCode :=
    consequence_iff'.mp (Theory.Proof.sound hZeroAdd) M
  rw [models_iff] at hA' hZero' hZeroAdd' ⊢
  simp only [
    jumpAStatement,
    noPredZeroStatement,
    zeroAddStatement,
    jumpBStatement,
    Semiformula.eval_univCl,
    Semiformula.eval_all,
    LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq,
    eval_progAt,
    eval_omegaPowAt,
    eval_tiUptoAt,
    eval_precAt,
    eval_addAt
  ] at hA' hZero' hZeroAdd' ⊢
  intro f a u
  by_cases hω : omegaPowCode.Eval ![u, a] f
  · by_cases hTI :
        (∀ x : M,
            (∀ y : M,
                prec.Eval ![y, x] f →
                  (jump prec addCode omegaPowCode φ).Eval ![y] f) →
              (jump prec addCode omegaPowCode φ).Eval ![x] f) →
          ∀ y : M,
            prec.Eval ![y, a] f →
              (jump prec addCode omegaPowCode φ).Eval ![y] f
    · refine Or.inr (Or.inr ?_)
      intro hProg
      have hJumpProg :
          ∀ x : M,
            (∀ y : M,
                prec.Eval ![y, x] f →
                  (jump prec addCode omegaPowCode φ).Eval ![y] f) →
              (jump prec addCode omegaPowCode φ).Eval ![x] f := by
        rcases hA' f with hnot | hyes
        · exact (hnot hProg).elim
        · exact hyes
      have hJumpBelow :
          ∀ y : M,
            prec.Eval ![y, a] f →
              (jump prec addCode omegaPowCode φ).Eval ![y] f :=
        hTI hJumpProg
      have hJumpAtA :
          (jump prec addCode omegaPowCode φ).Eval ![a] f :=
        hJumpProg a hJumpBelow
      let z0 : M := ((0 : ℕ) : Semiterm LX ℕ 0).val ![] f
      have hBelowZero :
          ∀ y : M, prec.Eval ![y, z0] f → φ.Eval ![y] f := by
        intro y hy
        exact (hZero' f y (by simpa [z0] using hy)).elim
      exact
        (eval_jump prec addCode omegaPowCode φ a f).mp hJumpAtA
          z0 u u hω
          (by simpa [z0] using hZeroAdd' f u)
          hBelowZero
    · exact Or.inr (Or.inl hTI)
  · exact Or.inl hω

end Gentzen

end OrdinalAnalysis
