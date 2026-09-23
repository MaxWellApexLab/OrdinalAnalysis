/-
  The transport of (EPSMONO), with surjectivity folded in, to `PA[X]`.

  `InternalEpsMono` proves the internal ε-function `iepsilon`, its surjectivity onto the
  ε-numbers (`eps_surj`), and its monotonicity (`eps_mono`, i.e. (EPSMONO):
  `ε_h ≺₁ ε_g → h ≺₁ g`).  This file packages the one instance the ACA progressiveness
  argument actually uses: `e` is *already* an ε-number below `ε_g` (rather than an arbitrary
  code), so `eps_surj` hands back a normal `h` with `e = ε_h`, and `eps_mono` then turns
  `e ≺₁ ε_g` into `h ≺₁ g`.  That combined fact is transported to the object language.

  **`Base` is restricted to `Fix`.**  `VeblenSuccStep.baseDef₁` guards `e = 0 ∨ fixIndic e = 1`,
  because the successor step needs both `0` and the ε-numbers as bases.  `eps_surj` has no
  clause for `e = 0`: it needs `fixIndic e = 1` outright, and indeed `0` is not in the range of
  `iepsilon` (`fixIndic_iepsilon` shows every value of `iepsilon` is a fixed point of `φ_1`,
  while `0` is not — `epsFixIndic_eq_one_iff` requires `g ≠ 0`).  So the guard here, `fixDef₁`,
  drops the `e = 0` disjunct and states `Fix(e) :≡ NF(e) ∧ fixIndic(e) = 1` outright.
-/
import OrdinalAnalysis.Gentzen.InternalEpsMono

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OrdinalAnalysis.Gentzen.InternalEpsMonoCode

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.InternalVNote
open OrdinalAnalysis.Gentzen.InternalVNoteOrder
open OrdinalAnalysis.Gentzen.InternalVNoteJump
open OrdinalAnalysis.Gentzen.CodedNotation (liftCode paLX_of_peano_semantic)
open OrdinalAnalysis.Gentzen.CodedVeblen
open OrdinalAnalysis.Gentzen.InternalEpsMono

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The ε-graph `Eps(y, g)` -/

/-- `Eps(y, g)`: `g` is a normal code and `y` is its ε-value, `y = ε_g`. -/
def epsDef₁ : 𝚺₁.Semisentence 2 := .mkSigma
  “y g. !isNFb₁Def 1 g ∧ !iepsilonDef y g”

@[simp] theorem eval_epsDef₁ (y g : V) :
    epsDef₁.val.Evalb ![y, g] ↔ isNF₁ g ∧ y = iepsilon g := by
  simp [epsDef₁, isNF₁, isNFb₁_defined.iff, iepsilon_defined.iff, eq_comm]

/-- The ε-graph, in `LX`. -/
def epsCode₁ : Semiformula LX ℕ 2 := liftCode epsDef₁

/-- Apply a result-first ε-graph: `Eps(y, g)`. -/
def epsAt (epsCode : Semiformula LX ℕ 2) {n : ℕ}
    (y g : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  Rew.subst ![y, g] ▹ epsCode

@[simp] theorem eval_epsAt {M : Type*} [Structure LX M]
    (epsCode : Semiformula LX ℕ 2) {n : ℕ} (y g : Semiterm LX ℕ n)
    (e : Fin n → M) (f : ℕ → M) :
    (epsAt epsCode y g).Eval e f ↔ epsCode.Eval ![y.val e f, g.val e f] f := by
  simp [epsAt]

/-! ## The guard `Fix(e)` -/

/-- `Fix(e)`: `e` is a normal code and an ε-number.  Narrower than
`VeblenSuccStep.baseDef₁` — see the module docstring. -/
def fixDef₁ : 𝚺₁.Semisentence 1 := .mkSigma
  “e. !isNFb₁Def 1 e ∧ !fixIndicDef 1 e”

@[simp] theorem eval_fixDef₁ (e : V) :
    fixDef₁.val.Evalb ![e] ↔ isNF₁ e ∧ fixIndic e = 1 := by
  simp [fixDef₁, isNF₁, isNFb₁_defined.iff, fixIndic_defined.iff, eq_comm]

/-- The guard, in `LX`. -/
def fixCode₁ : Semiformula LX ℕ 1 := liftCode fixDef₁

/-! ## The mathematical content -/

/-- **(EPSMONO) with surjectivity folded in.**  If `e` is itself an ε-number below `ε_g`, it
is `ε_h` for some normal `h` below `g`. -/
theorem eps_mono_of_surj {e g u : V} (he : isNF₁ e) (hfix : fixIndic e = 1)
    (hg : isNF₁ g) (hu : u = iepsilon g) (hlt : icmp₁ e u = 0) :
    ∃ h : V, isNF₁ h ∧ e = iepsilon h ∧ icmp₁ h g = 0 := by
  obtain ⟨h, hh, hhe⟩ := eps_surj he hfix
  refine ⟨h, hh, hhe.symm, eps_mono hg hh ?_⟩
  rw [hhe, ← hu]
  exact hlt

/-! ## The statement -/

/--
**(EPSMONO), with surjectivity folded in.**

`∀ e ∀ g ∀ u (Fix(e) → NF(g) → Eps(u, g) → e ≺₁ u → ∃ h (NF(h) ∧ Eps(e, h) ∧ h ≺₁ g))`.
-/
noncomputable def epsMonoStatement : Sentence LX :=
  (∀¹ ∀¹ ∀¹
    (∼(formulaAt fixCode₁ (#2 : Semiterm LX ℕ 3)) ⋎
      (∼(formulaAt nfCode₁ (#1 : Semiterm LX ℕ 3)) ⋎
        (∼(epsAt epsCode₁ (#0 : Semiterm LX ℕ 3) #1) ⋎
          (∼(precAt precCode₁ #2 #0) ⋎
            (∃¹
              (formulaAt nfCode₁ (#0 : Semiterm LX ℕ 4) ⋏
                (epsAt epsCode₁ (#3 : Semiterm LX ℕ 4) #0 ⋏
                  precAt precCode₁ #0 #2)))))))).univCl

private def arithFixAt {n : ℕ} (e : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![e] ▹ Rewriting.emb fixDef₁.val

private def arithNfAt {n : ℕ} (x : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![x] ▹ Rewriting.emb nfDef₁.val

private def arithPrecAt {n : ℕ} (x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![x, y] ▹ Rewriting.emb precDef₁.val

private def arithEpsAt {n : ℕ} (y g : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![y, g] ▹ Rewriting.emb epsDef₁.val

noncomputable def arithmeticEpsMonoStatement : ArithmeticSentence :=
  (∀¹ ∀¹ ∀¹
    (∼(arithFixAt (#2 : Semiterm ℒₒᵣ ℕ 3)) ⋎
      (∼(arithNfAt (#1 : Semiterm ℒₒᵣ ℕ 3)) ⋎
        (∼(arithEpsAt (#0 : Semiterm ℒₒᵣ ℕ 3) #1) ⋎
          (∼(arithPrecAt #2 #0) ⋎
            (∃¹
              (arithNfAt (#0 : Semiterm ℒₒᵣ ℕ 4) ⋏
                (arithEpsAt (#3 : Semiterm ℒₒᵣ ℕ 4) #0 ⋏
                  arithPrecAt #0 #2)))))))).univCl

/-! ## The `IΣ₁` proof -/

theorem arithmetic_epsMono : 𝗜𝚺₁ ⊢ arithmeticEpsMonoStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp [arithmeticEpsMonoStatement, arithFixAt, arithNfAt, arithEpsAt, arithPrecAt,
    eval_fixDef₁, eval_nfDef₁, eval_precDef₁, eval_epsDef₁]
  intro e g u
  by_cases hne : isNF₁ e
  · by_cases hfx : fixIndic e = 1
    · by_cases hng : isNF₁ g
      · by_cases hu : u = iepsilon g
        · by_cases hlt : icmp₁ e u = 0
          · right; right; right; right
            obtain ⟨h, hh, hhe, hhg⟩ := eps_mono_of_surj hne hfx hng hu hlt
            exact ⟨h, hh, ⟨hh, hhe⟩, hh, hng, hhg⟩
          · right; right; right; left
            intro _ _
            exact hlt
        · right; right; left
          intro _
          exact hu
      · right; left
        exact hng
    · left
      intro _
      exact hfx
  · left
    intro h
    exact absurd h hne

/-! ## Transport to `PA[X]` -/

private lemma map_epsMono_body :
    Semiformula.lMap toLX
        (∀¹ ∀¹ ∀¹
          (∼(arithFixAt (#2 : Semiterm ℒₒᵣ ℕ 3)) ⋎
            (∼(arithNfAt (#1 : Semiterm ℒₒᵣ ℕ 3)) ⋎
              (∼(arithEpsAt (#0 : Semiterm ℒₒᵣ ℕ 3) #1) ⋎
                (∼(arithPrecAt #2 #0) ⋎
                  (∃¹
                    (arithNfAt (#0 : Semiterm ℒₒᵣ ℕ 4) ⋏
                      (arithEpsAt (#3 : Semiterm ℒₒᵣ ℕ 4) #0 ⋏
                        arithPrecAt #0 #2)))))))) =
      (∀¹ ∀¹ ∀¹
        (∼(formulaAt fixCode₁ (#2 : Semiterm LX ℕ 3)) ⋎
          (∼(formulaAt nfCode₁ (#1 : Semiterm LX ℕ 3)) ⋎
            (∼(epsAt epsCode₁ (#0 : Semiterm LX ℕ 3) #1) ⋎
              (∼(precAt precCode₁ #2 #0) ⋎
                (∃¹
                  (formulaAt nfCode₁ (#0 : Semiterm LX ℕ 4) ⋏
                    (epsAt epsCode₁ (#3 : Semiterm LX ℕ 4) #0 ⋏
                      precAt precCode₁ #0 #2)))))))) := by
  simp [arithFixAt, arithNfAt, arithEpsAt, arithPrecAt, formulaAt, epsAt, precAt,
    fixCode₁, nfCode₁, epsCode₁, precCode₁, liftCode, Semiformula.lMap_subst]

lemma models_epsMono_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ epsMonoStatement ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticEpsMonoStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [epsMonoStatement, arithmeticEpsMonoStatement, Semiformula.eval_univCl]
  rw [← map_epsMono_body]
  simp [Semiformula.eval_lMap]

/-- **(EPSMONO) with surjectivity folded in, in `PA[X]`.** -/
theorem concrete_epsMono : paLX ⊢ epsMonoStatement := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_epsMono)
  intro M _ _
  exact models_epsMono_iff_arithmetic

/-! ## Semantic form -/

theorem models_epsMonoStatement {M : Type*} [Nonempty M] [Structure LX M]
    [Structure.Eq LX M] :
    M↓[LX] ⊧ epsMonoStatement ↔
      ∀ f : ℕ → M, ∀ e g u : M,
        fixCode₁.Eval ![e] f →
        nfCode₁.Eval ![g] f →
        epsCode₁.Eval ![u, g] f →
        precCode₁.Eval ![e, u] f →
        ∃ h : M, nfCode₁.Eval ![h] f ∧ epsCode₁.Eval ![e, h] f ∧ precCode₁.Eval ![h, g] f := by
  classical
  simp [models_iff, epsMonoStatement]
  constructor
  · intro h f e g u hf hn he hp
    rcases h f e g u with hnf | hnn | hne | hnp | hgoal
    · exact (hnf hf).elim
    · exact (hnn hn).elim
    · exact (hne he).elim
    · exact (hnp hp).elim
    · exact hgoal
  · intro h f e g u
    by_cases hf : fixCode₁.Eval ![e] f
    · right
      by_cases hn : nfCode₁.Eval ![g] f
      · right
        by_cases he : epsCode₁.Eval ![u, g] f
        · right
          by_cases hp : precCode₁.Eval ![e, u] f
          · exact Or.inr (h f e g u hf hn he hp)
          · exact Or.inl hp
        · exact Or.inl he
      · exact Or.inl hn
    · exact Or.inl hf

end OrdinalAnalysis.Gentzen.InternalEpsMonoCode
