/-
  The first-order carries of the
  ε-progressiveness step.

  The design note's (Prog) is the statement that

      `ψ₀(g) :≡ ∀u (Eps(u,g) → ∀²X TI(≺₁, u, X))`

  is `≺₁`-progressive.  Its content splits, as (⋆⋆)'s did, into a *second-order*
  part — `gen₂`, `spec₂`, and three instantiations of closed `ACA`-theorems — and
  a *first-order* part, which is everything about the coded Veblen ordering.
  This file is the first-order part, and it is stated exactly in the shape the
  second-order layer consumes.

  Two design decisions carried over from `ACA/TowerInduction.lean`:

  * **the internal existentials are pushed down**.  `progCoverStatement` below
    is the cover of `InternalEpsCover.concrete_cover` with the `∃e∃s∃n∃w` turned
    into a *universal hypothesis*, so the second-order layer never eliminates an
    existential whose witness it cannot name;
  * **the case split lives here**.  `goodBody` names the disjunction "the tower
    base is `0 ⊕ 1`, or it is `ε_h ⊕ 1` for some `h ≺₁ g`"; the second-order
    layer only ever splits that disjunction with `PSeq.and`, never re-proves it.

  Everything below is either an `IΣ₁`-theorem transported by
  `CodedNotation.paLX_of_peano_semantic`, or a semantic consequence of
  already-transported `paLX`-theorems.
-/
import OrdinalAnalysis.Gentzen.InternalEpsMonoCode
import OrdinalAnalysis.Gentzen.InternalVeblen

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OrdinalAnalysis.Gentzen.ProgStep

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
open OrdinalAnalysis.Gentzen.VeblenTower
open OrdinalAnalysis.Gentzen.VeblenSuccStep
open OrdinalAnalysis.Gentzen.InternalEpsCover
open OrdinalAnalysis.Gentzen.InternalEpsMono
open OrdinalAnalysis.Gentzen.InternalEpsMonoCode
open OrdinalAnalysis.Gentzen.InternalVeblen
open OrdinalAnalysis.Gentzen.OmegaTower (lMap_numeral)
open OrdinalAnalysis.Gentzen.Epsilon1UpperBound (gamma0Term)
open OrdinalAnalysis.Gamma0Note (epsilonNote)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## `Good(s, g)`: the legitimate tower bases

`s` is a legitimate base for the internal ω-tower covering the segment below
`ε_g` when `s` is the coded successor of a `Base` which is either `0` or an
ε-number `ε_h` with `h ≺₁ g`.  The `Base(e)` conjunct is carried along because
it is what `VeblenSuccStep.succGeneralStatement` consumes. -/

/-- The matrix of `Good`, with `#0 = s` and `#1 = g`. -/
noncomputable def goodBody : Semiformula LX ℕ 2 :=
  (formulaAt baseCode₁ ((0 : ℕ) : Semiterm LX ℕ 2) ⋏
      addAt addCode₁ (#0 : Semiterm LX ℕ 2) ((0 : ℕ) : Semiterm LX ℕ 2)
        ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 2)) ⋎
    (∃¹ ∃¹
      (precAt precCode₁ (#1 : Semiterm LX ℕ 4) #3 ⋏
        (formulaAt baseCode₁ (#0 : Semiterm LX ℕ 4) ⋏
          (epsAt epsCode₁ (#0 : Semiterm LX ℕ 4) #1 ⋏
            addAt addCode₁ (#2 : Semiterm LX ℕ 4) #0
              ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 4)))))

/-- `Good(s, g)`. -/
noncomputable def goodAt {n : ℕ} (s g : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  Rew.subst ![s, g] ▹ goodBody

@[simp] theorem eval_goodAt {M : Type*} [Structure LX M] {n : ℕ}
    (s g : Semiterm LX ℕ n) (e : Fin n → M) (f : ℕ → M) :
    (goodAt s g).Eval e f ↔ goodBody.Eval ![s.val e f, g.val e f] f := by
  simp [goodAt]

/-! ## The cover, as an object-language statement -/

/--
**The cover with the case split already performed.**

`∀g ∀u ∀x (Eps(u,g) → x ≺₁ u → ∃s ∃n ∃w (Good(s,g) ∧ Tower(w,n,s) ∧ x ≺₁ w))`.

Pure arithmetic — no `X` — so it is transported from `IΣ₁` in one step.
-/
noncomputable def coverGoodStatement : Sentence LX :=
  (∀¹ ∀¹ ∀¹
    (∼(epsAt epsCode₁ (#1 : Semiterm LX ℕ 3) #2) ⋎
      (∼(precAt precCode₁ (#0 : Semiterm LX ℕ 3) #1) ⋎
        (∃¹ ∃¹ ∃¹
          (goodAt (#2 : Semiterm LX ℕ 6) #5 ⋏
            (towerAt towerCode₁ (#0 : Semiterm LX ℕ 6) #1 #2 ⋏
              precAt precCode₁ (#3 : Semiterm LX ℕ 6) #0)))))).univCl

def arithBaseAt {n : ℕ} (e : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![e] ▹ Rewriting.emb baseDef₁.val

def arithPrecAt {n : ℕ} (x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![x, y] ▹ Rewriting.emb precDef₁.val

def arithEpsAt {n : ℕ} (y g : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![y, g] ▹ Rewriting.emb epsDef₁.val

def arithAddAt {n : ℕ} (z x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, x, y] ▹ Rewriting.emb safeIadd₁Def.val

def arithTowerAt {n : ℕ} (u k c : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![u, k, c] ▹ Rewriting.emb towerDef₁.val

noncomputable def arithGoodBody : Semiformula ℒₒᵣ ℕ 2 :=
  (arithBaseAt ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 2) ⋏
      arithAddAt (#0 : Semiterm ℒₒᵣ ℕ 2) ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 2)
        ((gamma0Code 1 : ℕ) : Semiterm ℒₒᵣ ℕ 2)) ⋎
    (∃¹ ∃¹
      (arithPrecAt (#1 : Semiterm ℒₒᵣ ℕ 4) #3 ⋏
        (arithBaseAt (#0 : Semiterm ℒₒᵣ ℕ 4) ⋏
          (arithEpsAt (#0 : Semiterm ℒₒᵣ ℕ 4) #1 ⋏
            arithAddAt (#2 : Semiterm ℒₒᵣ ℕ 4) #0
              ((gamma0Code 1 : ℕ) : Semiterm ℒₒᵣ ℕ 4)))))

noncomputable def arithGoodAt {n : ℕ} (s g : Semiterm ℒₒᵣ ℕ n) :
    Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![s, g] ▹ arithGoodBody

/-- **`Good` is the transport of a purely arithmetical formula.**  This is what
makes its second-order image parameter-independent, hence `NoSetFvar`. -/
theorem goodBody_eq_lMap : Semiformula.lMap toLX arithGoodBody = goodBody := by
  simp [arithGoodBody, goodBody, arithBaseAt, arithPrecAt, arithEpsAt, arithAddAt,
    formulaAt, precAt, addAt, epsAt, baseCode₁, precCode₁, addCode₁, epsCode₁,
    liftCode, Semiformula.lMap_subst, lMap_numeral]

noncomputable def arithmeticCoverGoodStatement : ArithmeticSentence :=
  (∀¹ ∀¹ ∀¹
    (∼(arithEpsAt (#1 : Semiterm ℒₒᵣ ℕ 3) #2) ⋎
      (∼(arithPrecAt (#0 : Semiterm ℒₒᵣ ℕ 3) #1) ⋎
        (∃¹ ∃¹ ∃¹
          (arithGoodAt (#2 : Semiterm ℒₒᵣ ℕ 6) #5 ⋏
            (arithTowerAt (#0 : Semiterm ℒₒᵣ ℕ 6) #1 #2 ⋏
              arithPrecAt (#3 : Semiterm ℒₒᵣ ℕ 6) #0)))))).univCl

/-! ## The `IΣ₁` proof -/

theorem arithmetic_coverGood : 𝗜𝚺₁ ⊢ arithmeticCoverGoodStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp [arithmeticCoverGoodStatement, arithGoodAt, arithGoodBody, arithBaseAt,
    arithPrecAt, arithEpsAt, arithAddAt, arithTowerAt,
    eval_baseDef₁, eval_precDef₁, eval_epsDef₁, eval_towerDef₁,
    safeIadd₁_defined.iff, Structure.numeral_eq_numeral, numeral_eq_natCast,
    Rew.q_subst]
  intro a b x
  have hone : ((gamma0Code 1 : ℕ) : M) = vcVadd 0 0 1 0 := modelCode_one
  by_cases ha : isNF₁ a
  · by_cases hb : b = iepsilon a
    · by_cases hx : isNF₁ x
      · by_cases hxb : icmp₁ x b = 0
        · obtain ⟨e, n, he, hbase, hle, hcov⟩ := tower_cover hx
          rcases hbase with rfl | hfix
          · refine Or.inr (Or.inr (Or.inl ?_))
            rw [iadd₁_zero_left] at hcov
            rw [hone]
            exact ⟨isNF₁_one, hx, n, isNF₁_itower isNF₁_one n, hcov⟩
          · refine Or.inr (Or.inr (Or.inr ?_))
            have hbNF : isNF₁ b := by rw [hb]; exact isNF₁_iepsilon ha
            have heb : icmp₁ e b = 0 := by
              rcases hle with h' | h'
              · exact icmp₁_trans he hx hbNF h' hxb
              · rw [h']; exact hxb
            obtain ⟨h, hh, hhe, hhg⟩ := eps_mono_of_surj he hfix ha hb heb
            have hsNF : isNF₁ (iadd₁ e (vcVadd 0 0 1 0)) := isNF₁_succBase he (Or.inr hfix)
            have hs : safeIadd₁ (iepsilon h) ((gamma0Code 1 : ℕ) : M) =
                iadd₁ e (vcVadd 0 0 1 0) := by
              rw [← hhe, hone, safeIadd₁_of_nf he]
            refine ⟨h, ⟨⟨hh, ha, hhg⟩, ⟨?_, ?_⟩, hh⟩, ?_, hx, ?_⟩
            · rw [← hhe]; exact he
            · rw [← hhe]; exact Or.inr hfix
            · rw [hs]; exact hsNF
            · rw [hs]; exact ⟨n, isNF₁_itower hsNF n, hcov⟩
        · exact Or.inr (Or.inl (fun _ _ => hxb))
      · exact Or.inr (Or.inl (fun hxx _ => absurd hxx hx))
    · exact Or.inl (fun _ => hb)
  · exact Or.inl (fun haa => absurd haa ha)

/-! ## Transport to `PA[X]` -/

private lemma map_coverGood_body :
    Semiformula.lMap toLX
        (∀¹ ∀¹ ∀¹
          (∼(arithEpsAt (#1 : Semiterm ℒₒᵣ ℕ 3) #2) ⋎
            (∼(arithPrecAt (#0 : Semiterm ℒₒᵣ ℕ 3) #1) ⋎
              (∃¹ ∃¹ ∃¹
                (arithGoodAt (#2 : Semiterm ℒₒᵣ ℕ 6) #5 ⋏
                  (arithTowerAt (#0 : Semiterm ℒₒᵣ ℕ 6) #1 #2 ⋏
                    arithPrecAt (#3 : Semiterm ℒₒᵣ ℕ 6) #0)))))) =
      (∀¹ ∀¹ ∀¹
        (∼(epsAt epsCode₁ (#1 : Semiterm LX ℕ 3) #2) ⋎
          (∼(precAt precCode₁ (#0 : Semiterm LX ℕ 3) #1) ⋎
            (∃¹ ∃¹ ∃¹
              (goodAt (#2 : Semiterm LX ℕ 6) #5 ⋏
                (towerAt towerCode₁ (#0 : Semiterm LX ℕ 6) #1 #2 ⋏
                  precAt precCode₁ (#3 : Semiterm LX ℕ 6) #0)))))) := by
  simp [arithGoodAt, arithGoodBody, arithBaseAt, arithPrecAt, arithEpsAt, arithAddAt,
    arithTowerAt, goodAt, goodBody, formulaAt, precAt, addAt, towerAt, epsAt,
    baseCode₁, precCode₁, addCode₁, towerCode₁, epsCode₁, liftCode,
    Semiformula.lMap_subst, lMap_numeral, Rew.q_subst]

lemma models_coverGood_iff_arithmetic {M : Type*} [Nonempty M] [sLX : Structure LX M] :
    M↓[LX] ⊧ coverGoodStatement ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticCoverGoodStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [coverGoodStatement, arithmeticCoverGoodStatement, Semiformula.eval_univCl]
  rw [← map_coverGood_body]
  simp [Semiformula.eval_lMap]

/-- **The cover with the case split, in `PA[X]`.** -/
theorem concrete_coverGood : paLX ⊢ coverGoodStatement := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_coverGood)
  intro M _ _
  exact models_coverGood_iff_arithmetic

/-! ## Semantic form -/

theorem models_coverGoodStatement {M : Type*} [Nonempty M] [Structure LX M]
    [Structure.Eq LX M] :
    M↓[LX] ⊧ coverGoodStatement ↔
      ∀ f : ℕ → M, ∀ g u x : M,
        epsCode₁.Eval ![u, g] f →
        precCode₁.Eval ![x, u] f →
        ∃ s n w : M, goodBody.Eval ![s, g] f ∧
          towerCode₁.Eval ![w, n, s] f ∧ precCode₁.Eval ![x, w] f := by
  classical
  simp [models_iff, coverGoodStatement]
  constructor
  · intro h f g u x he hp
    rcases h f g u x with hne | hnp | hgoal
    · exact (hne he).elim
    · exact (hnp hp).elim
    · exact hgoal
  · intro h f g u x
    by_cases he : (Semiformula.Eval ![u, g] f) epsCode₁
    · by_cases hp : (Semiformula.Eval ![x, u] f) precCode₁
      · exact Or.inr (Or.inr (h f g u x he hp))
      · exact Or.inr (Or.inl hp)
    · exact Or.inl he

/-! ## The cover as a universal-hypothesis implication

The shape the second-order layer consumes: the `∃s∃n∃w` of `coverGoodStatement`
is replaced by a *universal hypothesis* about all `s, n, w`, so that the
second-order derivation never has to name a witness it does not have. -/

/-- The universal hypothesis `∀s ∀n ∀w (Good(s,g) → Tower(w,n,s) → x ≺₁ w → X(x))`,
at arbitrary terms for `g` and `x`. -/
noncomputable def hypBodyAt {n : ℕ} (g x : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  ∀¹ ∀¹ ∀¹
    (∼(goodAt (Rew.bShift (Rew.bShift (#0 : Semiterm LX ℕ (n + 1))))
        (Rew.bShift (Rew.bShift (Rew.bShift g)))) ⋎
      (∼(towerAt towerCode₁ (#0 : Semiterm LX ℕ (n + 3))
          (Rew.bShift (#0 : Semiterm LX ℕ (n + 2)))
          (Rew.bShift (Rew.bShift (#0 : Semiterm LX ℕ (n + 1))))) ⋎
        (∼(precAt precCode₁ (Rew.bShift (Rew.bShift (Rew.bShift x)))
            (#0 : Semiterm LX ℕ (n + 3))) ⋎
          Xat (Rew.bShift (Rew.bShift (Rew.bShift x))))))

/-- The universal hypothesis in the context `#2 = g`, `#1 = u`, `#0 = x`. -/
noncomputable def progHypBody : Semiformula LX ℕ 3 :=
  hypBodyAt (#2 : Semiterm LX ℕ 3) (#0 : Semiterm LX ℕ 3)

/--
**(COV), in the form (Prog) consumes it.**

`∀g ∀u ∀x (Eps(u,g) → x ≺₁ u →
    (∀s ∀n ∀w (Good(s,g) → Tower(w,n,s) → x ≺₁ w → X(x))) → X(x))`.
-/
noncomputable def progCoverBody : Semiformula LX ℕ 3 :=
  ∼(epsAt epsCode₁ (#1 : Semiterm LX ℕ 3) #2) ⋎
    (∼(precAt precCode₁ (#0 : Semiterm LX ℕ 3) #1) ⋎
      (∼progHypBody ⋎ Xat (#0 : Semiterm LX ℕ 3)))

noncomputable def progCoverStatement : Sentence LX := (∀¹ ∀¹ ∀¹ progCoverBody).univCl

theorem concrete_progCover : paLX ⊢ progCoverStatement := by
  classical
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  have hC : M↓[LX] ⊧ coverGoodStatement :=
    consequence_iff_eq'.mp (Theory.Proof.sound concrete_coverGood) M
  have hC' := models_coverGoodStatement.mp hC
  show M↓[LX] ⊧ (∀¹ ∀¹ ∀¹
    (∼(epsAt epsCode₁ (#1 : Semiterm LX ℕ 3) #2) ⋎
      (∼(precAt precCode₁ (#0 : Semiterm LX ℕ 3) #1) ⋎
        (∼progHypBody ⋎ Xat (#0 : Semiterm LX ℕ 3))))).univCl
  rw [models_iff]
  simp [progHypBody, hypBodyAt]
  intro f g u x
  by_cases hX : Idiom.Xrel M x
  · exact Or.inr (Or.inr (Or.inr hX))
  · by_cases he : (Semiformula.Eval ![u, g] f) epsCode₁
    · by_cases hp : (Semiformula.Eval ![x, u] f) precCode₁
      · refine Or.inr (Or.inr (Or.inl ?_))
        obtain ⟨s, n, w, hg, ht, hpw⟩ := hC' f g u x he hp
        exact ⟨s, hg, n, w, ht, hpw, hX⟩
      · exact Or.inr (Or.inl hp)
    · exact Or.inl he

/-! ## The successor step, packaged with transfinite induction -/

/--
**The successor step at a variable `Base`, with `TI` folded in.**

`∀e ∀s (Base(e) → Add(s,e,1̄) → TI(≺₁,X,e) → TI(≺₁,X,s))`.
-/
noncomputable def succTIBody : Semiformula LX ℕ 2 :=
  ∼(formulaAt baseCode₁ (#1 : Semiterm LX ℕ 2)) ⋎
    (∼(addAt addCode₁ (#0 : Semiterm LX ℕ 2) #1
        ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 2)) ⋎
      (∼(tiUptoAt precCode₁ (Xat (#0 : Semiterm LX ℕ 1)) (#1 : Semiterm LX ℕ 2)) ⋎
        tiUptoAt precCode₁ (Xat (#0 : Semiterm LX ℕ 1)) (#0 : Semiterm LX ℕ 2)))

noncomputable def succTIStatement : Sentence LX := (∀¹ ∀¹ succTIBody).univCl

theorem concrete_succTI : paLX ⊢ succTIStatement := by
  classical
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  have hS : M↓[LX] ⊧ succGeneralStatement :=
    consequence_iff_eq'.mp (Theory.Proof.sound concrete_succ_general) M
  have hS' := models_succGeneralStatement.mp hS
  show M↓[LX] ⊧ (∀¹ ∀¹
    (∼(formulaAt baseCode₁ (#1 : Semiterm LX ℕ 2)) ⋎
      (∼(addAt addCode₁ (#0 : Semiterm LX ℕ 2) #1
          ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 2)) ⋎
        (∼(tiUptoAt precCode₁ (Xat (#0 : Semiterm LX ℕ 1)) (#1 : Semiterm LX ℕ 2)) ⋎
          tiUptoAt precCode₁ (Xat (#0 : Semiterm LX ℕ 1)) (#0 : Semiterm LX ℕ 2))))).univCl
  rw [models_iff]
  simp only [Semiformula.eval_univCl, Semiformula.eval_all,
    LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq,
    eval_formulaAt, eval_addAt, eval_tiUptoAt, Semiterm.val_bvar,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  intro f e s
  by_cases hb : (Semiformula.Eval ![e] f) baseCode₁
  · by_cases ha : (Semiformula.Eval
        ![s, e, Semiterm.val ![s, e] f ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 2)] f) addCode₁
    · have hnum : Semiterm.val ![s, e] f ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 2) =
          Semiterm.val ![] f ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 0) := by simp
      rw [hnum] at ha
      refine Or.inr (Or.inr ?_)
      rw [or_iff_not_imp_left]
      intro hnn
      have hti := not_not.mp hnn
      intro hProg y hy
      rcases hS' f e s y hb ha hy with hlt | heq
      · exact hti hProg y hlt
      · rw [heq]
        exact hProg e (hti hProg)
    · exact Or.inr (Or.inl ha)
  · exact Or.inl hb

/-! ## The value of the internal ε-function at a standard code -/

theorem iepsilon_gamma0ModelCode (c : Gamma0Note) :
    iepsilon (gamma0ModelCode (V := V) c) = gamma0ModelCode (V := V) (epsilonNote c) := by
  rw [← iveblen_one, ← modelCode_one, iveblen_gamma0ModelCode]
  rfl

noncomputable def epsValueStatement (c : Gamma0Note) : Sentence LX :=
  (epsAt epsCode₁ (gamma0Term (epsilonNote c)) (gamma0Term c)).univCl

noncomputable def arithmeticEpsValueStatement (c : Gamma0Note) : ArithmeticSentence :=
  (arithEpsAt ((gamma0Code (epsilonNote c) : ℕ) : Semiterm ℒₒᵣ ℕ 0)
    ((gamma0Code c : ℕ) : Semiterm ℒₒᵣ ℕ 0)).univCl

theorem arithmetic_epsValue (c : Gamma0Note) : 𝗜𝚺₁ ⊢ arithmeticEpsValueStatement c := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp [arithmeticEpsValueStatement, arithEpsAt, eval_epsDef₁,
    Structure.numeral_eq_numeral, numeral_eq_natCast]
  exact ⟨isNF₁_gamma0ModelCode c, (iepsilon_gamma0ModelCode (V := M) c).symm⟩

private lemma map_epsValue_body (c : Gamma0Note) :
    Semiformula.lMap toLX
        (arithEpsAt ((gamma0Code (epsilonNote c) : ℕ) : Semiterm ℒₒᵣ ℕ 0)
          ((gamma0Code c : ℕ) : Semiterm ℒₒᵣ ℕ 0)) =
      epsAt epsCode₁ (gamma0Term (epsilonNote c)) (gamma0Term c) := by
  simp [arithEpsAt, epsAt, epsCode₁, liftCode, gamma0Term, Semiformula.lMap_subst]
  rw [lMap_numeral (gamma0Code (epsilonNote c)), lMap_numeral (gamma0Code c)]

lemma models_epsValue_iff_arithmetic {M : Type*} [Nonempty M] [sLX : Structure LX M]
    (c : Gamma0Note) :
    M↓[LX] ⊧ epsValueStatement c ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticEpsValueStatement c := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [epsValueStatement, arithmeticEpsValueStatement, Semiformula.eval_univCl]
  constructor
  · intro h f
    apply Semiformula.eval_lMap.mp
    rw [map_epsValue_body]
    exact h f
  · intro h f
    rw [← map_epsValue_body]
    exact Semiformula.eval_lMap.mpr (h f)

/-- **`ε̄_c` is the internal ε-value of `c̄`, in `PA[X]`.** -/
theorem concrete_epsValue (c : Gamma0Note) : paLX ⊢ epsValueStatement c := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl (arithmetic_epsValue c))
  intro M _ _
  exact models_epsValue_iff_arithmetic c

end OrdinalAnalysis.Gentzen.ProgStep
