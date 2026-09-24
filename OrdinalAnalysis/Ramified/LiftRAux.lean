/-
  The vocabulary of the ramified upper bound, read inside a model, and the
  facts of `PA[X]` it uses, lifted into that model.

  Throughout, `M` is a model of `RAlt ν` (with true equality, where the lifting
  needs it).  The coded Veblen ordering and its graphs are arithmetical, so in
  `M` they are relations on `M` read off its arithmetic: `precM` (`y ≺₁ x`),
  `towerM` (`Tower(u, k, c)`), `omegaPowM`, `addM`, `epsM` (`Eps(u, g)`),
  `baseM`, and `goodM` (the case split of the ε-cover).  For a predicate `P`
  on `M`, `ProgM P`, `TIupM P a` and `JumpM P` are progressiveness, transfinite
  induction below `a`, and Gentzen's jump.

  `Ramified/LiftR.lean` shows that `lxStr P` models `PA[X]` whenever `P` is
  definable by a formula of level `< ν` (`DefinableLt ν P`).  The facts below
  are the theorems of `PA[X]` the argument consumes, each read in `lxStr P`:

  * `towerM_zero`, `towerM_succ` — the two laws of the internal ω-tower;
  * `jumpB_M` — Gentzen's Lemma B at `P`: `TI(Jump P, a) → TI(P, ω^a)`;
  * `cover_M` — the cover of the segment below `ε_g` by towers over good bases;
  * `succTI_M` — transfinite induction passes from a base `e` to `e + 1`;
  * `tiUp_code` — Gentzen's bound: `TI(P, c̄)` for every external `c < ε₀`;
  * `not_precM_zero`, `precM_trans`, `precM_code`, `epsM_code` — arithmetic of
    the ordering at standard codes.

  Besides these, `indM` is the induction scheme of `RAlt ν` read in `M`, and
  `comprM` is comprehension with a same-level parameter
  (`Ramified/Comprehension.lean`) read in `M`.
-/
import OrdinalAnalysis.Ramified.LiftR
import OrdinalAnalysis.Gentzen.ProgStep
import OrdinalAnalysis.Gentzen.VeblenEpsilon0UpperBound

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen (LX paLX)
open OrdinalAnalysis.Gentzen.CodedNotation (liftCode)
open OrdinalAnalysis.Gentzen.InternalVNote (precDef₁)
open OrdinalAnalysis.Gentzen.InternalVNoteJump (safeIadd₁Def)
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁)
open OrdinalAnalysis.Gentzen.CodedVeblenJump (addCode₁ omegaPowCode₁ omegaPowDef₁)
open OrdinalAnalysis.Gentzen.VeblenTower (towerCode₁ towerDef₁)
open OrdinalAnalysis.Gentzen.InternalEpsMonoCode (epsCode₁ epsDef₁)
open OrdinalAnalysis.Gentzen.VeblenSuccStep (baseCode₁ baseDef₁)

section Vocabulary

variable {M : Type} [s : Structure LRA M]

/-- An arithmetical semisentence, evaluated in the arithmetic of `M`. -/
def arEval {k : ℕ} (σ : ArithmeticSemisentence k) (v : Fin k → M) : Prop :=
  Semiformula.Evalb (s := s.lMap toLRA) v σ

theorem eval_liftCode_lxStr (P : M → Prop) {k : ℕ} (σ : ArithmeticSemisentence k)
    (v : Fin k → M) (f : ℕ → M) :
    Semiformula.Eval (s := lxStr P) v f (liftCode σ) ↔ arEval σ v := by
  rw [liftCode, Semiformula.eval_lMap]
  exact Semiformula.eval_emb (s := s.lMap toLRA) σ

/-- `y ≺₁ x` in `M`. -/
def precM (y x : M) : Prop := arEval precDef₁.val ![y, x]

/-- `Tower(u, k, c)` in `M`. -/
def towerM (u k c : M) : Prop := arEval towerDef₁.val ![u, k, c]

/-- `OmegaPow(z, a)` in `M`. -/
def omegaPowM (z a : M) : Prop := arEval omegaPowDef₁.val ![z, a]

/-- `Add(z, x, y)` in `M`. -/
def addM (z x y : M) : Prop := arEval safeIadd₁Def.val ![z, x, y]

/-- `Eps(u, g)` in `M`. -/
def epsM (u g : M) : Prop := arEval epsDef₁.val ![u, g]

/-- `Base(e)` in `M`. -/
def baseM (e : M) : Prop := arEval baseDef₁.val ![e]

@[simp] theorem eval_precCode₁_lxStr (P : M → Prop) (y x : M) (f : ℕ → M) :
    Semiformula.Eval (s := lxStr P) ![y, x] f precCode₁ ↔ precM y x :=
  eval_liftCode_lxStr P _ _ f

@[simp] theorem eval_towerCode₁_lxStr (P : M → Prop) (u k c : M) (f : ℕ → M) :
    Semiformula.Eval (s := lxStr P) ![u, k, c] f towerCode₁ ↔ towerM u k c :=
  eval_liftCode_lxStr P _ _ f

@[simp] theorem eval_omegaPowCode₁_lxStr (P : M → Prop) (z a : M) (f : ℕ → M) :
    Semiformula.Eval (s := lxStr P) ![z, a] f omegaPowCode₁ ↔ omegaPowM z a :=
  eval_liftCode_lxStr P _ _ f

@[simp] theorem eval_addCode₁_lxStr (P : M → Prop) (z x y : M) (f : ℕ → M) :
    Semiformula.Eval (s := lxStr P) ![z, x, y] f addCode₁ ↔ addM z x y :=
  eval_liftCode_lxStr P _ _ f

@[simp] theorem eval_epsCode₁_lxStr (P : M → Prop) (u g : M) (f : ℕ → M) :
    Semiformula.Eval (s := lxStr P) ![u, g] f epsCode₁ ↔ epsM u g :=
  eval_liftCode_lxStr P _ _ f

@[simp] theorem eval_baseCode₁_lxStr (P : M → Prop) (e : M) (f : ℕ → M) :
    Semiformula.Eval (s := lxStr P) ![e] f baseCode₁ ↔ baseM e :=
  eval_liftCode_lxStr P _ _ f

@[simp] theorem eval_Xat_lxStr (P : M → Prop) {n : ℕ} (t : Semiterm LX ℕ n) (e : Fin n → M)
    (f : ℕ → M) :
    Semiformula.Eval (s := lxStr P) e f (Gentzen.Xat t) ↔
      P (Semiterm.val (s := lxStr P) e f t) := Iff.rfl

@[simp] theorem xrel_lxStr (P : M → Prop) (x : M) :
    @Gentzen.Idiom.Xrel M (lxStr P) x ↔ P x := Iff.rfl

@[simp] theorem val_numeral_lxStr (P : M → Prop) {n : ℕ} (e : Fin n → M) (f : ℕ → M) (k : ℕ) :
    Semiterm.val (s := lxStr P) e f ((k : ℕ) : Semiterm LX ℕ n) = numVal M k := by
  rw [← Gentzen.OmegaTower.lMap_numeral, Semiterm.val_lMap]
  exact val_numeral_reduct e f k

/-- The successor function of `M`. -/
def succM (x : M) : M := Semiterm.val (s := s) ![x] (fun _ => x) (‘(#0 + 1)’ : Semiterm LRA ℕ 1)

theorem val_succ_LRA (x : M) (f : ℕ → M) :
    Semiterm.val (s := s) ![x] f (‘(#0 + 1)’ : Semiterm LRA ℕ 1) = succM x := by
  simp [succM, Semiterm.val_operator]

@[simp] theorem val_succ_lxStr (P : M → Prop) (x : M) (f : ℕ → M) :
    Semiterm.val (s := lxStr P) ![x] f (‘(#0 + 1)’ : Semiterm LX ℕ 1) = succM x := by
  rw [val_lxStr, lMap_succ_LX, val_succ_LRA]

/-- `P` is progressive along `≺₁` in `M`. -/
def ProgM (P : M → Prop) : Prop := ∀ x, (∀ y, precM y x → P y) → P x

/-- Transfinite induction for `P` along `≺₁` below `a`, in `M`. -/
def TIupM (P : M → Prop) (a : M) : Prop := ProgM P → ∀ y, precM y a → P y

/-- Gentzen's jump of `P`, in `M`. -/
def JumpM (P : M → Prop) (a : M) : Prop :=
  ∀ b u z : M, omegaPowM u a → addM z b u → (∀ y, precM y b → P y) → ∀ y, precM y z → P y

@[simp] theorem eval_tiUptoAt_Xat_lxStr (P : M → Prop) {n : ℕ} (a : Semiterm LX ℕ n)
    (e : Fin n → M) (f : ℕ → M) :
    Semiformula.Eval (s := lxStr P) e f
        (Gentzen.tiUptoAt precCode₁ (Gentzen.Xat (#0 : Semiterm LX ℕ 1)) a) ↔
      TIupM P (Semiterm.val (s := lxStr P) e f a) := by
  simp [Gentzen.eval_tiUptoAt, TIupM, ProgM]

theorem eval_jump_lxStr (P : M → Prop) (a : M) (f : ℕ → M) :
    Semiformula.Eval (s := lxStr P) ![a] f
        (Gentzen.jump precCode₁ addCode₁ omegaPowCode₁ (Gentzen.Xat (#0 : Semiterm LX ℕ 1))) ↔
      JumpM P a := by
  simp [Gentzen.eval_jump, JumpM]

/-- The code of `1`, in `M`. -/
noncomputable def oneM : M := numVal M (Gentzen.VNoteBridge.gamma0Code 1)

/-- `Good(s, g)` in `M`: `s = 0 + 1`, or `s = e + 1` with `e = ε_h` for some `h ≺₁ g`. -/
def goodM (s₀ g : M) : Prop :=
  (baseM (numVal M 0) ∧ addM s₀ (numVal M 0) oneM) ∨
    ∃ h e : M, precM h g ∧ baseM e ∧ epsM e h ∧ addM s₀ e oneM

theorem eval_goodBody_lxStr (P : M → Prop) (s₀ g : M) (f : ℕ → M) :
    Semiformula.Eval (s := lxStr P) ![s₀, g] f Gentzen.ProgStep.goodBody ↔ goodM s₀ g := by
  simp only [Gentzen.ProgStep.goodBody, goodM, oneM, Semiformula.eval_all, Semiformula.eval_ex, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_and, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.and_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, Gentzen.eval_precAt,
    Gentzen.eval_formulaAt, Gentzen.eval_addAt, Gentzen.eval_omegaPowAt,
    Gentzen.InternalEpsMonoCode.eval_epsAt, Semiterm.val_bvar, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, val_numeral_lxStr, eval_precCode₁_lxStr, eval_addCode₁_lxStr,
    eval_baseCode₁_lxStr, eval_epsCode₁_lxStr, eval_omegaPowCode₁_lxStr, eval_towerCode₁_lxStr]

end Vocabulary

/-! ### Definable predicates and the lifted `PA[X]` facts -/

section Lifted

variable {M : Type} [s : Structure LRA M] {ν : Lv}

/-- `P` is defined in `M`, with parameters, by a formula of level `< ν`. -/
def DefinableLt (ν : Lv) (P : M → Prop) : Prop :=
  ∃ B : Semiformula LRA ℕ 1, lvlOf B < ν ∧ ∃ fB : ℕ → M,
    ∀ x, P x ↔ Semiformula.Eval (s := s) ![x] fB B

theorem definableLt_top [Nonempty M] (hν : 1 ≤ ν) : DefinableLt (M := M) ν (fun _ => True) :=
  ⟨⊤, by rw [lvlOf_verum]; exact lt_of_lt_of_le Gamma0Note.zero_lt_one hν,
    fun _ => Classical.arbitrary M, fun _ => by simp⟩

theorem definableLt_mem {μ : Lv} (hμ : μ < ν) (z : M) :
    DefinableLt (M := M) ν (fun x => memM μ x z) :=
  ⟨memAt μ (#0 : Semiterm LRA ℕ 1) &0, by rw [lvlOf_memAt]; exact hμ, fun _ => z,
    fun x => by rw [eval_memAt]; rfl⟩

/-- **The lifting**, at a definable predicate. -/
theorem lift_models [Nonempty M] [Structure.Eq LRA M] {P : M → Prop} (hM : M↓[LRA] ⊧* RAlt ν) (hP : DefinableLt ν P)
    {σ : Sentence LX} (h : paLX ⊢ σ) : letI := lxStr P; M↓[LX] ⊧ σ := by
  obtain ⟨B, hB, fB, hPB⟩ := hP
  exact models_of_paLX hM B hB fB P hPB h

variable [Nonempty M] [Structure.Eq LRA M] (hM : M↓[LRA] ⊧* RAlt ν) (hν : 1 ≤ ν)
include hM hν

omit [Structure.Eq LRA M] hν in
/-- **Induction in `M`** for a formula of level `< ν`. -/
theorem indM (φ : Semiformula LRA ℕ 1) (hφ : lvlOf φ < ν) (f : ℕ → M)
    (h0 : Semiformula.Eval (s := s) ![numVal M 0] f φ)
    (hs : ∀ x, Semiformula.Eval (s := s) ![x] f φ → Semiformula.Eval (s := s) ![succM x] f φ) :
    ∀ x, Semiformula.Eval (s := s) ![x] f φ := by
  have hax : M↓[LRA] ⊧ Semiformula.univCl (succInd φ) :=
    Semantics.modelsSet_iff.mp hM (induction_mem_RAlt φ hφ)
  rw [models_iff_proposition] at hax
  have H := (eval_succInd_iff φ f).mp (hax f)
  have hz : Semiterm.val (s := s) ![] f ((0 : ℕ) : Semiterm LRA ℕ 0) = numVal M 0 :=
    val_numAtR_model ![] f 0
  rw [hz] at H
  simp only [val_succ_LRA] at H
  exact H h0 hs

omit [Structure.Eq LRA M] hν in
/-- **Comprehension in `M`**, at a level `0 < μ < ν`. -/
theorem comprM {μ : Lv} (h0 : 0 < μ) (hμ : μ < ν) {A : Semiformula LRA ℕ 1} (hA : Shape μ A)
    (z : M) : ∃ w : M, ∀ x : M, memM μ x w ↔ Semiformula.Eval (s := s) ![x] (fun _ => z) A := by
  have H : M↓[LRA] ⊧ Semiformula.univCl (compr μ A) :=
    consequence_iff.mp (Theory.Proof.sound (exists_comprehension_code_lt h0 hμ hA)) M hM
  rw [models_iff_proposition] at H
  exact (eval_compr μ A _).mp (H (fun _ => z)) z

theorem towerM_zero {c u : M} (h : towerM u (numVal M 0) c) : u = c := by
  let _ : Structure LX M := lxStr (fun _ => True)
  have _ : Structure.Eq LX M := lxStr_eq _
  have H := lift_models hM (definableLt_top hν) Gentzen.VeblenTower.concrete_towerZero
  have H' := (Gentzen.VeblenTower.models_towerZeroStatement towerCode₁).mp H
    (fun _ => Classical.arbitrary M) c u
  simp only [val_numeral_lxStr, eval_towerCode₁_lxStr] at H'
  exact H' h

theorem towerM_succ {c k u : M} (h : towerM u (succM k) c) :
    ∃ v, towerM v k c ∧ omegaPowM u v := by
  let _ : Structure LX M := lxStr (fun _ => True)
  have H := lift_models hM (definableLt_top hν) Gentzen.VeblenTower.concrete_towerSucc
  have H' := (Gentzen.VeblenTower.models_towerSuccStatement omegaPowCode₁ towerCode₁).mp H
    (fun _ => Classical.arbitrary M) c k u
  simp only [val_succ_lxStr, eval_towerCode₁_lxStr, eval_omegaPowCode₁_lxStr] at H'
  exact H' h

theorem not_precM_zero (x : M) : ¬ precM x (numVal M 0) := by
  let _ : Structure LX M := lxStr (fun _ => True)
  have H := lift_models hM (definableLt_top hν) Gentzen.CodedVeblenJump.noPredZero₁
  rw [Gentzen.noPredZeroStatement, models_iff_proposition] at H
  have H' := H (fun _ => Classical.arbitrary M)
  simp only [Semiformula.Evalf, Semiformula.eval_all, Semiformula.eval_ex, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_and, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.and_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, Gentzen.eval_precAt,
    Gentzen.eval_formulaAt, Gentzen.eval_addAt, Gentzen.eval_omegaPowAt,
    Gentzen.InternalEpsMonoCode.eval_epsAt, Semiterm.val_bvar, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, val_numeral_lxStr, eval_precCode₁_lxStr, eval_addCode₁_lxStr,
    eval_baseCode₁_lxStr, eval_epsCode₁_lxStr, eval_omegaPowCode₁_lxStr, eval_towerCode₁_lxStr] at H'
  exact H' x

theorem precM_trans {a b c : M} (hab : precM a b) (hbc : precM b c) : precM a c := by
  let _ : Structure LX M := lxStr (fun _ => True)
  have H := lift_models hM (definableLt_top hν) Gentzen.Epsilon1UpperBound.concrete_precTrans₁
  have H' := (Gentzen.Order.models_precTransStatement precCode₁).mp H
    (fun _ => Classical.arbitrary M) a b c
  simp only [eval_precCode₁_lxStr] at H'
  exact H' hab hbc

theorem precM_code {a b : Gamma0Note} (h : a < b) :
    precM (numVal M (Gentzen.VNoteBridge.gamma0Code a))
      (numVal M (Gentzen.VNoteBridge.gamma0Code b)) := by
  let _ : Structure LX M := lxStr (fun _ => True)
  have H := lift_models hM (definableLt_top hν) (Gentzen.Epsilon1UpperBound.concrete_gamma0_prec h)
  rw [Gentzen.Epsilon1UpperBound.closedPrec₁, models_iff_proposition] at H
  have H' := H (fun _ => Classical.arbitrary M)
  simpa only [Semiformula.Evalf, Gentzen.Epsilon1UpperBound.gamma0Term, Semiformula.eval_all, Semiformula.eval_ex, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_and, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.and_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, Gentzen.eval_precAt,
    Gentzen.eval_formulaAt, Gentzen.eval_addAt, Gentzen.eval_omegaPowAt,
    Gentzen.InternalEpsMonoCode.eval_epsAt, Semiterm.val_bvar, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, val_numeral_lxStr, eval_precCode₁_lxStr, eval_addCode₁_lxStr,
    eval_baseCode₁_lxStr, eval_epsCode₁_lxStr, eval_omegaPowCode₁_lxStr, eval_towerCode₁_lxStr] using H'

theorem epsM_code (c : Gamma0Note) :
    epsM (numVal M (Gentzen.VNoteBridge.gamma0Code (Gamma0Note.epsilonNote c)))
      (numVal M (Gentzen.VNoteBridge.gamma0Code c)) := by
  let _ : Structure LX M := lxStr (fun _ => True)
  have H := lift_models hM (definableLt_top hν) (Gentzen.ProgStep.concrete_epsValue c)
  rw [Gentzen.ProgStep.epsValueStatement, models_iff_proposition] at H
  have H' := H (fun _ => Classical.arbitrary M)
  simpa only [Semiformula.Evalf, Gentzen.Epsilon1UpperBound.gamma0Term, Semiformula.eval_all, Semiformula.eval_ex, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_and, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.and_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, Gentzen.eval_precAt,
    Gentzen.eval_formulaAt, Gentzen.eval_addAt, Gentzen.eval_omegaPowAt,
    Gentzen.InternalEpsMonoCode.eval_epsAt, Semiterm.val_bvar, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, val_numeral_lxStr, eval_precCode₁_lxStr, eval_addCode₁_lxStr,
    eval_baseCode₁_lxStr, eval_epsCode₁_lxStr, eval_omegaPowCode₁_lxStr, eval_towerCode₁_lxStr] using H'

theorem cover_M {g u x : M} (he : epsM u g) (hx : precM x u) :
    ∃ s₀ n w : M, goodM s₀ g ∧ towerM w n s₀ ∧ precM x w := by
  let _ : Structure LX M := lxStr (fun _ => True)
  have _ : Structure.Eq LX M := lxStr_eq _
  have H := lift_models hM (definableLt_top hν) Gentzen.ProgStep.concrete_coverGood
  have H' := Gentzen.ProgStep.models_coverGoodStatement.mp H (fun _ => Classical.arbitrary M) g u x
  simp only [eval_epsCode₁_lxStr, eval_precCode₁_lxStr, eval_goodBody_lxStr,
    eval_towerCode₁_lxStr] at H'
  exact H' he hx

variable {P : M → Prop} (hP : DefinableLt ν P)
include hP

omit hν in
theorem jumpB_M {a u : M} (hω : omegaPowM u a) (hJ : TIupM (JumpM P) a) : TIupM P u := by
  let _ : Structure LX M := lxStr P
  have H := lift_models hM hP (Gentzen.CodedVeblenJump.jumpB₁ (Gentzen.Xat (#0 : Semiterm LX ℕ 1)))
  rw [Gentzen.jumpBStatement, models_iff_proposition] at H
  have H' := H (fun _ => Classical.arbitrary M)
  simp only [Semiformula.Evalf, eval_tiUptoAt_Xat_lxStr, Gentzen.eval_tiUptoAt, Semiformula.eval_all, Semiformula.eval_ex, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_and, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.and_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, Gentzen.eval_precAt,
    Gentzen.eval_formulaAt, Gentzen.eval_addAt, Gentzen.eval_omegaPowAt,
    Gentzen.InternalEpsMonoCode.eval_epsAt, Semiterm.val_bvar, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, val_numeral_lxStr, eval_precCode₁_lxStr, eval_addCode₁_lxStr,
    eval_baseCode₁_lxStr, eval_epsCode₁_lxStr, eval_omegaPowCode₁_lxStr, eval_towerCode₁_lxStr] at H'
  rcases H' a u with h1 | h2 | h3
  · exact absurd hω h1
  · refine absurd ?_ h2
    intro hprog y hy
    have hprog' : ProgM (JumpM P) := fun x hx =>
      (eval_jump_lxStr P x _).mp (hprog x fun y hy => (eval_jump_lxStr P y _).mpr (hx y hy))
    exact (eval_jump_lxStr P y _).mpr (hJ hprog' y hy)
  · exact h3

omit hν in
theorem succTI_M {e s₀ : M} (hb : baseM e) (ha : addM s₀ e oneM) (hti : TIupM P e) :
    TIupM P s₀ := by
  let _ : Structure LX M := lxStr P
  have H := lift_models hM hP Gentzen.ProgStep.concrete_succTI
  rw [Gentzen.ProgStep.succTIStatement, models_iff_proposition] at H
  have H' := H (fun _ => Classical.arbitrary M)
  simp only [Semiformula.Evalf, Gentzen.ProgStep.succTIBody, eval_tiUptoAt_Xat_lxStr, Semiformula.eval_all, Semiformula.eval_ex, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_and, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.and_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, Gentzen.eval_precAt,
    Gentzen.eval_formulaAt, Gentzen.eval_addAt, Gentzen.eval_omegaPowAt,
    Gentzen.InternalEpsMonoCode.eval_epsAt, Semiterm.val_bvar, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, val_numeral_lxStr, eval_precCode₁_lxStr, eval_addCode₁_lxStr,
    eval_baseCode₁_lxStr, eval_epsCode₁_lxStr, eval_omegaPowCode₁_lxStr, eval_towerCode₁_lxStr] at H'
  rcases H' e s₀ with h1 | h2 | h3 | h4
  · exact absurd hb h1
  · exact absurd ha h2
  · exact absurd hti h3
  · exact h4

omit hν in
theorem tiUp_code {c : Gamma0Note} (hc : c < Gamma0Note.epsilonNote 0) :
    TIupM P (numVal M (Gentzen.VNoteBridge.gamma0Code c)) := by
  let _ : Structure LX M := lxStr P
  have H := lift_models hM hP
    (Gentzen.VeblenEpsilon0UpperBound.concrete_eps0_ti c hc (Gentzen.Xat (#0 : Semiterm LX ℕ 1)))
  rw [Gentzen.Epsilon1UpperBound.closedTI₁, models_iff_proposition] at H
  have H' := H (fun _ => Classical.arbitrary M)
  simpa only [Semiformula.Evalf, Gentzen.Epsilon1UpperBound.gamma0Term, eval_tiUptoAt_Xat_lxStr,
    val_numeral_lxStr] using H'

end Lifted

end Ramified

end OrdinalAnalysis
