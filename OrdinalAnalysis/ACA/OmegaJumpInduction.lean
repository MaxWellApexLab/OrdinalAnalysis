/-
  The tower-depth induction along the columns of an omega-jump.

  Let `Y` be the omega-jump of a set `Z` (`ACA/OmegaJump.lean`): reading `Y` as a
  sequence of columns `col_k Y := {x | ⟪k, x⟫ ∈ Y}`, column `0` is `Z` and column
  `k + 1` is Gentzen's jump of column `k`.  Gentzen's Lemma B (`jumpB_column`) turns
  `TI(Jump(col_k Y), a)` into `TI(col_k Y, ω^a)`; iterating it `n` times along the
  columns gives, for a tower `u = ω_n(c)` of height `n` over `c`,

      (∀j TI(col_j Y, c)) → (∀j TI(col_j Y, u)).

  The induction on the height `n` cannot be carried by the formula
  `∀²X TI(c, X) → ∀²X TI(u, X)` of `ACA/TowerInduction.lean` without the full
  second-order induction scheme; here the induction formula quantifies over the
  column index `j` instead, and is *arithmetical in `Y`*.  This is the point of
  the omega-jump: the columns of a single set carry the whole jump hierarchy.

  The argument is carried out in `PA[X]` with the fresh predicate `X` standing for
  `Y`, with the step condition of the omega-jump (`OmegaJump.lean`'s
  `hierStepColLX`, closed over `k` and `x`) as an *object-language hypothesis*
  `stepHypLX`.  Its content is proved semantically (`Theory.Proof.complete`), in
  the style of `ACA/TowerInduction.lean`'s `concrete_towerStepTI`: in a model of
  `PA[X]`, induction on the height (`Idiom.paLX_induction`) with the tower laws
  (`VeblenTower.concrete_towerZero`/`concrete_towerSucc`), Lemma B for the columns
  (`OmegaJumpTower.jumpB_column`), and the step condition to replace
  `col_{k+1} Y` by `Jump(col_k Y)`.  The Lean-level form `colTower_sem` is reused
  by the progressiveness argument (`ACA/OmegaJumpProg.lean`).

  The second part of the file records that the omega-jump axiom
  `∀Z ∃Y IsOmegaJump(Y, Z)` has no free variable of either kind, so that the
  eigenvariable rules are available over `ACAplus`/`ACAplus₀`, and lifts the tower
  statement.  In the second-order syntax the innermost `∀²`/`∃²` binds the bound set
  slot `0`; `OmegaJump.lean`'s `IsOmegaJump` has `Y` at slot `0` (bound by the inner
  `∃²`) and `Z` at slot `1` (bound by the outer `∀²`).  The truth of the axiom in the
  full ω-model is `ACA/OmegaJumpSound.lean`.
-/
import OrdinalAnalysis.ACA.OmegaJumpDepth

set_option autoImplicit false

namespace OrdinalAnalysis.ACA.ColumnTower

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁ freeVariables_precCode₁)
open OrdinalAnalysis.Gentzen.CodedVeblenJump (addCode₁ omegaPowCode₁)

/-! ### Transfinite induction for a column, with the column index a term -/

/-- `Below(col_j, b)`: every `y ≺₁ b` lies in column `j`. -/
def belowColAt {n : ℕ} (j b : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  ∀¹ (∼(precAt precCode₁ (#0 : Semiterm LX ℕ (n + 1)) (Rew.bShift b)) ⋎
    OrdinalAnalysis.ACA.columnXat (Rew.bShift j) (#0 : Semiterm LX ℕ (n + 1)))

/-- `Prog(col_j)`: column `j` is `≺₁`-progressive. -/
def progColAt {n : ℕ} (j : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  ∀¹ (∼(belowColAt (Rew.bShift j) (#0 : Semiterm LX ℕ (n + 1))) ⋎
    OrdinalAnalysis.ACA.columnXat (Rew.bShift j) (#0 : Semiterm LX ℕ (n + 1)))

/-- `TI(col_j, a) :≡ Prog(col_j) → Below(col_j, a)`. -/
def tiColAt {n : ℕ} (j a : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  ∼(progColAt j) ⋎ belowColAt j a

/-- `∀j TI(col_j, a)`: transfinite induction up to `a` for every column. -/
def allColTI {n : ℕ} (a : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  ∀¹ (tiColAt (#0 : Semiterm LX ℕ (n + 1)) (Rew.bShift a))

/-- The step condition of an omega-jump, closed over the column index and the
point: `∀k ∀x (x ∈ col_{k+1} X ↔ Jump(col_k X)(x))`. -/
def stepHypLX : Semiformula LX ℕ 0 := ∀¹ ∀¹ OrdinalAnalysis.ACA.hierStepColLX

/-- The tower-depth induction formula, with `#0 = n`:
`∀c ∀u (Tower(u,n,c) → ∀j TI(col_j,c) → ∀j TI(col_j,u))`. -/
def depthFormula : Semiformula LX ℕ 1 :=
  ∀¹ ∀¹ (∼(VeblenTower.towerAt VeblenTower.towerCode₁ (#0 : Semiterm LX ℕ 3) #2 #1) ⋎
    (∼(allColTI (#1 : Semiterm LX ℕ 3)) ⋎ allColTI (#0 : Semiterm LX ℕ 3)))

/-- The matrix of the tower statement, `#0 = u`, `#1 = n`, `#2 = c`. -/
def colTowerBody : Semiformula LX ℕ 3 :=
  ∼(VeblenTower.towerAt VeblenTower.towerCode₁ (#0 : Semiterm LX ℕ 3) #1 #2) ⋎
    (∼(allColTI (#2 : Semiterm LX ℕ 3)) ⋎ allColTI (#0 : Semiterm LX ℕ 3))

/-- **The tower-depth induction along the columns**, as a sentence of `PA[X]`:
if the columns of `X` satisfy the omega-jump step condition, then
`∀c ∀n ∀u (Tower(u,n,c) → ∀j TI(col_j,c) → ∀j TI(col_j,u))`. -/
def colTowerStatement : Sentence LX := (∼stepHypLX ⋎ (∀¹ ∀¹ ∀¹ colTowerBody)).univCl

/-! ### Closedness -/

theorem freeVariables_rew_subset {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂)
    {φ : Semiformula LX ℕ n₁} {S : Finset ℕ}
    (hb : ∀ i : Fin n₁, (ω #i).freeVariables ⊆ S)
    (hf : ∀ z ∈ φ.freeVariables, (ω &z).freeVariables ⊆ S) :
    (ω ▹ φ).freeVariables ⊆ S := by
  intro x hx
  rcases Semiformula.fvar?_rew (ω := ω) (φ := φ) (x := x) hx with ⟨i, hi⟩ | ⟨z, hz, hx'⟩
  · exact hb i hi
  · exact hf z hz hx'

theorem freeVariables_subst_subset {k n : ℕ} (v : Fin k → Semiterm LX ℕ n)
    {φ : Semiformula LX ℕ k} {S : Finset ℕ} (hv : ∀ i, (v i).freeVariables ⊆ S)
    (hφ : φ.freeVariables ⊆ S) : (Rew.subst v ▹ φ).freeVariables ⊆ S := by
  refine freeVariables_rew_subset _ (fun i => by simpa using hv i) (fun z hz => ?_)
  simpa using hφ hz

@[simp] theorem freeVariables_pairCode : OrdinalAnalysis.ACA.pairCode.freeVariables = ∅ := by
  simp [OrdinalAnalysis.ACA.pairCode, CodedNotation.liftCode]

@[simp] theorem freeVariables_succ_two :
    (‘(#1 + 1)’ : Semiterm LX ℕ 2).freeVariables = ∅ :=
  OrdinalAnalysis.ACA.TowerSyntax.freeVariables_operator _ (fun j => by
    fin_cases j
    · rfl
    · exact OrdinalAnalysis.ACA.TowerSyntax.freeVariables_operator _ (fun l => l.elim0))

theorem freeVariables_columnXat_subset {n : ℕ} {k y : Semiterm LX ℕ n} {S : Finset ℕ}
    (hk : k.freeVariables ⊆ S) (hy : y.freeVariables ⊆ S) :
    (OrdinalAnalysis.ACA.columnXat k y).freeVariables ⊆ S := by
  have h : (OrdinalAnalysis.ACA.pairAt (#0 : Semiterm LX ℕ (n + 1)) (Rew.bShift k)
      (Rew.bShift y)).freeVariables ⊆ S := by
    refine freeVariables_subst_subset _ (fun i => ?_) (by simp)
    fin_cases i
    · simp
    · simpa using hk
    · simpa using hy
  simp only [OrdinalAnalysis.ACA.columnXat, Semiformula.freeVariables_exs,
    Semiformula.freeVariables_and, Finset.union_subset_iff]
  refine ⟨h, ?_⟩
  rw [OrdinalAnalysis.ACA.TowerSyntax.freeVariables_XatZero]
  exact Finset.empty_subset _

theorem freeVariables_belowAt_subset (prec : Semiformula LX ℕ 2) (hprec : prec.freeVariables = ∅)
    {φ : Semiformula LX ℕ 1} {n : ℕ} {b : Semiterm LX ℕ n} {S : Finset ℕ}
    (hφ : φ.freeVariables ⊆ S) (hb : b.freeVariables ⊆ S) :
    (belowAt prec φ b).freeVariables ⊆ S := by
  have h1 : (precAt prec (#0 : Semiterm LX ℕ (n + 1)) (Rew.bShift b)).freeVariables ⊆ S :=
    freeVariables_subst_subset _ (fun i => by fin_cases i <;> simp [hb]) (by simp [hprec])
  have h2 : (formulaAt φ (#0 : Semiterm LX ℕ (n + 1))).freeVariables ⊆ S :=
    freeVariables_subst_subset _ (fun i => by fin_cases i; simp) hφ
  simp only [belowAt, Semiformula.freeVariables_all, Semiformula.freeVariables_or,
    Semiformula.freeVariables_not, Finset.union_subset_iff]
  exact ⟨h1, h2⟩

theorem freeVariables_jumpColumnFree :
    OrdinalAnalysis.ACA.jumpColumnFree.freeVariables ⊆ {0} := by
  have hc : OrdinalAnalysis.ACA.columnXatFree.freeVariables ⊆ {0} :=
    freeVariables_columnXat_subset (by simp) (by simp)
  have hb2 := freeVariables_belowAt_subset precCode₁ freeVariables_precCode₁ hc
    (b := (#2 : Semiterm LX ℕ 4)) (by simp)
  have hb0 := freeVariables_belowAt_subset precCode₁ freeVariables_precCode₁ hc
    (b := (#0 : Semiterm LX ℕ 4)) (by simp)
  have ho : (omegaPowAt omegaPowCode₁ (#1 : Semiterm LX ℕ 4)
      (Rew.bShift (Rew.bShift (Rew.bShift (#0 : Semiterm LX ℕ 1))))).freeVariables ⊆ {0} :=
    freeVariables_subst_subset _ (fun i => by fin_cases i <;> simp)
      (by simp [OrdinalAnalysis.ACA.TowerSyntax.freeVariables_omegaPowCode₁])
  have ha : (addAt addCode₁ (#0 : Semiterm LX ℕ 4) #2 #1).freeVariables ⊆ {0} :=
    freeVariables_subst_subset _ (fun i => by fin_cases i <;> simp)
      (by simp [OrdinalAnalysis.ACA.TowerSyntax.freeVariables_addCode₁])
  simp only [OrdinalAnalysis.ACA.jumpColumnFree, jump, jumpAt, Semiformula.freeVariables_all,
    Semiformula.freeVariables_or, Semiformula.freeVariables_not, Finset.union_subset_iff]
  exact ⟨ho, ha, hb2, hb0⟩

theorem freeVariables_jumpColumnAt2 :
    OrdinalAnalysis.ACA.jumpColumnAt2.freeVariables = ∅ := by
  apply Finset.subset_empty.mp
  refine freeVariables_rew_subset _ (fun i => ?_) (fun z hz => ?_)
  · rw [Rew.fixitr_bvar]; simp
  · have hz0 : z = 0 := by simpa using freeVariables_jumpColumnFree hz
    subst hz0
    rw [Rew.fixitr_fvar]; simp

theorem freeVariables_hierStepColLX : OrdinalAnalysis.ACA.hierStepColLX.freeVariables = ∅ := by
  have h1 : (OrdinalAnalysis.ACA.columnXat (‘#1 + 1’ : Semiterm LX ℕ 2)
      (#0 : Semiterm LX ℕ 2)).freeVariables ⊆ ∅ :=
    freeVariables_columnXat_subset (by simp) (by simp)
  have h2 := freeVariables_jumpColumnAt2
  simp only [OrdinalAnalysis.ACA.hierStepColLX, LogicalConnective.iff,
    Semiformula.freeVariables_and, Semiformula.freeVariables_imp, h2,
    Finset.subset_empty.mp h1, Finset.union_empty]

theorem freeVariables_stepHypLX : stepHypLX.freeVariables = ∅ := by
  simp only [stepHypLX, Semiformula.freeVariables_all, freeVariables_hierStepColLX]

theorem freeVariables_hierBaseColLX : OrdinalAnalysis.ACA.hierBaseColLX.freeVariables = ∅ :=
  Finset.subset_empty.mp (freeVariables_columnXat_subset (by simp) (by simp))

theorem freeVariables_belowColAt_subset {n : ℕ} {j b : Semiterm LX ℕ n} {S : Finset ℕ}
    (hj : j.freeVariables ⊆ S) (hb : b.freeVariables ⊆ S) :
    (belowColAt j b).freeVariables ⊆ S := by
  have h1 : (precAt precCode₁ (#0 : Semiterm LX ℕ (n + 1)) (Rew.bShift b)).freeVariables ⊆ S :=
    freeVariables_subst_subset _ (fun i => by fin_cases i <;> simp [hb])
      (by simp [freeVariables_precCode₁])
  have h2 : (OrdinalAnalysis.ACA.columnXat (Rew.bShift j)
      (#0 : Semiterm LX ℕ (n + 1))).freeVariables ⊆ S :=
    freeVariables_columnXat_subset (by simp [hj]) (by simp)
  simp only [belowColAt, Semiformula.freeVariables_all, Semiformula.freeVariables_or,
    Semiformula.freeVariables_not, Finset.union_subset_iff]
  exact ⟨h1, h2⟩

theorem freeVariables_tiColAt_subset {n : ℕ} {j a : Semiterm LX ℕ n} {S : Finset ℕ}
    (hj : j.freeVariables ⊆ S) (ha : a.freeVariables ⊆ S) :
    (tiColAt j a).freeVariables ⊆ S := by
  have h1 : (belowColAt (Rew.bShift j) (#0 : Semiterm LX ℕ (n + 1))).freeVariables ⊆ S :=
    freeVariables_belowColAt_subset (by simp [hj]) (by simp)
  have h2 : (OrdinalAnalysis.ACA.columnXat (Rew.bShift j)
      (#0 : Semiterm LX ℕ (n + 1))).freeVariables ⊆ S :=
    freeVariables_columnXat_subset (by simp [hj]) (by simp)
  have h3 : (belowColAt j a).freeVariables ⊆ S := freeVariables_belowColAt_subset hj ha
  simp only [tiColAt, progColAt, Semiformula.freeVariables_all, Semiformula.freeVariables_or,
    Semiformula.freeVariables_not, Finset.union_subset_iff]
  exact ⟨⟨h1, h2⟩, h3⟩

theorem freeVariables_allColTI {n : ℕ} {a : Semiterm LX ℕ n} (ha : a.freeVariables = ∅) :
    (allColTI a).freeVariables = ∅ :=
  Finset.subset_empty.mp (freeVariables_tiColAt_subset (by simp) (by simp [ha]))

theorem freeVariables_colTowerBody : colTowerBody.freeVariables = ∅ := by
  have h1 : (VeblenTower.towerAt VeblenTower.towerCode₁ (#0 : Semiterm LX ℕ 3) #1
      #2).freeVariables = ∅ :=
    OrdinalAnalysis.ACA.TowerSyntax.freeVariables_towerAt (by simp) (by simp) (by simp)
  have h2 := freeVariables_allColTI (a := (#2 : Semiterm LX ℕ 3)) (by simp)
  have h3 := freeVariables_allColTI (a := (#0 : Semiterm LX ℕ 3)) (by simp)
  simp [colTowerBody, h1, h2, h3]

/-! ### Evaluation -/

/-- Transfinite induction up to `a` along `R` for the predicate `S`, in a model. -/
def TIM {M : Type*} (R : M → M → Prop) (S : M → Prop) (a : M) : Prop :=
  (∀ x, (∀ y, R y x → S y) → S x) → ∀ y, R y a → S y

section Eval

variable {M : Type*} [Structure LX M]

/-- Membership in column `j` of the interpretation of `X`. -/
def colE (f : ℕ → M) (j y : M) : Prop :=
  ∃ p : M, OrdinalAnalysis.ACA.pairCode.Eval ![p, j, y] f ∧ Idiom.Xrel M p

/-- The coded ordering `≺₁`, in a model. -/
def precE (f : ℕ → M) (y x : M) : Prop := precCode₁.Eval ![y, x] f

/-- `k + 1`, as the value of the successor term. -/
def succE (f : ℕ → M) (k : M) : M :=
  (‘(#0 + 1)’ : Semiterm LX ℕ 1).val ![k] f

@[simp] theorem eval_columnXat {n : ℕ} (k y : Semiterm LX ℕ n) (e : Fin n → M) (f : ℕ → M) :
    (OrdinalAnalysis.ACA.columnXat k y).Eval e f ↔ colE f (k.val e f) (y.val e f) := by
  simp [OrdinalAnalysis.ACA.columnXat, OrdinalAnalysis.ACA.pairAt, colE]

@[simp] theorem eval_belowColAt {n : ℕ} (j b : Semiterm LX ℕ n) (e : Fin n → M) (f : ℕ → M) :
    (belowColAt j b).Eval e f ↔ ∀ y, precE f y (b.val e f) → colE f (j.val e f) y := by
  simp [belowColAt, precE, imp_iff_not_or]

@[simp] theorem eval_progColAt {n : ℕ} (j : Semiterm LX ℕ n) (e : Fin n → M) (f : ℕ → M) :
    (progColAt j).Eval e f ↔
      ∀ x, (∀ y, precE f y x → colE f (j.val e f) y) → colE f (j.val e f) x := by
  simp [progColAt, imp_iff_not_or]

@[simp] theorem eval_tiColAt {n : ℕ} (j a : Semiterm LX ℕ n) (e : Fin n → M) (f : ℕ → M) :
    (tiColAt j a).Eval e f ↔ TIM (precE f) (colE f (j.val e f)) (a.val e f) := by
  simp [tiColAt, TIM, imp_iff_not_or]

@[simp] theorem eval_allColTI {n : ℕ} (a : Semiterm LX ℕ n) (e : Fin n → M) (f : ℕ → M) :
    (allColTI a).Eval e f ↔ ∀ j, TIM (precE f) (colE f j) (a.val e f) := by
  simp [allColTI]

theorem eval_pairCode_indep (v : Fin 3 → M) (f f' : ℕ → M) :
    OrdinalAnalysis.ACA.pairCode.Eval v f ↔ OrdinalAnalysis.ACA.pairCode.Eval v f' := by
  simp [OrdinalAnalysis.ACA.pairCode, CodedNotation.liftCode, Semiformula.eval_lMap]

theorem eval_precCode₁_indep (v : Fin 2 → M) (f f' : ℕ → M) :
    precCode₁.Eval v f ↔ precCode₁.Eval v f' := by
  simp [precCode₁, CodedNotation.liftCode, Semiformula.eval_lMap]

theorem eval_omegaPowCode₁_indep (v : Fin 2 → M) (f f' : ℕ → M) :
    omegaPowCode₁.Eval v f ↔ omegaPowCode₁.Eval v f' := by
  simp [omegaPowCode₁, CodedNotation.liftCode, Semiformula.eval_lMap]

theorem colE_indep (f f' : ℕ → M) (j y : M) : colE f j y ↔ colE f' j y := by
  simp only [colE, eval_pairCode_indep _ f f']

theorem precE_indep (f f' : ℕ → M) (y x : M) : precE f y x ↔ precE f' y x :=
  eval_precCode₁_indep _ f f'

omit [Structure LX M] in
theorem TIM_congr {R R' : M → M → Prop} {S S' : M → Prop} {a : M}
    (hR : ∀ y x, R y x ↔ R' y x) (hS : ∀ y, S y ↔ S' y) : TIM R S a ↔ TIM R' S' a := by
  simp only [TIM, hR, hS]

theorem eval_jumpColumnAt2 (x k : M) (f : ℕ → M) :
    OrdinalAnalysis.ACA.jumpColumnAt2.Eval ![x, k] f ↔
      OrdinalAnalysis.ACA.jumpColumnFree.Eval ![x] (k :>ₙ f) := by
  unfold OrdinalAnalysis.ACA.jumpColumnAt2
  rw [Semiformula.eval_rew]
  have h1 : (Semiterm.val ![x, k] f ∘ ⇑(Rew.fixitr 1 1 : Rew LX ℕ 1 ℕ 2) ∘ Semiterm.bvar) =
      ![x] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    show Semiterm.val ![x, k] f ((Rew.fixitr 1 1 : Rew LX ℕ 1 ℕ (1 + 1)) #0) = x
    rw [Rew.fixitr_bvar]
    rfl
  have h2 : (Semiterm.val ![x, k] f ∘ ⇑(Rew.fixitr 1 1 : Rew LX ℕ 1 ℕ 2) ∘ Semiterm.fvar) =
      (k :>ₙ f) := by
    funext y
    cases y with
    | zero =>
        show Semiterm.val ![x, k] f ((Rew.fixitr 1 1 : Rew LX ℕ 1 ℕ (1 + 1)) &0) = k
        rw [Rew.fixitr_fvar]
        rfl
    | succ y =>
        show Semiterm.val ![x, k] f ((Rew.fixitr 1 1 : Rew LX ℕ 1 ℕ (1 + 1)) &(y + 1)) = f y
        rw [Rew.fixitr_fvar]
        simp
  rw [h1, h2]

theorem eval_stepHypLX (f : ℕ → M) :
    stepHypLX.Eval ![] f ↔
      ∀ k x, colE f (succE f k) x ↔ OrdinalAnalysis.ACA.jumpColumnFree.Eval ![x] (k :>ₙ f) := by
  simp [stepHypLX, OrdinalAnalysis.ACA.hierStepColLX, eval_jumpColumnAt2, succE]

theorem eval_depthFormula (n : M) (f : ℕ → M) :
    depthFormula.Eval ![n] f ↔
      ∀ c u, VeblenTower.towerCode₁.Eval ![u, n, c] f →
        (∀ j, TIM (precE f) (colE f j) c) → ∀ j, TIM (precE f) (colE f j) u := by
  simp [depthFormula, imp_iff_not_or]

end Eval

/-! ### The argument in a model of `PA[X]` -/

section Model

variable {M : Type} [Nonempty M] [Structure LX M] [Structure.Eq LX M] [M↓[LX] ⊧* paLX]

/-- Gentzen's Lemma B for the columns, read in a model: for every column index `k`,
`TI(Jump(col_k), a)` and `u = ω^a` give `TI(col_k, u)`. -/
theorem jumpB_column_sem (f : ℕ → M) (k a u : M)
    (hom : omegaPowCode₁.Eval ![u, a] f)
    (hJ : TIM (precE f) (fun y => OrdinalAnalysis.ACA.jumpColumnFree.Eval ![y] (k :>ₙ f)) a) :
    TIM (precE f) (colE f k) u := by
  have hB : M↓[LX] ⊧ jumpBStatement precCode₁ addCode₁ omegaPowCode₁
      OrdinalAnalysis.ACA.columnXatFree :=
    consequence_iff_eq'.mp (Theory.Proof.sound OrdinalAnalysis.ACA.jumpB_column) M
  rw [models_iff] at hB
  simp only [jumpBStatement, Semiformula.eval_univCl, Semiformula.eval_all,
    LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq,
    eval_omegaPowAt, eval_tiUptoAt, Semiterm.val_bvar, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hB
  have h := hB (k :>ₙ f) a u
  have hom' : omegaPowCode₁.Eval ![u, a] (k :>ₙ f) := (eval_omegaPowCode₁_indep _ f _).mp hom
  have hJ' : TIM (precE (k :>ₙ f))
      (fun y => OrdinalAnalysis.ACA.jumpColumnFree.Eval ![y] (k :>ₙ f)) a :=
    (TIM_congr (fun y x => precE_indep f (k :>ₙ f) y x) (fun _ => Iff.rfl)).mp hJ
  have hcol : ∀ y, OrdinalAnalysis.ACA.columnXatFree.Eval ![y] (k :>ₙ f) ↔ colE f k y := by
    intro y
    simp only [OrdinalAnalysis.ACA.columnXatFree, eval_columnXat]
    simp only [Semiterm.val_fvar, Semiterm.val_bvar, Matrix.cons_val_fin_one]
    exact colE_indep _ _ _ _
  rcases h with h | h | h
  · exact absurd hom' h
  · exact absurd hJ' h
  · exact (TIM_congr (fun y x => precE_indep (k :>ₙ f) f y x) hcol).mp h

/-- **The tower-depth induction along the columns, in a model of `PA[X]`.**  If the
columns of `X` satisfy the omega-jump step condition, then for every tower height `n`,
`TI` up to `c` for all columns gives `TI` up to `Tower(n, c)` for all columns. -/
theorem colTower_sem (f : ℕ → M)
    (hH : ∀ k x, colE f (succE f k) x ↔
      OrdinalAnalysis.ACA.jumpColumnFree.Eval ![x] (k :>ₙ f)) :
    ∀ n c u, VeblenTower.towerCode₁.Eval ![u, n, c] f →
      (∀ j, TIM (precE f) (colE f j) c) → ∀ j, TIM (precE f) (colE f j) u := by
  have hZ : M↓[LX] ⊧ VeblenTower.towerZeroStatement VeblenTower.towerCode₁ :=
    consequence_iff_eq'.mp (Theory.Proof.sound VeblenTower.concrete_towerZero) M
  have hZ' := (VeblenTower.models_towerZeroStatement VeblenTower.towerCode₁).mp hZ
  have hS : M↓[LX] ⊧ VeblenTower.towerSuccStatement omegaPowCode₁ VeblenTower.towerCode₁ :=
    consequence_iff_eq'.mp (Theory.Proof.sound VeblenTower.concrete_towerSucc) M
  have hS' := (VeblenTower.models_towerSuccStatement omegaPowCode₁
    VeblenTower.towerCode₁).mp hS
  have hInd := Idiom.paLX_induction (M := M) depthFormula f
  simp only [eval_depthFormula] at hInd
  intro n
  refine hInd ?_ ?_ n
  · intro c u htw hc
    have huc : u = c := hZ' f c u htw
    subst huc
    exact hc
  · intro m ih c u htw hc j
    obtain ⟨v, hv, hom⟩ := hS' f c m u htw
    have hcols := ih c v hv hc
    have h1 := hcols (succE f j)
    have h2 : TIM (precE f)
        (fun y => OrdinalAnalysis.ACA.jumpColumnFree.Eval ![y] (j :>ₙ f)) v :=
      (TIM_congr (fun _ _ => Iff.rfl) (hH j)).mp h1
    exact jumpB_column_sem f j v u hom h2

end Model

/-- **The tower-depth induction along the columns is a theorem of `PA[X]`.** -/
theorem concrete_colTower : paLX ⊢ colTowerStatement := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ _
  show M↓[LX] ⊧ (∼stepHypLX ⋎ (∀¹ ∀¹ ∀¹ colTowerBody)).univCl
  rw [models_iff_proposition]
  intro f
  by_cases hH : stepHypLX.Eval ![] f
  · have hH' := (eval_stepHypLX f).mp hH
    have key := colTower_sem f hH'
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
      LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq,
      Semiformula.eval_all]
    refine Or.inr (fun c n u => ?_)
    simp only [colTowerBody, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
      LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq,
      VeblenTower.eval_towerAt, eval_allColTI, Semiterm.val_bvar, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    by_cases htw : VeblenTower.towerCode₁.Eval ![u, n, c] f
    · by_cases hc : ∀ j, TIM (precE f) (colE f j) c
      · exact Or.inr (Or.inr (key n c u htw hc))
      · exact Or.inr (Or.inl hc)
    · exact Or.inl htw
  · simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
      LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
    exact Or.inl hH

end OrdinalAnalysis.ACA.ColumnTower

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX XRel Xat toLX paLX)

/-! ### The omega-jump axiom has no free variables

`OmegaJump.lean`'s `IsOmegaJump` has `Y` at the bound set slot `0` (bound by the inner
`∃²`) and `Z` at slot `1` (bound by the outer `∀²`), so `omegaJumpAxiom` is
`∀Z ∃Y IsOmegaJump(Y, Z)`.  It has neither free set nor free number variables, so
`ACAplus` and `ACAplus₀` admit the eigenvariable rules. -/

/-- **Everything `ACA` proves, `ACA^+` proves.** -/
theorem Provable_mono_ACAplus {φ : Proposition ℒₒᵣ} (h : Provable ACA φ) :
    Provable ACAplus φ :=
  acaplus_provable_mono h

theorem noSetFvar_emb_yWit2 :
    NoSetFvar (FirstOrder.Rewriting.emb yWit2 : Semiproposition ℒₒᵣ 2 1) := by
  simp [yWit2]

theorem noSetFvar_omegaJumpAxiom : NoSetFvar omegaJumpAxiom := by
  have h1 := noSetFvar_toSOAtB noSetFvar_emb_yWit2 hierBaseColLX
  have h2 := noSetFvar_toSOAtB noSetFvar_emb_yWit2 hierStepColLX
  simp [omegaJumpAxiom, IsOmegaJump, hierBase, hierStep, LogicalConnective.iff,
    LogicalConnective.DeMorgan.imply, h1, h2]

theorem shift₀_omegaJumpAxiom : Semiproposition.shift₀ omegaJumpAxiom = omegaJumpAxiom := by
  have hS : ((FirstOrder.Rew.shift : FirstOrder.Rew LX ℕ 0 ℕ 0).q.q) ▹ hierStepColLX =
      hierStepColLX := by
    refine FirstOrder.Semiformula.rew_eq_self_of (fun x => ?_) (fun x hx => ?_)
    · fin_cases x <;> simp
    · have hx' : x ∈ hierStepColLX.freeVariables := hx
      rw [ColumnTower.freeVariables_hierStepColLX] at hx'
      exact absurd hx' (by simp)
  have hB : ((FirstOrder.Rew.shift : FirstOrder.Rew LX ℕ 0 ℕ 0).q) ▹ hierBaseColLX =
      hierBaseColLX := by
    refine FirstOrder.Semiformula.rew_eq_self_of (fun x => ?_) (fun x hx => ?_)
    · fin_cases x; simp
    · have hx' : x ∈ hierBaseColLX.freeVariables := hx
      rw [ColumnTower.freeVariables_hierBaseColLX] at hx'
      exact absurd hx' (by simp)
  have eS : ((FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0).q.q) ▹
      (toSOAtB yWit2 hierStepColLX : Semiproposition ℒₒᵣ 2 2) =
      toSOAtB yWit2 hierStepColLX := by
    rw [← toSOAtB_rew (q_hb (q_hb hb_shift)) (q_hf (q_hf hf_shift)), hS]
  have eB : ((FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0).q) ▹
      (toSOAtB yWit2 hierBaseColLX : Semiproposition ℒₒᵣ 2 1) =
      toSOAtB yWit2 hierBaseColLX := by
    rw [← toSOAtB_rew (q_hb hb_shift) (q_hf hf_shift), hB]
  have eZ : ((FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0).q) ▹
      (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (1 : Fin 2)) : Semiproposition ℒₒᵣ 2 1) =
      ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (1 : Fin 2)) := by
    simp
  show (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹
    (∀² (∃² ((∀¹ ((toSOAtB yWit2 hierBaseColLX : Semiproposition ℒₒᵣ 2 1) 🡘
      ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (1 : Fin 2)))) ⋏
      (∀¹ ∀¹ (toSOAtB yWit2 hierStepColLX : Semiproposition ℒₒᵣ 2 2))))) = _
  rw [Semiformula.rew_all₁, Semiformula.rew_exs₁, LogicalConnective.HomClass.map_and,
    Semiformula.rew_all₀, LogicalConnective.HomClass.map_iff, eB, eZ,
    Semiformula.rew_all₀, Semiformula.rew_all₀, eS]
  rfl

theorem ACAplus_shift₁_invariant : ∀ χ ∈ ACAplus, Semiproposition.shift₁ χ = χ := by
  rintro χ (h | h)
  · exact ACA_shift₁_invariant χ h
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact shift₁_eq_self_of_noSetFvar noSetFvar_omegaJumpAxiom

theorem ACAplus_shift₀_invariant : ∀ χ ∈ ACAplus, Semiproposition.shift₀ χ = χ := by
  rintro χ (h | h)
  · exact ACA_shift₀_invariant χ h
  · rw [Set.mem_singleton_iff] at h
    subst h
    exact shift₀_omegaJumpAxiom

theorem ACAplus₀_shift₁_invariant : ∀ χ ∈ ACAplus₀, Semiproposition.shift₁ χ = χ :=
  fun χ h => ACAplus_shift₁_invariant χ (ACAplus₀_subset_ACAplus h)

theorem ACAplus₀_shift₀_invariant : ∀ χ ∈ ACAplus₀, Semiproposition.shift₀ χ = χ :=
  fun χ h => ACAplus_shift₀_invariant χ (ACAplus₀_subset_ACAplus h)

/-! ### The tower-depth induction, lifted

The free set variable `0` (`yWitFree`) stands for `Y`. -/

/-- **The tower-depth induction along the columns of `Y`, in `ACA`**: if `Y`
satisfies the omega-jump step condition `∀k ∀x (x ∈ col_{k+1} Y ↔ Jump(col_k Y)(x))`,
then `∀c ∀n ∀u (Tower(u,n,c) → ∀j TI(col_j Y, c) → ∀j TI(col_j Y, u))`.  No
second-order induction scheme is used beyond the lifting of `PA[X]`'s induction. -/
theorem columnTower_lifted :
    Provable ACA (∼(toSOAt yWitFree ColumnTower.stepHypLX) ⋎
      (∀¹ ∀¹ ∀¹ (toSOAt yWitFree ColumnTower.colTowerBody))) := by
  have h := lift_paLX₀ yWitFree arith_yWitFree ColumnTower.concrete_colTower
  unfold ColumnTower.colTowerStatement at h
  rw [TowerSyntax.emb_univCl_of_closed (by
    simp [ColumnTower.freeVariables_stepHypLX, ColumnTower.freeVariables_colTowerBody])] at h
  have h' : Provable ACA (toSOAtB yWitFree
      (∼ColumnTower.stepHypLX ⋎ (∀¹ ∀¹ ∀¹ ColumnTower.colTowerBody))) := h
  rwa [toSOAtB_or, toSOAtB_neg, toSOAtB_all, toSOAtB_all, toSOAtB_all] at h'

/-- **`omegaTowerInduction`**: the same in `ACA^+`, where every set `Z` has an
omega-jump `Y` satisfying the step condition. -/
theorem omegaTowerInduction :
    Provable ACAplus (∼(toSOAt yWitFree ColumnTower.stepHypLX) ⋎
      (∀¹ ∀¹ ∀¹ (toSOAt yWitFree ColumnTower.colTowerBody))) :=
  Provable_mono_ACAplus columnTower_lifted

/-- The tower statement over *all sets*,
`∀k ∀c ∀u (Tower(u,k,c) → ∀²X TI(c,X) → ∀²X TI(u,X))`, needs no omega-jump: it is
`TowerInduction.towerInduction`, a theorem of `ACA`.  The omega-jump is used for
the column form `omegaTowerInduction`, whose induction formula is arithmetical in
`Y`. -/
theorem towerInduction_plus : Provable ACAplus (∀¹ theta) :=
  Provable_mono_ACAplus towerInduction

end OrdinalAnalysis.ACA
