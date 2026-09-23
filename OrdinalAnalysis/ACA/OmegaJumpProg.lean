/-
  The ε-progressiveness along the columns of an omega-jump, and the ε-jump for
  one column.

  For a set `Y` whose columns satisfy the omega-jump step condition
  (`ACA/OmegaJumpInduction.lean`'s `stepHypLX`), let

      χ_Y(g) :≡ ∀u (Eps(u, g) → ∀j TI(≺₁, col_j Y, u)).

  Unlike `ACA/EpsProg.lean`'s `ψ₀(g) :≡ ∀u (Eps(u,g) → ∀²X TI(≺₁, u, X))`, this
  formula is *arithmetical in `Y`*: the second-order quantifier over all sets is
  replaced by the quantifier over the columns of the single set `Y`.  It is
  `≺₁`-progressive, by the argument of `EpsProg.lean` with the column tower
  induction (`ColumnTower.colTower_sem`) in place of `towerInduction`:

  * for `x ≺₁ u = ε_g`, the cover (`ProgStep.concrete_coverGood`) supplies `s`, `n`,
    `w` with `Good(s, g)`, `Tower(w, n, s)` and `x ≺₁ w`;
  * `Good(s, g)` says `s = 0 ⊕ 1`, or `s = ε_h ⊕ 1` for some `h ≺₁ g`; in both cases
    `∀j TI(col_j Y, s)` follows from `∀j TI(col_j Y, e)` for the base `e` (trivially
    for `e = 0`, by `χ_Y(h)` for `e = ε_h`) and the successor step
    (`VeblenSuccStep.concrete_succ_general`);
  * the column tower induction lifts `∀j TI(col_j Y, s)` to `∀j TI(col_j Y, w)`.

  Consequently `TI(≺₁, χ_Y, b)` gives `χ_Y(b)`, and with `Eps(ε̄_b, b̄)`
  (`ProgStep.concrete_epsValue`) transfinite induction for column `0` up to `ε_b`.
  Everything is proved in `PA[X]` with `X` standing for `Y` and the step condition
  as an object-language hypothesis, semantically; the results are lifted to `ACA`
  at the free set variable `0`.

  Because `χ_Y` is arithmetical, the hypothesis `TI(≺₁, χ_Y, b)` is an instance of
  `∀²Z TI(≺₁, b, Z)` by arithmetical comprehension; this is what the ε-jump of
  `ACA/OmegaJumpUpperBound.lean` uses.  (`progPsi`, the progressiveness of the `Π¹₁`
  formula `ψ₀`, is already a theorem of `ACA`, `EpsProg.epsProg`, and holds in
  `ACA^+` by monotonicity, `progPsi_plus`; it does not yield the ε-jump from
  `∀²Z TI(b, Z)`, since `TI(b, ψ₀)` is not an instance of it.)
-/
import OrdinalAnalysis.ACA.OmegaJumpInduction
import OrdinalAnalysis.ACA.EpsProg

set_option autoImplicit false

namespace OrdinalAnalysis.ACA.ColumnTower

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁ freeVariables_precCode₁)
open OrdinalAnalysis.Gentzen.CodedVeblenJump (addCode₁ omegaPowCode₁)
open OrdinalAnalysis.Gentzen.InternalEpsMonoCode (epsCode₁ epsAt)
open OrdinalAnalysis.Gentzen.VeblenSuccStep (baseCode₁)
open OrdinalAnalysis.Gentzen.Epsilon1UpperBound (gamma0Term)
open OrdinalAnalysis.Gamma0Note (epsilonNote)

/-! ### The formula `χ` -/

/-- **`χ(g) :≡ ∀u (Eps(u, g) → ∀j TI(≺₁, col_j X, u))`**, with `#0 = g`. -/
def chiLX : Semiformula LX ℕ 1 :=
  ∀¹ (∼(epsAt epsCode₁ (#0 : Semiterm LX ℕ 2) #1) ⋎ allColTI (#0 : Semiterm LX ℕ 2))

/-- The progressiveness of `χ` under the step condition, as a sentence of `PA[X]`. -/
def colProgStatement : Sentence LX := (∼stepHypLX ⋎ progAt precCode₁ chiLX).univCl

/-- **The ε-jump for column `0`**, as a sentence of `PA[X]`: under the step
condition, `TI(≺₁, χ, b̄)` gives `TI(≺₁, col_0 X, ε̄_b)`. -/
noncomputable def colEpsJumpStatement (b : Gamma0Note) : Sentence LX :=
  (∼stepHypLX ⋎ (∼(tiUptoAt precCode₁ chiLX (gamma0Term b)) ⋎
    tiUptoAt precCode₁ OrdinalAnalysis.ACA.hierBaseColLX (gamma0Term (epsilonNote b)))).univCl

theorem freeVariables_chiLX : chiLX.freeVariables = ∅ := by
  have h1 : (epsAt epsCode₁ (#0 : Semiterm LX ℕ 2) #1).freeVariables = ∅ :=
    OrdinalAnalysis.ACA.freeVariables_epsAt (by simp) (by simp)
  have h2 := freeVariables_allColTI (a := (#0 : Semiterm LX ℕ 2)) (by simp)
  simp [chiLX, h1, h2]

/-! ### Evaluation -/

section Eval

variable {M : Type*} [Structure LX M]

/-- `χ(g)`, in a model. -/
def chiE (f : ℕ → M) (g : M) : Prop :=
  ∀ u, epsCode₁.Eval ![u, g] f → ∀ j, TIM (precE f) (colE f j) u

theorem eval_chiLX (g : M) (f : ℕ → M) : chiLX.Eval ![g] f ↔ chiE f g := by
  simp [chiLX, chiE, imp_iff_not_or]

end Eval

/-! ### The argument in a model of `PA[X]` -/

section Model

variable {M : Type} [Nonempty M] [Structure LX M] [Structure.Eq LX M] [M↓[LX] ⊧* paLX]

/-- Transfinite induction up to `0` holds for every predicate. -/
theorem tim_zero (f : ℕ → M) (S : M → Prop) :
    TIM (precE f) S (((0 : ℕ) : Semiterm LX ℕ 0).val ![] f) := by
  have h0 : M↓[LX] ⊧ noPredZeroStatement precCode₁ :=
    consequence_iff_eq'.mp (Theory.Proof.sound CodedVeblenJump.noPredZero₁) M
  rw [models_iff] at h0
  simp only [noPredZeroStatement, Semiformula.eval_univCl, Semiformula.eval_all,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, eval_precAt,
    Semiterm.val_bvar, Matrix.cons_val_zero] at h0
  intro _ y hy
  have hz : ((0 : ℕ) : Semiterm LX ℕ 1).val ![y] f = ((0 : ℕ) : Semiterm LX ℕ 0).val ![] f := by
    simp
  exact absurd hy (by rw [← hz]; exact h0 f y)

/-- The successor step of the ordering: from `TI` up to a `Base` `e` to `TI` up to
`s = e ⊕ 1`. -/
theorem tim_succ (f : ℕ → M) (S : M → Prop) (e s : M)
    (hb : baseCode₁.Eval ![e] f)
    (ha : addCode₁.Eval ![s, e, ((Gentzen.VNoteBridge.gamma0Code 1 : ℕ) :
      Semiterm LX ℕ 0).val ![] f] f)
    (hti : TIM (precE f) S e) : TIM (precE f) S s := by
  have hS : M↓[LX] ⊧ VeblenSuccStep.succGeneralStatement :=
    consequence_iff_eq'.mp (Theory.Proof.sound VeblenSuccStep.concrete_succ_general) M
  have hS' := VeblenSuccStep.models_succGeneralStatement.mp hS
  intro hProg y hy
  rcases hS' f e s y hb ha hy with hlt | heq
  · exact hti hProg y hlt
  · rw [heq]
    exact hProg e (hti hProg)

/-- **`χ` is `≺₁`-progressive in every model of `PA[X]` whose `X` satisfies the
omega-jump step condition.** -/
theorem colProg_sem (f : ℕ → M)
    (hH : ∀ k x, colE f (succE f k) x ↔
      OrdinalAnalysis.ACA.jumpColumnFree.Eval ![x] (k :>ₙ f)) :
    ∀ g, (∀ h, precE f h g → chiE f h) → chiE f g := by
  have hC : M↓[LX] ⊧ ProgStep.coverGoodStatement :=
    consequence_iff_eq'.mp (Theory.Proof.sound ProgStep.concrete_coverGood) M
  have hC' := ProgStep.models_coverGoodStatement.mp hC
  intro g IH u heps j hProg y hy
  obtain ⟨s, n, w, hgood, htw, hyw⟩ := hC' f g u y heps hy
  have hs : ∀ j', TIM (precE f) (colE f j') s := by
    intro j'
    simp [ProgStep.goodBody] at hgood
    rcases hgood with ⟨hb0, ha0⟩ | ⟨h, hhg, v, hbv, hev, hav⟩
    · exact tim_succ f _ (((0 : ℕ) : Semiterm LX ℕ 0).val ![] f) s (by simpa using hb0)
        (by simpa using ha0) (tim_zero f _)
    · exact tim_succ f _ v s hbv (by simpa using hav) (IH h hhg v hev j')
  exact colTower_sem f hH n s w htw hs j hProg y hyw

/-- **The ε-jump for column `0`, in a model**: under the step condition,
`TI(χ, b̄)` gives `TI(col_0, ε̄_b)`. -/
theorem colEpsJump_sem (b : Gamma0Note) (f : ℕ → M)
    (hH : ∀ k x, colE f (succE f k) x ↔
      OrdinalAnalysis.ACA.jumpColumnFree.Eval ![x] (k :>ₙ f))
    (hTI : TIM (precE f) (chiE f) ((gamma0Term b).val ![] f)) :
    TIM (precE f) (colE f (((0 : ℕ) : Semiterm LX ℕ 0).val ![] f))
      ((gamma0Term (epsilonNote b)).val ![] f) := by
  have hE : M↓[LX] ⊧ ProgStep.epsValueStatement b :=
    consequence_iff_eq'.mp (Theory.Proof.sound (ProgStep.concrete_epsValue b)) M
  rw [models_iff] at hE
  simp only [ProgStep.epsValueStatement, Semiformula.eval_univCl,
    InternalEpsMonoCode.eval_epsAt] at hE
  have hprog := colProg_sem f hH
  have hb : chiE f ((gamma0Term b).val ![] f) := hprog _ (hTI hprog)
  exact hb _ (hE f) _

end Model

/-- **The progressiveness of `χ` under the step condition is a theorem of `PA[X]`.** -/
theorem concrete_colProg : paLX ⊢ colProgStatement := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ _
  show M↓[LX] ⊧ (∼stepHypLX ⋎ progAt precCode₁ chiLX).univCl
  rw [models_iff_proposition]
  intro f
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
  by_cases hH : stepHypLX.Eval ![] f
  · refine Or.inr ?_
    have key := colProg_sem f ((eval_stepHypLX f).mp hH)
    simp only [eval_progAt, eval_chiLX]
    exact key
  · exact Or.inl hH

/-- **The ε-jump for column `0` is a theorem of `PA[X]`**, for every notation `b`. -/
theorem concrete_colEpsJump (b : Gamma0Note) : paLX ⊢ colEpsJumpStatement b := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ _
  show M↓[LX] ⊧ (∼stepHypLX ⋎ (∼(tiUptoAt precCode₁ chiLX (gamma0Term b)) ⋎
    tiUptoAt precCode₁ OrdinalAnalysis.ACA.hierBaseColLX (gamma0Term (epsilonNote b)))).univCl
  rw [models_iff_proposition]
  intro f
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
  by_cases hH : stepHypLX.Eval ![] f
  · refine Or.inr ?_
    by_cases hTI : (tiUptoAt precCode₁ chiLX (gamma0Term b)).Eval ![] f
    · refine Or.inr ?_
      have hTI' : TIM (precE f) (chiE f) ((gamma0Term b).val ![] f) := by
        have h := (eval_tiUptoAt precCode₁ chiLX (gamma0Term b) ![] f).mp hTI
        simp only [eval_chiLX] at h
        exact h
      have key := colEpsJump_sem b f ((eval_stepHypLX f).mp hH) hTI'
      rw [eval_tiUptoAt]
      have hcol : ∀ y : M, OrdinalAnalysis.ACA.hierBaseColLX.Eval ![y] f ↔
          colE f (((0 : ℕ) : Semiterm LX ℕ 0).val ![] f) y := by
        intro y
        simp only [OrdinalAnalysis.ACA.hierBaseColLX, eval_columnXat, Semiterm.val_bvar,
          Matrix.cons_val_fin_one]
        have hz : ((0 : ℕ) : Semiterm LX ℕ 1).val ![y] f =
            ((0 : ℕ) : Semiterm LX ℕ 0).val ![] f := by simp
        rw [hz]
      exact (TIM_congr (fun _ _ => Iff.rfl) hcol).mpr key
    · exact Or.inl hTI
  · exact Or.inl hH

theorem freeVariables_colEpsJumpBody (b : Gamma0Note) :
    (∼stepHypLX ⋎ (∼(tiUptoAt precCode₁ chiLX (gamma0Term b)) ⋎
      tiUptoAt precCode₁ OrdinalAnalysis.ACA.hierBaseColLX
        (gamma0Term (epsilonNote b)))).freeVariables = ∅ := by
  have h1 : (tiUptoAt precCode₁ chiLX (gamma0Term b)).freeVariables = ∅ :=
    OrdinalAnalysis.ACA.TowerSyntax.freeVariables_tiUptoAt freeVariables_precCode₁
      freeVariables_chiLX (by simp [gamma0Term])
  have h2 : (tiUptoAt precCode₁ OrdinalAnalysis.ACA.hierBaseColLX
      (gamma0Term (epsilonNote b))).freeVariables = ∅ :=
    OrdinalAnalysis.ACA.TowerSyntax.freeVariables_tiUptoAt freeVariables_precCode₁
      freeVariables_hierBaseColLX (by simp [gamma0Term])
  simp [freeVariables_stepHypLX, h1, h2]

theorem freeVariables_colProgBody :
    (∼stepHypLX ⋎ progAt (n := 0) precCode₁ chiLX).freeVariables = ∅ := by
  have h : (progAt (n := 0) precCode₁ chiLX).freeVariables = ∅ :=
    OrdinalAnalysis.ACA.TowerSyntax.freeVariables_progAt freeVariables_precCode₁
      freeVariables_chiLX
  simp [freeVariables_stepHypLX, h]

end OrdinalAnalysis.ACA.ColumnTower

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX Xat paLX)
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁)
open OrdinalAnalysis.Gentzen.Epsilon1UpperBound (gamma0Term)
open OrdinalAnalysis.Gamma0Note (epsilonNote)

/-! ### Lifted to `ACA`, at the free set variable `Y` -/

/-- **`χ_Y` is progressive**: `ACA` proves, for the free set variable `Y`, that if
`Y` satisfies the omega-jump step condition then
`χ_Y(g) :≡ ∀u (Eps(u, g) → ∀j TI(≺₁, col_j Y, u))` is `≺₁`-progressive. -/
theorem colProg_lifted :
    Provable ACA (∼(toSOAt yWitFree ColumnTower.stepHypLX) ⋎
      toSOAt yWitFree (Gentzen.progAt (n := 0) precCode₁ ColumnTower.chiLX)) := by
  have h := lift_paLX₀ yWitFree arith_yWitFree ColumnTower.concrete_colProg
  unfold ColumnTower.colProgStatement at h
  rw [TowerSyntax.emb_univCl_of_closed ColumnTower.freeVariables_colProgBody] at h
  have h' : Provable ACA (toSOAtB yWitFree
      (∼ColumnTower.stepHypLX ⋎ Gentzen.progAt (n := 0) precCode₁ ColumnTower.chiLX)) := h
  rwa [toSOAtB_or, toSOAtB_neg] at h'

/-- **`epsProg_plus`**: the progressiveness of `χ_Y`, in `ACA^+`. -/
theorem epsProg_plus :
    Provable ACAplus (∼(toSOAt yWitFree ColumnTower.stepHypLX) ⋎
      toSOAt yWitFree (Gentzen.progAt (n := 0) precCode₁ ColumnTower.chiLX)) :=
  Provable_mono_ACAplus colProg_lifted

/-- **The ε-jump for column `0` of `Y`, lifted**: `ACA` proves, for the free set
variable `Y`: if `Y` satisfies the step condition, then `TI(≺₁, χ_Y, b̄)` gives
`TI(≺₁, col_0 Y, ε̄_b)`. -/
theorem colEpsJump_lifted (b : Gamma0Note) :
    Provable ACA (∼(toSOAt yWitFree ColumnTower.stepHypLX) ⋎
      (∼(toSOAt yWitFree (Gentzen.tiUptoAt precCode₁ ColumnTower.chiLX (gamma0Term b))) ⋎
        toSOAt yWitFree (Gentzen.tiUptoAt precCode₁ hierBaseColLX
          (gamma0Term (epsilonNote b))))) := by
  have h := lift_paLX₀ yWitFree arith_yWitFree (ColumnTower.concrete_colEpsJump b)
  unfold ColumnTower.colEpsJumpStatement at h
  rw [TowerSyntax.emb_univCl_of_closed (ColumnTower.freeVariables_colEpsJumpBody b)] at h
  have h' : Provable ACA (toSOAtB yWitFree
      (∼ColumnTower.stepHypLX ⋎ (∼(Gentzen.tiUptoAt precCode₁ ColumnTower.chiLX
        (gamma0Term b)) ⋎ Gentzen.tiUptoAt precCode₁ hierBaseColLX
          (gamma0Term (epsilonNote b))))) := h
  rwa [toSOAtB_or, toSOAtB_neg, toSOAtB_or, toSOAtB_neg] at h'

/-- `progPsi` (the progressiveness of the `Π¹₁` formula `ψ₀` of `EpsProg.lean`) in
`ACA^+`: already a theorem of `ACA`. -/
theorem progPsi_plus : Provable ACAplus (progPsi : Proposition ℒₒᵣ) :=
  Provable_mono_ACAplus epsProg

end OrdinalAnalysis.ACA
