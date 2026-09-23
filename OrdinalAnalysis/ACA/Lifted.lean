/-
  **The lifted inventory**.

  Every step of Gentzen's argument whose content is first-order in the fresh
  predicate `X` is already a `paLX`-theorem (the internal-arithmetic files); this file carries
  each of them across the bridge of `ACA/Lift.lean` at the parameter that the
  assembly uses, `ψ := segWitness` (`#0 ∈& 0`, the free set variable `0`),
  and adds the two pieces of glue the second-order layer needs:

  * `genSO` — the `∀²`-introduction over the free set variable, i.e. the
    identification of `toSOAt segWitness χ` with `free₁ (toSOAtB boundWitness χ)`
    (`free₁_toSOAtB`), which is what makes `Toolkit.lean`'s `gen₂` applicable;
  * `jumpWitness` — the arithmetical witness `Jump(X₀)` that `spec₂` (the `exs₂`
    rule, i.e. arithmetical comprehension) is instantiated at in the tower
    induction.

  It also contains the one genuinely new **first-order** lemma the assembly needs,
  the *relativisation* of progressiveness from `≺₁` to the `ε_{ε₀}`-segment
  ordering `precSeg` of `ACA/TI.lean` (design note §4, C5: "the relativised
  progressiveness as a `paLX` theorem lifted").  It is first-order, so it is
  proved in `paLX` and lifted, exactly as the two-layer discipline requires.
-/
import OrdinalAnalysis.ACA.LiftTI
import OrdinalAnalysis.Gentzen.InternalEpsMonoCode

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Layer 1: the first-order relativisation `≺₁ ↝ precSeg` -/

namespace OrdinalAnalysis.ACA.Relativise

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.CodedVeblen
open OrdinalAnalysis.Gentzen.CodedVeblenJump
open OrdinalAnalysis.Gentzen.Epsilon1UpperBound
open OrdinalAnalysis.Gentzen.EpsilonSegmentOrder
open OrdinalAnalysis.Gentzen.Order (precTransStatement models_precTransStatement)
open OrdinalAnalysis.Gamma0Note (epsilonNote)
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)

/-- The code of `ε_{ε₀}` — the right-hand end of the segment `ACA/TI.lean`'s
`precSeg` cuts out of `≺₁`. -/
def segBound : ℕ := gamma0Code (epsilonNote (epsilonNote 0))

/-- **The relativising formula** `y ≺₁ ε̄_{ε₀} → X y`.  Transfinite induction
along `≺₁` *for this formula* is what yields transfinite induction along the
segment ordering for `X` itself. -/
def segGuard : Semiformula LX ℕ 1 :=
  ∼(precAt precCode₁ (#0 : Semiterm LX ℕ 1) (Semiterm.numeral segBound)) ⋎
    Xat (#0 : Semiterm LX ℕ 1)

private theorem val_numeral_eq {M : Type*} [Nonempty M] [Structure LX M] (k : ℕ) {n : ℕ}
    (e : Fin n → M) (f : ℕ → M) :
    (Semiterm.numeral k : Semiterm LX ℕ n).val e f =
      (Semiterm.numeral k : Semiterm LX ℕ 0).val ![] f := by
  simp

/--
**The relativisation.**  Transfinite induction along `≺₁` below `a` for the
guarded formula `y ≺₁ ε̄_{ε₀} → X y` gives transfinite induction along the
`ε_{ε₀}`-segment ordering below `a` for `X`.

Both directions of the argument are one use of transitivity of `≺₁`: a
`precSeg`-progressive `X` makes the guarded formula `≺₁`-progressive, and a
`≺₁`-bound below `a` together with `a ≺₁ ε̄_{ε₀}` re-establishes the guard.
-/
theorem concrete_tiUptoSeg_of_closedTI₁ (a : Semiterm LX ℕ 0)
    (h : paLX ⊢ closedTI₁ segGuard a) :
    paLX ⊢ (TIupto (precCodeSeg (epsilonNote 0)) a).univCl := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  have hTransM : M↓[LX] ⊧ precTransStatement precCode₁ :=
    consequence_iff_eq'.mp (Theory.Proof.sound concrete_precTrans₁) M
  have hTIM : M↓[LX] ⊧ closedTI₁ segGuard a :=
    consequence_iff_eq'.mp (Theory.Proof.sound h) M
  have hTrans := (models_precTransStatement precCode₁).mp hTransM
  rw [← tiUptoAt_X_eq']
  rw [models_iff] at hTIM ⊢
  simp only [closedTI₁, Semiformula.eval_univCl, eval_tiUptoAt] at hTIM ⊢
  intro f
  have hguard : ∀ z : M,
      (Semiformula.Eval ![z] f segGuard ↔
        (¬ Semiformula.Eval ![z, (Semiterm.numeral segBound : Semiterm LX ℕ 0).val ![] f] f
              precCode₁ ∨
          Semiformula.Eval ![z] f (Xat (#0 : Semiterm LX ℕ 1)))) := by
    intro z
    show Semiformula.Eval ![z] f
        (∼(precAt precCode₁ (#0 : Semiterm LX ℕ 1) (Semiterm.numeral segBound)) ⋎
          Xat (#0 : Semiterm LX ℕ 1)) ↔ _
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
      LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, eval_precAt,
      Semiterm.val_bvar, Matrix.cons_val_fin_one, val_numeral_eq]
  have hseg : ∀ y x : M,
      (Semiformula.Eval ![y, x] f (precCodeSeg (epsilonNote 0)) ↔
        Semiformula.Eval ![y, x] f precCode₁ ∧
          Semiformula.Eval ![x, (Semiterm.numeral segBound : Semiterm LX ℕ 0).val ![] f] f
            precCode₁) := by
    intro y x
    show Semiformula.Eval ![y, x] f
        (precCode₁ ⋏ precAt precCode₁ (#1 : Semiterm LX ℕ 2)
          (epsilonNumeral (epsilonNote 0))) ↔ _
    have he : epsilonNumeral (epsilonNote 0) = (Semiterm.numeral segBound : Semiterm LX ℕ 2) :=
      rfl
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq, he,
      eval_precAt, Semiterm.val_bvar, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      val_numeral_eq]
  intro hProgSeg
  -- the guarded formula is `≺₁`-progressive
  have hProg₁ : ∀ x : M,
      (∀ y : M, Semiformula.Eval ![y, x] f precCode₁ → Semiformula.Eval ![y] f segGuard) →
        Semiformula.Eval ![x] f segGuard := by
    intro x hx
    rw [hguard x]
    by_cases hxE :
        Semiformula.Eval ![x, (Semiterm.numeral segBound : Semiterm LX ℕ 0).val ![] f] f
          precCode₁
    · refine Or.inr (hProgSeg x ?_)
      intro y hy
      rw [hseg y x] at hy
      rcases (hguard y).mp (hx y hy.1) with hn | hp
      · exact absurd (hTrans f y x _ hy.1 hxE) hn
      · exact hp
    · exact Or.inl hxE
  have hbelow := hTIM f hProg₁
  intro y hy
  rw [hseg y (a.val ![] f)] at hy
  rcases (hguard y).mp (hbelow y hy.1) with hn | hp
  · exact absurd (hTrans f y (a.val ![] f) _ hy.1 hy.2) hn
  · exact hp

/-- **The relativisation at every notation below `ε₀`.**  `Gentzen`'s `ε₀`
bound over the Veblen coding is generic in the induction formula, so it applies
to the guarded formula, and the previous theorem converts. -/
theorem concrete_tiUptoSeg (c : Gamma0Note) (hc : c < epsilonNote 0) :
    paLX ⊢ (TIupto (precCodeSeg (epsilonNote 0)) (gamma0Term c)).univCl :=
  concrete_tiUptoSeg_of_closedTI₁ (gamma0Term c)
    (VeblenEpsilon0UpperBound.concrete_eps0_ti c hc segGuard)

end OrdinalAnalysis.ACA.Relativise

/-! ## Layer 2: the lifted inventory -/

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX Xat TIupto paLX)

/-! ### `∀²`-introduction over the free set variable

`gen₂` wants its conclusion in the shape `∀² φ` with the premise `φ.free₁`.
The lifted theorems come in the shape `toSOAt segWitness χ`, and
`free₁_toSOAtB` says that *is* the eigenvariable form of `toSOAtB boundWitness χ`
— the bound-slot presentation of the same parameter. -/

/-- The bound-slot presentation of the set parameter: `#0 ∈# 0`. -/
def boundWitness : Semiformula ℒₒᵣ ℕ Empty 1 1 :=
  ((#0 : FirstOrder.Semiterm ℒₒᵣ Empty 1) ∈# (0 : Fin 1))

theorem noSetFvar_emb_boundWitness :
    NoSetFvar (FirstOrder.Rewriting.emb boundWitness : Semiproposition ℒₒᵣ 1 1) := by
  simp [boundWitness]

/-- Substituting `ψ` for the bound slot of `boundWitness` returns `ψ` — the
`N = 1` computation of `Lift.lean`'s `lift_paLX₀`. -/
theorem subst₁_boundWitness (ψ : Semiformula ℒₒᵣ ℕ Empty 0 1) :
    Semiproposition.subst₁ boundWitness ![ψ] = ψ := by
  show (SecondOrder.Rew.subst ![ψ]).app boundWitness = _
  simp only [boundWitness, SecondOrder.Rew.app_bvar, SecondOrder.Rew.subst_bv,
    Matrix.cons_val_fin_one]
  exact FirstOrder.Rewriting.subst1_bvar0_eq _

/-- The one-element witness vector, pushed through the embedding. -/
theorem emb_cons_witness (ψ : Semiformula ℒₒᵣ ℕ Empty 0 1) :
    (fun i : Fin 1 => (FirstOrder.Rewriting.emb (![ψ] i) : Semiformula ℒₒᵣ ℕ ℕ 0 1)) =
      ![(FirstOrder.Rewriting.emb ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1)] := by
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  rfl

theorem emb_segWitness :
    (FirstOrder.Rewriting.emb segWitness : Semiformula ℒₒᵣ ℕ ℕ 0 1) = freeWitness := rfl

/-- **The eigenvariable identity.**  `toSOAt segWitness χ` is `free₁` of the
bound-slot lifting — so `gen₂` turns any lifted theorem into its `∀²`-closure. -/
theorem free₁_toSOAtB (χ : FirstOrder.Semiformula LX ℕ 0) :
    Semiproposition.free₁ (toSOAtB boundWitness χ) = toSOAt segWitness χ := by
  rw [← subst₂_shift₁,
    shift₁_eq_self_of_noSetFvar (noSetFvar_toSOAtB noSetFvar_emb_boundWitness χ)]
  have h := subst₁_toSOAtB (ψ := boundWitness) ![segWitness] χ
  rw [emb_cons_witness, emb_segWitness, subst₁_boundWitness] at h
  exact h

/-- **`∀²`-introduction for a lifted theorem.**  This is the *only* way the
assembly ever produces a `∀²`, and it is available for every `paLX`-theorem. -/
theorem genSO {χ : FirstOrder.Semiformula LX ℕ 0}
    (h : Provable ACA (toSOAt segWitness χ)) :
    Provable ACA (∀² (toSOAtB boundWitness χ)) :=
  gen₂ ACA_shift₁_invariant (by rw [free₁_toSOAtB]; exact h)

/-- **`∀²`-introduction, directly from a `paLX`-theorem.** -/
theorem allSetsOfPaLX {σ : FirstOrder.Sentence LX} (h : paLX ⊢ σ) :
    Provable ACA (∀² (toSOAtB boundWitness (FirstOrder.Rewriting.emb σ))) :=
  genSO (lift_paLX_seg h)

/-- **`∀²`-elimination — the `exs₂` rule, i.e. arithmetical comprehension.**
The exact converse of `genSO`: a `∀²`-closed lifted statement may be
instantiated at *any* arithmetical parameter `ψ`, and the result is the lifting
of the same first-order statement at that parameter.

This is the form the tower induction (⋆⋆) needs, where the `∀²` is not a lifted
theorem but a *hypothesis* (`∀²X TI(c,X)`) and the witness is `Jump(X₀)`; for a
`∀²` that does come from a lifted theorem, `Lift.lean`'s `lift_paLX₀` reaches
the same conclusion in one step. -/
theorem specSO (ψ : Semiformula ℒₒᵣ ℕ Empty 0 1)
    (hψ : Arith (FirstOrder.Rewriting.emb ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1))
    {χ : FirstOrder.Semiformula LX ℕ 0}
    (h : Provable ACA (∀² (toSOAtB boundWitness χ))) :
    Provable ACA (toSOAt ψ χ) := by
  have h2 := spec₂ h hψ
  have he := subst₁_toSOAtB (ψ := boundWitness) ![ψ] χ
  rw [emb_cons_witness, subst₁_boundWitness] at he
  rwa [← he]

/-! ### The arithmetical witness `Jump(X₀)`

Instantiating a `∀²` at this witness is *the* use of arithmetical comprehension
in the tower induction (design note §2: "this IS arithmetical comprehension =
the `exs₂` rule; no `compAx` needed"). -/

/-- `Jump(φ)` for `φ := X₀`, as a second-order formula in one number variable. -/
def jumpWitness : Semiformula ℒₒᵣ ℕ ℕ 0 1 :=
  toSOAt segWitness
    (Gentzen.jump Gentzen.CodedVeblen.precCode₁ Gentzen.CodedVeblenJump.addCode₁
      Gentzen.CodedVeblenJump.omegaPowCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)))

theorem arith_jumpWitness : Arith jumpWitness :=
  arith_toSOAt arith_segWitness _

/-! ### The inventory

Each entry is one application of `LiftTI.lean`'s `lift_paLX_seg` to the
corresponding `paLX`-theorem; the statement is the `toSOAt segWitness`-image,
which is definitionally the second-order sentence the assembly wants. -/

open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁)
open OrdinalAnalysis.Gentzen.CodedVeblenJump (addCode₁ omegaPowCode₁ iterCode₁)

/-- **Gentzen's Lemma B**, lifted: `∀a∀u (OmegaPow(u,a) → TI(Jump φ, a) → TI(φ, u))`. -/
theorem jumpB_SO (φ : FirstOrder.Semiformula LX ℕ 1) :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      (Gentzen.jumpBStatement precCode₁ addCode₁ omegaPowCode₁ φ))) :=
  lift_paLX_seg (Gentzen.CodedVeblenJump.jumpB₁ φ)

/-- **Gentzen's Lemma A**, lifted. -/
theorem jumpA_SO (φ : FirstOrder.Semiformula LX ℕ 1) :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      (Gentzen.jumpAStatement precCode₁ addCode₁ omegaPowCode₁ φ))) :=
  lift_paLX_seg (Gentzen.CodedVeblenJump.jumpA₁ φ)

/-- **Zero has no `≺₁`-predecessor**, lifted. -/
theorem noPredZero_SO :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      (Gentzen.noPredZeroStatement precCode₁))) :=
  lift_paLX_seg Gentzen.CodedVeblenJump.noPredZero₁

/-- **`Add(u, 0, u)`**, lifted. -/
theorem zeroAdd_SO :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      (Gentzen.zeroAddStatement addCode₁))) :=
  lift_paLX_seg Gentzen.CodedVeblenJump.zeroAdd₁

/-- **Transitivity of `≺₁`**, lifted. -/
theorem precTrans_SO :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      (Gentzen.Order.precTransStatement precCode₁))) :=
  lift_paLX_seg Gentzen.Epsilon1UpperBound.concrete_precTrans₁

/-- **Transfinite induction below `0` is vacuous**, lifted. -/
theorem tiZero_SO (φ : FirstOrder.Semiformula LX ℕ 1) :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      (Gentzen.Epsilon1UpperBound.closedTI₁ φ
        ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 0)))) :=
  lift_paLX_seg (Gentzen.VeblenEpsilon0UpperBound.concrete_ti_zero₁ φ)

/-- **Downward closure of transfinite induction**, lifted. -/
theorem downward_SO (φ : FirstOrder.Semiformula LX ℕ 1)
    (a b : FirstOrder.Semiterm LX ℕ 0)
    (hab : paLX ⊢ Gentzen.Epsilon1UpperBound.closedPrec₁ a b)
    (hTIb : paLX ⊢ Gentzen.Epsilon1UpperBound.closedTI₁ φ b) :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      (Gentzen.Epsilon1UpperBound.closedTI₁ φ a))) :=
  lift_paLX_seg (Gentzen.VeblenEpsilon0UpperBound.concrete_tiUpto_downward₀ φ a b hab hTIb)

/-- **The successor step at a variable base**, lifted:
`∀e∀s∀y (Base(e) → Add(s,e,1̄) → y ≺₁ s → y ≺₁ e ∨ y = e)`. -/
theorem succStep_SO :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      Gentzen.VeblenSuccStep.succGeneralStatement)) :=
  lift_paLX_seg Gentzen.VeblenSuccStep.concrete_succ_general

/-- **The zero step of the internal ω-tower**, lifted. -/
theorem towerZero_SO :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      (Gentzen.VeblenTower.towerZeroStatement Gentzen.VeblenTower.towerCode₁))) :=
  lift_paLX_seg Gentzen.VeblenTower.concrete_towerZero

/-- **The successor step of the internal ω-tower**, lifted. -/
theorem towerSucc_SO :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      (Gentzen.VeblenTower.towerSuccStatement omegaPowCode₁
        Gentzen.VeblenTower.towerCode₁))) :=
  lift_paLX_seg Gentzen.VeblenTower.concrete_towerSucc

/-- **The internal ω-tower cover**, lifted (general base). -/
theorem cover_SO :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      Gentzen.InternalEpsCover.coverStatement)) :=
  lift_paLX_seg Gentzen.InternalEpsCover.concrete_cover

/-- **The internal ω-tower cover below `ε₀`**, lifted (base `0`). -/
theorem coverZero_SO :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      Gentzen.InternalEpsCover.coverZeroStatement)) :=
  lift_paLX_seg Gentzen.InternalEpsCover.concrete_cover_zero

/-- **Monotonicity of the internal `ε`-function**, lifted (EPSMONO). -/
theorem epsMono_SO :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      Gentzen.InternalEpsMonoCode.epsMonoStatement)) :=
  lift_paLX_seg Gentzen.InternalEpsMonoCode.concrete_epsMono

/-- **Gentzen's `ε₀` bound over the Veblen coding**, lifted: for every external
`c < ε₀` and every formula `φ`, `ACA` proves transfinite induction along `≺₁`
below `c̄` for the lifted `φ`. -/
theorem eps0Ti_SO (c : Gamma0Note) (hc : c < Gamma0Note.epsilonNote 0)
    (φ : FirstOrder.Semiformula LX ℕ 1) :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      (Gentzen.Epsilon1UpperBound.closedTI₁ φ
        (Gentzen.Epsilon1UpperBound.gamma0Term c)))) :=
  lift_paLX_seg (Gentzen.VeblenEpsilon0UpperBound.concrete_eps0_ti c hc φ)

/-- **The `X`-instance of the `ε₀` bound, `∀²`-closed.**  For every external
`c < ε₀`, `ACA ⊢ ∀²X TI(≺₁, c̄, X)`. -/
theorem aca_allSets_tiUpto₁ (c : Gamma0Note) (hc : c < Gamma0Note.epsilonNote 0) :
    Provable ACA (∀² (toSOAtB boundWitness (FirstOrder.Rewriting.emb
      (TIupto precCode₁ (Gentzen.Epsilon1UpperBound.gamma0Term c)).univCl))) :=
  allSetsOfPaLX (Gentzen.VeblenEpsilon0UpperBound.concrete_eps0_TIupto c hc)

/-! ### The syntactic normalisation of a `TIupto`-image

The images above are `toSOAt`-applications; every consumer wants them spelled
out as second-order formulas built from the *image of the ordering* and the
*image of the induction formula*.  Since `Jump.lean`'s `tiUptoAt`/`progAt`/
`belowAt`/`formulaAt`/`precAt` are all built from `Rew.subst` and the
propositional connectives, `Translate.lean`'s commutation lemmas do all the
work, uniformly in the parameter `ψ` and in the ordering.

This is what makes the two sides of the tower induction's comprehension step
meet: `specSO` at a witness `ψ₁` turns `∀²X TI(≺₁,a,X)` into
`tiUptoAtLift P (emb ψ₁) a`, and `jumpB_SO`'s hypothesis is
`tiUptoAtLift P (toSOAt segWitness (jump …)) a` — the same formula as soon as
`emb ψ₁` is the image of the jump. -/

section Normalise

variable {N : ℕ} {ψ : Semiformula ℒₒᵣ ℕ Empty N 1}

/-- `y ≺ x`, second-order. -/
def precAtLift {N n : ℕ} (P : Semiformula ℒₒᵣ ℕ ℕ N 2)
    (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ ℕ N n :=
  FirstOrder.Rew.subst ![y, x] ▹ P

/-- `Ψ(x)`, second-order. -/
def formulaAtLift {N n : ℕ} (Ψ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (x : FirstOrder.Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ ℕ N n := Ψ/[x]

/-- `Below(Ψ, b) :≡ ∀y (y ≺ b → Ψ(y))`, second-order. -/
def belowAtLift {N n : ℕ} (P : Semiformula ℒₒᵣ ℕ ℕ N 2) (Ψ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (b : FirstOrder.Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ ℕ N n :=
  ∀¹ (∼(precAtLift P (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1))
      (FirstOrder.Rew.bShift b)) ⋎ formulaAtLift Ψ #0)

/-- `Prog(Ψ) :≡ ∀x (Below(Ψ,x) → Ψ(x))`, second-order. -/
def progAtLift {N n : ℕ} (P : Semiformula ℒₒᵣ ℕ ℕ N 2) (Ψ : Semiformula ℒₒᵣ ℕ ℕ N 1) :
    Semiformula ℒₒᵣ ℕ ℕ N n :=
  ∀¹ (∼(belowAtLift P Ψ (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1))) ⋎ formulaAtLift Ψ #0)

/-- `TI(Ψ, a) :≡ Prog(Ψ) → Below(Ψ, a)`, second-order. -/
def tiUptoAtLift {N n : ℕ} (P : Semiformula ℒₒᵣ ℕ ℕ N 2) (Ψ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (a : FirstOrder.Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ ℕ N n :=
  ∼(progAtLift P Ψ) ⋎ belowAtLift P Ψ a

@[simp] theorem toSOAtB_precAt (prec : FirstOrder.Semiformula LX ℕ 2) {n : ℕ}
    (y x : FirstOrder.Semiterm LX ℕ n) :
    toSOAtB ψ (Gentzen.precAt prec y x) =
      precAtLift (toSOAtB ψ prec) (unTerm y) (unTerm x) := by
  show toSOAtB ψ (FirstOrder.Rew.subst ![y, x] ▹ prec) = _
  exact toSOAtB_rew (ω := FirstOrder.Rew.subst ![y, x])
    (ω' := FirstOrder.Rew.subst ![unTerm y, unTerm x])
    (fun i => by fin_cases i <;> simp) (fun _ => by simp) prec

@[simp] theorem toSOAtB_formulaAt (φ : FirstOrder.Semiformula LX ℕ 1) {n : ℕ}
    (x : FirstOrder.Semiterm LX ℕ n) :
    toSOAtB ψ (Gentzen.formulaAt φ x) = formulaAtLift (toSOAtB ψ φ) (unTerm x) :=
  toSOAtB_subst₁ φ x

@[simp] theorem toSOAtB_belowAt (prec : FirstOrder.Semiformula LX ℕ 2)
    (φ : FirstOrder.Semiformula LX ℕ 1) {n : ℕ} (b : FirstOrder.Semiterm LX ℕ n) :
    toSOAtB ψ (Gentzen.belowAt prec φ b) =
      belowAtLift (toSOAtB ψ prec) (toSOAtB ψ φ) (unTerm b) := by
  show ∀¹ (toSOAtB ψ (∼(Gentzen.precAt prec (#0 : FirstOrder.Semiterm LX ℕ (n + 1))
    (FirstOrder.Rew.bShift b)) ⋎ Gentzen.formulaAt φ #0)) = _
  rw [toSOAtB_or, toSOAtB_neg, toSOAtB_precAt, toSOAtB_formulaAt, unTerm_bShift]
  rfl

@[simp] theorem toSOAtB_progAt (prec : FirstOrder.Semiformula LX ℕ 2)
    (φ : FirstOrder.Semiformula LX ℕ 1) {n : ℕ} :
    toSOAtB ψ (Gentzen.progAt (n := n) prec φ) =
      progAtLift (toSOAtB ψ prec) (toSOAtB ψ φ) := by
  show ∀¹ (toSOAtB ψ (∼(Gentzen.belowAt prec φ (#0 : FirstOrder.Semiterm LX ℕ (n + 1))) ⋎
    Gentzen.formulaAt φ #0)) = _
  rw [toSOAtB_or, toSOAtB_neg, toSOAtB_belowAt, toSOAtB_formulaAt]
  rfl

/-- **The normalised image of a `TIupto`-instance.** -/
@[simp] theorem toSOAtB_tiUptoAt (prec : FirstOrder.Semiformula LX ℕ 2)
    (φ : FirstOrder.Semiformula LX ℕ 1) {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) :
    toSOAtB ψ (Gentzen.tiUptoAt prec φ a) =
      tiUptoAtLift (toSOAtB ψ prec) (toSOAtB ψ φ) (unTerm a) := by
  show toSOAtB ψ (∼(Gentzen.progAt prec φ) ⋎ Gentzen.belowAt prec φ a) = _
  rw [toSOAtB_or, toSOAtB_neg, toSOAtB_progAt, toSOAtB_belowAt]
  rfl

/-- **The image of a coded (hence `X`-free) formula does not depend on the
parameter.**  Every ordering and graph of the internal-arithmetic files is a `liftCode`, so
`precAtLift (toSOAtB ψ prec) …` is literally the same formula for every `ψ` —
which is what lets the tower induction compare a `spec₂`-instance at one
parameter with a lifted theorem at another. -/
@[simp] theorem toSOAtB_liftCode {n : ℕ} (σ : FirstOrder.Semiformula ℒₒᵣ Empty n) :
    toSOAtB ψ (Gentzen.CodedNotation.liftCode σ) =
      lift (FirstOrder.Rewriting.emb σ : FirstOrder.Semiformula ℒₒᵣ ℕ n) :=
  toSOAtB_lMap _

/-- **The image of the `X`-atom at the induction variable is the parameter
itself.**  With `toSOAtB_tiUptoAt` this says: the image of `TI(≺, X, a)` is
`TI` for the *parameter*, which is the whole point of the parametric lifting. -/
@[simp] theorem toSOAtB_Xat_bvar :
    toSOAtB ψ (Gentzen.Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) =
      (FirstOrder.Rewriting.emb ψ : Semiformula ℒₒᵣ ℕ ℕ N 1) := by
  show (FirstOrder.Rewriting.emb ψ : Semiformula ℒₒᵣ ℕ ℕ N 1)/[(#0 :
    FirstOrder.Semiterm ℒₒᵣ ℕ 1)] = _
  exact FirstOrder.Rewriting.subst1_bvar0_eq _

end Normalise

/-! ### `M0`: the segment form

`ACA/TI.lean`'s `tiUptoSegSO a` is the `toSOAt segWitness`-image of transfinite
induction along the `ε_{ε₀}`-*segment* ordering below `ā`.  Relativise.lean
turns the `≺₁`-bound into it, inside `paLX`; `lift_tiUptoSeg` carries it over. -/

/-- **Transfinite induction along the segment ordering, below every notation
`c < ε₀`.**  This is milestone `M0` of the design note in the form the lower
half (`ACAOmega/ACATheorem.lean`) refutes the unrestricted version of. -/
theorem aca_tiUptoSeg_of_lt_eps0 (c : Gamma0Note) (hc : c < Gamma0Note.epsilonNote 0) :
    Provable ACA (tiUptoSegSO c) :=
  lift_tiUptoSeg c (Relativise.concrete_tiUptoSeg c hc)

end OrdinalAnalysis.ACA
