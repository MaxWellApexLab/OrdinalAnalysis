/-
  Formula extensionality for `TIupto`, and the successor step of the
  omega-jump's column tower.

  `Gentzen/Jump.lean`'s `TIupto(prec, phi, a)` depends on its parameter formula
  `phi` only through its extension: if `phi` and `psi` agree pointwise, so do
  `TIupto(prec, phi, ·)` and `TIupto(prec, psi, ·)`.  This is proved directly at
  `paLX`, semantically (`Theory.Proof.complete`, exactly the technique
  `Gentzen/Jump.lean`'s `jump_B` and `Gentzen/JumpProgressive.lean`'s `jump_A`
  already use), since `eval_tiUptoAt`/`eval_progAt`/`eval_belowAt` already
  reduce both sides to the same nested shape built from `phi.Eval`/`psi.Eval`,
  which a pointwise hypothesis rewrites into each other termwise.

  Combined with `OmegaJumpTower.lean`'s `jumpB_column_ACAplus` and the omega-jump
  axiom's step condition (`OmegaJump.lean`'s `hierStep`, which gives exactly the
  pointwise equivalence needed between "column `k + 1`" and "the jump of column
  `k`"), this replaces `Jump(column_k Y)` in `jumpB_column_ACAplus`'s hypothesis
  by `column_{k+1} Y`, eliminating the jump construction from the externally
  visible statement of the successor step.
-/
import OrdinalAnalysis.ACA.OmegaJumpTower

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX XRel Xat toLX paLX)
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁)
open OrdinalAnalysis.Gentzen.CodedVeblenJump (addCode₁ omegaPowCode₁)

/-! ### Formula extensionality for `TIupto`, at `paLX` -/

/-- The body of `TIupto(prec, phi, ·) ↔ TIupto(prec, psi, ·)`, as a formula in
the one variable `a`. -/
def tiUptoCongrBody (prec : FirstOrder.Semiformula LX ℕ 2) (φ ψ : FirstOrder.Semiformula LX ℕ 1) :
    FirstOrder.Semiformula LX ℕ 1 :=
  (Gentzen.tiUptoAt prec φ (#0 : FirstOrder.Semiterm LX ℕ 1)) 🡘
    (Gentzen.tiUptoAt prec ψ (#0 : FirstOrder.Semiterm LX ℕ 1))

/-- **Formula extensionality for `TIupto`**: if `phi` and `psi` agree at every
point, `TIupto(prec, phi, ·)` and `TIupto(prec, psi, ·)` agree at every ordinal
notation. -/
def tiUptoCongrStatement (prec : FirstOrder.Semiformula LX ℕ 2)
    (φ ψ : FirstOrder.Semiformula LX ℕ 1) : FirstOrder.Sentence LX :=
  (∀¹ (φ 🡘 ψ) 🡒 ∀¹ (tiUptoCongrBody prec φ ψ)).univCl

theorem tiUpto_congr (prec : FirstOrder.Semiformula LX ℕ 2)
    (φ ψ : FirstOrder.Semiformula LX ℕ 1) :
    paLX ⊢ tiUptoCongrStatement prec φ ψ := by
  apply FirstOrder.Theory.Proof.complete.{0, 0}
  rw [FirstOrder.consequence_iff']
  intro M _ _ _
  rw [FirstOrder.models_iff]
  simp only [tiUptoCongrStatement, tiUptoCongrBody, FirstOrder.Semiformula.eval_univCl,
    FirstOrder.Semiformula.eval_all, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_iff, LogicalConnective.Prop.iff_eq, Gentzen.eval_tiUptoAt]
  intro f hiff a
  simp only [hiff]

/-! ### The successor step, `column_k` to `column_{k+1}`, without `Jump` -/

/-- `k + 1`, with `k` the free variable `&0` — `Rew.free` turns the bound `#0`
of `‘#0 + 1’` into the free `&0`. -/
def succFreeTerm : FirstOrder.Semiterm LX ℕ 0 :=
  FirstOrder.Rew.free (‘#0 + 1’ : FirstOrder.Semiterm LX ℕ 1)

/-- `column_{k+1}`, with the column index `k` the free variable `&0`, as the
unary formula `tiUptoCongrStatement` expects. -/
def columnSuccXatFree : FirstOrder.Semiformula LX ℕ 1 :=
  columnXat (FirstOrder.Rew.bShift succFreeTerm) (#0 : FirstOrder.Semiterm LX ℕ 1)

/-- **Formula extensionality for `TIupto`, specialised to a column and its
jump, lifted.**  `ACA` proves: for every column index `k`, if column `k + 1`
and the jump of column `k` agree pointwise, `TIupto` for one at any ordinal
notation is equivalent to `TIupto` for the other. -/
theorem tiUpto_congr_column_lifted :
    Provable ACA
      (toSOAt yWitFree
        (FirstOrder.Rewriting.emb
          (tiUptoCongrStatement precCode₁ columnSuccXatFree jumpColumnFree))) :=
  lift_paLX₀ yWitFree arith_yWitFree (tiUpto_congr precCode₁ columnSuccXatFree jumpColumnFree)

/-- The same fact, promoted to `ACAplus`.  Together with
`OmegaJumpTower.jumpB_column_ACAplus`, whose hypothesis `TIupto(Jump(column_k
Y), a)` this lets one replace by `TIupto(column_{k+1} Y, a)` (given the omega-
jump axiom's step condition for the column index at hand), this is the
successor step of the column tower: for every `k`, `a`, `u` with `ω^a = u`,
`TIupto(column_{k+1} Y, a)` gives `TIupto(column_k Y, u)`.  The two facts are
combined at their point of use (`OmegaJumpDepth.lean`), where the shared
column index `k` is opened by `spec₁` on both simultaneously rather than
re-closed here. -/
theorem tiUpto_congr_column_ACAplus :
    Provable ACAplus
      (toSOAt yWitFree
        (FirstOrder.Rewriting.emb
          (tiUptoCongrStatement precCode₁ columnSuccXatFree jumpColumnFree))) :=
  acaplus_provable_mono tiUpto_congr_column_lifted

end OrdinalAnalysis.ACA
