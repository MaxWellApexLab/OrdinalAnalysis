/-
  Gentzen's jump, lifted along the columns of an omega-jump.

  For a set `Z` with omega-jump `Y` (`ACA/OmegaJump.lean`'s `IsOmegaJump(Y, Z)`),
  column `k + 1` of `Y` is exactly the (Gentzen) jump of column `k` of `Y`.  Lemma B
  (`Gentzen/Jump.lean`'s `jump_B`, instantiated over the coded Veblen ordering by
  `Gentzen/CodedVeblenJump.lean`'s `jumpB₁`) is a `paLX` theorem, generic in its unary
  parameter formula; applied to `columnXatFree` (`OmegaJump.lean`, the formula
  "membership in the column indexed by the free variable `k`") it is *automatically*
  universally closed over `k` as well, since `Semiformula.univCl` closes off every
  stray free variable of its argument, and `k` is `columnXatFree`'s only one.

  This file lifts that fact into the second-order syntax (`ACA/Lift.lean`'s
  `lift_paLX₀`), landing in `ACAplus` (`ACA` plus the omega-jump axiom): the full
  second-order induction scheme is unavoidable here because `lift_paLX`'s only route
  for discharging `paLX`'s induction axiom is `ACA`'s own scheme (an `ACAplus₀`-only
  route, while not ruled out mathematically, would need a lifting of `paLX`'s
  induction axioms into `ACA₀` through arithmetical comprehension and set induction).
-/
import OrdinalAnalysis.ACA.OmegaJump
import OrdinalAnalysis.ACA.Lift

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX XRel Xat toLX paLX)
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁)
open OrdinalAnalysis.Gentzen.CodedVeblenJump (addCode₁ omegaPowCode₁ jumpB₁)

/-! ### Gentzen's Lemma B for the columns of a fixed set -/

/-- **Gentzen's Lemma B for "membership in a column"**, at `paLX`, automatically
closed over the column index `k` (the sole free variable of `columnXatFree`) by
`Semiformula.univCl`. -/
theorem jumpB_column :
    paLX ⊢ Gentzen.jumpBStatement precCode₁ addCode₁ omegaPowCode₁ columnXatFree :=
  jumpB₁ columnXatFree

/-- The `ψ` recovering the free set variable `0` (standing for `Y`), at no bound
set slot — the form `lift_paLX₀` consumes. -/
def yWitFree : Semiformula ℒₒᵣ ℕ Empty 0 1 := (#0 : FirstOrder.Semiterm ℒₒᵣ Empty 1) ∈& 0

theorem arith_yWitFree : Arith (FirstOrder.Rewriting.emb yWitFree : Semiformula ℒₒᵣ ℕ ℕ 0 1) :=
  trivial

/-- **Gentzen's Lemma B for the columns of `Y`, lifted.**  `ACA` proves: for every
column index `k` and every `a, u` with `u = ω^a`, transfinite induction up to `a` for
the jump of column `k` of `Y` gives transfinite induction up to `u` for column `k` of
`Y` itself. -/
theorem jumpB_column_lifted :
    Provable ACA
      (toSOAt yWitFree
        (FirstOrder.Rewriting.emb
          (Gentzen.jumpBStatement precCode₁ addCode₁ omegaPowCode₁ columnXatFree))) :=
  lift_paLX₀ yWitFree arith_yWitFree jumpB_column

/-- The same fact, promoted to `ACAplus` (`ACA` plus the omega-jump axiom), the
theory `ACA/OmegaJump.lean` sets up as the target of the provability argument. -/
theorem jumpB_column_ACAplus :
    Provable ACAplus
      (toSOAt yWitFree
        (FirstOrder.Rewriting.emb
          (Gentzen.jumpBStatement precCode₁ addCode₁ omegaPowCode₁ columnXatFree))) :=
  acaplus_provable_mono jumpB_column_lifted

end OrdinalAnalysis.ACA
