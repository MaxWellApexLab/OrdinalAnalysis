/-
  The tower's zero and successor laws, lifted to the second-order syntax
  without reference to any set — the arithmetic half of the tower-depth
  induction for the columns of an omega-jump.

  `Gentzen/VeblenTower.lean`'s `Tower(u, k, c)` (a tower of `omega`-exponentials
  of height `k` over `c`) never mentions the fresh predicate `X`, so its zero
  and successor laws (`concrete_towerZero`, `concrete_towerSucc`) lift to `ACA`
  at *any* `toSOAtB` witness, in particular `segWitness`
  (`ACA/TI.lean`'s arithmetical placeholder, already used by
  `ACA/TowerInduction.lean`'s own `towerSO`/`omegaPowSO`, which this file
  reuses unchanged).

  These are the tower laws of the tower-depth induction along the columns of an
  omega-jump `Y`: with `Z = column_0 Y`, the induction on the tower depth `d` for
  `theta(d) := forall c u (Tower(u, d, c) -> TIupto(c, column_d Y) ->
  TIupto(u, column_0 Y))` needs no second-order quantifier inside `theta` at
  all (unlike `ACA/TowerInduction.lean`'s `∀²X TI(c, X)`, since `column_d Y` is
  a single already-given set for each `d`, not a universally quantified one).
  The induction itself is carried out in `ACA/OmegaJumpInduction.lean`, inside
  `PA[X]` with the step condition of the omega-jump as a hypothesis.
-/
import OrdinalAnalysis.ACA.OmegaJumpExt
import OrdinalAnalysis.ACA.TowerInduction

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX XRel Xat toLX paLX)
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁)
open OrdinalAnalysis.Gentzen.CodedVeblenJump (addCode₁ omegaPowCode₁)

/-! ### The tower's zero and successor laws, lifted (no `X` involved) -/

theorem towerZero_lifted :
    Provable ACA
      (∀¹ (∀¹ (toSOAtB segWitness
        (∼(Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
            (#0 : FirstOrder.Semiterm LX ℕ 2) ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2) #1) ⋎
          (“#0 = #1” : FirstOrder.Semiformula LX ℕ 2))))) := by
  have h := lift_paLX₀ segWitness arith_segWitness Gentzen.VeblenTower.concrete_towerZero
  unfold Gentzen.VeblenTower.towerZeroStatement at h
  have hfv : (Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
      (#0 : FirstOrder.Semiterm LX ℕ 2) ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2) #1).freeVariables
        = ∅ :=
    TowerSyntax.freeVariables_towerAt (by simp) (by simp) (by simp)
  have hfvEq : (“#0 = #1” : FirstOrder.Semiformula LX ℕ 2).freeVariables = ∅ := by
    rw [FirstOrder.Semiformula.Operator.eq_def, FirstOrder.Semiformula.freeVariables_rel]
    decide
  rw [TowerSyntax.emb_univCl_of_closed (by simp [hfv, hfvEq])] at h
  exact h

theorem towerSucc_lifted :
    Provable ACA
      (∀¹ (∀¹ (∀¹ (toSOAtB segWitness
        (∼(Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
            (#0 : FirstOrder.Semiterm LX ℕ 3) (‘(#1 + 1)’ : FirstOrder.Semiterm LX ℕ 3) #2) ⋎
          (∃¹ (Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
              (#0 : FirstOrder.Semiterm LX ℕ 4) #2 #3 ⋏
            Gentzen.omegaPowAt omegaPowCode₁ (#1 : FirstOrder.Semiterm LX ℕ 4) #0))))))) := by
  have h := lift_paLX₀ segWitness arith_segWitness
    Gentzen.VeblenTower.concrete_towerSucc
  unfold Gentzen.VeblenTower.towerSuccStatement at h
  have hfv1 : FirstOrder.Semiformula.freeVariables (Gentzen.VeblenTower.towerAt
      Gentzen.VeblenTower.towerCode₁
      (#0 : FirstOrder.Semiterm LX ℕ 3) (‘(#1 + 1)’ : FirstOrder.Semiterm LX ℕ 3) #2) = ∅ :=
    TowerSyntax.freeVariables_towerAt (by simp) (by simp) (by simp)
  have hfv2 : FirstOrder.Semiformula.freeVariables (Gentzen.VeblenTower.towerAt
      Gentzen.VeblenTower.towerCode₁
      (#0 : FirstOrder.Semiterm LX ℕ 4) #2 #3) = ∅ :=
    TowerSyntax.freeVariables_towerAt (by simp) (by simp) (by simp)
  have hfv3 : FirstOrder.Semiformula.freeVariables (Gentzen.omegaPowAt omegaPowCode₁
      (#1 : FirstOrder.Semiterm LX ℕ 4) #0) = ∅ :=
    TowerSyntax.freeVariables_omegaPowAt (by simp) (by simp)
  rw [TowerSyntax.emb_univCl_of_closed (by simp [hfv1, hfv2, hfv3])] at h
  exact h

end OrdinalAnalysis.ACA
