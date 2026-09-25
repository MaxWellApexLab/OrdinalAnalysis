/-
  The `WFormsOmega`-named companions of `Theorem.lean`'s `wForms_positive`/`wForms_levelBounded`.

  `Theorem.lean` already proves, by structural induction over `wForm`/`DF`
  (`positiveIn_DF`, `levelBounded_DF`, `positiveIn_wForm`, `levelBounded_wForm`), that every
  well-ordering operator form is positive in its own predicate and mentions only the predicates
  of levels `≤ k` (`A_0(Y,x) := ∀y(y≺x→Y y)`;
  `D_k(x) := ∀j≤k ∀δ(δ∈E_j(x)→I_j δ)`; `A_{k+1}(Y,x) := D_k(x) ∧ x≺Ω_{k+2} ∧ ∀y(D_k(y)∧y≺x→Y y)`,
  with `I_j`, `j ≤ k`, occurring in both polarities in `A_{k+1}` via the two occurrences of
  `D_k`, and only `I_{k+1}` required positive). It packages this as `wForms_positive`/
  `wForms_levelBounded` for the finite-level family `WForms F n`, consumed by
  `Sound.IDn_consistent` and (via `PredCut.collapseHyps_of_levelBounded`) by the lower-bound
  chain.

  What is missing there is the same packaging for the all-levels family `WFormsOmega F`: the
  fact is already used, but only inline, in `idlt_wForms_consistent`. This file names it, by
  the identical instantiation (`ix := id`) of the already-proved `positiveIn_wForm`/
  `levelBounded_wForm`; no new induction.
-/
import OrdinalAnalysis.IDn.Theorem

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- **Every form of `WFormsOmega F` is positive in its own predicate.** Same instantiation
(`ix := id`) as `idlt_wForms_consistent`'s inline use of `positiveIn_wForm`. -/
theorem wFormsOmega_positive (F : OrderFormulas) : FamilyPositive (WFormsOmega F) :=
  fun k => positiveIn_wForm F id k fun i _ h => by simp only [id] at h; omega

/-- **Every form of `WFormsOmega F` mentions only the predicates of levels `≤ k`.** Same
instantiation (`ix := id`) as `idlt_wForms_consistent`'s inline use of `levelBounded_wForm`. -/
theorem wFormsOmega_levelBounded (F : OrderFormulas) : FamilyLevelBounded (WFormsOmega F) :=
  fun k => levelBounded_wForm F id k fun _ hi => hi

end OrdinalAnalysis.IDn.Upper
