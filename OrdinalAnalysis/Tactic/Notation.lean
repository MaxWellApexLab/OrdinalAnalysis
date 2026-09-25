/-
  `theta_norm`: closed-term evaluation for the multi-level ϑ-notation.

  Goal shapes closed.  Equations (or decidable propositions) between *closed* ϑ-notation
  expressions built from the numerals and the `ThetaWNoteD` operations, e.g.
  `ThetaWNoteD.ofNat 3 + ThetaWNoteD.one = ThetaWNoteD.ofNat 4` or
  `ThetaWNoteD.omegaPow ThetaWNoteD.zero = ThetaWNoteD.one`.  "Closed" means no free variables.

  Usage.
  ```
  example : ThetaWNoteD.ofNat 3 + ThetaWNoteD.one = ThetaWNoteD.ofNat 4 := by theta_norm
  example : ThetaWNoteD.omegaPow ThetaWNoteD.zero = ThetaWNoteD.one := by theta_norm
  example : ThetaWTerm.cTerm 0 = ThetaWTerm.theta 0 (ThetaWTerm.theta 0 ThetaWTerm.zero) := by
    theta_norm
  ```

  Implementation and the well-founded-recursion caveat.  `theta_norm` tries `rfl`, then
  `decide`, then `simp [theta_norm_simps]`, each required to close the goal outright (a partial
  `simp` is treated as failure and the next tactic is tried, not accepted as `first` would by
  default — `first`'s usual semantics only requires a branch not to *throw*, so a `simp` call
  that merely simplifies without closing the goal would otherwise "win" the alternative and
  leave the tactic block with unsolved goals).  If none succeeds, `theta_norm` reports *why*: a
  goal with a free variable is not what `theta_norm` is for (`theta_order`/`dom_tac`/`level_tac`
  are), while a genuinely closed goal that still fails is most likely one whose evaluation needs
  the *general* clause of `ThetaWTerm.ltb`/`cmp`.  These are compiled from a
  `termination_by`/`decreasing_by` (well-founded) recursion, which the kernel's definitional
  reduction does not unfold *at all*, base case or not — confirmed empirically while building
  `Tactic/Dom.lean`: `by decide` on `¬ Dom (theta 0 (theta 1 (Omega 2)))` fails with "did not
  reduce to `isTrue` or `isFalse`", stuck on a call to `ltb` whose head pattern (`Omega _, theta
  _ _`) has *no* recursive call of its own.  So `decide`/`rfl` normalize a closed `ThetaWNoteD`
  arithmetic expression only when its value can be computed *without* ever calling `<`/`≤`/`ltb`
  — plain structural unfolding (`ThetaWTerm.decEq`, `List.replicate`, `ThetaWTerm.cTerm`'s
  definition, or one operation *defined* as another, like `ThetaWNoteD.one := omegaPow zero`).
  The moment an operation has to *sort* its exponents (`+`, `nadd`, `succ`, `omegaMul` on a
  list of more than one distinct entry — `ofNat 3 + one`'s `addL` calls `ltb` to compare
  exponents), `decide`/`rfl` get stuck exactly as `dom_tac`'s did, and only the lemma-driven
  route through `theta_norm_simps` (`ofNat_succ`, `add_one_eq_succ`, `nadd_zero`, `omegaMul_Omega`,
  …: each arithmetic operation's defining identity re-expressed on numerals) gets there, by
  rewriting instead of reducing.
-/
import Lean
import OrdinalAnalysis.Tactic.RuleSets
import OrdinalAnalysis.Ordinal.ThetaW.Instance

set_option autoImplicit false

namespace OrdinalAnalysis

attribute [theta_norm_simps]
  ThetaWNoteD.ofNat_zero
  ThetaWNoteD.ofNat_one
  ThetaWNoteD.ofNat_succ
  ThetaWNoteD.add_one_eq_succ
  ThetaWNoteD.nadd_zero
  ThetaWNoteD.zero_nadd
  ThetaWNoteD.add_zero
  ThetaWNoteD.zero_add
  ThetaWNoteD.omegaMul_zero
  ThetaWNoteD.omegaMul_Omega
  ThetaWNoteD.omegaPow_Omega
  ThetaWNoteD.bot_eq_zero
  ThetaWNoteD.succ

open Lean Elab Tactic Meta

/-- Normalizes a *closed* ϑ-notation equation (or decidable proposition) by `rfl`, then
`decide`, then `simp [theta_norm_simps]`, in that order, each required to close the goal
outright; see the module docstring for the two different, precise error messages given
otherwise. -/
elab "theta_norm" : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  try
    evalTactic (← `(tactic| first | (rfl; done) | (decide; done) | (simp [theta_norm_simps]; done)))
  catch _ =>
    if target.hasFVar then
      throwError m!"theta_norm: the goal{indentD target}\n\
        still contains a free variable — `theta_norm` only normalizes CLOSED ϑ-notation \
        expressions (no variables); for a goal with variables use `theta_order`, `dom_tac`, \
        or `level_tac` instead."
    else
      throwError m!"theta_norm: could not normalize the closed goal{indentD target}\n\
        by `rfl`, `decide`, or `simp`. It most likely needs the general (well-founded-\
        recursive) clause of `ThetaWTerm.ltb`/`cmp`, which does not reduce in the kernel; \
        state it as an order lemma and close it with `theta_order` instead."

end OrdinalAnalysis
