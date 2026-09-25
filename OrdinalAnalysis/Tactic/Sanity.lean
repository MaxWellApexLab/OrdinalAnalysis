/-
  `sanity_check`: a property-test battery convention for the ϑ-notation development.

  A "sanity check" is a small, self-contained fact — usually a slot/shape check ("this
  particular nesting of `theta`/`Omega` is/isn't in the domain", "this order fact on small
  terms holds") — recorded once and for all as its own named theorem, so that a later change to
  `ThetaW/*` that silently breaks one of these small facts is caught by `lake build` rather than
  discovered by accident deep inside a large proof.

  Usage.
  ```
  sanity_check "cTerm3_dom" : ThetaWTerm.Dom (ThetaWTerm.cTerm 3) := by dom_tac
  ```
  expands to a theorem named `OrdinalAnalysis.Sanity.check_cTerm3_dom` (the string is turned
  into an identifier by replacing every non-alphanumeric character with `_`; a `#sanity_report`
  right after prints every registered check found so far in the environment, sorted by name).

  Naming convention (for a script, or a human, to find and run these without `#sanity_report`):
  every `sanity_check "foo" : ... := ...` expands to `theorem OrdinalAnalysis.Sanity.check_foo`,
  so `grep -n 'theorem OrdinalAnalysis.Sanity.check_' OrdinalAnalysis/Tactic/*.lean` lists every
  one, and `lake build OrdinalAnalysis.Tactic.Sanity` (re)proves them all at once — a check that
  no longer type-checks or whose proof no longer goes through fails the build exactly like any
  other theorem, no separate test runner needed.
-/
import Lean
import OrdinalAnalysis.Tactic.Dom
import OrdinalAnalysis.Tactic.Order
import OrdinalAnalysis.Tactic.Notation

set_option autoImplicit false

namespace OrdinalAnalysis

/-! ### The `sanity_check` command -/

/-- Turns an arbitrary string into a valid identifier fragment: every character that is not
alphanumeric becomes `_`, and a leading digit gets an `_` prefix (identifiers cannot start with
a digit). -/
def sanityIdentFragment (s : String) : String :=
  let mapped := String.ofList (s.toList.map fun c => if c.isAlphanum then c else '_')
  if mapped.isEmpty then "unnamed"
  else if mapped.front.isDigit then "_" ++ mapped else mapped

/-- The name a `sanity_check "s"` expands to, *relative to the enclosing namespace* —
`Sanity.check_s` (with `s` sanitized by `sanityIdentFragment`).  Every use in this development
is inside `namespace OrdinalAnalysis`, so the declaration's absolute name is
`OrdinalAnalysis.Sanity.check_s`; `#sanity_report` looks for exactly that absolute prefix. -/
def sanityCheckName (s : String) : Lean.Name :=
  .str (.str .anonymous "Sanity") ("check_" ++ sanityIdentFragment s)

/-- `sanity_check "name" : prop := proof` registers `proof : prop` as a named sanity check
(a plain `theorem`, so an unprovable or ill-typed check simply fails the build like any other
theorem — there is nothing further to "run"). -/
syntax (name := sanityCheckCmd) "sanity_check " str " : " term " := " term : command

macro_rules
  | `(sanity_check $n:str : $p:term := $prf:term) => do
      let ident := Lean.mkIdentFrom n (sanityCheckName n.getString)
      `(theorem $ident : $p := $prf)

-- Lists every registered `sanity_check` found in the environment so far (by the
-- `OrdinalAnalysis.Sanity` name prefix `sanity_check` always expands under), sorted by name.
-- (A leading `/-- -/` doc comment is not accepted before an `open ... in elab ...` command,
-- hence the plain `--` comment, as with `declare_aesop_rule_sets` in `RuleSets.lean`.)
open Lean Elab Command in
elab "#sanity_report" : command => do
  let env ← getEnv
  let prefix_ : Name := .str (.str .anonymous "OrdinalAnalysis") "Sanity"
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁ do
    if prefix_.isPrefixOf n && !n.isInternalDetail then names := names.push n
  for (n, _) in env.constants.map₂ do
    if prefix_.isPrefixOf n && !n.isInternalDetail then names := names.push n
  let sorted := names.qsort (fun a b => a.toString < b.toString)
  if sorted.isEmpty then
    logInfo "#sanity_report: no sanity checks registered yet"
  else
    let mut msg := m!"#sanity_report: {sorted.size} sanity check(s) registered"
    for n in sorted do
      msg := msg ++ m!"\n  {n}"
    logInfo msg

/-! ### Sanity checks for `ThetaWTerm`/`ThetaWNoteD`

Slot/shape checks (which nestings of `theta`/`Omega` are in the domain), order facts on small
terms, level facts, and a few closed-term arithmetic identities — one line each, closed by the
tactics of this directory. -/

open ThetaWTerm in
sanity_check "theta0_theta1_Omega2_not_dom" :
    ¬ Dom (theta 0 (theta 1 (Omega 2))) := by dom_tac

open ThetaWTerm in
sanity_check "theta1_theta0_Omega2_dom" :
    Dom (theta 1 (theta 0 (Omega 2))) := by dom_tac

open ThetaWTerm in
sanity_check "cTerm3_dom" : Dom (cTerm 3) := by dom_tac

open ThetaWTerm in
sanity_check "cTerm3_nf" : NF (cTerm 3) := by dom_tac

open ThetaWTerm in
sanity_check "theta1_Omega5_dom" : Dom (theta 1 (Omega 5)) := by dom_tac

open ThetaWTerm in
sanity_check "omega2_lt_omega3" : Omega 2 < Omega 3 := by theta_order

open ThetaWTerm in
sanity_check "omega3_not_lt_omega2" : ¬ Omega 3 < Omega 2 := by theta_order

open ThetaWTerm in
sanity_check "theta1_Omega5_lt_Omega1" : theta 1 (Omega 5) < Omega 1 := by theta_order

open ThetaWTerm in
sanity_check "theta0_lt_theta1_same_arg" : theta 0 (Omega 3) < theta 1 (Omega 3) := by theta_order

open ThetaWTerm in
sanity_check "levLT3_theta1_Omega2" : LevLT 3 (theta 1 (Omega 2)) := by level_tac

open ThetaWTerm in
sanity_check "not_levLT2_theta1_Omega5" : ¬ LevLT 2 (theta 1 (Omega 5)) := by level_tac

open ThetaWTerm in
sanity_check "theta1_Omega5_dom_but_not_levLT2" :
    Dom (theta 1 (Omega 5)) ∧ ¬ LevLT 2 (theta 1 (Omega 5)) :=
  ⟨by dom_tac, by level_tac⟩

sanity_check "ofNat3_add_one_eq_ofNat4" :
    ThetaWNoteD.ofNat 3 + ThetaWNoteD.one = ThetaWNoteD.ofNat 4 := by theta_norm

sanity_check "succ_zero_eq_one" :
    ThetaWNoteD.succ ThetaWNoteD.zero = ThetaWNoteD.one := by theta_norm

open ThetaWTerm in
sanity_check "cTerm0_eq_theta0_theta0_zero" :
    cTerm 0 = theta 0 (theta 0 zero) := by theta_norm

#sanity_report

end OrdinalAnalysis
