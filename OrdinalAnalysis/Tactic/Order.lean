/-
  `theta_order` and `level_tac`: automation for the order and level facts of the ϑ-notation.

  Goal shapes closed by `theta_order`.
  * principal-against-principal comparisons: `Omega i < Omega j`, `Omega i < theta j b`,
    `theta i a < Omega j`, and (via the `E_k`-clause, unfolded once) `theta k a < theta k b`;
  * principal-against-sum and sum-against-sum comparisons: the `cons`/`nil` clauses of
    `ThetaW/Basic.lean` and `prin_lt_cons_iff`/`cons_lt_prin_iff`;
  * the domain-notation order via its exponent lists (`ThetaWNoteD.lt_iff_entries`,
    `le_iff_entries`) and the monotonicity/indecomposability facts of `ThetaW/Arith.lean`
    (`nadd`, `add`, `omegaPow`, `omegaMul`, `succ`, `ofNat`, and the "closed under `p` from
    below" family `*_lt_prin`/`*_lt_Omega`);
  * `LevLT`/level comparisons, via `level_tac` (`levLT_Omega`, `levLT_theta`,
    `levLT_sum_iff`/`levLTList_iff` unfolded, then `omega`).

  Usage.
  ```
  example : ThetaWTerm.Omega 2 < ThetaWTerm.Omega 3 := by theta_order
  example : ThetaWTerm.theta 1 (ThetaWTerm.Omega 5) < ThetaWTerm.Omega 1 := by theta_order
  example (a b : ThetaWNoteD) (h : a < b) : ThetaWNoteD.omegaPow a < ThetaWNoteD.omegaPow b := by
    theta_order
  example : ThetaWTerm.LevLT 3 (ThetaWTerm.theta 1 (ThetaWTerm.Omega 2)) := by level_tac
  ```

  Implementation.  `theta_order` tries, in order: `decide` (closed terms — `<`/`≤`/`LevLT` are
  all decidable); the named simp set `theta_order_simps` (the `_iff` lemmas above) followed by
  `omega` on whatever numeral inequality is left; and the `OrdinalAnalysis.Order` aesop rule set
  (the monotonicity/indecomposability lemmas, as `safe apply`, with `omega` registered as a leaf
  tactic) for goals the simp set alone does not reduce to arithmetic.  `level_tac` is the same
  idea restricted to the `LevLT` unfolding lemmas, since the general order simp set is more than
  is needed (and, being general, occasionally rewrites a `LevLT` goal into something `omega`
  cannot see through, e.g. under `theta_lt_theta_iff`'s `E_k`-clause).
-/
import OrdinalAnalysis.Tactic.RuleSets
import OrdinalAnalysis.Ordinal.ThetaW.Instance

set_option autoImplicit false

namespace OrdinalAnalysis

/-! ### The `theta_order_simps` simp set -/

attribute [theta_order_simps]
  ThetaWTerm.Omega_lt_Omega_iff
  ThetaWTerm.Omega_lt_theta_iff
  ThetaWTerm.theta_lt_Omega_iff
  ThetaWTerm.not_Omega_lt_Omega
  ThetaWTerm.not_Omega_lt_nil
  ThetaWTerm.Omega_lt_cons_iff
  ThetaWTerm.not_theta_lt_nil
  ThetaWTerm.theta_lt_cons_iff
  ThetaWTerm.nil_lt_Omega
  ThetaWTerm.cons_lt_Omega_iff
  ThetaWTerm.nil_lt_theta
  ThetaWTerm.cons_lt_theta_iff
  ThetaWTerm.not_nil_lt_nil
  ThetaWTerm.nil_lt_cons
  ThetaWTerm.not_cons_lt_nil
  ThetaWTerm.cons_lt_cons_iff
  ThetaWTerm.prin_lt_cons_iff
  ThetaWTerm.nil_lt_prin
  ThetaWTerm.cons_lt_prin_iff
  ThetaWTerm.theta_lt_Omega_self
  ThetaWTerm.Omega_lt_theta_succ
  ThetaWTerm.levLT_Omega
  ThetaWTerm.levLT_theta
  ThetaWTerm.levLTList_iff
  ThetaWTerm.levLT_sum_iff
  ThetaWNoteD.lt_iff_entries
  ThetaWNoteD.le_iff_entries
  ThetaWNoteD.omegaPow_lt_omegaPow_iff
  ThetaWNoteD.lt_omegaPow_iff
  ThetaWNoteD.zero_lt_one
  ThetaWNoteD.entries_zero
  ThetaWNoteD.entries_Omega
  ThetaWNoteD.entries_one

/-! ### The `OrdinalAnalysis.Order` aesop rule set -/

attribute [aesop (rule_sets := [OrdinalAnalysis.Order]) safe apply]
  ThetaWTerm.theta_lt_theta_of_lt_level
  ThetaWTerm.lt_Omega_of_levLT
  ThetaWNoteD.ofNat_lt_ofNat
  ThetaWNoteD.add_lt_add_left
  ThetaWNoteD.nadd_lt_nadd_left
  ThetaWNoteD.nadd_lt_nadd_right
  ThetaWNoteD.omegaPow_lt_omegaPow
  ThetaWNoteD.omegaMul_lt_omegaMul
  ThetaWNoteD.lt_succ
  ThetaWNoteD.le_nadd_left
  ThetaWNoteD.le_nadd_right
  ThetaWNoteD.le_add_left
  ThetaWNoteD.one_lt_prin
  ThetaWNoteD.succ_lt_prin
  ThetaWNoteD.nadd_lt_prin
  ThetaWNoteD.add_lt_prin
  ThetaWNoteD.omegaPow_lt_prin
  ThetaWNoteD.omegaMul_lt_prin
  ThetaWNoteD.nadd_lt_Omega
  ThetaWNoteD.add_lt_Omega
  ThetaWNoteD.omegaPow_lt_Omega

/-! ### The tactics -/

/-- Closes routine order goals of the multi-level ϑ-notation: principal-vs-principal,
principal-vs-sum and sum-vs-sum comparisons, and the monotonicity/indecomposability facts of
`ThetaWNoteD`'s arithmetic.  See the module docstring for the precise shapes and the search
order. -/
macro "theta_order" : tactic =>
  `(tactic|
    first
      | decide
      | (simp_all [theta_order_simps] <;> first | rfl | omega)
      | aesop (rule_sets := [OrdinalAnalysis.Order]) (add safe tactic (by omega))
      | (intros; simp_all [theta_order_simps] <;> first | rfl | omega))

/-- Closes `LevLT n t` goals (and the order facts `lt_Omega_of_levLT` derives from them) by
unfolding `LevLT` down to `Nat` inequalities and calling `omega`. -/
macro "level_tac" : tactic =>
  `(tactic|
    first
      | decide
      | simp only [ThetaWTerm.levLT_Omega, ThetaWTerm.levLT_theta, ThetaWTerm.levLTList_iff,
          ThetaWTerm.levLT_sum_iff] at * <;> omega
      | (intros; simp only [ThetaWTerm.levLT_Omega, ThetaWTerm.levLT_theta,
          ThetaWTerm.levLTList_iff, ThetaWTerm.levLT_sum_iff] at * <;> omega))

end OrdinalAnalysis
