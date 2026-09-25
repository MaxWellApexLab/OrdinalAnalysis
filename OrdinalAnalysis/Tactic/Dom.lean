/-
  `dom_tac`: automation for the domain and normal-form side goals of the ϑ-notation.

  Goal shapes closed.  `dom_tac` closes goals of the form
  * `ThetaWTerm.Dom t`
  * `ThetaWTerm.NF t`
  * `ThetaWTerm.NF t ∧ ThetaWTerm.Dom t`
  for terms `t` built from `ThetaWTerm.Omega k`, `ThetaWTerm.theta k _`, `ThetaWTerm.sum _`
  (equivalently `ThetaWTerm.zero`, `ThetaWTerm.cTerm`, …) and the `ThetaWNoteD` operations
  (`nadd`, `add`, `omegaPow`, `omegaMul`, `succ`, `one`, `ofNat`, `zero`), together with goals
  that *extract* `NF`/`Dom` from a hypothesis or from a `ThetaWNoteD`/`ThetaWNote` element
  already in context (the `.2.1`/`.2.2` subtype-projection idiom used throughout
  `Ordinal/ThetaW/*.lean`).

  Usage.
  ```
  example : ThetaWTerm.Dom (ThetaWTerm.cTerm 3) := by dom_tac
  example (a : ThetaWNoteD) : ThetaWTerm.NF a.1 := by dom_tac
  example : ThetaWTerm.NF (ThetaWTerm.theta 0 (ThetaWTerm.Omega 1)) ∧
      ThetaWTerm.Dom (ThetaWTerm.theta 0 (ThetaWTerm.Omega 1)) := by dom_tac
  ```

  Implementation.  Two layers, tried in order:
  1. `decide` — `Dom`/`NF` are `DecidablePred`, so any goal about a *closed* term (no free
     variables) is settled by evaluation; this is the common case for the small terms used in
     sanity checks and one-off lemmas (`c_n`, `ϑ₀(Ω_{n+1})`, …).
  2. an `aesop` rule set (`OrdinalAnalysis.Dom`) assembled from the `dom_*`/`nf_*` lemmas of
     `ThetaW/Dom.lean`, `ThetaW/Arith.lean`, `ThetaW/Instance.lean` and `ThetaW/Veblen.lean`:
     the `_iff` lemmas as `simp` (unfolding normalizers), the "build a bigger domain term"
     lemmas (`dom_theta_of_G_nil`, `dom_theta_Omega`, `dom_cTerm`, the `ThetaWNoteD.dom_*`
     family, …) as `safe apply`, and the "extract a smaller one" lemmas (`Dom.theta_arg`,
     `Dom.of_mem`, `Dom.of_mem_E`, `Dom.of_mem_G`, `Dom.of_mem_toList`, and their `NF`
     counterparts) as `safe forward`, together with a plain `omega` fallback for the numeral
     side conditions (`k < k`, `k ≤ k + 1`, …) that show up under `G_k`/`E_k`.

  `grind` was tried as a third layer: it discharges the `decide`
  cases as fast as `decide` itself but does not chase the `dom_*`/`nf_*` lemma set the way
  `aesop`'s rule set does, so it is not included in `dom_tac`'s search — a user wanting to try
  it directly still can (`by grind [ThetaWTerm.dom_theta_iff, ...]`).
-/
import OrdinalAnalysis.Tactic.RuleSets
import OrdinalAnalysis.Ordinal.ThetaW.Veblen
import OrdinalAnalysis.Ordinal.ThetaW.Instance

set_option autoImplicit false

namespace OrdinalAnalysis

/-! ### Subtype-projection helpers for the `.2.1`/`.2.2` idiom -/

namespace ThetaWNoteD

theorem nf_val (a : ThetaWNoteD) : ThetaWTerm.NF a.1 := a.2.1
theorem dom_val (a : ThetaWNoteD) : ThetaWTerm.Dom a.1 := a.2.2

end ThetaWNoteD

namespace ThetaWNote

theorem nf_val (a : ThetaWNote) : ThetaWTerm.NF a.1 := a.2

end ThetaWNote

/-! ### Registering the rule set -/

attribute [aesop (rule_sets := [OrdinalAnalysis.Dom]) norm simp]
  ThetaWTerm.dom_theta_iff
  ThetaWTerm.nf_theta_iff
  ThetaWTerm.dom_sum_iff
  ThetaWTerm.nf_sum_iff
  ThetaWTerm.domList_iff
  ThetaWTerm.nfList_iff
  ThetaWTerm.dom_ofList_iff
  ThetaWTerm.dom_Omega
  ThetaWTerm.nf_Omega
  -- The `Dom`/`NF` side conditions bottom out in raw order facts (`Dom (theta k a)`'s
  -- `∀ x ∈ G k a, x < a`, unfolded); these order `_iff` lemmas (from `ThetaW/{Basic,Order}`,
  -- already transitively imported) let the same aesop call discharge them, instead of getting
  -- stuck on a bare `Omega i < theta j b` it has no rule for.
  ThetaWTerm.Omega_lt_Omega_iff
  ThetaWTerm.Omega_lt_theta_iff
  ThetaWTerm.theta_lt_Omega_iff
  ThetaWTerm.not_Omega_lt_nil
  ThetaWTerm.Omega_lt_cons_iff
  ThetaWTerm.not_theta_lt_nil
  ThetaWTerm.theta_lt_cons_iff
  ThetaWTerm.nil_lt_Omega
  ThetaWTerm.cons_lt_Omega_iff
  ThetaWTerm.nil_lt_theta
  ThetaWTerm.cons_lt_theta_iff
  ThetaWTerm.cons_lt_cons_iff
  ThetaWTerm.le_def
  -- `G_k`'s two conditional equations (the unconditional `G_Omega`/`G_nil`/`G_cons` clauses
  -- are already global `@[simp]` lemmas upstream): needed to turn `G k (theta j a)` into a
  -- concrete list before `Dom`'s `∀ x ∈ G k a, x < a` can be checked pointwise.
  ThetaWTerm.G_theta_of_lt
  ThetaWTerm.G_theta_of_le

attribute [aesop (rule_sets := [OrdinalAnalysis.Dom]) safe apply]
  ThetaWTerm.dom_zero
  ThetaWTerm.nf_zero
  ThetaWTerm.dom_theta_of_G_nil
  ThetaWTerm.dom_theta_Omega
  ThetaWTerm.dom_cTerm
  ThetaWTerm.nf_cTerm
  ThetaWNoteD.nf_phi
  ThetaWNoteD.dom_phi_of_lt
  ThetaWNoteD.nf_val
  ThetaWNoteD.dom_val
  ThetaWNote.nf_val
  ThetaWNoteD.dom_nadd
  ThetaWNoteD.dom_add
  ThetaWNoteD.dom_omegaPow
  ThetaWNoteD.dom_omegaMul
  ThetaWNoteD.dom_one
  ThetaWNoteD.dom_ofNat
  ThetaWNoteD.dom_succ
  ThetaWNoteD.dom_omegaMulOmega

attribute [aesop (rule_sets := [OrdinalAnalysis.Dom]) safe forward]
  ThetaWTerm.Dom.theta_arg
  ThetaWTerm.Dom.of_mem
  ThetaWTerm.Dom.of_mem_E
  ThetaWTerm.Dom.of_mem_G
  ThetaWTerm.Dom.of_mem_toList
  ThetaWTerm.NF.theta_arg
  ThetaWTerm.NF.of_mem
  ThetaWTerm.NF.of_mem_E
  ThetaWTerm.NF.of_mem_G

/-! ### The tactic -/

/-- Closes `Dom t`, `NF t` and `NF t ∧ Dom t` goals for the multi-level ϑ-notation: a fast
`decide` path for closed terms, then the `OrdinalAnalysis.Dom` aesop rule set (with `omega` as
a leaf tactic for the numeral side conditions) for everything else. -/
macro "dom_tac" : tactic =>
  `(tactic|
    first
      | decide
      | aesop (rule_sets := [OrdinalAnalysis.Dom]) (add safe tactic (by omega))
      | (intros; aesop (rule_sets := [OrdinalAnalysis.Dom]) (add safe tactic (by omega))))

end OrdinalAnalysis
