/-
  Declarations of the `aesop` rule sets and the `simp` set used by the tactics of this
  directory.

  `aesop`'s `declare_aesop_rule_sets` command (and, identically, Mathlib's `register_simp_attr`
  for a named `simp` set) registers a name in the environment, but the registration is only
  visible to files that *import* the declaring module — "in Lean 4, one cannot use an attribute
  in the same file where it was declared" (`Mathlib/Tactic/Attr/Register.lean`'s own docstring,
  which is exactly why Mathlib registers all of its named simp sets in one dedicated file).  So
  both declarations have to live in their own file, imported by every module that attaches
  rules to a set (`Dom.lean`, `Order.lean`) and by `Test.lean`, which calls the tactics built
  from them.
-/
import Aesop
import Mathlib.Tactic.Attr.Register

set_option autoImplicit false

namespace OrdinalAnalysis

-- Domain (`Dom`) and normal-form (`NF`) side goals of the ϑ-notation; used by `dom_tac`
-- (`Tactic/Dom.lean`).  (A leading `/-- -/` doc comment is not accepted before this command,
-- hence the plain `--` comments.)
declare_aesop_rule_sets [OrdinalAnalysis.Dom] (default := false)

-- Order and level facts of the ϑ-notation; used by `theta_order`/`level_tac`
-- (`Tactic/Order.lean`).
declare_aesop_rule_sets [OrdinalAnalysis.Order] (default := false)

/-- The named `simp` set of routine order/level facts for the multi-level ϑ-notation, driven
by `theta_order` (`Tactic/Order.lean`). -/
register_simp_attr theta_order_simps

/-- The named `simp` set of numeral/arithmetic identities for the multi-level ϑ-notation, used
by `theta_norm` (`Tactic/Notation.lean`) as its last resort after `rfl`/`decide`: the identities
that express an arithmetic operation on `ThetaWNoteD` (`+`, `nadd`, `omegaMul`, `succ`) in terms
of the *numerals*, so that closed goals whose evaluation would otherwise need the well-founded-
recursive order comparison `ThetaWTerm.ltb` (which does not reduce in the kernel — see
`Tactic/Notation.lean`'s module docstring) can still be settled lemma-by-lemma. -/
register_simp_attr theta_norm_simps

end OrdinalAnalysis
