/-
  Acceptance test: the tactics of this directory (`dom_tac`, `theta_order`, `level_tac`,
  `theta_norm`) on real goal shapes drawn from `Ordinal/ThetaW/{Basic,Order,Dom,Arith,Instance,
  Veblen,Descent}.lean` — every `example` below either restates a real lemma of one of those
  files (same statement, sometimes specialized to concrete numerals) or is the kind of side
  goal that recurs, hand-proved, throughout `ThetaW/*` and `ID1/*` (a `Dom`/`NF` obligation, an
  `Omega`/`theta` comparison, a `LevLT` fact, a closed numeral computation).  Every example is
  closed in one line by exactly one of the four tactics; none uses `sorry` and none needs
  `native_decide`.  This file is the acceptance test: if it compiles
  (`lake build OrdinalAnalysis.Tactic.Test`), the tactics work on real goals, not just on
  hand-picked toys.
-/
import OrdinalAnalysis.Tactic.Dom
import OrdinalAnalysis.Tactic.Order
import OrdinalAnalysis.Tactic.Notation
import OrdinalAnalysis.Tactic.Sanity

set_option autoImplicit false

namespace OrdinalAnalysis
open ThetaWTerm

/-! ### `dom_tac` — `Dom`/`NF` goals (from `ThetaW/Dom.lean`, `ThetaW/Arith.lean`,
`ThetaW/Instance.lean`, `ThetaW/Veblen.lean`) -/

example (k : ℕ) : Dom (Omega k) := by dom_tac

example (k : ℕ) : NF (Omega k) := by dom_tac

example (k n : ℕ) : Dom (theta k (Omega n)) := by dom_tac

example (n : ℕ) : Dom (cTerm n) := by dom_tac

example (n : ℕ) : NF (cTerm n) := by dom_tac

-- `ThetaW/Dom.lean`'s `dom_tower_one`.
example (j : ℕ) : Dom (tower j 1) := by dom_tac

-- `ThetaW/Dom.lean`'s `theta1_Omega5_lt_Omega1`'s companion `dom_theta1_Omega5`.
example : Dom (theta 1 (Omega 5)) := by dom_tac

-- The slot check, restated as an ordinary goal (also a `sanity_check`
-- in `Sanity.lean`): nesting a *higher*-level collapse inside a lower one is not in the domain.
example : ¬ Dom (theta 0 (theta 1 (Omega 2))) := by dom_tac

-- …while the other nesting order is fine (`G_k` only looks at levels `> k`).
example : Dom (theta 1 (theta 0 (Omega 2))) := by dom_tac

example (k : ℕ) (a : ThetaWTerm) (h : Dom (theta k a)) : Dom a := by dom_tac

example (k : ℕ) (a : ThetaWTerm) (h : NF (theta k a)) : NF a := by dom_tac

example (xs : List ThetaWTerm) (x : ThetaWTerm) (h : Dom (sum xs)) (hx : x ∈ xs) : Dom x := by
  dom_tac

-- The `.2.1`/`.2.2` subtype-projection idiom used throughout `ThetaW/Arith.lean`.
example (a : ThetaWNoteD) : NF a.1 := by dom_tac

example (a : ThetaWNoteD) : Dom a.1 := by dom_tac

example (a b : ThetaWNoteD) : Dom (ThetaWNoteD.nadd a b).1 := by dom_tac

example (a b : ThetaWNoteD) : Dom (a + b).1 := by dom_tac

example (a : ThetaWNoteD) : Dom (ThetaWNoteD.omegaPow a).1 := by dom_tac

example (a : ThetaWNoteD) : Dom (ThetaWNoteD.omegaMul a).1 := by dom_tac

example (n : ℕ) : Dom (ThetaWNoteD.ofNat n).1 := by dom_tac

-- `ThetaW/Veblen.lean`'s `dom_phi_of_lt`.
example (k : ℕ) (rho beta : ThetaWNoteD) (hrho : rho < ThetaWNoteD.Omega k)
    (hbeta : beta < ThetaWNoteD.Omega k) : Dom (ThetaWNoteD.phi k rho beta) := by dom_tac

example : NF (theta 0 (Omega 1)) ∧ Dom (theta 0 (Omega 1)) := by dom_tac

/-! ### `theta_order`/`level_tac` — order and level goals (from `ThetaW/{Basic,Order,Dom}.lean`,
`ThetaW/Arith.lean`) -/

example (i j : ℕ) (h : i < j) : Omega i < Omega j := by theta_order

example : Omega 3 < Omega 5 := by theta_order

example : ¬ Omega 5 < Omega 2 := by theta_order

example (k n : ℕ) : theta k (Omega n) < Omega k := by theta_order

-- `ThetaW/Dom.lean`'s `theta1_Omega5_lt_Omega1`.
example : theta 1 (Omega 5) < Omega 1 := by theta_order

example (k : ℕ) (a : ThetaWTerm) : Omega k < theta (k + 1) a := by theta_order

example (i j : ℕ) (h : i < j) (a b : ThetaWTerm) : theta i a < theta j b := by theta_order

-- `ThetaW/Dom.lean`'s `levLT_Omega1`.
example : LevLT 2 (Omega 1) := by level_tac

-- `ThetaW/Dom.lean`'s `not_levLT_theta1_Omega5`.
example : ¬ LevLT 2 (theta 1 (Omega 5)) := by level_tac

example : LevLT 3 (theta 1 (Omega 2)) := by level_tac

example (m n k : ℕ) (h : m ≤ n) (hm : LevLT m (Omega k)) : LevLT n (Omega k) := by level_tac

example (a b c : ThetaWNoteD) (h : a < b) : ThetaWNoteD.nadd a c < ThetaWNoteD.nadd b c := by
  theta_order

example (a b c : ThetaWNoteD) (h : b < c) : a + b < a + c := by theta_order

example (a b : ThetaWNoteD) (h : a < b) : ThetaWNoteD.omegaPow a < ThetaWNoteD.omegaPow b := by
  theta_order

example (a b : ThetaWNoteD) (h : a < b) : ThetaWNoteD.omegaMul a < ThetaWNoteD.omegaMul b := by
  theta_order

example (m n : ℕ) (h : m < n) : ThetaWNoteD.ofNat m < ThetaWNoteD.ofNat n := by theta_order

example (p : ThetaWNoteD) (hp : IsPrin p.1) : ThetaWNoteD.one < p := by theta_order

example (a p : ThetaWNoteD) (hp : IsPrin p.1) (h : a < p) : ThetaWNoteD.succ a < p := by
  theta_order

example (k : ℕ) (a : ThetaWNoteD) (h : a < ThetaWNoteD.Omega k) :
    ThetaWNoteD.omegaPow a < ThetaWNoteD.Omega k := by theta_order

example (a : ThetaWNoteD) : a ≤ ThetaWNoteD.nadd a (ThetaWNoteD.Omega 0) := by theta_order

/-! ### `theta_norm` — closed-term evaluation (from `ThetaW/{Arith,Dom}.lean`) -/

example : ThetaWNoteD.ofNat 3 + ThetaWNoteD.one = ThetaWNoteD.ofNat 4 := by theta_norm

example : ThetaWNoteD.succ ThetaWNoteD.zero = ThetaWNoteD.one := by theta_norm

example : ThetaWNoteD.omegaPow ThetaWNoteD.zero = ThetaWNoteD.one := by theta_norm

example : ThetaWNoteD.ofNat 0 = ThetaWNoteD.zero := by theta_norm

-- `ThetaW/Dom.lean`'s `cTerm`, unfolded at `n = 0`.
example : cTerm 0 = theta 0 (theta 0 zero) := by theta_norm

example (k : ℕ) : ThetaWNoteD.omegaMul (ThetaWNoteD.Omega k) = ThetaWNoteD.Omega k := by theta_norm

example : ThetaWNoteD.ofNat 1 = ThetaWNoteD.one := by theta_norm

end OrdinalAnalysis
