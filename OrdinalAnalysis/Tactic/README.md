# `OrdinalAnalysis/Tactic`

Automation for the routine side goals of the multi-level ϑ-notation (`ThetaWTerm`, `NF`, `Dom`,
`ThetaWNoteD`, the level-`k` coefficient sets `E k`/`G k`, the order, and levels). The intent is
that a proof over this notation can be written as a sequence of `have` steps stating the
mathematical content, with the mechanical side conditions — is this term in normal form, is it
in the domain of `theta`, does this order fact hold, does this closed numeral expression reduce
— discharged by one of the four tactics below in a single line each.

Every module here is self-contained (`Dom.lean`, `Order.lean`, `Notation.lean`), documented at
the top with a usage example, and builds independently
(`lake build OrdinalAnalysis.Tactic.<Module>`). `RuleSets.lean` holds the `aesop` rule sets and
named `simp` sets the other modules attach to — `aesop` rule sets and named `simp` sets are only
visible to files that *import* the module that declares them, so they cannot be declared and
used in the same file, and had to live on their own.

## `dom_tac`

Closes goals of the form `Dom t`, `NF t`, and `NF t ∧ Dom t`, for terms built from `Omega k`,
`theta k _`, `sum _` (so also `zero`, `cTerm n`, …) and the `ThetaWNoteD` operations (`nadd`,
`add`, `omegaPow`, `omegaMul`, `succ`, `one`, `ofNat`). It also closes goals that *extract* an
`NF`/`Dom` fact from a hypothesis or from a `ThetaWNoteD`/`ThetaWNote` element already in
context — the `.2.1`/`.2.2` subtype-projection idiom used throughout `Ordinal/ThetaW/Arith.lean`.

```
example : Dom (cTerm 3) := by dom_tac
example (a : ThetaWNoteD) : NF a.1 := by dom_tac
example (k : ℕ) (a : ThetaWTerm) (h : Dom (theta k a)) : Dom a := by dom_tac
```

It tries a fast `decide` first (closed terms), then an `aesop` rule set built from the
`dom_*`/`nf_*` lemmas of `Dom.lean`/`Arith.lean`/`Instance.lean`/`Veblen.lean` together with the
order facts those side conditions bottom out in, with `omega` available as a closing step for
the numeral arithmetic that shows up under `E k`/`G k`. It does not attempt substantive,
one-off arguments that happen to conclude a `Dom`/`NF` fact (for instance, `ThetaW/Dom.lean`'s
`not_dom_tower`, whose proof is a genuine position-comparison argument, not a schema) — those
stay hand-proved lemmas, used by name.

## `theta_order` and `level_tac`

`theta_order` closes routine order goals: principal-against-principal comparisons (`Omega i <
Omega j`, `Omega i < theta j b`, `theta i a < theta j b` for `i < j`, and the `E k`-clause at
one level), principal-against-sum and sum-against-sum comparisons, and the monotonicity and
additive-indecomposability facts of `ThetaWNoteD`'s arithmetic (`nadd`, `+`, `omegaPow`,
`omegaMul`, `succ`, `ofNat`, and the "below a principal term" family).

```
example : theta 1 (Omega 5) < Omega 1 := by theta_order
example (a b : ThetaWNoteD) (h : a < b) : omegaPow a < omegaPow b := by theta_order
```

`level_tac` is the narrower tactic for `LevLT n t` goals (every level occurring in `t` is below
`n`): it unfolds `LevLT` down to `Nat` inequalities and finishes with `omega`.

```
example : LevLT 3 (theta 1 (Omega 2)) := by level_tac
example : ¬ LevLT 2 (theta 1 (Omega 5)) := by level_tac
```

Both try `decide` first, then a named `simp` set of the relevant `_iff`/unfolding lemmas
together with `omega`, then (`theta_order` only) an `aesop` rule set of the monotonicity lemmas
for goals the simp set alone does not reduce to arithmetic.

## `theta_norm`

Normalizes an equation (or decidable proposition) between *closed* ϑ-notation expressions — no
free variables — built from the numerals and the `ThetaWNoteD` operations.

```
example : ofNat 3 + one = ofNat 4 := by theta_norm
example : omegaPow zero = one := by theta_norm
```

It tries `rfl`, then `decide`, then a named `simp` set of the arithmetic identities that express
each operation in terms of the numerals (`ofNat_succ`, `add_one_eq_succ`, `nadd_zero`,
`omegaMul_Omega`, …), each required to close the goal outright. If none succeeds, it reports
why: a goal with a free variable is not what `theta_norm` is for (use `theta_order`/`dom_tac`/
`level_tac` instead), while a genuinely closed goal that still fails almost always needs the
*general* clause of the order comparison `ltb`/`cmp`, which — being compiled from a
well-founded recursion — does not reduce in the kernel at all, not even on its flat, immediate
cases; `decide` and `rfl` only get through a closed expression whose value never calls `<`/`≤`
in the first place (plain structural unfolding, or one operation *defined* as another, such as
`one := omegaPow zero`). Once an operation has to compare or sort its exponents, only the
lemma-driven route through the named `simp` set gets there.

## `sanity_check` and `#sanity_report`

`sanity_check "name" : prop := proof` records a small, self-contained fact — usually a
slot/shape check on the notation ("this nesting of `theta`/`Omega` is/isn't in the domain", "this
order fact on small terms holds") — as its own theorem, named
`OrdinalAnalysis.Sanity.check_name` (the string is turned into an identifier by replacing every
non-alphanumeric character with `_`). This is a plain naming convention: every one of these
theorems can be found with
`grep -n 'theorem OrdinalAnalysis.Sanity.check_' OrdinalAnalysis/Tactic/Sanity.lean`, and
`lake build OrdinalAnalysis.Tactic.Sanity` re-proves all of them at once — a check that stops
type-checking, or whose proof stops going through, fails the build exactly like any other
theorem. The `#sanity_report` command lists every one currently registered, sorted by name.

```
sanity_check "cTerm3_dom" : Dom (cTerm 3) := by dom_tac
#sanity_report
```

`Sanity.lean` has 15 such checks for the multi-level ϑ-notation: domain slot checks (which
nestings of `theta 0`/`theta 1`/`Omega` are and are not in the domain), order facts on small
terms, `LevLT` facts, and a few closed-term arithmetic identities.

## The acceptance test, `Test.lean`

`Test.lean` has 48 one-line examples, each restating a real lemma statement (or the shape of a
side goal that recurs, hand-proved, throughout `Ordinal/ThetaW/*.lean`) from `Basic.lean`,
`Order.lean`, `Dom.lean`, `Arith.lean`, `Instance.lean`, and `Veblen.lean`, closed by exactly one
of the four tactics above. It is the file to build to check that nothing here has rotted:
`lake build OrdinalAnalysis.Tactic.Test`.

## What needed a fallback, and what did not

Every tactic above tries a fast, syntactic step first (`decide` for `dom_tac`/`theta_order`/
`level_tac`/`theta_norm`, `rfl` as well for `theta_norm`) before falling back to the
lemma-driven `aesop`/`simp` search, because `decide` and `rfl` are instant when they apply at
all. In practice `decide` only reaches goals whose evaluation never needs to compare two terms
with `<`/`≤` — the order function is compiled from a well-founded recursion and does not reduce
in the kernel, a fact confirmed directly (`by decide` on `¬ Dom (theta 0 (theta 1 (Omega 2)))`
fails with "did not reduce to `isTrue` or `isFalse`", stuck inside a call to the order
function). Every goal that needs an actual order comparison — which is most `Dom`/`NF`
obligations beyond the very smallest, and any arithmetic identity whose operands are not
already syntactically equal — falls through to the `aesop` rule sets and named `simp` sets,
which reason from the proved `_iff` characterizations instead of by kernel reduction, and that
is where essentially all of the real work in `Test.lean` and `Sanity.lean` is actually done.

`grind` was tried directly (not wired into the tactics above) on a handful of the same goals: it
closes the ones `decide` closes, plus a few more given the right lemma hints by hand, at
comparable speed, but it has no equivalent of `aesop`'s layered `norm simp`/`safe apply`/`safe
forward` rule construction, and got stuck on a goal that needed instantiating a
list-membership universal at a specific witness before an order fact about it could be seen to
be false — `aesop`'s `norm simp` phase reduces that kind of universal to a pointwise fact
before search even starts, sidestepping the instantiation problem. So `grind` is not part of the
search any of the tactics above perform, though nothing stops a user from reaching for it
directly on a specific goal.

No individual call to any of the four tactics took a noticeable fraction of a second in testing
(well under the 2-second budget); building each module (which imports a large share of
`Ordinal/ThetaW/*.lean`) takes on the order of 20–30 seconds, dominated by elaborating that
import chain, not by the tactic search itself.

## Limitations

* `dom_tac` does not attempt substantive, one-off domain arguments (`not_dom_tower`'s
  position-comparison proof is the example above) — only the schema of unfolding `Dom`/`NF`
  through the term structure and closing the resulting order/list-membership facts.
* `theta_order`'s `E k`-clause handling (`theta_lt_theta_iff`) is in the named `simp` set but is
  the most expensive rewrite available to it; a goal that genuinely needs several levels of
  `E k`-unfolding may need to be broken into smaller steps by hand.
* `theta_norm` only ever attempts to fully close a goal — it never leaves a partially simplified
  goal behind, by design (see the note in `Notation.lean` on why `first`'s usual semantics would
  otherwise silently accept an incomplete `simp` as success).
