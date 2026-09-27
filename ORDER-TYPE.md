# ORDER-TYPE: pin `≺` has order type exactly ε₀

Treadmill brief for branch `order-type-epsilon0` of `gotrevor/OrdinalAnalysis` (fork of KT. Wu's
`MaxWellApexLab/OrdinalAnalysis`, cut at `87baec7`).  This is a small gift PR to Wu.  **Drop this
file before opening the PR.**

## Why

`gentzen_theorem` (`OrdinalAnalysis/Gentzen/GentzenTheorem.lean:32`) is stated about the coded
ordering `≺` (`CodedNotation.precCode`), and its docstring concludes `|PA| = ε₀`.  Nothing in the
repo states that `≺` has order type ε₀; that reading rests on `precN_code_iff` plus mathlib's
`NONote`.  This file makes the ε₀ a Lean statement.

## Objective (frozen statements)

New file `OrdinalAnalysis/Gentzen/OrderType.lean`, namespace `OrdinalAnalysis.Gentzen.OrderType`,
imported from `OrdinalAnalysis.lean`.  Declarations, names frozen:

```lean
/-- The field of `≺` on `ℕ`: the codes the internal recogniser accepts. -/
abbrev Field : Type := {n : ℕ // InternalONote.isNF (V := ℕ) n}

/-- `≺` restricted to its field. -/
def precF (m n : Field) : Prop := PrecStandard.precN m.1 n.1

/-- `nonoteCode` is an order isomorphism from `NONote` onto the field. -/
def codeIso : NONote ≃o ... -- any order-iso form between (NONote, <) and (Field, precF);
                            -- a `RelIso (· < ·) precF` is equally fine

instance precF_isWellOrder : IsWellOrder Field precF

/-- **`≺` has order type exactly ε₀.** -/
theorem precF_type_eq_epsilon0 : Ordinal.type precF = ε₀   -- `open scoped Ordinal`
```

`precF_type_eq_epsilon0` is the headline; its statement is RATIFIED as written (only the
`codeIso` target type is yours to choose).  Optional corollary, if cheap:

```lean
theorem gentzen_theorem_with_order_type :
    Ordinal.type precF = ε₀ ∧ <the exact statement of gentzen_theorem>
```

## Route

1. `CodeSurj.isNF_iff_exists_nonote` (`CodeSurj.lean:123`) gives surjectivity of `nonoteCode`
   onto `Field`; injectivity from `NotationBridge` (look for it, else prove from `code`'s
   `Nat.pair` layout).
2. `PrecStandard.precN_code_iff` (`PrecStandard.lean:43`) makes it order-preserving: `codeIso`.
3. Transfer the well-order along `codeIso`; `Ordinal.type precF = Ordinal.type (NONote <)`.
4. `type (NONote, <) = ε₀`: `NONote.repr` is strictly monotone (mathlib) with range `Iio ε₀`.
   The range fact is **not in mathlib**; re-prove it here.  Source to adapt (Trevor's own repo,
   Apache 2.0, credit in the docstring): `gotrevor/goodstein-independence` branch `kreisel`,
   `GoodsteinPA/ToMathlib/Ordinal/Epsilon0.lean` (`exists_NF_repr_eq`, `range_NONote_repr`, ~200
   lines, depends on its `WellFoundedRank.lean`).  Copy only what is needed, in Wu's style (plain
   `import`, no `module`/`public`), then `Ordinal.type_Iio`-style lemma to finish.

## Rules

- Match the repo's conventions: `set_option autoImplicit false`, docstring headers like
  `GentzenTheorem.lean`, plain imports.  Don't touch `lake-manifest.json`, `lakefile.toml`, or
  any existing file except `OrdinalAnalysis.lean` (one import line) and `scripts/AxiomCheck.lean`
  (add a pin for `precF_type_eq_epsilon0` in the file's existing style).
- Build only the modules you touch: `lake build OrdinalAnalysis.Gentzen.OrderType`.
- Done when the headline is `sorry`-free and the AxiomCheck pin passes.  Log below, then stop.

## Log

### 2026-09-27 — done

`OrdinalAnalysis/Gentzen/OrderType.lean` (new, 200 lines, `sorry`-free), imported at the end of
`OrdinalAnalysis.lean`; two pins appended to `scripts/AxiomCheck.lean`.  `lake build` green
(full build, not just the touched module) and `lake env lean scripts/AxiomCheck.lean` silent.

Declarations, as frozen in the objective:

* `Field`, `precF`, `codeIso : @RelIso NONote Field (· < ·) precF`, `precF_isWellOrder`,
  `precF_type_eq_epsilon0 : Ordinal.type precF = ε₀`, and the corollary
  `gentzen_theorem_with_order_type`.

Route, as planned, with two simplifications worth recording.

1. **Injectivity of `nonoteCode` came for free.** No `Nat.pair`-layout argument and nothing from
   `NotationBridge` was needed: `precN_code_iff a b : precN (nonoteCode a) (nonoteCode b) ↔ a < b`
   already forces it.  If `nonoteCode a = nonoteCode b` then rewriting turns `precN_code_of_lt` on
   either strict side into `precN (nonoteCode a) (nonoteCode a)`, i.e. `a < a`; trichotomy on the
   linear order `NONote` then leaves only `a = b` (`toField_injective`).
2. **No `WellFoundedRank.lean` dependency.** The kreisel source computes the order type through a
   rank function (`rk`, `orderType`), needed there because the carrier was `ℕ` with a *pulled-back*
   order and only `ε₀ ≤ orderType` was wanted.  Here both bounds are wanted and `NONote.repr` is
   available directly, so `range_NONote_repr` upgrades to an honest order iso
   `reprIso : NONote ≃o Set.Iio ε₀` (`NONote`'s `≤` *is* `repr · ≤ repr ·` by definition, so
   `map_rel_iff'` is `Iff.rfl`), and mathlib's `type_lt_Iio` finishes:
   `typeLT NONote = ε₀` (`type_NONote_lt`).  Only the universe bookkeeping needs care —
   `Set.Iio ε₀ : Type 1`, so `RelIso.ordinal_lift_type_eq` lands at
   `lift.{1,0} (typeLT NONote) = lift.{0,1} (lift.{1,0} ε₀)`; one `simpa` collapses the double
   lift and `Ordinal.lift_inj` descends.
   So the copied block is just `log_omega0_lt_self`, `exists_NF_repr_eq`, `isSuccLimit_epsilon0`,
   `repr_lt_epsilon0`, `range_NONote_repr` (credited in the file header).

**One addition beyond the objective, for the audit surface:** `precF_iff_eval_precCode` shows that
`precF` on the field is literally `precAt CodedNotation.precCode (numLX m) (numLX n)` evaluated in
`stdLX P` — the exact spelling `gentzen_theorem`'s second conjunct is about — via
`PrecStandard.eval_precAt_numeral`.  Without it a reader has to trace `precN` → `precDef` →
`precCode = liftCode precDef` by hand to believe the ε₀ is about *Gentzen's* `≺`.
