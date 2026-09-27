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
