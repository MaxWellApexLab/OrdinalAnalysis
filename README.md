# OrdinalAnalysis

Proof-theoretic ordinal analysis in Lean 4, built on
[mathlib](https://github.com/leanprover-community/mathlib4) and
[FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation).

Everything below is `sorry`-free and every headline theorem's `#print axioms`
returns exactly `[propext, Classical.choice, Quot.sound]`.

---

## What is here

### Ordinal notations

| | |
|---|---|
| `Ordinal/NaturalSum.lean` | the natural (Hessenberg) sum on `ONote`, closure under normal form, commutativity |
| `Ordinal/NaturalSumMono.lean` | strict monotonicity in each argument; `cmp_swap`; `lt_oadd_cases` |
| `Ordinal/NONatSum.lean` | the natural sum on `NONote`, and the room lemma |
| `Ordinal/OmegaPow.lean` | `ω ^ a`, additive indecomposability for the natural sum, the `ω`-tower |
| `Ordinal/Notation.lean` | `class OrdinalNotation O`: the order arithmetic the infinitary calculus consumes — natural sum, `ω ^ ·` with additive indecomposability, `1`, the finite notations — as a mixin over an existing `LinearOrder`/`WellFoundedLT`, with `sq`, `mid`, `redOrd`, the `ω`-tower and the successor *defined* from them.  `NONote` is an instance, every field the lemma already proved above |

Three of these fill gaps in mathlib rather than restating it.

- **The natural sum does not exist in mathlib.** `Mathlib/SetTheory/Ordinal/NaturalOps.lean`
  is absent from this revision and `Ordinal.nadd` appears nowhere in the tree.
  Mizar has `a (+) b` and Metamath has `+no`; Lean has neither.
- **`cmp_swap`** — syntactic antisymmetry of `ONote.cmp` — is not in mathlib.
- **`lt_oadd_cases`** is an *elimination* rule for `<` on normal forms.  mathlib
  supplies the three introduction rules `oadd_lt_oadd_1/2/3` and nothing that
  lets you conclude anything *from* `oadd e n a < oadd e' n' a'`.

| `Ordinal/Veblen/Basic.lean`, `Cmp.lean`, `Gamma0Note.lean` | **Veblen normal-form notations below `Γ₀`**: `vadd a b n c` denotes `φ_a(b)·n + c`; normal form; a comparison that agrees with the comparison of the ordinals denoted (`cmp_eq_cmp_repr`); injectivity of the reading on normal forms; `Gamma0Note`, the normal forms as a linear order embedding into the ordinals, hence well founded; total `veblenNote` and `omegaPow` with the fixed-point case decided syntactically.  Veblen normal forms below `Γ₀` have been formalized before — in Coq by Castéran and Contejean (hydra-battles, `theories/ordinals/Gamma0`: comparison and well-foundedness, no ordinal semantics) and by Dockins (`robdockins/ordinals`: constructive denotations), and in Lean as a work in progress by Hernández (`vihdzp/ordinal-notation`, `Notations/Veblen.lean`); what is new here, as far as the surveys reach, is the order isomorphism of the normal forms onto `Γ₀` inside mathlib's `Ordinal` |
| `Ordinal/Veblen/NaturalSum.lean`, `NaturalSumAssoc.lean`, `Epsilon.lean`, `Instance.lean`, `OfNONote.lean`, `EpsilonBelow.lean` | the natural sum on the Veblen notations (commutative, associative, monotone, below every `ω^a`), the ε-numbers `epsilonNote a = φ_1(a)` and closure of each `ε_a` under `⊕`, `ω^·` and the numerals, the `OrdinalNotation` instance, the embedding of the `ε₀` notations, and the notation systems `Below (epsilonNote a)` |
| `Ordinal/Notation.lean`, `Ordinal/Below.lean` | `class OrdinalNotation`: the operations and laws a height system must have (`⊕`, `ω^·`, `1`, the numerals; **not** `a < ω^a`, which fails at ε-numbers), so that every theorem of the infinitary calculus is stated once for all systems; `Below ε`, the notations below a closed bound, as a system |
| `Gentzen/InternalVNote.lean`, `VNoteBridge.lean`, `CodedVeblen.lean` | the Veblen notations arithmetized inside PA: internal codes, the comparison `icmp₁`, the normal-form recogniser `isNF₁` as a course-of-values table, their `Σ₁` definitions, the bridge to the external notations (agreement on standard codes, surjectivity of the coding onto the internal normal forms), and `gamma0Order : CodedOrder Gamma0Note`, the coded `Γ₀`-ordering |
| `Gentzen/CodedOrder.lean` | `structure CodedOrder O`: a formula `≺` of `LX`, its reading in `ℕ`, and a coding of `O` under which `≺` is `<` — the interface the lower bound is generic over; `epsilon0Order` |
| `Gentzen/Climb.lean`, `ClimbEpsilon0.lean` | **the climb**: `¬Prog(X), X(n̄)` is derivable at height about `ω^(o+1)` for the code of `o`, generically in the coded ordering, given the false instances of `≺` at one height and the domain property; the `ε₀` instance |
| `Omega/HeightMap.lean` | a strictly monotone map of heights transports derivations |

### The finitary calculus

| | |
|---|---|
| `Proof/Bounded.lean` | `BoundedDerivable r α Γ`: an ordinal-indexed Tait-style one-sided calculus whose cut rule carries a rank side condition |
| `Proof/Weakening.lean`, `Proof/Substitution.lean` | structural rules, rewriting, context shift |
| `Proof/Inversion.lean`, `Proof/InversionAll.lean` | inversion for `⋎` and `⋏` |
| `Proof/Reduction.lean` | the reduction lemma, all four principal cases |
| `Proof/Elimination.lean` | rank `r + 1` at height `α` becomes rank `r` at height `ω ^ α` |
| `Proof/CutElimination.lean` | cut elimination with an explicit bound: rank `r` at `α` becomes cut free at the `r`-fold `ω`-tower over `α` |
| `Proof/Bridge.lean` | both directions between this and Foundation's concrete `Derivation` |

### The infinitary calculus

| | |
|---|---|
| `Omega/Calculus.lean` | `OmegaDerivable A I r α Γ`, over any `[OrdinalNotation O]` as the type of heights: the ω-rule replaces the universal rule, the existential rule takes a numeral, `A : Literals L` supplies a consistent set of closed literals as axioms — the true atoms arithmetic needs — and `I : Instantiation L` says how a quantifier is instantiated: substitute the numeral, then *normalise*.  Plain substitution is the instance `Instantiation.raw`; the evaluator of closed terms is the other.  Without the normaliser the calculus is not Buchholz's `Z∞` and no embedding of `PA[X]` exists (see the header of `Omega/Calculus.lean`) |
| `Omega/Reduction.lean` | reduction, elimination, and cut elimination for it |
| `Omega/Identity.lean` | `φ, ∼φ` for every formula, at height `2·complexity` |
| `Omega/Transfer.lean` | transport of derivations along a map of formulas that respects the rules |

---

## What is *not* new, and must not be claimed

**Cut elimination with an ordinal bound already exists in Lean 4.**
`FormalizedFormalLogic/goodstein-independence` has it twice — over `Ordinal`
in `GoodsteinPA/Zinfty/Cut.lean` and over `ONote` in `GoodsteinPA/Zef2TC/` —
along with an ω-rule calculus, inversion lemmas and a substitution lemma.
Its headline is Kirby–Paris via the Wainer hierarchy.

**Consistency of PA has been formalized twice.**  In Coq: Bryce & Goré,
[arXiv:2603.00487](https://arxiv.org/abs/2603.00487) (2026), completing
Sinclaire's 2019 thesis — 18,074 lines, Gentzen's 1936 argument with ordinal
assignments.  In Lean: goodstein-independence's
`GoodsteinPA/Result/ConsistencyPA.lean`, `consistency_PA : 𝗣𝗔 ⊬ ⊥`, in the
build and `sorry`-free, through its `Z∞` cut elimination.

So neither "first cut elimination with an ordinal bound in Lean" nor "first
machine-checked Gentzen consistency proof" — in any system, or in Lean — is
available as a claim.

---

## What *is* different

**The classical Gentzen bound.**  goodstein-independence records, at
`GoodsteinPA/Zinfty/Cut.lean:49`:

> Natural (Hessenberg) sum `α ⊕ β` is unavailable, so the classic
> reduction-lemma bound `α ⊕ β` cannot be used.

They route around it through invertibility of `∧`/`∨` and an induction on the
existential side.  This development builds the natural sum and takes the
classical route, which as far as the surveys below reach makes it the first
Lean cut elimination that uses Gentzen's own bound.

Two consequences of that choice are recorded in the source and are not
cosmetic.

*There is no inversion lemma in the reduction proof, and there cannot be one.*
The natural plan — induct on the left derivation, invert the right one to expose
the subformulas of `∼φ` — breaks at the universal quantifier, where it would
need an inversion for `∃`.  No such lemma exists: the witness a derivation chose
is not recoverable from its conclusion.  Both quantifier cases instead take the
witness from whichever premise has one.

*The recursion runs on the symmetric measure `β ⊕ γ`*, because the quantifier
cases produce their second cut premise by running the reduction with the two
sides swapped, which a measure counting only the left ordinal cannot see as a
decrease.

**The bound is below `ε₀` by typing, not by proof.**  `NONote` is the type of
notations in Cantor normal form — the ordinals below `ε₀` — and the tower is
built inside it, so "the bound is below `ε₀`" is discharged by the type of the
bound rather than by a lemma.

---

## Gentzen 1943: the upper bound of `|PA| = ε₀`

`OrdinalAnalysis/Gentzen/` proves the half of the ordinal analysis that, as far
as surveys of Lean, Coq/Rocq, Isabelle/AFP, Agda, HOL Light, HOL4, Mizar,
Metamath, ACL2 and Nuprl could find, no proof assistant had:

> **`gentzen_upper_bound`.**  For every formula `φ` of `LX` and every
> ordinal notation `a` in Cantor normal form, `PA[X] ⊢ TI(≺, φ, ⌜a⌝)` —
> transfinite induction along the `ε₀` ordering below the code of `a`.

Here `LX` is arithmetic with a fresh unary predicate, `PA[X]` has induction for
every formula of `LX`, and `≺` is the Σ₁-definable comparison of Cantor
normal form codes, tied to mathlib's `ONote` order on standard codes in every
model of `IΣ₁` (`NotationBridge.lt_iff_icmp_modelCode_eq_zero`).  The
quantifier over `a` is Lean's: one derivation per notation, which is exactly
what the lower bound says must be so.

The proof is Gentzen's: an internal notation system on the primitive-recursive
machinery of Foundation (`InternalONote.lean`), the jump `J` in relational-graph
form, Lemma A (`Prog(φ) → Prog(Jφ)`) and Lemma B
(`TI(Jφ, a) → TI(φ, ω^a)`), the finite towers, and cofinality of the towers in
the notations.

**Verification.**  Full build,
the axiom gate (`scripts/AxiomCheck.lean`, guarded `#print axioms`
including `gentzen_upper_bound`, every one `[propext, Classical.choice,
Quot.sound]`), a scan for `unsafe`/`partial`/`opaque`/`implemented_by`/
`native_decide`, and a reading of every definition the headline theorem
quantifies over.  Lean checks proofs; the reading is what checks that `≺` is
the `ε₀` ordering and `TI` is transfinite induction.  Residual caveat: the
public Zulip archive used for the prior-art survey ends 2026-02-28, so any
announcement between March and August 2026 was not visible to it.

## Gentzen 1943: the lower bound, and `|PA| = ε₀`

`OrdinalAnalysis/Gentzen/LowerBound.lean` proves the other half:

```
gentzen_lower_bound : paLX ⊬ (TI precCode).univCl
```

and `Gentzen/GentzenTheorem.lean` puts the two together:

```
gentzen_theorem :
  (∀ φ a ha, paLX ⊢ closedTI φ (notationTerm ⟨a, ha⟩)) ∧ paLX ⊬ (TI precCode).univCl
```

`paLX` proves transfinite induction along `≺` below every notation and does
not prove it along all of `≺`; `ε₀` is exactly the proof-theoretic ordinal of
Peano arithmetic.

The argument is Gentzen's, made exact by Buchholz, and every step is a
theorem in the tree:

1. a proof of `TI(≺)` from `paLX` is an LK derivation of `TI(≺)` together
   with the negations of finitely many axioms (Foundation's `provable_iff`);
2. `Embed.replay` turns any LK derivation into a derivation in the infinitary
   calculus under the *evaluating* instantiation, at the same cut rank and
   height, of every numeral instance of its sequent — the universal rule's
   fresh variable becomes the ω-rule, the existential rule's arbitrary witness
   becomes, after assignment, a ground term that the evaluator replaces by the
   numeral of its value (`Gentzen/Evaluate.lean`, `NumSubst.lean`, `EvInst.lean`);
3. every axiom of `paLX` has a cut-free derivation in that calculus: the
   equality and `PA⁻` axioms by ω-completeness of true `X`-free sentences
   (`OmegaTruth.lean`, `AxiomsLogic.lean`), the induction instances by a
   cut-free chain along the numerals at height `ω + 2` (`AxiomsInduction.lean`);
   the negated axioms are cut away;
4. `OmegaDerivable.cutElimination` removes the cuts, the height staying a
   notation below `ε₀`;
5. the boundedness lemma (`Boundedness.lean`) says no cut-free derivation of
   `TI(≺)` exists at any height: every member of the derivation is read with a
   lower and an upper bound on the ordinal its `X`-atoms code, the negated
   progressiveness axiom is given *no* reading at all, and the one case with
   content — the existential rule on that axiom — is settled by invoking the
   hypothesis a second time above the counterexample, which costs one more
   `ω^α` and is paid for by additive indecomposability.

Two design points carry the whole thing.  *The calculus instantiates by substitution followed by
evaluation of closed terms*: with plain substitution `X(n̄ + 1)` and `X(n+1‾)`
are unrelated atoms, the calculus has no equality reasoning about `X`, and no
embedding can exist — the naive substitution law `ev (φ/[t]) = (ev φ)/[n̄]` is
false for every evaluator, and the law that holds is the normalised one.
*The boundedness invariant is not a model*: `TI(≺)` is true in `ℕ` for every
reading of `X`, so soundness cannot refute it; only the height can.

**Prior art, surveyed 2026-09-07 and re-run before release** — mathlib master, Foundation, GitHub across
Lean/Coq/Isabelle/Agda/Metamath/Mizar/HOL, arXiv, and the Lean Zulip through
the archive repository's data (current to 2026-08-25; September unverifiable).
Gentzen's upper bound was found in no proof assistant.  The lower bound exists
in one place: goodstein-independence's `wip/Thm56.lean`,
`peano_not_proves_TI`, with the same architecture — embed, cut-eliminate,
boundedness.  It is outside that repository's build target, its imports do not
resolve, and `wip/EmbeddingX.lean` carries two `sorry`s and an `axiom` for the
value-congruent `X`-pair `{X s, ¬X t}` — precisely the gap the normalising
instantiation closes here; its README states that whether the formalization
succeeds is an open question.  Goodstein independence itself that repository
proves by the fast-growing-hierarchy route, not by ordinal analysis; that
proof, `peano_not_proves_goodstein`, is in its build and `sorry`-free, so an
unprovability result at the level of `ε₀` in Lean is not new — the ordinal
analysis is: both bounds of `|PA| = ε₀`, in the transfinite-induction form.  On
Zulip the last word is the February 2026 thread *Proof theory and Gentzen's
consistency proof in assistants*, opened with "I don't think Gentzen's
consistency proof of Peano Arithmetic has ever been formalized in an
assistant", corrected in March with the Coq proof, and closed by the suggestion to formalize instead
the `Π¹₁`-ordinal of `PA(X)` — which is what this development does.  As far as
that survey reaches, this is the first complete, machine-checked proof of
`|PA| = ε₀`, both bounds, in any proof assistant.

**Verification.**  Full build, the axiom gate (guarded `#print axioms`,
ending in `gentzen_theorem`), the forbidden-construct scan, and a reading of
every definition the headline theorem quantifies over.

## Above `ε₀`: `|PA + TI(ε₀)| = ε₁`, and the calculus for ACA

`OrdinalAnalysis/Gentzen/Epsilon1Theorem.lean`:

```
epsilon1_theorem :
  (∀ φ a, a < epsilonNote 1 → paLX₁ ⊢ closedTI₁ φ (gamma0Term a))
  ∧ paLX₁ ⊬ (TI epsilon1Order.prec).univCl
```

`paLX₁` is `PA[X]` together with the scheme of transfinite induction along the
coded Veblen ordering `≺₁` below the code of `ε₀`, for every unary formula of
`LX` (the scheme is necessary: with the single `X`-instance the upper bound is
false).  The upper bound proves transfinite induction for every formula below
every notation `< ε₁`; the lower bound is transfinite induction along the
`ε₁`-segment of `≺₁` for the free predicate `X`.  This is Schütte's theorem
(Avigad 2002, Thm 9.8), and as far as the surveys reach the first machine-checked
ordinal analysis above `ε₀`.

The upper bound is Gentzen's jump over the Veblen codes arithmetized inside
`PA` (`InternalVNote*.lean`, `CodedVeblenJump.lean`, `Epsilon1UpperBound.lean`;
towers `ω^…^(ε₀+1)` are cofinal in `ε₁`).  The lower bound runs the `ε₀` chain
one level up, in the notations below `ε₁` (`Below.lean`, `BelowDerivation.lean`,
`CutAxioms.lean`): the axiom `TI(ε₀)` is derived in the infinitary calculus at
height `ε₀ + 1` by the climb along the `Γ₀`-ordering (`Climb.lean`,
`ClimbVeblen.lean`), every other instance of the scheme by substituting the
formula for `X` in that one derivation (`SubstX.lean`, `Epsilon1Scheme.lean`),
and the boundedness lemma at the `ε₁`-segment closes it.

`OrdinalAnalysis/ACAOmega/` is the infinitary calculus for `ACA` (Afshari–Rathjen
2012): set quantifiers by an eigenvariable rule and substitution of an arithmetical
formula, ordinal cut ranks with set quantifiers at `ω`, and both cut-elimination
theorems — the first brings rank `ω + k` down to `ω` by a `k`-fold `ω`-tower, the
second (`secondCutElimination : ⊢^α_ω Γ → ⊢^{ε_α}_0 Γ`) removes the remaining
cuts at the cost `α ↦ ε_α`, which is the whole mechanism of `|ACA| = ε_{ε₀}`.

## Schütte: `|ACA| = ε_{ε₀}`

`OrdinalAnalysis/ACA/UpperBound.lean`:

```
aca_theorem :
  (∀ a : SegNote, Provable ACA (tiUptoSegSO a.val)) ∧ ¬ Provable ACA TIsegSO
```

`ACA` is arithmetical comprehension with the induction scheme for *every*
second-order formula, presented as a one-sided second-order sequent calculus
(`ACA/LK.lean`) that is sound for the full ω-model (`ACA/Standard.lean`).
`SegNote` is the set of Veblen notations below `ε_{ε₀}`; `tiUptoSegSO a` is
transfinite induction along the coded ordering below `ā`, for a free set
variable; `TIsegSO` is the same statement for the whole segment.  So `ACA`
proves transfinite induction along every proper initial segment of the
ordering below `ε_{ε₀}` and does not prove it along the whole of it — the
theorem is Schütte's, and the infinitary side follows Afshari–Rathjen
(CiE 2012).

The lower bound replays a proof in `ACA` into `ACA_∞` (`ACAOmega/Embed₂.lean`),
cuts the axioms away (`Axioms₂.lean`, `SchemeAxioms₂.lean`), brings the
derivation to cut rank `0` with the two cut-elimination theorems at a height
below `ε_{ε₀}`, and refutes it with the boundedness lemma of the second-order
calculus (`Boundedness₂.lean`, `LowerBound₂.lean`).  The upper bound lifts
Gentzen's `ε₀` argument from `PA[X]` into `ACA` at an arbitrary set parameter
(`ACA/Lift.lean`, `Congruence.lean`, `LiftInduction.lean`), runs the internal
ω-tower induction — the single use of the full second-order induction scheme,
which is where `ACA` outruns `ACA₀` (`ACA/TowerInduction.lean`) — and shows
that `∀u (Eps(u,g) → ∀X TI(≺₁, u, X))` is progressive along the Veblen ordering
(`ACA/EpsProg.lean`), which carries transfinite induction below every `ε_c`
with `c < ε₀`.

## Towards `Γ₀`

Two things sit above `ε_{ε₀}`.  Neither is Feferman–Schütte's `|ATR₀| = Γ₀`,
and nothing here should be read as that.

* `ACAOmega/Gamma0Theorem.lean`, `gamma0_theorem`: the theory `ACA + TI(<Γ₀)` —
  `ACA` with transfinite induction along every proper initial segment of the
  coded Veblen ordering below `Γ₀`, as a scheme — proves transfinite induction
  along every proper segment (by its axioms) and does not prove it along the
  whole ordering.  This is the sense in which the theories of Avigad's
  *Ordinal analysis without proofs* reach `Γ₀`; the content is the
  non-provability half, obtained by the same replay, cut elimination and
  boundedness as for `ACA`, with the segment orderings of `Gamma0Order₂.lean`.

* `OrdinalAnalysis/Ramified/`: ramified analysis in a "names" presentation.  A
  set of level `μ` is a numeral coding a predicator with one set parameter of
  the same level (`Code.lean`: the level, a stage, the formula and the
  parameter; the stage guard is what keeps the naming schema consistent), the
  set atoms `t ∈̇_μ s` are relation symbols, and every level is first-order
  (`Language.lean`).  The finitary theories `RA_{<ν}` (`Theory.lean`) have the
  equality axioms, `PA⁻`, induction for formulas of level below `ν`, and one
  pair of naming axioms per formula; comprehension with a same-level parameter,
  in particular the closure of every level under Gentzen's jump, is a theorem
  (`Comprehension.lean`).  The infinitary calculus `RA_∞` has two predicator
  rules and ordinal cut ranks in blocks `ω·μ` (`Calculus.lean`, `Rank.lean`);
  its reduction lemma and cut-elimination theorems are `Reduction.lean`,
  `PredicativeCut.lean` and `BlockCut.lean`, and predicative cut elimination
  holds at every Veblen level, `⊢^α_{ω^ξ} Γ ⇒ ⊢^{φ_ξ(α)}_0 Γ`
  (`PredicativeCutGeneral.lean`, over `Ordinal/VeblenStructure.lean` and the
  rank segments of the natural sum in `Ordinal/Veblen/RankSegments.lean`).
  The replay of `RA_{<ν}` into `RA_∞` (`Embed.lean`), the derivability and
  removal of its axioms (`NamingAxioms.lean`, `AxiomsLogic.lean`,
  `AxiomsInduction.lean`, `CutAxioms.lean`), and the boundedness lemma over the
  ramified language (`Boundedness.lean`) give the non-provability half
  (`LowerBound.lean`, `ramified_lower_bound`): `RA_{<ν+1}` does not prove
  transfinite induction along the coded Veblen ordering restricted below the
  ε-tower `φ_1^ν(ε₀)`.  The provability half is in progress.

## Building

```
lake exe cache get
lake build
```

`lake exe cache get` fetches mathlib's prebuilt oleans and saves hours.
Foundation has no cache and is compiled locally.
