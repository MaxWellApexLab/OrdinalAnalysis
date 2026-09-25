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
  (`LowerBound.lean`, `ramified_lower_bound`), and the lifting of `PA[X]` into
  `RA_{<ν}` at a level parameter (`LiftR.lean`), the tower at a level
  (`TowerR.lean`), the ε-progressiveness (`EpsProgR.lean`) and the descent
  through the levels (`DescentR.lean`) give the provability half.  Together,
  `Ramified/UpperBound.lean`:

  ```
  ramified_theorem (ν) (hν : 1 ≤ ν) :
    (∀ a < φ_1^ν(ε₀), RAlt (ν + 1) ⊢ tiUptoSegR (φ_1^ν(ε₀)) a)
    ∧ RAlt (ν + 1) ⊬ univCl (TIR (precBelowR (φ_1^ν(ε₀))))
  ```

  For every `ν ≥ 1`, ramified analysis with the levels `1, …, ν` proves
  transfinite induction along every proper initial segment of the coded Veblen
  ordering below the ε-tower `φ_1^ν(ε₀)` (that is, `ε_{ε_{⋯ε₀}}` with `ν`
  epsilons) for the free predicate `X`, and does not prove it along the whole
  of that ordering.  This is the finite-level part of the Feferman–Schütte
  analysis of ramified analysis; with only finitely many levels the values are
  ε-towers, and the limit theory `RA_{<ω}` (all finite levels) sits at
  `φ_2(0)`, both halves (`Ramified/LimitTheorem.lean`, `ramified_theorem_univ`).
  A finitary ramified theory cannot go further: any proof mentions finitely
  many levels, which can be renumbered, so transfinite level indices add
  nothing to a finitary theory.  Feferman–Schütte's `Γ₀` therefore belongs to
  the semiformal calculus `RA_∞` itself, in Schütte's formulation, and its
  bound half is `Ramified/FSLower.lean`: no derivation of `RA_∞` with cut rank
  and height below `Γ₀` proves transfinite induction along the whole coded
  Veblen ordering (`fs_lower`).  The levels of the calculus are now the Veblen
  notations below `Γ₀` themselves (`Language.lean`, `Ordinal/Veblen/OmegaMul.lean`,
  `Ordinal/Veblen/Encodable.lean`), with membership atoms of a code that is not
  a predicator at its level made false by literal axioms (`junkLitsR`), and the
  first transfinite bounds are in `Ramified/TransfiniteLower.lean`: below level
  `ω^n` no derivation of cut rank below `ω^{n+1}` and height below `φ_{n+1}(0)`
  proves transfinite induction along the ordering restricted below `φ_{n+1}(0)`
  (`sf_lower_omegaPow`, and `SemiformalLower.lean` at every index `γ`).

## Feferman–Schütte: `Γ₀` for the semiformal ramified calculus

`OrdinalAnalysis/Ramified/FefermanSchutte.lean`:

```
inductive Aut : Gamma0Note → Prop
  | base {a} : a < ε₀ → Aut a
  | step {λ a} : (∀ b, b < λ → Aut b) → SF λ λ a → Aut a

feferman_schutte :
  (∀ a : Gamma0Note, Aut a) ∧
  ∀ ρ h : Gamma0Note, ¬ OmegaDerivableR junkLitsR evInstR ρ h [evR (TIR gamma0OrderR.prec)]
```

`SF λ H a` says that transfinite induction along the coded Veblen ordering
restricted below `a`, for the free predicate `X`, has a derivation in `RA_∞`
of cut rank below the block of the level `λ` and height below `H`.  A notation
is *autonomous* when it is reached from `ε₀` by stages each of which uses only
levels and heights below a notation all of whose predecessors were reached
before.  The theorem says that every Veblen notation below `Γ₀` is autonomous,
and that no derivation whose cut rank and height are notations below `Γ₀`
proves transfinite induction along the whole ordering.  This is the
Feferman–Schütte theorem in Schütte's semiformal formulation: the autonomous
closure of ramified analysis is exactly `Γ₀`.

The engine is the generalised descent (`DescentBeta.lean`): from transfinite
induction at level `L + 1` up to `c` for all sets of that level, transfinite
induction at level `L` up to `φ_{1+β}(c)`, where `L` ends in `ω^β`, at cut rank
`ω·(L+1) + ω` and height below `ε_1`, for every Veblen index `β`.  It is built
from the effective unfolding of a name (`EffLevel.lean`), the copy of a set to a
higher level (`CopyR.lean`), the infinitary tools (`InfTools.lean`), the Veblen
covers on the notations (`Ordinal/Veblen/VeblenCover.lean`) and the fundamental
sequences of the Veblen normal form (`Ordinal/Veblen/FundSeq.lean`).

At each principal level the analysis is exact (`SemiformalUpper.lean`,
`sf_theorem`): for every index `γ ≥ 1`, with cut ranks below the block of the
level `ω^γ`, transfinite induction along the ordering restricted below
`φ_{1+γ}(0)` is derivable up to every notation below `φ_{1+γ}(0)` at heights
below an explicit bound under `φ_{1+γ}(0)`, and is not derivable for the whole
segment at any height below `φ_{1+γ}(0)`.

Two things this is not: it is not `|ATR₀| = Γ₀`, and it is not a statement
about a finitary theory.  A finitary ramified theory sees finitely many levels
in any proof and stays at `φ_2(0)` (`LimitTheorem.lean`).

* `ACA/OmegaJump.lean` and the `OmegaJump*` files: the theory `ACA⁺` — `ACA`
  with the axiom that every set has an ω-jump — its truth in the full ω-model
  and hence its consistency (`OmegaJumpSound.lean`), and the provability half
  of its analysis: the ε-jump `epsJump_plus` (transfinite induction up to `b`
  for all sets gives it up to `ε_b`, by a tower induction over the columns of
  an ω-jump, without any second-order induction) iterated outside the theory
  gives `aca_plus_upper_bound`: `ACA⁺` proves transfinite induction along every
  proper segment below `φ_2(0)`.  The non-provability half for `ACA⁺` is not
  here.

## Bachmann–Howard: `|ID₁| = ϑ(ε_{Ω+1})`

`OrdinalAnalysis/ID1/Theorem2.lean`:

```
id1_theorem :
  (∀ a : ThetaNote, a < Ω → ID1Acc precC ⊢ tiUptoSentence a)
  ∧ ¬ ID1Acc precC ⊢ tiFieldSentence
```

`ID1Acc precC` is the theory of one inductive definition over `PA` with a free
predicate `X`: the closure axiom and the induction scheme for the accessibility
operator `A(Y, x) :≡ ∀y (y ≺ x → Y y)` of the ordering `≺ = precC`, and
`precC` is the ordering of the Rathjen–Weiermann `ϑ`-notation for the
Bachmann–Howard ordinal, coded in arithmetic.  `tiFieldSentence` is
`Prog(≺, X) → ∀x (x ≺ ⌜Ω⌝ → X x)`: transfinite induction for `X` along `≺`
below `Ω`, and `tiUptoSentence a` is the same with `⌜a⌝` in place of `⌜Ω⌝`
(`tiUptoSentence Ω = tiFieldSentence` by definition).  The theorem says that
`ID₁` proves transfinite induction along `≺` below every notation below `Ω`,
that is, below every ordinal below the Bachmann–Howard ordinal, and does not
prove it along the whole of the field.  As far as the surveys reach (proof
assistants, arXiv, the Lean Zulip), no ordinal analysis of an impredicative
theory had been machine-checked before.

The pieces, following Freund's notes on the ordinal analysis of `ID₁`
(arXiv:2204.09321): the `ϑ`-notation as a syntactic linear order
(`Ordinal/Theta/{Basic,Order}.lean`), its arithmetic
(`Arith.lean`, `Instance.lean`), its well-foundedness by the accessible-part
argument (`WellFounded.lean`; a machine-checked well-foundedness proof of
Buchholz's notation `OT_B` below `ψ₀(Ω_ω)`, in Lean 4 and Isabelle, exists in
koteitan's `pss-proof` (2026), so this is not the first such proof — what is
new here, as far as the surveys reach, is the ordinal analysis built on it),
the hull sets and operators
(`Hull.lean`, `HullCofinal.lean`); the theory `ID₁` and its consistency by the
least fixed point (`ID1/{Theory,Sound}.lean`); the coding of the notation in
arithmetic with the order facts inside `IΣ₁` (`ID1/Internal/`); the stage
language and rank (`Language.lean`, `Rank.lean`); the operator-controlled
infinitary calculus with the stage rules, the boundedness lemma and the
collapsing theorem (`Calculus.lean`, `Boundedness.lean`, `Collapsing.lean`);
cut reduction and elimination away from `Ω` (`Reduction.lean`,
`Elimination.lean`); the embedding of `ID₁` (`Embed.lean` and the axiom
files); the stage semantics with its soundness, which refutes the collapsed
derivation (`StageSemantics.lean`, `LowerBound.lean`); and, for the
provability half, the well-ordering proof carried out inside an arbitrary
model of `ID₁` — the accessible part is closed under the operations of the
notation, Gentzen's jump on the exponent lists, and the main lemma for `ϑ`
(`WellOrdering.lean`, `Lift.lean`, `Bridge.lean`, `UpperBound.lean`), which
then becomes provability by completeness.

## Buchholz–Pohlers: `|ID_n| = ψ₀(ε_{Ω_n+1})`, and `|ID_{<ω}|`

`OrdinalAnalysis/IDn/Final.lean`, with no hypothesis beyond `0 < n`:

```
idn_analysis (hn : 0 < n) :
  (∀ a : ThetaWNoteD, a < ThetaWNoteD.c n →
      IDn n (WForms orderFormulas n) ⊢ tiUptoSentence orderFormulas (Fin n) a) ∧
    ¬ IDn n (WForms orderFormulas n) ⊢
      tiUptoSentence orderFormulas (Fin n) (ThetaWNoteD.c n)

idn_lower_bound_unconditional (hn : 0 < n) :
  ¬ IDn n (WForms orderFormulas n) ⊢ tiUptoSentence orderFormulas (Fin n) (ThetaWNoteD.Omega 0)
```

and, in the same file, the two-sided theorem for the union over every finite level, again with
no hypothesis:

```
idlt_analysis :
  (∀ a : ThetaWNoteD, a.1 < ThetaWTerm.Omega 0 →
      IDlt (Upper.WFormsOmega orderFormulas) ⊢ tiUptoSentence orderFormulas ℕ a) ∧
    ¬ IDlt (Upper.WFormsOmega orderFormulas) ⊢ tiUptoSentence orderFormulas ℕ (ThetaWNoteD.Omega 0)
```

`IDn n A` (`IDn/Theory.lean`) is `n` simultaneous positive inductive definitions: a family of
operator forms `A : Fin n → Semisentence (LXIn n) 1`, one level-bounded fixed point per index —
`PositiveIn k (A k)` (`I_k` occurs only positively in its own form) and `LevelBounded k (A k)`
(every `I_j`-atom of `A k`, either polarity, has `j ≤ k`) — with closure and induction axioms
per level. `IDlt A` (`IDn/Union.lean`) is the union over `ι := ℕ`, built as a genuine colimit of
the finite pieces `IDseq m ⊆ IDseq (m+1) ⊆ ⋯` pushed into the joint language `LXIomega`, not a
shortcut definition. Standard-model soundness (`IDn/Sound.lean`'s `models_ID`, read at
`ι := Fin n`) reads each `I_k` as the `k`-th iterated least fixed point and gives
`IDn_consistent` for every positive, level-bounded family.

`ThetaWNoteD` (`Ordinal/ThetaW/`) is the multi-level ϑ-notation carrying Wilken's domain
condition: a term is admitted only when every subterm `ϑ_k ξ` satisfies `G_k(ξ) ≺* ξ` for the
generator function of Wilken 2011 (*Ordinal arithmetic with simultaneously defined
theta-functions*, Math. Log. Quart. 57, Definition 2.7 and Proposition 2.15). This is a genuine
restriction, not a formality: `ThetaWNoteD.wellFoundedLT` (`WellFoundedD.lean`) holds for the
domained order, while the same syntax without the domain guard, `ThetaWNote`, is *not*
well-founded (`Descent.lean`'s `not_wellFoundedLT`, an explicit infinite descending sequence).
`c n = ϑ₀(ϑ_n 0)` (`Dom.lean`) is the domained term for the intended value of `|ID_n|`. Above the
raw system, `HullSingle.lean` proves the level-free hull operator is least (`theta_isLeastS`,
Wilken's Proposition 3.9 at every level at once), and `HullDom.lean` derives the domain lemma the
collapsing theorem needs from it (`dom_add_omegaPow`) while also recording where the audited
approach breaks for the naively merged per-level operators (`not_dom_add_omegaPow_Hop`).

The collapsing machinery is a genuine interface, not copied per station:
`Ordinal/Collapsing/Interface.lean` separates the level-free operator algebra
(`CollapsingNotation`, the Buchholz operators `H_α`) from the per-level data
(`CollapsingLevel`: the domain of `ϑ_k`, `ϑ_k` itself, and the hull hypothesis the collapsing
theorem consumes), with `ThetaInstance.lean`/`ThetaWInstance.lean` supplying the instances for
`ID₁` and `ID_n` respectively.

**The calculus and its cut elimination.** `IDn/Calculus.lean`'s `IDnDerivable A ρ H α Γ` is the
multi-level operator-controlled infinitary calculus, indexed by a domained height and an
operator `H`. `IDn/Boundedness.lean`, `IDn/Reduction.lean` and `IDn/Elimination.lean` give the
boundedness lemma, the reduction lemma and ordinary elimination; `IDn/PredCut.lean`'s
`predicative_cut_elim` is Buchholz's predicative cut elimination at every level (Buchholz 1992,
*A simplified version of local predicativity*, Theorem 3.16: `H ⊢^α_{γ+ω^ρ} Γ ⇒ H ⊢^{φρα}_γ Γ`
per level, assembled in `PredCutCases/`); `IDn/Collapsing/Theorem.lean`'s `collapse` is Buchholz's
collapsing and impredicative cut elimination theorem (1992, Theorem 4.8), assembled from twelve
rule cases carried over from the calculus. `IDn/StageSemantics.lean`'s `StageSem.sound` is the
stage semantics that reads a collapsed derivation and refutes it, the multi-level analogue of the
`ID₁` station's boundedness invariant.

**The embedding, now fully discharged.** `IDn/Embed.lean`'s `embedding_theorem` is Freund's
Theorem 6.5 per level (arXiv:2204.09321), replaying an `IDn n A`-proof into the infinitary
calculus at height `Ω_n · 2 + m`, cut-free. It needs four axiom facts and one term-replacement
fact, packaged as a hypothesis structure `EmbedHyps`, and all seven of its fields are proved on
disk. `EmbedHypsAll.lean`'s `embedHyps_wForms` assembles six of them unconditionally from
already-merged bridges — the equality and `𝗣𝗔⁻` axioms and the tautology lemma
(`EmbedHypsLogic.lean`, `EmbedHypsTaut.lean`), the induction scheme (`EmbedHypsPA.lean`'s
`embedHyps_induction_of_pa`), the head-term replacement (`EmbedHypsReplace.lean`), and the
closure axioms via `closure_axiom` (`AxiomsIDCases/closure_derivable.lean`, Freund Proposition
6.2) — and takes the seventh field, the `I_k`-induction axioms, as an explicit hypothesis shaped
exactly like `indAx_axiom`'s statement. `IDn/Final.lean`'s `wForms_indAx` supplies that hypothesis
for the well-ordering forms from `indAx_axiom` itself (`AxiomsIDCases/indBody_inst.lean`, Freund
Proposition 6.4), closing the last field and making `idn_analysis` above hypothesis-free.

The tautology field needs its height chosen with care. `IDn/AxiomsLogic.lean`'s `taut` (Freund
Lemma 6.1) proves it at height `ω · rk ψ`; `IDn/TautAdditive.lean` shows this scaling is not a
matter of convenience — the same field stated at the plain additive height `rk ψ` is refuted
outright (`taut_additive_impossible`, at `ψ := ∀x.X(x)`), because the ω-rule's witness family
must dominate every natural number at once and no finite successor height can do that.

**The upper bound is unconditional.** `IDn/UpperFinal.lean`'s `idn_upper_bound'` and
`idlt_upper_bound'` take no hypotheses beyond `0 < n` (the latter, none at all): the internal
codes and order facts (`IDn/Internal/`) discharge every field the in-model level tower of
`IDn/Theorem.lean` needs, so `IDn n` proves transfinite induction up to every `a ≺ c_n`, and
`IDlt` up to every countable notation, outright. **The lower bound meets it exactly at `c_n`,
also unconditionally**: `CollapseCorollarySharp.lean`'s `idn_lower_bound_sharp'` and
`idn_theorem_sharp'` assemble the embedding, `m`-fold predicative cut elimination, and collapsing
at level `0` into non-provability of `TI` up to `c_n` itself, given `EmbedHyps` as a hypothesis;
chained with `embedHyps_wForms` and `wForms_indAx` above, that hypothesis is always available for
the well-ordering forms, which is exactly `idn_analysis`'s route in `Final.lean`.

`IDn/Theorem2.lean`'s `idlt_theorem` extends this to `IDlt`: beyond `EmbedHyps` at every level,
its lower half needs one further link, `IDseqToIDn` — a derivation from the finite fragment
`IDseq m`, in the union language `LXIomega`, translated back into an honest `IDn m` derivation.
`IDn/Retract.lean` proves it (`idseq_to_idn`): the language retraction `LXIω →ᵥ LXIn m` sending
`I_j` to `I_{min(j, m−1)}` carries every proof from the fragment into `ID_m`, and the empty case
`m = 0` is refuted through the lower bound for `ID_1`. `idlt_analysis` in `Final.lean` chains
these, so the two-sided result for `ID_{<ω}` holds outright, as does its upper half alone,
`idlt_upper_bound'` above.

**Ordinal bookkeeping.** In Buchholz's `ψ`, `|ID_n| = ψ₀(ε_{Ω_n+1})` (Buchholz 1986, *A new
system of proof-theoretic ordinal functions*, Theorem 3.7; Buchholz–Pohlers 1978); in the
`ϑ`-notation used here, the same ordinal is `c_n = ϑ₀(ϑ_n 0)`, the identification with
`ψ₀(ε_{Ω_n+1})` for `n ≥ 2` being in print in Weiermann–Wilken 2011. `|ID_{<ω}| = ψ₀(Ω_ω) =
sup_n c_n`. `Π¹₁-CA₀` has the same ordinal as `ID_{<ω}` by its conservativity over it
(Buchholz 1986, p. 203; Pohlers 1998, Fig. 1) — this last identification is cited here, not
formalized.

**Prior art.** As far as the surveys reach, no machine-checked ordinal analysis of `ID_n` for
`n ≥ 2`, or of `ID_{<ω}`, exists in any proof assistant. The one adjacent result is
koteitan's `pss-proof` (2026): a machine-checked well-foundedness proof, in Lean 4 and Isabelle,
of Buchholz's notation `OT_B` below `ψ₀(Ω_ω)` — precisely the ordinal `|ID_{<ω}|` identifies here
— with no ordinal analysis built on it.

## Building

```
lake exe cache get
lake build
```

`lake exe cache get` fetches mathlib's prebuilt oleans and saves hours.
Foundation has no cache and is compiled locally.
