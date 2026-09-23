/-
  The finitary theory of ramified analysis, `RA_{<ν}` — design **D2**.

  This is the object theory whose ordinal is to be computed: `|RA_{<ν}| = φ_ν(0)`
  (Schütte ch. VIII–IX).  The whole point of D2 is visible in its *type*:

      RA (Λ : Set Lv) : Theory LRA

  a Foundation **first-order** theory, i.e. a set of `Sentence LRA`.  So
  `Theory.Proof.provable_iff` applies unchanged — a proof unpacks to an `LK`
  derivation of `σ :: ∼axioms`, which `Ramified/Embed.lean` replays into `RA_∞` —
  and so does everything else Foundation has for first-order theories
  (soundness, completeness, compactness).  Design D1 would have had to redo all
  of it for a forked second-order syntax; that is the con the design note lists
  against D1 and the pro it lists for D2.

  Four groups of axioms.

  * `𝗘𝗤 LRA` — equality for the *entire* enlarged language.  This is what
    supplies congruence for `X` and for every `∈̇_ν`; transporting the equality
    axioms of arithmetic alone would not.
  * `Theory.lMap toLRA 𝗣𝗔⁻` — the axioms of `PA⁻`, transported.
  * `InductionScheme LRA Set.univ` — induction for **every** `LRA`-formula,
    including those mentioning `X` and the membership symbols.  This is the same
    choice `Gentzen/Setup.lean`'s `paLX` makes, and for the same reason: with
    induction only for arithmetic formulas the calibration collapses.
  * `NamingAxioms Λ` — the **naming (comprehension) axioms**, one pair for each
    well-formed code `a` whose level lies in `Λ`:

        ∀x (x ∈̇_{lvl a} ā → A_a(x))        `nameOut`
        ∀x (A_a(x) → x ∈̇_{lvl a} ā)        `nameIn`

    with `A_a = body a`.  Written as two one-sided implications rather than one
    biconditional because the calculus is Tait-style; together they are the
    biconditional.

  ## Two things the prototype's notes settle, and one it does not

  **The naming axioms are an external schema** : one *instance per code*, generated in the metalanguage
  exactly as `InductionScheme` generates one instance per formula.  D2 therefore
  needs **no arithmetized `Good`/`body`** — no Σ₁-definable well-formedness
  predicate, no internal decoding.  That is a genuine saving: the design note's
  1,400-line estimate for this row was priced with an internal coding in it.

  **`Λ` is a set of levels, not a bound.**  `RAlt ν := RA {μ | μ < ν}` is the
  `RA_{<ν}` of the literature; keeping the general `Λ` costs nothing and makes
  `RA_subset` — monotonicity — a one-liner, which is what the level-by-level
  climb of the upper bound will iterate.

  **Codes must be parameter-free.**  A code `a` names *one* set, so its body may
  not carry free number variables: the axiom would be universally closed over
  them (`Semiformula.univCl` is how a `Proposition` becomes a `Sentence`) and two
  different values of a parameter would impose contradictory conditions on the
  same name.  Concretely, `A(x) :≡ x = &0` at level `1` would give
  `∀y ∀x (x ∈̇_1 ā ↔ x = y)`, which is refutable.  `ParamFree` is that side
  condition, and it is exactly the restriction `Ramified/Code.lean` already
  anticipates ("What is deliberately *not* here: parameters").  Predicators
  *with* parameters are a `⟨ν, ⌜A⌝, p⃗⟩` coding and belong with the full
  development; nothing below changes when they arrive except `ParamFree`, which
  becomes "the parameters of the body are among those the code records".

  ## The level guard on `RA_{<ν}`

  `RA Λ` puts *no* level restriction on its equality axioms or its induction
  scheme: `𝗘𝗤 LRA` supplies the congruence axiom of `∈̇_μ` for **every** `μ`, and
  `InductionScheme LRA Set.univ` supplies induction for **every** `LRA`-formula.
  That is exactly right for `RA Λ` itself — it is the union of all the
  ramified stages — but it is *wrong* for `RAlt ν`, the `RA_{<ν}` of the
  literature (Schütte ch. VIII–IX), whose whole point is that it talks about
  sets of level `< ν` only.

  The reason this is not bookkeeping but a correctness condition is the cut-rank
  bound the upper bound needs.  `Ramified/Rank.lean` prices a level-`μ` set atom
  at `rank = ω^μ`, and predicative cut elimination consumes derivations whose cut
  rank sits inside a single block `[0, ω^ν)`
  (`Rank.rank_lt_omegaPow_of_level : lvlOf φ < ν → rank φ < ω^ν`). If `RAlt ν`
  contained the congruence axiom of `∈̇_μ` for some `μ ≥ ν`, or induction for a
  formula mentioning `∈̇_μ`, a derivation from `RAlt ν` could legitimately cut on
  a formula of rank `ω^μ ≥ ω^ν` — the bound would be false, and with it the
  ordinal analysis of `RAlt ν`.

  The fix is to define `RAlt ν` by intersecting each unrestricted block of
  `RA Λ` with the level condition it needs: the equality axioms are kept only
  when their embedded `Proposition` has level `< ν`, and the induction scheme is
  restricted from `Set.univ` to `{φ | lvlOf φ < ν}` — exactly `Foundation`'s own
  device (`InductionScheme` already takes an arbitrary predicate `Γ`, and
  `Set.univ` was simply the ungraded choice `RA Λ` needs and `RAlt ν` does not).
  The naming schema was already graded (`NamingAxioms {μ | μ < ν}`), and `𝗣𝗔⁻`
  is levelless by construction (its axioms come from `ℒₒᵣ`, which has no set
  atoms at all), so those two blocks are unchanged.  The upshot is
  `lvlOf_emb_lt_of_mem_RAlt`: *every* axiom of `RAlt ν` (for `ν ≥ 1`) has level
  `< ν`, which is what `Ramified/Axioms.lean` turns into the rank bound
  `rank_evR_emb_lt_of_mem_RAlt` the upper bound consumes.

  `RAlt ν` is therefore **not** `RA {μ | μ < ν}` — it is a strict subset of it
  (`RAlt_subset_RA`), obtained by cutting down the two ungraded blocks of `RA`
  rather than by restricting the naming levels alone.
-/
import OrdinalAnalysis.Ramified.Code

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### Parameter-free codes -/

/-- A code is **parameter-free** when its body has no free number variable.  See
the header: without it the universally closed naming axiom is refutable. -/
def ParamFree (a : ℕ) : Prop := (body a).freeVariables = ∅

theorem paramFree_code {ν : Lv} {A : Semiformula LRA ℕ 1} (h : A.freeVariables = ∅) :
    ParamFree (code ν A) := by
  rw [ParamFree, body_code]
  exact h

/-! ### The naming axioms

`nameTerm a` is the numeral `ā` one binder down, where the subject `#0` lives. -/

/-- The name of the code `a`, as a term with one bound variable available. -/
def nameTerm (a : ℕ) : Semiterm LRA ℕ 1 := Semiterm.numeral a

/-- `∀x (x ∈̇_{lvl a} ā → A_a(x))` — "everything named by `a` satisfies its
body". -/
def nameOut (a : ℕ) : Proposition LRA :=
  ∀¹ (nmemAt (lvl a) (#0 : Semiterm LRA ℕ 1) (nameTerm a) ⋎ body a)

/-- `∀x (A_a(x) → x ∈̇_{lvl a} ā)` — "everything satisfying the body is named by
`a`". -/
def nameIn (a : ℕ) : Proposition LRA :=
  ∀¹ (∼(body a) ⋎ memAt (lvl a) (#0 : Semiterm LRA ℕ 1) (nameTerm a))

/-- The level of a naming axiom is the level of its code: the body sits strictly
below `lvl a` and the set atom sits exactly at it. -/
@[simp] theorem lvlOf_nameOut {a : ℕ} (h : Good a) : lvlOf (nameOut a) = lvl a := by
  simp only [nameOut, lvlOf_all, lvlOf_or, lvlOf_nmemAt]
  exact max_eq_left (le_of_lt (good_body_lvl h))

@[simp] theorem lvlOf_nameIn {a : ℕ} (h : Good a) : lvlOf (nameIn a) = lvl a := by
  simp only [nameIn, lvlOf_all, lvlOf_or, lvlOf_memAt, lvlOf_neg]
  exact max_eq_right (le_of_lt (good_body_lvl h))

/-- **The naming schema at the levels `Λ`.**  An *external* schema: one instance
per well-formed parameter-free code whose level lies in `Λ`, in both directions,
universally closed into a sentence. -/
def NamingAxioms (Λ : Set Lv) : Theory LRA :=
  { σ | ∃ a : ℕ, Good a ∧ ParamFree a ∧ lvl a ∈ Λ ∧
      (σ = Semiformula.univCl (nameOut a) ∨ σ = Semiformula.univCl (nameIn a)) }

theorem mem_NamingAxioms_out {Λ : Set Lv} {a : ℕ} (hg : Good a) (hp : ParamFree a)
    (hν : lvl a ∈ Λ) : Semiformula.univCl (nameOut a) ∈ NamingAxioms Λ :=
  ⟨a, hg, hp, hν, Or.inl rfl⟩

theorem mem_NamingAxioms_in {Λ : Set Lv} {a : ℕ} (hg : Good a) (hp : ParamFree a)
    (hν : lvl a ∈ Λ) : Semiformula.univCl (nameIn a) ∈ NamingAxioms Λ :=
  ⟨a, hg, hp, hν, Or.inr rfl⟩

/-- The schema is monotone in the set of levels. -/
theorem NamingAxioms_subset {Λ Λ' : Set Lv} (h : Λ ⊆ Λ') :
    NamingAxioms Λ ⊆ NamingAxioms Λ' := by
  rintro σ ⟨a, hg, hp, hν, hσ⟩
  exact ⟨a, hg, hp, h hν, hσ⟩

/-! ### The theory -/

/-- **`RA Λ`** — ramified analysis with names at the levels `Λ`: equality for the
whole of `LRA`, `PA⁻`, induction for *every* `LRA`-formula, and the naming
axioms. -/
def RA (Λ : Set Lv) : Theory LRA :=
  𝗘𝗤 LRA ∪ (Theory.lMap toLRA 𝗣𝗔⁻ ∪ (InductionScheme LRA Set.univ ∪ NamingAxioms Λ))

/-! ### Level bookkeeping for the guard

Four lemmas about `lvlOf`, needed once each by `RAlt`'s side conditions and by
`lvlOf_emb_lt_of_mem_RAlt` below.  None of them is specific to `RAlt`: they say
that `lvlOf` is blind to the `lMap`-transport of arithmetic, to universal
closure, and to the three occurrences of the body inside `succInd` — the same
kind of fact `Code.lean`'s `lvlOf_rew`/`lvlOf_neg` already record. -/

/-- **A transported `ℒₒᵣ`-formula is levelless.**  `toLRA` tags every arithmetic
relation symbol `Sum.inl`, and `relLevel (Sum.inl r) = none` always
(`relLevel_inl`); the four connective/quantifier cases just propagate `0`. -/
theorem lvlOf_lMap_toLRA {n : ℕ} : ∀ (φ : Semiformula ℒₒᵣ ℕ n),
    lvlOf (Semiformula.lMap toLRA φ) = 0 := by
  intro φ
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => rfl
  | hnrel r v => rfl
  | hand φ ψ ihφ ihψ => simp [LogicalConnective.HomClass.map_and, lvlOf_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [LogicalConnective.HomClass.map_or, lvlOf_or, ihφ, ihψ]
  | hall φ ih => simp [Semiformula.lMap_all, lvlOf_all, ih]
  | hexs φ ih => simp [Semiformula.lMap_exs, lvlOf_exs, ih]

/-- **`lvlOf` does not see a universal closure.**  `∀¹*` peels one `∀¹` at a
time (`allClosure_succ`), and `lvlOf_all` does not move the level either. -/
theorem lvlOf_allClosure : ∀ {n : ℕ} (φ : Semiformula LRA ℕ n), lvlOf (∀¹* φ) = lvlOf φ
  | 0, φ => rfl
  | n + 1, φ => by rw [allClosure_succ, lvlOf_allClosure (∀¹ φ), lvlOf_all]

/-- **`lvlOf` does not see the passage from a closed `Proposition` to its
`Sentence` universal closure.**  `Semiformula.univCl X = X.univCl'.toEmpty _`
and `emb` inverts `toEmpty` (`emb_toEmpty`); `X.univCl'` is a `fixitr`-rewriting
of `X` under `∀¹*`, and neither move touches a relation symbol. -/
theorem lvlOf_emb_univCl (X : Proposition LRA) :
    lvlOf (Rewriting.emb (Semiformula.univCl X) : Proposition LRA) = lvlOf X := by
  have h1 : (Rewriting.emb (Semiformula.univCl X) : Proposition LRA) = X.univCl' := by
    simp [Semiformula.univCl]
  rw [h1, Semiformula.univCl', lvlOf_allClosure, lvlOf_rew]

/-- **`succInd φ` has the same level as its body.**  `succInd φ` unfolds
(definitionally) to three substitution instances of `φ` — at `0̄`, `#0` and
`#0 + 1` — joined by `→` and `∀¹`; substitution does not move the level
(`lvlOf_subst₁`), and neither does `→` (which is `∼_ ⋎ _`) or `∀¹`. -/
theorem lvlOf_succInd (φ : Semiformula LRA ℕ 1) : lvlOf (succInd φ) = lvlOf φ := by
  show lvlOf ((φ/[((0 : ℕ) : SyntacticTerm LRA)]) 🡒
      (∀¹ (φ/[(#0 : Semiterm LRA ℕ 1)] 🡒 φ/[(‘(#0 + 1)’ : Semiterm LRA ℕ 1)]))
      🡒 ∀¹ (φ/[(#0 : Semiterm LRA ℕ 1)])) = lvlOf φ
  simp [Semiformula.imp_eq, lvlOf_or, lvlOf_neg, lvlOf_all]

/-- **`RA_{<ν}`**, the theory of the literature.  Ungraded `RA Λ` cut down by
the level guard the header explains: the equality axioms and the induction
scheme are restricted to level `< ν`, exactly as the naming schema already was.

`RAlt ν` is *not* `RA {μ | μ < ν}` — it is a strict subset of it
(`RAlt_subset_RA`); see the header for why the wider theory does not have the
cut-rank bound the upper bound needs. -/
def RAlt (ν : Lv) : Theory LRA :=
  {σ | σ ∈ 𝗘𝗤 LRA ∧ lvlOf (Rewriting.emb σ : Proposition LRA) < ν}
    ∪ (Theory.lMap toLRA 𝗣𝗔⁻ ∪ (InductionScheme LRA (fun φ => lvlOf φ < ν) ∪ NamingAxioms {μ | μ < ν}))

/-! ### Membership -/

section Membership

variable {Λ : Set Lv}

theorem eq_subset_RA : 𝗘𝗤 LRA ⊆ RA Λ := fun _ h => Or.inl h

theorem mem_RA_of_mem_eq {σ : Sentence LRA} (h : σ ∈ 𝗘𝗤 LRA) : σ ∈ RA Λ := Or.inl h

theorem mem_RA_of_mem_peanoMinus {σ : Sentence LRA} (h : σ ∈ Theory.lMap toLRA 𝗣𝗔⁻) :
    σ ∈ RA Λ := Or.inr (Or.inl h)

/-- Every axiom of `PA⁻`, transported along `toLRA`, is an axiom. -/
theorem lMap_peanoMinus_mem_RA {σ : Sentence ℒₒᵣ} (h : σ ∈ 𝗣𝗔⁻) :
    Semiformula.lMap toLRA σ ∈ RA Λ :=
  mem_RA_of_mem_peanoMinus ⟨σ, h, rfl⟩

theorem mem_RA_of_mem_induction {σ : Sentence LRA} (h : σ ∈ InductionScheme LRA Set.univ) :
    σ ∈ RA Λ := Or.inr (Or.inr (Or.inl h))

/-- **Induction for every `LRA`-formula** — including those with set atoms. -/
theorem induction_mem_RA (φ : Semiformula LRA ℕ 1) :
    Semiformula.univCl (succInd φ) ∈ RA Λ :=
  mem_RA_of_mem_induction ⟨φ, trivial, rfl⟩

theorem mem_RA_of_mem_naming {σ : Sentence LRA} (h : σ ∈ NamingAxioms Λ) : σ ∈ RA Λ :=
  Or.inr (Or.inr (Or.inr h))

theorem nameOut_mem_RA {a : ℕ} (hg : Good a) (hp : ParamFree a) (hν : lvl a ∈ Λ) :
    Semiformula.univCl (nameOut a) ∈ RA Λ :=
  mem_RA_of_mem_naming (mem_NamingAxioms_out hg hp hν)

theorem nameIn_mem_RA {a : ℕ} (hg : Good a) (hp : ParamFree a) (hν : lvl a ∈ Λ) :
    Semiformula.univCl (nameIn a) ∈ RA Λ :=
  mem_RA_of_mem_naming (mem_NamingAxioms_in hg hp hν)

end Membership

section MembershipAlt

variable {ν : Lv}

theorem mem_RAlt_of_eq {σ : Sentence LRA} (h1 : σ ∈ 𝗘𝗤 LRA)
    (h2 : lvlOf (Rewriting.emb σ : Proposition LRA) < ν) : σ ∈ RAlt ν :=
  Or.inl ⟨h1, h2⟩

theorem mem_RAlt_of_peanoMinus {σ : Sentence LRA} (h : σ ∈ Theory.lMap toLRA 𝗣𝗔⁻) :
    σ ∈ RAlt ν := Or.inr (Or.inl h)

/-- **Induction for every `LRA`-formula whose level is below `ν`.**  The one
place `RAlt ν` differs from `RA Λ`'s `induction_mem_RA`: the side condition
`lvlOf φ < ν` is required, not discharged by `trivial`. -/
theorem induction_mem_RAlt (φ : Semiformula LRA ℕ 1) (h : lvlOf φ < ν) :
    Semiformula.univCl (succInd φ) ∈ RAlt ν :=
  Or.inr (Or.inr (Or.inl ⟨φ, h, rfl⟩))

theorem naming_mem_RAlt {σ : Sentence LRA} (h : σ ∈ NamingAxioms {μ | μ < ν}) :
    σ ∈ RAlt ν := Or.inr (Or.inr (Or.inr h))

/-- **`RAlt ν ⊆ RA {μ | μ < ν}`.**  The guard only removes axioms — every block
of `RAlt ν` widens to the corresponding ungraded block of `RA`. -/
theorem RAlt_subset_RA (ν : Lv) : RAlt ν ⊆ RA {μ | μ < ν} := by
  rintro σ (⟨hσ, -⟩ | hσ | ⟨φ, -, rfl⟩ | hσ)
  · exact mem_RA_of_mem_eq hσ
  · exact mem_RA_of_mem_peanoMinus hσ
  · exact mem_RA_of_mem_induction ⟨φ, trivial, rfl⟩
  · exact mem_RA_of_mem_naming hσ

end MembershipAlt

/-! ### Monotonicity in the levels -/

/-- **`RA` is monotone in `Λ`.**  Only the naming schema moves. -/
theorem RA_subset {Λ Λ' : Set Lv} (h : Λ ⊆ Λ') : RA Λ ⊆ RA Λ' := by
  rintro σ (hσ | hσ | hσ | hσ)
  · exact Or.inl hσ
  · exact Or.inr (Or.inl hσ)
  · exact Or.inr (Or.inr (Or.inl hσ))
  · exact Or.inr (Or.inr (Or.inr (NamingAxioms_subset h hσ)))

/-- **`RAlt` is monotone in `ν`.**  All four blocks move: the level bounds
`lvlOf (emb σ) < μ`, `lvlOf φ < μ` and `{x | x < μ}` all widen under `μ ≤ ν`. -/
theorem RAlt_subset {μ ν : Lv} (h : μ ≤ ν) : RAlt μ ⊆ RAlt ν := by
  rintro σ (⟨hσ, hlvl⟩ | hσ | ⟨φ, hφ, rfl⟩ | hσ)
  · exact mem_RAlt_of_eq hσ (lt_of_lt_of_le hlvl h)
  · exact mem_RAlt_of_peanoMinus hσ
  · exact induction_mem_RAlt φ (lt_of_lt_of_le hφ h)
  · exact naming_mem_RAlt (NamingAxioms_subset (fun _ hx => lt_of_lt_of_le hx h) hσ)

/-- Everything `RA Λ` proves, `RA Λ'` proves. -/
theorem RA_weakerThan {Λ Λ' : Set Lv} (h : Λ ⊆ Λ') : RA Λ ⪯ RA Λ' :=
  Theory.Proof.weakerThan_of_le (RA_subset h)

theorem RAlt_weakerThan {μ ν : Lv} (h : μ ≤ ν) : RAlt μ ⪯ RAlt ν :=
  Theory.Proof.weakerThan_of_le (RAlt_subset h)

/-- The equality theory is available inside `RA Λ`, exactly as
`Gentzen/Setup.lean`'s `paLX_eqTheory` makes it available inside `PA[X]`. -/
instance RA_eqTheory (Λ : Set Lv) : 𝗘𝗤 LRA ⪯ RA Λ :=
  Entailment.WeakerThan.ofSubset eq_subset_RA

/-! ### Every level-correct closed formula is named

This is the half of the naming schema the upper bound consumes: `Code.lean`'s
`exists_good_code` supplies the witness, and the schema then supplies the two
axioms for it.  It is what makes "a level-`ν` set is a numeral" more than a
slogan — the theory can *talk about* every level-correct predicator. -/

/-- **Naming.**  For every closed `A` all of whose set atoms sit below `ν`, and
every `ν ∈ Λ`, there is a code naming `A` at level `ν`, and both of its naming
axioms are axioms of `RA Λ`. -/
theorem exists_naming {Λ : Set Lv} {ν : Lv} (hν : ν ∈ Λ) {A : Semiformula LRA ℕ 1}
    (hlvl : lvlOf A < ν) (hcl : A.freeVariables = ∅) :
    ∃ a : ℕ, Good a ∧ ParamFree a ∧ lvl a = ν ∧ body a = A ∧
      Semiformula.univCl (nameOut a) ∈ RA Λ ∧ Semiformula.univCl (nameIn a) ∈ RA Λ := by
  refine ⟨code ν A, good_code hlvl, paramFree_code hcl, lvl_code ν A, body_code ν A, ?_, ?_⟩
  · exact nameOut_mem_RA (good_code hlvl) (paramFree_code hcl) (by rw [lvl_code]; exact hν)
  · exact nameIn_mem_RA (good_code hlvl) (paramFree_code hcl) (by rw [lvl_code]; exact hν)

/-- The `RA_{<ν}` form: names for every level-correct closed `A` at every level
`μ < ν` above `lvlOf A`.

Not an instance of `exists_naming`, because `RAlt ν` is no longer `RA {x | x <
ν}` — proved the same way instead, landing in `RAlt ν` through
`naming_mem_RAlt`. -/
theorem exists_naming_lt {ν μ : Lv} (hμ : μ < ν) {A : Semiformula LRA ℕ 1}
    (hlvl : lvlOf A < μ) (hcl : A.freeVariables = ∅) :
    ∃ a : ℕ, Good a ∧ ParamFree a ∧ lvl a = μ ∧ body a = A ∧
      Semiformula.univCl (nameOut a) ∈ RAlt ν ∧ Semiformula.univCl (nameIn a) ∈ RAlt ν := by
  refine ⟨code μ A, good_code hlvl, paramFree_code hcl, lvl_code μ A, body_code μ A, ?_, ?_⟩
  · exact naming_mem_RAlt
      (mem_NamingAxioms_out (good_code hlvl) (paramFree_code hcl) (by rw [lvl_code]; exact hμ))
  · exact naming_mem_RAlt
      (mem_NamingAxioms_in (good_code hlvl) (paramFree_code hcl) (by rw [lvl_code]; exact hμ))

/-! ### The level bound the guard buys

The reason the guard exists: every axiom of `RAlt ν` (for `ν ≥ 1`) has level
`< ν`.  `Ramified/Axioms.lean` turns this into the rank bound
`rank_evR_emb_lt_of_mem_RAlt` via `Rank.rank_lt_omegaPow_of_level`. -/

/-- **Every axiom of `RAlt ν` has level below `ν`.**  One case per block: the
equality axioms carry the bound in their definition, `PA⁻` is levelless
(`lvlOf_lMap_toLRA`, using `ν ≥ 1`), the induction scheme carries the bound in
its side condition (via `lvlOf_emb_univCl` and `lvlOf_succInd`), and the naming
schema carries it in `Good`/`lvl a ∈ {μ | μ < ν}` (via `lvlOf_emb_univCl` and
`lvlOf_nameOut`/`lvlOf_nameIn`). -/
theorem lvlOf_emb_lt_of_mem_RAlt {ν : Lv} (hν : 1 ≤ ν) {σ : Sentence LRA} (h : σ ∈ RAlt ν) :
    lvlOf (Rewriting.emb σ : Proposition LRA) < ν := by
  rcases h with ⟨-, hlvl⟩ | h | ⟨φ, hφ, rfl⟩ | h
  · exact hlvl
  · obtain ⟨τ, -, rfl⟩ := h
    rw [← Semiformula.lMap_emb, lvlOf_lMap_toLRA]
    exact hν
  · rw [lvlOf_emb_univCl, lvlOf_succInd]
    exact hφ
  · obtain ⟨a, hg, -, hlt, rfl | rfl⟩ := h
    · rw [lvlOf_emb_univCl, lvlOf_nameOut hg]; exact hlt
    · rw [lvlOf_emb_univCl, lvlOf_nameIn hg]; exact hlt

/-! ### `RA Λ` is a first-order theory, and that is the point of D2

Nothing below is new mathematics — it is Foundation's own `provable_iff`,
recorded at `RA Λ` so that the replay has the statement it consumes in the exact
shape it consumes it.  Under design D1 this file would instead have had to
re-establish the whole provability apparatus for a forked second-order syntax. -/

/-- **`RA Λ ⊢ σ` unpacks to an `LK` derivation** of `σ` together with the
negations of finitely many axioms.  `Ramified/Embed.lean`'s `replayR` takes that
derivation into `RA_∞`. -/
theorem RA_provable_iff {Λ : Set Lv} {σ : Sentence LRA} :
    RA Λ ⊢ σ ↔ ∃ Γ : List (Sentence LRA), (∀ ψ ∈ Γ, ψ ∈ RA Λ) ∧
      Nonempty (⊢ᴸᴷ¹ (σ : Proposition LRA) :: ∼Sequent.embed Γ) :=
  Theory.Proof.provable_iff

theorem RAlt_provable_iff {ν : Lv} {σ : Sentence LRA} :
    RAlt ν ⊢ σ ↔ ∃ Γ : List (Sentence LRA), (∀ ψ ∈ Γ, ψ ∈ RAlt ν) ∧
      Nonempty (⊢ᴸᴷ¹ (σ : Proposition LRA) :: ∼Sequent.embed Γ) :=
  Theory.Proof.provable_iff

end Ramified

end OrdinalAnalysis
