/-
  The finitary theory of ramified analysis, `RA Λ` — design **D2**.

  The theory is a Foundation **first-order** theory, `RA (Λ : Set Lv) : Theory
  LRA`, i.e. a set of `Sentence LRA`.  So `Theory.Proof.provable_iff` applies
  unchanged — a proof unpacks to an `LK` derivation of `σ :: ∼axioms`, which
  `Ramified/Embed.lean` replays into `RA_∞` — and so does everything else
  Foundation has for first-order theories (soundness, completeness,
  compactness).

  Four groups of axioms.

  * `𝗘𝗤 LRA` — equality for the *entire* enlarged language.  This is what
    supplies congruence for `X` and for every `∈̇_ν`.
  * `Theory.lMap toLRA 𝗣𝗔⁻` — the axioms of `PA⁻`, transported.
  * `InductionScheme LRA Set.univ` — induction for **every** `LRA`-formula,
    including those mentioning `X` and the membership symbols.
  * `NamingAxioms Λ` — the **naming (comprehension) axioms**.

  ## The naming schema: one pair of axioms per formula, uniform in the code

  A level-`μ` set is a numeral `c = ⟨μ, s, ⌜A⌝, p⟩` (`Ramified/Code.lean`): a
  formula `A(x, p)` of shape `μ` with its parameter `p`, at a stage `s`.  For
  each level `μ ∈ Λ` with `μ > 0` and each formula `A` of shape `μ` the schema
  has the two axioms

      nameOutP μ A :≡ ∀c ∀p ∀s (G(c, p, s) → ∀x (x ∈̇_μ c → A(x, p)))
      nameInP  μ A :≡ ∀c ∀p ∀s (G(c, p, s) → ∀x (A(x, p) → x ∈̇_μ c))

  where the guard `G(c, p, s)` is the arithmetical formula
  `c = ⟨μ, s, ⌜A⌝, p⟩ ∧ A.complexity + stage p < s` (`Ramified/Guard.lean`).

  Three features, each forced.

  * **The parameter is a set of the same level.**  With parameter-free codes
    whose bodies mention only lower levels, every proof uses finitely many
    codes, and the level-`μ` sets it sees can be read level by level as
    explicit formulas of `PA[X]`: such a theory is conservative over `PA[X]`,
    however many levels it has.  A same-level parameter breaks this: at the jump
    formula the schema proves `∀z ∃w ∀x (x ∈̇_μ w ↔ J(x, z))`, closure of level
    `μ` under the jump uniformly in a level-`μ` set (`Ramified/Comprehension.lean`).

  * **The stage guard.**  Without it the schema is inconsistent:
    `A(x, p) :≡ x ∉̇_μ ⟨p, p⟩` would name, at `c = ⟨⌜A⌝, ⌜A⌝⟩`, a set with
    `x ∈̇_μ c ↔ x ∉̇_μ c`.  With it, a code is defined from a parameter of
    strictly smaller stage and membership is a recursion on (level, stage); the
    same inequality is what makes the predicator rule lower the cut rank
    (`Ramified/Rank.lean`).

  * **One axiom per formula, not per code.**  The code is a universally
    quantified number, so a single axiom speaks about every parameter at once —
    which is exactly what a comprehension principle with a set parameter has to
    do.  Everything about codes that the schema needs is arithmetic, and is
    decided in the guard; the schema needs no arithmetized syntax.

  The level of both axioms is `μ` (`lvlOf_nameOutP`, `lvlOf_nameInP`): the guard
  is arithmetical, `A` has shape `μ`, and the set atom sits at `μ`.  So the
  level guard of `RAlt ν` below is unchanged.  The parameter-free codes are the
  case where `A` is closed and the parameter is `0`
  (`Ramified/Comprehension.lean`'s `exists_naming`).

  ## The level guard on `RA_{<ν}`

  `RA Λ` puts *no* level restriction on its equality axioms or its induction
  scheme.  That is right for `RA Λ` itself, but wrong for `RAlt ν`, the theory
  of the sets of level `< ν`: `Ramified/Rank.lean` prices a level-`μ` set atom
  at up to `blkTop μ` (`ω·μ` at a finite `μ`), and predicative cut elimination consumes derivations whose
  cut rank sits below `blkTop ν` (`Rank.rank_lt_blkTop_of_level : lvlOf φ < ν →
  rank φ < blkTop ν`).  If `RAlt ν` contained the congruence axiom of `∈̇_μ` for some
  `μ ≥ ν`, or induction for a formula mentioning `∈̇_μ`, a derivation from
  `RAlt ν` could legitimately cut on a formula of rank `≥ blkTop ν`.

  So `RAlt ν` intersects each unrestricted block of `RA Λ` with the level
  condition it needs: the equality axioms are kept only when their embedded
  `Proposition` has level `< ν`, and the induction scheme is restricted from
  `Set.univ` to `{φ | lvlOf φ < ν}`.  The naming schema is graded
  (`NamingAxioms {μ | μ < ν}`), and `𝗣𝗔⁻` is levelless.  The upshot is
  `lvlOf_emb_lt_of_mem_RAlt`: *every* axiom of `RAlt ν` (for `ν ≥ 1`) has level
  `< ν`, which `Ramified/Axioms.lean` turns into the rank bound
  `rank_evR_emb_lt_of_mem_RAlt`.  `RAlt ν` is a strict subset of
  `RA {μ | μ < ν}` (`RAlt_subset_RA`).
-/
import OrdinalAnalysis.Ramified.Guard

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### The per-code naming formulas

`nameTerm a` is the numeral `ā` one binder down, where the subject `#0` lives.
`nameOut a`/`nameIn a` say that the code `a` names its body; for a `Good` code
they are theorems of the theory (`Ramified/Comprehension.lean`'s
`exists_naming`), not axioms. -/

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

/-- The level of a naming formula is the level of its code: the body sits at or
below `lvl a` and the set atom sits exactly at it. -/
@[simp] theorem lvlOf_nameOut {a : ℕ} (h : Good a) : lvlOf (nameOut a) = lvl a := by
  simp only [nameOut, lvlOf_all, lvlOf_or, lvlOf_nmemAt]
  exact max_eq_left (good_body_lvl h)

@[simp] theorem lvlOf_nameIn {a : ℕ} (h : Good a) : lvlOf (nameIn a) = lvl a := by
  simp only [nameIn, lvlOf_all, lvlOf_or, lvlOf_memAt, lvlOf_neg]
  exact max_eq_right (good_body_lvl h)

/-! ### The naming schema

Inside the axioms the bound variables are, from the outside in, `s`, `p`, `c`
(`∀¹*` over a matrix with three bound variables `#0 = c`, `#1 = p`, `#2 = s`),
and then the subject `x`: under the last binder `#0 = x`, `#1 = c`, `#2 = p`,
`#3 = s`. -/

/-- The guard `G(c, p, s)` of the formula `A` at level `μ`, as an arithmetical
semisentence with free slots `c`, `p`, `s`. -/
def guardSS (μ : Lv) (A : Semiformula LRA ℕ 1) : Semisentence ℒₒᵣ 3 :=
  Rew.subst ![(#0 : Semiterm ℒₒᵣ Empty 3), #1, #2, ((Encodable.encode μ : ℕ) : Semiterm ℒₒᵣ Empty 3),
    ((Encodable.encode A : ℕ) : Semiterm ℒₒᵣ Empty 3),
    (A.complexity : Semiterm ℒₒᵣ Empty 3)] ▹ guardDef.val

/-- The guard, transported to `LRA`. -/
def guardR (μ : Lv) (A : Semiformula LRA ℕ 1) : Semiformula LRA ℕ 3 :=
  Semiformula.lMap toLRA (Rewriting.emb (guardSS μ A))

/-- `A(x, p)` under the four binders `s p c x`: the subject is `#0` and every
free variable of `A` becomes the parameter `#2`. -/
def instA (A : Semiformula LRA ℕ 1) : Semiformula LRA ℕ 4 :=
  Rew.bind ![(#0 : Semiterm LRA ℕ 4)] (fun _ => #2) ▹ A

/-- The matrix of `nameOutP`: `G(c, p, s) → ∀x (x ∈̇_μ c → A(x, p))`. -/
def nameOutMat (μ : Lv) (A : Semiformula LRA ℕ 1) : Semiformula LRA ℕ 3 :=
  ∼(guardR μ A) ⋎ (∀¹ (nmemAt μ (#0 : Semiterm LRA ℕ 4) #1 ⋎ instA A))

/-- The matrix of `nameInP`: `G(c, p, s) → ∀x (A(x, p) → x ∈̇_μ c)`. -/
def nameInMat (μ : Lv) (A : Semiformula LRA ℕ 1) : Semiformula LRA ℕ 3 :=
  ∼(guardR μ A) ⋎ (∀¹ (∼(instA A) ⋎ memAt μ (#0 : Semiterm LRA ℕ 4) #1))

/-- **`nameOutP μ A`**: every code of `A` at level `μ` names only elements of
`{x | A(x, p)}`. -/
def nameOutP (μ : Lv) (A : Semiformula LRA ℕ 1) : Proposition LRA := ∀¹* (nameOutMat μ A)

/-- **`nameInP μ A`**: every code of `A` at level `μ` names all of
`{x | A(x, p)}`. -/
def nameInP (μ : Lv) (A : Semiformula LRA ℕ 1) : Proposition LRA := ∀¹* (nameInMat μ A)

/-- **A transported `ℒₒᵣ`-formula is levelless.**  `toLRA` tags every arithmetic
relation symbol `Sum.inl`, and `relLevel (Sum.inl r) = none` always
(`relLevel_inl`); the four connective/quantifier cases just propagate `0`. -/
theorem lvlOf_lMap_toLRA {n : ℕ} : ∀ (φ : Semiformula ℒₒᵣ ℕ n),
    lvlOf (Semiformula.lMap toLRA φ) = 0 := by
  intro φ
  induction φ using Semiformula.rec' with
  | hverum => rw [lvlOf_def]; rfl
  | hfalsum => rw [lvlOf_def]; rfl
  | hrel r v => rw [lvlOf_def]; rfl
  | hnrel r v => rw [lvlOf_def]; rfl
  | hand φ ψ ihφ ihψ => simp [LogicalConnective.HomClass.map_and, lvlOf_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [LogicalConnective.HomClass.map_or, lvlOf_or, ihφ, ihψ]
  | hall φ ih => simp [Semiformula.lMap_all, lvlOf_all, ih]
  | hexs φ ih => simp [Semiformula.lMap_exs, lvlOf_exs, ih]

/-- **`lvlOf` does not see a universal closure.**  `∀¹*` peels one `∀¹` at a
time (`allClosure_succ`), and `lvlOf_all` does not move the level either. -/
theorem lvlOf_allClosure : ∀ {n : ℕ} (φ : Semiformula LRA ℕ n), lvlOf (∀¹* φ) = lvlOf φ
  | 0, φ => rfl
  | n + 1, φ => by rw [allClosure_succ, lvlOf_allClosure (∀¹ φ), lvlOf_all]

/-- The guard is levelless. -/
@[simp] theorem lvlOf_guardR (μ : Lv) (A : Semiformula LRA ℕ 1) : lvlOf (guardR μ A) = 0 :=
  lvlOf_lMap_toLRA _

theorem lvlOf_instA (A : Semiformula LRA ℕ 1) : lvlOf (instA A) = lvlOf A := lvlOf_rew _ A

/-- **The level of a naming axiom is its level**, for a body of that shape. -/
@[simp] theorem lvlOf_nameOutP {μ : Lv} {A : Semiformula LRA ℕ 1} (hA : Shape μ A) :
    lvlOf (nameOutP μ A) = μ := by
  rw [nameOutP, lvlOf_allClosure, nameOutMat, lvlOf_or, lvlOf_neg, lvlOf_guardR, lvlOf_all,
    lvlOf_or, lvlOf_nmemAt, lvlOf_instA, max_eq_left (lvlOf_le_of_shape hA)]
  exact max_eq_right (Gamma0Note.zero_le_note μ)

@[simp] theorem lvlOf_nameInP {μ : Lv} {A : Semiformula LRA ℕ 1} (hA : Shape μ A) :
    lvlOf (nameInP μ A) = μ := by
  rw [nameInP, lvlOf_allClosure, nameInMat, lvlOf_or, lvlOf_neg, lvlOf_guardR, lvlOf_all,
    lvlOf_or, lvlOf_neg, lvlOf_memAt, lvlOf_instA, max_eq_right (lvlOf_le_of_shape hA)]
  exact max_eq_right (Gamma0Note.zero_le_note μ)

/-- **The naming schema at the levels `Λ`.**  An *external* schema: one pair of
instances per positive level `μ ∈ Λ` and per formula `A` of shape `μ`,
universally closed into sentences. -/
def NamingAxioms (Λ : Set Lv) : Theory LRA :=
  { σ | ∃ (μ : Lv) (A : Semiformula LRA ℕ 1), μ ∈ Λ ∧ 0 < μ ∧ Shape μ A ∧
      (σ = Semiformula.univCl (nameOutP μ A) ∨ σ = Semiformula.univCl (nameInP μ A)) }

theorem mem_NamingAxioms_out {Λ : Set Lv} {μ : Lv} {A : Semiformula LRA ℕ 1} (hμ : μ ∈ Λ)
    (h0 : 0 < μ) (hA : Shape μ A) : Semiformula.univCl (nameOutP μ A) ∈ NamingAxioms Λ :=
  ⟨μ, A, hμ, h0, hA, Or.inl rfl⟩

theorem mem_NamingAxioms_in {Λ : Set Lv} {μ : Lv} {A : Semiformula LRA ℕ 1} (hμ : μ ∈ Λ)
    (h0 : 0 < μ) (hA : Shape μ A) : Semiformula.univCl (nameInP μ A) ∈ NamingAxioms Λ :=
  ⟨μ, A, hμ, h0, hA, Or.inr rfl⟩

/-- The schema is monotone in the set of levels. -/
theorem NamingAxioms_subset {Λ Λ' : Set Lv} (h : Λ ⊆ Λ') :
    NamingAxioms Λ ⊆ NamingAxioms Λ' := by
  rintro σ ⟨μ, A, hμ, h0, hA, hσ⟩
  exact ⟨μ, A, h hμ, h0, hA, hσ⟩

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

theorem nameOutP_mem_RA {μ : Lv} {A : Semiformula LRA ℕ 1} (hμ : μ ∈ Λ) (h0 : 0 < μ)
    (hA : Shape μ A) : Semiformula.univCl (nameOutP μ A) ∈ RA Λ :=
  mem_RA_of_mem_naming (mem_NamingAxioms_out hμ h0 hA)

theorem nameInP_mem_RA {μ : Lv} {A : Semiformula LRA ℕ 1} (hμ : μ ∈ Λ) (h0 : 0 < μ)
    (hA : Shape μ A) : Semiformula.univCl (nameInP μ A) ∈ RA Λ :=
  mem_RA_of_mem_naming (mem_NamingAxioms_in hμ h0 hA)

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

/-! ### The level bound the guard buys

The reason the guard exists: every axiom of `RAlt ν` (for `ν ≥ 1`) has level
`< ν`.  `Ramified/Axioms.lean` turns this into the rank bound
`rank_evR_emb_lt_of_mem_RAlt` via `Rank.rank_lt_block_of_level`. -/

/-- **Every axiom of `RAlt ν` has level below `ν`.**  One case per block: the
equality axioms carry the bound in their definition, `PA⁻` is levelless
(`lvlOf_lMap_toLRA`, using `ν ≥ 1`), the induction scheme carries the bound in
its side condition (via `lvlOf_emb_univCl` and `lvlOf_succInd`), and the naming
schema carries it in its level `μ ∈ {μ | μ < ν}` (via `lvlOf_emb_univCl` and
`lvlOf_nameOutP`/`lvlOf_nameInP`). -/
theorem lvlOf_emb_lt_of_mem_RAlt {ν : Lv} (hν : 1 ≤ ν) {σ : Sentence LRA} (h : σ ∈ RAlt ν) :
    lvlOf (Rewriting.emb σ : Proposition LRA) < ν := by
  rcases h with ⟨-, hlvl⟩ | h | ⟨φ, hφ, rfl⟩ | h
  · exact hlvl
  · obtain ⟨τ, -, rfl⟩ := h
    rw [← Semiformula.lMap_emb, lvlOf_lMap_toLRA]
    exact lt_of_lt_of_le Gamma0Note.zero_lt_one hν
  · rw [lvlOf_emb_univCl, lvlOf_succInd]
    exact hφ
  · obtain ⟨μ, A, hlt, -, hA, rfl | rfl⟩ := h
    · rw [lvlOf_emb_univCl, lvlOf_nameOutP hA]; exact hlt
    · rw [lvlOf_emb_univCl, lvlOf_nameInP hA]; exact hlt

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
