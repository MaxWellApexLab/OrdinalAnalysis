/-
  The level of a formula, and the external Gödel coding of predicators (D2).

  Two things live here, and the first is the reason the second is cheap.

  * **`lvlOf`** — the level of a formula: the largest level carried by any of its
    set atoms, `0` if it has none.  Because D2 puts the level on the *relation
    symbol* (`Ramified/Language.lean`), this is a plain structural recursion, and
    — the point of §2 of the design note — it is invariant under substitution of
    terms (`lvlOf_rew`, `lvlOf_subst₁`) and under negation (`lvlOf_neg`).  In the
    untagged design §2 rejects, the corresponding quantity is a *depth*, and
    substitution adds depths; here nothing a substitution does to terms can reach
    a relation symbol, so there is nothing to add.

  * **the coding** — a predicator of level `ν` is a number `a = ⟨ν, ⌜A⌝⟩` with `A`
    a one-variable `LRA`-formula all of whose set atoms have level `< ν`.
    `lvl a` reads the first component, `body a` decodes the second (Foundation's
    `Semiformula.encodable`, `FirstOrder/Basic/Coding.lean:161`), and `Good a`
    says the second component decodes *and* the level condition holds.

  The design note flags the coding as the MED-risk component of D2 ("a new
  component — external Gödel coding with a well-founded level assignment") and
  budgets 700 lines.  The prototype's finding is that the level assignment needs
  no well-founded recursion at all: the invariant

      Good a → lvlOf (body a) < lvl a

  is a *side condition on the code*, not a theorem about a recursion, precisely
  because `lvlOf` does not recurse into codes — it reads symbols.  `good_code`
  shows the condition is not vacuous: every level-correct `A` has a code, and
  that code is `Good` with `body` and `lvl` the ones asked for, so the naming
  axioms of `RA_{<ν}` will have their witnesses.

  What is deliberately *not* here: parameters.  A predicator with parameters is
  `⟨ν, ⌜A⌝, p⃗⟩` and `body` would substitute `p⃗` for extra free variables.  The
  (Pr) rule does not need them — its premise is `body a` with the subject
  substituted — and the prototype's question (does the rank bookkeeping close?)
  does not see them, so they are left to the full development.
-/
import OrdinalAnalysis.Ramified.Language

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder

/-! ### The level of a formula -/

/-- **The level of a formula**: the largest level of a set atom occurring in it,
`0` if there is none.

`0` therefore means "no set atoms, or set atoms only at level `0`".  Both
readings are harmless for the only use, `lvlOf φ < ν`, which in either case says
exactly "every set atom of `φ` has level `< ν`". -/
def lvlOf {n : ℕ} : Semiformula LRA ℕ n → Lv
  |  .rel r _ => (relLevel r).getD 0
  | .nrel r _ => (relLevel r).getD 0
  |         ⊤ => 0
  |         ⊥ => 0
  |     φ ⋏ ψ => max (lvlOf φ) (lvlOf ψ)
  |     φ ⋎ ψ => max (lvlOf φ) (lvlOf ψ)
  |      ∀¹ φ => lvlOf φ
  |      ∃¹ φ => lvlOf φ

section LvlSimp

variable {n : ℕ}

@[simp] theorem lvlOf_rel {k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    lvlOf (.rel r v : Semiformula LRA ℕ n) = (relLevel r).getD 0 := rfl

@[simp] theorem lvlOf_nrel {k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    lvlOf (.nrel r v : Semiformula LRA ℕ n) = (relLevel r).getD 0 := rfl

@[simp] theorem lvlOf_verum : lvlOf (⊤ : Semiformula LRA ℕ n) = 0 := rfl

@[simp] theorem lvlOf_falsum : lvlOf (⊥ : Semiformula LRA ℕ n) = 0 := rfl

@[simp] theorem lvlOf_and (φ ψ : Semiformula LRA ℕ n) :
    lvlOf (φ ⋏ ψ) = max (lvlOf φ) (lvlOf ψ) := rfl

@[simp] theorem lvlOf_or (φ ψ : Semiformula LRA ℕ n) :
    lvlOf (φ ⋎ ψ) = max (lvlOf φ) (lvlOf ψ) := rfl

@[simp] theorem lvlOf_all (φ : Semiformula LRA ℕ (n + 1)) : lvlOf (∀¹ φ) = lvlOf φ := rfl

@[simp] theorem lvlOf_exs (φ : Semiformula LRA ℕ (n + 1)) : lvlOf (∃¹ φ) = lvlOf φ := rfl

/-- A set atom has exactly its own level. -/
@[simp] theorem lvlOf_memAt (ν : Lv) (t s : Semiterm LRA ℕ n) :
    lvlOf (memAt ν t s) = ν := rfl

@[simp] theorem lvlOf_nmemAt (ν : Lv) (t s : Semiterm LRA ℕ n) :
    lvlOf (nmemAt ν t s) = ν := rfl

/-- `X(t)` is levelless. -/
@[simp] theorem lvlOf_Xat (t : Semiterm LRA ℕ n) : lvlOf (Xat t) = 0 := rfl

end LvlSimp

/-- The level does not see negation: negating an atom keeps its relation symbol,
and the level lives on the symbol. -/
@[simp] theorem lvlOf_neg {n : ℕ} (φ : Semiformula LRA ℕ n) : lvlOf (∼φ) = lvlOf φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **The level does not see rewriting.**  This is the §2 property that untagged
syntax cannot have: substituting terms — including substituting a *whole coded
predicator's numeral* for a variable — cannot move a level. -/
@[simp] theorem lvlOf_rew {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (φ : Semiformula LRA ℕ n₁) :
    lvlOf (ω ▹ φ) = lvlOf φ := by
  induction φ using Semiformula.rec' generalizing n₂ <;> simp [*]

/-- The one-point substitution of a term, the form the (Pr) rule uses. -/
@[simp] theorem lvlOf_subst₁ {n : ℕ} (φ : Semiformula LRA ℕ 1) (t : Semiterm LRA ℕ n) :
    lvlOf (φ/[t]) = lvlOf φ := lvlOf_rew _ φ

/-! ### The coding

`a = ⟨ν, ⌜A⌝⟩`, a `Nat.pair`.  The decoding is Foundation's, which is why
`Ramified/Language.lean` had to supply the `Encodable` instances for `LRA`. -/

/-- The level of a code. -/
def lvl (a : ℕ) : Lv := a.unpair.1

/-- The body of a code, if the code is well formed. -/
def bodyOpt (a : ℕ) : Option (Semiformula LRA ℕ 1) := Encodable.decode a.unpair.2

/-- **The body of a code**, made total by sending a malformed code to `⊤`.

Totality costs nothing: `Good` rules the junk codes out, and every statement
below is under `Good`. -/
def body (a : ℕ) : Semiformula LRA ℕ 1 := (bodyOpt a).getD ⊤

/-- **`a` is a well-formed predicator code**: its second component decodes to a
formula, and that formula's set atoms all sit strictly below the code's own
level.

The second conjunct is the *ramification condition*.  It is what makes the (Pr)
rule rank-decreasing, hence what makes the (Pr)/(Pr) cut reduce. -/
def Good (a : ℕ) : Prop := (bodyOpt a).isSome = true ∧ lvlOf (body a) < lvl a

/-- **The coding invariant.**  A level-`ν` code's body has all its set atoms
strictly below `ν`. -/
theorem good_body_lvl {a : ℕ} (h : Good a) : lvlOf (body a) < lvl a := h.2

/-- A `Good` code has positive level: there is no level-`0` predicator, because
nothing is strictly below `0`. -/
theorem good_lvl_pos {a : ℕ} (h : Good a) : 0 < lvl a :=
  lt_of_le_of_lt (Nat.zero_le _) h.2

/-! ### Codes exist

`good_code` is the half the axioms of `RA_{<ν}` consume: every level-correct
formula is named by a code whose `body` and `lvl` are the ones asked for.  It is
also what shows `Good` is not vacuously satisfiable-free. -/

/-- The canonical code of the level-`ν` predicator `A`. -/
def code (ν : Lv) (A : Semiformula LRA ℕ 1) : ℕ := Nat.pair ν (Encodable.encode A)

@[simp] theorem lvl_code (ν : Lv) (A : Semiformula LRA ℕ 1) : lvl (code ν A) = ν := by
  simp [lvl, code]

@[simp] theorem bodyOpt_code (ν : Lv) (A : Semiformula LRA ℕ 1) :
    bodyOpt (code ν A) = some A := by
  simp [bodyOpt, code, Encodable.encodek]

@[simp] theorem body_code (ν : Lv) (A : Semiformula LRA ℕ 1) : body (code ν A) = A := by
  simp [body]

/-- **Every level-correct formula has a `Good` code.** -/
theorem good_code {ν : Lv} {A : Semiformula LRA ℕ 1} (h : lvlOf A < ν) : Good (code ν A) := by
  refine ⟨?_, ?_⟩ <;> simp [h]

/-- A `Good` code of level `ν` whose body is `A`, for every level-correct `A` —
the form the naming axioms want. -/
theorem exists_good_code {ν : Lv} {A : Semiformula LRA ℕ 1} (h : lvlOf A < ν) :
    ∃ a : ℕ, Good a ∧ lvl a = ν ∧ body a = A :=
  ⟨code ν A, good_code h, lvl_code ν A, body_code ν A⟩

end Ramified

end OrdinalAnalysis
