/-
  The level of a formula, and the external Gödel coding of predicators (D2).

  Two things live here, and the first is the reason the second is cheap.

  * **`lvlOf`** — the level of a formula: the largest level carried by any of its
    set atoms, `0` if it has none.  Because D2 puts the level on the *relation
    symbol* (`Ramified/Language.lean`), this is a plain structural recursion, and
    it is invariant under substitution of terms (`lvlOf_rew`, `lvlOf_subst₁`) and
    under negation (`lvlOf_neg`): nothing a substitution does to terms can reach
    a relation symbol.

  * **the coding** — a predicator of level `μ` is a number

        a = ⟨μ, s, e, p⟩        (nested `Nat.pair`)

    with `μ = lvl a` its level, `s = stage a` its *stage*, `e` the Gödel number
    of a formula `A = formula a : Semiformula LRA ℕ 1` (Foundation's
    `Semiformula.encodable`), and `p = param a` a **parameter**.  The subject of
    `A` is the bound variable `#0`; its parameter is the free variable `&0`.  The
    set named by `a` is `{x | A(x, p)}`: `body a` is `A` with every free
    variable replaced by the numeral `p̄`.

  ## Why a parameter of the same level

  With parameter-free codes whose bodies mention only strictly lower levels,
  every proof in the finitary theory uses finitely many codes, and the level-`μ`
  sets it sees can be read, level by level, as explicit formulas of `PA[X]`:
  such a theory is conservative over `PA[X]`, whatever the number of levels.
  What breaks this is comprehension with a set parameter *of the same level*,
  e.g. closure of level `μ` under the jump,

      ∀z ∃w ∀x (x ∈̇_μ w ↔ J(x, z))       with `z` of level `μ`.

  So a level-`μ` body may mention level-`μ` sets — but only through its
  parameter.  `Shape μ A` is that restriction: every level-`μ` atom of `A` is
  literally `t ∈̇_μ &0` or `t ∉̇_μ &0` (the set argument *is* the parameter, not
  a bound variable, not a term built from it), no atom has level `> μ`, and
  lower levels are unrestricted.

  ## Why a stage

  An unrestricted numeric parameter makes the naming schema inconsistent:
  `A(x, p) :≡ x ∉̇_μ ⟨p, p⟩` would name, at `c = ⟨⌜A⌝, ⌜A⌝⟩`, a set with
  `x ∈̇_μ c ↔ x ∉̇_μ c`.  The stage is the well-founded measure that rules this
  out: a code is `Good` only if

      A.complexity + stage p < s,

  so a level-`μ` set is defined from a level-`μ` parameter of strictly smaller
  stage, and the membership of a code is determined by recursion on (level,
  stage).  The same inequality is what makes the predicator rule (Pr) of
  `Ramified/Calculus.lean` lower the cut rank: `Ramified/Rank.lean` prices a
  ground level-`μ` atom at `ω·(μ−1) ⊕ stage`, and the unfolding of `a` has rank
  at most `ω·(μ−1) ⊕ (stage p + A.complexity) < ω·(μ−1) ⊕ s`.

  The invariant the rest of the development reads off a `Good` code is therefore

      Good a → lvlOf (body a) ≤ lvl a      (`good_body_lvl`)

  with the level-`lvl a` atoms of `body a` exactly the parameter atoms
  `t ∈̇_{lvl a} p̄`.  The parameter-free codes of level `μ` over a formula of
  level `< μ` are the special case `p = 0` (`code`, `good_code`).
-/
import OrdinalAnalysis.Ramified.Ground

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

/-- **The level does not see rewriting.**  Substituting terms — including
substituting a *whole coded predicator's numeral* for a variable — cannot move a
level. -/
@[simp] theorem lvlOf_rew {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (φ : Semiformula LRA ℕ n₁) :
    lvlOf (ω ▹ φ) = lvlOf φ := by
  induction φ using Semiformula.rec' generalizing n₂ <;> simp [*]

/-- The one-point substitution of a term, the form the (Pr) rule uses. -/
@[simp] theorem lvlOf_subst₁ {n : ℕ} (φ : Semiformula LRA ℕ 1) (t : Semiterm LRA ℕ n) :
    lvlOf (φ/[t]) = lvlOf φ := lvlOf_rew _ φ

/-! ### The shape of a level-`μ` body

A level-`μ` atom may occur only with the parameter `&0` as its set argument. -/

/-- The shape condition on one atom: a levelless symbol is unrestricted, a set
atom of level `κ` must have `κ < μ`, or `κ = μ` and set argument `&0`. -/
def AtomShape (μ : Lv) : {k : ℕ} → LRA.Rel k → {n : ℕ} → (Fin k → Semiterm LRA ℕ n) → Prop
  | _, Sum.inl _, _, _ => True
  | _, Sum.inr RARel.X, _, _ => True
  | _, Sum.inr (RARel.mem κ), _, v => κ < μ ∨ (κ = μ ∧ v 1 = &0)

/-- **`Shape μ A`**: every set atom of `A` has level `< μ`, or level `μ` and the
parameter `&0` as its set argument. -/
def Shape (μ : Lv) {n : ℕ} : Semiformula LRA ℕ n → Prop
  |  .rel r v => AtomShape μ r v
  | .nrel r v => AtomShape μ r v
  |         ⊤ => True
  |         ⊥ => True
  |     φ ⋏ ψ => Shape μ φ ∧ Shape μ ψ
  |     φ ⋎ ψ => Shape μ φ ∧ Shape μ ψ
  |      ∀¹ φ => Shape μ φ
  |      ∃¹ φ => Shape μ φ

section ShapeSimp

variable {μ : Lv} {n : ℕ}

@[simp] theorem shape_rel {k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    Shape μ (.rel r v : Semiformula LRA ℕ n) ↔ AtomShape μ r v := Iff.rfl

@[simp] theorem shape_nrel {k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    Shape μ (.nrel r v : Semiformula LRA ℕ n) ↔ AtomShape μ r v := Iff.rfl

@[simp] theorem shape_verum : Shape μ (⊤ : Semiformula LRA ℕ n) := trivial

@[simp] theorem shape_falsum : Shape μ (⊥ : Semiformula LRA ℕ n) := trivial

@[simp] theorem shape_and (φ ψ : Semiformula LRA ℕ n) :
    Shape μ (φ ⋏ ψ) ↔ Shape μ φ ∧ Shape μ ψ := Iff.rfl

@[simp] theorem shape_or (φ ψ : Semiformula LRA ℕ n) :
    Shape μ (φ ⋎ ψ) ↔ Shape μ φ ∧ Shape μ ψ := Iff.rfl

@[simp] theorem shape_all (φ : Semiformula LRA ℕ (n + 1)) : Shape μ (∀¹ φ) ↔ Shape μ φ :=
  Iff.rfl

@[simp] theorem shape_exs (φ : Semiformula LRA ℕ (n + 1)) : Shape μ (∃¹ φ) ↔ Shape μ φ :=
  Iff.rfl

theorem shape_memAt (κ : Lv) (t s : Semiterm LRA ℕ n) :
    Shape μ (memAt κ t s) ↔ κ < μ ∨ (κ = μ ∧ s = &0) := Iff.rfl

theorem shape_nmemAt (κ : Lv) (t s : Semiterm LRA ℕ n) :
    Shape μ (nmemAt κ t s) ↔ κ < μ ∨ (κ = μ ∧ s = &0) := Iff.rfl

@[simp] theorem shape_Xat (t : Semiterm LRA ℕ n) : Shape μ (Xat t) := trivial

end ShapeSimp

/-- The shape does not see negation. -/
@[simp] theorem shape_neg {μ : Lv} {n : ℕ} (φ : Semiformula LRA ℕ n) :
    Shape μ (∼φ) ↔ Shape μ φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- An atom of the right shape has level at most `μ`. -/
theorem atomShape_level_le {μ : Lv} {k n : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n)
    (h : AtomShape μ r v) : (relLevel r).getD 0 ≤ μ := by
  rcases r with r | r
  · exact Nat.zero_le _
  · cases r with
    | X => exact Nat.zero_le _
    | mem κ =>
        rcases h with h | ⟨rfl, -⟩
        · exact le_of_lt h
        · exact le_rfl

/-- **A body of shape `μ` has level at most `μ`.** -/
theorem lvlOf_le_of_shape {μ : Lv} {n : ℕ} {φ : Semiformula LRA ℕ n} (h : Shape μ φ) :
    lvlOf φ ≤ μ := by
  induction φ using Semiformula.rec' with
  | hverum => exact Nat.zero_le _
  | hfalsum => exact Nat.zero_le _
  | hrel r v => exact atomShape_level_le r v h
  | hnrel r v => exact atomShape_level_le r v h
  | hand φ ψ ihφ ihψ => exact max_le (ihφ h.1) (ihψ h.2)
  | hor φ ψ ihφ ihψ => exact max_le (ihφ h.1) (ihψ h.2)
  | hall φ ih => exact ih h
  | hexs φ ih => exact ih h

/-- An atom of level below `μ` has the right shape, whatever its arguments. -/
theorem atomShape_of_level_lt {μ : Lv} {k n : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n)
    (h : (relLevel r).getD 0 < μ) : AtomShape μ r v := by
  rcases r with r | r
  · trivial
  · cases r with
    | X => trivial
    | mem κ => exact Or.inl h

/-- **A formula strictly below level `μ` has shape `μ`**: the parameter-free
case. -/
theorem shape_of_lvlOf_lt {μ : Lv} {n : ℕ} {φ : Semiformula LRA ℕ n} (h : lvlOf φ < μ) :
    Shape μ φ := by
  induction φ using Semiformula.rec' with
  | hverum => trivial
  | hfalsum => trivial
  | hrel r v => exact atomShape_of_level_lt r v h
  | hnrel r v => exact atomShape_of_level_lt r v h
  | hand φ ψ ihφ ihψ =>
      simp only [lvlOf_and, max_lt_iff] at h
      exact ⟨ihφ h.1, ihψ h.2⟩
  | hor φ ψ ihφ ihψ =>
      simp only [lvlOf_or, max_lt_iff] at h
      exact ⟨ihφ h.1, ihψ h.2⟩
  | hall φ ih => exact ih h
  | hexs φ ih => exact ih h

/-! ### The coding

`a = ⟨μ, s, e, p⟩`, nested `Nat.pair`s.  The decoding of `e` is Foundation's,
which is why `Ramified/Language.lean` had to supply the `Encodable` instances
for `LRA`. -/

/-- The code with level `μ`, stage `s`, formula index `e` and parameter `p`. -/
def mkCode (μ : Lv) (s e p : ℕ) : ℕ := Nat.pair μ (Nat.pair s (Nat.pair e p))

/-- The level of a code. -/
def lvl (a : ℕ) : Lv := a.unpair.1

/-- **The stage of a number**, read as a code: its second field.  Total — every
number has a stage — so that the stage condition can speak about an arbitrary
parameter. -/
def stage (a : ℕ) : ℕ := a.unpair.2.unpair.1

/-- The formula index of a code. -/
def fcode (a : ℕ) : ℕ := a.unpair.2.unpair.2.unpair.1

/-- The parameter of a code. -/
def param (a : ℕ) : ℕ := a.unpair.2.unpair.2.unpair.2

@[simp] theorem lvl_mkCode (μ : Lv) (s e p : ℕ) : lvl (mkCode μ s e p) = μ := by
  simp [lvl, mkCode]

@[simp] theorem stage_mkCode (μ : Lv) (s e p : ℕ) : stage (mkCode μ s e p) = s := by
  simp [stage, mkCode]

@[simp] theorem fcode_mkCode (μ : Lv) (s e p : ℕ) : fcode (mkCode μ s e p) = e := by
  simp [fcode, mkCode]

@[simp] theorem param_mkCode (μ : Lv) (s e p : ℕ) : param (mkCode μ s e p) = p := by
  simp [param, mkCode]

@[simp] theorem stage_zero : stage 0 = 0 := by simp [stage]

/-- Every number is the code of its own fields. -/
theorem mkCode_fields (a : ℕ) : mkCode (lvl a) (stage a) (fcode a) (param a) = a := by
  simp [mkCode, lvl, stage, fcode, param]

/-- The formula of a code, if its index decodes. -/
def formulaOpt (a : ℕ) : Option (Semiformula LRA ℕ 1) := Encodable.decode (fcode a)

/-- **The formula of a code**, made total by sending a malformed index to `⊤`. -/
def formula (a : ℕ) : Semiformula LRA ℕ 1 := (formulaOpt a).getD ⊤

@[simp] theorem formulaOpt_mkCode (μ : Lv) (s p : ℕ) (A : Semiformula LRA ℕ 1) :
    formulaOpt (mkCode μ s (Encodable.encode A) p) = some A := by
  simp [formulaOpt, Encodable.encodek]

@[simp] theorem formula_mkCode (μ : Lv) (s p : ℕ) (A : Semiformula LRA ℕ 1) :
    formula (mkCode μ s (Encodable.encode A) p) = A := by
  simp [formula]

/-- Instantiating the parameter: every free variable becomes the numeral `p̄`. -/
def instParam (p : ℕ) : Rew LRA ℕ 1 ℕ 1 := Rew.rewrite fun _ => numAtR p

@[simp] theorem instParam_fvar (p x : ℕ) : instParam p &x = numAtR p := rfl

@[simp] theorem instParam_bvar (p : ℕ) (i : Fin 1) : instParam p #i = #i := rfl

/-- **The body of a code**: its formula with the parameter instantiated. -/
def body (a : ℕ) : Semiformula LRA ℕ 1 := instParam (param a) ▹ formula a

@[simp] theorem body_mkCode (μ : Lv) (s p : ℕ) (A : Semiformula LRA ℕ 1) :
    body (mkCode μ s (Encodable.encode A) p) = instParam p ▹ A := by
  simp [body]

/-- **`a` is a well-formed predicator code**: its formula index decodes, its
level is positive, its formula has the shape of its level, and the stage
condition holds.

The shape and stage conditions are what make the (Pr) rule rank-decreasing,
hence what makes the (Pr)/(Pr) cut reduce; the stage condition is also what
makes the naming schema consistent. -/
def Good (a : ℕ) : Prop :=
  (formulaOpt a).isSome = true ∧ 0 < lvl a ∧ Shape (lvl a) (formula a) ∧
    (formula a).complexity + stage (param a) < stage a

/-- A `Good` code has positive level: there is no level-`0` predicator. -/
theorem good_lvl_pos {a : ℕ} (h : Good a) : 0 < lvl a := h.2.1

/-- The formula of a `Good` code has the shape of its level. -/
theorem good_shape {a : ℕ} (h : Good a) : Shape (lvl a) (formula a) := h.2.2.1

/-- **The stage condition** of a `Good` code. -/
theorem good_stage {a : ℕ} (h : Good a) :
    (formula a).complexity + stage (param a) < stage a := h.2.2.2

/-- **The coding invariant.**  A level-`μ` code's body has all its set atoms at
levels `≤ μ`; those at level `μ` are the parameter atoms. -/
theorem good_body_lvl {a : ℕ} (h : Good a) : lvlOf (body a) ≤ lvl a := by
  rw [body, lvlOf_rew]
  exact lvlOf_le_of_shape (good_shape h)

/-- **Every formula of the right shape has a `Good` code**, at every parameter
and every stage above the stage condition. -/
theorem good_mkCode {μ : Lv} {s p : ℕ} {A : Semiformula LRA ℕ 1} (h0 : 0 < μ)
    (hA : Shape μ A) (hs : A.complexity + stage p < s) :
    Good (mkCode μ s (Encodable.encode A) p) := by
  refine ⟨by simp, by simpa using h0, by simpa using hA, ?_⟩
  simpa using hs

/-! ### Parameter-free codes

The canonical code of a level-`μ` predicator over a formula of level `< μ`: the
parameter is `0` and the stage is the least the stage condition allows. -/

/-- The canonical parameter-free code of the level-`μ` predicator `A`. -/
def code (μ : Lv) (A : Semiformula LRA ℕ 1) : ℕ :=
  mkCode μ (A.complexity + 1) (Encodable.encode A) 0

@[simp] theorem lvl_code (μ : Lv) (A : Semiformula LRA ℕ 1) : lvl (code μ A) = μ := by
  simp [code]

/-- A closed formula is its own body. -/
theorem body_code {μ : Lv} {A : Semiformula LRA ℕ 1} (h : A.freeVariables = ∅) :
    body (code μ A) = A := by
  rw [code, body_mkCode]
  refine Semiformula.rew_eq_self_of (fun x => rfl) (fun x hx => ?_)
  have hx' : x ∈ A.freeVariables := hx
  rw [h] at hx'
  exact absurd hx' (Finset.notMem_empty x)

/-- **Every level-correct formula has a `Good` parameter-free code.** -/
theorem good_code {μ : Lv} {A : Semiformula LRA ℕ 1} (h : lvlOf A < μ) : Good (code μ A) :=
  good_mkCode (lt_of_le_of_lt (Nat.zero_le _) h) (shape_of_lvlOf_lt h) (by simp)

/-- A `Good` code of level `μ` whose body is `A`, for every closed level-correct
`A` — the parameter-free special case of the coding. -/
theorem exists_good_code {μ : Lv} {A : Semiformula LRA ℕ 1} (h : lvlOf A < μ)
    (hcl : A.freeVariables = ∅) : ∃ a : ℕ, Good a ∧ lvl a = μ ∧ body a = A :=
  ⟨code μ A, good_code h, lvl_code μ A, body_code hcl⟩

end Ramified

end OrdinalAnalysis
