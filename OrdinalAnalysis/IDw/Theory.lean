/-
  The theory `IDw A` of ID_ω: ONE binary inductively defined predicate `J(y, x)` ("`x`
  is in the `y`-th inductive set"), governed by a SINGLE operator form applied uniformly
  at every level `y : ℕ`, with lower levels appearing (in either polarity) as a genuine
  binary predicate `J^{≺y}` guarded structurally by `· < y`.

  This generalises `IDn/Theory.lean` (a FAMILY `I_0, I_1, …` of unary predicates, one
  operator form per level, `LevelBounded` a syntactic side condition) to the UNIFORM
  formulation of Pohlers 1998 p.270, Buchholz 1987 p.144, Buchholz-Pohlers 1978 p.121: a
  single binary `J`, a single schema `A(x, y)` used at every level, and `∀y`-quantified
  closure/induction axioms. See the design notes
  for the design record; `OrdinalAnalysis.IDw.Sound` for the standard-model soundness.

  **Why binary, why uniform (not a family).** A unary `I_ω` whose defining form mentions
  "all `I_k`" is not first-order (a formula names finitely many symbols); the honest way
  to quantify over "the lower levels" inside a single formula is a genuine object-level
  binary predicate `J(y, x)`, with `y` itself a bound variable of the axiom, not a Lean-side
  index. This is *strictly stronger* than `IDn.IDlt` (`ID_{<ω}`, ψ₀(Ω_ω)): the uniformity
  lets full induction run over the whole `J`-relation at once (`|ID_ω| = ψ₀(ε_{Ω_ω+1})`).

  **The schema language `LForm := ℒₒᵣ + {P : Rel 1} + {Q : Rel 2}`.** A *form* is
  `A : Semisentence LForm 2`, Pohlers' `A(X, Y, x, y)` with the free predicate `X` dropped
  (it stays available in the object language `LXJ` for later embedding work, just not
  inside operator forms — matching how `X` is already ambient, not axiom-facing, in
  ID1/IDn) and `(X-slot, Y-slot)` renamed `(P, Q)`: `P` is the level's own place (to
  become `J(y, ·)` at closure, or an arbitrary `F(y, ·)` at induction), `Q` is "the lower
  levels", read *structurally* as `Q(z, a) ↦ z < y ∧ J(z, a)` wherever it is compiled into
  `LXJ` (`AAt`) — so a use of `Q` is automatically confined to `z < y` by the substitution
  itself, with no syntactic "`LevelBounded`" side condition to state or discharge (see
  `Sound.agreeBelowJ`, which replaces `IDn.levelBounded_agree` with an unconditional
  theorem instead of a hypothesis-dependent one).

  **Lean bound-variable convention** (fixed once, used consistently in `Sound`/`SlotCheck`
  too): in `A : Semisentence LForm 2`, `#0` is `x` (the object argument), `#1` is `y` (the
  level) — chosen so `∀¹ (∀¹ body)` reads outer-to-inner as `∀y ∀x body`, matching
  `Semiformula.eval_all`'s convention that crossing one quantifier shifts existing bound
  references up by one (the *outer* `∀¹` binds the *second* index of a 2-var body). This
  is the reverse of the design memo's prose order ("free `y`, `x`"), which names
  mathematical variables, not raw de Bruijn indices.

  **Positivity.** `PositiveP A`: `P` occurs only positively. `Q` is UNRESTRICTED in either
  polarity — this is exactly what separates ID_ω from the weaker "W-ID_ω" (Pohlers Fig. 1,
  ψ₀(Ω_ω·ε₀)): (P.2) below must hold for every `LXJ`-formula `F`, with no constraint on how
  `Q` occurs in `A`.

  **The two axioms of `IDw A`.**

    * **Closure** (`closureAxJ A`): `∀y ∀x (A_y(J(y,·), x) → J(y, x))`, i.e. `A` with `P`
      read as `J(y, ·)` and `Q` read as `J^{≺y}`.
    * **Induction** (`indAxJ A F`, for every `F : Semiformula LXJ ℕ 2`, `F` allowed to
      depend on `y` too): `∀y (∀x (A_y(F, x) → F(y,x)) → ∀x (J(y,x) → F(y,x)))`.

  `AAt F Y φ` compiles an `LForm`-formula `φ` into `LXJ`, given the "own-place" formula `F`
  and a term `Y` standing for the current level: `P(t) ↦ F/[t, Y]` (Foundation's 2-ary
  `substs`, i.e. `/[t, Y]` notation — shift-safe by construction since `F` is a *fixed*
  2-slot formula substituted afresh at every occurrence, generalising `IDn.substIAt`'s
  `F/[v 0]` from 1 to 2 slots), `Q(s,t) ↦ (s < Y) ∧ J(s,t)`, arithmetic atoms copied via
  `termCast := Semiterm.lMap homLFormLXJ` — *not* a bare cast: `LForm` and `LXJ` have
  definitionally equal `Func` components (`Language.add`'s `Func` field is `L₁.Func ⊕
  L₂.Func`, and both schema languages contribute `Func := fun _ => PEmpty`), but they are
  *not* themselves definitionally equal as `Language` values (their `Rel` components,
  `{P,Q}` vs `{X,J}`, genuinely differ), so `Semiterm LForm ξ n` and `Semiterm LXJ ξ n` are
  different types and a direct `cast`/`rfl` fails; `Semiterm.lMap` along an explicit
  `Language.Hom` (whose `rel` field is an arbitrary well-typed filler, `P ↦ X`, `Q ↦ J`,
  never read by `lMap` on terms) is the honest translation. `Y` is threaded explicitly
  through the recursion and bumped by `Rew.bShift` under `A`'s own internal quantifiers;
  `Semiterm.val_bShift` (library `@[simp]`) is what makes this track the same semantic
  level throughout.

  Contents.

    `XJRel`, `XJLang`, `LXJ`, `toLXJ`, `Xat`, `Jat`             the object language
    `PQRel`, `PQLang`, `LForm`, `Pat`, `Qat`, `FormJ`           the schema language
    `PositiveP`                                                 the one side condition
    `termCast`                                                  `LForm`-term ↦ `LXJ`-term
    `AAt`                                                       `A` compiled at level `Y`, own place `F`
    `closureAxJ`, `indAxJ`                                      the two axioms
    `paLXJ`, `IDw`                                              the theory, with membership lemmas
-/
import Foundation.FirstOrder.Arithmetic.Schemata

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### The object language `LXJ` -/

/-- The relation symbols of `LXJ`: the free predicate `X`, and the one binary inductively
defined predicate `J`. -/
inductive XJRel : ℕ → Type
  | X : XJRel 1
  | J : XJRel 2

/-- The fresh part of `LXJ`: no function symbols. -/
abbrev XJLang : Language where
  Func := fun _ => PEmpty
  Rel := XJRel

/-- Arithmetic together with the free predicate `X` and the binary predicate `J`. -/
abbrev LXJ : Language := Language.add ℒₒᵣ XJLang

instance : Language.ORing LXJ where
  eq := Sum.inl Language.Eq.eq
  lt := Sum.inl Language.LT.lt
  zero := Sum.inl Language.Zero.zero
  one := Sum.inl Language.One.one
  add := Sum.inl Language.Add.add
  mul := Sum.inl Language.Mul.mul

/-- The embedding of arithmetic into `LXJ`. -/
abbrev toLXJ : ℒₒᵣ →ᵥ LXJ := Language.Hom.add₁ ℒₒᵣ XJLang

variable {ξ : Type*} {n : ℕ}

/-- `X(t)`. -/
def Xat (t : Semiterm LXJ ξ n) : Semiformula LXJ ξ n :=
  Semiformula.rel (Sum.inr XJRel.X) ![t]

/-- `J(s, t)`: "`t` is in the `s`-th inductive set". -/
def Jat (s t : Semiterm LXJ ξ n) : Semiformula LXJ ξ n :=
  Semiformula.rel (Sum.inr XJRel.J) ![s, t]

/-- `s < t`, for any `ORing` language (used both in `LXJ` and, via the same definition
shape, left generic here for reuse). -/
def ltAt (s t : Semiterm LXJ ξ n) : Semiformula LXJ ξ n :=
  Semiformula.rel Language.LT.lt ![s, t]

/-! ### The schema language `LForm` -/

/-- The relation symbols of `LForm`: `P` (the level's own place, positivity-restricted) and
`Q` (the lower levels, unrestricted). No `X`: forms may not mention the free predicate
directly (it stays available in `LXJ` itself, for later embedding work). -/
inductive PQRel : ℕ → Type
  | P : PQRel 1
  | Q : PQRel 2

/-- The fresh part of `LForm`: no function symbols (the same shape as `XJLang` — both
contribute `Func := fun _ => PEmpty` — so `LForm` and `LXJ` agree on `Func`, though not as
whole `Language` values; see `termCast`). -/
abbrev PQLang : Language where
  Func := fun _ => PEmpty
  Rel := PQRel

/-- Arithmetic together with the schema predicates `P`, `Q`. -/
abbrev LForm : Language := Language.add ℒₒᵣ PQLang

instance : Language.ORing LForm where
  eq := Sum.inl Language.Eq.eq
  lt := Sum.inl Language.LT.lt
  zero := Sum.inl Language.Zero.zero
  one := Sum.inl Language.One.one
  add := Sum.inl Language.Add.add
  mul := Sum.inl Language.Mul.mul

/-- `P(t)`. -/
def Pat (t : Semiterm LForm ξ n) : Semiformula LForm ξ n :=
  Semiformula.rel (Sum.inr PQRel.P) ![t]

/-- `Q(s, t)`. -/
def Qat (s t : Semiterm LForm ξ n) : Semiformula LForm ξ n :=
  Semiformula.rel (Sum.inr PQRel.Q) ![s, t]

/-- **A form**: `A(x, y)`, `#0 = x` the object argument, `#1 = y` the level (see the file
header for the bound-variable convention). -/
abbrev FormJ := Semisentence LForm 2

/-! ### Positivity in `P` -/

/-- **`P` occurs only positively.** `Q` is unrestricted (either polarity) — the feature
that makes this ID_ω rather than the weaker "W-ID_ω". -/
def PositiveP : {n : ℕ} → Semiformula LForm ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel _ _ => True
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr PQRel.Q) _ => True
  | _, .nrel (Sum.inr PQRel.P) _ => False
  | _, .and φ ψ => PositiveP φ ∧ PositiveP ψ
  | _, .or φ ψ => PositiveP φ ∧ PositiveP ψ
  | _, .all φ => PositiveP φ
  | _, .exs φ => PositiveP φ

section Positive

@[simp] theorem positiveP_verum : PositiveP (⊤ : Semiformula LForm ξ n) := trivial

@[simp] theorem positiveP_falsum : PositiveP (⊥ : Semiformula LForm ξ n) := trivial

@[simp] theorem positiveP_and (φ ψ : Semiformula LForm ξ n) :
    PositiveP (φ ⋏ ψ) ↔ PositiveP φ ∧ PositiveP ψ := Iff.rfl

@[simp] theorem positiveP_or (φ ψ : Semiformula LForm ξ n) :
    PositiveP (φ ⋎ ψ) ↔ PositiveP φ ∧ PositiveP ψ := Iff.rfl

@[simp] theorem positiveP_all (φ : Semiformula LForm ξ (n + 1)) :
    PositiveP (∀¹ φ) ↔ PositiveP φ := Iff.rfl

@[simp] theorem positiveP_exs (φ : Semiformula LForm ξ (n + 1)) :
    PositiveP (∃¹ φ) ↔ PositiveP φ := Iff.rfl

theorem positiveP_Pat (t : Semiterm LForm ξ n) : PositiveP (Pat t) := trivial

theorem positiveP_Qat (s t : Semiterm LForm ξ n) : PositiveP (Qat s t) := trivial

theorem positiveP_neg_Qat (s t : Semiterm LForm ξ n) : PositiveP (∼(Qat s t)) := trivial

end Positive

/-! ### Casting an `LForm`-term into `LXJ` -/

/-- **The `Func`-level identification of `LForm` with `LXJ`**: both `PQLang` and `XJLang`
contribute `Func := fun _ => PEmpty`, so `Language.add`'s `Func` field (`L₁.Func ⊕ L₂.Func`)
agrees definitionally between `LForm` and `LXJ` (the two languages differ only in `Rel`,
`{P,Q}` vs `{X,J}`, which a term never touches). The `rel` component is an arbitrary
well-typed choice, `P ↦ X`, `Q ↦ J` — never invoked by `Semiterm.lMap`, which only reads
`func`. -/
def homLFormLXJ : LForm →ᵥ LXJ where
  func := fun f => f
  rel := fun
    | Sum.inl r => Sum.inl r
    | Sum.inr PQRel.P => Sum.inr XJRel.X
    | Sum.inr PQRel.Q => Sum.inr XJRel.J

/-- An `LForm`-term cast into `LXJ`, via `homLFormLXJ` (only its `func` part matters). -/
def termCast {n : ℕ} (t : Semiterm LForm ξ n) : Semiterm LXJ ξ n :=
  Semiterm.lMap homLFormLXJ t

/-! ### Compiling a form at a level -/

/-- **`AAt F Y φ`**: `φ` (a subformula of a form `A`) compiled into `LXJ`, with `P(t)`
read as `F(t, Y)` (Foundation's `/[·,·]` substitution — shift-safe, `F` is a fixed 2-slot
formula substituted afresh at every occurrence) and `Q(s,t)` read as `s < Y ∧ J(s,t)` —
structurally confined to `s < Y`, no separate boundedness side condition needed. `Y` is
bumped by `Rew.bShift` under `φ`'s own quantifiers, tracking the same semantic level
throughout (`Semiterm.val_bShift`). Generalises `IDn.substIAt`/`IDn.opAt` (one relation,
same language) to two relations, a cross-language compile, and a threaded level term. -/
def AAt {ξ : Type*} (F : Semiformula LXJ ξ 2) :
    {n : ℕ} → Semiterm LXJ ξ n → Semiformula LForm ξ n → Semiformula LXJ ξ n
  | _, _, .verum => ⊤
  | _, _, .falsum => ⊥
  | _, _, .rel (Sum.inl r) v => .rel (Sum.inl r) (fun i => termCast (v i))
  | _, Y, .rel (Sum.inr PQRel.P) v => F/[termCast (v 0), Y]
  | _, Y, .rel (Sum.inr PQRel.Q) v =>
      ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1))
  | _, _, .nrel (Sum.inl r) v => .nrel (Sum.inl r) (fun i => termCast (v i))
  | _, Y, .nrel (Sum.inr PQRel.P) v => ∼(F/[termCast (v 0), Y])
  | _, Y, .nrel (Sum.inr PQRel.Q) v =>
      ∼(ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1)))
  | _, Y, .and φ ψ => AAt F Y φ ⋏ AAt F Y ψ
  | _, Y, .or φ ψ => AAt F Y φ ⋎ AAt F Y ψ
  | _, Y, .all φ => ∀¹ AAt F (Rew.bShift Y) φ
  | _, Y, .exs φ => ∃¹ AAt F (Rew.bShift Y) φ

/-! ### The two axioms -/

/-- **Closure**: `∀y ∀x (A_y(J(y,·), x) → J(y, x))`. Kept at `ξ = Empty` throughout (`A`
already lives there, and `Jat #1 #0` mentions no parameters), so no `univCl` is needed. -/
def closureAxJ (A : FormJ) : Sentence LXJ :=
  ∀¹ (∀¹ (AAt (ξ := Empty) (Jat #1 #0) #1 A 🡒 Jat #1 #0))

/-- **Induction**, at the formula `F` (allowed to depend on `y` too):
`∀y (∀x (A_y(F,x) → F(y,x)) → ∀x (J(y,x) → F(y,x)))`, universal closure over `F`'s own
extra parameters. -/
def indAxJ (A : FormJ) (F : Semiformula LXJ ℕ 2) : Sentence LXJ :=
  Semiformula.univCl
    (∀¹ ((∀¹ (AAt F #1 (Rewriting.emb A) 🡒 F)) 🡒 (∀¹ (Jat #1 #0 🡒 F))))

/-! ### The theory -/

/-- `PA` in the language `LXJ`. -/
def paLXJ : Theory LXJ :=
  𝗘𝗤 LXJ ∪ (Theory.lMap toLXJ 𝗣𝗔⁻ ∪ InductionScheme LXJ Set.univ)

set_option linter.dupNamespace false in
/-- **`IDw A`**: `PA` for `LXJ`, the closure axiom, and every instance of the induction
scheme. No positivity hypothesis is needed to *state* the theory — `PositiveP` is exactly
what `Sound.lean`'s standard model needs. -/
def IDw (A : FormJ) : Theory LXJ :=
  insert (closureAxJ A) (paLXJ ∪ Set.range (indAxJ A))

section Membership

variable (A : FormJ)

theorem paLXJ_subset_IDw : paLXJ ⊆ IDw A := fun _ h => Or.inr (Or.inl h)

theorem closureAxJ_mem_IDw : closureAxJ A ∈ IDw A := Set.mem_insert _ _

theorem indAxJ_mem_IDw (F : Semiformula LXJ ℕ 2) : indAxJ A F ∈ IDw A :=
  Or.inr (Or.inr ⟨F, rfl⟩)

theorem mem_IDw {σ : Sentence LXJ} :
    σ ∈ IDw A ↔ σ = closureAxJ A ∨ σ ∈ paLXJ ∨ ∃ F, indAxJ A F = σ :=
  Iff.rfl

instance paLXJ_weakerThan_IDw : paLXJ ⪯ IDw A :=
  Entailment.WeakerThan.ofSubset (paLXJ_subset_IDw A)

end Membership

end IDw

end OrdinalAnalysis
