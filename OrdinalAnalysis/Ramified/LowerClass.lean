/-
  The class `Ce` of the boundedness lemma, for the ramified calculus, already
  evaluated.

  This merges `Gentzen/LowerClass.lean` and `Gentzen/LowerClassEv.lean` into
  one file, exactly as `ACAOmega/LowerClass₂.lean` merges the same two
  first-order files for the second-order calculus, and for the same reason:
  `evR` fixes the three atomic shapes `X(n̄)`, `∼X(n̄)`, `∀x X x` on the nose
  (`evR_Xat_num`, `evR_neg_Xat_num`, `evR_allXat` below), so there is no
  ground gained by keeping a "raw" class distinct from its `evR`-image, and
  the induction of `Ramified/Boundedness.lean` — over
  `OmegaDerivableR trueArithLitsR evInstR 0 α Γ`, whose quantifier rules
  instantiate through `evInstR.inst φ n = evR (φ/[n̄])` — only ever meets
  the evaluated shapes.

  The nine shapes are exactly `Gentzen`'s, with `Xat` for `LRA` in place of
  `Xat` for `LX` (D2 keeps the fresh unary predicate for the regression
  test), and one new fact that has no first-order counterpart:

  **no member of the class mentions a level-indexed set atom `∈̇_ν` at all.**
  `SetFree` records this — a formula mentions no `∈̇_ν`, though it may still
  mention `X` — and `inCe_setFree` proves it holds of every member.  This is
  the fact the (Pr)/(Pr⁻) cases of `Ramified/Boundedness.lean` need: the
  conclusion of a (Pr) inference is the bare atom `n̄ ∈̇_ν ā`, and `SetFree`
  applied to `not_inCe_memAt`/`not_inCe_nmemAt` says that atom is never a
  member of the class, so a cut-free derivation of a class sequent can never
  use those rules — the whole point of D2's rank design (`Ramified/Rank.lean`'s
  header).

  The two disjointness facts are proved the same way the first-order ones
  are — `head` (rel/nrel/and/or/all/exs, unchanged: `LRA`'s extra relation
  symbols do not add a new *connective* shape) settles every case except one,
  where a level-indexed atom and `X(n̄)` share the head tag `rel` (both are
  atoms) and must be told apart by which relation symbol they carry.  That
  finer discriminator is `isMemAtom`, defined here from
  `Ramified/Language.lean`'s `relLevel`.

  Everything else — the named members, their substitution normal forms, the
  closure lemmas under premise-formation, the sequent-level forms — is
  `Gentzen/LowerClass.lean` and `Gentzen/LowerClassEv.lean`, symbol for
  symbol, with `LX → LRA`, `numLX → numAtR`, `ev → evR`, `evInst → evInstR`,
  `TrueN → TrueNR`, `TI → TIR`.  Two syntactic traps those two files already
  had to work around apply unchanged to `LRA`: head clashes are decided by a
  numeric tag because `⋏`/`⋎`/`∀¹`/`∃¹` are notation, not constructors, and a
  term containing a fresh relation symbol (`Sum.inr …`) is opaque to
  `rw`/`simp`, so every such fact is proved by a `congrArg`/`show` argument
  instead.
-/
import OrdinalAnalysis.Ramified.CodedOrderR

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/- `numAtR` is a plain `def` (not an `abbrev`), and `numAtR_zero` — the fact
that it agrees with `num` at level `0` — is a `simp` lemma pointed the wrong
way for this file's purposes: it eagerly rewrites every level-`0` `numAtR k`
into `num k`, which then fails to match the many lemmas about `numAtR` used
below.  Turning it off keeps every named shape's numeral spelled `numAtR`
throughout. -/
attribute [-simp] numAtR_zero

variable {O : Type} [LinearOrder O] {C : CodedOrderR O}

/-! ### `SetFree`: no level-indexed set atom

Unlike `XFree` (`Ramified/CodedOrderR.lean`), `SetFree` permits `X` and
excludes only `∈̇_ν`: its atomic clause reads the level off the relation
symbol via `relLevel` (`Ramified/Language.lean`), which is `none` for both
arithmetic and `X` and `some ν` exactly for `∈̇_ν`. -/

/-- `φ` mentions no `∈̇_ν`, for any level `ν`.  It may still mention `X`. -/
def SetFree {n : ℕ} : Semiformula LRA ℕ n → Prop
  |                   ⊤ => True
  |                   ⊥ => True
  |  .rel (arity := _) r _ => relLevel r = none
  | .nrel (arity := _) r _ => relLevel r = none
  |               φ ⋏ ψ => SetFree φ ∧ SetFree ψ
  |               φ ⋎ ψ => SetFree φ ∧ SetFree ψ
  |                ∀¹ φ => SetFree φ
  |                ∃¹ φ => SetFree φ

@[simp] theorem SetFree_verum {n : ℕ} : SetFree (⊤ : Semiformula LRA ℕ n) := trivial

@[simp] theorem SetFree_falsum {n : ℕ} : SetFree (⊥ : Semiformula LRA ℕ n) := trivial

@[simp] theorem SetFree_rel {n k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    SetFree (Semiformula.rel r v) ↔ relLevel r = none := Iff.rfl

@[simp] theorem SetFree_nrel {n k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    SetFree (Semiformula.nrel r v) ↔ relLevel r = none := Iff.rfl

@[simp] theorem SetFree_and {n : ℕ} (φ ψ : Semiformula LRA ℕ n) :
    SetFree (φ ⋏ ψ) ↔ SetFree φ ∧ SetFree ψ := Iff.rfl

@[simp] theorem SetFree_or {n : ℕ} (φ ψ : Semiformula LRA ℕ n) :
    SetFree (φ ⋎ ψ) ↔ SetFree φ ∧ SetFree ψ := Iff.rfl

@[simp] theorem SetFree_all {n : ℕ} (φ : Semiformula LRA ℕ (n + 1)) :
    SetFree (∀¹ φ) ↔ SetFree φ := Iff.rfl

@[simp] theorem SetFree_exs {n : ℕ} (φ : Semiformula LRA ℕ (n + 1)) :
    SetFree (∃¹ φ) ↔ SetFree φ := Iff.rfl

@[simp] theorem SetFree_Xat {n : ℕ} (t : Semiterm LRA ℕ n) : SetFree (Xat t) := rfl

/-- **A level-`ν` set atom is never `SetFree`.** -/
theorem not_SetFree_memAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) : ¬ SetFree (memAt ν t s) :=
  Option.some_ne_none ν

theorem not_SetFree_nmemAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    ¬ SetFree (nmemAt ν t s) :=
  Option.some_ne_none ν

@[simp] theorem SetFree_neg {n : ℕ} (φ : Semiformula LRA ℕ n) : SetFree (∼φ) ↔ SetFree φ := by
  induction φ using Semiformula.rec' <;> simp [*]

@[simp] theorem SetFree_rew {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (φ : Semiformula LRA ℕ n₁) :
    SetFree (ω ▹ φ) ↔ SetFree φ := by
  induction φ using Semiformula.rec' generalizing n₂ <;> simp [*]

/-- **Every `XFree` formula is `SetFree`.**  `XFree`'s atomic clause already
excludes both fresh relation kinds, so this is immediate. -/
theorem SetFree_of_XFree {n : ℕ} : ∀ {φ : Semiformula LRA ℕ n}, XFree φ → SetFree φ := by
  intro φ
  induction φ using Semiformula.rec' with
  | hverum => intro _; trivial
  | hfalsum => intro _; trivial
  | hrel r v => rintro ⟨r', rfl⟩; rfl
  | hnrel r v => rintro ⟨r', rfl⟩; rfl
  | hand φ ψ ihφ ihψ => rintro ⟨hφ, hψ⟩; exact ⟨ihφ hφ, ihψ hψ⟩
  | hor φ ψ ihφ ihψ => rintro ⟨hφ, hψ⟩; exact ⟨ihφ hφ, ihψ hψ⟩
  | hall φ ih => exact ih
  | hexs φ ih => exact ih

/-! ### (a₂) `X`-free and closed

The property the ω-completeness half of the argument consumes, exactly as in
`Gentzen/LowerClass.lean`. -/

/-- `φ` is closed and mentions neither `X` nor any `∈̇_ν`. -/
def IsXFreeClosed (φ : Proposition LRA) : Prop := XFree φ ∧ φ.freeVariables = ∅

theorem IsXFreeClosed.xfree {φ : Proposition LRA} (h : IsXFreeClosed φ) : XFree φ := h.1

theorem IsXFreeClosed.closed {φ : Proposition LRA} (h : IsXFreeClosed φ) :
    φ.freeVariables = ∅ := h.2

theorem IsXFreeClosed.setFree {φ : Proposition LRA} (h : IsXFreeClosed φ) : SetFree φ :=
  SetFree_of_XFree h.1

@[simp] theorem isXFreeClosed_neg {φ : Proposition LRA} :
    IsXFreeClosed (∼φ) ↔ IsXFreeClosed φ := by simp [IsXFreeClosed]

@[simp] theorem isXFreeClosed_or {φ ψ : Proposition LRA} :
    IsXFreeClosed (φ ⋎ ψ) ↔ IsXFreeClosed φ ∧ IsXFreeClosed ψ := by
  simp only [IsXFreeClosed, XFree_or, Semiformula.freeVariables_or, Finset.union_eq_empty]
  tauto

@[simp] theorem isXFreeClosed_and {φ ψ : Proposition LRA} :
    IsXFreeClosed (φ ⋏ ψ) ↔ IsXFreeClosed φ ∧ IsXFreeClosed ψ := by
  simp only [IsXFreeClosed, XFree_and, Semiformula.freeVariables_and, Finset.union_eq_empty]
  tauto

theorem isXFreeClosed_subst_numeral {φ : Semiformula LRA ℕ 1}
    (hx : XFree φ) (hf : φ.freeVariables = ∅) (k : ℕ) :
    IsXFreeClosed (φ/[numAtR k]) := by
  refine ⟨by simpa using hx, ?_⟩
  refine freeVariables_rew_eq_empty' _ hf ?_
  intro i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp only [Rew.subst_bvar, Matrix.cons_val_zero]
  exact freeVariables_of_groundR (groundR_numAtR k)
where
  freeVariables_rew_eq_empty' {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂)
      {φ : Semiformula LRA ℕ n₁} (hφ : φ.freeVariables = ∅)
      (hb : ∀ i : Fin n₁, (ω #i).freeVariables = ∅) : (ω ▹ φ).freeVariables = ∅ := by
    ext x
    simp only [Finset.notMem_empty, iff_false]
    intro hx
    rcases Semiformula.fvar?_rew (ω := ω) (φ := φ) (x := x) hx with ⟨i, hi⟩ | ⟨z, hz, _⟩
    · rw [Semiterm.FVar?, hb i] at hi
      exact Finset.notMem_empty x hi
    · rw [Semiformula.FVar?, hφ] at hz
      exact Finset.notMem_empty z hz

theorem isXFreeClosed_all {φ : Semiformula LRA ℕ 1} (h : IsXFreeClosed (∀¹ φ)) (k : ℕ) :
    IsXFreeClosed (φ/[numAtR k]) :=
  isXFreeClosed_subst_numeral h.1 h.2 k

theorem isXFreeClosed_exs {φ : Semiformula LRA ℕ 1} (h : IsXFreeClosed (∃¹ φ)) (k : ℕ) :
    IsXFreeClosed (φ/[numAtR k]) :=
  isXFreeClosed_subst_numeral h.1 h.2 k

@[simp] theorem not_isXFreeClosed_Xat {t : Semiterm LRA ℕ 0} : ¬ IsXFreeClosed (Xat t) :=
  fun h => not_XFree_Xat t h.1

@[simp] theorem not_isXFreeClosed_neg_Xat {t : Semiterm LRA ℕ 0} :
    ¬ IsXFreeClosed (∼(Xat t)) := by simp

@[simp] theorem not_isXFreeClosed_memAt {ν : Lv} {t s : Semiterm LRA ℕ 0} :
    ¬ IsXFreeClosed (memAt ν t s) := fun h => not_XFree_memAt ν t s h.1

@[simp] theorem not_isXFreeClosed_nmemAt {ν : Lv} {t s : Semiterm LRA ℕ 0} :
    ¬ IsXFreeClosed (nmemAt ν t s) := fun h => not_XFree_nmemAt ν t s h.1

/-! ### Head tags

`⋏`, `⋎`, `∀¹`, `∃¹` are notation, not constructors; a numeric tag reduces
every "these two members cannot be equal" step to arithmetic. -/

/-- The outermost connective of a formula, as a numeric tag. -/
def head {n : ℕ} : Semiformula LRA ℕ n → ℕ
  |        ⊤ => 0
  |        ⊥ => 1
  | .rel _ _ => 2
  | .nrel _ _ => 3
  |    _ ⋏ _ => 4
  |    _ ⋎ _ => 5
  |     ∀¹ _ => 6
  |     ∃¹ _ => 7

@[simp] theorem head_verum {n : ℕ} : head (⊤ : Semiformula LRA ℕ n) = 0 := rfl

@[simp] theorem head_falsum {n : ℕ} : head (⊥ : Semiformula LRA ℕ n) = 1 := rfl

@[simp] theorem head_rel {n k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    head (Semiformula.rel r v) = 2 := rfl

@[simp] theorem head_nrel {n k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    head (Semiformula.nrel r v) = 3 := rfl

@[simp] theorem head_and {n : ℕ} (φ ψ : Semiformula LRA ℕ n) : head (φ ⋏ ψ) = 4 := rfl

@[simp] theorem head_or {n : ℕ} (φ ψ : Semiformula LRA ℕ n) : head (φ ⋎ ψ) = 5 := rfl

@[simp] theorem head_all {n : ℕ} (φ : Semiformula LRA ℕ (n + 1)) : head (∀¹ φ) = 6 := rfl

@[simp] theorem head_exs {n : ℕ} (φ : Semiformula LRA ℕ (n + 1)) : head (∃¹ φ) = 7 := rfl

@[simp] theorem head_Xat {n : ℕ} (t : Semiterm LRA ℕ n) : head (Xat t) = 2 := rfl

@[simp] theorem head_neg_Xat {n : ℕ} (t : Semiterm LRA ℕ n) : head (∼(Xat t)) = 3 := rfl

@[simp] theorem head_memAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    head (memAt ν t s) = 2 := rfl

@[simp] theorem head_nmemAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    head (nmemAt ν t s) = 3 := rfl

/-- **`evR` does not change the head symbol.** -/
@[simp] theorem head_evR {n : ℕ} (φ : Semiformula LRA ℕ n) : head (evR φ) = head φ := by
  induction φ using Semiformula.rec' <;> rfl

/-- The tactic for "this shape is not that shape": compare heads. -/
theorem ne_of_head {ψ χ : Proposition LRA} (h : head ψ ≠ head χ) : ψ ≠ χ :=
  fun e => h (congrArg head e)

/-! ### `isMemAtom`

The finer discriminator `head` cannot supply: `X(t)` and a level-indexed atom
share the head tag `rel`/`nrel` (both are atoms), and are told apart by which
relation symbol they carry. -/

/-- Whether an atom's relation symbol carries a level, i.e. is some `∈̇_ν`. -/
def isMemAtom {n : ℕ} : Semiformula LRA ℕ n → Bool
  |  .rel r _ => (relLevel r).isSome
  | .nrel r _ => (relLevel r).isSome
  |         _ => false

@[simp] theorem isMemAtom_memAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    isMemAtom (memAt ν t s) = true := rfl

@[simp] theorem isMemAtom_nmemAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    isMemAtom (nmemAt ν t s) = true := rfl

@[simp] theorem isMemAtom_Xat {n : ℕ} (t : Semiterm LRA ℕ n) : isMemAtom (Xat t) = false := rfl

@[simp] theorem isMemAtom_neg_Xat {n : ℕ} (t : Semiterm LRA ℕ n) : isMemAtom (∼(Xat t)) = false :=
  rfl

/-- The tactic for "this atom is not a level-indexed atom, or vice versa". -/
theorem ne_of_isMemAtom {ψ χ : Proposition LRA} (h : isMemAtom ψ ≠ isMemAtom χ) : ψ ≠ χ :=
  fun e => h (congrArg isMemAtom e)

/-! ### Numerals and `Xat` are injective

`Ramified/Language.lean` already proves numerals injective for `num`; `numAtR`
agrees with `num` at level `0` by `numAtR_zero`. `xArg` inverts `Xat`, exactly
as `Gentzen/LowerClass.lean`'s `xArg` inverts the first-order `Xat`. -/

theorem numAtR_injective : Function.Injective (numAtR : ℕ → SyntacticTerm LRA) := by
  intro a b h
  simp only [numAtR_zero] at h
  exact num_injective h

@[simp] theorem numAtR_inj {a b : ℕ} : (numAtR a : SyntacticTerm LRA) = numAtR b ↔ a = b :=
  ⟨fun h => numAtR_injective h, fun h => by rw [h]⟩

/-- A numeral is closed at every level — restated directly for `numAtR`
(rather than routed through `GroundR`) so `simp` can use it without also
pulling in `numAtR_zero`. -/
@[simp] theorem freeVariables_numAtR {n m : ℕ} : (numAtR m : Semiterm LRA ℕ n).freeVariables = ∅ :=
  freeVariables_of_groundR (groundR_numAtR m)

/-- The argument of a unary atom. -/
def xArg {n : ℕ} : Semiformula LRA ℕ n → Semiterm LRA ℕ n
  | .rel (arity := 1) _ v => v 0
  | _ => &0

@[simp] theorem xArg_Xat {n : ℕ} (t : Semiterm LRA ℕ n) : xArg (Xat t) = t := rfl

theorem Xat_inj {n : ℕ} {t s : Semiterm LRA ℕ n} (h : Xat t = Xat s) : t = s := by
  simpa using congrArg xArg h

@[simp] theorem Xat_numAtR_inj {n m : ℕ} :
    Xat (numAtR n : Semiterm LRA ℕ 0) = Xat (numAtR m) ↔ n = m :=
  ⟨fun h => numAtR_injective (Xat_inj h), fun h => by rw [h]⟩

@[simp] theorem neg_Xat_numAtR_inj {n m : ℕ} :
    ∼(Xat (numAtR n : Semiterm LRA ℕ 0)) = ∼(Xat (numAtR m)) ↔ n = m :=
  ⟨fun h => Xat_numAtR_inj.mp (neg_injective h), fun h => by rw [h]⟩

/-! ### (b) The named members of the class

`Gentzen/LowerClass.lean`'s four named shapes, built from `C.prec`, plus the
`C`-independent `allXat`. -/

/-- `(∀ y ≺ x, X y)` at the numeral `n̄`. -/
def belowAt (C : CodedOrderR O) (n : ℕ) : Proposition LRA := (below C.prec)/[numAtR n]

/-- `P n := (∀ y ≺ n̄, X y) ⋏ ∼X(n̄)`. -/
def P (C : CodedOrderR O) (n : ℕ) : Proposition LRA := belowAt C n ⋏ ∼(Xat (numAtR n))

/-- `∼(m̄ ≺ n̄) ⋎ X(m̄)`. -/
def precOrXat (C : CodedOrderR O) (m n : ℕ) : Proposition LRA :=
  ∼(precAt C.prec (numAtR m) (numAtR n)) ⋎ Xat (numAtR m)

/-- `∀ x, X x`. -/
def allXat : Proposition LRA := ∀¹ (Xat (#0 : Semiterm LRA ℕ 1))

theorem belowAt_def (n : ℕ) : belowAt C n = (below C.prec)/[numAtR n] := rfl

theorem P_eq (n : ℕ) : P C n = belowAt C n ⋏ ∼(Xat (numAtR n)) := rfl

theorem precOrXat_eq (m n : ℕ) :
    precOrXat C m n = ∼(precAt C.prec (numAtR m) (numAtR n)) ⋎ Xat (numAtR m) := rfl

theorem allXat_eq : allXat = ∀¹ (Xat (#0 : Semiterm LRA ℕ 1)) := rfl

theorem TIR_eq : TIR C.prec = ∼(Prog C.prec) ⋎ allXat := rfl

theorem negProg_eq : ∼(Prog C.prec) = ∃¹ ((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LRA ℕ 1))) :=
  neg_Prog C.prec

theorem subst_negProg_body (n : ℕ) :
    ((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LRA ℕ 1)))/[numAtR n] = P C n := by
  simp [P_eq, belowAt_def]

theorem belowAt_eq (n : ℕ) :
    belowAt C n = ∀¹ (∼(precAt C.prec (#0 : Semiterm LRA ℕ 1) (numAtR n : Semiterm LRA ℕ 1)) ⋎
      Xat (#0 : Semiterm LRA ℕ 1)) :=
  subst_below_numeral C.prec n

theorem subst_belowAt_body (m n : ℕ) :
    (∼(precAt C.prec (#0 : Semiterm LRA ℕ 1) (numAtR n : Semiterm LRA ℕ 1)) ⋎
      Xat (#0 : Semiterm LRA ℕ 1))/[numAtR m] = precOrXat C m n :=
  subst_belowBody_numeral C.prec n m

theorem subst_allXat_body (m : ℕ) :
    (Xat (#0 : Semiterm LRA ℕ 1))/[(numAtR m : Semiterm LRA ℕ 0)] = Xat (numAtR m : Semiterm LRA ℕ 0) :=
  subst_Xat_bvar_numeral m

@[simp] theorem head_TIR : head (TIR C.prec) = 5 := rfl

@[simp] theorem head_negProg : head (∼(Prog C.prec)) = 7 := by rw [negProg_eq]; simp

@[simp] theorem head_allXat : head allXat = 6 := rfl

@[simp] theorem head_belowAt (n : ℕ) : head (belowAt C n) = 6 := by rw [belowAt_eq]; simp

@[simp] theorem head_P (n : ℕ) : head (P C n) = 4 := rfl

@[simp] theorem head_precOrXat (m n : ℕ) : head (precOrXat C m n) = 5 := rfl

@[simp] theorem freeVariables_allXat : allXat.freeVariables = ∅ := by
  simp [allXat_eq, freeVariables_Xat]

@[simp] theorem freeVariables_belowAt (n : ℕ) : (belowAt C n).freeVariables = ∅ := by
  have h : (precAt C.prec (#0 : Semiterm LRA ℕ 1) (numAtR n : Semiterm LRA ℕ 1)).freeVariables = ∅ :=
    CodedOrderR.freeVariables_precAt C (by simp) (by simp)
  simp [belowAt_eq, h, freeVariables_Xat]

@[simp] theorem freeVariables_P (n : ℕ) : (P C n).freeVariables = ∅ := by simp [P_eq]

@[simp] theorem freeVariables_precOrXat (m n : ℕ) : (precOrXat C m n).freeVariables = ∅ := by
  simp [precOrXat_eq, freeVariables_Xat]

/-- `precAt C.prec` is `XFree` at any pair of arguments: `C.prec` is `XFree`,
and rewriting preserves `XFree`. -/
@[simp] theorem xFree_precAt {n : ℕ} (y x : Semiterm LRA ℕ n) : XFree (precAt C.prec y x) :=
  (XFree_rew _ _).mpr C.xfree_prec

theorem isXFreeClosed_neg_precAt (m n : ℕ) :
    IsXFreeClosed (∼(precAt C.prec (numAtR m : Semiterm LRA ℕ 0) (numAtR n : Semiterm LRA ℕ 0))) := by
  refine ⟨by simp, ?_⟩
  simp only [Semiformula.freeVariables_not]
  exact CodedOrderR.freeVariables_precAt C (by simp) (by simp)

/-! ### The evaluated shapes -/

/-- The body of `belowAt C n`. -/
def belowBody (C : CodedOrderR O) (n : ℕ) : Semiformula LRA ℕ 1 :=
  ∼(precAt C.prec (#0 : Semiterm LRA ℕ 1) (numAtR n : Semiterm LRA ℕ 1)) ⋎
    Xat (#0 : Semiterm LRA ℕ 1)

theorem belowAt_eq_all (n : ℕ) : belowAt C n = ∀¹ (belowBody C n) := belowAt_eq n

theorem subst_belowBody (m n : ℕ) : (belowBody C n)/[numAtR m] = precOrXat C m n :=
  subst_belowAt_body m n

@[simp] theorem evR_neg_Xat_num (n : ℕ) :
    evR (∼(Xat (numAtR n : Semiterm LRA ℕ 0))) = ∼(Xat (numAtR n : Semiterm LRA ℕ 0)) := by
  rw [evR_neg, evR_Xat_num]

@[simp] theorem evR_allXat : evR allXat = allXat := by
  rw [allXat_eq, evR_all, evR_Xat, evTR_bvar]

theorem evR_TIR_eq : evR (TIR C.prec) = evR (∼(Prog C.prec)) ⋎ allXat := by
  rw [TIR_eq, evR_or, evR_allXat]

theorem evR_negProg_eq :
    evR (∼(Prog C.prec)) = ∃¹ (evR ((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LRA ℕ 1)))) := by
  rw [negProg_eq, evR_exs]

@[simp] theorem head_neg_evR_Prog : head (∼(evR (Prog C.prec))) = 7 := by
  have h : ∼(evR (Prog C.prec)) = evR (∼(Prog C.prec)) := (evR_neg _).symm
  rw [h, evR_negProg_eq]
  simp

theorem evR_belowAt_eq (n : ℕ) : evR (belowAt C n) = ∀¹ (evR (belowBody C n)) := by
  rw [belowAt_eq_all, evR_all]

theorem evR_P_eq (n : ℕ) : evR (P C n) = evR (belowAt C n) ⋏ ∼(Xat (numAtR n)) := by
  rw [P_eq, evR_and, evR_neg, evR_Xat_num]

theorem evR_precOrXat_eq (k n : ℕ) :
    evR (precOrXat C k n) = evR (∼(precAt C.prec (numAtR k) (numAtR n))) ⋎ Xat (numAtR k) := by
  rw [precOrXat_eq, evR_or, evR_Xat_num]

/-! ### The evaluated premise computations -/

theorem inst_negProg_body (n : ℕ) :
    evInstR.inst (evR ((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LRA ℕ 1)))) n = evR (P C n) := by
  have he : evInstR.inst (evR ((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LRA ℕ 1)))) n
      = evR (((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LRA ℕ 1)))/[numAtR n]) :=
    evInstR_inst_ev _ n
  rw [he, subst_negProg_body]

theorem inst_belowBody (n k : ℕ) :
    evInstR.inst (evR (belowBody C n)) k = evR (precOrXat C k n) := by
  have he : evInstR.inst (evR (belowBody C n)) k = evR ((belowBody C n)/[numAtR k]) :=
    evInstR_inst_ev _ k
  rw [he, subst_belowBody]

theorem inst_allXat_body (n : ℕ) :
    evInstR.inst (Xat (#0 : Semiterm LRA ℕ 1)) n = Xat (numAtR n) := by
  have he : evInstR.inst (Xat (#0 : Semiterm LRA ℕ 1)) n
      = evR ((Xat (#0 : Semiterm LRA ℕ 1))/[numAtR n]) :=
    evInstR_inst _ n
  rw [he, subst_allXat_body, evR_Xat_num]

/-! ### `evR` preserves the (a₂) property, and the atomic side condition -/

@[simp] theorem xFree_evR {n : ℕ} (φ : Semiformula LRA ℕ n) : XFree (evR φ) ↔ XFree φ := by
  induction φ using Semiformula.rec' <;> simp [*]

@[simp] theorem isXFreeClosed_evR (φ : Proposition LRA) :
    IsXFreeClosed (evR φ) ↔ IsXFreeClosed φ := by
  simp only [IsXFreeClosed, xFree_evR, freeVariables_evR]

theorem isXFreeClosed_inst {φ : Semiformula LRA ℕ 1} (h : IsXFreeClosed (∀¹ φ)) (n : ℕ) :
    IsXFreeClosed (evInstR.inst φ n) := by
  have he : evInstR.inst φ n = evR (φ/[numAtR n]) := evInstR_inst φ n
  rw [he, isXFreeClosed_evR]
  exact isXFreeClosed_all h n

theorem isXFreeClosed_inst_exs {φ : Semiformula LRA ℕ 1} (h : IsXFreeClosed (∃¹ φ)) (n : ℕ) :
    IsXFreeClosed (evInstR.inst φ n) := by
  have he : evInstR.inst φ n = evR (φ/[numAtR n]) := evInstR_inst φ n
  rw [he, isXFreeClosed_evR]
  exact isXFreeClosed_exs h n

theorem isXFreeClosed_evR_neg_precAt (k n : ℕ) :
    IsXFreeClosed (evR (∼(precAt C.prec (numAtR k) (numAtR n)))) :=
  (isXFreeClosed_evR _).mpr (isXFreeClosed_neg_precAt k n)

theorem trueNR_evR_neg_precAt (k n : ℕ) :
    TrueNR (evR (∼(precAt C.prec (numAtR k) (numAtR n)))) ↔ ¬ C.precN k n := by
  rw [trueNR_evR, trueNR_neg]
  exact not_congr (C.eval_precAt_numeral raStruc k n (fun _ => 0))

/-! ### (b′) The class `Ce` -/

/-- **The evaluated class**: the shapes that can occur in a sequent of a
cut-free `RA_∞`-derivation of `evR (TIR C.prec)`. -/
inductive InCe {O : Type} [LinearOrder O] (C : CodedOrderR O) : Proposition LRA → Prop
  /-- every closed formula mentioning neither `X` nor any `∈̇_ν` -/
  | xfree {φ : Proposition LRA} : IsXFreeClosed φ → InCe C φ
  /-- `evR (TIR(≺))` -/
  | ti : InCe C (evR (TIR C.prec))
  /-- `evR (∼Prog(≺))` -/
  | negProg : InCe C (evR (∼(Prog C.prec)))
  /-- `∀ x, X x` -/
  | allX : InCe C allXat
  /-- `evR (∀ y ≺ n̄, X y)` -/
  | belowNum (n : ℕ) : InCe C (evR (belowAt C n))
  /-- `X(n̄)` -/
  | xatNum (n : ℕ) : InCe C (Xat (numAtR n))
  /-- `∼X(n̄)` -/
  | negXatNum (n : ℕ) : InCe C (∼(Xat (numAtR n)))
  /-- `evR (P n)` -/
  | pNum (n : ℕ) : InCe C (evR (P C n))
  /-- `evR (∼(m̄ ≺ n̄) ⋎ X(m̄))` -/
  | precOrX (m n : ℕ) : InCe C (evR (precOrXat C m n))

/-- **The decision lemma.** -/
theorem InCe.exhaustive {φ : Proposition LRA} (h : InCe C φ) :
    IsXFreeClosed φ ∨
    φ = evR (TIR C.prec) ∨
    φ = evR (∼(Prog C.prec)) ∨
    φ = allXat ∨
    (∃ n, φ = evR (belowAt C n)) ∨
    (∃ n, φ = Xat (numAtR n)) ∨
    (∃ n, φ = ∼(Xat (numAtR n))) ∨
    (∃ n, φ = evR (P C n)) ∨
    (∃ m n, φ = evR (precOrXat C m n)) := by
  cases h with
  | xfree hx => exact Or.inl hx
  | ti => exact Or.inr (Or.inl rfl)
  | negProg => exact Or.inr (Or.inr (Or.inl rfl))
  | allX => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | belowNum n => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))
  | xatNum n => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))
  | negXatNum n =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))))
  | pNum n =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))))
  | precOrX m n =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, n, rfl⟩)))))))

theorem InCe.freeVariables_eq_empty {φ : Proposition LRA} (h : InCe C φ) :
    φ.freeVariables = ∅ := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨m, n, he⟩
  · exact hx.2
  · rw [he, freeVariables_evR]; exact CodedOrderR.freeVariables_TIR C
  · rw [he, freeVariables_evR]; simp
  · rw [he]; simp
  · rw [he, freeVariables_evR]; simp
  · rw [he]; simp [freeVariables_Xat, freeVariables_of_groundR (groundR_numAtR n)]
  · rw [he]; simp [freeVariables_Xat, freeVariables_of_groundR (groundR_numAtR n)]
  · rw [he, freeVariables_evR]; simp
  · rw [he, freeVariables_evR]; simp

/-! ### No member of the class mentions a level-indexed set atom

The fact `Ramified/Boundedness.lean`'s `pr`/`npr` cases turn on: a (Pr)
inference's conclusion is a bare `∈̇_ν` atom, and no shape of the class is
one, whichever level it carries. -/

theorem not_inCe_memAt {ν : Lv} {t s : SyntacticTerm LRA} : ¬ InCe C (memAt ν t s) := by
  intro h
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨m, n, he⟩
  · exact not_isXFreeClosed_memAt hx
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg isMemAtom he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)

theorem not_inCe_nmemAt {ν : Lv} {t s : SyntacticTerm LRA} : ¬ InCe C (nmemAt ν t s) := by
  intro h
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨m, n, he⟩
  · exact not_isXFreeClosed_nmemAt hx
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg isMemAtom he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)

/-- `precAt C.prec` is `SetFree` at any pair of arguments: `C.prec` is `XFree`,
hence `SetFree`, and rewriting preserves `SetFree`. -/
@[simp] theorem setFree_precAt {n : ℕ} (y x : Semiterm LRA ℕ n) : SetFree (precAt C.prec y x) :=
  (SetFree_rew _ _).mpr (SetFree_of_XFree C.xfree_prec)

@[simp] theorem setFree_below : SetFree (below C.prec) := by simp [Ramified.below]

@[simp] theorem setFree_Prog : SetFree (Prog C.prec) := by simp [Ramified.Prog]

@[simp] theorem setFree_TIR : SetFree (TIR C.prec) := by simp [Ramified.TIR]

@[simp] theorem setFree_belowAt (n : ℕ) : SetFree (belowAt C n) := by
  rw [belowAt_def]; exact (SetFree_rew _ _).mpr setFree_below

@[simp] theorem setFree_P (n : ℕ) : SetFree (P C n) := by simp [P_eq]

@[simp] theorem setFree_precOrXat (m n : ℕ) : SetFree (precOrXat C m n) := by simp [precOrXat_eq]

/-- **Every member of the class mentions no `∈̇_ν`.**  The general form of the
previous two theorems. -/
theorem inCe_setFree {φ : Proposition LRA} (h : InCe C φ) : SetFree φ := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨m, n, he⟩
  · exact hx.setFree
  · rw [he]; exact (SetFree_evR _).mpr setFree_TIR
  · rw [he]; exact (SetFree_evR _).mpr ((SetFree_neg _).mpr setFree_Prog)
  · rw [he]; simp [allXat_eq]
  · rw [he]; exact (SetFree_evR _).mpr (setFree_belowAt n)
  · rw [he]; exact SetFree_Xat _
  · rw [he]; exact (SetFree_neg _).mpr (SetFree_Xat _)
  · rw [he]; exact (SetFree_evR _).mpr (setFree_P n)
  · rw [he]; exact (SetFree_evR _).mpr (setFree_precOrXat m n)
where
  SetFree_evR {n : ℕ} (φ : Semiformula LRA ℕ n) : SetFree (evR φ) ↔ SetFree φ := by
    induction φ using Semiformula.rec' <;> simp [*]

/-! ### (d) Which member is it? -/

theorem InCe.or_cases {φ ψ : Proposition LRA} (h : InCe C (φ ⋎ ψ)) :
    IsXFreeClosed (φ ⋎ ψ) ∨
    (φ = evR (∼(Prog C.prec)) ∧ ψ = allXat) ∨
    (∃ k n, φ = evR (∼(precAt C.prec (numAtR k) (numAtR n))) ∧ ψ = Xat (numAtR k)) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact Or.inl hx
  · rw [evR_TIR_eq] at he
    obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp he
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · rw [evR_precOrXat_eq] at he
    obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp he
    exact Or.inr (Or.inr ⟨k, n, rfl, rfl⟩)

theorem InCe.and_cases {φ ψ : Proposition LRA} (h : InCe C (φ ⋏ ψ)) :
    IsXFreeClosed (φ ⋏ ψ) ∨
    (∃ n, φ = evR (belowAt C n) ∧ ψ = ∼(Xat (numAtR n))) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact Or.inl hx
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · rw [evR_P_eq] at he
    obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp he
    exact Or.inr ⟨n, rfl, rfl⟩
  · exact absurd (congrArg head he) (by simp)

theorem InCe.all_cases {φ : Semiformula LRA ℕ 1} (h : InCe C (∀¹ φ)) :
    IsXFreeClosed (∀¹ φ) ∨ φ = Xat (#0 : Semiterm LRA ℕ 1) ∨
      (∃ n, φ = evR (belowBody C n)) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact Or.inl hx
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · rw [allXat_eq] at he
    obtain rfl := (Semiformula.all_inj _ _).mp he
    exact Or.inr (Or.inl rfl)
  · rw [evR_belowAt_eq] at he
    obtain rfl := (Semiformula.all_inj _ _).mp he
    exact Or.inr (Or.inr ⟨n, rfl⟩)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)

theorem InCe.exs_cases {φ : Semiformula LRA ℕ 1} (h : InCe C (∃¹ φ)) :
    IsXFreeClosed (∃¹ φ) ∨
      φ = evR ((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LRA ℕ 1))) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact Or.inl hx
  · exact absurd (congrArg head he) (by simp)
  · rw [evR_negProg_eq] at he
    obtain rfl := (Semiformula.exs_inj _ _).mp he
    exact Or.inr rfl
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)

theorem InCe.rel_cases {k : ℕ} (rl : LRA.Rel k) (v : Fin k → SyntacticTerm LRA)
    (h : InCe C (Semiformula.rel rl v)) :
    IsXFreeClosed (Semiformula.rel rl v) ∨ (∃ n, Semiformula.rel rl v = Xat (numAtR n)) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨m, n, he⟩
  · exact Or.inl hx
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact Or.inr ⟨n, he⟩
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)

theorem InCe.nrel_cases {k : ℕ} (rl : LRA.Rel k) (v : Fin k → SyntacticTerm LRA)
    (h : InCe C (Semiformula.nrel rl v)) :
    IsXFreeClosed (Semiformula.nrel rl v) ∨
      (∃ n, Semiformula.nrel rl v = ∼(Xat (numAtR n))) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨m, n, he⟩
  · exact Or.inl hx
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact Or.inr ⟨n, he⟩
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)

/-! ### Closure under premise-formation -/

theorem InCe.of_or {φ ψ : Proposition LRA} (h : InCe C (φ ⋎ ψ)) : InCe C φ ∧ InCe C ψ := by
  rcases h.or_cases with hx | ⟨rfl, rfl⟩ | ⟨k, n, rfl, rfl⟩
  · exact ⟨.xfree (isXFreeClosed_or.mp hx).1, .xfree (isXFreeClosed_or.mp hx).2⟩
  · exact ⟨.negProg, .allX⟩
  · exact ⟨.xfree (isXFreeClosed_evR_neg_precAt k n), .xatNum k⟩

theorem InCe.of_and {φ ψ : Proposition LRA} (h : InCe C (φ ⋏ ψ)) : InCe C φ ∧ InCe C ψ := by
  rcases h.and_cases with hx | ⟨n, rfl, rfl⟩
  · exact ⟨.xfree (isXFreeClosed_and.mp hx).1, .xfree (isXFreeClosed_and.mp hx).2⟩
  · exact ⟨.belowNum n, .negXatNum n⟩

theorem InCe.of_all {φ : Semiformula LRA ℕ 1} (h : InCe C (∀¹ φ)) (n : ℕ) :
    InCe C (evInstR.inst φ n) := by
  rcases h.all_cases with hx | rfl | ⟨m, rfl⟩
  · exact .xfree (isXFreeClosed_inst hx n)
  · rw [inst_allXat_body]
    exact .xatNum n
  · rw [inst_belowBody]
    exact .precOrX n m

theorem InCe.of_exs {φ : Semiformula LRA ℕ 1} (h : InCe C (∃¹ φ)) (n : ℕ) :
    InCe C (evInstR.inst φ n) := by
  rcases h.exs_cases with hx | rfl
  · exact .xfree (isXFreeClosed_inst_exs hx n)
  · rw [inst_negProg_body]
    exact .pNum n

/-! ### Sequents -/

/-- A sequent all of whose formulas are in the evaluated class. -/
def InCeSeq (C : CodedOrderR O) (Γ : Sequent LRA) : Prop := ∀ φ ∈ Γ, InCe C φ

@[simp] theorem inCeSeq_nil : InCeSeq C [] := by
  intro φ hφ
  simp at hφ

@[simp] theorem inCeSeq_cons {φ : Proposition LRA} {Γ : Sequent LRA} :
    InCeSeq C (φ :: Γ) ↔ InCe C φ ∧ InCeSeq C Γ := by
  constructor
  · intro h
    exact ⟨h φ List.mem_cons_self, fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)⟩
  · rintro ⟨hφ, hΓ⟩ ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact hφ
    · exact hΓ ψ hψ

@[simp] theorem inCeSeq_append {Γ Δ : Sequent LRA} :
    InCeSeq C (Γ ++ Δ) ↔ InCeSeq C Γ ∧ InCeSeq C Δ := by
  constructor
  · intro h
    exact ⟨fun φ hφ => h φ (List.mem_append_left _ hφ),
      fun φ hφ => h φ (List.mem_append_right _ hφ)⟩
  · rintro ⟨hΓ, hΔ⟩ φ hφ
    rcases List.mem_append.mp hφ with hφ | hφ
    · exact hΓ φ hφ
    · exact hΔ φ hφ

theorem InCeSeq.of_subset {Γ Δ : Sequent LRA} (h : InCeSeq C Γ) (hs : Δ ⊆ Γ) : InCeSeq C Δ :=
  fun φ hφ => h φ (hs hφ)

theorem InCeSeq.of_or {φ ψ : Proposition LRA} {Γ : Sequent LRA}
    (h : InCeSeq C (φ ⋎ ψ :: Γ)) : InCeSeq C (φ :: ψ :: Γ) := by
  rw [inCeSeq_cons] at h
  obtain ⟨hor, hΓ⟩ := h
  obtain ⟨h₁, h₂⟩ := hor.of_or
  simp [h₁, h₂, hΓ]

theorem InCeSeq.of_and {φ ψ : Proposition LRA} {Γ : Sequent LRA}
    (h : InCeSeq C (φ ⋏ ψ :: Γ)) : InCeSeq C (φ :: Γ) ∧ InCeSeq C (ψ :: Γ) := by
  rw [inCeSeq_cons] at h
  obtain ⟨hand, hΓ⟩ := h
  obtain ⟨h₁, h₂⟩ := hand.of_and
  exact ⟨by simp [h₁, hΓ], by simp [h₂, hΓ]⟩

theorem InCeSeq.of_all {φ : Semiformula LRA ℕ 1} {Γ : Sequent LRA}
    (h : InCeSeq C ((∀¹ φ) :: Γ)) (n : ℕ) : InCeSeq C (evInstR.inst φ n :: Γ) := by
  rw [inCeSeq_cons] at h
  obtain ⟨hall, hΓ⟩ := h
  simp [hall.of_all n, hΓ]

theorem InCeSeq.of_exs {φ : Semiformula LRA ℕ 1} {Γ : Sequent LRA}
    (h : InCeSeq C ((∃¹ φ) :: Γ)) (n : ℕ) : InCeSeq C (evInstR.inst φ n :: Γ) := by
  rw [inCeSeq_cons] at h
  obtain ⟨hexs, hΓ⟩ := h
  simp [hexs.of_exs n, hΓ]

theorem InCeSeq.freeVariables_eq_empty {Γ : Sequent LRA} (h : InCeSeq C Γ)
    {φ : Proposition LRA} (hφ : φ ∈ Γ) : φ.freeVariables = ∅ :=
  (h φ hφ).freeVariables_eq_empty

end Ramified

end OrdinalAnalysis
