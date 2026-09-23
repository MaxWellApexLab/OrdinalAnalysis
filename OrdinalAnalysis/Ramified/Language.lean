/-
  The language of ramified analysis, design **D2** of `gamma0_design.md` §4 G2.

  The decisive finding of that design note (§2) is that *levels must be in the
  syntax*: no monotone function of a structural depth can serve as a level,
  because substitution adds depths while ramification needs a tag that
  substitution does not move.  D1 puts the tag on second-order quantifiers and
  forks Foundation's second-order syntax; D2 — this file — puts the tag on a
  family of **relation symbols** and stays first-order:

      LRA  :=  ℒₒᵣ  +  { X (unary) }  ∪  { ∈̇_ν (binary) | ν : Lv }

  A "set of level `ν`" is then a *numeral* coding a predicator, a level-`ν` set
  quantifier is an ordinary number quantifier over codes — so the ω-rule already
  handles it — and the only new rules are the predicator rules (Pr).  Three
  consequences worth naming, because they are what the prototype is testing:

  * the level of a set atom is *read off the relation symbol*, so the "level of a
    formula" is a plain structural recursion (`Ramified/Code.lean`'s `lvlOf`) and
    is invariant under term substitution — that is the whole content of §2's
    complaint against untagged syntax, and D2 satisfies it by construction;

  * there is no formula-for-variable substitution anywhere in the calculus, so
    `ACAOmega`'s `SubstFamily`/`SubstProvider` machinery is not needed, and (see
    `Ramified/Calculus.lean`) neither is general identity;

  * nothing is forked.  The language is built exactly as `Gentzen/Setup.lean`
    builds `LX = ℒₒᵣ + XLang` with `XLang.Rel 1 := XRel`; here the fresh part has
    `Rel 1 := {X}` and `Rel 2 := Lv`.

  `Lv := ℕ` for the prototype.  The real thing wants `Lv := Gamma0Note` (or a
  segment of it); everything below except `RARel.enc`/`RARel.dec` and the two
  `Encodable` instances is already level-type-agnostic, and those three need
  only an `Encodable Lv`.

  The `Encodable` instances are not decoration: D2's codes are Gödel numbers of
  `Semiformula LRA ℕ 1`, and Foundation's `Semiformula.encodable`
  (`FirstOrder/Basic/Coding.lean:161`) needs `Encodable (L.Func k)` and
  `Encodable (L.Rel k)` for every `k`.  `ℒₒᵣ` has both
  (`Syntax/Predicate/Language.lean:139,163`); this file supplies the summand.
-/
import OrdinalAnalysis.Omega.Calculus
import Foundation.FirstOrder.Arithmetic.Schemata
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder

/-! ### Levels

The prototype's level type.  Every occurrence below is through `Lv`, so the
swap to `Gamma0Note` (or an initial segment) is local. -/

/-- The type of ramification levels. -/
abbrev Lv : Type := ℕ

/-! ### The fresh relation symbols -/

/-- The relation symbols added to arithmetic: one unary `X`, and one binary
membership symbol `∈̇_ν` for each level `ν`. -/
inductive RARel : ℕ → Type
  | X : RARel 1
  | mem : Lv → RARel 2

namespace RARel

instance instDecidableEq {k : ℕ} : DecidableEq (RARel k) := fun a b => by
  cases a with
  | X => cases b with
      | X => exact isTrue rfl
  | mem ν => cases b with
      | mem μ =>
          if h : ν = μ then
            exact isTrue (by rw [h])
          else
            exact isFalse (fun heq => h (by injection heq))

/-- The Gödel index of a relation symbol, within its arity. -/
def enc : {k : ℕ} → RARel k → ℕ
  | _, .X => 0
  | _, .mem ν => ν

/-- The inverse of `enc`, at a given arity. -/
def dec : (k : ℕ) → ℕ → Option (RARel k)
  | 1, _ => some .X
  | 2, n => some (.mem n)
  | _, _ => none

instance instEncodable (k : ℕ) : Encodable (RARel k) where
  encode := enc
  decode := dec k
  encodek := by intro r; cases r <;> rfl

/-- **The level tag.**  `some ν` for the membership symbol of level `ν`, `none`
for `X` — and, once lifted to `LRA.Rel`, `none` for every symbol of arithmetic.

This is the function §2 says cannot exist for untagged syntax: it reads a level
off a symbol, so nothing a substitution does to *terms* can change it. -/
def level : {k : ℕ} → RARel k → Option Lv
  | _, .X => none
  | _, .mem ν => some ν

@[simp] theorem level_X : level .X = none := rfl

@[simp] theorem level_mem (ν : Lv) : level (.mem ν) = some ν := rfl

end RARel

/-! ### The language -/

/-- The fresh part of the language: no function symbols, the relation symbols
`RARel`. -/
abbrev RALang : Language where
  Func := fun _ => PEmpty
  Rel := RARel

/-- **The language of ramified analysis.**  Arithmetic, the fresh unary `X`, and
the level-indexed membership symbols. -/
abbrev LRA : Language := Language.add ℒₒᵣ RALang

instance : Language.ORing LRA where
  eq := Sum.inl Language.Eq.eq
  lt := Sum.inl Language.LT.lt
  zero := Sum.inl Language.Zero.zero
  one := Sum.inl Language.One.one
  add := Sum.inl Language.Add.add
  mul := Sum.inl Language.Mul.mul

/-- The embedding of arithmetic into `LRA`, as `Gentzen/Setup.lean`'s `toLX`. -/
abbrev toLRA : ℒₒᵣ →ᵥ LRA := Language.Hom.add₁ ℒₒᵣ RALang

instance instEncodableRALangFunc (k : ℕ) : Encodable (RALang.Func k) :=
  inferInstanceAs (Encodable PEmpty)

instance instEncodableLRAFunc (k : ℕ) : Encodable (LRA.Func k) :=
  inferInstanceAs (Encodable (Language.Func ℒₒᵣ k ⊕ Language.Func RALang k))

instance instEncodableLRARel (k : ℕ) : Encodable (LRA.Rel k) :=
  inferInstanceAs (Encodable (Language.Rel ℒₒᵣ k ⊕ RARel k))

/-! ### The level of an `LRA` relation symbol

Arithmetic symbols and `X` are levelless; only `∈̇_ν` carries a level. -/

/-- The level tag of an `LRA` relation symbol. -/
def relLevel : {k : ℕ} → LRA.Rel k → Option Lv
  | _, Sum.inl _ => none
  | _, Sum.inr r => r.level

@[simp] theorem relLevel_inl {k : ℕ} (r : Language.Rel ℒₒᵣ k) :
    relLevel (Sum.inl r : LRA.Rel k) = none := rfl

@[simp] theorem relLevel_X : relLevel (Sum.inr RARel.X : LRA.Rel 1) = none := rfl

@[simp] theorem relLevel_mem (ν : Lv) :
    relLevel (Sum.inr (RARel.mem ν) : LRA.Rel 2) = some ν := rfl

/-! ### The atoms -/

/-- `X(t)`.  Kept for the regression test: at level `ν = 1` the ramified
calculus must reproduce `ACA_∞`, whose free set variable is this `X`. -/
def Xat {n : ℕ} (t : Semiterm LRA ℕ n) : Semiformula LRA ℕ n :=
  Semiformula.rel (Sum.inr RARel.X) ![t]

/-- `t ∈̇_ν s` — "`t` belongs to the level-`ν` set named `s`". -/
def memAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) : Semiformula LRA ℕ n :=
  Semiformula.rel (Sum.inr (RARel.mem ν)) ![t, s]

/-- `t ∉̇_ν s`, the negated atom. -/
def nmemAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) : Semiformula LRA ℕ n :=
  Semiformula.nrel (Sum.inr (RARel.mem ν)) ![t, s]

@[simp] theorem neg_memAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    ∼(memAt ν t s) = nmemAt ν t s := rfl

@[simp] theorem neg_nmemAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    ∼(nmemAt ν t s) = memAt ν t s := rfl

/-! ### Numerals

Foundation's ordered-ring numerals, available because `Language.ORing LRA` is an
instance.  They are closed terms; in D2 they are also the *names of sets*, which
is the whole point of the design — a level-`ν` set is the numeral of a code. -/

/-- The numerals of `LRA`. -/
def num : ℕ → SyntacticTerm LRA := fun k => Semiterm.numeral k

/-! ### Distinct numerals are distinct terms

Needed by the *dispatcher* of the reduction lemma, not by its principal case:
matching two (Pr) inferences on the same atom yields `n̄ = n̄'` and `ā = ā'` as
terms, and the two premises coincide only once those give `n = n'` and `a = a'`.

`Semiterm.numeral` has no syntactic injectivity lemma in Foundation and the only
cheap proof is semantic; this is `Gentzen/LowerClass.lean:190–221` with the
second summand of the language changed, which is the only thing that changes. -/

section Numeral

variable {ξ : Type*} {n : ℕ}

private lemma lMap_toLRA_numeral_zero :
    Semiterm.lMap toLRA ((0 : ℕ) : Semiterm ℒₒᵣ ξ n) = ((0 : ℕ) : Semiterm LRA ξ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, toLRA]

private lemma lMap_toLRA_numeral_one :
    Semiterm.lMap toLRA ((1 : ℕ) : Semiterm ℒₒᵣ ξ n) = ((1 : ℕ) : Semiterm LRA ξ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, toLRA]

private lemma lMap_toLRA_add (v : Fin 2 → Semiterm ℒₒᵣ ξ n) :
    Semiterm.lMap toLRA (Semiterm.Operator.Add.add.operator v) =
      Semiterm.Operator.Add.add.operator (Semiterm.lMap toLRA ∘ v) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, toLRA]
  funext i
  simp

/-- `numeral (k + 2) = numeral (k + 1) + 1`, in the shape `Add.add.operator ![_, _]`. -/
private lemma numeral_succ_succ' (L : Language) [L.Zero] [L.One] [L.Add] (k : ℕ) :
    ((k + 1 + 1 : ℕ) : Semiterm L ξ n) =
      Semiterm.Operator.Add.add.operator
        ![((k + 1 : ℕ) : Semiterm L ξ n), ((1 : ℕ) : Semiterm L ξ n)] := by
  have h : k + 1 ≠ 0 := Nat.succ_ne_zero k
  simp only [Semiterm.numeral, Semiterm.Operator.const,
    Semiterm.Operator.numeral_succ h, Semiterm.Operator.operator_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem lMap_toLRA_numeral (k : ℕ) :
    Semiterm.lMap toLRA ((k : ℕ) : Semiterm ℒₒᵣ ξ n) = ((k : ℕ) : Semiterm LRA ξ n) := by
  induction k with
  | zero => exact lMap_toLRA_numeral_zero
  | succ k ih =>
    cases k with
    | zero => exact lMap_toLRA_numeral_one
    | succ k =>
      rw [numeral_succ_succ' ℒₒᵣ k, numeral_succ_succ' LRA k, lMap_toLRA_add]
      congr 1
      funext i
      fin_cases i
      · exact ih
      · exact lMap_toLRA_numeral_one

end Numeral

set_option warn.classDefReducibility false in
/-- A throwaway reading of the fresh symbols.  `RALang` has no function symbols,
so only `rel` has to be decided, and the choice is irrelevant: the numerals are
`X`- and `∈̇`-free, so their values do not see it. -/
private def raStrucAux : Structure RALang ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ _ _ => False

set_option warn.classDefReducibility false in
/-- Arithmetic standard, the fresh symbols read arbitrarily.  Deliberately *not*
an instance: the standard model of `LRA` belongs with the atomic axioms, not
here. -/
private def stdAux : Structure LRA ℕ := Structure.add ℒₒᵣ RALang ℕ (str₂ := raStrucAux)

private theorem val_num_aux (k : ℕ) :
    Semiterm.val (s := stdAux) ![] (fun _ => 0) (num k) = k := by
  have h : (num k : Semiterm LRA ℕ 0) = Semiterm.lMap toLRA ((k : ℕ) : Semiterm ℒₒᵣ ℕ 0) :=
    (lMap_toLRA_numeral k).symm
  have key : Semiterm.val (s := stdAux) ![] (fun _ : ℕ => (0 : ℕ))
      (Semiterm.lMap toLRA ((k : ℕ) : Semiterm ℒₒᵣ ℕ 0))
      = Semiterm.val (M := ℕ) ![] (fun _ => 0) ((k : ℕ) : Semiterm ℒₒᵣ ℕ 0) :=
    Structure.val_lMap_add₁ (str₂ := raStrucAux) _ _ _
  rw [h, key]
  simp

/-- **Distinct numerals are distinct terms.** -/
theorem num_injective : Function.Injective num := by
  intro k m h
  have hval := congrArg (Semiterm.val (s := stdAux) ![] (fun _ => 0)) h
  rw [val_num_aux k, val_num_aux m] at hval
  exact hval

@[simp] theorem num_inj {k m : ℕ} : num k = num m ↔ k = m :=
  ⟨fun h => num_injective h, fun h => by rw [h]⟩

/-! ### Set atoms are injective

`Semiformula.rel`'s arity is an index, so `injEq` produces `HEq`s and `injection`
cannot invert it; the projections below do, exactly as `Gentzen/LowerClass.lean`
inverts `Xat` through `xArg`. -/

/-- The two arguments of a binary atom. -/
def atomArgs {n : ℕ} :
    Semiformula LRA ℕ n → Semiterm LRA ℕ n × Semiterm LRA ℕ n
  |  .rel (arity := 2) _ v => (v 0, v 1)
  | .nrel (arity := 2) _ v => (v 0, v 1)
  |                       _ => (&0, &0)

@[simp] theorem atomArgs_memAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    atomArgs (memAt ν t s) = (t, s) := rfl

@[simp] theorem atomArgs_nmemAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    atomArgs (nmemAt ν t s) = (t, s) := rfl

/-- The level of a binary atom, as a projection that `congrArg` can use. -/
def atomLv {n : ℕ} : Semiformula LRA ℕ n → Lv
  |  .rel r _ => (relLevel r).getD 0
  | .nrel r _ => (relLevel r).getD 0
  |         _ => 0

@[simp] theorem atomLv_memAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    atomLv (memAt ν t s) = ν := rfl

@[simp] theorem atomLv_nmemAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    atomLv (nmemAt ν t s) = ν := rfl

/-- **A set atom determines its level and its two arguments.** -/
theorem memAt_inj {n : ℕ} {ν ν' : Lv} {t s t' s' : Semiterm LRA ℕ n}
    (h : memAt ν t s = memAt ν' t' s') : ν = ν' ∧ t = t' ∧ s = s' := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg atomLv h
  · simpa using congrArg (fun φ => (atomArgs φ).1) h
  · simpa using congrArg (fun φ => (atomArgs φ).2) h

/-- The negated form, likewise. -/
theorem nmemAt_inj {n : ℕ} {ν ν' : Lv} {t s t' s' : Semiterm LRA ℕ n}
    (h : nmemAt ν t s = nmemAt ν' t' s') : ν = ν' ∧ t = t' ∧ s = s' := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg atomLv h
  · simpa using congrArg (fun φ => (atomArgs φ).1) h
  · simpa using congrArg (fun φ => (atomArgs φ).2) h

end Ramified

end OrdinalAnalysis
