/-
  DEFINITIONS ONLY: this file states the target, it proves nothing yet.

  Gentzen 1943: the calibration half of `|PA| = ε₀`.

  Cut elimination bounds how *strong* PA is from above.  It says nothing about
  how strong PA is from below, and the two-sided statement `|PA| = ε₀` is the
  ordinal analysis proper:

    upper bound   for every notation `a` below `ε₀`,  `PA[X] ⊢ TI(≺, a)`
    lower bound   `PA[X] ⊬ TI(≺)`

  The upper bound is Gentzen's 1943 paper, *Beweisbarkeit und Unbeweisbarkeit
  von Anfangsfällen der transfiniten Induktion in der reinen Zahlentheorie*,
  Math. Ann. 119 (1943) 140–161.  Surveys of Lean, Coq, Isabelle, Agda, HOL
  Light, HOL4, Mizar, Metamath, ACL2 and Nuprl find it formalized nowhere: every
  system has ordinal notations, many have an object theory with a provability
  predicate, and no system joins them.  Coq's `hydra-battles` has both halves in
  one project and its documentation says the authors chose not to build the
  bridge.

  This file sets up the statement.  Three things about the shape.

  * The language is arithmetic *plus a fresh unary predicate* `X`, and the
    theory is PA with induction extended to every formula of that larger
    language.  Transfinite induction is asserted for an arbitrary predicate, not
    for a definable one, and that is what makes the result a statement about the
    *ordinal* rather than about a particular formula.

  * The ordering `≺` is a parameter.  Gentzen's argument is uniform in it: it
    needs a handful of laws about `≺`, `+` and `a ↦ ω ^ a`, and nothing else
    about how the notations are coded.  Isolating those laws as an interface
    separates the mathematics — the jump construction — from the arithmetization,
    which is the part that is large and which no library in any system currently
    has.

  * The universal quantifier over `a` lives in the *meta*-language.  There is one
    PA-proof for each notation, and no single PA-proof of all of them; that is
    exactly the content of the lower bound.  So the theorem to be proved is a
    Lean *function* from notations to derivations, not a derivation.
-/
import Foundation.FirstOrder.Arithmetic.Schemata
import OrdinalAnalysis.Ordinal.OmegaPow

namespace OrdinalAnalysis

namespace Gentzen

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### The language -/

/-- One fresh unary predicate symbol. -/
inductive XRel : ℕ → Type
  | X : XRel 1

instance {k : ℕ} : DecidableEq (XRel k) := fun a b => by
  cases a; cases b; exact isTrue rfl

/-- The language consisting of that predicate alone. -/
abbrev XLang : Language where
  Func := fun _ => PEmpty
  Rel := XRel

/-- Arithmetic together with a fresh unary predicate. -/
abbrev LX : Language := Language.add ℒₒᵣ XLang

instance : Language.ORing LX where
  eq := Sum.inl Language.Eq.eq
  lt := Sum.inl Language.LT.lt
  zero := Sum.inl Language.Zero.zero
  one := Sum.inl Language.One.one
  add := Sum.inl Language.Add.add
  mul := Sum.inl Language.Mul.mul

/-- The embedding of arithmetic into the extended language. -/
abbrev toLX : ℒₒᵣ →ᵥ LX := Language.Hom.add₁ ℒₒᵣ XLang

/-- `X(t)`. -/
def Xat {n : ℕ} (t : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  Semiformula.rel (Sum.inr XRel.X) ![t]

/-! ### The theory

`PA[X]`: equality for the entire enlarged language, the axioms of `PA⁻`
transported into it, and the induction schema for *every* formula of that
language — including those mentioning `X`.  The full equality theory supplies
congruence for the fresh predicate; transporting arithmetic equality alone
would not.  Extending induction to the new predicate is equally essential;
with induction only for arithmetic formulas the argument below collapses. -/
def paLX : Theory LX :=
  𝗘𝗤 LX ∪ (Theory.lMap toLX 𝗣𝗔⁻ ∪ InductionScheme LX Set.univ)

instance paLX_eqTheory : 𝗘𝗤 LX ⪯ paLX := by
  apply Entailment.WeakerThan.ofSubset
  intro σ hσ
  change σ ∈ 𝗘𝗤 LX ∪ (Theory.lMap toLX 𝗣𝗔⁻ ∪ InductionScheme LX Set.univ)
  exact Or.inl hσ

/-! ### Progressiveness and transfinite induction

With `≺` a binary relation of the extended language, written as a formula in
two variables:

* `Prog(≺)` says `X` is progressive — it holds at `x` whenever it holds
  everywhere below `x`;
* `TI(≺)` says progressiveness forces `X` to hold everywhere;
* `TIupto(≺, t)` restricts that conclusion to the notations below `t`, and is
  the form the upper bound proves, one instance at a time. -/

variable (prec : Semiformula LX ℕ 2)

/-- `y ≺ x`, with `y` the innermost bound variable. -/
def precAt {n : ℕ} (y x : Semiterm LX ℕ n) : Semiformula LX ℕ n :=
  Rew.subst ![y, x] ▹ prec

/-- `∀ y ≺ x, X y` — the hypothesis of progressiveness at `x`. -/
def below : Semiformula LX ℕ 1 :=
  ∀¹ (∼(precAt prec (#0 : Semiterm LX ℕ 2) #1) ⋎ Xat #0)

/-- `Prog(≺) :≡ ∀ x ((∀ y ≺ x, X y) → X x)`. -/
def Prog : Semiformula LX ℕ 0 :=
  ∀¹ (∼(below prec) ⋎ Xat #0)

/-- `TI(≺) :≡ Prog(≺) → ∀ x, X x`. -/
def TI : Semiformula LX ℕ 0 :=
  ∼(Prog prec) ⋎ (∀¹ (Xat #0))

/-- `TIupto(≺, t) :≡ Prog(≺) → ∀ x ≺ t, X x`.

This is the sentence the upper bound proves, once for each notation `t`.  The
unrestricted `TI` is what the lower bound refutes, and the gap between them is
the whole of the ordinal analysis. -/
def TIupto (t : Semiterm LX ℕ 0) : Semiformula LX ℕ 0 :=
  ∼(Prog prec) ⋎ (∀¹ (∼(precAt prec (#0 : Semiterm LX ℕ 1) (Rew.bShift t)) ⋎ Xat #0))

end Gentzen

end OrdinalAnalysis
