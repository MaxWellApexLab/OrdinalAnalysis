/-
  The theory `ID₁` of one positive inductive definition.

  The language is arithmetic with two fresh unary predicates,

      LXI  :=  ℒₒᵣ  +  { X, I },

  built exactly as `Gentzen.LX = ℒₒᵣ + X` is built.  `X` is the free
  predicate of transfinite induction, as in every theory of this development;
  `I` is the inductively defined predicate.

  **Operator forms.**  An operator form is a formula `A(Y, x)` with one number
  slot `x`, in which the set variable `Y` occurs only positively.  Here the
  set variable is the symbol `I` itself: an operator form is a formula
  `A : Semisentence LXI 1` together with the syntactic condition `Positive A`
  (no negated `I`-atom; the formulas of Foundation are in negation normal
  form, so this is positivity).  Then

    * `A(I, x)` is `A` itself, and
    * `A(F, x)` is `substI F A`: every atom `I t` of `A` replaced by `F(t)`.

  No second language and no relabelling of symbols is needed.  `A` may mention
  `X`; in the standard model `X` is read by a fixed predicate, so it acts as a
  set parameter of the operator.

  **Why operator forms are sentences.**  `A` has no free number variables.
  This is forced: the axioms are universally closed, so a free variable `a` of
  `A` would make `I` a fixed point of *every* operator `A(·, a)` at once.  For
  `A_a(Y, x) :≡ ∀y (x ≠ a → Y y)` the least fixed point of `A_a` is `{a}`; the
  closure axioms give `I a` for every `a`, while the induction scheme with
  `F(x) :≡ x = a` gives `I ⊆ {a}` — an inconsistent theory.  The formulas `F`
  of the induction scheme, on the other hand, may have free variables (set
  parameters in the usual sense); they are closed off by `univCl`.

  **The axioms of `ID1 A`.**

    * `𝗘𝗤 LXI`, the equality axioms of the whole language;
    * `𝗣𝗔⁻`, transported along `ℒₒᵣ → LXI`;
    * induction for every formula of `LXI` (`InductionScheme LXI Set.univ`);
    * closure: `∀x (A(I, x) → I x)` (`closureAx`);
    * the induction scheme for `I`: for every `F : Semiformula LXI ℕ 1`, the
      universal closure of `∀x (A(F, x) → F x) → ∀x (I x → F x)` (`indAx`).

  The first three form `paLXI`, the analogue of `paLX`.

  **The accessible part.**  `accForm prec` is `A(Y, x) :≡ ∀y (y ≺ x → Y y)` for
  an arithmetic, parameter-free `prec`; it is positive (`accForm_positive`),
  and `ID1Acc prec := ID1 (accForm prec)` axiomatises `I` as the accessible
  part of `≺`.

  Contents.

    `IXRel`, `IXLang`, `LXI`, `toLXI`    the language
    `Xat`, `Iat`                         the atoms `X t`, `I t`
    `Positive`                           `I` occurs only positively
    `positive_lMap_toLXI`                arithmetic formulas and their negations are positive
    `substI`                             `A(F, ·)`: replace every `I t` by `F(t)`
    `opAt`                               `A(F, x)` for an operator form `A`
    `closureAx`, `indAx`                 the two axioms of the inductive definition
    `paLXI`, `idAxioms`, `ID1`           the theories, with membership lemmas
    `accForm`, `accForm_positive`, `ID1Acc`, `ID1Acc_positive`
-/
import Foundation.FirstOrder.Arithmetic.Schemata

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### The language -/

/-- The two fresh unary predicate symbols: `X`, the free predicate, and `I`,
the inductively defined one. -/
inductive IXRel : ℕ → Type
  | X : IXRel 1
  | I : IXRel 1

instance {k : ℕ} : DecidableEq (IXRel k) := fun a b => by
  cases a <;> cases b
  · exact isTrue rfl
  · exact isFalse (by intro h; cases h)
  · exact isFalse (by intro h; cases h)
  · exact isTrue rfl

/-- The language of the two predicates alone. -/
abbrev IXLang : Language where
  Func := fun _ => PEmpty
  Rel := IXRel

/-- Arithmetic together with the fresh predicates `X` and `I`. -/
abbrev LXI : Language := Language.add ℒₒᵣ IXLang

instance : Language.ORing LXI where
  eq := Sum.inl Language.Eq.eq
  lt := Sum.inl Language.LT.lt
  zero := Sum.inl Language.Zero.zero
  one := Sum.inl Language.One.one
  add := Sum.inl Language.Add.add
  mul := Sum.inl Language.Mul.mul

/-- The embedding of arithmetic into `LXI`. -/
abbrev toLXI : ℒₒᵣ →ᵥ LXI := Language.Hom.add₁ ℒₒᵣ IXLang

/-- `X(t)`. -/
def Xat {ξ : Type*} {n : ℕ} (t : Semiterm LXI ξ n) : Semiformula LXI ξ n :=
  Semiformula.rel (Sum.inr IXRel.X) ![t]

/-- `I(t)`. -/
def Iat {ξ : Type*} {n : ℕ} (t : Semiterm LXI ξ n) : Semiformula LXI ξ n :=
  Semiformula.rel (Sum.inr IXRel.I) ![t]

/-! ### Positivity -/

/-- **`I` occurs only positively**: no subformula is a negated `I`-atom.
Formulas are in negation normal form, so this is the usual syntactic
positivity; `X` and the arithmetic symbols are unrestricted. -/
def Positive {ξ : Type*} : {n : ℕ} → Semiformula LXI ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel _ _ => True
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr IXRel.X) _ => True
  | _, .nrel (Sum.inr IXRel.I) _ => False
  | _, .and φ ψ => Positive φ ∧ Positive ψ
  | _, .or φ ψ => Positive φ ∧ Positive ψ
  | _, .all φ => Positive φ
  | _, .exs φ => Positive φ

section Positive

variable {ξ : Type*} {n : ℕ}

@[simp] theorem positive_verum : Positive (⊤ : Semiformula LXI ξ n) := trivial

@[simp] theorem positive_falsum : Positive (⊥ : Semiformula LXI ξ n) := trivial

@[simp] theorem positive_and (φ ψ : Semiformula LXI ξ n) :
    Positive (φ ⋏ ψ) ↔ Positive φ ∧ Positive ψ := Iff.rfl

@[simp] theorem positive_or (φ ψ : Semiformula LXI ξ n) :
    Positive (φ ⋎ ψ) ↔ Positive φ ∧ Positive ψ := Iff.rfl

@[simp] theorem positive_all (φ : Semiformula LXI ξ (n + 1)) :
    Positive (∀¹ φ) ↔ Positive φ := Iff.rfl

@[simp] theorem positive_exs (φ : Semiformula LXI ξ (n + 1)) :
    Positive (∃¹ φ) ↔ Positive φ := Iff.rfl

theorem positive_Iat (t : Semiterm LXI ξ n) : Positive (Iat t) := trivial

theorem positive_Xat (t : Semiterm LXI ξ n) : Positive (Xat t) := trivial

theorem positive_neg_Xat (t : Semiterm LXI ξ n) : Positive (∼(Xat t)) := trivial

/-- An arithmetic formula, transported to `LXI`, is positive, and so is its
negation: it contains no `I` at all. -/
theorem positive_lMap_toLXI : ∀ {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n),
    Positive (Semiformula.lMap toLXI φ) ∧ Positive (∼(Semiformula.lMap toLXI φ))
  | _, .verum => ⟨trivial, trivial⟩
  | _, .falsum => ⟨trivial, trivial⟩
  | _, .rel _ _ => ⟨trivial, trivial⟩
  | _, .nrel _ _ => ⟨trivial, trivial⟩
  | _, .and φ ψ => by
      have h1 := positive_lMap_toLXI φ
      have h2 := positive_lMap_toLXI ψ
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  | _, .or φ ψ => by
      have h1 := positive_lMap_toLXI φ
      have h2 := positive_lMap_toLXI ψ
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  | _, .all φ => positive_lMap_toLXI φ
  | _, .exs φ => positive_lMap_toLXI φ

end Positive

/-! ### Substituting a formula for `I` -/

/-- **`substI F φ`**: every atom `I t` of `φ` replaced by `F(t)`, and every
`∼I t` by `∼F(t)`.  `F(t)` is `F/[t]`: the bound variable of `F` receives `t`,
and the free variables of `F` stay free — they are parameters shared with
`φ`, and under a binder of `φ` they cannot be captured, since free and bound
variables are separate sorts. -/
def substI {ξ : Type*} (F : Semiformula LXI ξ 1) :
    {n : ℕ} → Semiformula LXI ξ n → Semiformula LXI ξ n
  | _, .verum => ⊤
  | _, .falsum => ⊥
  | _, .rel (Sum.inl r) v => .rel (Sum.inl r) v
  | _, .rel (Sum.inr IXRel.X) v => .rel (Sum.inr IXRel.X) v
  | _, .rel (Sum.inr IXRel.I) v => F/[v 0]
  | _, .nrel (Sum.inl r) v => .nrel (Sum.inl r) v
  | _, .nrel (Sum.inr IXRel.X) v => .nrel (Sum.inr IXRel.X) v
  | _, .nrel (Sum.inr IXRel.I) v => ∼(F/[v 0])
  | _, .and φ ψ => substI F φ ⋏ substI F ψ
  | _, .or φ ψ => substI F φ ⋎ substI F ψ
  | _, .all φ => ∀¹ substI F φ
  | _, .exs φ => ∃¹ substI F φ

/-! ### Operator forms and the axioms of the inductive definition -/

/-- `A(F, x)`, a formula in the bound slot `x` with the free variables of `F`
as parameters.  `A(I, x)` is `A` itself. -/
def opAt (A : Semisentence LXI 1) (F : Semiformula LXI ℕ 1) : Semiformula LXI ℕ 1 :=
  substI F (Rewriting.emb A)

/-- **Closure**: `∀x (A(I, x) → I x)`. -/
def closureAx (A : Semisentence LXI 1) : Sentence LXI :=
  ∀¹ (A 🡒 Iat #0)

/-- **The induction scheme for `I`**, at the formula `F`: the universal
closure of `∀x (A(F, x) → F x) → ∀x (I x → F x)`. -/
def indAx (A : Semisentence LXI 1) (F : Semiformula LXI ℕ 1) : Sentence LXI :=
  Semiformula.univCl ((∀¹ (opAt A F 🡒 F)) 🡒 ∀¹ (Iat #0 🡒 F))

/-- `PA` in the language `LXI`: equality for the whole language, `𝗣𝗔⁻`
transported, and induction for every formula of `LXI`, including those
mentioning `X` and `I`. -/
def paLXI : Theory LXI :=
  𝗘𝗤 LXI ∪ (Theory.lMap toLXI 𝗣𝗔⁻ ∪ InductionScheme LXI Set.univ)

/-- The two axioms of the inductive definition given by `A`. -/
def idAxioms (A : Semisentence LXI 1) : Theory LXI :=
  insert (closureAx A) (Set.range (indAx A))

/-- **`ID₁` for the operator form `A`.** -/
def ID1 (A : Semisentence LXI 1) : Theory LXI :=
  paLXI ∪ idAxioms A

section Membership

variable (A : Semisentence LXI 1)

theorem paLXI_subset_ID1 : paLXI ⊆ ID1 A := Set.subset_union_left

theorem mem_ID1_of_eq {σ : Sentence LXI} (h : σ ∈ 𝗘𝗤 LXI) : σ ∈ ID1 A :=
  Or.inl (Or.inl h)

theorem mem_ID1_of_paMinus {σ : Sentence ℒₒᵣ} (h : σ ∈ 𝗣𝗔⁻) :
    Semiformula.lMap toLXI σ ∈ ID1 A :=
  Or.inl (Or.inr (Or.inl ⟨σ, h, rfl⟩))

theorem succInd_mem_ID1 (φ : Semiformula LXI ℕ 1) :
    Semiformula.univCl (succInd φ) ∈ ID1 A :=
  Or.inl (Or.inr (Or.inr ⟨φ, trivial, rfl⟩))

theorem closureAx_mem_ID1 : closureAx A ∈ ID1 A :=
  Or.inr (Set.mem_insert _ _)

theorem indAx_mem_ID1 (F : Semiformula LXI ℕ 1) : indAx A F ∈ ID1 A :=
  Or.inr (Set.mem_insert_of_mem _ ⟨F, rfl⟩)

/-- The axioms of `ID1 A`, by kind. -/
theorem mem_ID1 {σ : Sentence LXI} :
    σ ∈ ID1 A ↔ σ ∈ 𝗘𝗤 LXI ∨ σ ∈ Theory.lMap toLXI 𝗣𝗔⁻ ∨ σ ∈ InductionScheme LXI Set.univ ∨
      σ = closureAx A ∨ ∃ F, σ = indAx A F := by
  constructor
  · rintro ((h | h | h) | h | ⟨F, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨F, rfl⟩)))
  · rintro (h | h | h | rfl | ⟨F, rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact closureAx_mem_ID1 A
    · exact indAx_mem_ID1 A F

instance paLXI_weakerThan_ID1 : paLXI ⪯ ID1 A :=
  Entailment.WeakerThan.ofSubset (paLXI_subset_ID1 A)

instance eq_weakerThan_ID1 : 𝗘𝗤 LXI ⪯ ID1 A :=
  Entailment.WeakerThan.ofSubset fun _ h => mem_ID1_of_eq A h

end Membership

/-! ### The accessible part -/

/-- **The accessibility operator form** `A(Y, x) :≡ ∀y (y ≺ x → Y y)`.

`prec` is an arithmetic formula with two bound slots and no free variables,
read as in `Gentzen.precAt`: slot `#0` is the smaller element `y`, slot `#1`
the larger `x`.  Under the binder `∀y` of the form, `#0` is `y` and `#1` is the
form's slot `x`, so `prec` is used with no renaming.  It must have no free
variables, for the reason given in the header. -/
def accForm (prec : Semisentence ℒₒᵣ 2) : Semisentence LXI 1 :=
  ∀¹ (Semiformula.lMap toLXI prec 🡒 Iat #0)

/-- The accessibility form is positive: `I` occurs once, positively, and `prec`
contains no `I`. -/
theorem accForm_positive (prec : Semisentence ℒₒᵣ 2) : Positive (accForm prec) :=
  ⟨(positive_lMap_toLXI prec).2, positive_Iat _⟩

/-- **`ID₁` for the accessible part of `≺`**: `I` is axiomatised as the
accessible part of the relation `prec`.

The intended `prec` is the order of the ϑ-notation for the Bachmann–Howard
ordinal, restricted to its countable part and coded in arithmetic; nothing
here depends on that choice. -/
def ID1Acc (prec : Semisentence ℒₒᵣ 2) : Theory LXI :=
  ID1 (accForm prec)

/-- The operator form of `ID1Acc` is positive. -/
theorem ID1Acc_positive (prec : Semisentence ℒₒᵣ 2) : Positive (accForm prec) :=
  accForm_positive prec

end InductiveDef

end OrdinalAnalysis
