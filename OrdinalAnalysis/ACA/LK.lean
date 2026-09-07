/-
  Task 2c of the `|ACA| = ε_{ε₀}` node, part two: **our own second-order
  one-sided LK**, and `ACA₀` / `ACA` as schemata over it.

  Foundation's `SecondOrder/Derivation.lean` is full second-order logic: its
  `exs₂` rule instantiates a set quantifier by an *arbitrary* formula, which is
  full comprehension — the system it axiomatises is `Z₂`, not `ACA`.  The
  calculus here is Foundation's, rule for rule, with exactly one change:

      exs₂ now demands `Arith ψ`.

  That single side condition is what turns the calculus into Afshari–Rathjen's
  `ACA_∞` (CiE 2012, §2): arithmetical comprehension, and no other comprehension.
  Together with `Syntax.lean`'s `rank_subst₂_lt_exs₂` — an arithmetical instance
  of `∃² φ` has rank strictly below `rank (∃² φ)` — it is what will make cut
  elimination terminate.

  `identity` is kept **general**: `[φ, ∼φ]` for every `φ`, set quantifiers
  included.  Restricting it would be a different (weaker) system; Afshari–Rathjen
  keep it too and pay for it with their Lemma 2.1, which derives it at height
  `2·rank φ`.

  The theories.  `ACA₀` is equality, `PA⁻`, the **set** induction axiom (a single
  `∀²`-sentence, not a schema) and arithmetical comprehension; `ACA` adds the
  induction schema for *all* second-order formulas.  That is the whole gap
  between `ε₀` and `ε_{ε₀}`.

  A design decision, recorded because it is load-bearing.  **Axioms are stated
  with free number variables and are not universally closed.**  Foundation's
  `Schema.Derivation` is already a schema over `Proposition L`, i.e. over
  formulas with free variables of type `ℕ`, and the axiom sets below contain
  *every* instance — so for `compAx` and `indScheme` the substitution instance
  `ψ[t/&x]` is itself an element of the set, and a universal closure would add
  no provable consequence while forcing `free₀`/`shift₀` bookkeeping into every
  application.  There is no `univCl` on the second-order side of Foundation, and
  writing one would have to commute with `free₁`/`shift₁`; it is not needed.
  Semantically the convention is the right one as well: `Standard.lean` reads a
  free-variable axiom as true iff true under *every* assignment, which is exactly
  its universal closure.
-/
import OrdinalAnalysis.ACA.Syntax

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder

/-! ### The calculus -/

/-- **Second-order one-sided LK with arithmetical comprehension.**

Foundation's `LO.SecondOrder.Derivation`, verbatim, except that `exs₂` carries
the hypothesis `Arith ψ`. -/
inductive Derivation : SecondOrder.Sequent ℒₒᵣ → Type
  | identity {φ : Proposition ℒₒᵣ} : Derivation [φ, ∼φ]
  | cut {φ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      Derivation (φ :: Γ) → Derivation (∼φ :: Γ) → Derivation Γ
  | wk {Γ Δ : SecondOrder.Sequent ℒₒᵣ} : Derivation Γ → Γ ⊆ Δ → Derivation Δ
  | verum : Derivation [⊤]
  | and {φ ψ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      Derivation (φ :: Γ) → Derivation (ψ :: Γ) → Derivation (φ ⋏ ψ :: Γ)
  | or {φ ψ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      Derivation (φ :: ψ :: Γ) → Derivation (φ ⋎ ψ :: Γ)
  | all₁ {φ : Semiproposition ℒₒᵣ 0 1} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      Derivation (φ.free₀ :: SecondOrder.Sequent.shift₀ Γ) → Derivation ((∀¹ φ) :: Γ)
  | exs₁ {φ : Semiproposition ℒₒᵣ 0 1} {t : FirstOrder.Semiterm ℒₒᵣ ℕ 0}
      {Γ : SecondOrder.Sequent ℒₒᵣ} :
      Derivation (φ/[t] :: Γ) → Derivation ((∃¹ φ) :: Γ)
  | all₂ {φ : Semiproposition ℒₒᵣ 1 0} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      Derivation (φ.free₁ :: SecondOrder.Sequent.shift₁ Γ) → Derivation ((∀² φ) :: Γ)
  /-- **Arithmetical comprehension.**  The only comprehension of the system: the
  witness `ψ` for a set quantifier must have no set quantifier of its own. -/
  | exs₂ {φ : Semiproposition ℒₒᵣ 1 0} {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1}
      {Γ : SecondOrder.Sequent ℒₒᵣ} (hψ : Arith ψ) :
      Derivation (φ/⟦ψ⟧ :: Γ) → Derivation ((∃² φ) :: Γ)

namespace Derivation

/-- Transport a derivation along an equality of sequents. -/
def cast {Γ Δ : SecondOrder.Sequent ℒₒᵣ} (d : Derivation Γ) (h : Γ = Δ) : Derivation Δ := h ▸ d

/-- Every derivation of the restricted calculus is one of Foundation's full
second-order LK; the restriction only removes rules. -/
def toFull : {Γ : SecondOrder.Sequent ℒₒᵣ} → Derivation Γ → SecondOrder.Derivation Γ
  | _, identity => .identity
  | _, cut dp dn => .cut (toFull dp) (toFull dn)
  | _, wk d h => .wk (toFull d) h
  | _, verum => .verum
  | _, and dp dq => .and (toFull dp) (toFull dq)
  | _, or d => .or (toFull d)
  | _, all₁ d => .all₁ (toFull d)
  | _, exs₁ d => .exs₁ (toFull d)
  | _, all₂ d => .all₂ (toFull d)
  | _, exs₂ _ d => .exs₂ (toFull d)

end Derivation

/-! ### Provability from a schema -/

/-- A derivation of `φ` from finitely many instances of the schema `𝓢`.  The
shape is Foundation's `Schema.Derivation`. -/
structure SchemaDerivation (𝓢 : Set (Proposition ℒₒᵣ)) (φ : Proposition ℒₒᵣ) where
  /-- The axioms used. -/
  axioms : SecondOrder.Sequent ℒₒᵣ
  /-- A derivation of `φ` together with the negated axioms. -/
  derivation : Derivation (φ :: ∼axioms)
  /-- Each of them really is an axiom. -/
  isInstance : ∀ ψ ∈ axioms, ψ ∈ 𝓢

/-- `𝓢 ⊢ φ`. -/
def Provable (𝓢 : Set (Proposition ℒₒᵣ)) (φ : Proposition ℒₒᵣ) : Prop :=
  Nonempty (SchemaDerivation 𝓢 φ)

theorem provable_iff {𝓢 : Set (Proposition ℒₒᵣ)} {φ : Proposition ℒₒᵣ} :
    Provable 𝓢 φ ↔
      ∃ Γ : SecondOrder.Sequent ℒₒᵣ, (∀ ψ ∈ Γ, ψ ∈ 𝓢) ∧ Nonempty (Derivation (φ :: ∼Γ)) :=
  ⟨fun ⟨d⟩ => ⟨d.axioms, d.isInstance, ⟨d.derivation⟩⟩,
   fun ⟨Γ, hΓ, ⟨d⟩⟩ => ⟨⟨Γ, d, hΓ⟩⟩⟩

/-- Provability is monotone in the schema. -/
theorem provable_mono {𝓢 𝓣 : Set (Proposition ℒₒᵣ)} (h : 𝓢 ⊆ 𝓣) {φ : Proposition ℒₒᵣ}
    (hφ : Provable 𝓢 φ) : Provable 𝓣 φ := by
  obtain ⟨d⟩ := hφ
  exact ⟨⟨d.axioms, d.derivation, fun ψ hψ => h (d.isInstance ψ hψ)⟩⟩

/-! ### The axioms -/

/-- `0`, as an `ℒₒᵣ`-term. -/
abbrev zeroT {n : ℕ} : FirstOrder.Semiterm ℒₒᵣ ℕ n := ‘0’

/-- `x + 1`, as an `ℒₒᵣ`-term in one bound variable. -/
abbrev succT : FirstOrder.Semiterm ℒₒᵣ ℕ 1 := ‘#0 + 1’

/-- **The set induction axiom.**  A single `∀²`-proposition, not a schema:
`∀X ((0 ∈ X ∧ ∀x (x ∈ X → x+1 ∈ X)) → ∀x x ∈ X)`.  This is the induction of
`ACA₀`; it is *much* weaker than induction for arbitrary second-order formulas,
and the whole `ε₀` vs `ε_{ε₀}` gap is the difference. -/
def setInduction : Proposition ℒₒᵣ :=
  ∀² ((((zeroT : FirstOrder.Semiterm ℒₒᵣ ℕ 0) ∈# (0 : Fin 1)) ⋏
        (∀¹ (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)) 🡒
          ((succT : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)))))
      🡒 (∀¹ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1))))

/-- **A comprehension axiom.**  `∃X ∀x (x ∈ X ↔ ψ(x))`, with the number
parameters of `ψ` left free — see the file header for why there is no universal
closure.  Only the *arithmetical* `ψ` are taken as axioms (`ACA₀` below). -/
def compAx (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) : Proposition ℒₒᵣ :=
  ∃² (∀¹ (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)) 🡘 ψ.bmap Fin.elim0))

/-- The lift of a first-order *sentence* to a proposition of the second-order
syntax. -/
def liftSentence (σ : FirstOrder.Sentence ℒₒᵣ) : Proposition ℒₒᵣ :=
  lift (FirstOrder.Rewriting.emb σ)

/-- The equality axioms of `ℒₒᵣ`, lifted. -/
def eqAxioms : Set (Proposition ℒₒᵣ) := liftSentence '' (𝗘𝗤 ℒₒᵣ)

/-- The axioms of `PA⁻`, lifted. -/
def paMinus : Set (Proposition ℒₒᵣ) := liftSentence '' 𝗣𝗔⁻

/-- **An induction axiom for an arbitrary second-order formula.**  The shape of
`FirstOrder.Arithmetic.succInd`, with the antecedents joined by `⋏` so that it
is literally parallel to `setInduction` (the two shapes differ only by
associativity of `⋎` after de Morgan). -/
def indScheme (φ : Semiformula ℒₒᵣ ℕ ℕ 0 1) : Proposition ℒₒᵣ :=
  ((φ/[(zeroT : FirstOrder.Semiterm ℒₒᵣ ℕ 0)]) ⋏ (∀¹ (φ 🡒 φ/[(succT : FirstOrder.Semiterm ℒₒᵣ ℕ 1)])))
    🡒 (∀¹ φ)

/-- **`ACA₀`**: equality, `PA⁻`, the set induction axiom, and arithmetical
comprehension. -/
def ACA₀ : Set (Proposition ℒₒᵣ) :=
  eqAxioms ∪ paMinus ∪ {setInduction} ∪ {χ | ∃ ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1, Arith ψ ∧ χ = compAx ψ}

set_option linter.dupNamespace false in
/-- **`ACA`**: `ACA₀` with induction for *every* second-order formula. -/
def ACA : Set (Proposition ℒₒᵣ) :=
  ACA₀ ∪ {χ | ∃ φ : Semiformula ℒₒᵣ ℕ ℕ 0 1, χ = indScheme φ}

theorem setInduction_mem_ACA₀ : setInduction ∈ ACA₀ :=
  Or.inl (Or.inr rfl)

theorem compAx_mem_ACA₀ {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1} (hψ : Arith ψ) : compAx ψ ∈ ACA₀ :=
  Or.inr ⟨ψ, hψ, rfl⟩

theorem eqAxioms_subset_ACA₀ : eqAxioms ⊆ ACA₀ :=
  fun _ h => Or.inl (Or.inl (Or.inl h))

theorem paMinus_subset_ACA₀ : paMinus ⊆ ACA₀ :=
  fun _ h => Or.inl (Or.inl (Or.inr h))

theorem indScheme_mem_ACA (φ : Semiformula ℒₒᵣ ℕ ℕ 0 1) : indScheme φ ∈ ACA :=
  Or.inr ⟨φ, rfl⟩

/-- `ACA₀ ⊆ ACA`. -/
theorem ACA₀_subset_ACA : ACA₀ ⊆ ACA := Set.subset_union_left

/-- **Everything `ACA₀` proves, `ACA` proves.** -/
theorem aca_provable_mono {φ : Proposition ℒₒᵣ} (h : Provable ACA₀ φ) : Provable ACA φ :=
  provable_mono ACA₀_subset_ACA h

end OrdinalAnalysis.ACA
