/-
  The atomic axioms of the ramified calculus, and the side conditions the
  reduction lemma needs of them.

  `Omega/Calculus.lean`'s `Literals` asks two things of an axiom set: every axiom
  is a literal, and no axiom is asserted together with its negation.  For `LRA`
  that is not enough, and `Ramified/Calculus.lean` records the missing condition
  as `MemFree`: **no axiom is a set atom**.  The reason is structural rather than
  semantic.  A set atom `n̄ ∈̇_ν ā` *is* a literal, so `Literals` alone permits it
  as an axiom; but then a (Pr) inference and an axiom could be the two sides of a
  cut, and that pair has no principal reduction — the (Pr) side offers the
  unfolding `A_a(n̄)` while the axiom side offers nothing at all.  Every other
  rule is safe for exactly the reason `Literals.literal` was introduced: an axiom
  is never the principal formula of a propositional or quantifier rule.

  This is the exact analogue of `Gentzen/StandardLX.lean`'s `trueArithLits_xfree`
  (there: no axiom is `X(t)` or `∼X(t)`), and, as there, the intended axioms
  satisfy it on the nose.

  `trueArithLitsR` is that intended set: the closed literals of the *arithmetic*
  part of `LRA` that are true in `ℕ`.  Two differences from `StandardLX.lean`.

  * `MemFree` is proved **syntactically**, off the rank: an arithmetic symbol is
    `Sum.inl r`, `relLevel (Sum.inl r) = none`, so `rank = 0`, whereas a level-`ν`
    set atom has rank `ω^ν > 0`.  No semantics is involved.  `StandardLX.lean`
    had to argue semantically because its exclusion (`X`) also has rank `0`; the
    analogue here is `xfree`, and that one does go through a symbol projection.

  * The reading of the fresh symbols is fixed rather than a parameter.  The
    parametric family `stdLX P` exists in `Gentzen/` because the boundedness
    lemma reinterprets `X`; the ramified boundedness port will want the same
    thing and should reinstate the parameter at that point.  Nothing here
    depends on the choice: the axioms are `X`- and `∈̇`-free by construction.
-/
import OrdinalAnalysis.Ramified.Calculus

set_option autoImplicit false
set_option warn.classDefReducibility false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### Two facts about negation

`ACAOmega/Calculus.lean` proves these for the second-order syntax; the
first-order forms are the same one-liners and the reduction lemma's `identity`
case needs them. -/

theorem neg_ne_self {n : ℕ} (φ : Semiformula LRA ℕ n) : ∼φ ≠ φ := by
  cases φ using Semiformula.cases' <;> simp

theorem neg_injective {n : ℕ} {φ ψ : Semiformula LRA ℕ n} (h : ∼φ = ∼ψ) : φ = ψ := by
  have := congrArg (fun χ => ∼χ) h
  simpa using this

/-! ### `MemFree`, in the shapes the reduction lemma consumes

`Ramified/Calculus.lean` defines `MemFree A` as "every axiom has rank `0`" and
derives `ne_memAt`/`ne_nmemAt`.  The reduction lemma also meets the *negated*
forms: in its `atom` case the cut formula is the axiom `ψ`, and a (Pr) handler
presents `∼ψ` as a set atom. -/

namespace MemFree

variable {A : Literals LRA} (h : MemFree A)
include h

/-- The negation of an axiom is not a set atom either. -/
theorem neg_ne_memAt {φ : Proposition LRA} (hφ : A.T φ) (ν : Lv) (t s : SyntacticTerm LRA) :
    ∼φ ≠ memAt ν t s := by
  intro he
  have h0 : rank (∼φ) = 0 := by rw [rank_neg]; exact h φ hφ
  rw [he, rank_memAt] at h0
  exact absurd h0.symm (ne_of_lt (omegaPowLv_pos ν))

/-- The negation of an axiom is not a negated set atom either. -/
theorem neg_ne_nmemAt {φ : Proposition LRA} (hφ : A.T φ) (ν : Lv) (t s : SyntacticTerm LRA) :
    ∼φ ≠ nmemAt ν t s := by
  intro he
  have h0 : rank (∼φ) = 0 := by rw [rank_neg]; exact h φ hφ
  rw [he, rank_nmemAt] at h0
  exact absurd h0.symm (ne_of_lt (omegaPowLv_pos ν))

end MemFree

/-! ### A reading of `LRA`

Arithmetic standard, the fresh symbols empty.  Deliberately not an instance. -/

/-- The fresh symbols, read as empty.  `RALang` has no function symbols. -/
def raStruc : Structure RALang ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ _ _ => False

/-- **A standard model of `LRA`**: arithmetic standard, `X` and every `∈̇_ν`
empty. -/
def stdLRA : Structure LRA ℕ := Structure.add ℒₒᵣ RALang ℕ (str₂ := raStruc)

/-- Truth of a closed arithmetic formula in `ℕ`.  For the formulas the axiom set
is built from — closed, `X`-free and `∈̇`-free — the reading of the fresh
symbols and the assignment are both irrelevant; fixing them keeps the axiom set
a predicate on formulas alone. -/
def TrueNR (φ : Proposition LRA) : Prop :=
  Semiformula.Eval (s := stdLRA) ![] (fun _ => 0) φ

@[simp] theorem trueNR_neg (φ : Proposition LRA) : TrueNR (∼φ) ↔ ¬TrueNR φ := by
  simp [TrueNR]

/-! ### The closed arithmetic literals -/

/-- `φ` is an **arithmetic literal with closed arguments**: `rel r v` or
`nrel r v` with `r` a relation symbol of `ℒₒᵣ` — that is, tagged `Sum.inl`, so
never `X` and never a set atom — and every argument closed. -/
def IsArithLitR (φ : Proposition LRA) : Prop :=
  ∃ (k : ℕ) (r : Language.Rel ℒₒᵣ k) (v : Fin k → SyntacticTerm LRA),
    (φ = Semiformula.rel (Sum.inl r) v ∨ φ = Semiformula.nrel (Sum.inl r) v) ∧
      ∀ i, (v i).freeVariables = ∅

theorem isArithLitR_rel {k : ℕ} (r : Language.Rel ℒₒᵣ k) (v : Fin k → SyntacticTerm LRA)
    (hv : ∀ i, (v i).freeVariables = ∅) :
    IsArithLitR (Semiformula.rel (Sum.inl r) v) := ⟨k, r, v, Or.inl rfl, hv⟩

theorem isArithLitR_nrel {k : ℕ} (r : Language.Rel ℒₒᵣ k) (v : Fin k → SyntacticTerm LRA)
    (hv : ∀ i, (v i).freeVariables = ∅) :
    IsArithLitR (Semiformula.nrel (Sum.inl r) v) := ⟨k, r, v, Or.inr rfl, hv⟩

/-- The class is closed under negation. -/
theorem isArithLitR_neg {φ : Proposition LRA} (h : IsArithLitR φ) : IsArithLitR (∼φ) := by
  obtain ⟨k, r, v, (rfl | rfl), hcl⟩ := h
  · exact ⟨k, r, v, Or.inr (Semiformula.neg_rel _ _), hcl⟩
  · exact ⟨k, r, v, Or.inl (Semiformula.neg_nrel _ _), hcl⟩

/-- An arithmetic literal is closed.  As in `Gentzen/StandardLX.lean` the two
`rfl`-lemmas are applied by `Eq.trans` rather than by `rw`: a term carrying
`Sum.inl r : LRA.Rel k` is not type-correct at reducible transparency. -/
theorem freeVariables_of_isArithLitR {φ : Proposition LRA} (h : IsArithLitR φ) :
    φ.freeVariables = ∅ := by
  have hb : ∀ (k : ℕ) (v : Fin k → SyntacticTerm LRA), (∀ i, (v i).freeVariables = ∅) →
      (Finset.biUnion Finset.univ fun i => (v i).freeVariables) = (∅ : Finset ℕ) := by
    intro k v hv
    ext x
    simp [hv]
  obtain ⟨k, r, v, (rfl | rfl), hcl⟩ := h
  · exact (Semiformula.freeVariables_rel _ v).trans (hb k v hcl)
  · exact (Semiformula.freeVariables_nrel _ v).trans (hb k v hcl)

/-- **An arithmetic literal has rank `0`.**  `relLevel (Sum.inl r) = none`, so
`atomRank (Sum.inl r) = 0`; this is `MemFree` in one line, and it is the reason
that condition costs nothing for the intended axioms. -/
theorem rank_of_isArithLitR {φ : Proposition LRA} (h : IsArithLitR φ) : rank φ = 0 := by
  obtain ⟨k, r, v, (rfl | rfl), -⟩ := h <;> rfl

/-- **An arithmetic literal has level `0`.**  The companion of
`rank_of_isArithLitR`, in the form the level bookkeeping wants. -/
theorem lvlOf_of_isArithLitR {φ : Proposition LRA} (h : IsArithLitR φ) : lvlOf φ = 0 := by
  obtain ⟨k, r, v, (rfl | rfl), -⟩ := h <;> rfl

/-! ### The axiom set -/

/-- **The atomic axioms of the ramified calculus**: the closed arithmetic
literals true in `ℕ`.

`literal` is the first conjunct with the arithmetic symbol re-tagged `Sum.inl`;
`consistent` is `Eval` of a negation being the negation of `Eval`. -/
def trueArithLitsR : Literals LRA where
  T := fun φ => IsArithLitR φ ∧ TrueNR φ
  literal := by
    rintro φ ⟨⟨k, r, v, hv, -⟩, -⟩
    exact ⟨k, Sum.inl r, v, hv⟩
  consistent := by
    rintro φ ⟨-, ht⟩ ⟨-, hf⟩
    exact (trueNR_neg φ).mp hf ht

@[simp] theorem trueArithLitsR_T (φ : Proposition LRA) :
    trueArithLitsR.T φ ↔ IsArithLitR φ ∧ TrueNR φ := Iff.rfl

/-- **The axiom set is mem-free**, i.e. it satisfies the new obligation of
`Ramified/Calculus.lean`.  Every axiom is an arithmetic literal, hence of rank
`0`, while a level-`ν` set atom has rank `ω^ν`. -/
theorem memFree_trueArithLitsR : MemFree trueArithLitsR :=
  fun _ h => rank_of_isArithLitR h.1

/-! ### The axiom set is also `X`-free

`MemFree` is about rank and so cannot see `X`, which is levelless.  The
exclusion of `X`-atoms — `Gentzen/StandardLX.lean`'s `trueArithLits_xfree`, the
condition the boundedness lemma reads — is a statement about the *tag* of the
relation symbol instead, and is proved by a projection because
`Semiformula.rel`'s arity is an index. -/

/-- `true` exactly when the head symbol comes from the fresh summand. -/
def freshHead {n : ℕ} : Semiformula LRA ℕ n → Bool
  |  .rel r _ => r.isRight
  | .nrel r _ => r.isRight
  |         _ => false

@[simp] theorem freshHead_Xat {n : ℕ} (t : Semiterm LRA ℕ n) : freshHead (Xat t) = true := rfl

@[simp] theorem freshHead_neg_Xat {n : ℕ} (t : Semiterm LRA ℕ n) :
    freshHead (∼Xat t) = true := rfl

@[simp] theorem freshHead_memAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    freshHead (memAt ν t s) = true := rfl

@[simp] theorem freshHead_nmemAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    freshHead (nmemAt ν t s) = true := rfl

theorem freshHead_of_isArithLitR {φ : Proposition LRA} (h : IsArithLitR φ) :
    freshHead φ = false := by
  obtain ⟨k, r, v, (rfl | rfl), -⟩ := h <;> rfl

/-- **No axiom is an `X`-atom or a negated `X`-atom.**  The `LRA` form of
`trueArithLits_xfree`. -/
theorem trueArithLitsR_xfree {φ : Proposition LRA} (h : trueArithLitsR.T φ)
    (t : SyntacticTerm LRA) : φ ≠ Xat t ∧ φ ≠ ∼(Xat t) := by
  constructor <;> intro he <;>
    [ (have := congrArg freshHead he) ; (have := congrArg freshHead he) ] <;>
    rw [freshHead_of_isArithLitR h.1] at this <;> simp at this

/-! ### The normalisation side

`InstantiationR` asks for `rank_nf` and `num_inj` on top of `Instantiation`.
The prototype discharged both for the standard family; the two lemmas below
record that the standard family's normaliser is the identity, so "the axioms are
in normal form" is vacuous for it — there is nothing for an embedding to
normalise away. -/

@[simp] theorem std_nf (φ : Proposition LRA) : InstantiationR.std.nf φ = φ := rfl

@[simp] theorem std_num : InstantiationR.std.num = num := rfl

@[simp] theorem std_inst (φ : Semiproposition LRA 1) (n : ℕ) :
    InstantiationR.std.inst φ n = φ/[num n] :=
  InstantiationR.raw_inst num num_injective φ n

end Ramified

end OrdinalAnalysis
