/-
  The **syntax layer**
  of `ACA_∞`, on top of Foundation's monadic second-order formulas.

  Three things live here.

  * `Arith` — "no second-order quantifier".  Atoms `t ∈# X`, `t ∈& X` are
    allowed; only `∀²`/`∃²` are forbidden.  This is Afshari–Rathjen's class of
    *arithmetical* formulas, and it is the only comprehension the calculus of
    `LK.lean` admits: the `∃²` rule may instantiate a set quantifier by an
    arithmetical formula and by nothing else.  It is decidable, closed under
    negation, under first-order rewriting, and under second-order substitution.

  * `rank` — the cut rank of `ACA_∞`, valued in `NONote` rather than in `ℕ`.
    Propositional and number-quantifier steps pay a successor; a set quantifier
    pays `max (rank φ + 1) ω`.  So arithmetical formulas have finite rank and
    every formula with a set quantifier has rank `≥ ω`; the whole point is
    `rank_subst₂_lt`, which says that instantiating `∃² φ` by an *arithmetical*
    formula lands strictly below `rank (∃² φ)`.  That is what makes the
    second-order `∃₂` rule reduce the cut rank, and it is the only reason the
    calculus terminates at `ε_{ε₀}` rather than nowhere.

  * `TISO` — transfinite induction along the coded ordering, written with a
    genuine free *set* variable `X = (0 : ℕ)` in place of `LowerSyntax`'s fresh
    predicate symbol `Xat`.  It is arithmetical, hence of finite rank.

  Everything is stated for an arbitrary language `L`; only `TISO` fixes `ℒₒᵣ`.
-/
import Foundation.SecondOrder.Derivation
import Foundation.SecondOrder.Semantics
import OrdinalAnalysis.Proof.Bridge
import OrdinalAnalysis.Ordinal.OmegaPow
import OrdinalAnalysis.Gentzen.CodedNotation

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder

/-! ### `ω`, as a notation

`NONote` is the type of ordinal notations below `ε₀`, and `ω` is the notation
`ω ^ 1`.  Two facts are needed and no more: every `ofNat n` lies below it, and it
is closed under `NONote.succ` — the latter because `NONote.succ` is `· ⊕ 1` and
`ω ^ a` is additively indecomposable for the natural sum
(`NONote.nadd_lt_omegaPow`). -/

/-- `ω`, as a normal-form notation. -/
def omegaN : NONote := NONote.omegaPow (NONote.ofNat 1)

theorem ofNat_lt_omegaN (n : ℕ) : NONote.ofNat n < omegaN := by
  have h1 : ONote.repr (NONote.ofNat 1).1 = 1 := by
    show ONote.repr (ONote.ofNat 1) = 1
    simp
  show ONote.repr (ONote.ofNat n) < ONote.repr (NONote.omegaPow (NONote.ofNat 1)).1
  rw [NONote.repr_omegaPow, h1, ONote.repr_ofNat, Ordinal.opow_one]
  exact Ordinal.natCast_lt_omega0 n

theorem zero_lt_omegaN : (0 : NONote) < omegaN := by
  have h : NONote.ofNat 0 < omegaN := ofNat_lt_omegaN 0
  have e : (NONote.ofNat 0 : NONote) = 0 := rfl
  rwa [e] at h

theorem one_lt_omegaN : NONote.one < omegaN := by
  show ONote.repr (NONote.one).1 < ONote.repr (NONote.omegaPow (NONote.ofNat 1)).1
  have h1 : ONote.repr (NONote.ofNat 1).1 = 1 := by
    show ONote.repr (ONote.ofNat 1) = 1
    simp
  rw [NONote.repr_omegaPow, h1, Ordinal.opow_one, NONote.repr_one]
  exact Ordinal.one_lt_omega0

/-- `ω` is closed under successor. -/
theorem succ_lt_omegaN {a : NONote} (h : a < omegaN) : NONote.succ a < omegaN :=
  NONote.nadd_lt_omegaPow h one_lt_omegaN

/-- Contrapositive form, used constantly below: if a successor has reached `ω`,
its argument had already. -/
theorem le_of_le_succ {a : NONote} (h : omegaN ≤ NONote.succ a) : omegaN ≤ a := by
  by_contra hc
  exact absurd (succ_lt_omegaN (not_le.mp hc)) (not_lt.mpr h)

variable {L : FirstOrder.Language} {Ξ ξ : Type*}

/-! ### Arithmetical formulas

`Arith φ` says that `φ` contains no second-order quantifier.  Set *atoms* are
allowed — this is Afshari–Rathjen's `ACA_∞` notion, in which the arithmetical
formulas are exactly the ones the predicator `{x | A(x)}` may be built from. -/

/-- **`φ` has no second-order quantifier.** -/
def Arith {N n : ℕ} : Semiformula L Ξ ξ N n → Prop
  |  .rel _ _ => True
  | .nrel _ _ => True
  |    _ ∈# _ => True
  |    _ ∉# _ => True
  |    _ ∈& _ => True
  |    _ ∉& _ => True
  |         ⊤ => True
  |         ⊥ => True
  |     φ ⋏ ψ => Arith φ ∧ Arith ψ
  |     φ ⋎ ψ => Arith φ ∧ Arith ψ
  |      ∀¹ φ => Arith φ
  |      ∃¹ φ => Arith φ
  |      ∀² _ => False
  |      ∃² _ => False

section ArithSimp

variable {N n : ℕ}

@[simp] theorem arith_rel {k : ℕ} (r : L.Rel k) (v : Fin k → FirstOrder.Semiterm L ξ n) :
    Arith (.rel r v : Semiformula L Ξ ξ N n) := trivial

@[simp] theorem arith_nrel {k : ℕ} (r : L.Rel k) (v : Fin k → FirstOrder.Semiterm L ξ n) :
    Arith (.nrel r v : Semiformula L Ξ ξ N n) := trivial

@[simp] theorem arith_bvar (X : Fin N) (t : FirstOrder.Semiterm L ξ n) :
    Arith (t ∈# X : Semiformula L Ξ ξ N n) := trivial

@[simp] theorem arith_nbvar (X : Fin N) (t : FirstOrder.Semiterm L ξ n) :
    Arith (t ∉# X : Semiformula L Ξ ξ N n) := trivial

@[simp] theorem arith_fvar (X : Ξ) (t : FirstOrder.Semiterm L ξ n) :
    Arith (t ∈& X : Semiformula L Ξ ξ N n) := trivial

@[simp] theorem arith_nfvar (X : Ξ) (t : FirstOrder.Semiterm L ξ n) :
    Arith (t ∉& X : Semiformula L Ξ ξ N n) := trivial

@[simp] theorem arith_verum : Arith (⊤ : Semiformula L Ξ ξ N n) := trivial

@[simp] theorem arith_falsum : Arith (⊥ : Semiformula L Ξ ξ N n) := trivial

@[simp] theorem arith_and (φ ψ : Semiformula L Ξ ξ N n) :
    Arith (φ ⋏ ψ) ↔ Arith φ ∧ Arith ψ := Iff.rfl

@[simp] theorem arith_or (φ ψ : Semiformula L Ξ ξ N n) :
    Arith (φ ⋎ ψ) ↔ Arith φ ∧ Arith ψ := Iff.rfl

@[simp] theorem arith_all₁ (φ : Semiformula L Ξ ξ N (n + 1)) :
    Arith (∀¹ φ) ↔ Arith φ := Iff.rfl

@[simp] theorem arith_exs₁ (φ : Semiformula L Ξ ξ N (n + 1)) :
    Arith (∃¹ φ) ↔ Arith φ := Iff.rfl

@[simp] theorem arith_all₂ (φ : Semiformula L Ξ ξ (N + 1) n) :
    ¬Arith (∀² φ) := id

@[simp] theorem arith_exs₂ (φ : Semiformula L Ξ ξ (N + 1) n) :
    ¬Arith (∃² φ) := id

end ArithSimp

/-- Arithmeticity is decidable. -/
def decArith {N n : ℕ} : (φ : Semiformula L Ξ ξ N n) → Decidable (Arith φ)
  |  .rel _ _ => isTrue trivial
  | .nrel _ _ => isTrue trivial
  |    _ ∈# _ => isTrue trivial
  |    _ ∉# _ => isTrue trivial
  |    _ ∈& _ => isTrue trivial
  |    _ ∉& _ => isTrue trivial
  |         ⊤ => isTrue trivial
  |         ⊥ => isTrue trivial
  |     φ ⋏ ψ => @instDecidableAnd _ _ (decArith φ) (decArith ψ)
  |     φ ⋎ ψ => @instDecidableAnd _ _ (decArith φ) (decArith ψ)
  |      ∀¹ φ => decArith φ
  |      ∃¹ φ => decArith φ
  |      ∀² _ => isFalse id
  |      ∃² _ => isFalse id

instance instDecidablePredArith {N n : ℕ} :
    DecidablePred (Arith : Semiformula L Ξ ξ N n → Prop) := decArith

/-- Arithmeticity is invariant under negation. -/
@[simp] theorem arith_neg {N n : ℕ} (φ : Semiformula L Ξ ξ N n) :
    Arith (∼φ) ↔ Arith φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- Arithmeticity is invariant under first-order rewriting. -/
@[simp] theorem arith_rew {N : ℕ} {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}
    (ω : FirstOrder.Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N n₁) :
    Arith (ω ▹ φ) ↔ Arith φ := by
  induction φ using Semiformula.rec' generalizing n₂ <;>
    simp [Semiformula.rew_rel, Semiformula.rew_nrel, *]

/-- Arithmeticity is invariant under the second-order `bmap`. -/
@[simp] theorem arith_bmap {N M n : ℕ} (f : Fin N → Fin M) (φ : Semiformula L Ξ ξ N n) :
    Arith (φ.bmap f) ↔ Arith φ := by
  induction φ using Semiformula.rec' generalizing M <;> simp [*]

/-- Arithmeticity is preserved by a second-order substitution all of whose
components are arithmetical.

Stated for a general `SecondOrder.Rew`, because the `∀²`/`∃²` cases of the
`rank` analysis below need the same induction with `Ω`.  Here they are vacuous:
`Arith` rules out set quantifiers outright. -/
theorem arith_app {N₁ n : ℕ} (φ : Semiformula L Ξ ξ N₁ n) (hφ : Arith φ) :
    ∀ {N₂ : ℕ} (Ω : SecondOrder.Rew L Ξ N₁ Ξ N₂ ξ),
      (∀ X, Arith (Ω.bv X)) → (∀ X, Arith (Ω.fv X)) → Arith (Ω.app φ) := by
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₂ Ω _ _; simp
  | hNrel r v => intro N₂ Ω _ _; simp
  | hBvar X t => intro N₂ Ω hb _; simpa using hb X
  | hNbvar X t => intro N₂ Ω hb _; simpa using hb X
  | hFvar X t => intro N₂ Ω _ hf; simpa using hf X
  | hNfvar X t => intro N₂ Ω _ hf; simpa using hf X
  | hVerum => intro N₂ Ω _ _; simp
  | hFalsum => intro N₂ Ω _ _; simp
  | hAnd φ ψ ihφ ihψ =>
      intro N₂ Ω hb hf
      exact ⟨ihφ hφ.1 Ω hb hf, ihψ hφ.2 Ω hb hf⟩
  | hOr φ ψ ihφ ihψ =>
      intro N₂ Ω hb hf
      exact ⟨ihφ hφ.1 Ω hb hf, ihψ hφ.2 Ω hb hf⟩
  | hAll₁ φ ih => intro N₂ Ω hb hf; exact ih hφ Ω hb hf
  | hExs₁ φ ih => intro N₂ Ω hb hf; exact ih hφ Ω hb hf
  | hAll₂ φ _ => exact absurd hφ (arith_all₂ φ)
  | hExs₂ φ _ => exact absurd hφ (arith_exs₂ φ)

/-- **Arithmeticity survives second-order substitution.**  Substituting an
arithmetical `ψ` for the single bound set variable of an arithmetical `φ` gives
an arithmetical formula — the closure property that makes the `∃₂` rule of
`LK.lean` an *arithmetical* comprehension rule. -/
theorem arith_subst₂ {φ : Semiproposition L 1 0} {ψ : Semiformula L ℕ ℕ 0 1}
    (hφ : Arith φ) (hψ : Arith ψ) : Arith (φ/⟦ψ⟧) := by
  refine arith_app φ hφ (SecondOrder.Rew.subst ![ψ]) (fun X => ?_) (fun X => ?_)
  · have : (SecondOrder.Rew.subst ![ψ]).bv X = ψ := by
      simp only [SecondOrder.Rew.subst_bv]
      exact Matrix.cons_val_fin_one _ _ X
    rw [this]; exact hψ
  · simp

/-! ### The rank

Afshari–Rathjen's cut rank for `ACA_∞`: literals have rank `0`, propositional
and number-quantifier steps pay a successor, and a set quantifier pays
`max (rank φ + 1) ω`.  The rank is an *ordinal* notation, not a natural number,
because the second-order clause pushes it to `ω` and the first-order clauses then
walk it up through `ω + k`. -/

/-- **The cut rank of `ACA_∞`.** -/
def rank {N n : ℕ} : Semiformula L Ξ ξ N n → NONote
  |  .rel _ _ => 0
  | .nrel _ _ => 0
  |    _ ∈# _ => 0
  |    _ ∉# _ => 0
  |    _ ∈& _ => 0
  |    _ ∉& _ => 0
  |         ⊤ => 0
  |         ⊥ => 0
  |     φ ⋏ ψ => NONote.succ (max (rank φ) (rank ψ))
  |     φ ⋎ ψ => NONote.succ (max (rank φ) (rank ψ))
  |      ∀¹ φ => NONote.succ (rank φ)
  |      ∃¹ φ => NONote.succ (rank φ)
  |      ∀² φ => max (NONote.succ (rank φ)) omegaN
  |      ∃² φ => max (NONote.succ (rank φ)) omegaN

section RankSimp

variable {N n : ℕ}

@[simp] theorem rank_rel {k : ℕ} (r : L.Rel k) (v : Fin k → FirstOrder.Semiterm L ξ n) :
    rank (.rel r v : Semiformula L Ξ ξ N n) = 0 := rfl

@[simp] theorem rank_nrel {k : ℕ} (r : L.Rel k) (v : Fin k → FirstOrder.Semiterm L ξ n) :
    rank (.nrel r v : Semiformula L Ξ ξ N n) = 0 := rfl

@[simp] theorem rank_bvar (X : Fin N) (t : FirstOrder.Semiterm L ξ n) :
    rank (t ∈# X : Semiformula L Ξ ξ N n) = 0 := rfl

@[simp] theorem rank_nbvar (X : Fin N) (t : FirstOrder.Semiterm L ξ n) :
    rank (t ∉# X : Semiformula L Ξ ξ N n) = 0 := rfl

@[simp] theorem rank_fvar (X : Ξ) (t : FirstOrder.Semiterm L ξ n) :
    rank (t ∈& X : Semiformula L Ξ ξ N n) = 0 := rfl

@[simp] theorem rank_nfvar (X : Ξ) (t : FirstOrder.Semiterm L ξ n) :
    rank (t ∉& X : Semiformula L Ξ ξ N n) = 0 := rfl

@[simp] theorem rank_verum : rank (⊤ : Semiformula L Ξ ξ N n) = 0 := rfl

@[simp] theorem rank_falsum : rank (⊥ : Semiformula L Ξ ξ N n) = 0 := rfl

@[simp] theorem rank_and (φ ψ : Semiformula L Ξ ξ N n) :
    rank (φ ⋏ ψ) = NONote.succ (max (rank φ) (rank ψ)) := rfl

@[simp] theorem rank_or (φ ψ : Semiformula L Ξ ξ N n) :
    rank (φ ⋎ ψ) = NONote.succ (max (rank φ) (rank ψ)) := rfl

@[simp] theorem rank_all₁ (φ : Semiformula L Ξ ξ N (n + 1)) :
    rank (∀¹ φ) = NONote.succ (rank φ) := rfl

@[simp] theorem rank_exs₁ (φ : Semiformula L Ξ ξ N (n + 1)) :
    rank (∃¹ φ) = NONote.succ (rank φ) := rfl

@[simp] theorem rank_all₂ (φ : Semiformula L Ξ ξ (N + 1) n) :
    rank (∀² φ) = max (NONote.succ (rank φ)) omegaN := rfl

@[simp] theorem rank_exs₂ (φ : Semiformula L Ξ ξ (N + 1) n) :
    rank (∃² φ) = max (NONote.succ (rank φ)) omegaN := rfl

/-- A set quantifier always costs at least `ω`. -/
theorem omegaN_le_rank_all₂ (φ : Semiformula L Ξ ξ (N + 1) n) :
    omegaN ≤ rank (∀² φ) := le_max_right _ _

theorem omegaN_le_rank_exs₂ (φ : Semiformula L Ξ ξ (N + 1) n) :
    omegaN ≤ rank (∃² φ) := le_max_right _ _

end RankSimp

/-- The rank does not see negation. -/
@[simp] theorem rank_neg {N n : ℕ} (φ : Semiformula L Ξ ξ N n) :
    rank (∼φ) = rank φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- The rank does not see first-order rewriting. -/
@[simp] theorem rank_rew {N : ℕ} {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}
    (ω : FirstOrder.Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N n₁) :
    rank (ω ▹ φ) = rank φ := by
  induction φ using Semiformula.rec' generalizing n₂ <;>
    simp [Semiformula.rew_rel, Semiformula.rew_nrel, *]

/-- The rank does not see the renaming of bound set variables. -/
@[simp] theorem rank_bmap {N M n : ℕ} (f : Fin N → Fin M) (φ : Semiformula L Ξ ξ N n) :
    rank (φ.bmap f) = rank φ := by
  induction φ using Semiformula.rec' generalizing M <;> simp [*]

/-- The rank does not see a one-point substitution of a term. -/
@[simp] theorem rank_subst₁ {N n : ℕ} (φ : Semiformula L Ξ ξ N 1)
    (t : FirstOrder.Semiterm L ξ n) : rank (φ/[t]) = rank φ := rank_rew _ φ

/-- **Arithmetical formulas have finite rank.** -/
theorem rank_lt_omega_of_arith {N n : ℕ} {φ : Semiformula L Ξ ξ N n} (h : Arith φ) :
    rank φ < omegaN := by
  induction φ using Semiformula.rec' with
  | hRel r v => simpa using zero_lt_omegaN
  | hNrel r v => simpa using zero_lt_omegaN
  | hBvar X t => simpa using zero_lt_omegaN
  | hNbvar X t => simpa using zero_lt_omegaN
  | hFvar X t => simpa using zero_lt_omegaN
  | hNfvar X t => simpa using zero_lt_omegaN
  | hVerum => simpa using zero_lt_omegaN
  | hFalsum => simpa using zero_lt_omegaN
  | hAnd φ ψ ihφ ihψ =>
      simpa using succ_lt_omegaN (max_lt (ihφ h.1) (ihψ h.2))
  | hOr φ ψ ihφ ihψ =>
      simpa using succ_lt_omegaN (max_lt (ihφ h.1) (ihψ h.2))
  | hAll₁ φ ih => simpa using succ_lt_omegaN (ih h)
  | hExs₁ φ ih => simpa using succ_lt_omegaN (ih h)
  | hAll₂ φ _ => exact absurd h (arith_all₂ φ)
  | hExs₂ φ _ => exact absurd h (arith_exs₂ φ)

/-! ### The rank under second-order substitution

The invariant.  If every component of a second-order substitution `Ω` has finite
rank, then applying `Ω`

* keeps a finite rank finite, and
* **leaves an infinite rank alone**.

The second half is the delicate one, and it is what makes `rank_subst₂_lt` true:
once a formula carries a set quantifier its rank is `≥ ω`, and the finite growth
that substitution can cause at the atoms is absorbed by the `max … ω` sitting at
that quantifier. -/

private theorem max_congr_of_omegaN_le {a b a' b' : NONote}
    (ha1 : a < omegaN → a' < omegaN) (ha2 : omegaN ≤ a → a' = a)
    (hb1 : b < omegaN → b' < omegaN) (hb2 : omegaN ≤ b → b' = b)
    (h : omegaN ≤ max a b) : max a' b' = max a b := by
  rcases lt_or_ge a omegaN with hA | hA <;> rcases lt_or_ge b omegaN with hB | hB
  · exact absurd (max_lt hA hB) (not_lt.mpr h)
  · have ha' : a' < omegaN := ha1 hA
    rw [hb2 hB, max_eq_right (le_of_lt (lt_of_lt_of_le ha' hB)),
      max_eq_right (le_of_lt (lt_of_lt_of_le hA hB))]
  · have hb' : b' < omegaN := hb1 hB
    rw [ha2 hA, max_eq_left (le_of_lt (lt_of_lt_of_le hb' hA)),
      max_eq_left (le_of_lt (lt_of_lt_of_le hB hA))]
  · rw [ha2 hA, hb2 hB]

set_option maxHeartbeats 1000000 in
/-- **The rank invariant for second-order substitution.** -/
theorem rank_app {N₁ n : ℕ} (φ : Semiformula L Ξ ξ N₁ n) :
    ∀ {N₂ : ℕ} (Ω : SecondOrder.Rew L Ξ N₁ Ξ N₂ ξ),
      (∀ X, rank (Ω.bv X) < omegaN) → (∀ X, rank (Ω.fv X) < omegaN) →
      (rank φ < omegaN → rank (Ω.app φ) < omegaN) ∧
        (omegaN ≤ rank φ → rank (Ω.app φ) = rank φ) := by
  induction φ using Semiformula.rec' with
  | hRel r v =>
      intro N₂ Ω _ _
      refine ⟨fun h => ?_, fun h => absurd h (not_le.mpr zero_lt_omegaN)⟩
      simpa using zero_lt_omegaN
  | hNrel r v =>
      intro N₂ Ω _ _
      refine ⟨fun h => ?_, fun h => absurd h (not_le.mpr zero_lt_omegaN)⟩
      simpa using zero_lt_omegaN
  | hBvar X t =>
      intro N₂ Ω hb _
      refine ⟨fun _ => ?_, fun h => absurd h (not_le.mpr zero_lt_omegaN)⟩
      simpa using hb X
  | hNbvar X t =>
      intro N₂ Ω hb _
      refine ⟨fun _ => ?_, fun h => absurd h (not_le.mpr zero_lt_omegaN)⟩
      simpa using hb X
  | hFvar X t =>
      intro N₂ Ω _ hf
      refine ⟨fun _ => ?_, fun h => absurd h (not_le.mpr zero_lt_omegaN)⟩
      simpa using hf X
  | hNfvar X t =>
      intro N₂ Ω _ hf
      refine ⟨fun _ => ?_, fun h => absurd h (not_le.mpr zero_lt_omegaN)⟩
      simpa using hf X
  | hVerum =>
      intro N₂ Ω _ _
      refine ⟨fun h => ?_, fun h => absurd h (not_le.mpr zero_lt_omegaN)⟩
      simpa using zero_lt_omegaN
  | hFalsum =>
      intro N₂ Ω _ _
      refine ⟨fun h => ?_, fun h => absurd h (not_le.mpr zero_lt_omegaN)⟩
      simpa using zero_lt_omegaN
  | hAnd φ ψ ihφ ihψ =>
      intro N₂ Ω hb hf
      obtain ⟨hφ1, hφ2⟩ := ihφ Ω hb hf
      obtain ⟨hψ1, hψ2⟩ := ihψ Ω hb hf
      constructor
      · intro h
        rw [rank_and] at h
        have hm : max (rank φ) (rank ψ) < omegaN := lt_trans (NONote.lt_succ _) h
        have h1 : rank φ < omegaN := lt_of_le_of_lt (le_max_left _ _) hm
        have h2 : rank ψ < omegaN := lt_of_le_of_lt (le_max_right _ _) hm
        simpa using succ_lt_omegaN (max_lt (hφ1 h1) (hψ1 h2))
      · intro h
        rw [rank_and] at h ⊢
        have hm : omegaN ≤ max (rank φ) (rank ψ) := le_of_le_succ h
        simp only [LogicalConnective.HomClass.map_and, rank_and]
        rw [max_congr_of_omegaN_le hφ1 hφ2 hψ1 hψ2 hm]
  | hOr φ ψ ihφ ihψ =>
      intro N₂ Ω hb hf
      obtain ⟨hφ1, hφ2⟩ := ihφ Ω hb hf
      obtain ⟨hψ1, hψ2⟩ := ihψ Ω hb hf
      constructor
      · intro h
        rw [rank_or] at h
        have hm : max (rank φ) (rank ψ) < omegaN := lt_trans (NONote.lt_succ _) h
        have h1 : rank φ < omegaN := lt_of_le_of_lt (le_max_left _ _) hm
        have h2 : rank ψ < omegaN := lt_of_le_of_lt (le_max_right _ _) hm
        simpa using succ_lt_omegaN (max_lt (hφ1 h1) (hψ1 h2))
      · intro h
        rw [rank_or] at h ⊢
        have hm : omegaN ≤ max (rank φ) (rank ψ) := le_of_le_succ h
        simp only [LogicalConnective.HomClass.map_or, rank_or]
        rw [max_congr_of_omegaN_le hφ1 hφ2 hψ1 hψ2 hm]
  | hAll₁ φ ih =>
      intro N₂ Ω hb hf
      obtain ⟨h1, h2⟩ := ih Ω hb hf
      constructor
      · intro h
        rw [rank_all₁] at h
        simpa using succ_lt_omegaN (h1 (lt_trans (NONote.lt_succ _) h))
      · intro h
        rw [rank_all₁] at h ⊢
        simp only [SecondOrder.Rew.app_all₀, rank_all₁]
        rw [h2 (le_of_le_succ h)]
  | hExs₁ φ ih =>
      intro N₂ Ω hb hf
      obtain ⟨h1, h2⟩ := ih Ω hb hf
      constructor
      · intro h
        rw [rank_exs₁] at h
        simpa using succ_lt_omegaN (h1 (lt_trans (NONote.lt_succ _) h))
      · intro h
        rw [rank_exs₁] at h ⊢
        simp only [SecondOrder.Rew.app_exs₀, rank_exs₁]
        rw [h2 (le_of_le_succ h)]
  | hAll₂ φ ih =>
      intro N₂ Ω hb hf
      have hbq : ∀ X, rank ((SecondOrder.Rew.q Ω).bv X) < omegaN := by
        refine Fin.cases ?_ ?_
        · simpa using zero_lt_omegaN
        · intro X; simpa using hb X
      have hfq : ∀ X, rank ((SecondOrder.Rew.q Ω).fv X) < omegaN := by
        intro X; simpa using hf X
      obtain ⟨h1, h2⟩ := ih (SecondOrder.Rew.q Ω) hbq hfq
      refine ⟨fun h => absurd h (not_lt.mpr (omegaN_le_rank_all₂ φ)), fun _ => ?_⟩
      simp only [SecondOrder.Rew.app_all₁, rank_all₂]
      rcases lt_or_ge (rank φ) omegaN with hlt | hle
      · rw [max_eq_right (le_of_lt (succ_lt_omegaN (h1 hlt))),
          max_eq_right (le_of_lt (succ_lt_omegaN hlt))]
      · rw [h2 hle]
  | hExs₂ φ ih =>
      intro N₂ Ω hb hf
      have hbq : ∀ X, rank ((SecondOrder.Rew.q Ω).bv X) < omegaN := by
        refine Fin.cases ?_ ?_
        · simpa using zero_lt_omegaN
        · intro X; simpa using hb X
      have hfq : ∀ X, rank ((SecondOrder.Rew.q Ω).fv X) < omegaN := by
        intro X; simpa using hf X
      obtain ⟨h1, h2⟩ := ih (SecondOrder.Rew.q Ω) hbq hfq
      refine ⟨fun h => absurd h (not_lt.mpr (omegaN_le_rank_exs₂ φ)), fun _ => ?_⟩
      simp only [SecondOrder.Rew.app_exs₁, rank_exs₂]
      rcases lt_or_ge (rank φ) omegaN with hlt | hle
      · rw [max_eq_right (le_of_lt (succ_lt_omegaN (h1 hlt))),
          max_eq_right (le_of_lt (succ_lt_omegaN hlt))]
      · rw [h2 hle]

theorem rank_app_lt_omegaN {N₁ N₂ n : ℕ} {φ : Semiformula L Ξ ξ N₁ n}
    (Ω : SecondOrder.Rew L Ξ N₁ Ξ N₂ ξ)
    (hb : ∀ X, rank (Ω.bv X) < omegaN) (hf : ∀ X, rank (Ω.fv X) < omegaN)
    (h : rank φ < omegaN) : rank (Ω.app φ) < omegaN :=
  (rank_app φ Ω hb hf).1 h

theorem rank_app_eq_of_omegaN_le {N₁ N₂ n : ℕ} {φ : Semiformula L Ξ ξ N₁ n}
    (Ω : SecondOrder.Rew L Ξ N₁ Ξ N₂ ξ)
    (hb : ∀ X, rank (Ω.bv X) < omegaN) (hf : ∀ X, rank (Ω.fv X) < omegaN)
    (h : omegaN ≤ rank φ) : rank (Ω.app φ) = rank φ :=
  (rank_app φ Ω hb hf).2 h

/-! ### The key instantiation bound

`rank_subst₂_lt` is what buys the whole calculus: instantiating a set quantifier
by an **arithmetical** formula produces a formula of *strictly smaller* rank.  It
is the second-order analogue of "a substitution instance of `∀x φ` has the rank
of `φ`", and it is the reason `ACA_∞`'s cut elimination terminates. -/

section Subst

variable {φ : Semiproposition L 1 0} {ψ : Semiformula L ℕ ℕ 0 1}

private theorem subst_bv_eq (X : Fin 1) : (SecondOrder.Rew.subst ![ψ]).bv X = ψ := by
  simp only [SecondOrder.Rew.subst_bv]
  exact Matrix.cons_val_fin_one _ _ X

/-- The two halves of the invariant, for the substitution `φ ↦ φ/⟦ψ⟧`. -/
theorem rank_subst₂_lt_omegaN (hψ : Arith ψ) (h : rank φ < omegaN) :
    rank (φ/⟦ψ⟧) < omegaN := by
  refine rank_app_lt_omegaN _ (fun X => ?_) (fun X => ?_) h
  · rw [subst_bv_eq]; exact rank_lt_omega_of_arith hψ
  · simpa using zero_lt_omegaN

theorem rank_subst₂_eq (hψ : Arith ψ) (h : omegaN ≤ rank φ) :
    rank (φ/⟦ψ⟧) = rank φ := by
  refine rank_app_eq_of_omegaN_le _ (fun X => ?_) (fun X => ?_) h
  · rw [subst_bv_eq]; exact rank_lt_omega_of_arith hψ
  · simpa using zero_lt_omegaN

/-- **The instantiation bound.**  An arithmetical instance of `∃² φ` has rank
strictly below `rank (∃² φ)`. -/
theorem rank_subst₂_lt_exs₂ (hψ : Arith ψ) : rank (φ/⟦ψ⟧) < rank (∃² φ) := by
  rw [rank_exs₂]
  rcases lt_or_ge (rank φ) omegaN with hlt | hle
  · exact lt_of_lt_of_le (rank_subst₂_lt_omegaN hψ hlt) (le_max_right _ _)
  · rw [rank_subst₂_eq hψ hle]
    exact lt_of_lt_of_le (NONote.lt_succ _) (le_max_left _ _)

/-- The same bound for `∀²`; the two ranks are the same notation. -/
theorem rank_subst₂_lt_all₂ (hψ : Arith ψ) : rank (φ/⟦ψ⟧) < rank (∀² φ) :=
  rank_subst₂_lt_exs₂ hψ

end Subst

/-! ### Lifting first-order formulas

Foundation has no first-order → second-order embedding (`grep`ped `SecondOrder/`
for `ofFirstOrder`, `FirstOrder.Semiformula`, `lift`: nothing), so here is one.
It is a plain structural copy; the point of it is `arith_lift`, which says the
image consists of arithmetical formulas, and hence has finite rank. -/

/-- **The lift of a first-order formula to a second-order one.** -/
def lift {N n : ℕ} : FirstOrder.Semiformula L ξ n → Semiformula L Ξ ξ N n
  |         ⊤ => ⊤
  |         ⊥ => ⊥
  |  .rel r v => .rel r v
  | .nrel r v => .nrel r v
  |     φ ⋏ ψ => lift φ ⋏ lift ψ
  |     φ ⋎ ψ => lift φ ⋎ lift ψ
  |      ∀¹ φ => ∀¹ lift φ
  |      ∃¹ φ => ∃¹ lift φ

section Lift

variable {N n : ℕ}

@[simp] theorem lift_verum : (lift ⊤ : Semiformula L Ξ ξ N n) = ⊤ := rfl

@[simp] theorem lift_falsum : (lift ⊥ : Semiformula L Ξ ξ N n) = ⊥ := rfl

@[simp] theorem lift_rel {k : ℕ} (r : L.Rel k) (v : Fin k → FirstOrder.Semiterm L ξ n) :
    (lift (.rel r v) : Semiformula L Ξ ξ N n) = .rel r v := rfl

@[simp] theorem lift_nrel {k : ℕ} (r : L.Rel k) (v : Fin k → FirstOrder.Semiterm L ξ n) :
    (lift (.nrel r v) : Semiformula L Ξ ξ N n) = .nrel r v := rfl

@[simp] theorem lift_and (φ ψ : FirstOrder.Semiformula L ξ n) :
    (lift (φ ⋏ ψ) : Semiformula L Ξ ξ N n) = lift φ ⋏ lift ψ := rfl

@[simp] theorem lift_or (φ ψ : FirstOrder.Semiformula L ξ n) :
    (lift (φ ⋎ ψ) : Semiformula L Ξ ξ N n) = lift φ ⋎ lift ψ := rfl

@[simp] theorem lift_all₁ (φ : FirstOrder.Semiformula L ξ (n + 1)) :
    (lift (∀¹ φ) : Semiformula L Ξ ξ N n) = ∀¹ lift φ := rfl

@[simp] theorem lift_exs₁ (φ : FirstOrder.Semiformula L ξ (n + 1)) :
    (lift (∃¹ φ) : Semiformula L Ξ ξ N n) = ∃¹ lift φ := rfl

@[simp] theorem lift_neg (φ : FirstOrder.Semiformula L ξ n) :
    (lift (∼φ) : Semiformula L Ξ ξ N n) = ∼lift φ := by
  induction φ using FirstOrder.Semiformula.rec' <;> simp [*]

@[simp] theorem lift_imply (φ ψ : FirstOrder.Semiformula L ξ n) :
    (lift (φ 🡒 ψ) : Semiformula L Ξ ξ N n) = lift φ 🡒 lift ψ := by
  simp [LogicalConnective.DeMorgan.imply]

/-- The lift commutes with first-order rewriting. -/
@[simp] theorem lift_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}
    (ω : FirstOrder.Rew L ξ₁ n₁ ξ₂ n₂) (φ : FirstOrder.Semiformula L ξ₁ n₁) :
    (lift (ω ▹ φ) : Semiformula L Ξ ξ₂ N n₂) = ω ▹ lift φ := by
  induction φ using FirstOrder.Semiformula.rec' generalizing n₂ <;>
    simp [Semiformula.rew_rel, Semiformula.rew_nrel, Function.comp_def, *]

/-- **Lifted first-order formulas are arithmetical.** -/
@[simp] theorem arith_lift (φ : FirstOrder.Semiformula L ξ n) :
    Arith (lift φ : Semiformula L Ξ ξ N n) := by
  induction φ using FirstOrder.Semiformula.rec' <;> simp [*]

/-- **Lifted first-order formulas have finite rank.** -/
theorem rank_lift_lt_omegaN (φ : FirstOrder.Semiformula L ξ n) :
    rank (lift φ : Semiformula L Ξ ξ N n) < omegaN :=
  rank_lt_omega_of_arith (arith_lift φ)

end Lift

/-! ### Transfinite induction with a genuine set variable

`Gentzen/Setup.lean` writes `TI(≺, X)` in a first-order language enlarged by a
fresh unary predicate symbol `X`; that is the only way to say "arbitrary set" in
a first-order setting.  Here `X` is a real second-order variable — the free set
variable `0 : ℕ` — and `≺` is the *arithmetical* coded ordering `precDef` of
`Gentzen/CodedNotation.lean`, lifted rather than `lMap`ped, because the base
language is now plain `ℒₒᵣ`.

The shape is `LowerSyntax`'s, symbol for symbol, with `t ∈& 0` in place of
`Xat t`. -/

section TI

open Gentzen

/-- The coded ordering, as a first-order `ℒₒᵣ`-formula with free variables. -/
def precFO : FirstOrder.Semiformula ℒₒᵣ ℕ 2 :=
  FirstOrder.Rewriting.emb CodedNotation.precDef.val

/-- The coded ordering, lifted to the second-order syntax. -/
def precSO : Semiformula ℒₒᵣ ℕ ℕ 0 2 := lift precFO

/-- `y ≺ x`, with `y` the innermost bound variable. -/
def precAtSO {n : ℕ} (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ ℕ 0 n :=
  FirstOrder.Rew.subst ![y, x] ▹ precSO

/-- The free set variable of `TISO`. -/
def setX : ℕ := 0

/-- `∀ y ≺ x, y ∈ X` — the hypothesis of progressiveness at `x`. -/
def belowSO : Semiformula ℒₒᵣ ℕ ℕ 0 1 :=
  ∀¹ (∼(precAtSO (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) #1) ⋎ (#0 ∈& setX))

/-- `Prog(≺, X) :≡ ∀ x ((∀ y ≺ x, y ∈ X) → x ∈ X)`. -/
def ProgSO : Proposition ℒₒᵣ :=
  ∀¹ (∼belowSO ⋎ (#0 ∈& setX))

/-- `TI(≺, X) :≡ Prog(≺, X) → ∀ x, x ∈ X`, with `X` a genuine set variable. -/
def TISO : Proposition ℒₒᵣ :=
  ∼ProgSO ⋎ (∀¹ (#0 ∈& setX))

@[simp] theorem arith_precSO : Arith precSO := arith_lift _

@[simp] theorem arith_precAtSO {n : ℕ} (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    Arith (precAtSO y x) := by simp [precAtSO]

@[simp] theorem arith_belowSO : Arith belowSO := by simp [belowSO]

@[simp] theorem arith_ProgSO : Arith ProgSO := by simp [ProgSO]

/-- **`TI(≺, X)` is arithmetical** — it has no set quantifier, only the free set
variable.  This is what puts it inside the fragment the `∃₂` rule of `LK.lean`
may instantiate by, and it is why the boundedness argument of the `ε₀` case
carries over unchanged. -/
@[simp] theorem arith_TISO : Arith TISO := by simp [TISO]

/-- Hence its rank is finite. -/
theorem rank_TISO_lt_omegaN : rank TISO < omegaN := rank_lt_omega_of_arith arith_TISO

theorem rank_precSO_lt_omegaN : rank precSO < omegaN := rank_lt_omega_of_arith arith_precSO

end TI

end OrdinalAnalysis.ACA
