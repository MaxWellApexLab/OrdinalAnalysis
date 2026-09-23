/-
  The cut rank of the ramified calculus.

  `ACA/Syntax.lean`'s rank is the `ν = 1` case of what is here: literals cost
  `0`, propositional and quantifier steps cost a successor, and the one clause
  that leaves the finite ordinals is the *set* clause.  In `ACA_∞` there is one
  set quantifier and it costs `ω`; in D2 there are no set quantifiers at all —
  a level-`ν` set quantifier is an ordinary number quantifier over codes — and
  the cost is moved onto the set *atoms*:

      rank (t ∈̇_ν s)  =  ω ^ ν                    (`rank_memAt`)

  as §2 of the design note prescribes (`ω^ν`, not `ω·ν`: rank blocks are
  `ω`-powers because predicative cut elimination is `⊢^α_{ρ ⊕ ω^ξ} ⇒ ⊢^{φ_ξ(α)}_ρ`).

  Two lemmas carry the design.

  * `rank_lt_omegaPow_of_level` — if every set atom of `φ` sits strictly below
    `ν`, then `rank φ < ω^ν`.  The proof is the closure of `ω^ν` under the three
    things the rank clauses do: it is positive, it is closed under `max`
    (trivially, being a linear order), and it is closed under `succ` — the last
    because `succ x = x ⊕ 1`, `ω^ν` is additively indecomposable
    (`OrdinalNotation.nadd_lt_omegaPow`), and `1 = ω^0 < ω^ν` for `ν ≥ 1`.
    `ν ≥ 1` is free: `lvlOf φ < ν` already forces it.

  * `rank_body_lt` — **the** lemma.  `Good a → rank (body a) < ω^{lvl a}`, i.e.
    *a predicator's unfolding has strictly smaller rank than the atom it
    unfolds*.  Everything in `Ramified/ReductionProbe.lean` is downstream of it:
    it is what makes the (Pr)/(Pr) cut reducible, hence what makes D2 a
    cut-elimination argument at all.  It is `rank_lt_omegaPow_of_level` applied
    to the coding invariant, and the coding invariant is a side condition on
    codes (see `Ramified/Code.lean`), so the whole chain is three lines of proof
    over ten lines of arithmetic.

  The rank is stated concretely in `Gamma0Note`, as the design table asks, but
  every ordinal step below goes through the `OrdinalNotation` class; nothing uses
  a Veblen-specific fact, so the same file works over any notation system that
  the `Ordinal/Notation.lean` class admits.
-/
import OrdinalAnalysis.Ramified.Code
import OrdinalAnalysis.Ordinal.Veblen.Instance

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder

/-! ### `ω ^ ν` at a level -/

/-- `ω ^ ν`, for a level `ν`.  The single place the level type meets the
notation system: replacing `Lv := ℕ` by a notation type replaces
`OrdinalNotation.ofNat ν` by `ν` and changes nothing else. -/
def omegaPowLv (ν : Lv) : Gamma0Note :=
  OrdinalNotation.omegaPow (OrdinalNotation.ofNat ν)

theorem omegaPowLv_pos (ν : Lv) : (0 : Gamma0Note) < omegaPowLv ν :=
  Gamma0Note.omegaPow_pos _

theorem omegaPowLv_lt_omegaPowLv {μ ν : Lv} (h : μ < ν) : omegaPowLv μ < omegaPowLv ν :=
  OrdinalNotation.omegaPow_lt_omegaPow (OrdinalNotation.ofNat_lt_ofNat h)

/-- `1 < ω ^ ν` for `ν ≥ 1`.  `1 = ω ^ 0` and `ω ^ ·` is strictly monotone; the
class has no `0`, so `1 ≤ ω ^ 0` is the field `one_le_omegaPow` and the strict
step comes from `ofNat 0 < ofNat ν`. -/
theorem one_lt_omegaPowLv {ν : Lv} (hν : 0 < ν) :
    (OrdinalNotation.one : Gamma0Note) < omegaPowLv ν :=
  lt_of_le_of_lt (OrdinalNotation.one_le_omegaPow (OrdinalNotation.ofNat 0))
    (omegaPowLv_lt_omegaPowLv (μ := 0) hν)

/-- **`ω ^ ν` is closed under successor**, for `ν ≥ 1`.  This is the clause the
rank induction turns on, and it is exactly additive indecomposability. -/
theorem succ_lt_omegaPowLv {ν : Lv} (hν : 0 < ν) {x : Gamma0Note} (hx : x < omegaPowLv ν) :
    OrdinalNotation.succ x < omegaPowLv ν :=
  OrdinalNotation.nadd_lt_omegaPow hx (one_lt_omegaPowLv hν)

/-! ### The rank -/

/-- The rank of an atom: `ω ^ ν` for a level-`ν` set atom, `0` for every symbol
of arithmetic and for `X`. -/
def atomRank {k : ℕ} (r : LRA.Rel k) : Gamma0Note :=
  match relLevel r with
  | none => 0
  | some ν => omegaPowLv ν

/-- **The cut rank of the ramified calculus.** -/
def rank {n : ℕ} : Semiformula LRA ℕ n → Gamma0Note
  |  .rel r _ => atomRank r
  | .nrel r _ => atomRank r
  |         ⊤ => 0
  |         ⊥ => 0
  |     φ ⋏ ψ => OrdinalNotation.succ (max (rank φ) (rank ψ))
  |     φ ⋎ ψ => OrdinalNotation.succ (max (rank φ) (rank ψ))
  |      ∀¹ φ => OrdinalNotation.succ (rank φ)
  |      ∃¹ φ => OrdinalNotation.succ (rank φ)

section RankSimp

variable {n : ℕ}

@[simp] theorem rank_rel {k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    rank (.rel r v : Semiformula LRA ℕ n) = atomRank r := rfl

@[simp] theorem rank_nrel {k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    rank (.nrel r v : Semiformula LRA ℕ n) = atomRank r := rfl

@[simp] theorem rank_verum : rank (⊤ : Semiformula LRA ℕ n) = 0 := rfl

@[simp] theorem rank_falsum : rank (⊥ : Semiformula LRA ℕ n) = 0 := rfl

@[simp] theorem rank_and (φ ψ : Semiformula LRA ℕ n) :
    rank (φ ⋏ ψ) = OrdinalNotation.succ (max (rank φ) (rank ψ)) := rfl

@[simp] theorem rank_or (φ ψ : Semiformula LRA ℕ n) :
    rank (φ ⋎ ψ) = OrdinalNotation.succ (max (rank φ) (rank ψ)) := rfl

@[simp] theorem rank_all (φ : Semiformula LRA ℕ (n + 1)) :
    rank (∀¹ φ) = OrdinalNotation.succ (rank φ) := rfl

@[simp] theorem rank_exs (φ : Semiformula LRA ℕ (n + 1)) :
    rank (∃¹ φ) = OrdinalNotation.succ (rank φ) := rfl

/-- **A level-`ν` set atom costs `ω ^ ν`.**  §2 of the design note. -/
@[simp] theorem rank_memAt (ν : Lv) (t s : Semiterm LRA ℕ n) :
    rank (memAt ν t s) = omegaPowLv ν := rfl

@[simp] theorem rank_nmemAt (ν : Lv) (t s : Semiterm LRA ℕ n) :
    rank (nmemAt ν t s) = omegaPowLv ν := rfl

/-- `X(t)` is a literal and costs nothing: the `ν = 1` regression against
`ACA/Syntax.lean`, where `rank (t ∈& X) = 0`. -/
@[simp] theorem rank_Xat (t : Semiterm LRA ℕ n) : rank (Xat t) = 0 := rfl

end RankSimp

/-- The rank does not see negation. -/
@[simp] theorem rank_neg {n : ℕ} (φ : Semiformula LRA ℕ n) : rank (∼φ) = rank φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- The rank does not see rewriting. -/
@[simp] theorem rank_rew {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (φ : Semiformula LRA ℕ n₁) :
    rank (ω ▹ φ) = rank φ := by
  induction φ using Semiformula.rec' generalizing n₂ <;> simp [*]

/-- **Substituting a number term does not change the rank.**  This is what lets
the (Pr) rule instantiate its body at an arbitrary subject without disturbing the
bookkeeping. -/
@[simp] theorem rank_subst₁ {n : ℕ} (φ : Semiformula LRA ℕ 1) (t : Semiterm LRA ℕ n) :
    rank (φ/[t]) = rank φ := rank_rew _ φ

/-! ### The rank below a level -/

/-- An atom of level `< ν` — including a levelless one — has rank `< ω ^ ν`. -/
theorem atomRank_lt_omegaPowLv {k : ℕ} (r : LRA.Rel k) {ν : Lv}
    (h : (relLevel r).getD 0 < ν) : atomRank r < omegaPowLv ν := by
  cases hr : relLevel r with
  | none =>
      have he : atomRank r = 0 := by simp [atomRank, hr]
      rw [he]; exact omegaPowLv_pos ν
  | some μ =>
      have he : atomRank r = omegaPowLv μ := by simp [atomRank, hr]
      have hlt : μ < ν := by rw [hr] at h; simpa using h
      rw [he]; exact omegaPowLv_lt_omegaPowLv hlt

/-- **Every set atom below `ν` ⇒ rank below `ω ^ ν`.**

The induction has exactly three ingredients: `ω ^ ν` is positive, it is closed
under `max` because the order is linear, and it is closed under `succ` because
it is additively indecomposable and lies above `1`. -/
theorem rank_lt_omegaPow_of_level {n : ℕ} {ν : Lv} {φ : Semiformula LRA ℕ n}
    (h : lvlOf φ < ν) : rank φ < omegaPowLv ν := by
  have hν : 0 < ν := lt_of_le_of_lt (Nat.zero_le _) h
  induction φ using Semiformula.rec' with
  | hverum => exact omegaPowLv_pos ν
  | hfalsum => exact omegaPowLv_pos ν
  | hrel r v => exact atomRank_lt_omegaPowLv r (by simpa using h)
  | hnrel r v => exact atomRank_lt_omegaPowLv r (by simpa using h)
  | hand φ ψ ihφ ihψ =>
      simp only [lvlOf_and, max_lt_iff] at h
      exact succ_lt_omegaPowLv hν (max_lt (ihφ h.1) (ihψ h.2))
  | hor φ ψ ihφ ihψ =>
      simp only [lvlOf_or, max_lt_iff] at h
      exact succ_lt_omegaPowLv hν (max_lt (ihφ h.1) (ihψ h.2))
  | hall φ ih => exact succ_lt_omegaPowLv hν (ih (by simpa using h))
  | hexs φ ih => exact succ_lt_omegaPowLv hν (ih (by simpa using h))

/-- **The rank blocks.**  Every formula of level `ν` has rank below `ω^{ν+1}`,
and (when it has a level-`ν` atom at all) at least `ω^ν`.  So the ranks of the
level-`ν` fragment fill the block `[ω^ν, ω^{ν+1})` — which is exactly the shape
predicative cut elimination consumes, `⊢^α_{ρ ⊕ ω^ξ} ⇒ ⊢^{φ_ξ(α)}_ρ`, and is
§2's reason for `ω^ν` rather than `ω·ν`. -/
theorem rank_lt_omegaPowLv_succ {n : ℕ} (φ : Semiformula LRA ℕ n) :
    rank φ < omegaPowLv (lvlOf φ + 1) :=
  rank_lt_omegaPow_of_level (Nat.lt_succ_self _)

/-! ### The lemma the reduction lemma consumes -/

/-- **A predicator's unfolding has smaller rank than the atom it unfolds.**

`Good a → rank (body a) < ω^{lvl a}`.  This is the fact on which the whole of
D2 turns: it says the (Pr) rule strictly *lowers* the rank, so the cut that the
(Pr)/(Pr) principal case of the reduction lemma performs is legal at the very
rank the (Pr) atom itself is being cut at. -/
theorem rank_body_lt {a : ℕ} (h : Good a) : rank (body a) < omegaPowLv (lvl a) :=
  rank_lt_omegaPow_of_level (good_body_lvl h)

/-- `rank_body_lt` in the shape the cut rule wants: the unfolding's rank is
below the rank of the atom, for any subject and any name. -/
theorem rank_body_lt_rank_memAt {a : ℕ} (h : Good a) (t s : SyntacticTerm LRA) :
    rank (body a) < rank (memAt (lvl a) t s) := by
  rw [rank_memAt]; exact rank_body_lt h

/-- The same, after the (Pr) rule has substituted the subject into the body. -/
theorem rank_subst_body_lt {a : ℕ} (h : Good a) (t : SyntacticTerm LRA) :
    rank ((body a)/[t]) < omegaPowLv (lvl a) := by
  rw [rank_subst₁]; exact rank_body_lt h

end Ramified

end OrdinalAnalysis
