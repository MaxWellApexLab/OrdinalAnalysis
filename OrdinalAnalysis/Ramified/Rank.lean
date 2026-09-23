/-
  The cut rank of the ramified calculus.

  `ACA/Syntax.lean`'s rank is the one-level case of what is here: literals cost
  `0`, propositional and quantifier steps cost a successor, and the one clause
  that leaves the finite ordinals is the *set* clause.  In D2 there are no set
  quantifiers — a level-`μ` set quantifier is an ordinary number quantifier over
  codes — and the cost sits on the set *atoms*.

  ## `ω·μ` blocks

  A level-`μ` set atom `t ∈̇_μ s` (with `μ ≥ 1`) is priced inside the block
  `[ω·(μ−1), ω·μ]`:

      rank (t ∈̇_μ s) = ω·(μ−1) ⊕ stage(s)     if `s` is ground,
      rank (t ∈̇_μ s) = ω·μ                     otherwise,

  where `stage(s)` is the stage field (`Ramified/Code.lean`) of the value of the
  ground term `s`.  Level-`0` atoms, `X` and the symbols of arithmetic cost `0`.

  **Why `ω·μ` and not `ω^μ`.**  Cut reduction needs two facts of the rank: an
  instance of `∀z φ` has smaller rank than `∀z φ`, and the (Pr) rule lowers the
  rank.  Both hold with either pricing.  The difference is what predicative cut
  elimination then charges: removing the cuts of a block `[ω·(j−1), ω·j)` costs
  one application of `φ_1` (`PowClosed 1 (ω·j)`), so `ν` levels cost `φ_1^ν`,
  whereas `ω^μ` blocks would charge `φ_μ` for level `μ` and give a bound that is
  sound but not attained.  See the boundedness and upper-bound files for the
  ordinals themselves.

  **Why the stage.**  With a same-level parameter a level-`μ` body may contain
  level-`μ` atoms `t ∈̇_μ p̄`; the unfolding of a code can therefore only be
  cheaper than the code's own atom if the price of a level-`μ` atom depends on
  the name.  The stage condition of `Good` (`A.complexity + stage p < s`) is
  exactly the inequality that makes the (Pr) rule rank-decreasing:

      rank (body a/[t]) ≤ ω·(μ−1) ⊕ (A.complexity + stage p) < ω·(μ−1) ⊕ s
                        = rank (t ∈̇_μ ā)          (`rank_body_lt_memRank`).

  **The price of the change.**  A rewriting can turn an open set argument into
  a ground one, never the reverse, and ground terms keep their values; so the
  rank no longer is invariant under substitution, but it can only go down
  (`rank_rew_le`).  That is all cut reduction uses: `rank (φ/[n̄]) < rank (∀¹ φ)`.
  Evaluation of closed terms preserves values and groundness, so the rank *is*
  invariant under the evaluator (`Ramified/Evaluate.lean`'s `rank_evR`).

  The block lemmas: `rank_lt_block_of_level` (every atom below level `ν` ⇒ rank
  below `ω·ν`), `rank_le_maxAtomRank_nadd` (the rank is at most the largest
  atom rank plus the complexity), and its two consequences
  `rank_le_omegaMul_lvlOf_nadd` and `rank_body_lt_memRank`.
-/
import OrdinalAnalysis.Ramified.Code
import OrdinalAnalysis.Ordinal.Veblen.RankSegments

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder

/-! ### `ω ^ ν` at a level

Kept for the cut-rank bookkeeping of `Ramified/PredicativeCut.lean`, which is
stated at `ω^1 = ω`. -/

/-- `ω ^ ν`, for a level `ν`. -/
def omegaPowLv (ν : Lv) : Gamma0Note :=
  OrdinalNotation.omegaPow (OrdinalNotation.ofNat ν)

theorem omegaPowLv_pos (ν : Lv) : (0 : Gamma0Note) < omegaPowLv ν :=
  Gamma0Note.omegaPow_pos _

theorem omegaPowLv_lt_omegaPowLv {μ ν : Lv} (h : μ < ν) : omegaPowLv μ < omegaPowLv ν :=
  OrdinalNotation.omegaPow_lt_omegaPow (OrdinalNotation.ofNat_lt_ofNat h)

/-- `1 < ω ^ ν` for `ν ≥ 1`. -/
theorem one_lt_omegaPowLv {ν : Lv} (hν : 0 < ν) :
    (OrdinalNotation.one : Gamma0Note) < omegaPowLv ν :=
  lt_of_le_of_lt (OrdinalNotation.one_le_omegaPow (OrdinalNotation.ofNat 0))
    (omegaPowLv_lt_omegaPowLv (μ := 0) hν)

/-- `ω ^ ν` is closed under successor, for `ν ≥ 1`. -/
theorem succ_lt_omegaPowLv {ν : Lv} (hν : 0 < ν) {x : Gamma0Note} (hx : x < omegaPowLv ν) :
    OrdinalNotation.succ x < omegaPowLv ν :=
  OrdinalNotation.nadd_lt_omegaPow hx (one_lt_omegaPowLv hν)

theorem repr_omegaPowLv (ν : Lv) : Gamma0Note.repr (omegaPowLv ν) = Ordinal.omega0 ^ (ν : Ordinal) := by
  show Gamma0Note.repr (Gamma0Note.omegaPow (Gamma0Note.ofNat ν)) = _
  rw [Gamma0Note.repr_omegaPow, Gamma0Note.repr_ofNat]

/-! ### Finite parts

Small facts about `ρ ⊕ n` for a natural number `n`. -/

/-- `0` is the least notation. -/
theorem gamma0_zero_le (x : Gamma0Note) : (0 : Gamma0Note) ≤ x := by
  rw [Gamma0Note.le_def, Gamma0Note.repr_zero]
  exact zero_le

/-- `OrdinalNotation.ofNat` is monotone. -/
theorem ofNat_le_ofNat {m n : ℕ} (h : m ≤ n) :
    (OrdinalNotation.ofNat m : Gamma0Note) ≤ OrdinalNotation.ofNat n := by
  rcases h.eq_or_lt with rfl | h
  · exact le_refl _
  · exact le_of_lt (OrdinalNotation.ofNat_lt_ofNat h)

/-- **The successor of a finite part is the next finite part.** -/
theorem nadd_ofNat_succ (ρ : Gamma0Note) (c : ℕ) :
    OrdinalNotation.succ (OrdinalNotation.nadd ρ (OrdinalNotation.ofNat c))
      = OrdinalNotation.nadd ρ (OrdinalNotation.ofNat (c + 1)) := by
  apply Gamma0Note.repr_inj.mp
  show Gamma0Note.repr (Gamma0Note.nadd (Gamma0Note.nadd ρ (Gamma0Note.ofNat c)) 1)
      = Gamma0Note.repr (Gamma0Note.nadd ρ (Gamma0Note.ofNat (c + 1)))
  rw [Gamma0Note.repr_nadd_one, Gamma0Note.repr_nadd_ofNat, Gamma0Note.repr_nadd_ofNat]
  push_cast
  rw [add_assoc]

/-- The successor is monotone. -/
theorem succ_le_succ' {x y : Gamma0Note} (h : x ≤ y) :
    OrdinalNotation.succ x ≤ OrdinalNotation.succ y :=
  OrdinalNotation.nadd_le_nadd_left _ h

/-! ### `ω · μ` at a level -/

/-- **`ω · μ`**, the `μ`-fold natural sum of `ω`: the top of the level-`μ` rank
block. -/
def omegaMul (μ : Lv) : Gamma0Note := Gamma0Note.omegaPowMul 1 μ

@[simp] theorem omegaMul_zero : omegaMul 0 = 0 := rfl

theorem repr_omegaMul (μ : Lv) :
    Gamma0Note.repr (omegaMul μ) = Ordinal.omega0 * (μ : Ordinal) := by
  rw [omegaMul, Gamma0Note.repr_omegaPowMul, Gamma0Note.repr_one, Ordinal.opow_one]

/-- **`ω · μ` is a multiple of `ω`**: the side condition under which predicative
cut elimination at `ξ = 1` may start at the base `ω · μ`. -/
theorem powClosed_omegaMul (μ : Lv) : Gamma0Note.PowClosed 1 (omegaMul μ) := by
  have h := (Gamma0Note.powClosed_nadd_omegaPowMul (Gamma0Note.powClosed_zero 1) μ).1
  rwa [Gamma0Note.zero_nadd] at h

/-- `ω · (μ + 1) = ω · μ ⊕ ω`. -/
theorem omegaMul_succ (μ : Lv) :
    omegaMul (μ + 1) = Gamma0Note.nadd (omegaMul μ) (Gamma0Note.omegaPow 1) := rfl

theorem omegaMul_lt_omegaMul {μ ν : Lv} (h : μ < ν) : omegaMul μ < omegaMul ν := by
  rw [Gamma0Note.lt_def, repr_omegaMul, repr_omegaMul]
  exact mul_lt_mul_of_pos_left (by exact_mod_cast h) Ordinal.omega0_pos

theorem omegaMul_le_omegaMul {μ ν : Lv} (h : μ ≤ ν) : omegaMul μ ≤ omegaMul ν := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · exact le_of_lt (omegaMul_lt_omegaMul h)

theorem omegaMul_pos {ν : Lv} (hν : 0 < ν) : (0 : Gamma0Note) < omegaMul ν :=
  omegaMul_lt_omegaMul (μ := 0) hν

/-- The value of `ω · μ ⊕ k`. -/
theorem repr_omegaMul_nadd_ofNat (μ : Lv) (k : ℕ) :
    Gamma0Note.repr (Gamma0Note.nadd (omegaMul μ) (Gamma0Note.ofNat k))
      = Ordinal.omega0 * (μ : Ordinal) + (k : Ordinal) := by
  rw [Gamma0Note.repr_nadd_ofNat, repr_omegaMul]

/-- **`ω · μ ⊕ k < ω · (μ + 1)`**: a finite part never leaves its block. -/
theorem omegaMul_nadd_ofNat_lt (μ : Lv) (k : ℕ) :
    Gamma0Note.nadd (omegaMul μ) (Gamma0Note.ofNat k) < omegaMul (μ + 1) := by
  rw [Gamma0Note.lt_def, repr_omegaMul_nadd_ofNat, repr_omegaMul, Nat.cast_succ, mul_add_one]
  exact (add_lt_add_iff_left _).2 (Ordinal.natCast_lt_omega0 k)

theorem omegaMul_le_nadd (μ : Lv) (x : Gamma0Note) :
    omegaMul μ ≤ Gamma0Note.nadd (omegaMul μ) x :=
  OrdinalNotation.le_nadd_left (omegaMul μ) x

/-- **`ω · ν` is closed under successor**, for `ν ≥ 1`: it is a limit. -/
theorem succ_lt_omegaMul {ν : Lv} (hν : 0 < ν) {x : Gamma0Note} (hx : x < omegaMul ν) :
    OrdinalNotation.succ x < omegaMul ν := by
  show Gamma0Note.nadd x 1 < omegaMul ν
  rw [Gamma0Note.lt_def, Gamma0Note.repr_nadd_one, repr_omegaMul]
  rw [Gamma0Note.lt_def, repr_omegaMul] at hx
  have hlim : Order.IsSuccLimit (Ordinal.omega0 * (ν : Ordinal)) :=
    Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (by exact_mod_cast hν)
  rw [← Order.succ_eq_add_one]
  exact hlim.succ_lt hx

/-- `ω · ν ≤ ω ^ ν`: the old pricing is an upper bound for the new one. -/
theorem omegaMul_le_omegaPowLv (ν : Lv) : omegaMul ν ≤ omegaPowLv ν := by
  rw [Gamma0Note.le_def, repr_omegaMul, repr_omegaPowLv]
  rcases ν with _ | m
  · simp
  rcases m with _ | m
  · simp
  have h1 : Ordinal.omega0 * ((m + 1 + 1 : ℕ) : Ordinal) < Ordinal.omega0 * Ordinal.omega0 :=
    mul_lt_mul_of_pos_left (Ordinal.natCast_lt_omega0 _) Ordinal.omega0_pos
  have h2 : Ordinal.omega0 * Ordinal.omega0 = Ordinal.omega0 ^ ((2 : ℕ) : Ordinal) := by
    rw [Ordinal.opow_natCast, pow_two]
  have h3 : Ordinal.omega0 ^ ((2 : ℕ) : Ordinal) ≤ Ordinal.omega0 ^ ((m + 1 + 1 : ℕ) : Ordinal) :=
    Ordinal.opow_le_opow_right Ordinal.omega0_pos (by exact_mod_cast (by omega : 2 ≤ m + 1 + 1))
  exact le_of_lt (lt_of_lt_of_le (h2 ▸ h1) h3)

/-! ### Ground set arguments and the rank of a set atom -/

/-- **The rank of a level-`μ` set atom with set argument `s`.**  Level `0`
costs nothing; at level `μ + 1` a ground argument costs `ω·μ ⊕ stage(s)` and an
open one the whole block `ω·(μ + 1)`. -/
def memRank {n : ℕ} : Lv → Semiterm LRA ℕ n → Gamma0Note
  | 0, _ => 0
  | μ + 1, s =>
      if GroundR s then Gamma0Note.nadd (omegaMul μ) (Gamma0Note.ofNat (stage (evTermR s)))
      else omegaMul (μ + 1)

@[simp] theorem memRank_zero {n : ℕ} (s : Semiterm LRA ℕ n) : memRank 0 s = 0 := rfl

theorem memRank_of_groundR {n : ℕ} (μ : Lv) {s : Semiterm LRA ℕ n} (h : GroundR s) :
    memRank (μ + 1) s = Gamma0Note.nadd (omegaMul μ) (Gamma0Note.ofNat (stage (evTermR s))) :=
  if_pos h

theorem memRank_of_not_groundR {n : ℕ} (μ : Lv) {s : Semiterm LRA ℕ n} (h : ¬GroundR s) :
    memRank (μ + 1) s = omegaMul (μ + 1) :=
  if_neg h

/-- A level-`μ` atom costs at most `ω · μ`. -/
theorem memRank_le_omegaMul {n : ℕ} (μ : Lv) (s : Semiterm LRA ℕ n) :
    memRank μ s ≤ omegaMul μ := by
  rcases μ with _ | μ
  · exact le_rfl
  · by_cases h : GroundR s
    · rw [memRank_of_groundR μ h]
      exact le_of_lt (omegaMul_nadd_ofNat_lt μ _)
    · rw [memRank_of_not_groundR μ h]

/-- **A rewriting can only lower the rank of a set atom**: a ground argument
keeps its value, an open one may become ground. -/
theorem memRank_rew_le {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (μ : Lv) (s : Semiterm LRA ℕ n₁) :
    memRank μ (ω s) ≤ memRank μ s := by
  rcases μ with _ | μ
  · exact le_rfl
  · by_cases h : GroundR s
    · rw [memRank_of_groundR μ h, memRank_of_groundR μ (groundR_rew ω h), evTermR_rew ω h]
    · rw [memRank_of_not_groundR μ h]
      exact memRank_le_omegaMul _ _

/-- The rank of an atom `r v`: `0` for arithmetic symbols and `X`, and
`memRank μ (v 1)` for a level-`μ` set atom. -/
def atomRank : {k : ℕ} → LRA.Rel k → {n : ℕ} → (Fin k → Semiterm LRA ℕ n) → Gamma0Note
  | _, Sum.inl _, _, _ => 0
  | _, Sum.inr RARel.X, _, _ => 0
  | _, Sum.inr (RARel.mem μ), _, v => memRank μ (v 1)

/-- An atom costs at most `ω` times its level. -/
theorem atomRank_le_omegaMul_level {k n : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    atomRank r v ≤ omegaMul ((relLevel r).getD 0) := by
  rcases r with r | r
  · exact gamma0_zero_le _
  · cases r with
    | X => exact gamma0_zero_le _
    | mem μ => exact memRank_le_omegaMul μ (v 1)

theorem atomRank_rew_le {k n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (r : LRA.Rel k)
    (v : Fin k → Semiterm LRA ℕ n₁) : atomRank r (fun i => ω (v i)) ≤ atomRank r v := by
  rcases r with r | r
  · exact le_rfl
  · cases r with
    | X => exact le_rfl
    | mem μ => exact memRank_rew_le ω μ (v 1)

/-! ### The rank -/

/-- **The cut rank of the ramified calculus.** -/
def rank {n : ℕ} : Semiformula LRA ℕ n → Gamma0Note
  |  .rel r v => atomRank r v
  | .nrel r v => atomRank r v
  |         ⊤ => 0
  |         ⊥ => 0
  |     φ ⋏ ψ => OrdinalNotation.succ (max (rank φ) (rank ψ))
  |     φ ⋎ ψ => OrdinalNotation.succ (max (rank φ) (rank ψ))
  |      ∀¹ φ => OrdinalNotation.succ (rank φ)
  |      ∃¹ φ => OrdinalNotation.succ (rank φ)

section RankSimp

variable {n : ℕ}

@[simp] theorem rank_rel {k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    rank (.rel r v : Semiformula LRA ℕ n) = atomRank r v := rfl

@[simp] theorem rank_nrel {k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    rank (.nrel r v : Semiformula LRA ℕ n) = atomRank r v := rfl

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

/-- **A set atom costs `memRank` of its set argument.** -/
@[simp] theorem rank_memAt (μ : Lv) (t s : Semiterm LRA ℕ n) :
    rank (memAt μ t s) = memRank μ s := rfl

@[simp] theorem rank_nmemAt (μ : Lv) (t s : Semiterm LRA ℕ n) :
    rank (nmemAt μ t s) = memRank μ s := rfl

/-- `X(t)` is a literal and costs nothing: the one-level regression against
`ACA/Syntax.lean`, where `rank (t ∈& X) = 0`. -/
@[simp] theorem rank_Xat (t : Semiterm LRA ℕ n) : rank (Xat t) = 0 := rfl

end RankSimp

/-- The rank does not see negation. -/
@[simp] theorem rank_neg {n : ℕ} (φ : Semiformula LRA ℕ n) : rank (∼φ) = rank φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **A rewriting can only lower the rank.**  It may turn an open set argument
into a ground one, never the reverse. -/
theorem rank_rew_le {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (φ : Semiformula LRA ℕ n₁) :
    rank (ω ▹ φ) ≤ rank φ := by
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => simp
  | hfalsum => simp
  | hrel r v =>
      rw [Semiformula.rew_rel, rank_rel, rank_rel]
      exact atomRank_rew_le ω r v
  | hnrel r v =>
      rw [Semiformula.rew_nrel, rank_nrel, rank_nrel]
      exact atomRank_rew_le ω r v
  | hand φ ψ ihφ ihψ =>
      simp only [LogicalConnective.HomClass.map_and, rank_and]
      exact succ_le_succ' (max_le_max (ihφ ω) (ihψ ω))
  | hor φ ψ ihφ ihψ =>
      simp only [LogicalConnective.HomClass.map_or, rank_or]
      exact succ_le_succ' (max_le_max (ihφ ω) (ihψ ω))
  | hall φ ih =>
      simp only [Rewriting.app_all, rank_all]
      exact succ_le_succ' (ih ω.q)
  | hexs φ ih =>
      simp only [Rewriting.app_exs, rank_exs]
      exact succ_le_succ' (ih ω.q)

/-- **Substituting a number term can only lower the rank.**  This is what cut
reduction uses: an instance of `∀¹ φ` has rank below `rank (∀¹ φ)`. -/
theorem rank_subst₁_le {n : ℕ} (φ : Semiformula LRA ℕ 1) (t : Semiterm LRA ℕ n) :
    rank (φ/[t]) ≤ rank φ := rank_rew_le _ φ

/-! ### The rank below a level -/

/-- An atom of level `< ν` — including a levelless one — has rank `< ω · ν`. -/
theorem atomRank_lt_omegaMul {k n : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) {ν : Lv}
    (h : (relLevel r).getD 0 < ν) : atomRank r v < omegaMul ν :=
  lt_of_le_of_lt (atomRank_le_omegaMul_level r v) (omegaMul_lt_omegaMul h)

/-- **Every set atom below `ν` ⇒ rank below `ω · ν`.**

The induction has three ingredients: `ω · ν` is positive, it is closed under
`max` because the order is linear, and it is closed under `succ` because it is
a limit. -/
theorem rank_lt_block_of_level {n : ℕ} {ν : Lv} {φ : Semiformula LRA ℕ n}
    (h : lvlOf φ < ν) : rank φ < omegaMul ν := by
  have hν : 0 < ν := lt_of_le_of_lt (Nat.zero_le _) h
  induction φ using Semiformula.rec' with
  | hverum => exact omegaMul_pos hν
  | hfalsum => exact omegaMul_pos hν
  | hrel r v => exact atomRank_lt_omegaMul r v h
  | hnrel r v => exact atomRank_lt_omegaMul r v h
  | hand φ ψ ihφ ihψ =>
      simp only [lvlOf_and, max_lt_iff] at h
      exact succ_lt_omegaMul hν (max_lt (ihφ h.1) (ihψ h.2))
  | hor φ ψ ihφ ihψ =>
      simp only [lvlOf_or, max_lt_iff] at h
      exact succ_lt_omegaMul hν (max_lt (ihφ h.1) (ihψ h.2))
  | hall φ ih => exact succ_lt_omegaMul hν (ih h)
  | hexs φ ih => exact succ_lt_omegaMul hν (ih h)

/-- **The rank blocks.**  Every formula of level `ν` has rank below `ω·(ν+1)`. -/
theorem rank_lt_omegaMul_succ {n : ℕ} (φ : Semiformula LRA ℕ n) :
    rank φ < omegaMul (lvlOf φ + 1) :=
  rank_lt_block_of_level (Nat.lt_succ_self _)

/-- The coarser `ω ^ ν` form of `rank_lt_block_of_level`. -/
theorem rank_lt_omegaPow_of_level {n : ℕ} {ν : Lv} {φ : Semiformula LRA ℕ n}
    (h : lvlOf φ < ν) : rank φ < omegaPowLv ν :=
  lt_of_lt_of_le (rank_lt_block_of_level h) (omegaMul_le_omegaPowLv ν)

/-! ### The largest atom rank -/

/-- **The largest rank of an atom of `φ`**, `0` if it has none. -/
def maxAtomRank {n : ℕ} : Semiformula LRA ℕ n → Gamma0Note
  |  .rel r v => atomRank r v
  | .nrel r v => atomRank r v
  |         ⊤ => 0
  |         ⊥ => 0
  |     φ ⋏ ψ => max (maxAtomRank φ) (maxAtomRank ψ)
  |     φ ⋎ ψ => max (maxAtomRank φ) (maxAtomRank ψ)
  |      ∀¹ φ => maxAtomRank φ
  |      ∃¹ φ => maxAtomRank φ

/-- **The rank is at most the largest atom rank plus the complexity.** -/
theorem rank_le_maxAtomRank_nadd {n : ℕ} (φ : Semiformula LRA ℕ n) :
    rank φ ≤ Gamma0Note.nadd (maxAtomRank φ) (Gamma0Note.ofNat φ.complexity) := by
  induction φ using Semiformula.rec' with
  | hverum => exact gamma0_zero_le _
  | hfalsum => exact gamma0_zero_le _
  | hrel r v =>
      show atomRank r v ≤ Gamma0Note.nadd (atomRank r v) (Gamma0Note.ofNat 0)
      exact OrdinalNotation.le_nadd_left _ _
  | hnrel r v =>
      show atomRank r v ≤ Gamma0Note.nadd (atomRank r v) (Gamma0Note.ofNat 0)
      exact OrdinalNotation.le_nadd_left _ _
  | hand φ ψ ihφ ihψ =>
      rw [rank_and, Semiformula.complexity_and]
      have e := nadd_ofNat_succ (max (maxAtomRank φ) (maxAtomRank ψ))
        (max φ.complexity ψ.complexity)
      refine le_trans ?_ (le_of_eq e)
      refine succ_le_succ' (max_le ?_ ?_)
      · exact le_trans ihφ (le_trans (OrdinalNotation.nadd_le_nadd_left _ (le_max_left _ _))
          (OrdinalNotation.nadd_le_nadd_right _ (ofNat_le_ofNat (le_max_left _ _))))
      · exact le_trans ihψ (le_trans (OrdinalNotation.nadd_le_nadd_left _ (le_max_right _ _))
          (OrdinalNotation.nadd_le_nadd_right _ (ofNat_le_ofNat (le_max_right _ _))))
  | hor φ ψ ihφ ihψ =>
      rw [rank_or, Semiformula.complexity_or]
      have e := nadd_ofNat_succ (max (maxAtomRank φ) (maxAtomRank ψ))
        (max φ.complexity ψ.complexity)
      refine le_trans ?_ (le_of_eq e)
      refine succ_le_succ' (max_le ?_ ?_)
      · exact le_trans ihφ (le_trans (OrdinalNotation.nadd_le_nadd_left _ (le_max_left _ _))
          (OrdinalNotation.nadd_le_nadd_right _ (ofNat_le_ofNat (le_max_left _ _))))
      · exact le_trans ihψ (le_trans (OrdinalNotation.nadd_le_nadd_left _ (le_max_right _ _))
          (OrdinalNotation.nadd_le_nadd_right _ (ofNat_le_ofNat (le_max_right _ _))))
  | hall φ ih =>
      rw [rank_all, Semiformula.complexity_all]
      exact le_trans (succ_le_succ' ih) (le_of_eq (nadd_ofNat_succ _ _))
  | hexs φ ih =>
      rw [rank_exs, Semiformula.complexity_exs]
      exact le_trans (succ_le_succ' ih) (le_of_eq (nadd_ofNat_succ _ _))

/-- The largest atom rank is at most `ω` times the level. -/
theorem maxAtomRank_le_omegaMul_lvlOf {n : ℕ} (φ : Semiformula LRA ℕ n) :
    maxAtomRank φ ≤ omegaMul (lvlOf φ) := by
  induction φ using Semiformula.rec' with
  | hverum => exact gamma0_zero_le _
  | hfalsum => exact gamma0_zero_le _
  | hrel r v => exact atomRank_le_omegaMul_level r v
  | hnrel r v => exact atomRank_le_omegaMul_level r v
  | hand φ ψ ihφ ihψ =>
      exact max_le (le_trans ihφ (omegaMul_le_omegaMul (le_max_left _ _)))
        (le_trans ihψ (omegaMul_le_omegaMul (le_max_right _ _)))
  | hor φ ψ ihφ ihψ =>
      exact max_le (le_trans ihφ (omegaMul_le_omegaMul (le_max_left _ _)))
        (le_trans ihψ (omegaMul_le_omegaMul (le_max_right _ _)))
  | hall φ ih => exact ih
  | hexs φ ih => exact ih

/-- **The finite-part rank bound**: `rank φ ≤ ω · lvlOf φ ⊕ complexity φ`. -/
theorem rank_le_omegaMul_lvlOf_nadd {n : ℕ} (φ : Semiformula LRA ℕ n) :
    rank φ ≤ Gamma0Note.nadd (omegaMul (lvlOf φ)) (Gamma0Note.ofNat φ.complexity) :=
  le_trans (rank_le_maxAtomRank_nadd φ)
    (OrdinalNotation.nadd_le_nadd_left _ (maxAtomRank_le_omegaMul_lvlOf φ))

/-! ### The lemma the reduction lemma consumes -/

/-- A rewriting that sends every free variable to a ground term of value `p`. -/
def ParamRew {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (p : ℕ) : Prop :=
  ∀ x : ℕ, GroundR (ω &x) ∧ evTermR (ω &x) = p

theorem ParamRew.q {n₁ n₂ : ℕ} {ω : Rew LRA ℕ n₁ ℕ n₂} {p : ℕ} (h : ParamRew ω p) :
    ParamRew ω.q p := by
  intro x
  rw [Rew.q_fvar]
  exact ⟨groundR_rew _ (h x).1, (evTermR_rew _ (h x).1).trans (h x).2⟩

/-- Instantiating the parameter is such a rewriting. -/
theorem paramRew_instParam (p : ℕ) : ParamRew (instParam p) p :=
  fun _ => ⟨groundR_numAtR p, evTermR_numAtR p⟩

/-- One atom of `maxAtomRank_rew_le_of_shape`. -/
theorem atomRank_rew_le_of_atomShape {μ : Lv} {p : ℕ} {k n₁ : ℕ} (r : LRA.Rel k)
    (v : Fin k → Semiterm LRA ℕ n₁) (hr : AtomShape (μ + 1) r v) {n₂ : ℕ}
    (ω : Rew LRA ℕ n₁ ℕ n₂) (hω : ParamRew ω p) :
    atomRank r (fun i => ω (v i)) ≤ Gamma0Note.nadd (omegaMul μ) (Gamma0Note.ofNat (stage p)) := by
  rcases r with r | r
  · exact gamma0_zero_le _
  · cases r with
    | X => exact gamma0_zero_le _
    | mem κ =>
        show memRank κ (ω (v 1)) ≤ _
        rcases hr with hlt | ⟨rfl, hv⟩
        · exact le_trans (memRank_le_omegaMul κ _)
            (le_trans (omegaMul_le_omegaMul (Nat.le_of_lt_succ hlt)) (omegaMul_le_nadd μ _))
        · rw [hv, memRank_of_groundR μ (hω 0).1, (hω 0).2]

/-- **The atoms of an instantiated body of shape `μ + 1` cost at most
`ω · μ ⊕ stage p`**: lower levels cost at most `ω · μ`, and a level-`(μ + 1)`
atom has the parameter, now the ground term of value `p`, as its set
argument. -/
theorem maxAtomRank_rew_le_of_shape {μ : Lv} {p : ℕ} {n₁ : ℕ} {φ : Semiformula LRA ℕ n₁}
    (hφ : Shape (μ + 1) φ) {n₂ : ℕ} {ω : Rew LRA ℕ n₁ ℕ n₂} (hω : ParamRew ω p) :
    maxAtomRank (ω ▹ φ) ≤ Gamma0Note.nadd (omegaMul μ) (Gamma0Note.ofNat (stage p)) := by
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => exact gamma0_zero_le _
  | hfalsum => exact gamma0_zero_le _
  | hrel r v =>
      rw [Semiformula.rew_rel]
      exact atomRank_rew_le_of_atomShape r v hφ ω hω
  | hnrel r v =>
      rw [Semiformula.rew_nrel]
      exact atomRank_rew_le_of_atomShape r v hφ ω hω
  | hand φ ψ ihφ ihψ =>
      simp only [LogicalConnective.HomClass.map_and]
      exact max_le (ihφ hφ.1 hω) (ihψ hφ.2 hω)
  | hor φ ψ ihφ ihψ =>
      simp only [LogicalConnective.HomClass.map_or]
      exact max_le (ihφ hφ.1 hω) (ihψ hφ.2 hω)
  | hall φ ih =>
      simp only [Rewriting.app_all]
      exact ih hφ hω.q
  | hexs φ ih =>
      simp only [Rewriting.app_exs]
      exact ih hφ hω.q

/-- **The rank of an instantiated body of shape `μ + 1`**:
`ω · μ ⊕ (complexity + stage p)`. -/
theorem rank_rew_le_of_shape {μ : Lv} {p : ℕ} {n₁ : ℕ} {φ : Semiformula LRA ℕ n₁}
    (hφ : Shape (μ + 1) φ) {n₂ : ℕ} {ω : Rew LRA ℕ n₁ ℕ n₂} (hω : ParamRew ω p) :
    rank (ω ▹ φ) ≤
      Gamma0Note.nadd (omegaMul μ) (Gamma0Note.ofNat (φ.complexity + stage p)) := by
  refine le_trans (rank_le_maxAtomRank_nadd _) ?_
  rw [Semiformula.complexity_rew]
  refine le_trans (OrdinalNotation.nadd_le_nadd_left _ (maxAtomRank_rew_le_of_shape hφ hω))
    (le_of_eq ?_)
  apply Gamma0Note.repr_inj.mp
  show Gamma0Note.repr (Gamma0Note.nadd (Gamma0Note.nadd (omegaMul μ)
      (Gamma0Note.ofNat (stage p))) (Gamma0Note.ofNat φ.complexity)) = _
  rw [Gamma0Note.repr_nadd_ofNat, Gamma0Note.repr_nadd_ofNat, Gamma0Note.repr_nadd_ofNat,
    add_assoc, ← Nat.cast_add, Nat.add_comm]

/-- **A predicator's unfolding has smaller rank than the atom it unfolds.**

For a `Good` code `a` of level `μ + 1`, any instance of the body costs at most
`ω · μ ⊕ (complexity + stage (param a))`, which the stage condition puts
strictly below `ω · μ ⊕ stage a` — the rank of every atom `t ∈̇_{μ+1} s` whose
ground set argument `s` has value `a`.  This is what makes the (Pr)/(Pr) cut of
the reduction lemma legal at the very rank the (Pr) atom is cut at. -/
theorem rank_body_lt_memRank {a : ℕ} (h : Good a) {n : ℕ} {s : Semiterm LRA ℕ n}
    (hs : GroundR s) (hv : evTermR s = a) : rank (body a) < memRank (lvl a) s := by
  rw [body]
  obtain ⟨μ, hμ⟩ : ∃ μ : Lv, lvl a = μ + 1 :=
    ⟨lvl a - 1, (Nat.sub_add_cancel (good_lvl_pos h)).symm⟩
  have hshape : Shape (μ + 1) (formula a) := by rw [← hμ]; exact good_shape h
  have hle : rank (instParam (param a) ▹ formula a) ≤ Gamma0Note.nadd (omegaMul μ)
      (Gamma0Note.ofNat ((formula a).complexity + stage (param a))) :=
    rank_rew_le_of_shape (ω := instParam (param a)) hshape (paramRew_instParam (param a))
  have key : ∀ m k : ℕ, m < k → Gamma0Note.nadd (omegaMul μ) (Gamma0Note.ofNat m)
      < Gamma0Note.nadd (omegaMul μ) (Gamma0Note.ofNat k) :=
    fun m k hmk => Gamma0Note.nadd_lt_nadd_right _ (Gamma0Note.ofNat_lt_ofNat hmk)
  have hlt := key _ _ (good_stage h)
  have hm : memRank (lvl a) s = Gamma0Note.nadd (omegaMul μ) (Gamma0Note.ofNat (stage a)) := by
    rw [hμ, memRank_of_groundR μ hs, hv]
  rw [hm]
  exact lt_of_le_of_lt hle hlt

/-- The same, after a substitution into the body. -/
theorem rank_rew_body_lt_memRank {a : ℕ} (h : Good a) {n₂ : ℕ} (ω : Rew LRA ℕ 1 ℕ n₂)
    {n : ℕ} {s : Semiterm LRA ℕ n} (hs : GroundR s) (hv : evTermR s = a) :
    rank (ω ▹ body a) < memRank (lvl a) s :=
  lt_of_le_of_lt (rank_rew_le ω _) (rank_body_lt_memRank h hs hv)

end Ramified

end OrdinalAnalysis
