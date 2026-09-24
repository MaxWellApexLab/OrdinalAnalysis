/-
  The replay of finitary derivations in the ramified infinitary calculus
  (design **D2**).

  Every derivation of Foundation's one-sided `LK` for `LRA` becomes a derivation
  in `RA_∞` (`Ramified/Calculus.lean`) with the evaluating instantiation
  (`Ramified/Evaluate.lean`), at the same ordinal height and at a cut rank read
  off the derivation, of every numeral instance of its sequent — the free
  variable `x` sent to the numeral `f x`, every ground term then replaced by the
  numeral of its value.

  This is `Gentzen/Embed.lean` with two changes, both bookkeeping.

  * **The cut rank is an ordinal**, `cutRankR d : Gamma0Note`, defined exactly as
    `ACAOmega/CutRank₂.lean`'s `cutRank₂` is on `NONote`: `Proof/CutRank.cutRank`
    with `φ.complexity + 1` replaced by `OrdinalNotation.succ (rank φ)`.  The
    `cut` rule of `OmegaDerivableR` asks `rank φ < ρ`, and `lt_succ` delivers it.
    The *height* is untouched: `Proof/Bridge.ordN` is already generic in the
    notation system and is reused verbatim.

  * **There is no (Pr) case.**  Foundation's `LK` has eight rules and none of
    them is a predicator rule, so the replay never fires `pr`/`npr`.  That is not
    an omission: in D2 the naming axioms are an *external schema* (see
    `Ramified/Theory.lean`), so a proof in `RA Λ` arrives as `⊢ᴸᴷ¹ σ :: ∼axioms`
    and the naming axioms enter as ordinary formulas of the sequent, to be cut
    away later against (Pr)-derivations of themselves.  The (Pr) rules exist for
    that cut, not for the replay.

  Everything else is the first-order argument unchanged, and for the reason the
  design note gives: under D2 the only substitution anywhere is of a *term*, so
  `Gentzen/`'s `Rew` idioms port and `ACAOmega/`'s `SubstFamily` machinery is not
  needed.  In particular `identity` stays atomic on both sides, which is what
  lets the case be a `simp only` plus `OmegaDerivableR.identity`.

  ## The cut-rank bound

  A derivation's formulas are not bounded in level a priori — the `cut` rule may
  introduce a formula of any level at all.  So, exactly as
  `ACAOmega/RankBound.lean` bounds `rank` by `ω + complexity` and then extracts a
  bound for a finite list of axioms, this file measures the derivation itself:

      cutLvl d : Lv                            the largest level of a cut formula in `d`
      cutRankR d < blkTop (cutLvl d ⊕ 1)        `cutRankR_lt_blkTop_succ`
      cutLvl d < ν  →  cutRankR d < blkTop ν    `cutRankR_lt_blkTop`

  The second is `Ramified/Rank.lean`'s `rank_lt_blkTop_of_level` run over the
  derivation tree, and it is the shape predicative cut elimination consumes: at
  a finite level `ν` the cut rank sits below `blkTop ν = ω · ν`
  (`cutRankR_lt_omegaMul`), and each block `[ω·(j−1), ω·j)` is removed by one
  application of `φ_1` (`Ramified/BlockCut.lean`).  `exists_blkTop_bound` is the
  list form, the analogue of `RankBound.exists_omegaAdd_bound`.
-/
import OrdinalAnalysis.Proof.Bridge
import OrdinalAnalysis.Ramified.Evaluate
import OrdinalAnalysis.Ramified.NumSubst

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Derivation

/-! ### The ordinal cut rank of an `LK` derivation -/

/-- **The cut rank of an `LRA`-derivation**, as an ordinal notation: `0` if it
uses no `cut`, and otherwise the `max` over every `cut` node of
`OrdinalNotation.succ` of the cut formula's `rank`, together with the cut ranks
of the two premises.

`Proof/CutRank.cutRank` with `φ.complexity + 1` replaced by `succ (rank φ)`,
which is `ACAOmega/CutRank₂.lean`'s `cutRank₂` transported to the first-order
`Derivation`. -/
def cutRankR : {Δ : Sequent LRA} → ⊢ᴸᴷ¹ Δ → Gamma0Note
  | _, Derivation.identity _ _ => 0
  | _, Derivation.verum => 0
  | _, @Derivation.cut _ φ _ _ dp dn =>
      max (OrdinalNotation.succ (rank φ)) (max (cutRankR dp) (cutRankR dn))
  | _, Derivation.contraction d _ => cutRankR d
  | _, Derivation.or d => cutRankR d
  | _, Derivation.and dp dq => max (cutRankR dp) (cutRankR dq)
  | _, Derivation.all d => cutRankR d
  | _, Derivation.exs d => cutRankR d

@[simp] theorem cutRankR_identity {k : ℕ} (r : LRA.Rel k) (v) :
    cutRankR (Derivation.identity r v) = 0 := rfl

@[simp] theorem cutRankR_verum :
    cutRankR (Derivation.verum : ⊢ᴸᴷ¹ ([⊤] : Sequent LRA)) = 0 := rfl

@[simp] theorem cutRankR_cut {φ : Proposition LRA} {Γ Δ : Sequent LRA}
    (dp : ⊢ᴸᴷ¹ φ :: Γ) (dn : ⊢ᴸᴷ¹ ∼φ :: Δ) :
    cutRankR (dp.cut dn)
      = max (OrdinalNotation.succ (rank φ)) (max (cutRankR dp) (cutRankR dn)) := rfl

@[simp] theorem cutRankR_contraction {Δ Γ : Sequent LRA} (d : ⊢ᴸᴷ¹ Δ) (ss : Δ ⊆ Γ) :
    cutRankR (d.contraction ss) = cutRankR d := rfl

@[simp] theorem cutRankR_or {φ ψ : Proposition LRA} {Γ : Sequent LRA}
    (d : ⊢ᴸᴷ¹ φ :: ψ :: Γ) : cutRankR d.or = cutRankR d := rfl

@[simp] theorem cutRankR_and {φ ψ : Proposition LRA} {Γ : Sequent LRA}
    (dp : ⊢ᴸᴷ¹ φ :: Γ) (dq : ⊢ᴸᴷ¹ ψ :: Γ) :
    cutRankR (dp.and dq) = max (cutRankR dp) (cutRankR dq) := rfl

@[simp] theorem cutRankR_all {φ : Semiproposition LRA 1} {Γ : Sequent LRA}
    (d : ⊢ᴸᴷ¹ Rewriting.free φ :: Γ⁺) : cutRankR d.all = cutRankR d := rfl

@[simp] theorem cutRankR_exs {φ : Semiproposition LRA 1} {t : SyntacticTerm LRA}
    {Γ : Sequent LRA} (d : ⊢ᴸᴷ¹ φ/[t] :: Γ) : cutRankR d.exs = cutRankR d := rfl

/-- **Every cut formula's rank is strictly below the cut rank** — the side
condition `OmegaDerivableR.cut` demands, discharged once here instead of at every
replayed cut. -/
theorem rank_lt_cutRankR_cut {φ : Proposition LRA} {Γ Δ : Sequent LRA}
    (dp : ⊢ᴸᴷ¹ φ :: Γ) (dn : ⊢ᴸᴷ¹ ∼φ :: Δ) : rank φ < cutRankR (dp.cut dn) := by
  rw [cutRankR_cut]
  exact lt_of_lt_of_le (OrdinalNotation.lt_succ _) (le_max_left _ _)

/-! ### The level of a derivation

The cut rank is an ordinal and we must place it inside an `ω`-power block.  The
measure that does it is the largest *level* of a cut formula. -/

/-- **The largest level of a cut formula of `d`**, `0` if `d` is cut free. -/
def cutLvl : {Δ : Sequent LRA} → ⊢ᴸᴷ¹ Δ → Lv
  | _, Derivation.identity _ _ => 0
  | _, Derivation.verum => 0
  | _, @Derivation.cut _ φ _ _ dp dn => max (lvlOf φ) (max (cutLvl dp) (cutLvl dn))
  | _, Derivation.contraction d _ => cutLvl d
  | _, Derivation.or d => cutLvl d
  | _, Derivation.and dp dq => max (cutLvl dp) (cutLvl dq)
  | _, Derivation.all d => cutLvl d
  | _, Derivation.exs d => cutLvl d

@[simp] theorem cutLvl_identity {k : ℕ} (r : LRA.Rel k) (v) :
    cutLvl (Derivation.identity r v) = 0 := rfl

@[simp] theorem cutLvl_verum :
    cutLvl (Derivation.verum : ⊢ᴸᴷ¹ ([⊤] : Sequent LRA)) = 0 := rfl

@[simp] theorem cutLvl_cut {φ : Proposition LRA} {Γ Δ : Sequent LRA}
    (dp : ⊢ᴸᴷ¹ φ :: Γ) (dn : ⊢ᴸᴷ¹ ∼φ :: Δ) :
    cutLvl (dp.cut dn) = max (lvlOf φ) (max (cutLvl dp) (cutLvl dn)) := rfl

@[simp] theorem cutLvl_contraction {Δ Γ : Sequent LRA} (d : ⊢ᴸᴷ¹ Δ) (ss : Δ ⊆ Γ) :
    cutLvl (d.contraction ss) = cutLvl d := rfl

@[simp] theorem cutLvl_or {φ ψ : Proposition LRA} {Γ : Sequent LRA}
    (d : ⊢ᴸᴷ¹ φ :: ψ :: Γ) : cutLvl d.or = cutLvl d := rfl

@[simp] theorem cutLvl_and {φ ψ : Proposition LRA} {Γ : Sequent LRA}
    (dp : ⊢ᴸᴷ¹ φ :: Γ) (dq : ⊢ᴸᴷ¹ ψ :: Γ) :
    cutLvl (dp.and dq) = max (cutLvl dp) (cutLvl dq) := rfl

@[simp] theorem cutLvl_all {φ : Semiproposition LRA 1} {Γ : Sequent LRA}
    (d : ⊢ᴸᴷ¹ Rewriting.free φ :: Γ⁺) : cutLvl d.all = cutLvl d := rfl

@[simp] theorem cutLvl_exs {φ : Semiproposition LRA 1} {t : SyntacticTerm LRA}
    {Γ : Sequent LRA} (d : ⊢ᴸᴷ¹ φ/[t] :: Γ) : cutLvl d.exs = cutLvl d := rfl

/-! ### Raising the level of a block -/

/-- Raising the level of the block keeps a bound. -/
theorem lt_blkTop_succ_of_le {x : Gamma0Note} {m n : Lv}
    (hx : x < Gamma0Note.blkTop (Gamma0Note.nadd m 1)) (h : m ≤ n) :
    x < Gamma0Note.blkTop (Gamma0Note.nadd n 1) :=
  lt_of_lt_of_le hx (Gamma0Note.blkTop_mono (Gamma0Note.nadd_le_nadd_left 1 h))

theorem blkTop_succ_pos (m : Lv) : (0 : Gamma0Note) < Gamma0Note.blkTop (Gamma0Note.nadd m 1) :=
  Gamma0Note.blkTop_pos (ne_of_gt (lt_of_le_of_lt (gamma0_zero_le m) (Gamma0Note.lt_nadd_one m)))

/-! ### The cut-rank bound -/

/-- **The cut rank sits inside the block of the derivation's level.**

`Ramified/Rank.lean`'s `rank_lt_blkTop_of_level` run over the derivation tree:
at a `cut` node the cut formula's rank is below `blkTop (lvlOf φ ⊕ 1)` and a
successor stays inside the block because the top of a block is a limit, and
everything else is the induction hypothesis lifted along `blkTop` monotone. -/
theorem cutRankR_lt_blkTop_succ : ∀ {Δ : Sequent LRA} (d : ⊢ᴸᴷ¹ Δ),
    cutRankR d < Gamma0Note.blkTop (Gamma0Note.nadd (cutLvl d) 1) := by
  intro Δ d
  induction d with
  | identity r v => exact blkTop_succ_pos _
  | verum => exact blkTop_succ_pos _
  | cut dp dn ihp ihn =>
      rename_i φ _ _
      refine max_lt ?_ (max_lt ?_ ?_)
      · refine Gamma0Note.succ_lt_blkTop ?_
        exact lt_blkTop_succ_of_le (rank_lt_blkTop_succ φ) (le_max_left _ _)
      · exact lt_blkTop_succ_of_le ihp (le_trans (le_max_left _ _) (le_max_right _ _))
      · exact lt_blkTop_succ_of_le ihn (le_trans (le_max_right _ _) (le_max_right _ _))
  | contraction d ss ih => exact ih
  | or d ih => exact ih
  | and dp dq ihp ihq =>
      exact max_lt (lt_blkTop_succ_of_le ihp (le_max_left _ _))
        (lt_blkTop_succ_of_le ihq (le_max_right _ _))
  | all d ih => exact ih
  | exs d ih => exact ih

/-- **The form predicative cut elimination consumes.**  If every cut of `d` is on
a formula of level `< ν`, the whole derivation's cut rank is below `blkTop ν`. -/
theorem cutRankR_lt_blkTop {Δ : Sequent LRA} (d : ⊢ᴸᴷ¹ Δ) {ν : Lv}
    (h : cutLvl d < ν) : cutRankR d < Gamma0Note.blkTop ν :=
  lt_of_lt_of_le (cutRankR_lt_blkTop_succ d)
    (Gamma0Note.blkTop_mono (Gamma0Note.nadd_one_le_of_lt h))

/-- **The finite form**: every cut of `d` below the finite level `ν` ⇒ cut rank
below `ω · ν`. -/
theorem cutRankR_lt_omegaMul {Δ : Sequent LRA} (d : ⊢ᴸᴷ¹ Δ) {ν : ℕ}
    (h : cutLvl d < Gamma0Note.ofNat ν) : cutRankR d < omegaMul ν := by
  rw [← blkTop_ofNat]; exact cutRankR_lt_blkTop d h

/-- The coarser `ω`-power form of `cutRankR_lt_omegaMul`. -/
theorem cutRankR_lt_omegaPowLv {Δ : Sequent LRA} (d : ⊢ᴸᴷ¹ Δ) {ν : ℕ}
    (h : cutLvl d < Gamma0Note.ofNat ν) : cutRankR d < omegaPowLv ν :=
  lt_of_lt_of_le (cutRankR_lt_omegaMul d h) (omegaMul_le_omegaPowLv ν)

/-- The list form, the analogue of `ACAOmega/RankBound.exists_omegaAdd_bound`:
any finite list of formulas — a sequent of axioms, say — has *some* block
containing the (evaluated) rank of every member. -/
theorem exists_blkTop_bound : ∀ Γ : Sequent LRA,
    ∃ ν : Lv, ∀ φ ∈ Γ, rank (evR φ) < Gamma0Note.blkTop ν
  | [] => ⟨0, by simp⟩
  | φ :: Γ => by
      obtain ⟨ν, hν⟩ := exists_blkTop_bound Γ
      refine ⟨max ν (Gamma0Note.nadd (lvlOf φ) 1), fun ψ hψ => ?_⟩
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · rw [rank_evR]
        exact lt_of_lt_of_le (rank_lt_blkTop_succ ψ)
          (Gamma0Note.blkTop_mono (le_max_right _ _))
      · exact lt_of_lt_of_le (hν ψ hψ') (Gamma0Note.blkTop_mono (le_max_left _ _))

/-! ### The replay -/

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- **The replay.**  An `LK` derivation of `Γ` yields, for every assignment `f`,
a derivation in `RA_∞` of the evaluated `f`-instance of `Γ`, at the same height
and at the derivation's own ordinal cut rank.

Proved for all `f` at once: that is what makes it an induction, because
Foundation's `cut` may introduce a formula with free variables the conclusion
does not have, so "closed" is not an invariant of the derivation but
"instantiated by `f`" is.  The two quantifier rules are the content, exactly as
in `Gentzen/Embed.lean` — `all` becomes the ω-rule via `numSubstR_free` and
`seqSubstR_shifts`, and `exs`'s arbitrary witness becomes a numeral via
`evR_subst_ground`. -/
theorem replayR : ∀ {Γ : Sequent LRA} (d : ⊢ᴸᴷ¹ Γ) (f : ℕ → ℕ),
    OmegaDerivableR trueArithLitsR evInstR (cutRankR d) (ordN d : O)
      ((seqSubstR f Γ).map evR)
  | _, Derivation.identity rl v, f => by
      simp only [seqSubstR_cons, seqSubstR_nil, List.map_cons, List.map_nil,
        Semiformula.rew_rel, Semiformula.rew_nrel, evR_rel, evR_nrel]
      exact OmegaDerivableR.identity _ _
  | _, Derivation.verum, f => by
      simpa using OmegaDerivableR.verum
  | _, Derivation.contraction d ss, f =>
      OmegaDerivableR.contraction (List.map_subset _ (seqSubstR_subset ss)) (replayR d f)
  | _, Derivation.or d, f => by
      have h := replayR d f
      simp only [seqSubstR_cons, List.map_cons] at h ⊢
      simp only [LogicalConnective.HomClass.map_or, evR_or]
      exact OmegaDerivableR.or (OrdinalNotation.lt_succ _)
        (h.mono_rank (le_of_eq (cutRankR_or d).symm))
  | _, Derivation.and dp dq, f => by
      have hp := replayR dp f
      have hq := replayR dq f
      simp only [seqSubstR_cons, List.map_cons] at hp hq ⊢
      simp only [LogicalConnective.HomClass.map_and, evR_and]
      exact OmegaDerivableR.and
        (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_left _ _))
        (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_right _ _))
        (hp.mono_rank (by rw [cutRankR_and]; exact le_max_left _ _))
        (hq.mono_rank (by rw [cutRankR_and]; exact le_max_right _ _))
  | _, Derivation.cut dp dn, f => by
      have hp := replayR dp f
      have hn := replayR dn f
      simp only [seqSubstR_cons, List.map_cons] at hp hn
      simp only [LogicalConnective.HomClass.map_neg, evR_neg] at hn
      simp only [seqSubstR_append, List.map_append]
      refine OmegaDerivableR.cut ?_
        (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_left _ _))
        (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_right _ _))
        (hp.mono_rank (by rw [cutRankR_cut]; exact le_trans (le_max_left _ _) (le_max_right _ _)))
        (hn.mono_rank (by rw [cutRankR_cut]; exact le_trans (le_max_right _ _) (le_max_right _ _)))
      rw [cutRankR_cut, rank_evR]
      exact lt_of_le_of_lt (rank_numSubstR_le f _)
        (lt_of_lt_of_le (OrdinalNotation.lt_succ _) (le_max_left _ _))
  | _, Derivation.all d, f => by
      simp only [seqSubstR_cons, List.map_cons, numSubstR_all, evR_all]
      refine OmegaDerivableR.omegaRule (fun _ => (ordN d : O))
        (fun _ => OrdinalNotation.lt_succ _)
        (fun n => ?_)
      have h := replayR d (n :>ₙ f)
      simp only [seqSubstR_cons, List.map_cons, seqSubstR_shifts, numSubstR_free] at h
      rw [evInstR_inst_ev]
      exact h.mono_rank (le_of_eq (cutRankR_all d).symm)
  | _, Derivation.exs d, f => by
      rename_i φ t Γ
      have h := replayR d f
      simp only [seqSubstR_cons, List.map_cons, numSubstR_subst] at h
      simp only [seqSubstR_cons, List.map_cons, numSubstR_exs, evR_exs]
      refine OmegaDerivableR.exs (evTermR (numSubstR f t)) (OrdinalNotation.lt_succ _) ?_
      rw [evInstR_inst_ev,
        ← evR_subst_ground (groundR_of_closed (freeVariables_numSubstR_term f t))]
      exact h.mono_rank (le_of_eq (cutRankR_exs d).symm)

/-- **The replay of a closed sequent** is a derivation of its evaluation, with no
`seqSubstR` wrapper. -/
theorem replayR_closed {Γ : Sequent LRA} (d : ⊢ᴸᴷ¹ Γ)
    (hc : ∀ φ ∈ Γ, Semiformula.freeVariables φ = ∅) :
    OmegaDerivableR trueArithLitsR evInstR (cutRankR d) (ordN d : O) (Γ.map evR) := by
  have h := replayR (O := O) d (fun _ => 0)
  rwa [seqSubstR_eq_self hc] at h

/-- **The replay, with the cut rank placed inside a block.**  The form
predicative cut elimination consumes: if every cut of `d` is on a formula of
level `< ν`, the replayed derivation has cut rank below `blkTop ν`. -/
theorem replayR_closed_of_level {Γ : Sequent LRA} (d : ⊢ᴸᴷ¹ Γ) {ν : Lv} (hν : cutLvl d < ν)
    (hc : ∀ φ ∈ Γ, Semiformula.freeVariables φ = ∅) :
    OmegaDerivableR trueArithLitsR evInstR (Gamma0Note.blkTop ν) (ordN d : O) (Γ.map evR) :=
  (replayR_closed (O := O) d hc).mono_rank
    (le_of_lt (cutRankR_lt_blkTop d hν))

end Ramified

end OrdinalAnalysis
