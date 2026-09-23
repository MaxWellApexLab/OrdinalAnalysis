/-
  Cutting away the negated axioms of a theory, in the ramified calculus, and the
  finite-part rank bound the sharp upper bound will need.

  ## `cut_axioms_of`

  This is `Gentzen/CutAxioms.lean`'s `cut_axioms_of` ported from the unramified
  `OmegaDerivable` to `OmegaDerivableR`, with one simplification the port earns:
  there the cut rank is a natural number bounding formula *complexity*, and each
  step has to re-derive a bigger rank `r' := max r (φ.complexity + 1)` before it
  may cut on `φ`; here the cut rank `ρ` is already an ordinal notation fixed by
  the caller, and the hypothesis `hrk` supplies `rank φ < ρ` for every axiom
  directly, so no such bump is needed — the whole derivation runs at the single
  rank `ρ` throughout, and only `OmegaDerivableR.mono_rank` is used, to lift the
  rank-`0` axiom derivations `hax` supplies up to `ρ`.

  The proof is otherwise the Gentzen one line for line: cut the axioms of `Δ` out
  one at a time, from the last to the first, replaying `Sequent.embed_cons` to
  see the negated list as a cons, cutting the freshly-exposed negated axiom
  against its (rank-lifted) derivation, and recursing on the shorter list.

  ## The finite-part rank bound

  `Rank.lean`'s `rank_lt_block_of_level` bounds the rank of a level-`< ν`
  formula by `ω · ν`.  The finer bound says *how far* below, as a function of
  the formula's logical complexity: `rank` and `complexity` are the same
  structural recursion, differing only at the atoms, and an atom of level `μ`
  costs at most `ω · μ`, so

      rank φ ≤ ω · lvlOf φ ⊕ complexity φ       (`rank_le_omegaMul_lvlOf_nadd`).
-/
import OrdinalAnalysis.Ramified.Evaluate
import OrdinalAnalysis.Ordinal.Veblen.RankSegments

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Derivation

/-! ### `cut_axioms_of` -/

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- **Cutting away the negated axioms of a theory `T`**, one at a time, at a
fixed cut rank `ρ`, given that every axiom of `T` is cut-free derivable at some
height in `O` and has rank below `ρ`. -/
theorem cut_axioms_of (T : Theory LRA) {ρ : Gamma0Note}
    (hax : ∀ σ ∈ T, ∃ β : O, OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb σ : Proposition LRA)])
    (hrk : ∀ σ ∈ T, rank (evR (Rewriting.emb σ : Proposition LRA)) < ρ) :
    ∀ (Δ : List (Sentence LRA)), (∀ σ ∈ Δ, σ ∈ T) → ∀ {α : O} {Θ : Sequent LRA},
      OmegaDerivableR trueArithLitsR evInstR ρ α (Θ ++ (∼Sequent.embed Δ).map evR) →
      ∃ α' : O, OmegaDerivableR trueArithLitsR evInstR ρ α' Θ
  | [], _, α, Θ, h => ⟨α, by simpa [List.tilde_def] using h⟩
  | σ :: Δ, hΔ, α, Θ, h => by
      obtain ⟨β, hσ⟩ := hax σ (hΔ σ (by simp))
      set φ : Proposition LRA := evR (Rewriting.emb σ : Proposition LRA) with hφ
      set rest : Sequent LRA := (∼Sequent.embed Δ).map evR with hrest
      have h' : OmegaDerivableR trueArithLitsR evInstR ρ α (Θ ++ ((∼φ) :: rest)) := by
        have e : (∼Sequent.embed (σ :: Δ)).map evR = (∼φ) :: rest := by
          simp only [Sequent.embed_cons, List.tilde_def, List.map_cons, hφ, hrest, evR_neg]
        rw [← e]
        exact h
      have hL : OmegaDerivableR trueArithLitsR evInstR ρ α ((∼φ) :: (Θ ++ rest)) := by
        refine OmegaDerivableR.contraction ?_ h'
        intro x hx
        simp only [List.mem_append, List.mem_cons] at hx ⊢
        tauto
      have hR : OmegaDerivableR trueArithLitsR evInstR ρ β (φ :: []) :=
        hσ.mono_rank (gamma0_zero_le ρ)
      have hcrk : rank φ < ρ := hrk σ (hΔ σ (by simp))
      have hcut : OmegaDerivableR trueArithLitsR evInstR ρ
          (OrdinalNotation.succ (OrdinalNotation.nadd β α)) ([] ++ (Θ ++ rest)) :=
        OmegaDerivableR.cut hcrk
          (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_left _ _))
          (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_right _ _)) hR hL
      exact cut_axioms_of T hax hrk Δ (fun τ hτ => hΔ τ (List.mem_cons_of_mem _ hτ))
        (by simpa using hcut)

/-! ### The finite-part rank bound

`Rank.lean`'s `rank_le_omegaMul_lvlOf_nadd` is the bound; here it is lifted to
an arbitrary level above `lvlOf φ`, and to the coarser `ω`-power form. -/

/-- **The finite-part rank bound, at an arbitrary level above `lvlOf φ`**:
`rank φ ≤ ω · ν ⊕ complexity φ` whenever `lvlOf φ ≤ ν`. -/
theorem rank_le_nadd_ofNat_complexity_of_level {n : ℕ} {ν : Lv} {φ : Semiformula LRA ℕ n}
    (h : lvlOf φ ≤ ν) :
    rank φ ≤ Gamma0Note.nadd (omegaMul ν) (Gamma0Note.ofNat φ.complexity) :=
  le_trans (rank_le_omegaMul_lvlOf_nadd φ)
    (OrdinalNotation.nadd_le_nadd_left _ (omegaMul_le_omegaMul h))

/-- **Every rank is its level's `ω`-power plus a finite part** — the coarser
form of `rank_le_omegaMul_lvlOf_nadd`, through `ω · μ ≤ ω ^ μ`. -/
theorem rank_le_omegaPowLv_lvlOf_nadd {n : ℕ} (φ : Semiformula LRA ℕ n) :
    rank φ ≤ OrdinalNotation.nadd (omegaPowLv (lvlOf φ)) (OrdinalNotation.ofNat φ.complexity) :=
  le_trans (rank_le_omegaMul_lvlOf_nadd φ)
    (OrdinalNotation.nadd_le_nadd_left _ (omegaMul_le_omegaPowLv (lvlOf φ)))

end Ramified

end OrdinalAnalysis
