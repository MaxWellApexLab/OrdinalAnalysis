/-
  **The collapsing corollary for `ID_ω`**, discharging `IDw.CollapseCorollary` (`IDw/LowerBound.lean`),
  and the lower bound of `IDw WFormWc` with no hypothesis.

  Route (Buchholz 1992, Theorem 3.16 + Theorem 4.8; Freund, arXiv:2204.09321, Corollary 7.2):

  1. `embedding_theorem_xfree` gives, at every nice operator, cut rank `OmegaPlus m = Ω_ω + m`
     (and, after the transfer of `IDw/LowerBound.lean`, a `Σ(Ω₁)` end-sequent).
  2. **`elimination_OmegaW`** (`IDw/Elimination.lean`, Freund Exercise 7.1 (c) with `ρ = Ω_ω`,
     `Ω_ω + i ≠ Ω_j` for all `i, j`) lowers the cut rank `Ω_ω + m` to `Ω_ω` in `m` steps,
     at height `ω_m(α)`.
  3. `collapseW` at the limit `μ = Ω_ω`, i.e. `muBarW ⊤` (`IDw/Collapsing/Final.lean`), at level `0`,
     `γ = 0`, `X = ∅` (`collapseW_zero_bound`): the stage `b = ψ₀(ω^{Ω_ω·2+α}) ≺ Ω₁`, and a
     derivation of the bounded sequent `φ^b` at cut rank and height `b`.

  Unlike the corollary of `IDn` (`IDn/CollapseCorollary.lean`, and `CollapseCorollarySharp.lean`
  for the sharp bound `c_n`), **no predicative cut elimination on a window `[Ω̄_n, Ω_{n+2})` is
  needed**: `Ω_ω` is not regular, the cut rank is lowered straight to `Ω_ω = muBarW ⊤`, and the
  collapse works at the limit (`IDw/Collapsing/CaseCut.lean` treats the cut of rank below `Ω_ω` for
  every `m : WithTop ℕ`).
-/
import OrdinalAnalysis.IDw.LowerBound
import OrdinalAnalysis.IDw.Elimination
import OrdinalAnalysis.IDw.Collapsing.Final
import OrdinalAnalysis.IDw.EmbedHypsAll

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.IDw.Upper

/-- **The collapsing corollary for `ID_ω`** (`CollapseCorollary`, proved), for every positive
operator form. -/
theorem collapseCorollaryW {A : FormJ} (hA : PositiveP A) : CollapseCorollary A := by
  intro m φ hφ α d
  have hH : ThetaVNoteD.NiceS (ThetaVNoteD.HopS ThetaVNoteD.zero) :=
    ThetaVNoteD.HopS_nice ThetaVNoteD.zero
  -- lower the cut rank `Ω_ω + m` to `Ω_ω`
  have d₁ := IDwDerivable.elimination_OmegaW hH m d
  -- collapsing at the limit, at level `0`
  obtain ⟨b, hb, D⟩ := Collapsing.collapseW_zero_bound (m := ⊤) hA 0 hφ d₁
  refine ⟨b, ?_, _, ThetaVNoteD.HopS_nice _, D⟩
  rw [hb]
  exact Collapsing.psi_lt_Omega 0 _

/-- **`IDw WFormWc ⊬ TI_{Ω₁}(≺, X)`**: transfinite induction along the ϑ-order up to `Ω₁`, for the
free predicate `X`, is not provable in `ID_ω` (`IDw` with the uniform well-ordering form
`WFormWc`); with `Upper.idw_upper_bound` (every notation `a ≺ Ω₁` is provable) this is
`|ID_ω| = ψ₀(ε_{Ω_ω+1})`. No hypothesis: `EmbedHyps` is `embedHyps`, positivity is
`positiveP_WFormWc`. -/
theorem idw_lower_bound :
    ¬ IDw WFormWc ⊢ tiUptoSentence orderFormulas (ThetaVNoteD.Omega 0) :=
  idw_lower_bound_of (embedHyps WFormWc) (collapseCorollaryW positiveP_WFormWc)

end IDw

end OrdinalAnalysis
