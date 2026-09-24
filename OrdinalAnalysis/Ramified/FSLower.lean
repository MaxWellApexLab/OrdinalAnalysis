/-
  The bound half of the Feferman-Schutte theorem for the semiformal ramified
  calculus `RA_∞` (`OmegaDerivableR`, `Ramified/Calculus.lean`).

  `Ramified/Boundedness.lean` proves the cut-free case: no cut-free
  `RA_∞`-derivation, of any height, proves transfinite induction along the
  whole coded Veblen ordering `gamma0OrderR` for the free predicate `X`
  (`not_derivable_TI_R_gamma0`).  This file removes the cut-free restriction.

  The route is predicative cut elimination.  Given a cut rank `ρ : Gamma0Note`,
  raise it to `omegaPow (ρ ⊕ 1)`, which exceeds `ρ` because `ρ < ρ ⊕ 1 ≤
  omegaPow (ρ ⊕ 1)` (in fact `<`, since `omegaPow` is strictly monotone and
  already dominates its argument).  `Ramified/PredicativeCutGeneral.lean`'s
  `predicativeCut_veblen` then eliminates that rank block for free (cut rank
  `0` needs no side condition on `PowClosed`), producing a cut-free derivation
  of the same sequent at height `veblenStructure.veblen (ρ ⊕ 1) h`, still a
  `Gamma0Note`.  `not_derivable_TI_R_gamma0` refutes that.

  Every `Gamma0Note` used here — the cut rank `ρ`, the height `h`, and the
  cut-free height produced along the way — is a notation for an ordinal below
  `Γ₀`, by construction of the type `Gamma0Note` (it is the type of Cantor
  normal forms in the Veblen hierarchy below `Γ₀`, together with the proof
  that they normalise the coded ordinal `Γ₀` itself).  So `fs_lower` says: no
  `RA_∞`-derivation with both cut rank and height below `Γ₀` derives `TI(≺)`
  along the whole Veblen ordering of `Γ₀`.  This is exactly the bound half of
  Schutte's form of the Feferman-Schutte theorem for `RA_∞` — every initial
  segment `TI(≺↾a)`, `a < Γ₀`, is meant to be autonomously derivable (the
  companion upper half, not proved here), while no height or cut rank below
  `Γ₀` suffices for the whole order. Only the bound half is claimed in this
  file; the autonomy half is a separate, substantially larger argument.

  The levels range over all notations below `Γ₀`, so the cut ranks in play are
  genuinely transfinite.  `fs_lower_junk` states the bound for the calculus
  whose atomic axioms include the junk literals (`Ramified/Literals.lean`'s
  `junkLitsR`: a name that is not a `Good` code of a level denotes, at that
  level, the empty set); `fs_lower` is its restriction to the arithmetic
  literals.
-/
import OrdinalAnalysis.Ramified.Boundedness
import OrdinalAnalysis.Ramified.PredicativeCutGeneral

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

/-- **The bound half of Feferman-Schutte for `RA_∞`, with the junk literals.**  No
derivation of the semiformal ramified calculus whose atomic axioms are the true
arithmetic literals together with the junk literals (every non-`Good` name at a
level denotes the empty set), with cut rank `ρ` and height `h` both below `Γ₀`,
proves transfinite induction along the whole coded Veblen ordering `gamma0OrderR`
for the free predicate `X`. -/
theorem fs_lower_junk (ρ h : Gamma0Note) :
    ¬ OmegaDerivableR junkLitsR evInstR ρ h [evR (TIR gamma0OrderR.prec)] := by
  intro hder
  -- Raise the cut rank to a Veblen block strictly above `ρ`.
  set ξ : Gamma0Note := Gamma0Note.nadd ρ 1 with hξ_def
  have hξ1 : (1 : Gamma0Note) ≤ ξ := Gamma0Note.one_le_nadd_one ρ
  have hρlt : ρ < Gamma0Note.omegaPow ξ :=
    lt_of_le_of_lt (Gamma0Note.le_omegaPow_self ρ)
      (Gamma0Note.omegaPow_lt_omegaPow (Gamma0Note.lt_nadd_one ρ))
  have hraised :
      OmegaDerivableR junkLitsR evInstR (Gamma0Note.omegaPow ξ) h
        [evR (TIR gamma0OrderR.prec)] :=
    hder.mono_rank hρlt.le
  -- Eliminate that rank block: cut-free at rank `0`, height `φ_ξ(h)`.
  have hcut :
      OmegaDerivableR junkLitsR evInstR 0 (Gamma0Note.veblenStructure.veblen ξ h)
        [evR (TIR gamma0OrderR.prec)] :=
    OmegaDerivableR.predicativeCut_veblen memFree_junkLitsR hξ1 hraised
  -- No cut-free derivation, at any height, proves `TI` along the whole order.
  exact not_derivable_TI_R_gamma0_junk (Gamma0Note.veblenStructure.veblen ξ h) hcut

/-- **The bound half of Feferman-Schutte for `RA_∞`.**  No derivation of the
semiformal ramified calculus, with cut rank `ρ` and height `h` both below
`Γ₀`, proves transfinite induction along the whole coded Veblen ordering
`gamma0OrderR` for the free predicate `X`. -/
theorem fs_lower (ρ h : Gamma0Note) :
    ¬ OmegaDerivableR trueArithLitsR evInstR ρ h [evR (TIR gamma0OrderR.prec)] := fun hder =>
  fs_lower_junk ρ h (hder.mono_lits trueArithLitsR_le_junkLitsR)

end Ramified

end OrdinalAnalysis
