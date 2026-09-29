/-
  `CollapsingLimit`: Layer 3 of `Interface.lean` (`CollapsingTower`), extended with the four
  "window" facts of elimination and the disjointness (□) that the limit case at `Ω_ω` needs
  (`idomega_design.md` §2.4):

  * `OmegaW`, `isPrin_OmegaW`, `supp_OmegaW`: `Ω_ω` is principal with empty support, exactly like
    every level's `Ω_{k+1}` (`CollapsingLevel.isPrin_Omega`/`supp_Omega`), so it is available to
    every hull.
  * `Omega_lt_OmegaW`: `Ω_ω` lies above every level.
  * `exists_Omega_of_lt_OmegaW`: everything below `Ω_ω` is already below some finite level —
    trivial for `ThetaV` because `Ω_ω` is the genuine constructor bounding every `Ω_{k+1}`, not a
    supremum that has to be approximated (§2.4: "the tower's cofinality becomes easy").
  * `add_Omega_OmegaW`: `Ω_ω` absorbs every level on the left under `+`, the same fixed-point
    argument one level up as `add_Omega_of_lt`/`omegaPow_Omega`.
  * `OmegaW_add_ne_Omega`: `Ω_ω + n` never collides with a level's `Ω_{k+1}` (`+` cannot shrink
    the left summand below itself, and `Ω_ω` is already strictly above every level).

  All seven fields of §2.4 type-check verbatim; none needed correction. The supporting `ThetaVNoteD`
  lemmas (`le_add_right`, `add_OmegaW_of_lt`, `add_Omega_OmegaW`, `exists_Omega_of_lt_OmegaW`,
  `OmegaW_add_ne_Omega`) are new here, proved directly from already-landed `ThetaV/{Arith,Order,
  Dom}.lean` facts (`add_omegaPow_of_lt`, `omegaPow_eq_self_iff`, `ThetaVTerm.isPrin_OmegaW`,
  `ThetaVTerm.exists_lt_Omega_of_lt_OmegaW`, `ThetaVNoteD.Omega_lt_OmegaW`) with no change to those
  files. `thetaVLimit` then fills `CollapsingLimit ThetaVNoteD` on top of `thetaVTower`
  (`ThetaVInstance.lean`), which already gives every `CollapsingTower` field for `ThetaVNoteD`.
-/
import OrdinalAnalysis.Ordinal.Collapsing.ThetaVInstance

set_option autoImplicit false

namespace OrdinalAnalysis
namespace ThetaVNoteD

-- `le_add_right` and `add_OmegaW_of_lt` live in `Ordinal/ThetaV/Arith.lean` (single copy).

/-- §2.4's `add_Omega_OmegaW`, specialised to `ThetaVNoteD`: `Ω_k + Ω_ω = Ω_ω`. -/
theorem add_Omega_OmegaW (k : ℕ) : Omega k + OmegaW = OmegaW :=
  add_OmegaW_of_lt (Omega_lt_OmegaW k)

/-- §2.4's `exists_Omega_of_lt_OmegaW`: every notation below `Ω_ω` is already below some finite
level. Trivial here since `Ω_ω` bounds every level by construction
(`ThetaVTerm.exists_lt_Omega_of_lt_OmegaW`, no `NF`/`Dom` side conditions needed). -/
theorem exists_Omega_of_lt_OmegaW {a : ThetaVNoteD} (h : a < OmegaW) : ∃ k, a < Omega k := by
  obtain ⟨k, hk⟩ := ThetaVTerm.exists_lt_Omega_of_lt_OmegaW (lt_iff.mp h)
  exact ⟨k, lt_iff.mpr hk⟩

/-- §2.4's `OmegaW_add_ne_Omega`: `Ω_ω + n` never collides with a level's `Ω_{k+1}` — `+` cannot
shrink the left summand below itself (`le_add_right`), and `Ω_ω` is already strictly above every
level (`Omega_lt_OmegaW`). -/
theorem OmegaW_add_ne_Omega (j k : ℕ) : OmegaW + ofNat j ≠ Omega k := by
  intro h
  have h1 : OmegaW ≤ OmegaW + ofNat j := le_add_right OmegaW (ofNat j)
  rw [h] at h1
  exact absurd h1 (not_le.mpr (Omega_lt_OmegaW k))

end ThetaVNoteD

namespace Notn

/-- Layer 3, extended: a tower of levels with a limit point `Ω_ω` above every level, absorbing
each level under `+`, bounding everything below it via some finite level, and never colliding
(even after a finite offset) with any level's `Ω_{k+1}` — the window facts of elimination and (□)
that Buchholz's argument needs at the limit case (`idomega_design.md` §2.4). -/
structure CollapsingLimit (O : Type) [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
    [CollapsingNotation O] extends CollapsingTower O where
  OmegaW : O
  isPrin_OmegaW : CollapsingNotation.IsPrin OmegaW
  supp_OmegaW : CollapsingNotation.supp OmegaW = ∅
  Omega_lt_OmegaW : ∀ k, (lev k).Omega < OmegaW
  exists_Omega_of_lt_OmegaW : ∀ {a}, a < OmegaW → ∃ k, a < (lev k).Omega
  add_Omega_OmegaW : ∀ k, CollapsingNotation.add (lev k).Omega OmegaW = OmegaW
  OmegaW_add_ne_Omega :
    ∀ j k, CollapsingNotation.add OmegaW (OrdinalNotation.ofNat j) ≠ (lev k).Omega

/-- `ThetaVNoteD` as a `CollapsingLimit`: `thetaVTower` (`ThetaVInstance.lean`) for the tower part,
`Ω_ω` and the five `ThetaVNoteD` lemmas above for the new fields. -/
noncomputable def thetaVLimit : CollapsingLimit ThetaVNoteD where
  toCollapsingTower := thetaVTower
  OmegaW := ThetaVNoteD.OmegaW
  isPrin_OmegaW := ThetaVTerm.isPrin_OmegaW
  supp_OmegaW := ThetaVNoteD.Ahull_OmegaW
  Omega_lt_OmegaW := ThetaVNoteD.Omega_lt_OmegaW
  exists_Omega_of_lt_OmegaW := fun h => ThetaVNoteD.exists_Omega_of_lt_OmegaW h
  add_Omega_OmegaW := ThetaVNoteD.add_Omega_OmegaW
  OmegaW_add_ne_Omega := ThetaVNoteD.OmegaW_add_ne_Omega

#print axioms thetaVLimit

end Notn
end OrdinalAnalysis
