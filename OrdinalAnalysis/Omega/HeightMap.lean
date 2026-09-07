/-
  Transport of derivations along a strictly monotone map of heights.

  The rules of the ω-calculus mention the height only through `<` between a
  premise's height and the conclusion's.  So any strictly monotone map from
  one notation system to another carries derivations across, at the same
  cut rank, without touching the sequent.  This is how a derivation built
  below `ε₀` in `NONote` becomes a derivation in the Veblen notations, where
  the heights above `ε₀` live.
-/
import OrdinalAnalysis.Omega.Calculus

set_option autoImplicit false

namespace OrdinalAnalysis.OmegaDerivable

open LO LO.FirstOrder

variable {L : Language}
variable {O O' : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
  [LinearOrder O'] [WellFoundedLT O'] [OrdinalNotation O']

/-- **Height transport.**  A strictly monotone map of heights preserves
derivability, at the same rank. -/
theorem map_height {A : Literals L} {I : Instantiation L} {r : ℕ}
    (e : O → O') (he : StrictMono e) :
    ∀ {α : O} {Γ : Sequent L}, OmegaDerivable A I r α Γ → OmegaDerivable A I r (e α) Γ := by
  intro α Γ h
  induction h with
  | atom hφ => exact atom hφ
  | identity rl v => exact identity rl v
  | verum => exact verum
  | or hβ _ ih => exact or (he hβ) ih
  | and hβ hγ _ _ ihφ ihψ => exact and (he hβ) (he hγ) ihφ ihψ
  | omegaRule β hβ _ ih => exact omegaRule (fun n => e (β n)) (fun n => he (hβ n)) ih
  | exs n hβ _ ih => exact exs n (he hβ) ih
  | contraction ss _ ih => exact contraction ss ih
  | cut hc hβ hγ _ _ ihφ ihψ => exact cut hc (he hβ) (he hγ) ihφ ihψ

end OrdinalAnalysis.OmegaDerivable
