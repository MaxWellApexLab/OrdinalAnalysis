/-
  The missing tower-cofinality fact for `IDn`'s sharp lower bound.

  An earlier pass at `IDn/LowerLt.lean`
  flagged exactly this gap: "Need: `ω_j(Ω_{n-1}+1) < theta n zero` for the specific finite `j`
  `elimination_iter` leaves … grepped … not found on disk." The direction is the reverse of
  `Ordinal/ThetaW/HullCofinal.lean`'s `dom_lt_theta0_omegaTower`/`exists_lt_theta0_omegaTower_of_levLT`
  (which bound a *given* term from *above* by some tower `ω_m(Ω_n+1)`, used for the upper bound);
  here every *fixed* finite tower `ω_m(Ω_k+1)` must lie *below* `ϑ_{k+1}(0)` — the closure
  ordinal is a strict upper bound of its own generating sequence.

  Closed here from library facts already on disk, with no new machinery: `ThetaWTerm.
  Omega_lt_theta_succ` (`Ω_k ≺ ϑ_{k+1}(0)`, a clause of the raw term order), `succ_lt_prin`/
  `omegaPow_lt_prin` (`Ordinal/ThetaW/Arith.lean`: a principal term absorbs `succ`/`ω^·` of
  anything already below it), composed by a one-line induction on the tower height. The second
  theorem (`theta0_hat_lt_c`) is the actual "notation lemma" the sharp lower bound
  (`IDn/LowerSharp.lean`) needs: `ϑ₀(ω^{μ+μ+α}) ≺ c_n = ϑ₀(ϑ_n 0)` whenever `μ, α ≺ ϑ_n(0)` and
  neither has a level-`0` subterm of its own (`E_0 = ∅` for both — automatic for the heights the
  collapsing chain produces, which are built from `Omega`/`one`/`ofNat`/`+` at levels `≥ 1`
  only, never from a `ϑ_0`-application), via `Ordinal/ThetaW/Hull.lean`'s `Ehull` coefficient
  calculus (`Ehull_add_subset_hull`, `Ehull_omegaPow_hull`, `Ehull_eq_nil_iff`) and
  `ThetaWTerm.theta_lt_theta_of_lt`.
-/
import OrdinalAnalysis.Ordinal.ThetaW.HullCofinal

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWNoteD

open ThetaWTerm

/-! ### `ϑ_{k+1}(0)`, packaged as a domain-safe notation -/

/-- `ϑ_{k+1}(0)`: always in the domain, since `G` vanishes on `zero` (no subterms at all). -/
def thetaZero (k : ℕ) : ThetaWNoteD :=
  ⟨ThetaWTerm.theta (k + 1) ThetaWTerm.zero,
    (ThetaWTerm.nf_theta_iff _ _).mpr ThetaWTerm.nf_zero,
    ThetaWTerm.dom_theta_of_G_nil ThetaWTerm.dom_zero (ThetaWTerm.G_nil (k + 1))⟩

theorem thetaZero_val (k : ℕ) : (thetaZero k).1 = ThetaWTerm.theta (k + 1) ThetaWTerm.zero := rfl

theorem isPrin_thetaZero (k : ℕ) : ThetaWTerm.IsPrin (thetaZero k).1 := trivial

/-- `Ω_k ≺ ϑ_{k+1}(0)`, as notations. -/
theorem Omega_lt_thetaZero (k : ℕ) : Omega k < thetaZero k :=
  lt_iff.mpr (ThetaWTerm.Omega_lt_theta_succ k ThetaWTerm.zero)

/-- `Ω_k + 1 ≺ ϑ_{k+1}(0)`: `thetaZero k` is principal, so it absorbs the successor of anything
already below it. -/
theorem Omega_add_one_lt_thetaZero (k : ℕ) : Omega k + one < thetaZero k := by
  have h := succ_lt_prin (isPrin_thetaZero k) (Omega_lt_thetaZero k)
  rwa [add_one_eq_succ]

/-! ### The tower-cofinality fact -/

/-- **Every finite ω-tower over `Ω_k + 1` lies strictly below `ϑ_{k+1}(0)`.** The missing fact
flagged above: closed from `omegaPow_lt_prin` and induction on the
tower height, since `thetaZero k` is principal and `omegaPow` never escapes a principal term
that already bounds its argument. -/
theorem omegaTower_lt_thetaZero (k : ℕ) : ∀ m : ℕ, omegaTower m (Omega k + one) < thetaZero k
  | 0 => Omega_add_one_lt_thetaZero k
  | m + 1 => by
      rw [omegaTower_succ]
      exact omegaPow_lt_prin (isPrin_thetaZero k) (omegaTower_lt_thetaZero k m)

/-! ### The notation lemma for the sharp lower bound: `ϑ₀(ω^{μ+μ+α}) ≺ c_n` -/

/-- `E_0` vanishes on a sum of two notations each with vanishing `E_0`. -/
theorem Ehull_add_eq_empty {a b : ThetaWNoteD} (ha : Ehull 0 a = ∅) (hb : Ehull 0 b = ∅) :
    Ehull 0 (a + b) = ∅ :=
  Set.eq_empty_of_subset_empty
    ((Ehull_add_subset_hull 0 a b).trans (by rw [ha, hb]; simp))

/-- **The notation lemma `IDn/LowerSharp.lean` needs.** For `n ≥ 1`: if `μ, α ≺ ϑ_n(0)` and
neither has a level-`0` subterm of its own (`E_0(μ) = E_0(α) = ∅`), then
`ϑ₀(ω^{μ+μ+α}) ≺ c_n = ϑ₀(ϑ_n(0))`.

Proof: `μ + μ + α ≺ ϑ_n(0)` (`add_lt_prin` twice, `thetaZero (n-1)`'s own principality), hence
`ω^{μ+μ+α} ≺ ϑ_n(0)` (`omegaPow_lt_prin`); then `ϑ₀` is order-preserving on this argument against
`ϑ_n(0)` (`theta_lt_theta_of_lt`), since `E_0(ω^{μ+μ+α}) = E_0(μ+μ+α) = ∅`
(`Ehull_omegaPow_hull`, `Ehull_add_eq_empty` from the two hypotheses), so the side condition of
`theta_lt_theta_of_lt` is vacuous. -/
theorem theta0_hat_lt_c {n : ℕ} (hn : 0 < n) {μ α : ThetaWNoteD}
    (hμ : μ < thetaZero (n - 1)) (hα : α < thetaZero (n - 1))
    (hμE : Ehull 0 μ = ∅) (hαE : Ehull 0 α = ∅) :
    ThetaWTerm.theta 0 (omegaPow (μ + μ + α)).1 <
      ThetaWTerm.theta 0 (ThetaWTerm.theta n ThetaWTerm.zero) := by
  have hnz : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
  have hp : ThetaWTerm.IsPrin (thetaZero (n - 1)).1 := isPrin_thetaZero (n - 1)
  have harg : μ + μ + α < thetaZero (n - 1) := add_lt_prin hp (add_lt_prin hp hμ hμ) hα
  have hargOmegaPow : omegaPow (μ + μ + α) < thetaZero (n - 1) := omegaPow_lt_prin hp harg
  have hargOmegaPow' : (omegaPow (μ + μ + α)).1 < ThetaWTerm.theta n ThetaWTerm.zero := by
    have h := lt_iff.mp hargOmegaPow
    rwa [thetaZero_val, hnz] at h
  refine ThetaWTerm.theta_lt_theta_of_lt hargOmegaPow' fun g hg => ?_
  exfalso
  have hEomegaPow : Ehull 0 (omegaPow (μ + μ + α)) = ∅ := by
    rw [Ehull_omegaPow_hull]
    exact Ehull_add_eq_empty (Ehull_add_eq_empty hμE hμE) hαE
  have hgmem : (⟨g, (omegaPow (μ + μ + α)).2.1.of_mem_E hg,
      (omegaPow (μ + μ + α)).2.2.of_mem_E hg⟩ : ThetaWNoteD) ∈
      Ehull 0 (omegaPow (μ + μ + α)) := hg
  rw [hEomegaPow] at hgmem
  exact hgmem

end ThetaWNoteD

end OrdinalAnalysis
