import OrdinalAnalysis.KPi.Ord.Hull

/-!
# Sanity statements for the ordinal notation system of B92 §4

`kpiOrd = ψ_{Ω₁}(ε_{I+1})` is the ordinal `ψ` of B92's Main Theorem 4.9 (no numeric identification claimed).
The remaining statements are direct consequences of Lemma 4.5 (a), (i), (c) and check the definitions
against expected values (`ψ_κ α < κ`, monotonicity, `φ`-closure, `ε₀ ≤ ψ_{Ω₁}(0)`).
-/

set_option autoImplicit false

open Ordinal Cardinal Set Order

noncomputable section

namespace OrdinalAnalysis.KPi.Ord

theorem omega_one_mem_Rset : ω_ 1 ∈ Rset := by
  have := omega_succ_mem_Rset (σ := 0) Iord_pos
  simpa using this

/-- `ψ_{Ω₁}(ε_{I+1})` (B92's value for the bound on `|KPi|`; no numeric identification claimed). -/
def kpiOrd : O := psiK (ω_ 1) (Ordinal.epsilon (Iord + 1))

theorem kpiOrd_lt : kpiOrd < ω_ 1 := psiK_lt omega_one_mem_Rset _

/-- sanity: `ψ_κ α < κ` for `κ ∈ R`. -/
theorem sanity_lt {κ : O} (hκ : κ ∈ Rset) (α : O) : psiK κ α < κ := psiK_lt hκ α

/-- sanity: `ψ_κ` is monotone in `α`. -/
theorem sanity_mono {κ : O} (hκ : κ ∈ Rset) {α α' : O} (h : α ≤ α') : psiK κ α ≤ psiK κ α' :=
  (psiK_mono hκ h).1

/-- sanity: `ψ_{Ω₁}(0)` is `φ`-closed. -/
theorem sanity_phi_closed {x y : O} (hx : x < psiK (ω_ 1) 0) (hy : y < psiK (ω_ 1) 0) :
    veblen x y < psiK (ω_ 1) 0 :=
  psiK_veblen_lt omega_one_mem_Rset 0 hx hy

/-- sanity: `ε₀ ≤ ψ_{Ω₁}(0)`. -/
theorem sanity_epsilon0_le : Ordinal.epsilon 0 ≤ psiK (ω_ 1) 0 := by
  rw [epsilon_eq_deriv, deriv_zero_right]
  exact nfp_le_fp (isNormal_opow one_lt_omega0).strictMono.monotone bot_le
    (opow_psiK omega_one_mem_Rset 0).le

end OrdinalAnalysis.KPi.Ord
