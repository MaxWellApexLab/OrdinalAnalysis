import OrdinalAnalysis.IDn.AxiomsIDCases.Defs
import OrdinalAnalysis.IDn.AxiomsIDCases.ThetaWNoteD_add_ofNat_eq_nadd
import OrdinalAnalysis.IDn.AxiomsPA

set_option autoImplicit false
namespace OrdinalAnalysis

variable {n : ℕ} (k : Fin n)


namespace IDn


open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting


/-! ### Ordinal sums for Proposition 6.4 -/

section Sums


open ThetaWTerm in

-- case_skeleton: generated header ends here

/-- `(Ω ⊕ y) + Ω = Ω · 2` for `y ≺ Ω` (`Ω := Ω_n = Ω_{n-1}` of `AxiomsPA`'s top-level
convention): the summands of `y` are absorbed. -/
theorem ThetaWNoteD.nadd_Omega_add_Omega {y : ThetaWNoteD} (hy : y < (ThetaWNoteD.Omega (n - 1))) :
    ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) y + ThetaWNoteD.Omega (n - 1) =
      ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) (ThetaWNoteD.Omega (n - 1)) := by
  have hy' : ∀ e ∈ y.entries, e < ThetaWTerm.Omega (n - 1) := (ThetaWNoteD.lt_prin_iff (p := (ThetaWNoteD.Omega (n - 1))) trivial).mp hy
  have e1 : (ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) y).entries = ThetaWTerm.Omega (n - 1) :: y.entries := by
    rw [ThetaWNoteD.entries_nadd, ThetaWNoteD.entries_Omega]
    cases hys : y.entries with
    | nil => exact mergeL_nil_right _
    | cons y0 ys =>
      rw [mergeL_cons_cons_of_le [] ys
        (le_of_lt' (hy' y0 (by rw [hys]; exact List.mem_cons_self))), mergeL_nil_left]
  refine ThetaWNoteD.ext_entries ?_
  rw [ThetaWNoteD.entries_add, e1, ThetaWNoteD.entries_Omega, addL_cons, ThetaWNoteD.entries_nadd,
    ThetaWNoteD.entries_Omega, mergeL_cons_cons_of_le [] [] (le_refl' _), mergeL_nil_left]
  rw [List.filter_cons_of_pos (by simp [geb]),
    List.filter_eq_nil_iff.mpr (fun e he => by
      simp only [geb, decide_eq_true_eq]
      exact not_le_of_lt' (hy' e he))]
  rfl

/-- `ω · (Ω ⊕ c) + ω · Ω = Ω · 2`. -/
theorem omegaMul_beta_add_Omega (c : ℕ) :
    ThetaWNoteD.omegaMul (ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) (ThetaWNoteD.ofNat c)) +
        ThetaWNoteD.omegaMul (ThetaWNoteD.Omega (n - 1)) = OmegaTwo_pa (n := n) := by
  rw [ThetaWNoteD.omegaMul_nadd, ThetaWNoteD.omegaMul_Omega]
  exact ThetaWNoteD.nadd_Omega_add_Omega (omegaMul_ofNat_lt_Omega c)

/-- **Generalisation of `omegaMul_beta_add_Omega` to any level `j ≤ n - 1`** (needed since
`indAx_claim`'s induction is run at level `k`'s own top `Omega k.val`, not necessarily the
global top `Omega (n - 1)`): `ω·(Ω_{n-1} ⊕ c) + ω·Ω_j ⪯ Ω_{n-1}·2` — only `≤`, not `=`, since
`Omega j ≤ Omega (n - 1)` need not be equality. -/
theorem omegaMul_beta_add_Omega_le (c j : ℕ) (hj : j ≤ n - 1) :
    ThetaWNoteD.omegaMul (ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) (ThetaWNoteD.ofNat c)) +
        ThetaWNoteD.omegaMul (ThetaWNoteD.Omega j) ≤ OmegaTwo_pa (n := n) := by
  rw [ThetaWNoteD.omegaMul_nadd, ThetaWNoteD.omegaMul_Omega, ThetaWNoteD.omegaMul_Omega]
  calc ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) (ThetaWNoteD.omegaMul (ThetaWNoteD.ofNat c)) +
        ThetaWNoteD.Omega j
      ≤ ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) (ThetaWNoteD.omegaMul (ThetaWNoteD.ofNat c)) +
          ThetaWNoteD.Omega (n - 1) :=
        ThetaWNoteD.add_le_add_left _ (ThetaWNoteD.Omega_le_Omega_of_le_pa hj)
    _ = OmegaTwo_pa (n := n) := ThetaWNoteD.nadd_Omega_add_Omega (omegaMul_ofNat_lt_Omega c)

/-- The step of the induction on stages: `(ω·β + ω·γ) ⊕ k ≺ ω·β + ω·δ` for `γ ≺ δ`. -/
theorem stage_sum_lt (b : ThetaWNoteD) {g d : ThetaWNoteD} (h : g < d) (k : ℕ) :
    ThetaWNoteD.nadd (ThetaWNoteD.omegaMul b + ThetaWNoteD.omegaMul g) (ThetaWNoteD.ofNat k) <
      ThetaWNoteD.omegaMul b + ThetaWNoteD.omegaMul d := by
  rw [← ThetaWNoteD.add_ofNat_eq_nadd, ThetaWNoteD.add_assoc, ThetaWNoteD.add_ofNat_eq_nadd]
  exact ThetaWNoteD.add_lt_add_left _ (ThetaWNoteD.omegaMul_nadd_ofNat_lt h k)


end Sums
end IDn
end OrdinalAnalysis
