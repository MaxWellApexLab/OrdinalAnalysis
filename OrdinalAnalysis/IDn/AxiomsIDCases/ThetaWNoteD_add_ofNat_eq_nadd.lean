import OrdinalAnalysis.IDn.AxiomsIDCases.Defs

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

/-- Finite ordinal and natural increments agree: `α + m = α ⊕ m`. -/
theorem ThetaWNoteD.add_ofNat_eq_nadd (a : ThetaWNoteD) :
    ∀ k : ℕ, a + ThetaWNoteD.ofNat k = ThetaWNoteD.nadd a (ThetaWNoteD.ofNat k)
  | 0 => by rw [ThetaWNoteD.ofNat_zero, ThetaWNoteD.add_zero, ThetaWNoteD.nadd_zero]
  | k + 1 => by
    have e1 : a + ThetaWNoteD.ofNat (k + 1) = (a + ThetaWNoteD.ofNat k) + ThetaWNoteD.one := by
      rw [ThetaWNoteD.add_assoc, ThetaWNoteD.add_one_eq_succ, ← ThetaWNoteD.ofNat_succ]
    rw [e1, ThetaWNoteD.add_one_eq_succ, ThetaWNoteD.add_ofNat_eq_nadd a k, ThetaWNoteD.ofNat_succ]
    show ThetaWNoteD.nadd (ThetaWNoteD.nadd a (ThetaWNoteD.ofNat k)) ThetaWNoteD.one =
      ThetaWNoteD.nadd a (ThetaWNoteD.nadd (ThetaWNoteD.ofNat k) ThetaWNoteD.one)
    rw [ThetaWNoteD.nadd_assoc]

theorem ThetaWNoteD.le_add_right' (a b : ThetaWNoteD) : a ≤ a + b := by
  have h := ThetaWNoteD.add_le_add_left a (ThetaWNoteD.zero_le' b)
  rwa [ThetaWNoteD.add_zero] at h


end Sums
end IDn
end OrdinalAnalysis
