/-
  **The ordinal analysis of `ID_ω`** (Buchholz–Pohlers 1978; Buchholz 1992 for the collapsing):
  `|ID_ω| = ψ₀(ε_{Ω_ω+1})`, in the form of the `ID_n`/`ID_{<ω}` headlines — `ID_ω` proves
  transfinite induction along the notation order below every notation under `Ω₁` (these are cofinal
  in `ψ₀(ε_{Ω_ω+1})`, `Upper.exists_lt_tower`), and not up to `Ω₁` itself.
-/
import OrdinalAnalysis.IDw.UpperFinal
import OrdinalAnalysis.IDw.CollapseCorollaryW

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open Upper

/-- **`|ID_ω| = ψ₀(ε_{Ω_ω+1})`.** -/
theorem idw_analysis :
    (∀ a : ThetaVNoteD, a < ThetaVNoteD.Omega 0 →
        IDw WFormWc ⊢ tiUptoSentence orderFormulas a) ∧
      ¬ IDw WFormWc ⊢ tiUptoSentence orderFormulas (ThetaVNoteD.Omega 0) :=
  ⟨idw_upper_bound, idw_lower_bound⟩

end IDw

end OrdinalAnalysis
