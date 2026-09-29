/-
  **The upper bound of `ID_ω`, headline.**  For every countable notation `a ≺ Ω₁`, `IDw WFormWc`
  proves transfinite induction up to `a` for the free predicate `X`:
  `TI_a(≺, X) :≡ Prog(≺, X) → ∀x (x ≺ ⌜a⌝ → X x)` (`tiUptoSentence` of `IDw/TISentence.lean`, the
  order being that of `orderFormulas`).  This is the analysis bound
  `|ID_ω| ≥ ψ₀(ε_{Ω_ω+1})` read from above: `ψ₀(ε_{Ω_ω+1})` is the supremum of the countable
  notations, cofinally the terms `ϑ₀(ω_m(Ω_ω + 1))` (`Upper.exists_lt_tower`).

  The proof is `Upper.upper_bound` (`IDw/UpperBound.lean`): in every arithmetically standard model
  of `IDw WFormWc`, `ϑ₀(ω_m(Ω_ω + 1)) ∈ J(0, ·)` (`W_theta_tau`, BP78 Theorems 2 and 3), then
  downward closure and the induction scheme of level `0`; completeness
  (`Lift.provable_of_models`) turns truth in the standard models into provability.
-/
import OrdinalAnalysis.IDw.UpperBound

set_option autoImplicit false

namespace OrdinalAnalysis.IDw.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- **The upper bound of `ID_ω`**: for every notation `a ≺ Ω₁`, `IDw WFormWc` proves transfinite
induction for the free predicate `X` up to `a`. -/
theorem idw_upper_bound :
    ∀ a : ThetaVNoteD, a < ThetaVNoteD.Omega 0 →
      IDw WFormWc ⊢ tiUptoSentence orderFormulas a :=
  fun _ ha => upper_bound ha

/-- The same, with the bound on the terms: `a.1 < Ω₁`. -/
theorem idw_upper_bound_term :
    ∀ a : ThetaVNoteD, a.1 < ThetaVTerm.Omega 0 →
      IDw WFormWc ⊢ tiUptoSentence orderFormulas a :=
  fun _ ha => upper_bound ha

end OrdinalAnalysis.IDw.Upper
