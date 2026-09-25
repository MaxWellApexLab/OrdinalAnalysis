import OrdinalAnalysis.IDn.Theorem
import OrdinalAnalysis.IDn.Internal.OrderFacts

/-!
# The upper bounds of `ID_n` and `ID_{<ω}` without hypotheses

`Internal/OrderFacts.lean` proves every field of `InternalOrderFacts` for the coded order
(`codedOrderFacts`), so the in-model level tower of `IDn/Theorem.lean` applies outright.
-/

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Upper

open OrdinalAnalysis.IDn.Internal

/-- **The upper bound of `ID_n`**: for every notation `a ≺ c_n = ϑ₀(ϑ_n 0)`, `ID_n` for the
well-ordering forms proves transfinite induction for the free predicate `X` up to `a`. -/
theorem idn_upper_bound' (n : ℕ) (hn : 0 < n) :
    ∀ a : ThetaWNoteD, a < ThetaWNoteD.c n →
      IDn n (WForms codedOrderFacts.toOrderFormulas n) ⊢
        tiUptoSentence codedOrderFacts.toOrderFormulas (Fin n) a :=
  idn_upper_bound codedOrderFacts n hn

/-- **The upper bound of `ID_{<ω}`**: for every countable notation `a ≺ Ω₁`, `ID_{<ω}` for the
well-ordering forms proves transfinite induction for the free predicate `X` up to `a`. -/
theorem idlt_upper_bound' :
    ∀ a : ThetaWNoteD, a.1 < ThetaWTerm.Omega 0 →
      IDlt (WFormsOmega codedOrderFacts.toOrderFormulas) ⊢
        tiUptoSentence codedOrderFacts.toOrderFormulas ℕ a :=
  idlt_upper_bound codedOrderFacts

end OrdinalAnalysis.IDn.Upper
