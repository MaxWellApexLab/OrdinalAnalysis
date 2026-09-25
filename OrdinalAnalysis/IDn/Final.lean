import OrdinalAnalysis.IDn.EmbedHypsAll
import OrdinalAnalysis.IDn.AxiomsIDCases.indBody_inst
import OrdinalAnalysis.IDn.Retract

/-!
# The ordinal analysis of `ID_n`, with no hypotheses

The embedding hypotheses of `IDn/Embed.lean` are all discharged: the last field, the
`I_k`-induction axioms, is `indAx_axiom` (Freund, Proposition 6.4, at every level). The
well-ordering forms are positive and level-bounded, so the two-sided theorem at
`c_n = ϑ₀(ϑ_n 0)` holds outright.
-/

set_option autoImplicit false

namespace OrdinalAnalysis.IDn

open LO LO.FirstOrder
open OrdinalAnalysis.IDn.Upper

variable {n : ℕ}

/-- The `I_k`-induction axioms of the well-ordering forms are derivable, at every level. -/
theorem wForms_indAx (hn : 0 < n) :
    ∀ (k : Fin n), PositiveIn k (WForms orderFormulas n k) →
      (∀ j, XFreeL (WForms orderFormulas n j)) → ∀ F : Semiformula (LXIn n) ℕ 1,
        AxDerivable (WForms orderFormulas n) (indAxAt k (WForms orderFormulas n k) F) :=
  fun k hA hX F => indAx_axiom k (WForms orderFormulas n) (wForms_levelBounded orderFormulas n) hA hX F

/-- **`|ID_n| = c_n = ϑ₀(ϑ_n 0)`**: `ID_n` (for the well-ordering operator forms) proves
transfinite induction for the free predicate `X` up to every notation below `c_n`, and does
not prove it at `c_n`. -/
theorem idn_analysis (hn : 0 < n) :
    (∀ a : ThetaWNoteD, a < ThetaWNoteD.c n →
        IDn n (WForms orderFormulas n) ⊢ tiUptoSentence orderFormulas (Fin n) a) ∧
      ¬ IDn n (WForms orderFormulas n) ⊢
        tiUptoSentence orderFormulas (Fin n) (ThetaWNoteD.c n) :=
  idn_theorem_final hn (wForms_indAx hn)

/-- The lower bound alone, at `Ω₁`. -/
theorem idn_lower_bound_unconditional (hn : 0 < n) :
    ¬ IDn n (WForms orderFormulas n) ⊢ tiUptoSentence orderFormulas (Fin n) (ThetaWNoteD.Omega 0) :=
  idn_lower_bound_final hn (wForms_indAx hn)

/-- The `I_k`-induction axioms of the well-ordering forms, at every number of levels. -/
theorem wForms_indAx_all :
    ∀ (m : ℕ) (k : Fin m), PositiveIn k (WForms orderFormulas m k) →
      (∀ j, XFreeL (WForms orderFormulas m j)) → ∀ F : Semiformula (LXIn m) ℕ 1,
        AxDerivable (WForms orderFormulas m) (indAxAt k (WForms orderFormulas m k) F) :=
  fun m k hA hX F => indAx_axiom k (WForms orderFormulas m) (wForms_levelBounded orderFormulas m) hA hX F

/-- **`|ID_{<ω}| = ψ₀(Ω_ω)`**: `ID_{<ω}` (for the well-ordering operator forms) proves transfinite
induction for `X` up to every countable notation, and does not prove it at `Ω₁`. -/
theorem idlt_analysis :
    (∀ a : ThetaWNoteD, a.1 < ThetaWTerm.Omega 0 →
        IDlt (Upper.WFormsOmega orderFormulas) ⊢ tiUptoSentence orderFormulas ℕ a) ∧
      ¬ IDlt (Upper.WFormsOmega orderFormulas) ⊢
        tiUptoSentence orderFormulas ℕ (ThetaWNoteD.Omega 0) :=
  idlt_theorem_final wForms_indAx_all
    (idseq_to_idn (embedHyps_wForms Nat.zero_lt_one (wForms_indAx Nat.zero_lt_one))
      (collapseCorollary Nat.zero_lt_one))

end OrdinalAnalysis.IDn
