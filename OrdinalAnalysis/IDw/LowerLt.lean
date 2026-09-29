/- Source: OrdinalAnalysis/IDn/LowerLt.lean (`IDn n (WForms orderFormulas n)` -> `IDw WFormWc`; the monotonicity hypothesis `TiMonotoneProvable`, an open link in `IDn`, is discharged here for every bound `a ≥ Ω₁`, `tiMonotoneProvable_of_le`). -/

/-
  The lower bound for `IDw WFormWc`, propagated upward from `Ω₁` to every larger bound.

  `IDw/LowerBound.lean`'s `idw_lower_bound_of` gives `IDw WFormWc ⊬ tiUptoSentence orderFormulas
  (Omega 0)`.  Since `TI_a(≺, X)` is monotone in `a` (a bigger field only makes the induction
  hypothesis `Prog(≺, X)` harder to discharge down to `X`, so `TI_a ⊢ TI_{a'}` whenever `a' ≤ a`),
  unprovability at the smaller bound `Ω₁` gives unprovability at every `a ≥ Ω₁`.

  **`TiMonotoneProvable`.**  Running this argument needs the monotonicity implication itself
  *derivable* in `IDw WFormWc`, not merely true.  In `IDn` this was kept as an explicit hypothesis
  (`IDn/LowerLt.lean`).  Here it is proved for every `a ≥ Ω₁` (`tiMonotoneProvable_of_le`):
  in every arithmetically standard model `N` of `IDw WFormWc` the implication is the arithmetized
  fact `x ≺ ⌜Ω₁⌝ → x ≺ ⌜a⌝` (`iltb_mc`, transitivity of `iltb`), through
  `Lift.provable_of_models`.

  Contents.

    `TiMonotoneProvable`            the monotonicity implication as a provable sentence
    `tiMonotoneProvable_of_le`      **it is provable for every `a ≥ Ω₁`**
    `idw_lower_bound_lt`            `IDw WFormWc ⊬ tiUptoSentence orderFormulas a` when
                                    `TiMonotoneProvable a`
    `idw_lower_bound_of_le`         **`IDw WFormWc ⊬ TI_a` for every `a ≥ Ω₁`**
-/
import OrdinalAnalysis.IDw.LowerBound
import OrdinalAnalysis.IDw.CollapseCorollaryW

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.IDw.Upper
open OrdinalAnalysis.IDw.Lift (ArithStd)
open OrdinalAnalysis.IDw.Internal (mc iltb)

/-- **`TI_a(≺, X) → TI_{Ω₁}(≺, X)` is provable in `IDw WFormWc`**, for a given `a` (sensible only
when `Ω₁ ≤ a`, so that the field below `Ω₁` really is included in the field below `a`; not assumed
here, since only the derivability itself is used). -/
def TiMonotoneProvable (a : ThetaVNoteD) : Prop :=
  IDw WFormWc ⊢
    (tiUptoSentence orderFormulas a 🡒 tiUptoSentence orderFormulas (ThetaVNoteD.Omega 0))

/-- **The monotonicity implication is provable for every `a ≥ Ω₁`.** -/
theorem tiMonotoneProvable_of_le {a : ThetaVNoteD} (hle : ThetaVNoteD.Omega 0 ≤ a) :
    TiMonotoneProvable a := by
  refine Lift.provable_of_models WFormWc fun N _ s _ hN => ?_
  refine models_iff.mpr ?_
  have hIS : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := Lift.models_iSigma₁ WFormWc
  rw [LogicalConnective.HomClass.map_imply, eval_tiUpto, eval_tiUpto]
  intro hA hProg x ⟨hfx, hfΩ, hxΩ⟩
  have hfa : orderFormulas.fld (mc (V := N) a.1) := by
    exact ⟨(Internal.eval_thNFDef_mc a.1).mpr a.2.1, (Internal.eval_thDomDef_mc a.1).mpr a.2.2⟩
  refine hA hProg x ⟨hfx, hfa, ?_⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · have h1 : iltb (mc (V := N) (ThetaVNoteD.Omega 0).1) (mc a.1) = 1 :=
      (Internal.iltb_mc _ _).mpr hlt
    have h2 := (fld_iff_isNF_isDom _).mp hfx
    have h3 := (fld_iff_isNF_isDom _).mp hfΩ
    have h4 := (fld_iff_isNF_isDom _).mp hfa
    exact (lt_iff_iltb _ _).mpr (Internal.iltb_trans (Internal.isTerm_of_isNF h2.1)
      (Internal.isTerm_of_isNF h3.1) (Internal.isTerm_of_isNF h4.1)
      ((lt_iff_iltb _ _).mp hxΩ) h1)
  · rw [← heq]
    exact hxΩ

/-- **`IDw WFormWc ⊬ TI_a(≺, X)`, for every `a` at which the monotonicity implication down to
`Ω₁` is provable** (given `EmbedHyps` and the collapsing corollary). -/
theorem idw_lower_bound_lt (hyps : EmbedHyps WFormWc) (hcol : CollapseCorollary WFormWc)
    {a : ThetaVNoteD} (hmono : TiMonotoneProvable a) :
    ¬ IDw WFormWc ⊢ tiUptoSentence orderFormulas a := by
  intro h
  exact idw_lower_bound_of hyps hcol (Entailment.mdp hmono h)

/-- **`IDw WFormWc ⊬ TI_a(≺, X)` for every notation `a ≥ Ω₁`**, with no hypothesis. -/
theorem idw_lower_bound_of_le {a : ThetaVNoteD} (hle : ThetaVNoteD.Omega 0 ≤ a) :
    ¬ IDw WFormWc ⊢ tiUptoSentence orderFormulas a :=
  idw_lower_bound_lt (embedHyps WFormWc) (collapseCorollaryW positiveP_WFormWc)
    (tiMonotoneProvable_of_le hle)

end IDw

end OrdinalAnalysis
