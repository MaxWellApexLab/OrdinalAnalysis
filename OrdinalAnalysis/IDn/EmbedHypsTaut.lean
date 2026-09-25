/-
  Bridge lemma for `IDn/Embed.lean`'s `EmbedHyps.taut` field, now that the field's height has
  been corrected (`IDn/Embed.lean`) from `rk ψ` (refuted unconditionally by
  `IDn.taut_additive_impossible`, `IDn/TautAdditive.lean`) to `ThetaWNoteD.omegaMul (rk ψ)`.

  Unlike `EmbedHypsLogic.lean`'s `eq_axiom`/`paMinus_axiom` (which needed a height-monotonicity
  argument to reconcile `AxiomsLogic`'s `nadd`-based `Ω_n · 2` convention with `Embed`'s `+`-based
  one), `taut`'s two sides now agree on the nose: `IDn.AxiomsLogic.taut` (Freund Lemma 6.1,
  `IDn/AxiomsLogic.lean:415`) already concludes at height `ThetaWNoteD.omegaMul (rk ψ)` over
  `ThetaWNoteD.adjoin H (Stage.val '' params ψ)` at rank `zero` for `[ψ, ∼ψ]` — exactly the
  corrected field's statement, `NiceS H` for `NiceS H`, no `Nice k`/`NiceS` bridging needed. The
  only extra ingredient `AxiomsLogic.taut` needs beyond the field's own binders is
  `FamilyLevelBounded A`, taken here as an explicit hypothesis, matching the pattern
  `EmbedHypsLogic.lean`'s `embedHypsLogicPart` already uses for `induction_axiom`/`closure_axiom`/
  `indAx_axiom`-style extra side conditions on `A`.

  Contents.

    `embedHyps_taut`   the bridge, `IDn.AxiomsLogic.taut` specialised to the field's exact shape
-/
import OrdinalAnalysis.IDn.Embed
import OrdinalAnalysis.IDn.AxiomsLogic

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting
open LO.FirstOrder.Arithmetic

variable {n : ℕ} {A : Fin n → Semisentence (LXIn n) 1}

/-- **`EmbedHyps.taut`, bridged from `IDn.AxiomsLogic.taut`** (Freund, Lemma 6.1): the corrected
field (height `ω · rk ψ`) is discharged directly, with no height reconciliation needed — both
sides already agree on `ThetaWNoteD.adjoin H (Stage.val '' params ψ)`, rank `zero`, height
`ThetaWNoteD.omegaMul (rk ψ)`, and conclusion `[ψ, ∼ψ]`. -/
theorem embedHyps_taut (hAb : FamilyLevelBounded A) :
    ∀ {H : Set ThetaWNoteD → Set ThetaWNoteD}, ThetaWNoteD.NiceS H →
      ∀ ψ : Proposition (LIinfN n), ψ.freeVariables = ∅ →
        IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params ψ))
          (ThetaWNoteD.omegaMul (rk ψ)) [ψ, ∼ψ] :=
  fun hH ψ hc => taut hAb hH ψ hc

end IDn

end OrdinalAnalysis
