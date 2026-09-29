/- Source: OrdinalAnalysis\IDn\EmbedHypsID.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.Embed
import OrdinalAnalysis.IDw.AxiomsIDCases.closure_derivable
import OrdinalAnalysis.IDw.AxiomsIDCases.indBody_inst

/-
  The two `ID_ω`-specific fields of `IDw.Embed`'s `EmbedHyps`: the closure axiom and the induction
  axiom scheme.

  **Closure** (`closure_axiom`).  `AxDerivable A (closureAxJ A)` for a positive form `A`: the ω-rule
  over the level `y = k̄` and over `x`; for each instance the `Cong` producer of `IDw.TransferCong`
  and `Transfer.transfer5_bwd` give `⊢ ¬A_{k̄}(t), A_k(t; I_k, Jlev k)`, the rule (Fix) turns the
  unfolding into `I_k t`, and (jlev) turns `I_k t` into `Jlev ⊤ (k̄, t)`; all cut-free
  (`IDw.AxiomsIDCases.closure_derivable`).

  **Induction** (`indAx_axiom`).  `AxDerivable A (indAxJ A F)` for a positive form `A` and every
  `F`, in the proof of Freund's Proposition 6.4: for each level `k̄` the induction on stages
  (`indAx_claim`, the rule (nstage), one `Cong` from the unfolding to the embedded body, Lemma 6.1
  for `F`), then (njlev), the ω-rule over `y`, and the universal closure over the free variables of
  `F` (`IDw.AxiomsIDCases.indBody_inst`); all cut-free, height `Ω_ω · 2 + m`.

  Neither statement takes a hypothesis beyond `PositiveP A`: the `Cong` producer is a proved theorem.

  Contents.

    `embedHyps_closure_axiom`, `embedHyps_indAx_axiom`   the two fields, as theorems
    `EmbedHypsIDPart`, `embedHypsIDPart`                 the two fields bundled
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder

/-- **`EmbedHyps.closure_axiom`**, exactly. -/
theorem embedHyps_closure_axiom {A : FormJ} : PositiveP A → AxDerivable A (closureAxJ A) :=
  fun hA => closure_derivable hA

/-- **`EmbedHyps.indAx_axiom`**, exactly. -/
theorem embedHyps_indAx_axiom {A : FormJ} :
    PositiveP A → ∀ F : Semiformula LXJ ℕ 2, AxDerivable A (indAxJ A F) :=
  fun hA F => indAx_axiom hA F

/-- The two `ID_ω`-specific axiom fields of `EmbedHyps`. -/
structure EmbedHypsIDPart (A : FormJ) : Prop where
  closure_axiom : PositiveP A → AxDerivable A (closureAxJ A)
  indAx_axiom : PositiveP A → ∀ F : Semiformula LXJ ℕ 2, AxDerivable A (indAxJ A F)

theorem embedHypsIDPart (A : FormJ) : EmbedHypsIDPart A where
  closure_axiom := embedHyps_closure_axiom
  indAx_axiom := embedHyps_indAx_axiom

end IDw

end OrdinalAnalysis
