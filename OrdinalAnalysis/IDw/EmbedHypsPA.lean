/- Source: OrdinalAnalysis\IDn\EmbedHypsPA.lean (ID_n -> ID_omega: `OmegaW`, level-free embedding). -/

/- Bridges `OrdinalAnalysis.IDw.AxiomsPA`'s abstract induction-axiom theorem (proved against a
`Ω_ω · 2`-height convention built from the *natural* sum `nadd`, `OmegaTwo_pa := nadd OmegaW
OmegaW`, since it is a faithful lift of `ID1.AxiomsPA`'s Cantor-normal-form bookkeeping) into
`OrdinalAnalysis.IDw.Embed`'s `EmbedHyps.induction_axiom` field (stated against the
self-contained `AxDerivable`/`OmegaTwo := OmegaW + OmegaW`, the *ordinary* sum).

**The bridging inequality** (`OmegaTwo_pa_le_OmegaTwo`): `OmegaTwo_pa ≤ OmegaTwo`. This is *not*
the general fact "`nadd a b ≥ a + b`" run backwards; it holds because `entries OmegaW =
[OmegaW]` (a singleton), so merging `[OmegaW]` with itself (`nadd`) and ordinarily adding
`[OmegaW]` to itself both produce `[OmegaW, OmegaW]` (`OmegaW_add_self_eq_nadd_self`; the same
argument for `Omega j` is `Omega_add_self_eq_nadd_self`). Composing with `add_ofNat_eq_nadd`
turns this into the height bound `axDerivable_of_le_of_pa` needs.

**No level witness any more.** In `IDn`, `AxiomsPA.induction_axiom` carried a spurious
`(k : Fin n)` (forced by an `include k in`), so the bridge lemma needed a witness `k`. In `IDw`
the embedding is level-free (`embT := lMap embedW`), the parameter is gone from `AxiomsPA`, and
`embedHyps_induction_of_pa` takes neither `k` nor the `XFreeL (A j)` hypothesis (`IDw`'s operator
form is one `A : FormJ` without `X`). -/
import OrdinalAnalysis.IDw.AxiomsPA
import OrdinalAnalysis.IDw.Embed

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaVNoteD

open ThetaVTerm in
/-- `Ω_j + Ω_j = Ω_j ⊕ Ω_j`: `Omega j`'s own CNF entry list is the singleton `[Omega j]`
(`entries_Omega`), so both the merge (`nadd`) and the ordinal sum (`+`) of `Omega j` with itself
produce the same two-element list `[Omega j, Omega j]` — merging two equal singletons needs no
reordering, and adding does not truncate an entry equal to (only strictly below) the other side's
leading exponent. -/
theorem Omega_add_self_eq_nadd_self (j : ℕ) :
    ThetaVNoteD.Omega j + ThetaVNoteD.Omega j =
      ThetaVNoteD.nadd (ThetaVNoteD.Omega j) (ThetaVNoteD.Omega j) := by
  apply ThetaVNoteD.ext_entries
  rw [ThetaVNoteD.entries_add, ThetaVNoteD.entries_nadd, ThetaVNoteD.entries_Omega,
    addL_cons, mergeL_cons_cons_of_le [] [] (le_refl' _)]
  simp [geb]

open ThetaVTerm in
/-- `Ω_ω + Ω_ω = Ω_ω ⊕ Ω_ω`: as `Omega_add_self_eq_nadd_self`, with `entries OmegaW = [OmegaW]`. -/
theorem OmegaW_add_self_eq_nadd_self :
    ThetaVNoteD.OmegaW + ThetaVNoteD.OmegaW =
      ThetaVNoteD.nadd ThetaVNoteD.OmegaW ThetaVNoteD.OmegaW := by
  apply ThetaVNoteD.ext_entries
  have hE : ThetaVNoteD.OmegaW.entries = [ThetaVTerm.OmegaW] := rfl
  rw [ThetaVNoteD.entries_add, ThetaVNoteD.entries_nadd, hE,
    addL_cons, mergeL_cons_cons_of_le [] [] (le_refl' _)]
  simp [geb]

end ThetaVNoteD

namespace IDw

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting
open LO.FirstOrder.Arithmetic

variable {A : Semisentence LForm 2}

/-- **The height-convention bridge**: `AxiomsPA`'s `Ω_ω · 2` (built from the natural sum) is below
`Embed`'s `Ω_ω · 2` (built from the ordinary sum). -/
theorem OmegaTwo_pa_le_OmegaTwo : OmegaTwo_pa ≤ OmegaTwo := by
  -- both are `Ω_ω · 2`; `+` and `⊕` coincide on `Ω_ω ⊕ Ω_ω`
  calc OmegaTwo_pa
      = ThetaVNoteD.nadd ThetaVNoteD.OmegaW ThetaVNoteD.OmegaW := rfl
    _ = ThetaVNoteD.OmegaW + ThetaVNoteD.OmegaW :=
        ThetaVNoteD.OmegaW_add_self_eq_nadd_self.symm
    _ ≤ OmegaTwo := le_rfl

/-- **`AxDerivableOfLeHyp` for the real `Embed.AxDerivable`**: instantiates `AxiomsPA`'s abstract
`axDerivable_of_le` hypothesis at `Embed`'s genuine, self-contained `AxDerivable`/`axDerivable_of_le`
pair, bridging the two height conventions via `OmegaTwo_pa_le_OmegaTwo`. -/
theorem axDerivable_of_le_of_pa : AxDerivableOfLeHyp A AxDerivable :=
  fun {σ} m β hβ hder =>
    axDerivable_of_le A m β
      (le_trans hβ (by
        rw [ThetaVNoteD.add_ofNat_eq_nadd]
        exact ThetaVNoteD.nadd_le_nadd_left' _ OmegaTwo_pa_le_OmegaTwo))
      hder

/-- **The bridge lemma**: `EmbedHyps.induction_axiom`'s field, discharged from `AxiomsPA.
induction_axiom` plus the genuine `Embed.AxDerivable`/`axDerivable_of_le`. Needs no level
witness (see the file header). -/
theorem embedHyps_induction_of_pa (taut : TautHyp A) (Sim : SimRel)
    (sim_subst_closed : SimSubstClosedHyp Sim) (replace_head : ReplaceHeadHyp A Sim)
    (allClosure_derivable : AllClosureDerivableHyp A) :
    ∀ {σ : Sentence (LXJ)}, σ ∈ InductionScheme (LXJ) Set.univ → AxDerivable A σ :=
  fun h =>
    induction_axiom AxDerivable taut Sim sim_subst_closed replace_head
      axDerivable_of_le_of_pa allClosure_derivable h

end IDw

end OrdinalAnalysis
