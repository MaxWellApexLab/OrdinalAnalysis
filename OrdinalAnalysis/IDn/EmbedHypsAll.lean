/-
  **The full `EmbedHyps (WForms orderFormulas n)`**, assembled from every merged bridge file, and
  the final theorems that follow from it.

  Six of the seven `EmbedHyps` fields (`IDn/Embed.lean`) are discharged unconditionally (given
  only `hn : 0 < n`), from already-merged, already-green declarations:

  * `taut`                      `EmbedHypsTaut.lean`'s `embedHyps_taut`, at
                                 `wForms_levelBounded orderFormulas n : FamilyLevelBounded
                                 (WForms orderFormulas n)` (`Theorem.lean`).
  * `eq_axiom`, `paMinus_axiom` `EmbedHypsLogic.lean`'s `embedHypsLogicPart`, same `hAb`.
  * `induction_axiom`           `EmbedHypsPA.lean`'s `embedHyps_induction_of_pa`, at
                                 `k := lvl0 hn` and with its four abstract side-hypotheses
                                 (`TautHyp`, `SimRel`/`SimSubstClosedHyp`/`ReplaceHeadHyp`,
                                 `AllClosureDerivableHyp`) discharged from the *real* `IDn.Sim`,
                                 `sim_subst_closed`, `IDnDerivable.replace_head` (all
                                 `IDn/Evaluate.lean`) and `IDn.allClosure_derivable`
                                 (`IDn/AxiomsLogic.lean:846` — landed there since
                                 `EmbedHypsPA.lean`'s header comment was written, which still
                                 calls it "not yet on disk").
  * `closure_axiom`             `IDn.closure_axiom` (`AxiomsIDCases/closure_derivable.lean`),
                                 checked green today (`remote_build.sh` on that module alone
                                 exits 0), at the same `wForms_levelBounded` for its own extra
                                 `FamilyLevelBounded A` hypothesis. Matches the field on the nose
                                 modulo that one extra hypothesis, exactly the `taut`/`eq_axiom`
                                 pattern — no further hypothesis needed.
  * `replaceHeadNumI`           `EmbedHypsReplace.lean`'s `embedHyps_replaceHeadNumI`, verbatim.

  The seventh field, `indAx_axiom`, is **taken as an explicit hypothesis `hind`**: the shard
  meant to discharge it, `AxiomsIDCases/indBody_inst.lean`, is red today — checked with
  `remote_build.sh` on that module alone, which surfaces genuine elaboration errors (`Unknown
  identifier IDerivable`, type-class synthesis failures, application type mismatches at lines
  60–174), not stale-import noise: its `AxDerivable`/`IDerivable`/`OmegaTwo` resolve to
  `AxiomsIDCases/Defs.lean`'s *single-formula* (`A : Semisentence (LXIn n) 1`) ID₁-per-level
  port, not `Embed.lean`'s *family*-indexed `AxDerivable` the field needs — a real, unbridged
  type mismatch. (`indAx_claim.lean`, the sibling shard, *is* green and already family-shaped,
  but only proves the induction-on-stages claim, not the wrapped axiom in `AxDerivable` form —
  exactly the step red `indBody_inst.lean` was to supply.) `hind`'s type is `indAx_axiom`'s
  field text instantiated at `A := WForms orderFormulas n`.

  `idn_theorem_final`/`idn_lower_bound_final` need only `hn`/`hind` (both `CollapseCorollary`
  and its sharp counterpart are discharged internally by `collapseCorollary`/
  `collapseCorollarySharp`, already unconditional theorems). `idlt_theorem_final` additionally
  needs `htr : IDseqToIDn orderFormulas (ThetaWNoteD.Omega 0)` as an explicit hypothesis: the
  theorem meant to discharge it, `IDn/Retract.lean`'s `idseq_to_idn`, is red today (checked the
  same way: genuine errors at lines 231–445, unrelated to staleness) — `Retract.lean` is not
  touched here.

  Contents.

    `embedHyps_wForms`      the full `EmbedHyps (WForms orderFormulas n)`, given `hn` and `hind`
    `idn_theorem_final`     the sharp two-sided theorem at `c_n` (`CollapseCorollarySharp.lean`)
    `idn_lower_bound_final` the non-sharp lower bound at `Omega 0` (`CollapseCorollary.lean`)
    `idlt_theorem_final`    both halves for `ID_{<ω}` (`Theorem2.lean`), given `htr` as well
-/
import OrdinalAnalysis.IDn.EmbedHypsTaut
import OrdinalAnalysis.IDn.EmbedHypsLogic
import OrdinalAnalysis.IDn.EmbedHypsPA
import OrdinalAnalysis.IDn.EmbedHypsReplace
import OrdinalAnalysis.IDn.AxiomsIDCases.closure_derivable
import OrdinalAnalysis.IDn.CollapseCorollary
import OrdinalAnalysis.IDn.CollapseCorollarySharp
import OrdinalAnalysis.IDn.Theorem2

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting
open LO.FirstOrder.Arithmetic
open OrdinalAnalysis.IDn.Upper

variable {n : ℕ}

/-- **The full `EmbedHyps (WForms orderFormulas n)`.** Six fields (`taut`, `eq_axiom`,
`paMinus_axiom`, `induction_axiom`, `closure_axiom`, `replaceHeadNumI`) are discharged
unconditionally from already-merged bridges (see the file header). The seventh,
`indAx_axiom`, is taken verbatim as the explicit hypothesis `hind` — `AxiomsIDCases/
indBody_inst.lean` (the shard meant to supply it) is red today. -/
theorem embedHyps_wForms (hn : 0 < n)
    (hind : ∀ (k : Fin n), PositiveIn k (WForms orderFormulas n k) →
      (∀ j, XFreeL (WForms orderFormulas n j)) → ∀ F : Semiformula (LXIn n) ℕ 1,
        AxDerivable (WForms orderFormulas n) (indAxAt k (WForms orderFormulas n k) F)) :
    EmbedHyps (WForms orderFormulas n) where
  taut := embedHyps_taut (wForms_levelBounded orderFormulas n)
  eq_axiom := (embedHypsLogicPart (wForms_levelBounded orderFormulas n)).eq_axiom
  paMinus_axiom := (embedHypsLogicPart (wForms_levelBounded orderFormulas n)).paMinus_axiom
  induction_axiom :=
    embedHyps_induction_of_pa (lvl0 hn)
      (embedHyps_taut (wForms_levelBounded orderFormulas n))
      Sim sim_subst_closed IDnDerivable.replace_head allClosure_derivable
  closure_axiom := fun k hX => closure_axiom k (wForms_levelBounded orderFormulas n) hX
  indAx_axiom := hind
  replaceHeadNumI := embedHyps_replaceHeadNumI

/-- **The Buchholz–Pohlers analysis of `ID_n`, sharp**, given only `hn` and `hind`
(`indAx_axiom`'s field text): `ID_n` proves transfinite induction up to every `a ≺ c_n`, and
not up to `c_n = ϑ₀(ϑ_n 0)` itself. -/
theorem idn_theorem_final (hn : 0 < n)
    (hind : ∀ (k : Fin n), PositiveIn k (WForms orderFormulas n k) →
      (∀ j, XFreeL (WForms orderFormulas n j)) → ∀ F : Semiformula (LXIn n) ℕ 1,
        AxDerivable (WForms orderFormulas n) (indAxAt k (WForms orderFormulas n k) F)) :
    (∀ a : ThetaWNoteD, a < ThetaWNoteD.c n →
        IDn n (WForms orderFormulas n) ⊢ tiUptoSentence orderFormulas (Fin n) a) ∧
      ¬ IDn n (WForms orderFormulas n) ⊢
        tiUptoSentence orderFormulas (Fin n) (ThetaWNoteD.c n) :=
  idn_theorem_sharp' hn (embedHyps_wForms hn hind)

/-- **`IDn n (WForms orderFormulas n) ⊬ TI_{Ω_1}(≺, X)`**, given only `hn` and `hind`. -/
theorem idn_lower_bound_final (hn : 0 < n)
    (hind : ∀ (k : Fin n), PositiveIn k (WForms orderFormulas n k) →
      (∀ j, XFreeL (WForms orderFormulas n j)) → ∀ F : Semiformula (LXIn n) ℕ 1,
        AxDerivable (WForms orderFormulas n) (indAxAt k (WForms orderFormulas n k) F)) :
    ¬ IDn n (WForms orderFormulas n) ⊢
      tiUptoSentence orderFormulas (Fin n) (ThetaWNoteD.Omega 0) :=
  idn_lower_bound' hn (embedHyps_wForms hn hind)

/-- **The Buchholz–Pohlers analysis of `ID_{<ω}`, both halves**, given `hind` at every level and
the translation link `htr : IDseqToIDn orderFormulas (Omega 0)` (`Theorem2.lean`'s own open
link — `IDn/Retract.lean`'s `idseq_to_idn`, meant to discharge it, is red today). -/
theorem idlt_theorem_final
    (hind : ∀ (m : ℕ) (k : Fin m), PositiveIn k (WForms orderFormulas m k) →
      (∀ j, XFreeL (WForms orderFormulas m j)) → ∀ F : Semiformula (LXIn m) ℕ 1,
        AxDerivable (WForms orderFormulas m) (indAxAt k (WForms orderFormulas m k) F))
    (htr : IDseqToIDn orderFormulas (ThetaWNoteD.Omega 0)) :
    (∀ a : ThetaWNoteD, a.1 < ThetaWTerm.Omega 0 →
        IDlt (Upper.WFormsOmega orderFormulas) ⊢ tiUptoSentence orderFormulas ℕ a) ∧
      ¬ IDlt (Upper.WFormsOmega orderFormulas) ⊢
        tiUptoSentence orderFormulas ℕ (ThetaWNoteD.Omega 0) :=
  idlt_theorem (fun m hm => embedHyps_wForms hm (hind m)) (fun _m hm => collapseCorollary hm) htr

end IDn

end OrdinalAnalysis
