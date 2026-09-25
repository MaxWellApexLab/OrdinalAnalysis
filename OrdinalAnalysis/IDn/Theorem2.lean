/-
  The Buchholz–Pohlers analysis of `ID_n` and `ID_{<ω}`, both halves, mirroring
  `OrdinalAnalysis.ID1.Theorem2`'s `id1_theorem`.

  * **Upper bound** (`Upper.idn_upper_bound'`; Arai, arXiv:2304.00246, §1.6, already merged
    and hypothesis-free): for every notation `a ≺ c_n`, `IDn n (WForms F n)` proves `TI_a`.
  * **Lower bound** (`idn_lower_bound`, `IDn/LowerBound.lean`): `IDn n (WForms F n) ⊬
    TI_{Omega 0}`, given `EmbedHyps` and `CollapseCorollary` (the one open link, see that
    file's header).

  These two do not meet at the same bound (`c_n < Omega 0`, `ThetaWNoteD.c_lt_Omega` or
  similar order fact): the upper bound reaches every notation strictly below the sharp
  Buchholz–Pohlers ordinal `c_n`, the lower bound only rules out the whole field up to
  `Omega 0`. Closing the gap needs the sharp lower bound `idn_lower_bound_c` at `a := c n`,
  which could not be closed either (a missing tower-cofinality
  fact, on top of `CollapseCorollary`) — not attempted again here. `idn_theorem` below states
  precisely what is proved: the sharp upper bound and the (non-sharp, hypothesis-gated) lower
  bound, conjoined honestly, not silently narrowed to look tight.

  `Upper.idn_upper_bound'` is stated for `Internal.codedOrderFacts.toOrderFormulas`; this
  file's lower bound is stated for `Upper.orderFormulas` (chosen
  to avoid defeq friction with `IDn/Internal/OrderBridge.lean`). The two are equal by
  `rfl` (`orderFormulas_eq_codedOrderFacts`, checked live) — different declared constants with
  identical underlying `Σ₁` definitions — so the conjunction below states both halves for
  `Upper.orderFormulas` via that bridge.

  **`idlt_theorem`.** The upper half (`Upper.idlt_upper_bound'`) is merged and
  hypothesis-free. The lower half needs `IDlt (WFormsOmega F) ⊬ TI_{Omega 0}`; `provable_IDlt_iff`
  reduces this to `∀ m, IDseq (WFormsOmega F) m ⊬ TI_{Omega 0}` (`Union.lean`), but translating an
  `IDseq`-derivation (in `LXIomega` directly) down to an honest `IDn m` one (in the smaller
  language `LXIn m`, what `idn_lower_bound` is about) is a translation-of-derivations lemma
  `Union.lean`'s own docstring says is **not built** ("pushing this further down into an honest
  `IDn m A'` ... is true as well ... but is not built here"). Kept as a further explicit
  hypothesis, `IDseqToIDn`, alongside `EmbedHyps`/`CollapseCorollary` for every level.

  Contents.

    `orderFormulas_eq_codedOrderFacts`   the bridge between the two `OrderFormulas` instances
    `idn_theorem`                        both halves, for `IDn n`
    `IDseqToIDn`                         the one further open link `idlt_theorem` needs
    `idlt_theorem`                       both halves, for `IDlt`
-/
import OrdinalAnalysis.IDn.LowerLt
import OrdinalAnalysis.IDn.UpperFinal
import OrdinalAnalysis.IDn.Union

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder
open OrdinalAnalysis.IDn.Upper
open OrdinalAnalysis.IDn.Internal (codedOrderFacts)

variable {n : ℕ}

/-- `Upper.orderFormulas` (`IDn/InternalFacts.lean`, what the lower bound is stated
for) and `Internal.codedOrderFacts.toOrderFormulas` (`IDn/Internal/OrderFacts.lean`, what the
merged upper bound `Upper.idn_upper_bound'`/`Upper.idlt_upper_bound'` is stated for) are the
same `Σ₁` order, by two separately-declared but definitionally-equal `ltDef`s. -/
theorem orderFormulas_eq_codedOrderFacts :
    orderFormulas = codedOrderFacts.toOrderFormulas := rfl

/-- **The Buchholz–Pohlers analysis of `ID_n`**, both halves, for the well-ordering forms
`WForms orderFormulas n`: `ID_n` proves transfinite induction up to every notation `a ≺ c_n`
(sharp, hypothesis-free), and does not prove it for the whole field up to `Omega 0`, given
`EmbedHyps` and `CollapseCorollary` (`IDn/LowerBound.lean`'s one open link — not sharp; see
the file header for exactly what gap remains between `c_n` and `Omega 0`). -/
theorem idn_theorem (hn : 0 < n) (hyps : EmbedHyps (WForms orderFormulas n))
    (hcol : CollapseCorollary hn) :
    (∀ a : ThetaWNoteD, a < ThetaWNoteD.c n →
        IDn n (WForms orderFormulas n) ⊢ tiUptoSentence orderFormulas (Fin n) a) ∧
      ¬ IDn n (WForms orderFormulas n) ⊢
        tiUptoSentence orderFormulas (Fin n) (ThetaWNoteD.Omega 0) := by
  refine ⟨fun a ha => ?_, idn_lower_bound hn hyps hcol⟩
  rw [orderFormulas_eq_codedOrderFacts]
  exact idn_upper_bound' n hn a ha

/-- **The one further open link `idlt_theorem`'s lower half needs**: translating a derivation
of `IDseq (WFormsOmega F) m` (in `LXIomega` directly) down to an honest `IDn m (WForms F m)`
derivation (in the smaller language `LXIn m`) — `Union.lean`'s own docstring on
`provable_IDlt_iff` says this is not built. Stated in exactly the contrapositive shape
`idlt_theorem`'s lower half needs. -/
def IDseqToIDn (F : Upper.OrderFormulas) (a : ThetaWNoteD) : Prop :=
  ∀ m : ℕ, IDseq (Upper.WFormsOmega F) m ⊢ tiUptoSentence F ℕ a →
    ∃ hm : 0 < m, IDn m (WForms F m) ⊢ tiUptoSentence F (Fin m) a

/-- **The Buchholz–Pohlers analysis of `ID_{<ω}`**, both halves: `ID_{<ω}` proves transfinite
induction up to every countable notation `a ≺ Omega 0` (sharp, hypothesis-free,
`Upper.idlt_upper_bound'`), and does not prove it for the whole field up to `Omega 0`, given
`EmbedHyps`/`CollapseCorollary` at every level and the translation link `IDseqToIDn` (see the
file header). -/
theorem idlt_theorem (hyps : ∀ m : ℕ, 0 < m → EmbedHyps (WForms orderFormulas m))
    (hcol : ∀ (m : ℕ) (hm : 0 < m), CollapseCorollary (n := m) hm)
    (htr : IDseqToIDn orderFormulas (ThetaWNoteD.Omega 0)) :
    (∀ a : ThetaWNoteD, a.1 < ThetaWTerm.Omega 0 →
        IDlt (Upper.WFormsOmega orderFormulas) ⊢ tiUptoSentence orderFormulas ℕ a) ∧
      ¬ IDlt (Upper.WFormsOmega orderFormulas) ⊢
        tiUptoSentence orderFormulas ℕ (ThetaWNoteD.Omega 0) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · rw [orderFormulas_eq_codedOrderFacts]
    exact idlt_upper_bound' a ha
  · rw [provable_IDlt_iff]
    rintro ⟨m, hm⟩
    obtain ⟨hpos, hIDn⟩ := htr m hm
    exact idn_lower_bound hpos (hyps m hpos) (hcol m hpos) hIDn

end IDn

end OrdinalAnalysis
