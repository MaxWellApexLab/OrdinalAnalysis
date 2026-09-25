/-
  The lower bound for `IDn n (WForms orderFormulas n)`, propagated upward from `Omega 0` to
  every larger bound.

  `IDn/LowerBound.lean`'s `idn_lower_bound` gives `IDn n (WForms orderFormulas n) ⊬
  tiUptoSentence orderFormulas (Fin n) (Omega 0)`. Since `TI_a(≺, X)` is monotone in `a` (a
  bigger field only makes the induction hypothesis `Prog(≺, X)` harder to discharge down to
  `X`, so `TI_a ⊢ TI_{a'}` whenever `a' ≤ a`), unprovability at the smaller bound `Omega 0`
  gives unprovability at every `a ≥ Omega 0` too — the direct analogue of the trivial
  `tiFieldSentence`-vs-`tiUptoSentence Omega` rewrite `ID1.Theorem.id1_theorem'` does for `ID₁`
  (there a pure renaming, since `ID1` has no `a`-parametrised family to begin with; here a
  genuine, if easy, corollary, because `IDn`'s `tiUptoSentence` already is one).

  **The one added hypothesis (`TiMonotoneProvable`).** Running this argument needs the
  monotonicity implication itself *derivable* inside `IDn n (WForms orderFormulas n)`, not
  merely true — a first-order consequence of the arithmetized fact `∀x (x ≺ ⌜Omega 0⌝ → x ≺
  ⌜a⌝)` (itself provable in `𝗣𝗔⁻ + IΣ₁` from order transitivity plus the numerical fact
  `Omega 0 ≼ a`, both plausible but not composed anywhere: `grep`ped `IDn/*.lean` for
  `trans`/`provable` combined with the internal order — nothing). Kept as an explicit
  hypothesis in exactly the shape `Entailment.mdp` needs it in so
  that closing it later is a one-line application, not a restatement of this file.

  Contents.

    `TiMonotoneProvable`            the one open link, documented above
    `idn_lower_bound_lt`            `IDn n (WForms orderFormulas n) ⊬ tiUptoSentence
                                     orderFormulas (Fin n) a`, for every `a` at which the
                                     monotonicity implication is provable
-/
import OrdinalAnalysis.IDn.LowerBound

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder
open OrdinalAnalysis.IDn.Upper

variable {n : ℕ}

/-- **`TI_a(≺, X) → TI_{Omega 0}(≺, X)` is provable in `IDn n (WForms orderFormulas n)`**, for
a given `a` (sensible only when `Omega 0 ≤ a`, so that the field below `Omega 0` really is
included in the field below `a`; not assumed here, since only the derivability itself is used).
The one hypothesis `idn_lower_bound_lt` needs beyond `idn_lower_bound` (see the file header). -/
def TiMonotoneProvable (n : ℕ) (a : ThetaWNoteD) : Prop :=
  IDn n (WForms orderFormulas n) ⊢
    (tiUptoSentence orderFormulas (Fin n) a 🡒
      tiUptoSentence orderFormulas (Fin n) (ThetaWNoteD.Omega 0))

/-- **`IDn n (WForms orderFormulas n) ⊬ TI_a(≺, X)`, for every `a` at which the monotonicity
implication down to `Omega 0` is provable** — in particular for every `a ≥ Omega 0` once
`TiMonotoneProvable` is discharged there. -/
theorem idn_lower_bound_lt (hn : 0 < n) (hyps : EmbedHyps (WForms orderFormulas n))
    (hcol : CollapseCorollary hn) {a : ThetaWNoteD} (hmono : TiMonotoneProvable n a) :
    ¬ IDn n (WForms orderFormulas n) ⊢ tiUptoSentence orderFormulas (Fin n) a := by
  intro h
  exact idn_lower_bound hn hyps hcol (Entailment.mdp hmono h)

end IDn

end OrdinalAnalysis
