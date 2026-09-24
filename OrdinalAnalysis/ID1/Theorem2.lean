/-
  The Bachmann–Howard analysis of `ID₁`, both halves.

  `ID1Acc precC` is `ID₁` for the accessibility operator `A(Y, x) :≡ ∀y (y ≺ x → Y y)` of the
  coded ϑ-order `≺ = precC` (Freund, arXiv:2204.09321, Definition 3.1); `X` is a free unary
  predicate.  For a notation `a`,

      TI_a(≺, X)  :≡  Prog(≺, X) → ∀x (x ≺ ⌜a⌝ → X x),

  with the same `Prog(≺, X)`, the same `≺` and the same `X` in both halves; `TI_Ω(≺, X)` is the
  instance `a = Ω` (`UpperBound.tiUptoSentence_Omega`).

  * **Upper bound** (`UpperBound.id1_upper_bound`; Arai, arXiv:2304.00246, §1.6): for every
    notation `a ≺ Ω`, `ID1Acc precC ⊢ TI_a(≺, X)`.
  * **Lower bound** (`id1_lower_bound`; Freund, Corollary 7.2): `ID1Acc precC ⊬ TI_Ω(≺, X)`.

  The notations below `Ω` are the field of the order, and their order type is the
  Bachmann–Howard ordinal (`ThetaNote.bhOrdinal`, the definition used in the literature): `ID₁`
  proves transfinite induction along every proper initial segment of the countable part of the
  ϑ-order, and not along the whole of it.
-/
import OrdinalAnalysis.ID1.UpperBound
import OrdinalAnalysis.ID1.Theorem

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

open LO LO.FirstOrder
open OrdinalAnalysis.ID1.Internal

/-- **The Bachmann–Howard analysis of `ID₁`**, both halves, for the same order `≺ = precC` and
the same free predicate `X`: transfinite induction up to every notation `a ≺ Ω` is provable in
`ID1Acc precC`, transfinite induction up to `Ω` is not. -/
theorem id1_theorem :
    (∀ a : ThetaNote, a < ThetaNote.Omega → ID1Acc precC ⊢ UpperBound.tiUptoSentence a) ∧
      ¬ ID1Acc precC ⊢ LowerBound.tiFieldSentence :=
  ⟨fun _ ha => UpperBound.id1_upper_bound ha, id1_lower_bound⟩

/-- The same, with both sentences in the form `TI_a(≺, X)`. -/
theorem id1_theorem' :
    (∀ a : ThetaNote, a < ThetaNote.Omega → ID1Acc precC ⊢ UpperBound.tiUptoSentence a) ∧
      ¬ ID1Acc precC ⊢ UpperBound.tiUptoSentence ThetaNote.Omega := by
  rw [UpperBound.tiUptoSentence_Omega]
  exact id1_theorem

end InductiveDef

end OrdinalAnalysis
