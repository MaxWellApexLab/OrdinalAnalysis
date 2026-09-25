/-
  The `ℕ`-standard-model bridge between the arithmetic order formulas `OrderFormulas`
  (`F.lt`, `F.nf`, `F.dom`, `F.fld`; `IDn/UpperAux.lean`), evaluated at the concrete instance
  `Upper.orderFormulas := ⟨iltDef, thNFDef, thDomDef⟩` (`IDn/InternalFacts.lean`), and the actual
  Lean-level order / normal-form / domain predicates on `ThetaWTerm` / `ThetaWNoteD`
  (`IDn/Internal/Order.lean`).

  Two facts, for `IDn/LowerBound.lean`'s Step 6 (`codeAt0_mem_stageSetN_iff`):

  1. `eval_lt_iff_lt` / `eval_nf_iff` / `eval_dom_iff` / `eval_fld_iff`: `orderFormulas.lt`
     (resp. `.nf` / `.dom` / `.fld`), evaluated on the code of a `ThetaWTerm` in `ℕ`, agrees with
     the actual order / `NF` / `Dom` / `NF ∧ Dom` on that term. This composes
     `InternalFacts.lean`'s `eval_iltDef` and `Order.lean`'s `eval_thNFDef` / `eval_thDomDef`
     (arithmetic-formula unfolding) with `Order.lean`'s `standard_lt_iff` / `standard_nf_iff` /
     `standard_dom_iff` (the `ℕ`-model bridge for the raw predicates `iltb` / `isNF` / `isDom`) —
     the same composition `InternalFacts.lean`'s `slotCheck_precW` already performs for the
     paired sentence, repackaged here at the single-predicate `OrderFormulas` level that
     `LowerBound.lean` is stated in.
  2. `fld_surj`: every natural number satisfying `orderFormulas.fld` is the code of some
     `t : ThetaWNoteD` — i.e. the field of the coded order in `ℕ` is exactly
     `{code t | NF t ∧ Dom t}`. Via `Standard.lean`'s `isTerm_surj` (term-code surjectivity),
     fed by `OrderT.lean`'s `isTerm_of_isNF` (a code satisfying `isNF` is in particular a code
     satisfying `isTerm`, so `isTerm_surj` applies to it).
-/
import OrdinalAnalysis.IDn.InternalFacts
import OrdinalAnalysis.IDn.Internal.OrderT
import OrdinalAnalysis.IDn.Internal.Standard

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.ThetaWTerm
open OrdinalAnalysis.IDn.Upper (orderFormulas iltDef eval_iltDef)

/-! ### The `ℕ`-bridge for the concrete order formulas -/

/-- **The coded order, read in `ℕ`, is the actual order on `ThetaWTerm`.** -/
theorem eval_lt_iff_lt (a b : ThetaWTerm) :
    orderFormulas.lt (code a : ℕ) (code b) ↔ a < b := by
  show iltDef.val.Evalb ![(code a : ℕ), code b] ↔ a < b
  rw [eval_iltDef, standard_lt_iff]

/-- **The coded normal-form predicate, read in `ℕ`, is `NF`.** -/
theorem eval_nf_iff (t : ThetaWTerm) : orderFormulas.nf (code t : ℕ) ↔ NF t := by
  show thNFDef.val.Evalb ![(code t : ℕ)] ↔ NF t
  rw [eval_thNFDef, standard_nf_iff]

/-- **The coded domain predicate, read in `ℕ`, is `Dom`.** -/
theorem eval_dom_iff (t : ThetaWTerm) : orderFormulas.dom (code t : ℕ) ↔ Dom t := by
  show thDomDef.val.Evalb ![(code t : ℕ)] ↔ Dom t
  rw [eval_thDomDef, standard_dom_iff]

/-- **The coded field predicate, read in `ℕ`, is `NF ∧ Dom`.** -/
theorem eval_fld_iff (t : ThetaWTerm) :
    orderFormulas.fld (code t : ℕ) ↔ NF t ∧ Dom t := by
  show orderFormulas.nf (code t : ℕ) ∧ orderFormulas.dom (code t : ℕ) ↔ NF t ∧ Dom t
  rw [eval_nf_iff, eval_dom_iff]

/-! ### Surjectivity of the field onto normal domain terms -/

/-- **Every code satisfying the field predicate in `ℕ` is the code of a normal domain term.**
The field of the coded order in `ℕ` is exactly `{code t | NF t ∧ Dom t}`. -/
theorem fld_surj (n : ℕ) (h : orderFormulas.fld n) :
    ∃ t : ThetaWNoteD, code (t.1 : ThetaWTerm) = n := by
  have h' : orderFormulas.nf n ∧ orderFormulas.dom n := h
  have hisNF : isNF n := eval_thNFDef n |>.mp h'.1
  have hisDom : isDom n := eval_thDomDef n |>.mp h'.2
  have hisTerm : isTerm n := isTerm_of_isNF hisNF
  obtain ⟨t, ht⟩ := isTerm_surj n hisTerm
  have hNF : NF t := (standard_nf_iff t).mp (by rw [ht]; exact hisNF)
  have hDom : Dom t := (standard_dom_iff t).mp (by rw [ht]; exact hisDom)
  exact ⟨⟨t, hNF, hDom⟩, ht⟩

/-! ### Slot check: small concrete terms -/

section SlotCheck

/-- **Same-level clause, at the `OrderFormulas` level**: `ϑ₀(Ω₂) ≺ ϑ₀(Ω₃)`, the same pair as
`Internal/Order.lean`'s `slotCheck_iltb_theta_same_level`, now read through `eval_lt_iff_lt`. -/
example :
    orderFormulas.lt (code (theta 0 (Omega 1)) : ℕ) (code (theta 0 (Omega 2))) := by
  rw [eval_lt_iff_lt, theta_lt_theta_iff]
  exact Or.inl ⟨(Omega_lt_Omega_iff 1 2).mpr (by norm_num), by simp⟩

/-- **A genuine field element, at the `OrderFormulas` level**: `ϑ_0(Ω_6)` is in the field of the
coded order in `ℕ` (`Internal/Order.lean`'s `slotCheck_isDom_theta0_Omega5` upgraded from
`isDom` alone to the full `fld = NF ∧ Dom`), and `fld_surj` recovers exactly this term back. -/
example : orderFormulas.fld (code (theta 0 (Omega 5)) : ℕ) := by
  rw [eval_fld_iff]
  exact ⟨by simp, dom_theta_Omega 0 5⟩

/-- **`fld_surj` recovers exactly this term back.** -/
example : ∃ t : ThetaWNoteD, t.1 = theta 0 (Omega 5) := by
  obtain ⟨t, ht⟩ := fld_surj (code (theta 0 (Omega 5)) : ℕ)
    (by rw [eval_fld_iff]; exact ⟨by simp, dom_theta_Omega 0 5⟩)
  exact ⟨t, code_inj.mp ht⟩

end SlotCheck

end OrdinalAnalysis.IDn.Internal
