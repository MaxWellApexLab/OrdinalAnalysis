/- Source: OrdinalAnalysis\IDn\InternalFacts.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega; the order-formula part only). -/

import OrdinalAnalysis.IDw.UpperAux
import OrdinalAnalysis.IDw.Internal.Order

/-
  The concrete formulas of the internal order of `IDw/Internal/Order.lean`.

  The three `Σ₁` formulas the theories and sentences of the upper bound are written with
  (`OrderFormulas`, `IDw/UpperAux.lean`): `x ≺ y` is `iltb x y = 1` (`iltDef`), normal form is
  `isNF` (`thNFDef`) and the domain condition is `isDom` (`thDomDef`, both of
  `IDw/Internal/Order.lean`).  `orderFormulas := ⟨iltDef, thNFDef, thDomDef⟩` is the instance
  read by `IDw/Internal/OrderBridge.lean`.

  The rest of `IDn/InternalFacts.lean` (the field-by-field proof of `OrderAxioms` up to
  transitivity, `InternalOrderFacts.ofTrans`, the slot check for `precW`, and the headlines
  `idn_upper_bound_of_trans`, `idlt_upper_bound_of_trans`) is not part of this file: the
  `OrderAxioms` fields for the coded order are discharged unconditionally from
  `IDw/Internal/{Order,OrderT,OrderE,JumpList}.lean` (the role of `IDn/Internal/OrderFacts.lean`),
  and the headlines need the theorem side of the upper bound.
-/

set_option autoImplicit false

namespace OrdinalAnalysis.IDw.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.IDw.Internal

/-! ### The concrete formulas -/

/-- `iltb x y = 1`, slot `0` the smaller element. -/
def iltDef : 𝚺₁.Semisentence 2 := .mkSigma “x y. !iltbDef 1 x y”

/-- **The formulas of the internal order of `IDw/Internal/Order.lean`.** -/
def orderFormulas : OrderFormulas := ⟨iltDef, thNFDef, thDomDef⟩

section Model

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eval_iltDef (x y : V) : iltDef.val.Evalb ![x, y] ↔ iltb x y = 1 := by
  simp [iltDef, iltb_defined.iff, eq_comm]

end Model

end OrdinalAnalysis.IDw.Upper
