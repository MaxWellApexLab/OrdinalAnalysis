import OrdinalAnalysis.Gentzen.InternalONote
/-
  Generic evaluation lemmas for the `Semisentence` wrappers `.mkSigma “x y. !d 1 x y”` of a
  `𝚺₁`-defined function.

  The wrapper formulas of the order/code predicates (`iltDef`, `thLtDef`, `thInEDef`, ..) are the
  substitution instance `!d 1 x y` of the (large, `PR`-generated) formula `d` of the function.
  Proving their `Evalb` reading by `simp` directly on the concrete `d` makes a kernel that reduces
  `subst` structurally (nanoda) unfold `d`; with `d` an abstract variable the reading is proved once,
  and each concrete lemma is an instance whose only kernel obligation is delta-unfolding the
  wrapper definition.
-/

set_option autoImplicit false

namespace OrdinalAnalysis

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol

section Model

variable {V : Type*} [ORingStructure V]

theorem eval_wrap2 (d : 𝚺₁.Semisentence 3) (f : V → V → V) [h : 𝚺₁-Function₂ f via d] (x y : V) :
    (.mkSigma “x y. !d 1 x y” : 𝚺₁.Semisentence 2).val.Evalb ![x, y] ↔ f x y = 1 := by
  simp [h.iff, eq_comm]

theorem eval_wrap3 (d : 𝚺₁.Semisentence 4) (f : V → V → V → V) [h : 𝚺₁-Function₃ f via d]
    (k g a : V) :
    (.mkSigma “k g a. !d 1 k g a” : 𝚺₁.Semisentence 3).val.Evalb ![k, g, a] ↔ f k g a = 1 := by
  simp [h.iff, eq_comm]

end Model

end OrdinalAnalysis
