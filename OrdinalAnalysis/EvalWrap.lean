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


/-- Successor step of a finite-iteration `PR` construction whose step function is the abstract
`𝚺₁`-function `f` (defined by `d`): the blueprint formula is `“y ih k b w. !d y ih w”`. -/
theorem iterSucc_defined_wrap (d : 𝚺₁.Semisentence 3) (f : V → V → V)
    [h : 𝚺₁-Function₂ f via d] :
    𝚺₁.DefinedFunction (fun v : Fin 4 → V ↦ f (v 0) (v 3))
      (.mkSigma “y ih k b w. !d y ih w” : 𝚺₁.Semisentence 5) := .mk fun v ↦ by
  simp [h.iff]

/-- Successor step of a finite-tower `PR` construction (one parameter) whose step function is
the abstract `𝚺₁`-function `f` (defined by `d`): the blueprint formula is
`“y ih k c. !d y ih”`. -/
theorem towerSucc_defined_wrap (d : 𝚺₁.Semisentence 2) (f : V → V)
    [h : 𝚺₁-Function₁ f via d] :
    𝚺₁.DefinedFunction (fun v : Fin 3 → V ↦ f (v 0))
      (.mkSigma “y ih k c. !d y ih” : 𝚺₁.Semisentence 4) := .mk fun v ↦ by
  simp [h.iff]

end Model

end OrdinalAnalysis
