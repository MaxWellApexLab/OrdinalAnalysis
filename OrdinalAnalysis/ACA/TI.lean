/-
  The single source of the transfinite-induction
  sentence the upper half assembles towards and the lower half refutes — `TIsegSO`/`tiUptoSegSO`,
  both instances of `toSOAt` at the free set variable `0`.  Everything here is
  a one-line application of `A3`'s `toSOAt`; no new mathematics.

  Per the design note §5.3: this file is the *single source* of the TI
  sentence, over `EpsilonSegmentOrder.precCodeSeg (epsilonNote 0)`, heights in
  `Gamma0Note.EpsilonBelow (epsilonNote 0)` — what `ACAOmega/SecondCut.lean`'s
  `EpsilonStructure`/`secondCutElimination_Gamma0` and
  `EpsilonSegmentOrder.not_derivable_TI_epsilon (epsilonNote 0)` expect.
  `ACA/Syntax.lean`'s `TISO` (over `precDef`) is the `ACA₀` warm-up and is left
  untouched.
-/
import OrdinalAnalysis.ACA.Translate
import OrdinalAnalysis.Gentzen.EpsilonSegmentOrder
import OrdinalAnalysis.Gentzen.Epsilon1UpperBound

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX TI TIupto)

/-- **The witness recovering the free set variable `0`**, over `ξ := Empty`
(no free number variable of its own) — `toSOAt`'s own requirement. -/
def segWitness : Semiformula ℒₒᵣ ℕ Empty 0 1 := (#0 : FirstOrder.Semiterm ℒₒᵣ Empty 1) ∈& (0 : ℕ)

theorem arith_segWitness : Arith segWitness := trivial

/-- **The segment below `ε₀`** that `ACAOmega.SecondCut`'s cut elimination and
`EpsilonSegmentOrder.not_derivable_TI_epsilon` work over. -/
abbrev SegNote : Type := Gamma0Note.EpsilonBelow (Gamma0Note.epsilonNote 0)

/-- **The coded ordering, restricted to `SegNote`.** -/
def precSeg : FirstOrder.Semiformula LX ℕ 2 :=
  Gentzen.EpsilonSegmentOrder.precCodeSeg (Gamma0Note.epsilonNote 0)

/-- **`TI(≺_seg, X)` at the free set variable `0`.**  What 2e refutes. -/
def TIsegSO : Proposition ℒₒᵣ := toSOAt segWitness (TI precSeg)

theorem arith_TIsegSO : Arith TIsegSO := arith_toSOAt arith_segWitness (TI precSeg)

/-- **`TIupto(≺_seg, ā, X)` at the free set variable `0`, universally closed
over the numeral-free number variables of `TIupto`.**  What the upper half proves,
one instance at a time, for every `a` below the segment's bound. -/
noncomputable def tiUptoSegSO (a : Gamma0Note) : Proposition ℒₒᵣ :=
  toSOAt segWitness
    (FirstOrder.Rewriting.emb (TIupto precSeg (Gentzen.Epsilon1UpperBound.gamma0Term a)).univCl)

theorem arith_tiUptoSegSO (a : Gamma0Note) : Arith (tiUptoSegSO a) :=
  arith_toSOAt arith_segWitness _

end OrdinalAnalysis.ACA
