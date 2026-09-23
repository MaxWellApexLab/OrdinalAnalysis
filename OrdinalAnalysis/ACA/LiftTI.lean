/-
  The lifting specialised to the parameter
  `TI.lean`'s `segWitness` (`#0 ∈& 0`), which is the one `Lifted.lean`
  uses.  Everything here is `lift_paLX₀` at `ψ := segWitness` — the point of the
  file is that the images are *definitionally* the propositions `TI.lean`
  already names, so the assembly never has to compute a `toSOAt`.
-/
import OrdinalAnalysis.ACA.Lift
import OrdinalAnalysis.ACA.TI

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX TIupto paLX)

/-- **`lift_paLX` at the free-set-variable parameter `#0 ∈& 0`.**  This is the
form the assembly needs: `segWitness` has a free set variable, so it is *not*
`NoSetFvar`; the bound-slot presentation `#0 ∈# 0` of `lift_paLX₀` is what makes
the induction scheme's image an `ACA`-axiom all the same. -/
theorem lift_paLX_seg {σ : FirstOrder.Sentence LX} (h : paLX ⊢ σ) :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb σ)) :=
  lift_paLX₀ segWitness arith_segWitness h

/-- **The image of a `TIupto`-instance is exactly `TI.lean`'s `tiUptoSegSO`.** -/
theorem lift_tiUptoSeg (a : Gamma0Note)
    (h : paLX ⊢ (TIupto precSeg (Gentzen.Epsilon1UpperBound.gamma0Term a)).univCl) :
    Provable ACA (tiUptoSegSO a) :=
  lift_paLX_seg h

/-- **The image of `closedTI₁ φ t`.**  `closedTI₁ φ t = (tiUptoAt precCode₁ φ t).univCl`,
so the image is the `∀¹`-closure of the lifted matrix; `toSOAtB_allClosure` and
`toSOAtB_rew` compute it whenever a caller needs it spelled out. -/
theorem lift_closedTI₁ (φ : FirstOrder.Semiformula LX ℕ 1)
    (t : FirstOrder.Semiterm LX ℕ 0)
    (h : paLX ⊢ Gentzen.Epsilon1UpperBound.closedTI₁ φ t) :
    Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      ((Gentzen.tiUptoAt Gentzen.CodedVeblen.precCode₁ φ t).univCl))) :=
  lift_paLX_seg h

end OrdinalAnalysis.ACA
