/-
  The climb along the coded Veblen ordering, with heights in `Gamma0Note`.

  The three inputs of `Climb.ClimbData` for `gamma0Order`, exactly as
  `ClimbEpsilon0.lean` supplies them for `epsilon0Order`:

  * a false instance `∼(k̄ ≺₁ n̄)` is a true `X`-free closed sentence, hence
    derivable by ω-completeness at the height `c₁ = complexity ≺₁` — in
    `NONote`; the height map `ofNONote` carries the derivation into the
    Veblen notations, at `K₁ := ofNONote (NONote.ofNat c₁)`;
  * `K₁` and `1` are below every `ω^(a+1)`, since both are below `ω = ω^1`
    and `1 ≤ a ⊕ 1`;
  * both sides of a true `k ≺₁ n` are codes (`CodedVeblen.precN₁_dom`).

  The file closes with the height bookkeeping the new axiom needs: the climb
  to a notation below `ε₀` stays below `ε₀`, because `ε₀` is closed under
  `ω^·`, the natural sum, `1` and the finite notations.

  `c₁` is `irreducible_def`, as `ClimbEpsilon0.c₀` is: with a transparent
  `def` the elaborator unfolds the entire formula when it meets the
  complexity, and hangs.
-/
import OrdinalAnalysis.Gentzen.Climb
import OrdinalAnalysis.Gentzen.CodedVeblen
import OrdinalAnalysis.Omega.HeightMap
import OrdinalAnalysis.Ordinal.Veblen.EpsilonBelow
import OrdinalAnalysis.Ordinal.Veblen.OfNONote

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace OrdinalAnalysis.Gentzen.ClimbVeblen

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.StandardLX (trueArithLits stdLX)
open OrdinalAnalysis.Gentzen.LowerSyntax OrdinalAnalysis.Gentzen.LowerClass
open OrdinalAnalysis.Gentzen.Evaluate OrdinalAnalysis.Gentzen.EvInst
open OrdinalAnalysis.Gentzen.LowerClassEv
open OrdinalAnalysis.Gentzen.CodedVeblen OrdinalAnalysis.Gentzen.VNoteBridge
open OrdinalAnalysis.Gentzen.OmegaTruth OrdinalAnalysis.Gentzen.Climb
open OrdinalAnalysis.Gamma0Note
open Ordinal

/-- The complexity of the coded Veblen ordering; every instance `k̄ ≺₁ n̄` has it. -/
irreducible_def c₁ : ℕ := precCode₁.complexity

/-- The height at which every false instance of `≺₁` is derivable, as a Veblen
notation: the image of the finite `NONote` height under `ofNONote`. -/
def K₁ : Gamma0Note := ofNONote (NONote.ofNat c₁)

/-! ### Ordinal facts -/

theorem repr_K₁ : repr K₁ = (c₁ : Ordinal) := by
  rw [K₁, repr_ofNONote]
  exact ONote.repr_ofNat c₁

theorem K₁_lt_epsilon0 : K₁ < epsilonNote 0 :=
  ofNONote_lt_epsilonNote_zero _

theorem repr_omegaPow_one : repr (Gamma0Note.omegaPow 1) = ω := by
  rw [repr_omegaPow, repr_one, opow_one]

theorem omegaPow_one_le_omegaPow_nadd_one (a : Gamma0Note) :
    Gamma0Note.omegaPow 1 ≤ Gamma0Note.omegaPow (Gamma0Note.nadd a 1) :=
  omegaPow_le_omegaPow (Gamma0Note.le_nadd_right a 1)

/-- `K₁ < ω^(a+1)` for every `a`: `K₁` is finite and `ω ≤ ω^(a+1)`. -/
theorem K₁_lt (a : Gamma0Note) :
    K₁ < OrdinalNotation.omegaPow (OrdinalNotation.nadd a OrdinalNotation.one) := by
  show K₁ < Gamma0Note.omegaPow (Gamma0Note.nadd a 1)
  refine lt_of_lt_of_le ?_ (omegaPow_one_le_omegaPow_nadd_one a)
  rw [lt_def, repr_K₁, repr_omegaPow_one]
  exact natCast_lt_omega0 c₁

/-- `1 < ω^(a+1)` for every `a`. -/
theorem one_lt (a : Gamma0Note) :
    OrdinalNotation.one
      < OrdinalNotation.omegaPow (OrdinalNotation.nadd a OrdinalNotation.one) := by
  show (1 : Gamma0Note) < Gamma0Note.omegaPow (Gamma0Note.nadd a 1)
  refine lt_of_lt_of_le ?_ (omegaPow_one_le_omegaPow_nadd_one a)
  rw [lt_def, repr_one, repr_omegaPow_one]
  exact one_lt_omega0

/-! ### The false instances -/

/-- `∼(k̄ ≺₁ n̄)` is a true `X`-free closed formula whenever `¬ k ≺₁ n`, hence
derivable by ω-completeness at the finite height `c₁` in `NONote`, hence at
`K₁` in the Veblen notations. -/
theorem neg_precAt_derivable {k n : ℕ} (h : ¬ precN₁ k n) :
    D K₁ [ev (∼(precAt precCode₁ (numLX k) (numLX n)))] := by
  have hX : OmegaTruth.XFree (∼(precAt precCode₁ (numLX k) (numLX n))) := by
    rw [OmegaTruth.xFree_neg]
    simp only [precAt]
    exact OmegaTruth.xFree_rew _ omegaTruth_XFree_precCode₁
  have hc : (∼(precAt precCode₁ (numLX k) (numLX n))).freeVariables = ∅ := by
    have h1 : (precAt precCode₁ (numLX k) (numLX n)).freeVariables = ∅ :=
      freeVariables_precAt_eq_empty freeVariables_precCode₁ (by simp) (by simp)
    simp [h1]
  have ht : Semiformula.Eval (s := stdLX fun _ => False) ![] (fun _ => 0)
      (∼(precAt precCode₁ (numLX k) (numLX n))) := by
    rw [OmegaTruth.eval_neg_iff, eval_precAt₁_numeral]
    exact h
  have hd := omega_complete_ev (fun _ => False) (fun _ => 0) _ hX hc ht
  have e : hgt (∼(precAt precCode₁ (numLX k) (numLX n))) = NONote.ofNat c₁ := by
    simp [hgt, c₁_def]
  rw [e] at hd
  exact hd.map_height ofNONote ofNONote_strictMono

/-! ### The climb -/

/-- **The data of the climb along `≺₁`**, with heights in the Veblen notations. -/
def veblenClimb : ClimbData gamma0Order where
  K := K₁
  neg_precAt := fun h => neg_precAt_derivable h
  K_lt := K₁_lt
  one_lt := one_lt
  dom := fun h => precN₁_dom h

@[simp] theorem veblenClimb_K : veblenClimb.K = K₁ := rfl

/-- **The climb along `≺₁`.**  `¬Prog(X), X(n̄)` is derivable for every `n`, at
some height below `Γ₀`. -/
theorem climb (n : ℕ) : ∃ α : Gamma0Note, D α [ev (∼(Prog precCode₁)), Xat (numLX n)] :=
  veblenClimb.climb n

/-- The explicit height for a code. -/
theorem climb_code (o : Gamma0Note) :
    D (veblenClimb.height o) [ev (∼(Prog precCode₁)), Xat (numLX (gamma0Code o))] :=
  veblenClimb.code o

/-! ### Below `ε₀`

The height of the climb to a notation below `ε₀` is below `ε₀`: it is a
natural sum of `ω^(o+1)`, `K₁`, and four `1`s, and `ε₀` is closed under all of
them. -/

/-- **The climb to a notation below `ε₀` stays below `ε₀`.** -/
theorem height_lt_epsilon0 {o : Gamma0Note} (ho : o < epsilonNote 0) :
    veblenClimb.height o < epsilonNote 0 := by
  have h1 : (1 : Gamma0Note) < epsilonNote 0 := one_lt_epsilon 0
  have hK : K₁ < epsilonNote 0 := K₁_lt_epsilon0
  have hw : Gamma0Note.omegaPow (Gamma0Note.nadd o 1) < epsilonNote 0 :=
    omegaPow_lt_epsilon (nadd_lt_epsilon ho h1)
  show Gamma0Note.nadd (Gamma0Note.nadd (Gamma0Note.nadd (Gamma0Note.nadd
      (Gamma0Note.nadd (Gamma0Note.omegaPow (Gamma0Note.nadd o 1)) K₁) 1) 1) 1) 1
    < epsilonNote 0
  exact nadd_lt_epsilon (nadd_lt_epsilon (nadd_lt_epsilon (nadd_lt_epsilon
    (nadd_lt_epsilon hw hK) h1) h1) h1) h1

end OrdinalAnalysis.Gentzen.ClimbVeblen
