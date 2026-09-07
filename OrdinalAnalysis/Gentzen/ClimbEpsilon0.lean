/-
  The climb along the ε₀-ordering, in the notations below ε₀.

  The three inputs of `Climb.ClimbData` for `epsilon0Order`: the false
  instances of `≺` are derivable by ω-completeness at height `c₀`, the
  complexity of `≺`; `c₀` and `1` are below every `ω^(a+1)` in `NONote`; and
  both sides of a true `k ≺ n` are codes (`CodeSurj.precN_dom`, which is
  where surjectivity of the coding onto the internal normal forms enters).
-/
import OrdinalAnalysis.Gentzen.Climb
import OrdinalAnalysis.Gentzen.CodeSurj

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace OrdinalAnalysis.Gentzen.ClimbEpsilon0

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.StandardLX (trueArithLits stdLX)
open OrdinalAnalysis.Gentzen.LowerSyntax OrdinalAnalysis.Gentzen.LowerClass
open OrdinalAnalysis.Gentzen.Evaluate OrdinalAnalysis.Gentzen.EvInst
open OrdinalAnalysis.Gentzen.PrecStandard OrdinalAnalysis.Gentzen.LowerClassEv
open OrdinalAnalysis.Gentzen.NotationBridge OrdinalAnalysis.Gentzen.CodedNotation
open OrdinalAnalysis.Gentzen.OmegaTruth OrdinalAnalysis.Gentzen.Climb

/-- The complexity of the coded ordering; every instance `k̄ ≺ n̄` has it. -/
irreducible_def c₀ : ℕ := precCode.complexity

/-! ### Ordinal facts -/

theorem ofNat_one_le_of_pos {o : NONote} (h : 0 < o) : NONote.ofNat 1 ≤ o := by
  refine not_lt.mp (fun h' => ?_)
  have h1 : ONote.repr o.1 < ONote.repr (ONote.ofNat 1) := h'
  have h0 : ONote.repr (0 : ONote) < ONote.repr o.1 := h
  rw [ONote.repr_ofNat] at h1
  simp only [ONote.repr_zero, Nat.cast_one] at h1 h0
  rw [Order.lt_one_iff] at h1
  rw [h1] at h0
  exact lt_irrefl _ h0

theorem ofNat_lt_omegaPow_of_pos {o : NONote} (h : 0 < o) (m : ℕ) :
    NONote.ofNat m < NONote.omegaPow o :=
  lt_of_lt_of_le (ofNat_lt_omegaNO m) (NONote.omegaPow_le_omegaPow (ofNat_one_le_of_pos h))

theorem one_lt_omegaPow_of_pos {o : NONote} (h : 0 < o) : NONote.one < NONote.omegaPow o := by
  rw [NONote.one_eq_omegaPow_zero]
  exact NONote.omegaPow_lt_omegaPow h

theorem pos_nadd_one (a : NONote) : 0 < NONote.nadd a NONote.one :=
  lt_of_le_of_lt (NONote.zero_le' a) (NONote.lt_succ a)

/-! ### The false instances -/

/-- `∼(k̄ ≺ n̄)` is a true `X`-free closed formula whenever `¬ k ≺ n`, hence
derivable by ω-completeness, at the fixed height `c₀`. -/
theorem neg_precAt_derivable {k n : ℕ} (h : ¬ precN k n) :
    D (NONote.ofNat c₀) [ev (∼(precAt precCode (numLX k) (numLX n)))] := by
  have hX : OmegaTruth.XFree (∼(precAt precCode (numLX k) (numLX n))) := by
    rw [OmegaTruth.xFree_neg]
    simp only [precAt]
    refine OmegaTruth.xFree_rew _ ?_
    simp only [precCode, liftCode]
    exact OmegaTruth.xFree_lMap_toLX _
  have hc : (∼(precAt precCode (numLX k) (numLX n))).freeVariables = ∅ := by simp
  have ht : Semiformula.Eval (s := stdLX fun _ => False) ![] (fun _ => 0)
      (∼(precAt precCode (numLX k) (numLX n))) := by
    rw [OmegaTruth.eval_neg_iff, eval_precAt_numeral]
    exact h
  have hd := omega_complete_ev (fun _ => False) (fun _ => 0) _ hX hc ht
  have e : hgt (∼(precAt precCode (numLX k) (numLX n))) = NONote.ofNat c₀ := by
    simp [hgt, c₀_def]
  rw [e] at hd
  exact hd

/-! ### The climb -/

/-- **The data of the ε₀-climb.** -/
def epsilon0Climb : ClimbData epsilon0Order where
  K := NONote.ofNat c₀
  neg_precAt := fun h => neg_precAt_derivable h
  K_lt := fun a => ofNat_lt_omegaPow_of_pos (pos_nadd_one a) c₀
  one_lt := fun a => one_lt_omegaPow_of_pos (pos_nadd_one a)
  dom := fun h => CodeSurj.precN_dom h

/-- **The climb along `≺`.**  `¬Prog(X), X(n̄)` is derivable for every `n`, at
some height below `ε₀`. -/
theorem climb (n : ℕ) : ∃ α : NONote, D α [ev (∼(Prog precCode)), Xat (numLX n)] :=
  epsilon0Climb.climb n

/-- The explicit height for a code. -/
theorem climb_code (o : NONote) :
    D (epsilon0Climb.height o) [ev (∼(Prog precCode)), Xat (numLX (nonoteCode o))] :=
  epsilon0Climb.code o

end OrdinalAnalysis.Gentzen.ClimbEpsilon0
