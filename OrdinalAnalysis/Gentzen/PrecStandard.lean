/-
  The coded ordering, read in the standard model.

  Everything the boundedness lemma needs to know about `≺` is about *standard*
  codes, and on standard codes `≺` is nothing but mathlib's order on `NONote`:
  the bridge `nonote_lt_iff_icmpModelCode_eq_zero` says so in every model of
  `IΣ₁`, and `ℕ` is one.  So the facts below are corollaries, not new content —
  what this file does is fix the *spelling* the boundedness induction will see
  (`precAt precCode (numLX m) (numLX n)` evaluated in `stdLX P`) and tie it to
  the order on notations.

  The one genuinely order-theoretic fact of the argument — on a linear order,
  if everything below `o` is below `γ` then `o ≤ γ` — used to be stated here for
  `NONote`.  It says nothing about `≺`, so it now lives generically as
  `Gentzen.le_of_forall_lt_lt` in `Gentzen/CodedOrder.lean`.
-/
import OrdinalAnalysis.Gentzen.StandardLX
import OrdinalAnalysis.Gentzen.LowerSyntax

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.PrecStandard

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.CodedNotation
open OrdinalAnalysis.Gentzen.NotationBridge
open OrdinalAnalysis.Gentzen.StandardLX
open OrdinalAnalysis.Gentzen.LowerSyntax

/-- `m ≺ n` on natural numbers: the coded ordering read in `ℕ`. -/
def precN (m n : ℕ) : Prop := precDef.val.Evalb ![m, n]

theorem precN_iff (m n : ℕ) : precN m n ↔ isNF m ∧ isNF n ∧ icmp m n = 0 :=
  eval_precDef (V := ℕ) m n

/-- In `ℕ`, the model code of a notation is its code. -/
@[simp] theorem nonoteModelCode_nat (o : NONote) :
    nonoteModelCode (V := ℕ) o = nonoteCode o := by
  simp [nonoteModelCode]

/-- **Standard codes are ordered as the notations are.** -/
theorem precN_code_iff (a b : NONote) :
    precN (nonoteCode a) (nonoteCode b) ↔ a < b := by
  rw [precN_iff]
  have hb := nonote_lt_iff_icmpModelCode_eq_zero (V := ℕ) a b
  simp only [nonoteModelCode_nat] at hb
  have ha' := isNF_nonoteModelCode (V := ℕ) a
  have hb' := isNF_nonoteModelCode (V := ℕ) b
  simp only [nonoteModelCode_nat] at ha' hb'
  constructor
  · rintro ⟨_, _, h⟩; exact hb.mpr h
  · intro h; exact ⟨ha', hb', hb.mp h⟩

theorem precN_code_of_lt {a b : NONote} (h : a < b) :
    precN (nonoteCode a) (nonoteCode b) :=
  (precN_code_iff a b).mpr h

theorem lt_of_precN_code {a b : NONote} (h : precN (nonoteCode a) (nonoteCode b)) :
    a < b :=
  (precN_code_iff a b).mp h

/-- The numeral's value in the operator spelling `simp` normalises to.  Derived
from `val_numLX`, which is stated for `StandardLX.numLX` — a `def`, which is why
`simp` cannot see through it and this restatement is needed. -/
@[simp] theorem opval_numeral (P : ℕ → Prop) (n : ℕ) :
    Semiterm.Operator.val (s := stdLX P) ![] (Semiterm.Operator.numeral LX n) = n := by
  have h := val_numLX (P := P) n (fun _ => 0)
  simpa [StandardLX.numLX] using h

/-- `precCode` evaluates in the standard structure as `precN`, whatever `X` is. -/
theorem eval_precCode (P : ℕ → Prop) (m n : ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := stdLX P) ![m, n] f precCode ↔ precN m n := by
  unfold precCode liftCode precN
  rw [eval_lMap_toLX]
  simp

/-- The instance the boundedness induction actually meets:
`precAt precCode (numLX m) (numLX n)` says `m ≺ n`. -/
theorem eval_precAt_numeral (P : ℕ → Prop) (m n : ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := stdLX P) ![] f
      (precAt precCode (LowerSyntax.numLX m) (LowerSyntax.numLX n)) ↔ precN m n := by
  unfold precAt
  rw [Semiformula.eval_rew]
  have e₁ : (Semiterm.val (s := stdLX P) ![] f ∘
      ⇑(Rew.subst ![LowerSyntax.numLX m, LowerSyntax.numLX n]) ∘ Semiterm.bvar) = ![m, n] := by
    have h : ∀ i : Fin 2, (Semiterm.val (s := stdLX P) ![] f ∘
        ⇑(Rew.subst ![LowerSyntax.numLX m, LowerSyntax.numLX n]) ∘ Semiterm.bvar) i = ![m, n] i := by
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> simp
    funext i; exact h i
  have e₂ : (Semiterm.val (s := stdLX P) ![] f ∘
      ⇑(Rew.subst ![LowerSyntax.numLX m, LowerSyntax.numLX n]) ∘ Semiterm.fvar) = f := by
    funext x; simp
  rw [e₁, e₂]
  exact eval_precCode P m n f

end OrdinalAnalysis.Gentzen.PrecStandard
