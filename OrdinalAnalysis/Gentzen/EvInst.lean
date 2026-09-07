/-
  The evaluating instantiation.

  The infinitary calculus takes as a parameter how its quantifiers are
  instantiated.  For the replay of PA[X] proofs the right choice is
  "substitute the numeral, then evaluate every ground term": that is
  Buchholz's convention that closed terms are identified with their values,
  and it is what lets the ω-rule see `X(n+1‾)` where the syntax has
  `X(n̄ + 1)`.

  This file packages the evaluator of `Evaluate.lean` as an `Instantiation`,
  and transports along `ev` — from plain substitution to evaluated
  substitution — the one family of derivations proved under the former: the
  ω-completeness of true X-free sentences.  The transport is the general lemma
  of `Omega/Transfer.lean`; what has to be checked here is only that `ev`
  respects the rules, and every clause is one of the evaluator's equations.
-/
import OrdinalAnalysis.Omega.Transfer
import OrdinalAnalysis.Gentzen.Evaluate
import OrdinalAnalysis.Gentzen.OmegaTruth

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.EvInst

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen OrdinalAnalysis.Gentzen.StandardLX
open OrdinalAnalysis.Gentzen.Evaluate OrdinalAnalysis.Gentzen.OmegaTruth

/-- Substitute the numeral, then evaluate the ground terms. -/
def evInst : Instantiation LX :=
  ⟨numLX, ev, fun φ => ev_neg φ, fun φ => complexity_ev φ⟩

@[simp] theorem evInst_num : evInst.num = numLX := rfl

theorem evInst_inst (φ : Semiproposition LX 1) (n : ℕ) :
    evInst.inst φ n = ev (φ/[numLX n]) := rfl

/-- The instance of an evaluated body is the evaluated instance: evaluating
the body first changes nothing, by the congruence law of the evaluator. -/
theorem evInst_inst_ev (φ : Semiproposition LX 1) (n : ℕ) :
    evInst.inst (ev φ) n = ev (φ/[numLX n]) := by
  rw [evInst_inst]
  exact ev_rew_ev φ 0 (Rew.subst ![numLX n])

/-- `ev` respects every rule of the calculus. -/
def evTransport :
    OmegaDerivable.Transport trueArithLits (Instantiation.raw numLX) evInst where
  F := fun {_} φ => ev φ
  F_verum := fun {_} => ev_verum
  F_or := fun φ ψ => ev_or φ ψ
  F_and := fun φ ψ => ev_and φ ψ
  F_all := fun φ => ev_all φ
  F_exs := fun φ => ev_exs φ
  F_neg := fun φ => ev_neg φ
  F_complexity := fun φ => complexity_ev φ
  F_inst := fun φ n => by
    rw [Instantiation.raw_inst, evInst_inst_ev]
  F_atom := fun _ h => trueArithLits_ev h
  F_rel := fun rl v => ⟨fun i => evT (v i), ev_rel rl v⟩

/-- **Transport along `ev`.** -/
theorem toEv {r : ℕ} {α : NONote} {Γ : Sequent LX}
    (h : OmegaDerivable trueArithLits (Instantiation.raw numLX) r α Γ) :
    OmegaDerivable trueArithLits evInst r α (Γ.map ev) :=
  OmegaDerivable.transport evTransport h

/-- ω-completeness of true X-free closed formulas, in the evaluating calculus. -/
theorem omega_complete_ev (P : ℕ → Prop) (f : ℕ → ℕ) (φ : Proposition LX)
    (hX : XFree φ) (hc : φ.freeVariables = ∅)
    (ht : Semiformula.Eval (s := stdLX P) ![] f φ) :
    OmegaDerivable trueArithLits evInst 0 (hgt φ) [ev φ] :=
  toEv (omega_complete P f φ hX hc ht)

/-- The same for an arithmetic sentence true in `ℕ`. -/
theorem omega_complete_sentence_ev (σ : Sentence ℒₒᵣ)
    (h : Semiformula.Eval (M := ℕ) ![] Empty.elim σ) :
    OmegaDerivable trueArithLits evInst 0
      (hgt (Rewriting.emb (Semiformula.lMap toLX σ)))
      [ev (Rewriting.emb (Semiformula.lMap toLX σ) : Proposition LX)] :=
  toEv (omega_complete_sentence σ h)

end OrdinalAnalysis.Gentzen.EvInst
