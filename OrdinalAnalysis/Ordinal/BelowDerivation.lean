/-
  Restricting a derivation to the notations below a bound.

  The rules of the ω-calculus mention the height only through `<` between a
  premise's height and the conclusion's, and the order of `Below ε` is the
  order of `O` on the underlying notations.  So a derivation whose height is
  below `ε` is, verbatim, a derivation in `Below ε`: every premise's height is
  below the conclusion's, hence below `ε` too.

  This is the step that puts the ε₁ lower bound into the notation system it
  has to be stated in.  Boundedness reads a derivation's `X`-atoms as codes of
  elements of its height system, and the induction axiom it refutes is
  transfinite induction along all of that system's coded ordering; for
  `|PA + TI(ε₀)| = ε₁` the system must therefore be exactly the notations
  below `ε₁`, while the derivations are built in the Veblen notations at
  large and only afterwards seen to stay below `ε₁`.

  The `OrdinalNotation (Below ε)` instance plays no role in the proof — only
  `<` is used — but the calculus cannot be *stated* at `Below ε` without it.

  One elaboration point: the height is written `Below.mk α hα` rather than
  `⟨α, hα⟩`, because the anonymous constructor reports its type as the
  subtype `{o // o < ε}` and instance search then cannot find the
  `OrdinalNotation` instance, which is declared on the `def` `Below ε`.
-/
import OrdinalAnalysis.Ordinal.Below
import OrdinalAnalysis.Omega.Calculus

set_option autoImplicit false

namespace OrdinalAnalysis

open LO LO.FirstOrder

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

omit [WellFoundedLT O] [OrdinalNotation O] in
/-- The element of `Below ε` with underlying notation `a`. -/
def Below.mk {ε : O} (a : O) (h : a < ε) : Below ε := ⟨a, h⟩

omit [WellFoundedLT O] [OrdinalNotation O] in
@[simp] theorem Below.mk_val {ε : O} (a : O) (h : a < ε) : (Below.mk a h).1 = a := rfl

omit [WellFoundedLT O] [OrdinalNotation O] in
theorem Below.mk_lt_mk {ε : O} {a b : O} (ha : a < ε) (hb : b < ε) (h : a < b) :
    Below.mk a ha < Below.mk b hb := h

namespace OmegaDerivable

variable {L : Language}

/-- **Restriction to the notations below `ε`.**  A derivation of height below
`ε` is a derivation in `Below ε`, at the same rank, of the same sequent. -/
theorem toBelow {ε : O} [OrdinalNotation (Below ε)] {A : Literals L} {I : Instantiation L}
    {r : ℕ} :
    ∀ {α : O} {Γ : Sequent L}, OmegaDerivable A I r α Γ →
      ∀ (hα : α < ε), OmegaDerivable (O := Below ε) A I r (Below.mk α hα) Γ := by
  intro α Γ h
  induction h with
  | atom hφ => intro _; exact atom hφ
  | identity rl v => intro _; exact identity rl v
  | verum => intro _; exact verum
  | or hβ _ ih =>
      intro hα
      exact or (Below.mk_lt_mk _ _ hβ) (ih (lt_trans hβ hα))
  | and hβ hγ _ _ ihφ ihψ =>
      intro hα
      exact and (Below.mk_lt_mk _ _ hβ) (Below.mk_lt_mk _ _ hγ)
        (ihφ (lt_trans hβ hα)) (ihψ (lt_trans hγ hα))
  | omegaRule β hβ _ ih =>
      intro hα
      exact omegaRule (fun n => Below.mk (β n) (lt_trans (hβ n) hα))
        (fun n => Below.mk_lt_mk _ _ (hβ n)) (fun n => ih n (lt_trans (hβ n) hα))
  | exs n hβ _ ih =>
      intro hα
      exact exs n (Below.mk_lt_mk _ _ hβ) (ih (lt_trans hβ hα))
  | contraction ss _ ih => intro hα; exact contraction ss (ih hα)
  | cut hc hβ hγ _ _ ihφ ihψ =>
      intro hα
      exact cut hc (Below.mk_lt_mk _ _ hβ) (Below.mk_lt_mk _ _ hγ)
        (ihφ (lt_trans hβ hα)) (ihψ (lt_trans hγ hα))

end OmegaDerivable

end OrdinalAnalysis
