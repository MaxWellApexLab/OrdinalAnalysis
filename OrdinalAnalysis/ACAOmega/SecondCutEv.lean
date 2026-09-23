/-
  Cut elimination for `ACA_∞` under the **evaluating** instantiation.

  Everything is already proved: `Reduction.lean` gives the first cut-elimination
  theorem for any `SubstProvider`, `SecondCut.lean` the second for any
  `EpsilonStructure`, `EvProvider.lean` the provider of `evInst₂`, and
  `Ordinal/Veblen/Instance.lean` the ε-numbers of `Gamma0Note`.  This file plugs
  them together and supplies the last missing arithmetic: the rank chains that
  start at `ω` rather than at `0`.

  The replay of a finitary `ACA` derivation produces cuts on formulas of rank
  `< ω + k` for some fixed `k` (each set quantifier costs `ω`, each of the
  finitely many propositional and number-quantifier steps above it costs one
  more), so what the tower needs is `Chain k ω (ω + k)` — and `ω + k` is
  `omegaN + NONote.ofNat k`, whose `repr` is `ω + k` by `NONote.repr_add`.
  `chain_of_repr_omegaAdd` is `SecondCut.lean`'s `chain_of_repr` shifted by `ω`:
  every notation below `ω + (k+1)` is at most `ω + k`, because `ω + (k+1)` is
  the successor of `ω + k`.
-/
import OrdinalAnalysis.ACAOmega.EvProvider
import OrdinalAnalysis.ACAOmega.SecondCut

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA

namespace OmegaDerivable₂

/-! ### The rank chains that start at `ω` -/

/-- The notation `ω + n`. -/
def omegaAdd (n : ℕ) : NONote := omegaN + NONote.ofNat n

@[simp] theorem repr_omegaAdd (n : ℕ) :
    NONote.repr (omegaAdd n) = Ordinal.omega0 + (n : Ordinal) := by
  rw [omegaAdd, NONote.repr_add, repr_omegaN]
  congr 1
  exact ONote.repr_ofNat n

@[simp] theorem omegaAdd_zero : omegaAdd 0 = omegaN + 0 := rfl

theorem omegaN_le_omegaAdd (n : ℕ) : omegaN ≤ omegaAdd n := by
  show NONote.repr omegaN ≤ NONote.repr (omegaAdd n)
  rw [repr_omegaAdd, repr_omegaN]
  simpa using Ordinal.add_le_add_left (Ordinal.zero_le (n : Ordinal)) Ordinal.omega0

/-- **Every notation whose value is `ω + n` is `n` predecessor steps from
`ω`.** -/
theorem chain_of_repr_omegaAdd : ∀ (n : ℕ) (a : NONote),
    NONote.repr a = Ordinal.omega0 + (n : Ordinal) → Chain n omegaN a
  | 0, a, h => by
      show NONote.repr a ≤ NONote.repr omegaN
      rw [h, repr_omegaN]
      simp
  | n + 1, a, h => by
      refine ⟨omegaAdd n, ?_, chain_of_repr_omegaAdd n (omegaAdd n) (repr_omegaAdd n)⟩
      intro b hb
      show NONote.repr b ≤ NONote.repr (omegaAdd n)
      have hb' : NONote.repr b < NONote.repr a := hb
      have e : Ordinal.omega0 + ((n + 1 : ℕ) : Ordinal)
          = Order.succ (Ordinal.omega0 + (n : Ordinal)) := by
        rw [Nat.cast_succ, ← add_assoc, Order.succ_eq_add_one]
      rw [h, e] at hb'
      rw [repr_omegaAdd]
      exact Order.lt_succ_iff.mp hb'

/-- `ω + k` is reached from `ω` in `k` steps. -/
theorem chain_omegaAdd (k : ℕ) : Chain k omegaN (omegaAdd k) :=
  chain_of_repr_omegaAdd k (omegaAdd k) (repr_omegaAdd k)

/-! ### Cut elimination for the evaluating calculus -/

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- **The second cut-elimination theorem for the evaluating calculus**, at
heights in an arbitrary notation system with ε-numbers. -/
theorem secondCutElimination_ev (E : EpsilonStructure O) {α : O}
    {Γ : SecondOrder.Sequent ℒₒᵣ}
    (h : OmegaDerivable₂ trueArithLits₂ evInst₂ omegaN α Γ) :
    OmegaDerivable₂ trueArithLits₂ evInst₂ 0 (E.epsilon α) Γ :=
  secondCutElimination evProvider E h

/-- **Both theorems together**, at heights in `Gamma0Note`: a replayed
derivation of rank `ρ'` reached from `ω` in `k` steps, at height `α`, is cut
free at height `ε_{ω_k(α)}`. -/
theorem cutElimination_epsilon_ev {k : ℕ} {ρ' : NONote} (hch : Chain k omegaN ρ')
    {α : Gamma0Note} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (h : OmegaDerivable₂ trueArithLits₂ evInst₂ ρ' α Γ) :
    OmegaDerivable₂ trueArithLits₂ evInst₂ 0
      (Gamma0Note.epsilonNote (OrdinalNotation.omegaTower k α)) Γ :=
  cutElimination_epsilon evProvider Gamma0Note.epsilonStructure hch h

/-- **The form the lower bound will use.**  A replayed derivation with cuts of
rank below `ω + k` becomes cut free at height `ε_{ω_k(α)}`. -/
theorem cutElimination_omegaAdd_ev (k : ℕ) {α : Gamma0Note}
    {Γ : SecondOrder.Sequent ℒₒᵣ}
    (h : OmegaDerivable₂ trueArithLits₂ evInst₂ (omegaAdd k) α Γ) :
    OmegaDerivable₂ trueArithLits₂ evInst₂ 0
      (Gamma0Note.epsilonNote (OrdinalNotation.omegaTower k α)) Γ :=
  cutElimination_epsilon_ev (chain_omegaAdd k) h

/-- The second theorem alone, at heights in `Gamma0Note`. -/
theorem secondCutElimination_ev_Gamma0 {α : Gamma0Note} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (h : OmegaDerivable₂ trueArithLits₂ evInst₂ omegaN α Γ) :
    OmegaDerivable₂ trueArithLits₂ evInst₂ 0 (Gamma0Note.epsilonNote α) Γ :=
  secondCutElimination evProvider Gamma0Note.epsilonStructure h

/-- **Substituting the witness into a `(∀₂)` eigenvariable derivation**, for the
evaluating instantiation: the interface the reduction lemma consumes, spelled
out here because the replay calls it directly. -/
theorem subst_eigen_ev {ρ : NONote} (hρ : omegaN ≤ ρ)
    {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1} (hψ : Arith ψ) {α : O}
    {φ : Semiproposition ℒₒᵣ 1 0} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (h : OmegaDerivable₂ trueArithLits₂ evInst₂ ρ α
      (Semiproposition.free₁ φ :: SecondOrder.Sequent.shift₁ Γ)) :
    OmegaDerivable₂ trueArithLits₂ evInst₂ ρ α (evInst₂.inst₂ φ ψ :: Γ) :=
  SubstProvider.subst_eigen evProvider hρ hψ h

end OmegaDerivable₂

end OrdinalAnalysis.ACAOmega
