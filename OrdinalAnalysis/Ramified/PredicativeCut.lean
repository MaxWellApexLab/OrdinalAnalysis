/-
  Predicative cut elimination for the ramified calculus.

  Pohlers' theorem is

      ⊢^α_{ρ ⊕ ω^ξ} Γ   ⇒   ⊢^{φ_ξ(α)}_ρ Γ,

  proved by main induction on `ξ` with a side induction on `α`.  `ξ = 0` is the
  elimination lemma (`ρ + 1`, cost `φ_0(α) = ω^α`); `ξ = 1` at `ρ = 0` is
  `ACAOmega/SecondCut.lean`'s `secondCutElimination` (`ω`, cost `ε_α`), the
  theorem that turns `ε₀` into `ε_{ε₀}`.  `Ramified/Rank.lean` puts the ranks of
  the level-`≤ ν` fragment below `ω · (ν + 1)`; the theorem at `ξ = 1` with base
  `ρ = ω · j` removes one such block at a time (`Ramified/BlockCut.lean`).

  This file factors the theorem into the part that is proof theory and the part
  that is ordinal arithmetic, proves the first in full generality, and proves the
  second at `ξ = 1`.

  * **`RankAbsorbed ρ σ V ξ`** is the arithmetic half, as a hypothesis: *every*
    cut rank below `σ` can be eliminated from `max ρ a` down to `ρ` at a cost
    that `φ_ξ(β)` absorbs.  It says nothing about derivations that
    `cutElimination_chain` does not already say; what it adds is a *uniform*
    bound over the whole rank segment, which is the only thing the side
    induction needs.

  * **`predicativeCutElimination`** is the proof-theoretic half: the side
    induction on the derivation, generic in `ξ ≥ 1` and in `ρ`, `σ`.  Every
    non-cut rule is rebuilt with `V.veblen_lt_right`; the cut is reduced at
    `max ρ (rank φ)` by `Ramified/Reduction.lean`'s `reduction` and then handed
    to `RankAbsorbed`, the resulting height staying below `φ_ξ(α)` by
    `V.redOrd_lt_veblen`.  This is the whole of `secondCutElimination`'s
    argument with the ε-specific steps abstracted away.

  * **`rankAbsorbed_of_chain`** discharges `RankAbsorbed` at `ξ = 1` from the
    finite-chain property "every rank below `σ` is finitely many predecessor
    steps above `ρ`", and `chain_of_lt_omegaPowLv_one` establishes that property
    concretely for `ρ = 0`, `σ = ω^1` in `Gamma0Note` — the analogue of
    `SecondCut.lean`'s `chain_of_lt_omegaN` for `NONote`.  Together they give
    **`predicativeCut_omega`** and, over `Gamma0Note` heights,
    **`secondCutEliminationR`**: `⊢^α_ω Γ ⇒ ⊢^{ε_α}_0 Γ`.  That is the ν = 1
    regression the design note asks for, reproducing the ε-jump in the ramified
    calculus.

  ## What is missing, and why

  `PredicativeCutStatement` is the general theorem, stated for heights and ranks
  both in `Gamma0Note`, and `predicativeCutStatement_of_absorbed` proves it *from*
  `RankAbsorbed` at every level.  So the residual obligation is exactly

      RankAbsorbed A I ρ (ρ ⊕ ω^ξ) veblenStructure ξ     for every ρ and every ξ ≥ 1,

  and it is pure ordinal arithmetic on `Gamma0Note`.  Unwinding Pohlers, the main
  induction on `ξ` discharges it from three facts none of which the repository
  has today:

  1. *(successor step)* for `ξ = η + 1`, every `a < ρ ⊕ ω^{η+1}` satisfies
     `a < ρ ⊕ ω^η · m` for some `m : ℕ`, and `ρ ⊕ ω^η · m` descends to `ρ` by `m`
     applications of the level-`η` case.  `Gamma0Note` has no multiplication, so
     even the statement `ω^η · m` has to be built (as an `m`-fold natural sum,
     with `nadd_lt_omegaPow` no longer available to absorb it).
  2. *(limit step)* for `ξ` a limit, every `a < ρ ⊕ ω^ξ` satisfies
     `a < ρ ⊕ ω^η` for some `η < ξ`.  This is a Cantor-normal-form statement
     about `Gamma0Note`; the type has `repr` into `Ordinal` and could get it that
     way, but there is no `Ordinal`-side decomposition lemma in the repository
     either.
  3. *(absorption)* `φ_η(x) < φ_ξ(β)` for `η < ξ` and `x < φ_ξ(β)`.  This one is
     *already available*: it is `V.veblen_lt_right` composed with
     `V.veblen_veblen_of_lt`, both fields of `VeblenStructure`.  So the Veblen
     package as it stands is sufficient for the general case; what is missing is
     entirely the rank-segment arithmetic of (1) and (2).

  Consequence: the general `ξ` is *not* blocked on anything
  proof-theoretic and does not touch `Ramified/Reduction.lean`.  It is an
  `Ordinal/` file about the rank notation, and it should be written there rather
  than here.
-/
import OrdinalAnalysis.Ramified.Reduction
import OrdinalAnalysis.Ordinal.Veblen.VeblenStructureInstance

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Derivation

namespace OmegaDerivableR

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals LRA} {I : InstantiationR}

/-! ### The arithmetic half, as a hypothesis -/

/-- **The rank segment `[ρ, σ)` is absorbed by `φ_ξ`.**

For every cut rank `a` below `σ`, a derivation at rank `max ρ a` and height below
`φ_ξ(β)` can be brought down to rank `ρ` without leaving `φ_ξ(β)`.

`max ρ a` rather than `a`: the reduction lemma has to be applied at a rank that
is at least `rank φ` *and* at least `ρ`, because the two premises have already
been brought down to `ρ` by the side induction and `rank φ` may well be below
`ρ`.  `chain_max` is the lemma that makes this harmless.

At `ξ = 1` this is `cutElimination_chain` plus `omegaTower_lt_veblen`
(`rankAbsorbed_of_chain`).  In general it is the main induction on `ξ`, which is
where the remaining ordinal arithmetic lives; see the module docstring. -/
def RankAbsorbed (A : Literals LRA) (I : InstantiationR) (ρ σ : Gamma0Note)
    (V : VeblenStructure O) (ξ : O) : Prop :=
  ∀ a : Gamma0Note, a < σ → ∀ {α β : O} {Γ : Sequent LRA}, α < V.veblen ξ β →
    OmegaDerivableR A I (max ρ a) α Γ →
      ∃ α' : O, α' < V.veblen ξ β ∧ OmegaDerivableR A I ρ α' Γ

namespace RankAbsorbed

/-- Shrinking the segment. -/
theorem mono_seg (V : VeblenStructure O) {ρ σ σ' : Gamma0Note} {ξ : O} (hσ : σ ≤ σ')
    (h : RankAbsorbed A I ρ σ' V ξ) : RankAbsorbed A I ρ σ V ξ :=
  fun a ha => h a (lt_of_lt_of_le ha hσ)

/-- **Raising the level.**  A segment absorbed by `φ_η` is absorbed by `φ_ξ` for
every `ξ > η`, because `φ_ξ(β)` is a fixed point of `φ_η`
(`VeblenStructure.veblen_veblen_of_lt`).

This is the third of the three facts the general main induction on `ξ` needs, and
the only one of the three the repository already has; the module docstring says
so, and this lemma is the proof.  It is what lets a level-`η` elimination be
*reused* at a higher level instead of re-proved. -/
theorem mono_level (V : VeblenStructure O) {ρ σ : Gamma0Note} {η ξ : O} (hηξ : η < ξ)
    (h : RankAbsorbed A I ρ σ V η) : RankAbsorbed A I ρ σ V ξ := by
  intro a ha α β Γ hα hd
  have hfix : V.veblen η (V.veblen ξ β) = V.veblen ξ β := V.veblen_veblen_of_lt hηξ
  obtain ⟨α', hα', hd'⟩ := h a ha (β := V.veblen ξ β) (by rw [hfix]; exact hα) hd
  exact ⟨α', by rwa [hfix] at hα', hd'⟩

/-- **Composing two absorbed segments.**  `[ρ₁, σ)` descends to `ρ₁`, and then
`ρ₁` itself — which lies inside `[ρ, σ')` — descends to `ρ`.

This is the step the *successor* case of the general main induction iterates: a
rank in `[ρ ⊕ ω^{η+1})` is brought to `ρ ⊕ ω^η · m` and then walked down `m`
level-`η` steps.  What is missing for that is not this lemma but the arithmetic
that produces the finite `m` (module docstring, obstacle 1). -/
theorem trans (V : VeblenStructure O) {ρ ρ₁ σ σ' : Gamma0Note} {ξ : O}
    (hle : ρ ≤ ρ₁) (hlt : ρ₁ < σ')
    (h₁ : RankAbsorbed A I ρ₁ σ V ξ) (h₂ : RankAbsorbed A I ρ σ' V ξ) :
    RankAbsorbed A I ρ σ V ξ := by
  intro a ha α β Γ hα hd
  have hmono : max ρ a ≤ max ρ₁ a := max_le_max hle le_rfl
  obtain ⟨α', hα', hd'⟩ := h₁ a ha hα (hd.mono_rank hmono)
  have he : max ρ ρ₁ = ρ₁ := max_eq_right hle
  exact h₂ ρ₁ hlt hα' (by rw [he]; exact hd')

end RankAbsorbed

/-! ### The proof-theoretic half -/

/-- **Predicative cut elimination, given the rank arithmetic.**

A derivation at cut rank `σ` and height `α` becomes one at cut rank `ρ` and
height `φ_ξ(α)`, provided the rank segment below `σ` is absorbed by `φ_ξ`.

The proof is the side induction on the derivation.  Only the cut case does any
work: the two premises come back at rank `ρ` and heights `φ_ξ(β')`, `φ_ξ(γ')`,
both below `φ_ξ(α)`; they are raised to `max ρ (rank φ)`, reduced against each
other by `Ramified/Reduction.lean`'s `reduction`, which lands at
`redOrd (φ_ξ β') (φ_ξ γ')` — still below `φ_ξ(α)`, because `φ_ξ(α)` is closed
under the natural sum for `ξ ≥ 1` (`V.redOrd_lt_veblen`) — and the residual rank
is absorbed by hypothesis. -/
theorem predicativeCutElimination (hA : MemFree A) (V : VeblenStructure O)
    {ρ σ : Gamma0Note} {ξ : O} (hξ : OrdinalNotation.one ≤ ξ)
    (habs : RankAbsorbed A I ρ σ V ξ) :
    ∀ {α : O} {Γ : Sequent LRA}, OmegaDerivableR A I σ α Γ →
      OmegaDerivableR A I ρ (V.veblen ξ α) Γ := by
  intro α Γ h
  induction h with
  | atom h => exact .atom h
  | identity rl v => exact .identity rl v
  | verum => exact .verum
  | or hlt _ ih => exact .or (V.veblen_lt_right hlt) ih
  | and hb hc _ _ ihp ihq =>
      exact .and (V.veblen_lt_right hb) (V.veblen_lt_right hc) ihp ihq
  | omegaRule f hf _ ih =>
      exact .omegaRule (fun n => V.veblen ξ (f n)) (fun n => V.veblen_lt_right (hf n)) ih
  | exs n hlt _ ih => exact .exs n (V.veblen_lt_right hlt) ih
  | contraction ss _ ih => exact .contraction ss ih
  | pr ha hlt _ ih => exact .pr ha (V.veblen_lt_right hlt) ih
  | npr ha hlt _ ih => exact .npr ha (V.veblen_lt_right hlt) ih
  | @cut α' β' γ' φ Γ₁ Γ₂ hrank hb hc _ _ ihp ihn =>
      have hmono : ρ ≤ max ρ (rank φ) := le_max_left _ _
      have hrφ : rank φ ≤ max ρ (rank φ) := le_max_right _ _
      have hkey := reduction hA (V.veblen ξ β') (V.veblen ξ γ') (Θ := Γ₁ ++ Γ₂) hrφ
        (ihp.mono_rank hmono)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr (List.mem_append_left _ hx))
        (ihn.mono_rank hmono)
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr (List.mem_append_right _ hx))
      have hlt : OrdinalNotation.redOrd (V.veblen ξ β') (V.veblen ξ γ') < V.veblen ξ α' :=
        V.redOrd_lt_veblen hξ (V.veblen_lt_right hb) (V.veblen_lt_right hc)
      obtain ⟨α'', hα'', hd⟩ := habs (rank φ) hrank hlt hkey
      exact hd.mono_ord (le_of_lt hα'')

/-! ### `ξ = 1`: the rank segment is a finite chain -/

/-- **`RankAbsorbed` at `ξ = 1`**, from the finite-chain property.  `φ_1(β)` is
an ε-number, hence closed under `ω ^ ·`, hence under the `k`-fold tower that
`cutElimination_chain` charges for `k` rank levels. -/
theorem rankAbsorbed_of_chain (hA : MemFree A) (V : VeblenStructure O) {ρ σ : Gamma0Note}
    (hfin : ∀ a : Gamma0Note, a < σ → ∃ k : ℕ, Chain k ρ a) :
    RankAbsorbed A I ρ σ V OrdinalNotation.one := by
  intro a ha α β Γ hα h
  obtain ⟨k, hch⟩ := hfin a ha
  obtain ⟨k', hch'⟩ := chain_max hch
  exact ⟨OrdinalNotation.omegaTower k' α, V.omegaTower_lt_veblen le_rfl k' α β hα,
    cutElimination_chain hA k' hch' h⟩

/-- **Predicative cut elimination at `ξ = 1`.**  The ramified form of
`ACAOmega/SecondCut.lean`'s `secondCutElimination`, generalised from the base
rank `0` to an arbitrary `ρ`: if every cut rank below `σ` is finitely many
predecessor steps above `ρ`, then rank `σ` at height `α` becomes rank `ρ` at
height `φ_1(α)`. -/
theorem predicativeCutElimination_one (hA : MemFree A) (V : VeblenStructure O)
    {ρ σ : Gamma0Note} (hfin : ∀ a : Gamma0Note, a < σ → ∃ k : ℕ, Chain k ρ a)
    {α : O} {Γ : Sequent LRA} (h : OmegaDerivableR A I σ α Γ) :
    OmegaDerivableR A I ρ (V.veblen OrdinalNotation.one α) Γ :=
  predicativeCutElimination hA V le_rfl (rankAbsorbed_of_chain hA V hfin) h

/-! ### The finite-chain property for `Gamma0Note`, below `ω`

`SecondCut.lean` proves this for `NONote` (`chain_of_repr`, `chain_of_lt_omegaN`);
the ramified calculus ranks in `Gamma0Note`, and the proof is the same one read
through `Gamma0Note.repr`. -/

/-- A rank whose value is the natural number `n` is reached from `0` in `n`
predecessor steps. -/
theorem chain_of_repr : ∀ (n : ℕ) (a : Gamma0Note), Gamma0Note.repr a = (n : Ordinal) →
    Chain n 0 a
  | 0, a, h => by
      show a ≤ (0 : Gamma0Note)
      rw [Gamma0Note.le_def, h]
      simp
  | n + 1, a, h => by
      have hr : Gamma0Note.repr (Gamma0Note.ofNat n) = (n : Ordinal) := Gamma0Note.repr_ofNat n
      refine ⟨Gamma0Note.ofNat n, ?_, chain_of_repr n (Gamma0Note.ofNat n) hr⟩
      intro b hb
      have hb' : Gamma0Note.repr b < Gamma0Note.repr a := hb
      rw [h] at hb'
      have hcast : ((n + 1 : ℕ) : Ordinal) = Order.succ (n : Ordinal) := by
        rw [Order.succ_eq_add_one]
        push_cast
        rfl
      rw [hcast] at hb'
      rw [Gamma0Note.le_def, hr]
      exact Order.lt_succ_iff.mp hb'

/-- `ω^1` is `ω`. -/
theorem repr_omegaPowLv_one : Gamma0Note.repr (omegaPowLv 1) = Ordinal.omega0 := by
  show Gamma0Note.repr (OrdinalNotation.omegaPow (OrdinalNotation.ofNat 1)) = _
  simp only [OrdinalNotation.Gamma0Note_omegaPow, OrdinalNotation.Gamma0Note_ofNat,
    Gamma0Note.repr_omegaPow, Gamma0Note.repr_ofNat, Nat.cast_one]
  exact Ordinal.opow_one _

/-- **Every rank below `ω` is a finite chain from `0`.**  The `Gamma0Note` form
of `SecondCut.lean`'s `chain_of_lt_omegaN`, and the fact that makes the `ξ = 1`
instance non-vacuous. -/
theorem chain_of_lt_omegaPowLv_one (a : Gamma0Note) (h : a < omegaPowLv 1) :
    ∃ k : ℕ, Chain k 0 a := by
  have h' : Gamma0Note.repr a < Ordinal.omega0 := by
    have hr : Gamma0Note.repr a < Gamma0Note.repr (omegaPowLv 1) := h
    rwa [repr_omegaPowLv_one] at hr
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp h'
  exact ⟨n, chain_of_repr n a hn⟩

/-- **The ε-jump, in the ramified calculus.**  A derivation whose cuts are all of
rank below `ω` — that is, on formulas whose set atoms have level `≤ 1` and, at
level `1`, ground set arguments (`Ramified/Rank.lean`'s `rank_lt_block_of_level`
and `memRank`) — at height `α` becomes cut free at height `φ_1(α)`.

This is the one-level regression against `ACAOmega/SecondCut.lean`: cut rank
`ω` costs exactly `α ↦ ε_α`. -/
theorem predicativeCut_omega (hA : MemFree A) (V : VeblenStructure O)
    {α : O} {Γ : Sequent LRA} (h : OmegaDerivableR A I (omegaPowLv 1) α Γ) :
    OmegaDerivableR A I 0 (V.veblen OrdinalNotation.one α) Γ :=
  predicativeCutElimination_one hA V chain_of_lt_omegaPowLv_one h

/-! ### The regression, concretely -/

/-- `φ_1` on `Gamma0Note` *is* the ε-function of `Ordinal/Veblen/Epsilon.lean`;
`Ordinal/Veblen/VeblenStructureInstance.lean` records the same identification at
the level of structures (`epsilonStructure_eq`). -/
theorem veblen_one_eq_epsilonNote (α : Gamma0Note) :
    Gamma0Note.veblenStructure.veblen OrdinalNotation.one α = Gamma0Note.epsilonNote α := rfl

/-- **The second cut-elimination theorem for the ramified calculus**, with both
heights and ranks in `Gamma0Note`:

    ⊢^α_ω Γ   ⇒   ⊢^{ε_α}_0 Γ.

Exactly `ACAOmega/SecondCut.lean`'s `secondCutElimination`, with the
`SubstProvider` argument replaced by `MemFree` and the rank `ω` now meaning
"no set atom above level `0` is cut on". -/
theorem secondCutEliminationR (hA : MemFree A) {α : Gamma0Note} {Γ : Sequent LRA}
    (h : OmegaDerivableR A I (omegaPowLv 1) α Γ) :
    OmegaDerivableR A I 0 (Gamma0Note.epsilonNote α) Γ :=
  predicativeCut_omega hA Gamma0Note.veblenStructure h

/-- **Both theorems together**, as `cutElimination_epsilon` does for `ACA_∞`:
rank `ω + k` at height `α` becomes cut free at height `ε_{ω_k(α)}`. -/
theorem cutElimination_epsilonR (hA : MemFree A) {k : ℕ} {ρ' : Gamma0Note}
    (hch : Chain k (omegaPowLv 1) ρ') {α : Gamma0Note} {Γ : Sequent LRA}
    (h : OmegaDerivableR A I ρ' α Γ) :
    OmegaDerivableR A I 0 (Gamma0Note.epsilonNote (OrdinalNotation.omegaTower k α)) Γ :=
  secondCutEliminationR hA (cutElimination_chain hA k hch h)

/-! ### The general theorem, and the exact residual obligation -/

/-- **Predicative cut elimination in full**, for heights and ranks both in
`Gamma0Note`:  `⊢^α_{ρ ⊕ ω^ξ} Γ ⇒ ⊢^{φ_ξ(α)}_ρ Γ` for every `ξ ≥ 1`.

Stated, not proved; `predicativeCutStatement_of_absorbed` reduces it to the
arithmetic obligation, and the module docstring says what that obligation needs. -/
def PredicativeCutStatement (A : Literals LRA) (I : InstantiationR) : Prop :=
  ∀ (ρ ξ : Gamma0Note), OrdinalNotation.one ≤ ξ →
    ∀ {α : Gamma0Note} {Γ : Sequent LRA},
      OmegaDerivableR A I (OrdinalNotation.nadd ρ (OrdinalNotation.omegaPow ξ)) α Γ →
        OmegaDerivableR A I ρ (Gamma0Note.veblenStructure.veblen ξ α) Γ

/-- **The general theorem follows from the rank arithmetic alone.**

Everything proof-theoretic in Pohlers' predicative cut elimination is already
done: what is left is `RankAbsorbed` at each level, i.e. the statement that the
rank segment `[ρ, ρ ⊕ ω^ξ)` descends to `ρ` at a cost `φ_ξ` absorbs.  The `ξ = 1`
instance of that hypothesis is `rankAbsorbed_of_chain` together with
`chain_of_lt_omegaPowLv_one`. -/
theorem predicativeCutStatement_of_absorbed (hA : MemFree A)
    (habs : ∀ (ρ ξ : Gamma0Note), OrdinalNotation.one ≤ ξ →
      RankAbsorbed A I ρ (OrdinalNotation.nadd ρ (OrdinalNotation.omegaPow ξ))
        Gamma0Note.veblenStructure ξ) :
    PredicativeCutStatement A I := by
  intro ρ ξ hξ α Γ h
  exact predicativeCutElimination hA Gamma0Note.veblenStructure hξ (habs ρ ξ hξ) h

end OmegaDerivableR

end Ramified

end OrdinalAnalysis
