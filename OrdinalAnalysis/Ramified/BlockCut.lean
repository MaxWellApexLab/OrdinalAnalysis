/-
  Cut elimination block by block: `ω · ν ⊕ k ⇒ φ_1^ν (ω_k(α))`.

  `Ramified/Rank.lean` prices a level-`μ` set atom inside the block
  `[ω·(μ−1), ω·μ]`, so a derivation whose cuts are on formulas of level `≤ ν`
  has cut rank below `ω · (ν + 1)`, i.e. at most `ω · ν ⊕ k` for some finite `k`.
  Such a derivation is made cut free in two stages.

  * The finite part `k` goes first, by the first cut-elimination theorem
    (`Reduction.cutElimination_chain`): `ω · ν ⊕ k` is `k` predecessor-bound
    steps above `ω · ν` (`chain_nadd_ofNat`), and each step costs one
    `ω`-power, so the height `α` becomes `ω_k(α)`.

  * Then the `ν` blocks of width `ω`, one at a time from the top, by
    predicative cut elimination at `ξ = 1`
    (`PredicativeCutGeneral.predicativeCut_powClosed`): the rank `ω · (j + 1)`
    is `ω · j ⊕ ω^1`, and `ω · j` is a multiple of `ω` (`powClosed_omegaMul`),
    so one application of `φ_1` brings the rank down to `ω · j`.  After `ν`
    blocks the rank is `0` and the height is `φ_1^ν(ω_k(α))` (`blocks`).

  So `ν` levels of sets cost `ν` applications of `φ_1`, not one application of
  `φ_ν`; see the boundedness and upper-bound files for the ordinals of the
  theories.
-/
import OrdinalAnalysis.Ramified.PredicativeCutGeneral

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder

namespace OmegaDerivableR

variable {A : Literals LRA} {I : InstantiationR}

/-- **`ρ ⊕ n` is exactly `n` predecessor-bound steps above `ρ`.** -/
theorem chain_nadd_ofNat (ρ : Gamma0Note) :
    ∀ n : ℕ, Chain n ρ (Gamma0Note.nadd ρ (Gamma0Note.ofNat n))
  | 0 => by
    have h0 : (Gamma0Note.ofNat 0 : Gamma0Note) = 0 := Subtype.ext rfl
    show Gamma0Note.nadd ρ (Gamma0Note.ofNat 0) ≤ ρ
    rw [h0, Gamma0Note.nadd_zero]
  | (n + 1) => by
    refine ⟨Gamma0Note.nadd ρ (Gamma0Note.ofNat n), ?_, chain_nadd_ofNat ρ n⟩
    intro b hb
    have hb' : Gamma0Note.repr b < Gamma0Note.repr ρ + ((n + 1 : ℕ) : Ordinal) := by
      rw [Gamma0Note.lt_def, Gamma0Note.repr_nadd_ofNat] at hb
      exact hb
    rw [Gamma0Note.le_def, Gamma0Note.repr_nadd_ofNat]
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, ← Order.succ_eq_add_one,
      Order.lt_succ_iff] at hb'
    exact hb'

/-- **The `ν` blocks.**  A derivation at cut rank `ω · ν` becomes cut free at the
`ν`-fold `φ_1` of its height. -/
theorem blocks (hA : MemFree A) (ν : ℕ) {α : Gamma0Note} {Γ : Sequent LRA}
    (h : OmegaDerivableR A I (omegaMul ν) α Γ) :
    OmegaDerivableR A I 0 (veblenIter 1 ν α) Γ := by
  have h' : OmegaDerivableR A I (Gamma0Note.nadd 0 (Gamma0Note.omegaPowMul 1 ν)) α Γ := by
    rw [Gamma0Note.zero_nadd]
    exact h
  exact descend hA le_rfl (fun ρ' hpc => rankAbsorbed_powClosed hA 1 le_rfl ρ' hpc) ν 0
    (Gamma0Note.powClosed_zero 1) h'

/-- **Cut elimination by blocks**:

    ⊢^α_{ω·ν ⊕ k} Γ   ⇒   ⊢^{φ_1^ν(ω_k(α))}_0 Γ.

The finite part is removed by `k` steps of the first cut-elimination theorem,
the `ν` blocks of width `ω` by `ν` applications of predicative cut elimination
at `ξ = 1`. -/
theorem cutElimination_blocks (hA : MemFree A) (ν k : ℕ) {α : Gamma0Note} {Γ : Sequent LRA}
    (h : OmegaDerivableR A I (Gamma0Note.nadd (omegaMul ν) (Gamma0Note.ofNat k)) α Γ) :
    OmegaDerivableR A I 0 (veblenIter 1 ν (OrdinalNotation.omegaTower k α)) Γ :=
  blocks hA ν (cutElimination_chain hA k (chain_nadd_ofNat (omegaMul ν) k) h)

/-- **Every cut rank below `ω · (ν + 1)` is eliminated at the cost of `φ_1^ν`
after finitely many `ω`-powers**: the form a derivation whose cuts all have
level `≤ ν` arrives in (`Ramified/Embed.lean`'s `cutRankR_lt_omegaMul`). -/
theorem cutElimination_below_block (hA : MemFree A) (ν : ℕ) {ρ : Gamma0Note}
    (hρ : ρ < omegaMul (ν + 1)) {α : Gamma0Note} {Γ : Sequent LRA}
    (h : OmegaDerivableR A I ρ α Γ) :
    ∃ k : ℕ, OmegaDerivableR A I 0 (veblenIter 1 ν (OrdinalNotation.omegaTower k α)) Γ := by
  obtain ⟨k, hk⟩ := chain_of_lt_nadd_omegaPow_one (powClosed_omegaMul ν) ρ hρ
  exact ⟨k, blocks hA ν (cutElimination_chain hA k hk h)⟩

end OmegaDerivableR

end Ramified

end OrdinalAnalysis
