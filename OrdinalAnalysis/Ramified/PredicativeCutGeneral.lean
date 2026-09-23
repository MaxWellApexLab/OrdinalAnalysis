/-
  Predicative cut elimination for the ramified calculus, at every level `ξ`.

  `Ramified/PredicativeCut.lean` proved the proof-theoretic half in full
  (`predicativeCutElimination`) and reduced the theorem

      ⊢^α_{ρ ⊕ ω^ξ} Γ   ⇒   ⊢^{φ_ξ(α)}_ρ Γ

  to a single hypothesis about the rank notation,
  `RankAbsorbed A I ρ (ρ ⊕ ω^ξ) V ξ`, discharged there at `ξ = 1`.  This file
  discharges it at every `ξ ≥ 1`, by Pohlers' main induction on `ξ`, using the
  rank arithmetic of `Ordinal/Veblen/RankSegments.lean`.

  ## The side condition, and why it is not a weakening

  `⊕` is the **natural** sum, and the theorem as stated for an arbitrary `ρ` is
  false.  At `ρ = 1`, `ξ = 1` the segment is `[1, 1 ⊕ ω) = [1, ω + 1)`, which
  contains the *limit* rank `ω`: a derivation of cut-rank bound `ω` carries cuts
  of unbounded finite rank, and bringing it down to bound `1` is the whole
  ε-jump, whose cost `φ_1(α)` is not below `φ_1(β)` just because `α` is.  With
  Pohlers' *ordinal* addition the situation cannot arise, because `1 + ω = ω`.

  The natural sum agrees with ordinal addition exactly when every Veblen term of
  `ρ` is at least `ω^ξ`, i.e. when `ρ` is a multiple of `ω^ξ`; that is
  `Gamma0Note.PowClosed ξ ρ`, and it is the hypothesis carried here.  It costs
  nothing: `PowClosed ξ 0` holds for every `ξ`, so the theorem in the form it is
  used — `⊢^α_{ω^ξ} Γ ⇒ ⊢^{φ_ξ(α)}_0 Γ`, `predicativeCut_veblen` — is
  unconditional, and the induction only ever moves `ρ` to `ρ ⊕ ω^η·m` with
  `η < ξ`, which preserves it.

  ## The shape of the induction

  All three cases go through one lemma of `RankSegments.lean`: the segment
  `[ρ, ρ ⊕ ω^ξ)` is exhausted from inside,

      a < ρ ⊕ ω^ξ  ⇒  ∃ d < ω^ξ, a < ρ ⊕ d      (`exists_lt_nadd_omegaPow`).

  Let `e` be the exponent of the leading term of that `d` (`leadExpNote`).  Then
  `d < ω^{e ⊕ 1}` and `e ⊕ 1 ≤ ξ`, and the case split is on which:

  * `ξ = 1` — `rankAbsorbed_of_chain`, with the finite chain produced by the same
    segment lemma (`d < ω` is a numeral, and `ρ ⊕ n` descends to `ρ` in `n`
    steps).
  * `e ⊕ 1 < ξ` — the induction hypothesis at level `e ⊕ 1`, lifted by
    `RankAbsorbed.mono_level`.  This is the *limit* case; note that it never
    mentions limits, and needs no syntactic predecessor of `ξ`.
  * `e ⊕ 1 = ξ` — then `ξ` is a successor *and its predecessor `e` has been
    handed to us by the syntax of `d`*.  This is the successor case: `d < ω^e·m`
    for some finite `m` (`exists_lt_omegaPowMul`), and the rank block
    `ρ ⊕ ω^e·m` descends to `ρ` by `m` applications of `predicativeCutElimination`
    at level `e` (`descend`), at a cost `φ_e^m(α)` that `φ_ξ(β)` absorbs because
    `φ_ξ(β)` is a fixed point of `φ_e`.
-/
import OrdinalAnalysis.Ramified.PredicativeCut
import OrdinalAnalysis.Ordinal.Veblen.RankSegments

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Derivation
open Gamma0Note

namespace OmegaDerivableR

variable {A : Literals LRA} {I : InstantiationR}

/-! ### Iterating a Veblen level -/

/-- The `m`-fold `φ_e`.  The recursion pushes the new application *inside*, exactly as
`OrdinalNotation.omegaTower` does, so that peeling one block of rank turns `α` into
`φ_e(α)` and leaves `m` blocks still to peel. -/
def veblenIter (e : Gamma0Note) : ℕ → Gamma0Note → Gamma0Note
  | 0, α => α
  | (m + 1), α => veblenIter e m (Gamma0Note.veblenStructure.veblen e α)

@[simp] theorem veblenIter_zero (e α : Gamma0Note) : veblenIter e 0 α = α := rfl

@[simp] theorem veblenIter_succ (e : Gamma0Note) (m : ℕ) (α : Gamma0Note) :
    veblenIter e (m + 1) α = veblenIter e m (Gamma0Note.veblenStructure.veblen e α) := rfl

/-- **`φ_ξ(β)` absorbs any finite iteration of a lower Veblen level**, because it is a fixed
point of `φ_e` for `e < ξ`. -/
theorem veblenIter_lt_veblen {e ξ : Gamma0Note} (hlt : e < ξ) (β : Gamma0Note) :
    ∀ (m : ℕ) (α : Gamma0Note), α < Gamma0Note.veblenStructure.veblen ξ β →
      veblenIter e m α < Gamma0Note.veblenStructure.veblen ξ β
  | 0, _, h => h
  | (m + 1), α, h => by
    refine veblenIter_lt_veblen hlt β m _ ?_
    have hfix : Gamma0Note.veblenStructure.veblen e
        (Gamma0Note.veblenStructure.veblen ξ β) = Gamma0Note.veblenStructure.veblen ξ β :=
      Gamma0Note.veblenStructure.veblen_veblen_of_lt hlt
    calc Gamma0Note.veblenStructure.veblen e α
        < Gamma0Note.veblenStructure.veblen e (Gamma0Note.veblenStructure.veblen ξ β) :=
          Gamma0Note.veblenStructure.veblen_lt_right h
      _ = Gamma0Note.veblenStructure.veblen ξ β := hfix

/-! ### The two easy `RankAbsorbed` instances -/

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- A segment that stays at or below `ρ` is absorbed for free: the derivation is already at
rank `ρ`. -/
theorem rankAbsorbed_of_le (V : VeblenStructure O) {ρ σ : Gamma0Note} {ξ : O}
    (h : σ ≤ Gamma0Note.nadd ρ 1) : RankAbsorbed A I ρ σ V ξ := by
  intro a ha α β Γ hα hd
  have hle : a ≤ ρ := Gamma0Note.lt_nadd_one_iff.mp (lt_of_lt_of_le ha h)
  rw [max_eq_left hle] at hd
  exact ⟨α, hα, hd⟩

/-! ### The finite chains below `ρ ⊕ ω` -/

/-- `ρ ⊕ n` is `n` predecessor-bound steps above `ρ`, and so is anything below it. -/
theorem chain_of_le_nadd_ofNat (ρ : Gamma0Note) :
    ∀ (n : ℕ) (a : Gamma0Note), a ≤ Gamma0Note.nadd ρ (Gamma0Note.ofNat n) →
      ∃ k : ℕ, Chain k ρ a
  | 0, a, h => by
    refine ⟨0, ?_⟩
    have h0 : (Gamma0Note.ofNat 0 : Gamma0Note) = 0 := Subtype.ext rfl
    rw [h0, Gamma0Note.nadd_zero] at h
    exact h
  | (n + 1), a, h => by
    obtain ⟨k, hk⟩ :=
      chain_of_le_nadd_ofNat ρ n (Gamma0Note.nadd ρ (Gamma0Note.ofNat n)) le_rfl
    refine ⟨k + 1, Gamma0Note.nadd ρ (Gamma0Note.ofNat n), ?_, hk⟩
    intro b hb
    have hb' : Gamma0Note.repr b < Gamma0Note.repr ρ + ((n + 1 : ℕ) : Ordinal) := by
      have hlt : b < Gamma0Note.nadd ρ (Gamma0Note.ofNat (n + 1)) := lt_of_lt_of_le hb h
      rw [Gamma0Note.lt_def, Gamma0Note.repr_nadd_ofNat] at hlt
      exact hlt
    rw [Gamma0Note.le_def, Gamma0Note.repr_nadd_ofNat]
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, ← Order.succ_eq_add_one,
      Order.lt_succ_iff] at hb'
    exact hb'

/-- **Every rank below `ρ ⊕ ω` is a finite chain above `ρ`** — provided `ρ` is a multiple of
`ω`.  This is `PredicativeCut.lean`'s `chain_of_lt_omegaPowLv_one` with the base `0`
generalised; the side condition is what stops `ρ = 1`, where `ρ ⊕ ω = ω + 1` contains the
limit rank `ω`. -/
theorem chain_of_lt_nadd_omegaPow_one {ρ : Gamma0Note} (hρ : PowClosed 1 ρ) (a : Gamma0Note)
    (ha : a < Gamma0Note.nadd ρ (Gamma0Note.omegaPow 1)) : ∃ k : ℕ, Chain k ρ a := by
  obtain ⟨d, hd, had⟩ := exists_lt_nadd_omegaPow Gamma0Note.zero_lt_one hρ ha
  have hdω : Gamma0Note.repr d < Ordinal.omega0 := by
    have h : Gamma0Note.repr d < Gamma0Note.repr (Gamma0Note.omegaPow 1) := hd
    rwa [Gamma0Note.repr_omegaPow, Gamma0Note.repr_one, Ordinal.opow_one] at h
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 hdω
  have hdn : d = Gamma0Note.ofNat n :=
    Gamma0Note.repr_injective (by rw [hn, Gamma0Note.repr_ofNat])
  rw [hdn] at had
  exact chain_of_le_nadd_ofNat ρ n a (le_of_lt had)

/-! ### The successor step: walking down a block `ρ ⊕ ω^e·m` -/

/-- **`m` applications of level-`e` predicative cut elimination.**  A derivation at rank
`ρ ⊕ ω^e·m` comes down to rank `ρ` at the cost of `m` applications of `φ_e`.

Each step peels one `ω^e` off the rank: `ρ ⊕ ω^e·(m+1) = (ρ ⊕ ω^e·m) ⊕ ω^e`, and the level-`e`
theorem applies at the base `ρ ⊕ ω^e·m`, which is again a multiple of `ω^e`
(`powClosed_nadd_omegaPowMul`). -/
theorem descend (hA : MemFree A) {e : Gamma0Note} (he : (1 : Gamma0Note) ≤ e)
    (hIH : ∀ ρ' : Gamma0Note, PowClosed e ρ' →
      RankAbsorbed A I ρ' (Gamma0Note.nadd ρ' (Gamma0Note.omegaPow e))
        Gamma0Note.veblenStructure e) :
    ∀ (m : ℕ) (ρ : Gamma0Note), PowClosed e ρ → ∀ {α : Gamma0Note} {Γ : Sequent LRA},
      OmegaDerivableR A I (Gamma0Note.nadd ρ (Gamma0Note.omegaPowMul e m)) α Γ →
        OmegaDerivableR A I ρ (veblenIter e m α) Γ := by
  intro m
  induction m with
  | zero =>
      intro ρ _ α Γ h
      rw [Gamma0Note.omegaPowMul_zero, Gamma0Note.nadd_zero] at h
      exact h
  | succ m ih =>
      intro ρ hρ α Γ h
      have hassoc : Gamma0Note.nadd ρ (Gamma0Note.omegaPowMul e (m + 1))
          = Gamma0Note.nadd (Gamma0Note.nadd ρ (Gamma0Note.omegaPowMul e m))
              (Gamma0Note.omegaPow e) := by
        rw [Gamma0Note.omegaPowMul_succ, Gamma0Note.nadd_assoc]
      rw [hassoc] at h
      have hpc : PowClosed e (Gamma0Note.nadd ρ (Gamma0Note.omegaPowMul e m)) :=
        (powClosed_nadd_omegaPowMul hρ m).1
      have h' := predicativeCutElimination hA Gamma0Note.veblenStructure he (hIH _ hpc) h
      exact ih ρ hρ h'

/-! ### The main induction -/

/-- **The rank segment `[ρ, ρ ⊕ ω^ξ)` is absorbed by `φ_ξ`, for every `ξ ≥ 1`.**

Pohlers' main induction on `ξ`, and the last thing `Ramified/PredicativeCut.lean` was
missing.  `PowClosed ξ ρ` — `ρ` is a multiple of `ω^ξ` — is the side condition without which
the statement is false for the *natural* sum; it holds of `ρ = 0`, and the induction
preserves it.

The three cases are `ξ = 1` (finite chains), `e ⊕ 1 < ξ` (the induction hypothesis lifted by
`mono_level`) and `e ⊕ 1 = ξ` (the finite descent `descend`), where `e` is the exponent of
the leading term of the witness `d` supplied by `exists_lt_nadd_omegaPow`. -/
theorem rankAbsorbed_powClosed (hA : MemFree A) (ξ : Gamma0Note) (hξ : (1 : Gamma0Note) ≤ ξ)
    (ρ : Gamma0Note) (hρ : PowClosed ξ ρ) :
    RankAbsorbed A I ρ (Gamma0Note.nadd ρ (Gamma0Note.omegaPow ξ))
      Gamma0Note.veblenStructure ξ := by
  by_cases hbase : ξ = 1
  · subst hbase
    exact rankAbsorbed_of_chain hA Gamma0Note.veblenStructure
      (chain_of_lt_nadd_omegaPow_one hρ)
  · have h1ξ : (1 : Gamma0Note) < ξ := lt_of_le_of_ne hξ (Ne.symm hbase)
    have hξ0 : (0 : Gamma0Note) < ξ := lt_trans Gamma0Note.zero_lt_one h1ξ
    intro a ha α β Γ hα hd
    rcases le_or_gt a ρ with hle | hgt
    · exact ⟨α, hα, by rwa [max_eq_left hle] at hd⟩
    · obtain ⟨d, hdlt, had⟩ := exists_lt_nadd_omegaPow hξ0 hρ ha
      have he : leadExpNote d < ξ := leadExpNote_lt_of_lt_omegaPow hξ0 hdlt
      have hdE : d < Gamma0Note.omegaPow (Gamma0Note.nadd (leadExpNote d) 1) :=
        lt_omegaPow_leadExp_succ d
      have hEle : Gamma0Note.nadd (leadExpNote d) 1 ≤ ξ := nadd_one_le_of_lt he
      rcases lt_or_eq_of_le hEle with hElt | hEeq
      · -- the induction hypothesis already covers the level `e ⊕ 1`
        have hIH := rankAbsorbed_powClosed hA (Gamma0Note.nadd (leadExpNote d) 1)
          (one_le_nadd_one (leadExpNote d)) ρ (hρ.mono hEle)
        have hlift :=
          RankAbsorbed.mono_level (A := A) (I := I) Gamma0Note.veblenStructure hElt hIH
        have haa : a < Gamma0Note.nadd ρ
            (Gamma0Note.omegaPow (Gamma0Note.nadd (leadExpNote d) 1)) :=
          lt_trans had (Gamma0Note.nadd_lt_nadd_right ρ hdE)
        exact hlift a haa hα hd
      · -- `ξ` is the successor of `e`, and `e` came out of the syntax of `d`
        have hepos : (0 : Gamma0Note) < leadExpNote d := by
          by_contra hcon
          have h0 : leadExpNote d = 0 := le_antisymm (not_lt.1 hcon) (by
            rw [Gamma0Note.le_def, Gamma0Note.repr_zero]
            exact zero_le)
          rw [h0, Gamma0Note.zero_nadd] at hEeq
          exact hbase hEeq.symm
        have h1e : (1 : Gamma0Note) ≤ leadExpNote d := by
          rw [Gamma0Note.le_def, Gamma0Note.repr_one]
          have hp : (0 : Ordinal) < Gamma0Note.repr (leadExpNote d) := by
            simpa using Gamma0Note.lt_def.mp hepos
          simpa using Order.add_one_le_iff.2 hp
        obtain ⟨m, hm⟩ := exists_lt_omegaPowMul hdE
        have hlt : a < Gamma0Note.nadd ρ (Gamma0Note.omegaPowMul (leadExpNote d) m) :=
          lt_trans had (Gamma0Note.nadd_lt_nadd_right ρ hm)
        have hmax : max ρ a = a := max_eq_right (le_of_lt hgt)
        rw [hmax] at hd
        have hd' := hd.mono_rank (le_of_lt hlt)
        refine ⟨veblenIter (leadExpNote d) m α, veblenIter_lt_veblen he β m α hα, ?_⟩
        exact descend hA h1e
          (fun ρ' hpc => rankAbsorbed_powClosed hA (leadExpNote d) h1e ρ' hpc) m ρ
          (hρ.mono (le_of_lt he)) hd'
termination_by ξ
decreasing_by
  · exact hElt
  · exact he

/-! ### The theorem -/

/-- **Predicative cut elimination, at every level.**

    ⊢^α_{ρ ⊕ ω^ξ} Γ   ⇒   ⊢^{φ_ξ(α)}_ρ Γ,     for `ξ ≥ 1` and `ρ` a multiple of `ω^ξ`.

This is Pohlers' theorem for the ramified calculus, with the side condition the *natural*
sum forces (see the module docstring).  `PredicativeCut.lean`'s
`predicativeCutStatement_of_absorbed` is exactly this statement minus `PowClosed`; it cannot
be discharged, and the module docstring of this file says why. -/
theorem predicativeCut_powClosed (hA : MemFree A) {ρ ξ : Gamma0Note}
    (hξ : (1 : Gamma0Note) ≤ ξ) (hρ : PowClosed ξ ρ) {α : Gamma0Note} {Γ : Sequent LRA}
    (h : OmegaDerivableR A I (Gamma0Note.nadd ρ (Gamma0Note.omegaPow ξ)) α Γ) :
    OmegaDerivableR A I ρ (Gamma0Note.veblenStructure.veblen ξ α) Γ :=
  predicativeCutElimination hA Gamma0Note.veblenStructure hξ
    (rankAbsorbed_powClosed hA ξ hξ ρ hρ) h

/-- **The cut-free form**, which is the one the ordinal analysis uses:

    ⊢^α_{ω^ξ} Γ   ⇒   ⊢^{φ_ξ(α)}_0 Γ.

No side condition survives: `ρ = 0` is a multiple of every `ω^ξ`.  At `ξ = 1` this is
`PredicativeCut.lean`'s `secondCutEliminationR`, the ε-jump; at `ξ = ν` it is the level-`ν`
fragment of the ramified hierarchy, costing `α ↦ φ_ν(α)`. -/
theorem predicativeCut_veblen (hA : MemFree A) {ξ : Gamma0Note} (hξ : (1 : Gamma0Note) ≤ ξ)
    {α : Gamma0Note} {Γ : Sequent LRA}
    (h : OmegaDerivableR A I (Gamma0Note.omegaPow ξ) α Γ) :
    OmegaDerivableR A I 0 (Gamma0Note.veblenStructure.veblen ξ α) Γ := by
  refine predicativeCut_powClosed hA hξ (powClosed_zero ξ) ?_
  rwa [Gamma0Note.zero_nadd]

/-- `φ_ξ` on `Gamma0Note` is `veblenNote ξ`, so the cut-free form reads
`⊢^α_{ω^ξ} Γ ⇒ ⊢^{φ_ξ(α)}_0 Γ` with `φ` the Veblen function of
`Ordinal/Veblen/Gamma0Note.lean`. -/
theorem predicativeCut_veblenNote (hA : MemFree A) {ξ : Gamma0Note}
    (hξ : (1 : Gamma0Note) ≤ ξ) {α : Gamma0Note} {Γ : Sequent LRA}
    (h : OmegaDerivableR A I (Gamma0Note.omegaPow ξ) α Γ) :
    OmegaDerivableR A I 0 (Gamma0Note.veblenNote ξ α) Γ :=
  predicativeCut_veblen hA hξ h

/-- **The general theorem, packaged as `PredicativeCut.lean`'s `PredicativeCutStatement` is**,
with the one side condition the natural sum forces.

`PredicativeCutStatement` itself — the same statement with `PowClosed ξ ρ` dropped — is *not*
provable; the module docstring gives the obstruction at `ρ = 1`, `ξ = 1`.  Everything that
statement is used for is `ρ = 0`, where `PowClosed` is free (`predicativeCut_veblen`). -/
def PredicativeCutStatementPowClosed (A : Literals LRA) (I : InstantiationR) : Prop :=
  ∀ (ρ ξ : Gamma0Note), OrdinalNotation.one ≤ ξ → PowClosed ξ ρ →
    ∀ {α : Gamma0Note} {Γ : Sequent LRA},
      OmegaDerivableR A I (OrdinalNotation.nadd ρ (OrdinalNotation.omegaPow ξ)) α Γ →
        OmegaDerivableR A I ρ (Gamma0Note.veblenStructure.veblen ξ α) Γ

/-- **Predicative cut elimination for the ramified calculus, in full.**  This is what
`PredicativeCut.lean`'s `predicativeCutStatement_of_absorbed` was waiting for; the hypothesis
it asks for is `rankAbsorbed_powClosed`, which holds for every `ρ` that is a multiple of
`ω^ξ`. -/
theorem predicativeCutStatement_powClosed (hA : MemFree A) :
    PredicativeCutStatementPowClosed A I := by
  intro ρ ξ hξ hρ α Γ h
  exact predicativeCut_powClosed hA hξ hρ h

/-- **Rank bookkeeping above a block**, as `cutElimination_epsilonR` does at `ξ = 1`: a rank
`ρ'` reached from `ω^ξ` by `k` predecessor-bound steps is eliminated at height
`φ_ξ(ω_k(α))`. -/
theorem cutElimination_veblen (hA : MemFree A) {ξ : Gamma0Note} (hξ : (1 : Gamma0Note) ≤ ξ)
    {k : ℕ} {ρ' : Gamma0Note} (hch : Chain k (Gamma0Note.omegaPow ξ) ρ')
    {α : Gamma0Note} {Γ : Sequent LRA} (h : OmegaDerivableR A I ρ' α Γ) :
    OmegaDerivableR A I 0
      (Gamma0Note.veblenStructure.veblen ξ (OrdinalNotation.omegaTower k α)) Γ :=
  predicativeCut_veblen hA hξ (cutElimination_chain hA k hch h)

end OmegaDerivableR

end Ramified

end OrdinalAnalysis
