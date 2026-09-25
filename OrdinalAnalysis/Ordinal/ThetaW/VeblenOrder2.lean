/-
  Buchholz's `φ.4`: the mixed comparison for the multi-level Veblen function `φ_k`
  (`ThetaW/Veblen.lean`), under the domain regime `ρ, ρ', β, β' ≺ Ω_{k+1}` (`dom_phi_of_lt`).

  Source: W. Buchholz, *A simplified version of local predicativity*, in *Proof Theory* (Aczel,
  Simmons, Wainer eds.), CUP 1992, §1, the `φ`-hierarchy axioms (φ.1)–(φ.4); the shape quoted
  here is `φ.4`: for `ξ < ξ'`, `η < φ_{ξ'}(η') → φ_ξ(η) < φ_{ξ'}(η')` (equivalently, via `φ.2`/
  `φ.3` of `ThetaW/VeblenOrder.lean`, the fact that makes `φ_ξ(η) < φ_{ξ'}(η')` decidable from
  `ξ < ξ'` alone once `η` is known to be small enough). W. Pohlers, *Subsystems of Set Theory and
  Second Order Number Theory*, in *Handbook of Proof Theory*, North-Holland 1998, §3.4, states
  the same clause for the (two-argument) Veblen functions on ordinals. Both sources state it for
  ordinals directly; here `φ_ξ(η)` is Freund's/this repo's *syntactic* `φ_k(ρ,β) :=
  ϑ_k(Ω_{k+1}·ρ+β)` one level up (`ThetaW/Veblen.lean`'s module docstring), so `ξ < ξ'` becomes
  `ρ < ρ'` and `η < φ_{ξ'}(η')` becomes `β.1 < φ_k ρ' β'` (`phi` returns a raw `ThetaWTerm`, not
  a bundled `ThetaWNoteD`, exactly as in `lt_phi_of_lt`, `ThetaW/VeblenOrder.lean`).

  the design notes's "blocked lemma" section worked out two routes to close
  this, both stalling on `harg : phiArg k rho beta < phiArg k rho' beta'` (the argument-level
  form of the inequality, which then closes exactly as `phi_lt_phi_right`'s proof does via
  `theta_lt_theta_iff`/`E_phiArg_eq_of_lt`, only with `rho`/`rho'` now different):
  * Route A needed the *equality* `φ_k(ρ, φ_k(ρ',β')) = φ_k(ρ',β')` (harder than the inequality
    actually wanted);
  * Route B needed a "successor gap" fact `omegaMulOmega k ρ + Ω_{k+1} ≤ omegaMulOmega k ρ'`,
    for which the notes flagged a missing discreteness lemma `a < b → succ a ≤ b` (now proved,
    `ArithSucc.lean`).

  Neither route is taken below. `harg` instead follows from a *direct* argument-list comparison
  that needs no successor-gap fact at all: `omegaMulOmega_lt_omegaMulOmega` already turns `ρ <
  ρ'` into `sum (omegaMulOmega k ρ).entries < sum (omegaMulOmega k ρ').entries`, and appending
  `β`'s / `β'`'s entries (all `≺ Ω_{k+1}`) to two lists whose *comparison* is already decided,
  where every entry appended to the larger list dominates every entry appended to the smaller one
  (`Omega_le_omegaAdd_of_lt`), cannot flip a strict lexicographic comparison
  (`sum_append_lt_sum_append_of_lt_of_forall_lt` below, by induction on the exponent lists,
  mirroring `ThetaW/Basic.lean`'s `cons_lt_cons_iff` case split exactly as `ArithSucc.lean`'s
  discreteness lemma does). This closes `harg` unconditionally from `ρ < ρ'` alone, without
  needing to know how big a "gap" `omegaMulOmega k ρ'` opens up over `omegaMulOmega k ρ` — so
  the discreteness lemma, while proved (`ArithSucc.lean`, as requested), turns out not to be on
  the critical path for `φ.4` after all.
-/
import OrdinalAnalysis.Ordinal.ThetaW.VeblenOrder

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

/-! ### Appending a dominated tail cannot flip a decided lexicographic comparison -/

/-- If `sum A ≺ sum A'` is already decided, and every entry of `A'` dominates every entry of `B`,
then appending `B` to `A` and (anything) `B'` to `A'` preserves the strict comparison: `sum (A ++
B) ≺ sum (A' ++ B')`. Induction on `A` (generalizing `A'`), the same case split as
`cons_lt_cons_iff`/`ArithSucc.lean`'s `sum_append_nil_le_of_lt`: whenever the comparison is
decided by a difference within the common length of `A`/`A'`, the tails `B`/`B'` are never
examined; whenever `A` runs out first (forcing `A'` to continue, which is the only way `sum A ≺
sum A'` can hold once `A`'s entries are exhausted), the appended `B` competes against `A'`'s
next entry, which dominates every entry of `B` by hypothesis. -/
theorem sum_append_lt_sum_append_of_lt_of_forall_lt :
    ∀ {A : List ThetaWTerm} (A' B B' : List ThetaWTerm), sum A < sum A' →
      (∀ x ∈ A', ∀ y ∈ B, y < x) → sum (A ++ B) < sum (A' ++ B')
  | [], A', B, B', hA, hbound => by
      cases A' with
      | nil => exact absurd hA not_nil_lt_nil
      | cons x xs =>
        cases B with
        | nil => exact nil_lt_cons _ _
        | cons y ys =>
          have hyx : y < x := hbound x List.mem_cons_self y List.mem_cons_self
          exact (cons_lt_cons_iff _ _ _ _).mpr (Or.inl hyx)
  | a :: as, A', B, B', hA, hbound => by
      cases A' with
      | nil => exact absurd hA (not_cons_lt_nil a as)
      | cons x xs =>
        show sum (a :: (as ++ B)) < sum (x :: (xs ++ B'))
        rcases (cons_lt_cons_iff _ _ _ _).mp hA with hax | ⟨rfl, hA'⟩
        · exact (cons_lt_cons_iff _ _ _ _).mpr (Or.inl hax)
        · refine (cons_lt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, ?_⟩)
          exact sum_append_lt_sum_append_of_lt_of_forall_lt xs B B' hA'
            (fun x' hx' y hy => hbound x' (List.mem_cons_of_mem _ hx') y hy)

end ThetaWTerm

namespace ThetaWNoteD

open ThetaWTerm

/-! ### The entries (not just `E_k`) of `φ_k`'s argument -/

/-- The term-level counterpart of `E_phiArg_eq_of_lt` (`ThetaW/VeblenOrder.lean`): the raw
exponent list of `Ω_{k+1}·ρ + β` splits as the concatenation of `Ω_{k+1}·ρ`'s and `β`'s, for
`ρ, β ≺ Ω_{k+1}`. Same argument as the `hentries` step inside `E_phiArg_eq_of_lt`'s proof
(every entry of `Ω_{k+1}·ρ` is `≽ Ω_{k+1} ≻` every entry of `β`, so `addL` cannot merge across
the two parts), extracted here as its own lemma since `phi_lt_phi_of_lt_left` needs it for two
different `(ρ, β)` pairs. -/
theorem entries_phiArg_eq_of_lt {k : ℕ} {rho beta : ThetaWNoteD} (hrho : rho < Omega k)
    (hbeta : beta < Omega k) :
    (phiArg k rho beta).entries = (omegaMulOmega k rho).entries ++ beta.entries := by
  have hrho' : ∀ e ∈ rho.entries, e < (ThetaWTerm.Omega k) := (lt_prin_iff (isPrin_Omega k)).mp hrho
  have hbeta' : ∀ e ∈ beta.entries, e < (ThetaWTerm.Omega k) :=
    (lt_prin_iff (isPrin_Omega k)).mp hbeta
  show (omegaMulOmega k rho + beta).entries = _
  rw [entries_add]
  refine addL_append_of_forall_le fun x hx y hy => ?_
  have hx' : ThetaWTerm.Omega k ≤ x := by
    rw [entries_omegaMulOmega] at hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact Omega_le_omegaAdd_of_lt (hrho' e he)
  exact le_trans' (le_of_lt' (hbeta' y hy)) hx'

/-! ### `φ_k` order preservation, `ρ`-and-`β` mixed comparison -/

/-- **`φ.4`: the mixed comparison** (Buchholz 1992 §1; Pohlers 1998, *Handbook of Proof Theory*
§3.4): if `ρ ≺ ρ'` and `β` is already below `φ_k(ρ',β')`, then `φ_k(ρ,β) ≺ φ_k(ρ',β')`. -/
theorem phi_lt_phi_of_lt_left {k : ℕ} {rho rho' beta beta' : ThetaWNoteD}
    (hrho : rho < Omega k) (hrho' : rho' < Omega k) (hbeta : beta < Omega k)
    (hbeta' : beta' < Omega k) (hlt : rho < rho') (hb : beta.1 < phi k rho' beta') :
    phi k rho beta < phi k rho' beta' := by
  have hrho'' : ∀ e ∈ rho'.entries, e < (ThetaWTerm.Omega k) := (lt_prin_iff (isPrin_Omega k)).mp hrho'
  have hbeta'' : ∀ e ∈ beta.entries, e < (ThetaWTerm.Omega k) :=
    (lt_prin_iff (isPrin_Omega k)).mp hbeta
  have hbound : ∀ x ∈ (omegaMulOmega k rho').entries, ∀ y ∈ beta.entries, y < x := by
    intro x hx y hy
    rw [entries_omegaMulOmega] at hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact lt_of_lt_of_le' (hbeta'' y hy) (Omega_le_omegaAdd_of_lt (hrho'' e he))
  have hsum : sum ((omegaMulOmega k rho).entries ++ beta.entries) <
      sum ((omegaMulOmega k rho').entries ++ beta'.entries) :=
    ThetaWTerm.sum_append_lt_sum_append_of_lt_of_forall_lt _ _ _
      (lt_iff_entries.mp (omegaMulOmega_lt_omegaMulOmega hlt)) hbound
  rw [← entries_phiArg_eq_of_lt hrho hbeta, ← entries_phiArg_eq_of_lt hrho' hbeta'] at hsum
  have harg : phiArg k rho beta < phiArg k rho' beta' := lt_iff_entries.mpr hsum
  unfold phi
  refine (theta_lt_theta_iff k _ _).mpr (Or.inl ⟨harg, fun g hg => ?_⟩)
  rw [E_phiArg_eq_of_lt hrho hbeta, List.mem_append] at hg
  rcases hg with hg | hg
  · -- `g` comes from `E_k(ρ)`: bounded via `ρ ≺ ρ'` and `exists_mem_E_of_theta_le` at `ρ'`.
    obtain ⟨j, δ, hjk, rfl⟩ := exists_eq_theta_of_mem_E hg
    rcases hjk.lt_or_eq with hj | hj
    · exact theta_lt_theta_of_lt_level δ (phiArg k rho' beta').1 hj
    · rw [hj] at hg ⊢
      have hle : theta k δ ≤ rho.1 := le_of_mem_E rho.2.1 hg
      have hlt2 : theta k δ ≤ rho'.1 := le_of_lt' (lt_of_le_of_lt' hle hlt)
      obtain ⟨g', hg', hg'le⟩ := exists_mem_E_of_theta_le δ hrho' hlt2
      refine theta_lt_theta_of_le_mem_E ?_ hg'le
      rw [E_phiArg_eq_of_lt hrho' hbeta']
      exact List.mem_append_left _ hg'
  · -- `g` comes from `E_k(β)`: bounded directly via `hb`.
    obtain ⟨j, δ, hjk, rfl⟩ := exists_eq_theta_of_mem_E hg
    rcases hjk.lt_or_eq with hj | hj
    · exact theta_lt_theta_of_lt_level δ (phiArg k rho' beta').1 hj
    · rw [hj] at hg ⊢
      have hle : theta k δ ≤ beta.1 := le_of_mem_E beta.2.1 hg
      exact lt_of_le_of_lt' hle hb

/-! ### `φ_k` order preservation, normality (`φ.1`) -/

/-- **`φ.1`: normality**, the input-to-output bound `β ≼ φ_k(ρ,β)` that the predicative
cut-elimination step also consumes (Buchholz 1992 §1's `φ`-hierarchy axioms; here the strict form
`β ≺ φ_k(ρ,β)` on the domain `ρ, β ≺ Ω_{k+1}`, which is what actually holds — even at `β = 0`,
since `ϑ_k` never produces `0` (`ThetaW/Basic.lean`'s `nil_lt_theta`), so there is no need for a
separate `≤` statement). Route: every `g ∈ E_k(β)` is also in `E_k(Ω_{k+1}·ρ+β)`
(`E_phiArg_eq_of_lt`, since `E_k(β)` is literally one of the two halves of the split), hence `g ≺
φ_k(ρ,β)` (`lt_theta_of_mem_E`, unconditional: every element of `E_k(α)` is below `ϑ_k α`); and
`β` itself, built from these `E_k`-pieces by `+`/`ω^·` (which `ϑ_k`-values absorb, being
principal), is then below `φ_k(ρ,β)` too by the packaged induction `forall_E_lt_theta_iff`
(`ThetaW/Order.lean`, Exercise 3.2(c) at level `k`) — the same fact
`phi_lt_phi_right`/`phi_lt_phi_of_lt_left` build their own coefficient-wise bounds out of, just
applied to `β` as the *whole* term instead of one `E_k`-member at a time. -/
theorem lt_phi_right_self {k : ℕ} {rho beta : ThetaWNoteD} (hrho : rho < Omega k)
    (hbeta : beta < Omega k) : beta.1 < phi k rho beta := by
  unfold phi
  refine (forall_E_lt_theta_iff (phiArg k rho beta).1 beta.2.1 hbeta).mp fun g hg => ?_
  refine lt_theta_of_mem_E ?_
  rw [E_phiArg_eq_of_lt hrho hbeta]
  exact List.mem_append_right _ hg

end ThetaWNoteD

end OrdinalAnalysis
