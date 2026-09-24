/-
  Cut elimination for cut ranks other than `Ω`, and Corollary 7.2.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Exercise 7.1 (c) and Corollary 7.2, with
  Exercise 7.1 (b) (reduction), Theorem 6.7 (collapsing) and the function `ω(α)` of §5.

  **Exercise 7.1 (c).**  For a nice operator `H` and `ρ ≠ Ω`,

      H ⊢^α_{ρ+1} Γ   ⇒   H ⊢^{ω(α)}_ρ Γ.

  The proof is by induction on the derivation.  Every clause is repeated at the height
  `ω(α)`, with the premises of heights `ω(α₀) ≺ ω(α)`; the side conditions `γ ≺ α` and
  `Ω ⪯ α` persist since `α ⪯ ω(α)`.  A cut of rank `≺ ρ` stays a cut.  A cut of rank `ρ`
  (a cut formula of rank `≺ ρ + 1` has rank `⪯ ρ`) is removed by the reduction lemma,
  Exercise 7.1 (b), at the height `ω(α₀) + ω(α₀) ≺ ω(α)`.  Iterating, `H ⊢^α_{ρ+n} Γ`
  gives `H ⊢^{ω_n(α)}_ρ Γ` when none of `ρ, …, ρ + n - 1` is `Ω`, where `ω₀(α) = α` and
  `ω_{k+1}(α) = ω(ω_k(α))`.

  **Corollary 7.2.**  Freund's proof: the embedding (Theorem 6.5) gives `H_0 ⊢^β_{Ω+m} ψ⁺`;
  iterated applications of Exercise 7.1 (c) reduce the rank to `Ω + 1`; collapsing
  (Theorem 6.7) gives `H_η ⊢^{ϑη}_{ϑη} ψ⁺` for `η = ω(β')`.  Here the embedded derivation is
  the hypothesis, and the ordinals are explicit: from `H_0 ⊢^β_{Ω+(m+1)} Γ`, `Γ` a
  `Σ(Ω)`-sequent, Exercise 7.1 (c) applied `m` times gives `H_0 ⊢^{ω_m(β)}_{Ω+1} Γ`, and
  collapsing gives

      H_η ⊢^{ϑη}_{ϑη} Γ    for    η = ω_{m+1}(β).

  Every notation lies below some `ω_n(Ω + 1)`, so `η ≺ ω_k(Ω + 1)` for some `k`, and since
  `η ∈ H_0(∅)` (Proposition 3.11 (c)) the height and the cut rank `ϑη` lie below
  `ϑ(ω_k(Ω + 1))`: below the Bachmann–Howard ordinal, the supremum of these notations.

  The collapsed derivation still has cuts, of rank `ϑη ≺ Ω`.  Exercise 7.1 (c) lowers a cut
  rank `ρ + 1` to `ρ`, so it cannot reach cut rank `0` from the limit `ϑη`; this is done by
  predicative cut elimination (Theorem 7.8, Corollary 7.9), which is not part of
  Corollary 7.2.

  **Contents.**

    `IDerivable.elimination`        Exercise 7.1 (c)
    `IDerivable.elimination_iter`   Exercise 7.1 (c), iterated
    `collapsing_embedded`           Corollary 7.2, with `η = ω_{m+1}(β)`
    `theta_omegaTower_lt`           the bound `ϑη ≺ ϑ(ω_k(Ω + 1))`
    `corollary_7_2`                 Corollary 7.2, from cut rank `Ω + m`
-/
import OrdinalAnalysis.ID1.Reduction

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

open LO LO.FirstOrder

/-! ### Exercise 7.1 (c) -/

namespace IDerivable

variable {A : Semisentence LXI 1} {ρ : ThetaNote}

/-- **Exercise 7.1 (c), the induction** on the derivation. -/
theorem elim_aux (hρ : ρ ≠ ThetaNote.Omega) {H : Set ThetaNote → Set ThetaNote}
    {α : ThetaNote} {Γ : Sequent LIinf} (d : IDerivable A (ρ + ThetaNote.one) H α Γ) :
    ThetaNote.Nice H → IDerivable A ρ H (ThetaNote.omegaPow α) Γ := by
  induction d with
  | literal hα hΓ hφ hm => intro hH; exact .literal (hH.omegaPow_mem hα) hΓ hφ hm
  | verum hα hΓ hm => intro hH; exact .verum (hH.omegaPow_mem hα) hΓ hm
  | idX t hα hΓ h1 h2 => intro hH; exact .idX t (hH.omegaPow_mem hα) hΓ h1 h2
  | and hα hΓ hm h0 h1 _ _ ih0 ih1 =>
    intro hH
    exact .and (hH.omegaPow_mem hα) hΓ hm (ThetaNote.omegaPow_lt_omegaPow h0)
      (ThetaNote.omegaPow_lt_omegaPow h1) (ih0 hH) (ih1 hH)
  | orL hα hΓ hm h0 _ ih =>
    intro hH
    exact .orL (hH.omegaPow_mem hα) hΓ hm (ThetaNote.omegaPow_lt_omegaPow h0) (ih hH)
  | orR hα hΓ hm h1 h0 _ ih =>
    intro hH
    exact .orR (hH.omegaPow_mem hα) hΓ hm (lt_of_lt_of_le h1 (ThetaNote.le_omegaPow_red _))
      (ThetaNote.omegaPow_lt_omegaPow h0) (ih hH)
  | all f hα hΓ hm hf _ ih =>
    intro hH
    exact .all (fun n => ThetaNote.omegaPow (f n)) (hH.omegaPow_mem hα) hΓ hm
      (fun n => ThetaNote.omegaPow_lt_omegaPow (hf n)) fun n => ih n hH
  | exs n hα hΓ hm hn h0 _ ih =>
    intro hH
    exact .exs n (hH.omegaPow_mem hα) hΓ hm (lt_of_lt_of_le hn (ThetaNote.le_omegaPow_red _))
      (ThetaNote.omegaPow_lt_omegaPow h0) (ih hH)
  | stage g hα hΓ hm hga hgα hgH h0 _ ih =>
    intro hH
    exact .stage g (hH.omegaPow_mem hα) hΓ hm hga
      (lt_of_lt_of_le hgα (ThetaNote.le_omegaPow_red _)) hgH
      (ThetaNote.omegaPow_lt_omegaPow h0) (ih hH)
  | nstage f hα hΓ hm hf _ ih =>
    intro hH
    exact .nstage (fun g => ThetaNote.omegaPow (f g)) (hH.omegaPow_mem hα) hΓ hm
      (fun g hg => ThetaNote.omegaPow_lt_omegaPow (hf g hg)) fun g hg =>
        ih g hg (hH.adjoin {g.1})
  | fix hα hΓ hm hΩ h0 _ ih =>
    intro hH
    exact .fix (hH.omegaPow_mem hα) hΓ hm (le_trans hΩ (ThetaNote.le_omegaPow_red _))
      (ThetaNote.omegaPow_lt_omegaPow h0) (ih hH)
  | cut hα hΓ hr h0 _ _ ih0 ih1 =>
    intro hH
    rcases lt_or_eq_of_le (ThetaNote.le_of_lt_add_one_red hr) with hlt | heq
    · exact .cut (hH.omegaPow_mem hα) hΓ hlt (ThetaNote.omegaPow_lt_omegaPow h0) (ih0 hH)
        (ih1 hH)
    · exact (reduction_cut hH heq hρ (ih0 hH) (ih1 hH)).mono_height
        (le_of_lt (ThetaNote.omegaPow_add_omegaPow_lt_red h0)) (hH.omegaPow_mem hα)

/-- **Freund, Exercise 7.1 (c) (Cut elimination)**: for a nice operator `H` and `ρ ≠ Ω`,

    `H ⊢^α_{ρ+1} Γ` gives `H ⊢^{ω(α)}_ρ Γ`. -/
theorem elimination {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.Nice H)
    (hρ : ρ ≠ ThetaNote.Omega) {α : ThetaNote} {Γ : Sequent LIinf}
    (d : IDerivable A (ρ + ThetaNote.one) H α Γ) :
    IDerivable A ρ H (ThetaNote.omegaPow α) Γ :=
  elim_aux hρ d hH

/-- **Exercise 7.1 (c), iterated**: `H ⊢^α_{ρ+n} Γ` gives `H ⊢^{ω_n(α)}_ρ Γ` when
`ρ + k ≠ Ω` for all `k ≺ n`. -/
theorem elimination_iter {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.Nice H) :
    ∀ (n : ℕ) {ρ α : ThetaNote} {Γ : Sequent LIinf},
      (∀ k < n, ρ + ThetaNote.ofNat k ≠ ThetaNote.Omega) →
      IDerivable A (ρ + ThetaNote.ofNat n) H α Γ →
      IDerivable A ρ H (ThetaNote.omegaTower n α) Γ
  | 0, ρ, α, Γ, _, d => by
    rw [ThetaNote.ofNat_zero, ThetaNote.add_zero] at d
    exact d
  | n + 1, ρ, α, Γ, hρ, d => by
    rw [ThetaNote.add_ofNat_succ_red] at d
    have d' := elimination hH (hρ n (Nat.lt_succ_self n)) d
    rw [ThetaNote.omegaTower_succ_red]
    exact elimination_iter hH n (fun k hk => hρ k (Nat.lt_succ_of_lt hk)) d'

end IDerivable

/-! ### Corollary 7.2 -/

section Corollary

variable {A : Semisentence LXI 1}

theorem Omega_add_ofNat_succ (m : ℕ) :
    ThetaNote.Omega + ThetaNote.ofNat (m + 1) =
      ThetaNote.Omega + ThetaNote.one + ThetaNote.ofNat m := by
  rw [ThetaNote.add_assoc, ← ThetaNote.ofNat_one, ThetaNote.ofNat_add_ofNat_red, Nat.add_comm]

/-- **Freund, Corollary 7.2, with the ordinals explicit**: for a positive operator form `A`
and a `Σ(Ω)`-sequent `Γ`,

    `H_0 ⊢^β_{Ω+(m+1)} Γ` gives `H_η ⊢^{ϑη}_{ϑη} Γ` for `η = ω_{m+1}(β)`.

Exercise 7.1 (c) is applied `m` times, to the ranks `Ω + m, …, Ω + 1`, and then
collapsing (Theorem 6.7). -/
theorem collapsing_embedded (hA : Positive A) {Γ : Sequent LIinf}
    (hΓ : ∀ φ ∈ Γ, SigmaOmega φ) (m : ℕ) {β : ThetaNote}
    (d : IDerivable A (ThetaNote.Omega + ThetaNote.ofNat (m + 1)) (ThetaNote.Hop ThetaNote.zero)
      β Γ) :
    IDerivable A (ThetaNote.theta (ThetaNote.omegaTower (m + 1) β))
      (ThetaNote.Hop (ThetaNote.omegaTower (m + 1) β))
      (ThetaNote.theta (ThetaNote.omegaTower (m + 1) β)) Γ := by
  rw [Omega_add_ofNat_succ] at d
  have hne : ∀ k < m, ThetaNote.Omega + ThetaNote.one + ThetaNote.ofNat k ≠ ThetaNote.Omega :=
    fun k _ => ne_of_gt (lt_of_lt_of_le ThetaNote.Omega_lt_Omega_add_one
      (ThetaNote.le_self_add_red _ _))
  exact collapsing_zero hA hΓ
    (IDerivable.elimination_iter (ThetaNote.Hop_nice ThetaNote.zero) m hne d)

/-- **The collapsed height lies below the Bachmann–Howard ordinal**: for `β ∈ H_0(∅)` and
`η = ω_{m+1}(β)` there is `k` with `η ≺ ω_k(Ω + 1)` and `ϑη ≺ ϑ(ω_k(Ω + 1))`. -/
theorem theta_omegaTower_lt {β : ThetaNote} (hβ : β ∈ ThetaNote.Hop ThetaNote.zero ∅)
    (m : ℕ) : ∃ k : ℕ,
      ThetaNote.omegaTower (m + 1) β < ThetaNote.omegaTower k (ThetaNote.Omega + ThetaNote.one) ∧
      ThetaNote.theta (ThetaNote.omegaTower (m + 1) β) <
        ThetaNote.theta (ThetaNote.omegaTower k (ThetaNote.Omega + ThetaNote.one)) := by
  obtain ⟨n, hn⟩ := ThetaNote.exists_lt_omegaTower β
  have hlt : ThetaNote.omegaTower (m + 1) β <
      ThetaNote.omegaTower (m + 1 + n) (ThetaNote.Omega + ThetaNote.one) := by
    rw [← ThetaNote.omegaTower_omegaTower_red (m + 1) n]
    exact ThetaNote.omegaTower_lt_omegaTower_red hn (m + 1)
  refine ⟨m + 1 + n, hlt, ?_⟩
  exact ThetaNote.theta_lt_theta_of_mem_Hop (X := ∅) (Set.empty_subset _)
    (ThetaNote.zero_le' _) hlt ((ThetaNote.Hop_nice _).omegaTower_mem_red hβ (m + 1))

/-- **Freund, Corollary 7.2**: for a positive operator form `A` and a `Σ(Ω)`-sequent `Γ`,
`H_0 ⊢^β_{Ω+m} Γ` gives `H_η ⊢^{ϑη}_{ϑη} Γ` for some `η`; here `η = ω_{m+1}(β)`, and the
height and cut rank `ϑη ≺ Ω` lie below `ϑ(ω_k(Ω + 1))` for some `k`, i.e. below the
Bachmann–Howard ordinal. -/
theorem corollary_7_2 (hA : Positive A) {Γ : Sequent LIinf} (hΓ : ∀ φ ∈ Γ, SigmaOmega φ)
    (m : ℕ) {β : ThetaNote}
    (d : IDerivable A (ThetaNote.Omega + ThetaNote.ofNat m) (ThetaNote.Hop ThetaNote.zero) β Γ) :
    ∃ k : ℕ,
      ThetaNote.omegaTower (m + 1) β < ThetaNote.omegaTower k (ThetaNote.Omega + ThetaNote.one) ∧
      ThetaNote.theta (ThetaNote.omegaTower (m + 1) β) <
        ThetaNote.theta (ThetaNote.omegaTower k (ThetaNote.Omega + ThetaNote.one)) ∧
      ThetaNote.theta (ThetaNote.omegaTower (m + 1) β) < ThetaNote.Omega ∧
      IDerivable A (ThetaNote.theta (ThetaNote.omegaTower (m + 1) β))
        (ThetaNote.Hop (ThetaNote.omegaTower (m + 1) β))
        (ThetaNote.theta (ThetaNote.omegaTower (m + 1) β)) Γ := by
  obtain ⟨k, h1, h2⟩ := theta_omegaTower_lt d.height_mem m
  refine ⟨k, h1, h2, ThetaNote.theta_lt_Omega _, collapsing_embedded hA hΓ m ?_⟩
  exact d.mono_rank (ThetaNote.add_le_add_left _
    (le_of_lt (ThetaNote.ofNat_lt_ofNat (Nat.lt_succ_self m))))

end Corollary

end InductiveDef

end OrdinalAnalysis
