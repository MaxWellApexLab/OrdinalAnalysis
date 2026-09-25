/- Source: OrdinalAnalysis\ID1\Elimination.lean (one-level `Omega`/`Stage` generalised to level `k : Fin n`). -/

import OrdinalAnalysis.IDn.Reduction
/-
  Cut elimination for cut ranks other than `Ω_k` (any level `k`), Freund's Exercise 7.1 (c).

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Exercise 7.1 (c), with Exercise 7.1 (b) (reduction).

  **Exercise 7.1 (c).**  For a nice operator `H` and `ρ ≠ Ω`,

      H ⊢^α_{ρ+1} Γ   ⇒   H ⊢^{ω(α)}_ρ Γ.

  The proof is by induction on the derivation.  Every clause is repeated at the height
  `ω(α)`, with the premises of heights `ω(α₀) ≺ ω(α)`; the side conditions `γ ≺ α` and
  `Ω ⪯ α` persist since `α ⪯ ω(α)`.  A cut of rank `≺ ρ` stays a cut.  A cut of rank `ρ`
  (a cut formula of rank `≺ ρ + 1` has rank `⪯ ρ`) is removed by the reduction lemma,
  Exercise 7.1 (b), at the height `ω(α₀) + ω(α₀) ≺ ω(α)`.  Iterating, `H ⊢^α_{ρ+m} Γ`
  gives `H ⊢^{ω_m(α)}_ρ Γ` when none of `ρ, …, ρ + m - 1` is any `Ω_k`, where `ω₀(α) = α`
  and `ω_{j+1}(α) = ω(ω_j(α))`.

  **Scope of this port.**  Freund's Corollary 7.2 (embedding + iterated Exercise 7.1 (c) +
  collapsing, giving `H_η ⊢^{ϑη}_{ϑη} ψ⁺`) is *not* ported here.  This file covers Exercise 7.1 (b),(c) only; the multi-level
  collapsing corollary is `IDn/Collapsing.lean`'s job (station C4, Buchholz Theorem 4.8, §2.4),
  a different statement (no `ω_m(Ω+1)`-indexed embedding search) that is not written yet.
  Dropped from the mechanical draft: `collapsing_embedded`, `theta_omegaTower_lt`,
  `corollary_7_2`, `Omega_add_ofNat_succ`. (The draft's own use of a bare `ThetaWNoteD.Omega`,
  with no level argument, in that section was also a mechanical-translation bug — `Omega` always
  takes a level `: ℕ` — so it could not have compiled as generated regardless of scope.)

  **The reduction lemma, two forms.**  `IDn/Reduction.lean` (merged) supplies
  `IDnDerivable.reduction_cut`, whose rank side condition is *stronger* than the one-level
  source's: `∀ k : Fin n, ρ ≠ Ω_k`, not just `ρ ≠ Ω_{n-1}` — every level has its own `(Fix)`
  clause, so a cut of rank `ρ = Ω_j` for *any* `j`, not only the top level, can be principal, and
  `reduction_cut` needs `FamilyLevelBounded A` on top of that (`red_aux`'s docstring: needed for
  the multi-level form of `rk_unfold_lt_stageAt`, absent from the one-level source since there is
  only one level to bound). Below:

  * `elim_aux`/`elimination`/`elimination_iter` are the **concrete** theorems, using
    `IDnDerivable.reduction_cut` directly, with its real (stronger) hypotheses
    `hAb : FamilyLevelBounded A` and `hρ : ∀ k, ρ ≠ Ω_k`. These are what the rest of the
    development should call.
  * `elim_aux_of_hredCut`/`elimination_of_hredCut`/`elimination_iter_of_hredCut` are the
    **original hypothesis-form** theorems from before the reduction files merged, kept because
    their rank side condition (`ρ ≠ Ω_{n-1}` only, the literal one-level reading) is *weaker*
    than what `reduction_cut` actually needs, so they are not simply subsumed: they still say
    something `reduction_cut`'s own statement does not, for anyone who has (or later proves) a
    reduction lemma at the weaker hypothesis.

  **Contents.**

    `IDnDerivable.elim_aux`, `.elimination`, `.elimination_iter`
                                    Exercise 7.1 (c), concrete (via `IDnDerivable.reduction_cut`)
    `IDnDerivable.elim_aux_of_hredCut`, `.elimination_of_hredCut`, `.elimination_iter_of_hredCut`
                                    the same, generic in an abstract reduction-lemma hypothesis
-/

set_option autoImplicit false

namespace OrdinalAnalysis
variable {n : ℕ} (k : Fin n)

namespace IDn

open LO LO.FirstOrder

/-! ### Exercise 7.1 (c) -/

namespace IDnDerivable

variable {A : Fin n → Semisentence (LXIn n) 1} {ρ : ThetaWNoteD}

/-- **Hypothesis**: the reduction lemma at cut rank `ρ` (Freund, Exercise 7.1 (b)), in the
literal one-level form (`ρ ≠ Ω_{n-1}` only), used by the `_of_hredCut` theorems below. Packaged
as a `def : Prop` (rather than a bare `variable`) so it can be threaded as an *explicit* parameter
of every theorem that needs it: a `variable` is only auto-included in a declaration whose own
*stated signature* mentions it, not one that merely uses it inside the proof term, so a bare
`variable (hredCut : ...)` here would silently disappear from `elim_aux_of_hredCut`'s signature
(its header never spells out `hredCut`) and leave the tactic proof unable to see it. -/
def ReductionCutHyp (A : Fin n → Semisentence (LXIn n) 1) (ρ : ThetaWNoteD) : Prop :=
  ∀ {H : Set ThetaWNoteD → Set ThetaWNoteD}, ThetaWNoteD.NiceS H →
    ∀ {ψ : Proposition (LIinfN n)}, rk ψ = ρ → ρ ≠ ThetaWNoteD.Omega (n - 1) →
    ∀ {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)},
      IDnDerivable A ρ H α (ψ :: Γ) → IDnDerivable A ρ H α (∼ψ :: Γ) →
      IDnDerivable A ρ H (α + α) Γ

/-- **Exercise 7.1 (c), the induction**, generic in the reduction-lemma hypothesis `hredCut`
(rank side condition `ρ ≠ Ω_{n-1}`, the literal one-level reading). -/
theorem elim_aux_of_hredCut (hredCut : ReductionCutHyp A ρ) (hρ : ρ ≠ (ThetaWNoteD.Omega (n - 1)))
    {H : Set ThetaWNoteD → Set ThetaWNoteD}
    {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)} (d : IDnDerivable A (ρ + ThetaWNoteD.one) H α Γ) :
    ThetaWNoteD.NiceS H → IDnDerivable A ρ H (ThetaWNoteD.omegaPow α) Γ := by
  induction d with
  | literal hα hΓ hφ hm => intro hH; exact .literal (hH.omegaPow_mem hα) hΓ hφ hm
  | verum hα hΓ hm => intro hH; exact .verum (hH.omegaPow_mem hα) hΓ hm
  | idX t hα hΓ h1 h2 => intro hH; exact .idX t (hH.omegaPow_mem hα) hΓ h1 h2
  | and hα hΓ hm h0 h1 _ _ ih0 ih1 =>
    intro hH
    exact .and (hH.omegaPow_mem hα) hΓ hm (ThetaWNoteD.omegaPow_lt_omegaPow h0)
      (ThetaWNoteD.omegaPow_lt_omegaPow h1) (ih0 hH) (ih1 hH)
  | orL hα hΓ hm h0 _ ih =>
    intro hH
    exact .orL (hH.omegaPow_mem hα) hΓ hm (ThetaWNoteD.omegaPow_lt_omegaPow h0) (ih hH)
  | orR hα hΓ hm h1 h0 _ ih =>
    intro hH
    exact .orR (hH.omegaPow_mem hα) hΓ hm (lt_of_lt_of_le h1 (ThetaWNoteD.le_omegaPow_red _))
      (ThetaWNoteD.omegaPow_lt_omegaPow h0) (ih hH)
  | all f hα hΓ hm hf _ ih =>
    intro hH
    exact .all (fun m => ThetaWNoteD.omegaPow (f m)) (hH.omegaPow_mem hα) hΓ hm
      (fun m => ThetaWNoteD.omegaPow_lt_omegaPow (hf m)) fun m => ih m hH
  | exs m hα hΓ hm hn h0 _ ih =>
    intro hH
    exact .exs m (hH.omegaPow_mem hα) hΓ hm (lt_of_lt_of_le hn (ThetaWNoteD.le_omegaPow_red _))
      (ThetaWNoteD.omegaPow_lt_omegaPow h0) (ih hH)
  | stage g hα hΓ hm hga hgα hgH h0 _ ih =>
    intro hH
    exact .stage g (hH.omegaPow_mem hα) hΓ hm hga
      (lt_of_lt_of_le hgα (ThetaWNoteD.le_omegaPow_red _)) hgH
      (ThetaWNoteD.omegaPow_lt_omegaPow h0) (ih hH)
  | nstage f hα hΓ hm hf _ ih =>
    intro hH
    exact .nstage (fun g => ThetaWNoteD.omegaPow (f g)) (hH.omegaPow_mem hα) hΓ hm
      (fun g hg => ThetaWNoteD.omegaPow_lt_omegaPow (hf g hg)) fun g hg =>
        ih g hg (hH.adjoin {g.1})
  | fix hα hΓ hm hΩ h0 _ ih =>
    intro hH
    exact .fix (hH.omegaPow_mem hα) hΓ hm (le_trans hΩ (ThetaWNoteD.le_omegaPow_red _))
      (ThetaWNoteD.omegaPow_lt_omegaPow h0) (ih hH)
  | cut hα hΓ hr h0 _ _ ih0 ih1 =>
    intro hH
    rcases lt_or_eq_of_le (ThetaWNoteD.le_of_lt_add_one_red hr) with hlt | heq
    · exact .cut (hH.omegaPow_mem hα) hΓ hlt (ThetaWNoteD.omegaPow_lt_omegaPow h0) (ih0 hH)
        (ih1 hH)
    · exact (hredCut hH heq hρ (ih0 hH) (ih1 hH)).mono_height
        (le_of_lt (ThetaWNoteD.omegaPow_add_omegaPow_lt_red h0)) (hH.omegaPow_mem hα)

/-- **Freund, Exercise 7.1 (c) (Cut elimination)**, generic form: for a nice operator `H` and
`ρ ≠ Ω_{n-1}`, `H ⊢^α_{ρ+1} Γ` gives `H ⊢^{ω(α)}_ρ Γ`. -/
theorem elimination_of_hredCut {H : Set ThetaWNoteD → Set ThetaWNoteD} (hredCut : ReductionCutHyp A ρ)
    (hH : ThetaWNoteD.NiceS H)
    (hρ : ρ ≠ (ThetaWNoteD.Omega (n - 1))) {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    (d : IDnDerivable A (ρ + ThetaWNoteD.one) H α Γ) :
    IDnDerivable A ρ H (ThetaWNoteD.omegaPow α) Γ :=
  elim_aux_of_hredCut hredCut hρ d hH

/-- **Exercise 7.1 (c), iterated**, generic form: `H ⊢^α_{ρ+m} Γ` gives `H ⊢^{ω_m(α)}_ρ Γ` when
`ρ + j ≠ Ω_{n-1}` for all `j ≺ m`. Takes `hredCut` at *every* rank `ρ'` the iteration passes
through (`ReductionCutHyp A ρ'`), since `A` alone does not determine `ρ`. -/
theorem elimination_iter_of_hredCut {H : Set ThetaWNoteD → Set ThetaWNoteD}
    (hredCut : ∀ ρ' : ThetaWNoteD, ReductionCutHyp A ρ') (hH : ThetaWNoteD.NiceS H) :
    ∀ (m : ℕ) {ρ α : ThetaWNoteD} {Γ : Sequent (LIinfN n)},
      (∀ j < m, ρ + ThetaWNoteD.ofNat j ≠ (ThetaWNoteD.Omega (n - 1))) →
      IDnDerivable A (ρ + ThetaWNoteD.ofNat m) H α Γ →
      IDnDerivable A ρ H (ThetaWNoteD.omegaTower m α) Γ
  | 0, ρ, α, Γ, _, d => by
    rw [ThetaWNoteD.ofNat_zero, ThetaWNoteD.add_zero] at d
    exact d
  | m + 1, ρ, α, Γ, hρ, d => by
    rw [ThetaWNoteD.add_ofNat_succ_red] at d
    have d' := elimination_of_hredCut (hredCut (ρ + ThetaWNoteD.ofNat m)) hH
      (hρ m (Nat.lt_succ_self m)) d
    rw [ThetaWNoteD.omegaTower_succ_red]
    exact elimination_iter_of_hredCut hredCut hH m (fun j hj => hρ j (Nat.lt_succ_of_lt hj)) d'

end IDnDerivable

/-! ### The concrete theorems, via the merged `IDnDerivable.reduction_cut` -/

namespace IDnDerivable

variable {A : Fin n → Semisentence (LXIn n) 1} {ρ : ThetaWNoteD}

/-- **Exercise 7.1 (c), the induction**, concrete: uses `IDnDerivable.reduction_cut` directly, so
the rank side condition is `reduction_cut`'s own, `∀ k, ρ ≠ Ω_k` (every level), not just the top
one, and there is the extra hypothesis `hAb : FamilyLevelBounded A` `reduction_cut` needs. -/
theorem elim_aux (hAb : FamilyLevelBounded A) (hρ : ∀ j : Fin n, ρ ≠ ThetaWNoteD.Omega j.val)
    {H : Set ThetaWNoteD → Set ThetaWNoteD}
    {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)} (d : IDnDerivable A (ρ + ThetaWNoteD.one) H α Γ) :
    ThetaWNoteD.NiceS H → IDnDerivable A ρ H (ThetaWNoteD.omegaPow α) Γ := by
  induction d with
  | literal hα hΓ hφ hm => intro hH; exact .literal (hH.omegaPow_mem hα) hΓ hφ hm
  | verum hα hΓ hm => intro hH; exact .verum (hH.omegaPow_mem hα) hΓ hm
  | idX t hα hΓ h1 h2 => intro hH; exact .idX t (hH.omegaPow_mem hα) hΓ h1 h2
  | and hα hΓ hm h0 h1 _ _ ih0 ih1 =>
    intro hH
    exact .and (hH.omegaPow_mem hα) hΓ hm (ThetaWNoteD.omegaPow_lt_omegaPow h0)
      (ThetaWNoteD.omegaPow_lt_omegaPow h1) (ih0 hH) (ih1 hH)
  | orL hα hΓ hm h0 _ ih =>
    intro hH
    exact .orL (hH.omegaPow_mem hα) hΓ hm (ThetaWNoteD.omegaPow_lt_omegaPow h0) (ih hH)
  | orR hα hΓ hm h1 h0 _ ih =>
    intro hH
    exact .orR (hH.omegaPow_mem hα) hΓ hm (lt_of_lt_of_le h1 (ThetaWNoteD.le_omegaPow_red _))
      (ThetaWNoteD.omegaPow_lt_omegaPow h0) (ih hH)
  | all f hα hΓ hm hf _ ih =>
    intro hH
    exact .all (fun m => ThetaWNoteD.omegaPow (f m)) (hH.omegaPow_mem hα) hΓ hm
      (fun m => ThetaWNoteD.omegaPow_lt_omegaPow (hf m)) fun m => ih m hH
  | exs m hα hΓ hm hn h0 _ ih =>
    intro hH
    exact .exs m (hH.omegaPow_mem hα) hΓ hm (lt_of_lt_of_le hn (ThetaWNoteD.le_omegaPow_red _))
      (ThetaWNoteD.omegaPow_lt_omegaPow h0) (ih hH)
  | stage g hα hΓ hm hga hgα hgH h0 _ ih =>
    intro hH
    exact .stage g (hH.omegaPow_mem hα) hΓ hm hga
      (lt_of_lt_of_le hgα (ThetaWNoteD.le_omegaPow_red _)) hgH
      (ThetaWNoteD.omegaPow_lt_omegaPow h0) (ih hH)
  | nstage f hα hΓ hm hf _ ih =>
    intro hH
    exact .nstage (fun g => ThetaWNoteD.omegaPow (f g)) (hH.omegaPow_mem hα) hΓ hm
      (fun g hg => ThetaWNoteD.omegaPow_lt_omegaPow (hf g hg)) fun g hg =>
        ih g hg (hH.adjoin {g.1})
  | fix hα hΓ hm hΩ h0 _ ih =>
    intro hH
    exact .fix (hH.omegaPow_mem hα) hΓ hm (le_trans hΩ (ThetaWNoteD.le_omegaPow_red _))
      (ThetaWNoteD.omegaPow_lt_omegaPow h0) (ih hH)
  | cut hα hΓ hr h0 _ _ ih0 ih1 =>
    intro hH
    rcases lt_or_eq_of_le (ThetaWNoteD.le_of_lt_add_one_red hr) with hlt | heq
    · exact .cut (hH.omegaPow_mem hα) hΓ hlt (ThetaWNoteD.omegaPow_lt_omegaPow h0) (ih0 hH)
        (ih1 hH)
    · exact (IDnDerivable.reduction_cut hH hAb heq hρ (ih0 hH) (ih1 hH)).mono_height
        (le_of_lt (ThetaWNoteD.omegaPow_add_omegaPow_lt_red h0)) (hH.omegaPow_mem hα)

/-- **Freund, Exercise 7.1 (c) (Cut elimination)**, concrete: for a nice operator `H`, a
level-bounded `A`, and `ρ` avoiding every level's `Ω`, `H ⊢^α_{ρ+1} Γ` gives `H ⊢^{ω(α)}_ρ Γ`. -/
theorem elimination {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    (hAb : FamilyLevelBounded A) (hρ : ∀ j : Fin n, ρ ≠ ThetaWNoteD.Omega j.val)
    {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    (d : IDnDerivable A (ρ + ThetaWNoteD.one) H α Γ) :
    IDnDerivable A ρ H (ThetaWNoteD.omegaPow α) Γ :=
  elim_aux hAb hρ d hH

/-- **Exercise 7.1 (c), iterated**, concrete: `H ⊢^α_{ρ+m} Γ` gives `H ⊢^{ω_m(α)}_ρ Γ` when
`ρ + i` avoids every level's `Ω` for all `i ≺ m`. -/
theorem elimination_iter {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.NiceS H)
    (hAb : FamilyLevelBounded A) :
    ∀ (m : ℕ) {ρ α : ThetaWNoteD} {Γ : Sequent (LIinfN n)},
      (∀ i < m, ∀ j : Fin n, ρ + ThetaWNoteD.ofNat i ≠ ThetaWNoteD.Omega j.val) →
      IDnDerivable A (ρ + ThetaWNoteD.ofNat m) H α Γ →
      IDnDerivable A ρ H (ThetaWNoteD.omegaTower m α) Γ
  | 0, ρ, α, Γ, _, d => by
    rw [ThetaWNoteD.ofNat_zero, ThetaWNoteD.add_zero] at d
    exact d
  | m + 1, ρ, α, Γ, hρ, d => by
    rw [ThetaWNoteD.add_ofNat_succ_red] at d
    have d' := elimination hH hAb (hρ m (Nat.lt_succ_self m)) d
    rw [ThetaWNoteD.omegaTower_succ_red]
    exact elimination_iter hH hAb m (fun i hi => hρ i (Nat.lt_succ_of_lt hi)) d'

end IDnDerivable

end IDn

end OrdinalAnalysis
