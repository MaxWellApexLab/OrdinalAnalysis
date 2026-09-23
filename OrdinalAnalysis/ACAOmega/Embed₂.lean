/-
  The replay of `ACA`'s finitary derivations in the infinitary calculus — the second-order counterpart of `Gentzen/Embed.lean`.

  Every `ACA.Derivation` of `Γ` (`ACA/LK.lean`) becomes a derivation in
  `OmegaDerivable₂ trueArithLits₂ evInst₂` (`ACAOmega/{Calculus,Evaluate}.lean`),
  at the same cut rank (`cutRank₂`) and the same ordinal height (`ordN₂`,
  `CutRank₂.lean`), of every numeral instance of its sequent — the free number
  variable `x` sent to the numeral `f x`, every ground number term then
  replaced by the numeral of its value, exactly as `Gentzen/Embed.lean`'s
  `replay` does for the first-order calculus, and for the same reason: the
  `cut` rule may introduce a formula with free number variables the conclusion
  does not have, so "instantiated by `f`" is the invariant proved for every `f`
  at once, not "closed".

  Six of the eight cases are ports.

  * `identity` is **general** in `ACA.Derivation` (`[φ, ∼φ]` for arbitrary
    `φ`), which is a strictly easier match than the first-order file's atomic
    `identity rl v`: `numSubst₂_neg`/`ev₂_neg` turn the replayed sequent
    directly into `OmegaDerivable₂.identity`'s own general shape, no case
    analysis on `φ` needed.
  * `verum` is immediate.
  * `wk` replays to `OmegaDerivable₂.contraction`, exactly as the first-order
    file's `contraction` case does, via `List.map_subset` and
    `NumSubst₂.seqSubst₂_subset`.
  * `and`/`or` are the propositional cases, ported verbatim (`ev₂_and`/`ev₂_or`
    replacing `ev_and`/`ev_or`).
  * `cut` replays to `OmegaDerivable₂.cut`; the one new step is the rank bound
    `ACA.rank φ < cutRank₂ (dp.cut dn)`, discharged by `rank_ev₂` (`ev₂` does
    not change the rank) and `ACA.rank_rew` (nor does any first-order
    rewriting), landing exactly on `cutRank₂_cut`'s definition.
  * `all₁`/`exs₁` are the two first-order quantifier cases, ported with
    `NumSubst₂`'s first-order laws (`numSubst₂_free₀`, `NumSubst₂.seqSubst₂_shift₀`,
    `numSubst₂_subst₁`) and the evaluator's own (`evInst₂_inst_ev`,
    `ev₂_subst_ground`), in place of `Gentzen/NumSubst.lean`'s and
    `Gentzen/Evaluate.lean`'s.

  The genuinely new content is the two second-order quantifier cases.

  * `all₂` replays to `OmegaDerivable₂.all₂`: the eigenvariable step needs
    `numSubst₂_free₁` (number assignment commutes with the free-set-variable
    introduction) and `ev₂_free₁` (so does evaluation), and the shifted
    context needs `NumSubst₂.seqSubst₂_shift₁` and the list-level form of
    `ev₂_shift₁` proved here as `ev₂_shift₁_map`.
  * `exs₂` replays to `OmegaDerivable₂.exs₂`, whose witness is
    `ev₂ (numSubst₂ f ▹ ψ)`: `numSubst₂_subst₂` turns the replayed premise into
    exactly `evInst₂.inst₂`'s shape (`evInst₂_inst₂_ev`) after the witness is
    replaced by its own normal form (`ev₂_subst₂_congr`, "evaluating the
    witness first changes nothing"), and `Arith` of that witness survives both
    the renumbering (`NumSubst₂.arith_numSubst₂`) and the evaluation
    (`arith_ev₂`).

  `replay₂_closed` is `replay_closed` transported, using `NumSubst₂`'s local
  `NumClosed₂` in place of the (nonexistent, for this syntax — see
  `NumSubst₂.lean`'s header) `Semiformula.freeVariables = ∅`.

  `replay₂_provable` unpacks `Provable ACA φ` via `ACA.provable_iff` and feeds
  the witnessing derivation straight to `replay₂` at the trivial assignment
  `fun _ => 0`; it deliberately does **not** attempt the
  `Gentzen/CutAxioms.cut_axioms_of`-style assembly into a clean `ev₂ φ ::
  (negated axioms).map ev₂` free of any `seqSubst₂` wrapper — that would need a
  bridge from `ACA_shift₀_invariant` (which `ACA/LK.lean` already proves for
  every axiom) to `NumSubst₂.NumClosed₂`, which is no likely a one-line lemma
  and is out of scope here; see the checkpoint notes.
-/
import OrdinalAnalysis.ACAOmega.CutRank₂
import OrdinalAnalysis.ACAOmega.NumSubst₂

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega.Embed₂

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA OrdinalAnalysis.ACAOmega
open OrdinalAnalysis.ACAOmega.NumSubst₂

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-! ### One list-level fact about `ev₂` and `shift₁`

`Evaluate.lean` has the per-formula law `ev₂_shift₁'`; the `all₂` replay needs
its action on a whole (shifted) context. -/

theorem ev₂_shift₁_map (Δ : SecondOrder.Sequent ℒₒᵣ) :
    (SecondOrder.Sequent.shift₁ Δ).map ev₂ = SecondOrder.Sequent.shift₁ (Δ.map ev₂) := by
  induction Δ with
  | nil => rfl
  | cons φ Δ ih =>
      simp only [SecondOrder.Sequent.shift₁_cons, List.map_cons, ev₂_shift₁', ih]

/-- **The replay.**  An `ACA.Derivation` of `Γ` yields, for every assignment
`f`, an `ACA_∞`-derivation of the evaluated `f`-instance of `Γ`, at the same
rank and height. -/
theorem replay₂ : ∀ {Γ : SecondOrder.Sequent ℒₒᵣ} (d : ACA.Derivation Γ) (f : ℕ → ℕ),
    OmegaDerivable₂ trueArithLits₂ evInst₂ (cutRank₂ d) (ordN₂ d : O) ((seqSubst₂ f Γ).map ev₂)
  | _, .identity, f => by
      simp only [seqSubst₂_cons, seqSubst₂_nil, List.map_cons, List.map_nil,
        numSubst₂_neg, ev₂_neg]
      exact OmegaDerivable₂.identity _
  | _, .verum, f => by
      simpa using OmegaDerivable₂.verum
  | _, .wk d ss, f =>
      OmegaDerivable₂.contraction (List.map_subset _ (seqSubst₂_subset ss)) (replay₂ d f)
  | _, .and dp dq, f => by
      have hp := replay₂ dp f
      have hq := replay₂ dq f
      simp only [seqSubst₂_cons, List.map_cons] at hp hq ⊢
      simp only [LogicalConnective.HomClass.map_and, ev₂_and]
      exact OmegaDerivable₂.and (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_left _ _))
        (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_right _ _))
        (hp.mono_rank (by simp [cutRank₂_and])) (hq.mono_rank (by simp [cutRank₂_and]))
  | _, .or d, f => by
      have h := replay₂ d f
      simp only [seqSubst₂_cons, List.map_cons] at h ⊢
      simp only [LogicalConnective.HomClass.map_or, ev₂_or]
      exact OmegaDerivable₂.or (OrdinalNotation.lt_succ _) (h.mono_rank (by simp [cutRank₂_or]))
  | _, .cut dp dn, f => by
      -- `ACA.Derivation.cut` shares one context `Γ` between its two premises
      -- (unlike the finitary calculus's `Γ`/`Δ`): the replayed cut therefore
      -- produces `Γ' ++ Γ'`, collapsed back to `Γ'` by `contraction`.
      have hp := replay₂ dp f
      have hn := replay₂ dn f
      simp only [seqSubst₂_cons, List.map_cons] at hp hn
      simp only [numSubst₂_neg, ev₂_neg] at hn
      refine OmegaDerivable₂.contraction
        (List.append_subset.mpr ⟨List.Subset.refl _, List.Subset.refl _⟩)
        (OmegaDerivable₂.cut ?_ (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_left _ _))
          (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_right _ _))
          (hp.mono_rank (by simp [cutRank₂_cut])) (hn.mono_rank (by simp [cutRank₂_cut])))
      simp only [cutRank₂_cut, rank_ev₂, ACA.rank_rew]
      exact lt_of_lt_of_le (NONote.lt_succ _) (le_max_left _ _)
  | _, .all₁ d, f => by
      simp only [seqSubst₂_cons, List.map_cons, Semiformula.rew_all₀, numSubst₂_q, ev₂_all₁]
      refine OmegaDerivable₂.omegaRule (fun _ => (ordN₂ d : O))
        (fun _ => OrdinalNotation.lt_succ _)
        (fun n => ?_)
      have h := replay₂ d (n :>ₙ f)
      simp only [seqSubst₂_cons, List.map_cons, seqSubst₂_shift₀, numSubst₂_free₀] at h
      rw [evInst₂_inst_ev]
      exact h.mono_rank (by simp [cutRank₂_all₁])
  | _, .exs₁ d, f => by
      rename_i φ t Γ
      have h := replay₂ d f
      simp only [seqSubst₂_cons, List.map_cons, numSubst₂_subst₁] at h
      simp only [seqSubst₂_cons, List.map_cons, Semiformula.rew_exs₀, numSubst₂_q, ev₂_exs₁]
      refine OmegaDerivable₂.exs (evTerm ((numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) t))
        (OrdinalNotation.lt_succ _) ?_
      rw [evInst₂_inst_ev, ← ev₂_subst_ground _ (ground_numSubst₂_term f t)]
      exact h.mono_rank (by simp [cutRank₂_exs₁])
  | _, .all₂ d, f => by
      simp only [seqSubst₂_cons, List.map_cons, Semiformula.rew_all₁, ev₂_all₂]
      refine OmegaDerivable₂.all₂ (OrdinalNotation.lt_succ _) ?_
      have h := replay₂ d f
      simp only [seqSubst₂_cons, List.map_cons, seqSubst₂_shift₁, numSubst₂_free₁,
        ev₂_free₁', ev₂_shift₁_map] at h
      exact h.mono_rank (by simp [cutRank₂_all₂])
  | _, .exs₂ hψ d, f => by
      simp only [seqSubst₂_cons, List.map_cons, Semiformula.rew_exs₁, ev₂_exs₂]
      refine OmegaDerivable₂.exs₂ ((arith_ev₂ _).mpr (arith_numSubst₂ f hψ))
        (OrdinalNotation.lt_succ _) ?_
      have h := replay₂ d f
      simp only [seqSubst₂_cons, List.map_cons, numSubst₂_subst₂] at h
      rw [evInst₂_inst₂_ev, ev₂_subst₂_congr]
      exact h.mono_rank (by simp [cutRank₂_exs₂])

/-- **The replay of a sequent with no free number variable** is a derivation of
its evaluation, with no `seqSubst₂` wrapper. -/
theorem replay₂_closed {Γ : SecondOrder.Sequent ℒₒᵣ} (d : ACA.Derivation Γ)
    (hc : ∀ φ ∈ Γ, NumClosed₂ φ) :
    OmegaDerivable₂ trueArithLits₂ evInst₂ (cutRank₂ d) (ordN₂ d : O) (Γ.map ev₂) := by
  have h := replay₂ (O := O) d (fun _ => 0)
  rwa [seqSubst₂_eq_self hc] at h

/-- **The replay of a schema-provable formula.**  `Provable ACA φ` unpacks
(`ACA.provable_iff`) to a derivation of `φ :: ∼axioms` for some list of
instances of `ACA`; replaying it (at the trivial assignment) gives a
derivation of the evaluated numeral-`0`-instance of that sequent, at some rank
and some height. Turning this into a *closed* derivation of `ev₂ φ ::
(negated axioms).map ev₂` needs every member of `axioms` (and `φ`) to be
`NumClosed₂`; `ACA/LK.lean` proves the axioms are `Semiproposition.shift₀`-fixed
(`ACA_shift₀_invariant`), which is the right *fact* but not the same
*statement*, and bridging the two is left to whichever later file actually
needs the clean form (`Boundedness₂.lean`/`LowerClass₂.lean`). -/
theorem replay₂_provable {φ : Proposition ℒₒᵣ} (hφ : Provable ACA φ) :
    ∃ (axioms : SecondOrder.Sequent ℒₒᵣ), (∀ ψ ∈ axioms, ψ ∈ ACA) ∧
      ∃ (ρ : NONote) (α : O),
        OmegaDerivable₂ trueArithLits₂ evInst₂ ρ α
          ((seqSubst₂ (fun _ => 0) (φ :: ∼axioms)).map ev₂) := by
  obtain ⟨axioms, hax, ⟨d⟩⟩ := provable_iff.mp hφ
  exact ⟨axioms, hax, cutRank₂ d, (ordN₂ d : O), replay₂ d (fun _ => 0)⟩

end OrdinalAnalysis.ACAOmega.Embed₂
