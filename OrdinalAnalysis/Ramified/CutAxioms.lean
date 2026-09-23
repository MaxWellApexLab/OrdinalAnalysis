/-
  Cutting away the negated axioms of a theory, in the ramified calculus, and the
  finite-part rank bound the sharp upper bound will need.

  ## `cut_axioms_of`

  This is `Gentzen/CutAxioms.lean`'s `cut_axioms_of` ported from the unramified
  `OmegaDerivable` to `OmegaDerivableR`, with one simplification the port earns:
  there the cut rank is a natural number bounding formula *complexity*, and each
  step has to re-derive a bigger rank `r' := max r (φ.complexity + 1)` before it
  may cut on `φ`; here the cut rank `ρ` is already an ordinal notation fixed by
  the caller, and the hypothesis `hrk` supplies `rank φ < ρ` for every axiom
  directly, so no such bump is needed — the whole derivation runs at the single
  rank `ρ` throughout, and only `OmegaDerivableR.mono_rank` is used, to lift the
  rank-`0` axiom derivations `hax` supplies up to `ρ`.

  The proof is otherwise the Gentzen one line for line: cut the axioms of `Δ` out
  one at a time, from the last to the first, replaying `Sequent.embed_cons` to
  see the negated list as a cons, cutting the freshly-exposed negated axiom
  against its (rank-lifted) derivation, and recursing on the shorter list.

  ## The finite-part rank bound

  `Rank.lean`'s `rank_lt_omegaPow_of_level` bounds the rank of a level-`< ν`
  formula by `ω^ν`, which is what the naming schema needs (`NamingAxioms.lean`).
  The sharp upper bound needs more: not just that the rank sits *below* `ω^ν`,
  but *how far* below, as a function of the formula's logical complexity — the
  finite part that the ordinal-arithmetic climb of the upper bound absorbs.  The
  answer is exactly the one `complexity` itself gives: `rank` and `complexity`
  are the *same* structural recursion (`succ (max ⬝ ⬝)` at the connectives,
  `succ ⬝` at the quantifiers), differing only at the atoms — `rank` charges
  `atomRank r`, `complexity` charges `0` — so replacing each atom's contribution
  by its worst case `ω^{lvlOf φ}` throughout gives

      rank φ ≤ ω^{lvlOf φ} ⊕ complexity φ

  proved by the same induction `rank_lt_omegaPow_of_level` uses, strengthened
  from `<` to `≤` and from a strict level bound to a bound on the *value*, with
  the successor step going through on the nose because
  `succ (ρ ⊕ ofNat c) = ρ ⊕ ofNat (c + 1)` (`nadd_ofNat_succ`, itself immediate
  from `Ordinal.Veblen.RankSegments`'s `repr_nadd_one`/`repr_nadd_ofNat`).
-/
import OrdinalAnalysis.Ramified.Evaluate
import OrdinalAnalysis.Ordinal.Veblen.RankSegments

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Derivation

/-! ### `cut_axioms_of` -/

/-- `0` is the least cut rank.  Needed to lift a cut-free (rank-`0`) axiom
derivation up to an arbitrary rank `ρ` before cutting with it. -/
theorem Gamma0Note.zero_le' (x : Gamma0Note) : (0 : Gamma0Note) ≤ x := by
  rw [Gamma0Note.le_def, Gamma0Note.repr_zero]
  exact zero_le

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- **Cutting away the negated axioms of a theory `T`**, one at a time, at a
fixed cut rank `ρ`, given that every axiom of `T` is cut-free derivable at some
height in `O` and has rank below `ρ`. -/
theorem cut_axioms_of (T : Theory LRA) {ρ : Gamma0Note}
    (hax : ∀ σ ∈ T, ∃ β : O, OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb σ : Proposition LRA)])
    (hrk : ∀ σ ∈ T, rank (evR (Rewriting.emb σ : Proposition LRA)) < ρ) :
    ∀ (Δ : List (Sentence LRA)), (∀ σ ∈ Δ, σ ∈ T) → ∀ {α : O} {Θ : Sequent LRA},
      OmegaDerivableR trueArithLitsR evInstR ρ α (Θ ++ (∼Sequent.embed Δ).map evR) →
      ∃ α' : O, OmegaDerivableR trueArithLitsR evInstR ρ α' Θ
  | [], _, α, Θ, h => ⟨α, by simpa [List.tilde_def] using h⟩
  | σ :: Δ, hΔ, α, Θ, h => by
      obtain ⟨β, hσ⟩ := hax σ (hΔ σ (by simp))
      set φ : Proposition LRA := evR (Rewriting.emb σ : Proposition LRA) with hφ
      set rest : Sequent LRA := (∼Sequent.embed Δ).map evR with hrest
      have h' : OmegaDerivableR trueArithLitsR evInstR ρ α (Θ ++ ((∼φ) :: rest)) := by
        have e : (∼Sequent.embed (σ :: Δ)).map evR = (∼φ) :: rest := by
          simp only [Sequent.embed_cons, List.tilde_def, List.map_cons, hφ, hrest, evR_neg]
        rw [← e]
        exact h
      have hL : OmegaDerivableR trueArithLitsR evInstR ρ α ((∼φ) :: (Θ ++ rest)) := by
        refine OmegaDerivableR.contraction ?_ h'
        intro x hx
        simp only [List.mem_append, List.mem_cons] at hx ⊢
        tauto
      have hR : OmegaDerivableR trueArithLitsR evInstR ρ β (φ :: []) :=
        hσ.mono_rank (Gamma0Note.zero_le' ρ)
      have hcrk : rank φ < ρ := hrk σ (hΔ σ (by simp))
      have hcut : OmegaDerivableR trueArithLitsR evInstR ρ
          (OrdinalNotation.succ (OrdinalNotation.nadd β α)) ([] ++ (Θ ++ rest)) :=
        OmegaDerivableR.cut hcrk
          (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_left _ _))
          (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_right _ _)) hR hL
      exact cut_axioms_of T hax hrk Δ (fun τ hτ => hΔ τ (List.mem_cons_of_mem _ hτ))
        (by simpa using hcut)

/-! ### The finite-part rank bound

`rank` and `Semiformula.complexity` share the same recursive shape; the lemmas
below make that precise at the level of `Gamma0Note` arithmetic. -/

/-- `OrdinalNotation.ofNat` is monotone, not just strictly monotone: the
non-strict form the `max`-taking connective step needs. -/
theorem ofNat_le_ofNat {m n : ℕ} (h : m ≤ n) :
    (OrdinalNotation.ofNat m : Gamma0Note) ≤ OrdinalNotation.ofNat n := by
  rcases h.eq_or_lt with rfl | h
  · exact le_refl _
  · exact le_of_lt (OrdinalNotation.ofNat_lt_ofNat h)

/-- **The successor of a finite part is the next finite part.**  Both sides
have the same `repr`: `ρ ⊕ c`, then `+1`, on one side; `ρ ⊕ (c + 1)` directly on
the other; `Gamma0Note.repr_nadd_one` and `Gamma0Note.repr_nadd_ofNat` compute
both. This is what lets `succ` pass straight through a `nadd _ (ofNat _)` bound,
with no ordinal arithmetic beyond associativity of `+` on `Ordinal`. -/
theorem nadd_ofNat_succ (ρ : Gamma0Note) (c : ℕ) :
    OrdinalNotation.succ (OrdinalNotation.nadd ρ (OrdinalNotation.ofNat c))
      = OrdinalNotation.nadd ρ (OrdinalNotation.ofNat (c + 1)) := by
  apply Gamma0Note.repr_inj.mp
  show Gamma0Note.repr (Gamma0Note.nadd (Gamma0Note.nadd ρ (Gamma0Note.ofNat c)) 1)
      = Gamma0Note.repr (Gamma0Note.nadd ρ (Gamma0Note.ofNat (c + 1)))
  rw [Gamma0Note.repr_nadd_one, Gamma0Note.repr_nadd_ofNat, Gamma0Note.repr_nadd_ofNat]
  push_cast
  rw [add_assoc]

/-- **An atom's rank sits below the `ω`-power of its own level.**  `atomRank`'s
two branches: `0 ≤ ω^0` when the symbol is levelless, `ω^ν ≤ ω^ν` when it is
tagged `ν` — and `(relLevel r).getD 0` reads off exactly that `ν` (or `0`) in
either case. -/
theorem atomRank_le_omegaPowLv_self {k : ℕ} (r : LRA.Rel k) :
    atomRank r ≤ omegaPowLv ((relLevel r).getD 0) := by
  unfold atomRank
  cases hr : relLevel r with
  | none => simpa using Gamma0Note.zero_le' (omegaPowLv 0)
  | some ν => simp

/-- **The finite-part rank bound, at an arbitrary level above `lvlOf φ`.**  The
generalisation `rank_le_omegaPowLv_lvlOf_nadd` needs: unlike a strict bound, a
non-strict one is not automatically inherited from a subformula to a larger
level, so the level `ν` is threaded through the induction exactly as
`rank_lt_omegaPow_of_level` threads its strict bound. -/
theorem rank_le_nadd_ofNat_complexity_of_level {n : ℕ} {ν : Lv} :
    ∀ {φ : Semiformula LRA ℕ n}, lvlOf φ ≤ ν →
      rank φ ≤ OrdinalNotation.nadd (omegaPowLv ν) (OrdinalNotation.ofNat φ.complexity) := by
  intro φ h
  induction φ using Semiformula.rec' with
  | hverum => simpa using Gamma0Note.zero_le' _
  | hfalsum => simpa using Gamma0Note.zero_le' _
  | hrel r v =>
      refine le_trans (atomRank_le_omegaPowLv_self r) ?_
      have h' : (relLevel r).getD 0 ≤ ν := by simpa using h
      have hpow : omegaPowLv ((relLevel r).getD 0) ≤ omegaPowLv ν := by
        rcases h'.eq_or_lt with rfl | hlt
        · exact le_refl _
        · exact le_of_lt (omegaPowLv_lt_omegaPowLv hlt)
      exact hpow.trans (OrdinalNotation.le_nadd_left _ _)
  | hnrel r v =>
      refine le_trans (atomRank_le_omegaPowLv_self r) ?_
      have h' : (relLevel r).getD 0 ≤ ν := by simpa using h
      have hpow : omegaPowLv ((relLevel r).getD 0) ≤ omegaPowLv ν := by
        rcases h'.eq_or_lt with rfl | hlt
        · exact le_refl _
        · exact le_of_lt (omegaPowLv_lt_omegaPowLv hlt)
      exact hpow.trans (OrdinalNotation.le_nadd_left _ _)
  | hand φ ψ ihφ ihψ =>
      simp only [lvlOf_and, max_le_iff] at h
      have hφ := ihφ h.1
      have hψ := ihψ h.2
      have hcφ : (OrdinalNotation.ofNat φ.complexity : Gamma0Note)
          ≤ OrdinalNotation.ofNat (max φ.complexity ψ.complexity) :=
        ofNat_le_ofNat (le_max_left _ _)
      have hcψ : (OrdinalNotation.ofNat ψ.complexity : Gamma0Note)
          ≤ OrdinalNotation.ofNat (max φ.complexity ψ.complexity) :=
        ofNat_le_ofNat (le_max_right _ _)
      set M : Gamma0Note :=
        OrdinalNotation.nadd (omegaPowLv ν) (OrdinalNotation.ofNat (max φ.complexity ψ.complexity))
        with hM
      have hφM : rank φ ≤ M := hφ.trans (OrdinalNotation.nadd_le_nadd_right _ hcφ)
      have hψM : rank ψ ≤ M := hψ.trans (OrdinalNotation.nadd_le_nadd_right _ hcψ)
      have hmax : max (rank φ) (rank ψ) ≤ M := max_le hφM hψM
      have hsucc : OrdinalNotation.succ (max (rank φ) (rank ψ)) ≤ OrdinalNotation.succ M :=
        OrdinalNotation.nadd_le_nadd_left _ hmax
      rw [rank_and, Semiformula.complexity_and]
      refine hsucc.trans (le_of_eq ?_)
      rw [hM, nadd_ofNat_succ]
  | hor φ ψ ihφ ihψ =>
      simp only [lvlOf_or, max_le_iff] at h
      have hφ := ihφ h.1
      have hψ := ihψ h.2
      have hcφ : (OrdinalNotation.ofNat φ.complexity : Gamma0Note)
          ≤ OrdinalNotation.ofNat (max φ.complexity ψ.complexity) :=
        ofNat_le_ofNat (le_max_left _ _)
      have hcψ : (OrdinalNotation.ofNat ψ.complexity : Gamma0Note)
          ≤ OrdinalNotation.ofNat (max φ.complexity ψ.complexity) :=
        ofNat_le_ofNat (le_max_right _ _)
      set M : Gamma0Note :=
        OrdinalNotation.nadd (omegaPowLv ν) (OrdinalNotation.ofNat (max φ.complexity ψ.complexity))
        with hM
      have hφM : rank φ ≤ M := hφ.trans (OrdinalNotation.nadd_le_nadd_right _ hcφ)
      have hψM : rank ψ ≤ M := hψ.trans (OrdinalNotation.nadd_le_nadd_right _ hcψ)
      have hmax : max (rank φ) (rank ψ) ≤ M := max_le hφM hψM
      have hsucc : OrdinalNotation.succ (max (rank φ) (rank ψ)) ≤ OrdinalNotation.succ M :=
        OrdinalNotation.nadd_le_nadd_left _ hmax
      rw [rank_or, Semiformula.complexity_or]
      refine hsucc.trans (le_of_eq ?_)
      rw [hM, nadd_ofNat_succ]
  | hall φ ih =>
      have h' : lvlOf φ ≤ ν := by simpa using h
      have hφ := ih h'
      have hsucc : OrdinalNotation.succ (rank φ)
          ≤ OrdinalNotation.succ
            (OrdinalNotation.nadd (omegaPowLv ν) (OrdinalNotation.ofNat φ.complexity)) :=
        OrdinalNotation.nadd_le_nadd_left _ hφ
      rw [rank_all, Semiformula.complexity_all]
      exact hsucc.trans (le_of_eq (nadd_ofNat_succ _ _))
  | hexs φ ih =>
      have h' : lvlOf φ ≤ ν := by simpa using h
      have hφ := ih h'
      have hsucc : OrdinalNotation.succ (rank φ)
          ≤ OrdinalNotation.succ
            (OrdinalNotation.nadd (omegaPowLv ν) (OrdinalNotation.ofNat φ.complexity)) :=
        OrdinalNotation.nadd_le_nadd_left _ hφ
      rw [rank_exs, Semiformula.complexity_exs]
      exact hsucc.trans (le_of_eq (nadd_ofNat_succ _ _))

/-- **Every rank is its level's `ω`-power plus a finite part.**  The sharp
form `rank_lt_omegaPow_of_level` does not give: not merely `rank φ < ω^{ν+1}`,
but `rank φ ≤ ω^{lvlOf φ} ⊕ complexity φ`, an exact finite correction on top of
the level's own `ω`-power. -/
theorem rank_le_omegaPowLv_lvlOf_nadd {n : ℕ} (φ : Semiformula LRA ℕ n) :
    rank φ ≤ OrdinalNotation.nadd (omegaPowLv (lvlOf φ)) (OrdinalNotation.ofNat φ.complexity) :=
  rank_le_nadd_ofNat_complexity_of_level le_rfl

end Ramified

end OrdinalAnalysis
