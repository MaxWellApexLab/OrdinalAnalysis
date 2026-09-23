/-
  The cut-rank bound of `ACA_∞`'s axioms: `rank φ ≤ ω + complexity φ`.

  `ACA/Syntax.lean`'s `rank` pays a successor for every propositional and
  number-quantifier step and `max (succ · ) ω` for every set quantifier, while
  Foundation's `Semiformula.complexity` pays a plain `+ 1` for *all* of them,
  first- or second-order alike.  So by induction on the formula, `rank` never
  overtakes `omegaAdd complexity := ω + complexity`:

  * at a literal both sides are `0`;
  * at `⋏`/`⋎`/`∀¹`/`∃¹`, `rank` takes a `NONote.succ` and `complexity` a
    `+ 1`, and `succ_omegaAdd_le` (via `NONote.repr_succ`,
    `Ordinal/NONoteSucc.lean`) says these match: `succ (ω + c) ≤ ω + (c+1)`;
  * at `∀²`/`∃²`, `rank` additionally takes a `max · ω`, absorbed because
    `omegaN ≤ omegaAdd _` (`omegaN_le_omegaAdd`, already in
    `ACAOmega/SecondCutEv.lean`).

  The rest of the file packages this into the exact shape
  `ACAOmega/Axioms₂.lean`'s `cut_axioms₂_of` consumes: a rank bound `ρ'`
  together with `∀ σ ∈ Δ, rank (ev₂ σ) < ρ'` for a finite list `Δ`, with
  `ρ' := omegaAdd k` for `k` one more than the largest complexity on `Δ`.
-/
import OrdinalAnalysis.ACAOmega.SecondCutEv
import OrdinalAnalysis.Ordinal.NONoteSucc

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA

namespace OmegaDerivable₂

variable {L : FirstOrder.Language} {Ξ ξ : Type*}

/-! ### `omegaAdd` is monotone in its natural-number argument -/

theorem omegaAdd_le_omegaAdd {m n : ℕ} (h : m ≤ n) : omegaAdd m ≤ omegaAdd n := by
  show NONote.repr (omegaAdd m) ≤ NONote.repr (omegaAdd n)
  rw [repr_omegaAdd, repr_omegaAdd]
  have h' : (m : Ordinal) ≤ (n : Ordinal) := by exact_mod_cast h
  exact add_le_add_right h' _

theorem omegaAdd_lt_omegaAdd {m n : ℕ} (h : m < n) : omegaAdd m < omegaAdd n := by
  show NONote.repr (omegaAdd m) < NONote.repr (omegaAdd n)
  rw [repr_omegaAdd, repr_omegaAdd]
  have h' : (m : Ordinal) < (n : Ordinal) := by exact_mod_cast h
  exact add_lt_add_right h' _

/-- **`NONote.succ` of `omegaAdd n` reaches `omegaAdd (n+1)`.**  The successor
here is the project's `nadd`-based one, but by `NONote.repr_succ` its `repr`
is still ordinary successor, so it lands exactly on `ω + (n+1)`. -/
theorem succ_omegaAdd_le (n : ℕ) : NONote.succ (omegaAdd n) ≤ omegaAdd (n + 1) := by
  show NONote.repr (NONote.succ (omegaAdd n)) ≤ NONote.repr (omegaAdd (n + 1))
  have hs : NONote.repr (NONote.succ (omegaAdd n)) = NONote.repr (omegaAdd n) + 1 :=
    NONote.repr_succ (omegaAdd n)
  rw [hs, repr_omegaAdd, repr_omegaAdd, Nat.cast_succ, add_assoc]

/-! ### The rank bound -/

/-- **The cut rank of `ACA_∞` is bounded by `ω + complexity`.** -/
theorem rank_le_omegaAdd {N n : ℕ} (φ : Semiformula L Ξ ξ N n) :
    rank φ ≤ omegaAdd φ.complexity := by
  induction φ using Semiformula.rec' with
  | hRel r v => simpa using NONote.zero_le' _
  | hNrel r v => simpa using NONote.zero_le' _
  | hBvar X t => simpa using NONote.zero_le' _
  | hNbvar X t => simpa using NONote.zero_le' _
  | hFvar X t => simpa using NONote.zero_le' _
  | hNfvar X t => simpa using NONote.zero_le' _
  | hVerum => simpa using NONote.zero_le' _
  | hFalsum => simpa using NONote.zero_le' _
  | hAnd φ ψ ihφ ihψ =>
      have hφc : φ.complexity ≤ max φ.complexity ψ.complexity := le_max_left _ _
      have hψc : ψ.complexity ≤ max φ.complexity ψ.complexity := le_max_right _ _
      have h1 : rank φ ≤ omegaAdd (max φ.complexity ψ.complexity) :=
        le_trans ihφ (omegaAdd_le_omegaAdd hφc)
      have h2 : rank ψ ≤ omegaAdd (max φ.complexity ψ.complexity) :=
        le_trans ihψ (omegaAdd_le_omegaAdd hψc)
      have hm : max (rank φ) (rank ψ) ≤ omegaAdd (max φ.complexity ψ.complexity) :=
        max_le h1 h2
      calc rank (φ ⋏ ψ) = NONote.succ (max (rank φ) (rank ψ)) := rank_and φ ψ
        _ ≤ NONote.succ (omegaAdd (max φ.complexity ψ.complexity)) :=
            NONote.succ_le_succ hm
        _ ≤ omegaAdd (max φ.complexity ψ.complexity + 1) := succ_omegaAdd_le _
        _ = omegaAdd (φ ⋏ ψ).complexity := by rw [complexity_and]
  | hOr φ ψ ihφ ihψ =>
      have hφc : φ.complexity ≤ max φ.complexity ψ.complexity := le_max_left _ _
      have hψc : ψ.complexity ≤ max φ.complexity ψ.complexity := le_max_right _ _
      have h1 : rank φ ≤ omegaAdd (max φ.complexity ψ.complexity) :=
        le_trans ihφ (omegaAdd_le_omegaAdd hφc)
      have h2 : rank ψ ≤ omegaAdd (max φ.complexity ψ.complexity) :=
        le_trans ihψ (omegaAdd_le_omegaAdd hψc)
      have hm : max (rank φ) (rank ψ) ≤ omegaAdd (max φ.complexity ψ.complexity) :=
        max_le h1 h2
      calc rank (φ ⋎ ψ) = NONote.succ (max (rank φ) (rank ψ)) := rank_or φ ψ
        _ ≤ NONote.succ (omegaAdd (max φ.complexity ψ.complexity)) :=
            NONote.succ_le_succ hm
        _ ≤ omegaAdd (max φ.complexity ψ.complexity + 1) := succ_omegaAdd_le _
        _ = omegaAdd (φ ⋎ ψ).complexity := by rw [complexity_or]
  | hAll₁ φ ih =>
      calc rank (∀¹ φ) = NONote.succ (rank φ) := rank_all₁ φ
        _ ≤ NONote.succ (omegaAdd φ.complexity) := NONote.succ_le_succ ih
        _ ≤ omegaAdd (φ.complexity + 1) := succ_omegaAdd_le _
        _ = omegaAdd (∀¹ φ).complexity := by rw [complexity_all₁]
  | hExs₁ φ ih =>
      calc rank (∃¹ φ) = NONote.succ (rank φ) := rank_exs₁ φ
        _ ≤ NONote.succ (omegaAdd φ.complexity) := NONote.succ_le_succ ih
        _ ≤ omegaAdd (φ.complexity + 1) := succ_omegaAdd_le _
        _ = omegaAdd (∃¹ φ).complexity := by rw [complexity_exs₁]
  | hAll₂ φ ih =>
      have h1 : NONote.succ (rank φ) ≤ omegaAdd (φ.complexity + 1) :=
        le_trans (NONote.succ_le_succ ih) (succ_omegaAdd_le _)
      have h2 : omegaN ≤ omegaAdd (φ.complexity + 1) := omegaN_le_omegaAdd _
      calc rank (∀² φ) = max (NONote.succ (rank φ)) omegaN := rank_all₂ φ
        _ ≤ omegaAdd (φ.complexity + 1) := max_le h1 h2
        _ = omegaAdd (∀² φ).complexity := by rw [complexity_all₂]
  | hExs₂ φ ih =>
      have h1 : NONote.succ (rank φ) ≤ omegaAdd (φ.complexity + 1) :=
        le_trans (NONote.succ_le_succ ih) (succ_omegaAdd_le _)
      have h2 : omegaN ≤ omegaAdd (φ.complexity + 1) := omegaN_le_omegaAdd _
      calc rank (∃² φ) = max (NONote.succ (rank φ)) omegaN := rank_exs₂ φ
        _ ≤ omegaAdd (φ.complexity + 1) := max_le h1 h2
        _ = omegaAdd (∃² φ).complexity := by rw [complexity_exs₂]

/-- The strict form: the rank is strictly below `omegaAdd (complexity + 1)`. -/
theorem rank_lt_omegaAdd_succ {N n : ℕ} (φ : Semiformula L Ξ ξ N n) :
    rank φ < omegaAdd (φ.complexity + 1) :=
  lt_of_le_of_lt (rank_le_omegaAdd φ) (omegaAdd_lt_omegaAdd (Nat.lt_succ_self _))

/-! ### The shape `Axioms₂.lean`'s `cut_axioms₂_of` consumes -/

/-- **`ev₂` does not raise the rank above `ω + complexity`.**  `rank (ev₂ σ)
= rank σ` by `rank_ev₂` (`ACAOmega/Evaluate.lean`), so this is just
`rank_le_omegaAdd` transported across the evaluation. -/
theorem rank_ev₂_le_omegaAdd (σ : Proposition ℒₒᵣ) :
    rank (ev₂ σ) ≤ omegaAdd σ.complexity := by
  rw [rank_ev₂]; exact rank_le_omegaAdd σ

theorem rank_ev₂_lt_omegaAdd_succ (σ : Proposition ℒₒᵣ) :
    rank (ev₂ σ) < omegaAdd (σ.complexity + 1) := by
  rw [rank_ev₂]; exact rank_lt_omegaAdd_succ σ

/-- **The corollary the assembly needs.**  Every finite list of axioms has
*some* rank bound `ω + k` dominating the (evaluated) rank of every member on
the list — take `k` one more than the largest complexity on it. -/
theorem exists_omegaAdd_bound : ∀ (Δ : SecondOrder.Sequent ℒₒᵣ),
    ∃ k : ℕ, ∀ σ ∈ Δ, rank (ev₂ σ) < omegaAdd k
  | [] => ⟨0, by simp⟩
  | σ :: Δ => by
      obtain ⟨k', hk'⟩ := exists_omegaAdd_bound Δ
      refine ⟨max k' (σ.complexity + 1), fun τ hτ => ?_⟩
      rcases List.mem_cons.mp hτ with rfl | hτ'
      · exact lt_of_lt_of_le (rank_ev₂_lt_omegaAdd_succ τ)
          (omegaAdd_le_omegaAdd (le_max_right _ _))
      · exact lt_of_lt_of_le (hk' τ hτ') (omegaAdd_le_omegaAdd (le_max_left _ _))

/-- **The `Chain`-form the assembly needs.**  Every finite list of axioms'
rank bound is reached from `ω` in finitely many `PredBound` steps
(`chain_omegaAdd`, `ACAOmega/SecondCutEv.lean`), which is what
`cutElimination_omegaAdd_ev` consumes. -/
theorem exists_chain_bound (Δ : SecondOrder.Sequent ℒₒᵣ) :
    ∃ k : ℕ, Chain k omegaN (omegaAdd k) ∧ ∀ σ ∈ Δ, rank (ev₂ σ) < omegaAdd k :=
  let ⟨k, hk⟩ := exists_omegaAdd_bound Δ
  ⟨k, chain_omegaAdd k, hk⟩

end OmegaDerivable₂

end OrdinalAnalysis.ACAOmega
