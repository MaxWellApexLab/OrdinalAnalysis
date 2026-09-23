/-
  Numeral substitutions for the ramified language (design **D2**).

  A direct port of `Gentzen/NumSubst.lean` from `LX` to `LRA`.  Nothing about
  the ramification is visible here: `LRA` is another `Language.add`, the fresh
  summand contributes no function symbols, and every statement below is about
  *terms* and about the three rewriters `free`, `shift`, `bShift`.  So the same
  `Rew` idioms apply verbatim, including the one pitfall — `rw [← comp_app]`
  does not fire; `simpa [← comp_app] using smul_ext' <| by ext x <;> simp` does.

  Why the replay needs these at all.  `Ramified/Embed.lean` proves its statement
  for every *numeral instance* of the sequent at once: the free variable `x` is
  sent to the numeral `f x`, for an arbitrary `f : ℕ → ℕ`.  That is what makes
  the statement inductive — Foundation's `cut` may introduce a formula with free
  variables the conclusion does not have, so "all formulas closed" is not an
  invariant, but "all formulas after substitution" is — and it is what turns the
  finitary `all` rule, which introduces a fresh free variable, into the ω-rule,
  which quantifies over numerals.

  The three equations the replay consumes:

  * `numSubstR_free`: substituting `n :>ₙ f` into the premise of `all` is the
    `n`-th instance of the conclusion's body under `f`;
  * `seqSubstR_shifts`: the shifted context is unaffected;
  * `numSubstR_subst`: the premise of `exs`, with witness `t`, is the body
    substituted with the closed term `numSubstR f t` — which the evaluator then
    replaces by its numeral (`Ramified/Evaluate.lean`'s `evR_subst_ground`).

  All three are equalities of rewriters, proved the way Foundation proves its
  own: compose, then compare on bound and free variables.  They are true because
  the numerals are closed terms, which `free`, `shift` and `bShift` all leave
  alone.
-/
import OrdinalAnalysis.Ramified.Rank

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting

/-- `k̄` is a closed term. -/
@[simp] theorem freeVariables_num (k : ℕ) : (num k).freeVariables = ∅ := by
  simp [num, Semiterm.Operator.operator]

/-- Every rewriter fixes a numeral. -/
@[simp] theorem rew_num {n : ℕ} (ω : Rew LRA ℕ 0 ℕ n) (k : ℕ) :
    ω (num k) = (Semiterm.numeral k : Semiterm LRA ℕ n) := by
  simp [num]

/-- The substitution sending the free variable `x` to the numeral `f x`. -/
def numSubstR (f : ℕ → ℕ) : Rew LRA ℕ 0 ℕ 0 := Rew.rewrite fun x => num (f x)

/-- The same substitution, one binder down. -/
def numSubstR₁ (f : ℕ → ℕ) : Rew LRA ℕ 1 ℕ 1 :=
  Rew.rewrite fun x => (Semiterm.numeral (f x) : Semiterm LRA ℕ 1)

@[simp] theorem numSubstR_fvar (f : ℕ → ℕ) (x : ℕ) : numSubstR f &x = num (f x) := rfl

@[simp] theorem numSubstR₁_fvar (f : ℕ → ℕ) (x : ℕ) :
    numSubstR₁ f &x = (Semiterm.numeral (f x) : Semiterm LRA ℕ 1) := rfl

@[simp] theorem numSubstR₁_bvar (f : ℕ → ℕ) (x : Fin 1) : numSubstR₁ f #x = #x := rfl

/-- The pointwise action on a sequent. -/
def seqSubstR (f : ℕ → ℕ) (Γ : Sequent LRA) : Sequent LRA := Γ.map (numSubstR f ▹ ·)

@[simp] theorem seqSubstR_nil (f : ℕ → ℕ) : seqSubstR f [] = [] := rfl

@[simp] theorem seqSubstR_cons (f : ℕ → ℕ) (φ : Proposition LRA) (Γ : Sequent LRA) :
    seqSubstR f (φ :: Γ) = (numSubstR f ▹ φ) :: seqSubstR f Γ := rfl

@[simp] theorem seqSubstR_append (f : ℕ → ℕ) (Γ Δ : Sequent LRA) :
    seqSubstR f (Γ ++ Δ) = seqSubstR f Γ ++ seqSubstR f Δ := List.map_append ..

theorem seqSubstR_subset {f : ℕ → ℕ} {Δ Γ : Sequent LRA} (h : Δ ⊆ Γ) :
    seqSubstR f Δ ⊆ seqSubstR f Γ := List.map_subset _ h

theorem mem_seqSubstR {f : ℕ → ℕ} {Γ : Sequent LRA} {φ : Proposition LRA} (h : φ ∈ Γ) :
    numSubstR f ▹ φ ∈ seqSubstR f Γ := List.mem_map_of_mem h

/-- On a closed formula every substitution is the identity. -/
theorem numSubstR_eq_self {f : ℕ → ℕ} {φ : Proposition LRA}
    (h : φ.freeVariables = ∅) : numSubstR f ▹ φ = φ := by
  refine Semiformula.rew_eq_self_of (fun x => Fin.elim0 x) ?_
  intro x hx
  have hx' : x ∈ Semiformula.freeVariables φ := hx
  rw [h] at hx'
  exact absurd hx' (by simp)

/-- On a closed sequent every substitution is the identity. -/
theorem seqSubstR_eq_self {f : ℕ → ℕ} {Γ : Sequent LRA}
    (h : ∀ φ ∈ Γ, Semiformula.freeVariables φ = ∅) : seqSubstR f Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih =>
      rw [seqSubstR_cons, numSubstR_eq_self (h φ (by simp)),
        ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))]

/-! ### A numeral substitution does not raise the rank, and keeps the level

The level is `Rew`-invariant (`Ramified/Code.lean`'s `lvlOf_rew`) and the rank can
only go down under a rewriting (`Ramified/Rank.lean`'s `rank_rew_le`), so the
replay may renumber freely without breaking either the cut rank it is required
to respect or the level bookkeeping.  Recorded here in the `numSubstR` shape the
replay meets. -/

theorem rank_numSubstR_le (f : ℕ → ℕ) (φ : Proposition LRA) :
    rank (numSubstR f ▹ φ) ≤ rank φ := rank_rew_le _ φ

@[simp] theorem lvlOf_numSubstR (f : ℕ → ℕ) (φ : Proposition LRA) :
    lvlOf (numSubstR f ▹ φ) = lvlOf φ := lvlOf_rew _ φ

/-! ### The three equations -/

/-- The substitution pushed under one quantifier. -/
theorem numSubstR_all (f : ℕ → ℕ) (φ : Semiproposition LRA 1) :
    numSubstR f ▹ (∀¹ φ) = ∀¹ (numSubstR₁ f ▹ φ) := by
  simp only [numSubstR, numSubstR₁, Rewriting.app_all, Rew.q_rewrite]
  congr 1
  exact smul_ext' (by ext x <;> simp [num])

theorem numSubstR_exs (f : ℕ → ℕ) (φ : Semiproposition LRA 1) :
    numSubstR f ▹ (∃¹ φ) = ∃¹ (numSubstR₁ f ▹ φ) := by
  simp only [numSubstR, numSubstR₁, Rewriting.app_exs, Rew.q_rewrite]
  congr 1
  exact smul_ext' (by ext x <;> simp [num])

/-- **The `all` premise.**  Assigning `n` to the fresh variable of `φ.free` is
the `n`-th instance of the body under `f`. -/
theorem numSubstR_free (f : ℕ → ℕ) (n : ℕ) (φ : Semiproposition LRA 1) :
    numSubstR (n :>ₙ f) ▹ Rewriting.free φ = (numSubstR₁ f ▹ φ)/[num n] := by
  simp only [numSubstR, numSubstR₁]
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app, num]

/-- **The shifted context.**  Under `n :>ₙ f` a shifted formula is the formula
under `f`. -/
theorem numSubstR_shift (f : ℕ → ℕ) (n : ℕ) (φ : Proposition LRA) :
    numSubstR (n :>ₙ f) ▹ Rewriting.shift φ = numSubstR f ▹ φ := by
  simp only [numSubstR]
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]

theorem seqSubstR_shifts (f : ℕ → ℕ) (n : ℕ) (Γ : Sequent LRA) :
    seqSubstR (n :>ₙ f) Γ⁺ = seqSubstR f Γ := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih => simp [Rewriting.shifts_cons, numSubstR_shift, ih]

/-- **The `exs` premise.**  The witness becomes the closed term `numSubstR f t`. -/
theorem numSubstR_subst (f : ℕ → ℕ) (t : SyntacticTerm LRA) (φ : Semiproposition LRA 1) :
    numSubstR f ▹ (φ/[t]) = (numSubstR₁ f ▹ φ)/[numSubstR f t] := by
  simp only [numSubstR, numSubstR₁]
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app, num]

/-- The witness is closed after substitution. -/
theorem freeVariables_numSubstR_term (f : ℕ → ℕ) (t : SyntacticTerm LRA) :
    (numSubstR f t).freeVariables = ∅ := by
  induction t with
  | bvar x => exact Fin.elim0 x
  | fvar x => simp
  | func fn v ih =>
      simp only [numSubstR, Rew.func, Semiterm.freeVariables_func]
      exact Finset.biUnion_eq_empty.mpr (fun i _ => ih i)

end Ramified

end OrdinalAnalysis
