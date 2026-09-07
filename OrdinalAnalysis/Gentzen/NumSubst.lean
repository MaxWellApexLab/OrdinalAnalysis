/-
  Numeral substitutions.

  The replay of a finitary derivation inside the infinitary calculus is proved
  for every *numeral instance* of the sequent at once: the free variable `x` is
  sent to the numeral `f x`, for an arbitrary assignment `f : ℕ → ℕ`.  This is
  what makes the statement inductive — the cut rule may introduce a formula
  with free variables the conclusion does not have, so "all formulas closed" is
  not an invariant, but "all formulas after substitution" is — and it is what
  turns the finitary `all` rule, which introduces a fresh free variable, into
  the ω-rule, which quantifies over numerals: the premise's fresh variable is
  assigned `n`, the others are shifted along.

  This file has the three equations the replay needs and nothing else.

  * `numSubst_free`: substituting `n :>ₙ f` into the premise of `all` is the
    `n`-th instance of the conclusion's body under `f`.
  * `seqSubst_shifts`: the shifted context is unaffected — under `n :>ₙ f` it is
    the context under `f`.
  * `numSubst_subst`: the premise of `exs`, with witness `t`, is the body
    substituted with the closed term `numSubst f t`; the evaluator will then
    replace that closed term by its numeral.

  All three are equalities of rewriters, proved the way Foundation proves its
  own (`free_rewrite_eq`, `rewrite_subst_eq`): compose, then compare on bound
  and free variables.  They are true because the numerals are closed terms,
  which `free`, `shift` and `bShift` all leave alone.
-/
import OrdinalAnalysis.Gentzen.StandardLX
import OrdinalAnalysis.Gentzen.LowerSyntax

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.NumSubst

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting LO.FirstOrder.LawfulSyntacticRewriting
open OrdinalAnalysis.Gentzen OrdinalAnalysis.Gentzen.StandardLX

/-- Every rewriter fixes a numeral. -/
@[simp] theorem rew_numLX {n : ℕ} (ω : Rew LX ℕ 0 ℕ n) (k : ℕ) :
    ω (numLX k) = (Semiterm.numeral k : Semiterm LX ℕ n) := by
  simp [numLX]

/-- The substitution sending the free variable `x` to the numeral `f x`. -/
def numSubst (f : ℕ → ℕ) : Rew LX ℕ 0 ℕ 0 := Rew.rewrite fun x => numLX (f x)

/-- The same substitution, one binder down. -/
def numSubst₁ (f : ℕ → ℕ) : Rew LX ℕ 1 ℕ 1 :=
  Rew.rewrite fun x => (Semiterm.numeral (f x) : Semiterm LX ℕ 1)

@[simp] theorem numSubst_fvar (f : ℕ → ℕ) (x : ℕ) : numSubst f &x = numLX (f x) := rfl

@[simp] theorem numSubst₁_fvar (f : ℕ → ℕ) (x : ℕ) :
    numSubst₁ f &x = (Semiterm.numeral (f x) : Semiterm LX ℕ 1) := rfl

@[simp] theorem numSubst₁_bvar (f : ℕ → ℕ) (x : Fin 1) : numSubst₁ f #x = #x := rfl

/-- The pointwise action on a sequent. -/
def seqSubst (f : ℕ → ℕ) (Γ : Sequent LX) : Sequent LX := Γ.map (numSubst f ▹ ·)

@[simp] theorem seqSubst_nil (f : ℕ → ℕ) : seqSubst f [] = [] := rfl

@[simp] theorem seqSubst_cons (f : ℕ → ℕ) (φ : Proposition LX) (Γ : Sequent LX) :
    seqSubst f (φ :: Γ) = (numSubst f ▹ φ) :: seqSubst f Γ := rfl

@[simp] theorem seqSubst_append (f : ℕ → ℕ) (Γ Δ : Sequent LX) :
    seqSubst f (Γ ++ Δ) = seqSubst f Γ ++ seqSubst f Δ := List.map_append ..

theorem seqSubst_subset {f : ℕ → ℕ} {Δ Γ : Sequent LX} (h : Δ ⊆ Γ) :
    seqSubst f Δ ⊆ seqSubst f Γ := List.map_subset _ h

theorem mem_seqSubst {f : ℕ → ℕ} {Γ : Sequent LX} {φ : Proposition LX} (h : φ ∈ Γ) :
    numSubst f ▹ φ ∈ seqSubst f Γ := List.mem_map_of_mem h

/-- On a closed formula every substitution is the identity. -/
theorem numSubst_eq_self {f : ℕ → ℕ} {φ : Proposition LX}
    (h : φ.freeVariables = ∅) : numSubst f ▹ φ = φ := by
  refine Semiformula.rew_eq_self_of (fun x => Fin.elim0 x) ?_
  intro x hx
  have hx' : x ∈ Semiformula.freeVariables φ := hx
  rw [h] at hx'
  exact absurd hx' (by simp)

/-- On a closed sequent every substitution is the identity. -/
theorem seqSubst_eq_self {f : ℕ → ℕ} {Γ : Sequent LX}
    (h : ∀ φ ∈ Γ, Semiformula.freeVariables φ = ∅) : seqSubst f Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih =>
      rw [seqSubst_cons, numSubst_eq_self (h φ (by simp)),
        ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))]

/-! ### The three equations -/

/-- The substitution pushed under one quantifier. -/
theorem numSubst_all (f : ℕ → ℕ) (φ : Semiproposition LX 1) :
    numSubst f ▹ (∀¹ φ) = ∀¹ (numSubst₁ f ▹ φ) := by
  simp only [numSubst, numSubst₁, Rewriting.app_all, Rew.q_rewrite]
  congr 1
  exact smul_ext' (by ext x <;> simp [numLX])

theorem numSubst_exs (f : ℕ → ℕ) (φ : Semiproposition LX 1) :
    numSubst f ▹ (∃¹ φ) = ∃¹ (numSubst₁ f ▹ φ) := by
  simp only [numSubst, numSubst₁, Rewriting.app_exs, Rew.q_rewrite]
  congr 1
  exact smul_ext' (by ext x <;> simp [numLX])

/-- **The `all` premise.**  Assigning `n` to the fresh variable of `φ.free` is
the `n`-th instance of the body under `f`. -/
theorem numSubst_free (f : ℕ → ℕ) (n : ℕ) (φ : Semiproposition LX 1) :
    numSubst (n :>ₙ f) ▹ Rewriting.free φ = (numSubst₁ f ▹ φ)/[numLX n] := by
  simp only [numSubst, numSubst₁]
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app, numLX]

/-- **The shifted context.**  Under `n :>ₙ f` a shifted formula is the formula
under `f`. -/
theorem numSubst_shift (f : ℕ → ℕ) (n : ℕ) (φ : Proposition LX) :
    numSubst (n :>ₙ f) ▹ Rewriting.shift φ = numSubst f ▹ φ := by
  simp only [numSubst]
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]

theorem seqSubst_shifts (f : ℕ → ℕ) (n : ℕ) (Γ : Sequent LX) :
    seqSubst (n :>ₙ f) Γ⁺ = seqSubst f Γ := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih => simp [Rewriting.shifts_cons, numSubst_shift, ih]

/-- **The `exs` premise.**  The witness becomes the closed term `numSubst f t`. -/
theorem numSubst_subst (f : ℕ → ℕ) (t : SyntacticTerm LX) (φ : Semiproposition LX 1) :
    numSubst f ▹ (φ/[t]) = (numSubst₁ f ▹ φ)/[numSubst f t] := by
  simp only [numSubst, numSubst₁]
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app, numLX]

/-- The witness is closed after substitution. -/
theorem freeVariables_numSubst_term (f : ℕ → ℕ) (t : SyntacticTerm LX) :
    (numSubst f t).freeVariables = ∅ := by
  induction t with
  | bvar x => exact Fin.elim0 x
  | fvar x => simp
  | func fn v ih =>
      simp only [numSubst, Rew.func, Semiterm.freeVariables_func]
      exact Finset.biUnion_eq_empty.mpr (fun i _ => ih i)

end OrdinalAnalysis.Gentzen.NumSubst
