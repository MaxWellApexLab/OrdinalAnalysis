/-
  The coded Veblen ordering restricted to a segment `VeblenBelow ν b`, for the
  ramified calculus `RA_∞`, and the transport of a derivation whose height is
  below a bound into that segment's own notation system.

  This is `ACAOmega/Gamma0Order₂.lean`'s `vebSegOrder₂` ported from
  `CodedOrder₂` (second-order) to `CodedOrderR` (first-order, `Ramified/CodedOrderR.lean`):
  the segment ordering `x ≺₁ y ∧ y ≺₁ (code of φ_a(b))`, read on
  `Gamma0Note.VeblenBelow a b`.  Every arithmetic-level fact it needs —
  `precN₁`, `gamma0Code`, `precN₁_code_iff` — is the same one `Ramified/CodedOrderR.lean`'s
  `gamma0OrderR` already uses for the unsegmented ordering; only the extra
  conjunct restricting to the segment is new, and it is built exactly as
  `Ramified.precAt` builds `precAt prec y x` from a formula and two terms —
  indeed the extra conjunct *is* `precAt precCode₁R (#1) (numAtR (code of the
  bound))`, so its closedness and syntactic bridge reuse
  `Ramified.freeVariables_precAt_eq_empty` and `Ramified.eval_precAt₁R_numeral`
  instead of being reproved from scratch.

  The height transport `OmegaDerivableR.toBelow` is `Ordinal/BelowDerivation.lean`'s
  `OmegaDerivable.toBelow` ported to `OmegaDerivableR`: the rules of the ramified
  calculus mention the height only through `<` between a premise and its
  conclusion, exactly as the unramified ones do, so a derivation whose height is
  below `ε` is, verbatim, a derivation in `Below ε` — the two new (Pr)/(Pr⁻)
  cases are handled the same way every other unary rule is.
-/
import OrdinalAnalysis.Ramified.CodedOrderR
import OrdinalAnalysis.Ordinal.Veblen.VeblenBelow
import OrdinalAnalysis.Ordinal.BelowDerivation

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalVNote (precDef₁)
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)
open OrdinalAnalysis.Gentzen.CodedVeblen (precN₁ precN₁_code_iff)
open OrdinalAnalysis.Gamma0Note (veblenNote VeblenBelow)

/-! ### The segment ordering below `φ_a(b)` -/

/-- `≺₁`'s segment below `φ_a(b)`: `x ≺₁ y ∧ y ≺₁ (code of φ_a(b))`.
`Ramified.precCode₁R` conjoined with `precAt precCode₁R (#1) (numAtR (code of
φ_a(b)))` — the latter is literally `Ramified.precAt` applied to the code
bound, so all of its bookkeeping is reused unchanged. -/
def precSegVebR (a b : Gamma0Note) : Semiformula LRA ℕ 2 :=
  precCode₁R ⋏
    precAt precCode₁R (#1 : Semiterm LRA ℕ 2)
      (numAtR (gamma0Code (veblenNote a b)) : Semiterm LRA ℕ 2)

theorem XFree_precSegVebR (a b : Gamma0Note) : XFree (precSegVebR a b) := by
  refine (XFree_and _ _).mpr ⟨XFree_precCode₁R, ?_⟩
  show XFree (Rew.subst ![(#1 : Semiterm LRA ℕ 2),
    (numAtR (gamma0Code (veblenNote a b)) : Semiterm LRA ℕ 2)] ▹ precCode₁R)
  exact (XFree_rew _ _).mpr XFree_precCode₁R

theorem freeVariables_precSegVebR (a b : Gamma0Note) : (precSegVebR a b).freeVariables = ∅ := by
  have h2 : (precAt precCode₁R (#1 : Semiterm LRA ℕ 2)
      (numAtR (gamma0Code (veblenNote a b)) : Semiterm LRA ℕ 2)).freeVariables = ∅ :=
    freeVariables_precAt_eq_empty precCode₁R freeVariables_precCode₁R (by simp)
      (freeVariables_of_groundR (groundR_numAtR _))
  simp [precSegVebR, h2, freeVariables_precCode₁R]

/-- `m ≺_{a,b} n`: `m ≺₁ n` and `n ≺₁ (code of φ_a(b))`. -/
def precNSegVebR (a b : Gamma0Note) (m n : ℕ) : Prop :=
  precN₁ m n ∧ precN₁ n (gamma0Code (veblenNote a b))

/-- **The syntactic bridge for the segment.**  `precAt (precSegVebR a b)` at a
pair of numerals reads, in any standard reading of the fresh symbols, as
`precNSegVebR a b`: the outer substitution distributes over the conjunction,
the first conjunct is `Ramified.eval_precAt₁R_numeral` outright, and the second
reduces to it after chasing the composed substitution back to `precAt` at
`(numAtR n, numAtR (code of the bound))` via `Ramified.rew_precAt`. -/
theorem eval_precSegVebR (a b : Gamma0Note) (s₂ : Structure RALang ℕ) (m n : ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := raStd s₂) ![] f
      (precAt (precSegVebR a b) (numAtR m) (numAtR n)) ↔ precNSegVebR a b m n := by
  have hrw : precAt (precSegVebR a b) (numAtR m : Semiterm LRA ℕ 0) (numAtR n : Semiterm LRA ℕ 0)
      = precAt precCode₁R (numAtR m : Semiterm LRA ℕ 0) (numAtR n : Semiterm LRA ℕ 0) ⋏
          precAt precCode₁R (numAtR n : Semiterm LRA ℕ 0)
            (numAtR (gamma0Code (veblenNote a b)) : Semiterm LRA ℕ 0) := by
    show (Rew.subst ![(numAtR m : Semiterm LRA ℕ 0), (numAtR n : Semiterm LRA ℕ 0)] ▹
        precSegVebR a b)
      = precAt precCode₁R (numAtR m : Semiterm LRA ℕ 0) (numAtR n : Semiterm LRA ℕ 0) ⋏
          precAt precCode₁R (numAtR n : Semiterm LRA ℕ 0)
            (numAtR (gamma0Code (veblenNote a b)) : Semiterm LRA ℕ 0)
    unfold precSegVebR
    rw [LogicalConnective.HomClass.map_and]
    have h1 : (Rew.subst ![(numAtR m : Semiterm LRA ℕ 0), (numAtR n : Semiterm LRA ℕ 0)] ▹
        precCode₁R)
        = precAt precCode₁R (numAtR m : Semiterm LRA ℕ 0) (numAtR n : Semiterm LRA ℕ 0) := rfl
    have h2 : (Rew.subst ![(numAtR m : Semiterm LRA ℕ 0), (numAtR n : Semiterm LRA ℕ 0)] ▹
        precAt precCode₁R (#1 : Semiterm LRA ℕ 2)
          (numAtR (gamma0Code (veblenNote a b)) : Semiterm LRA ℕ 2))
        = precAt precCode₁R (numAtR n : Semiterm LRA ℕ 0)
            (numAtR (gamma0Code (veblenNote a b)) : Semiterm LRA ℕ 0) := by
      rw [rew_precAt precCode₁R _ (fun z => by simp) (#1 : Semiterm LRA ℕ 2)
        (numAtR (gamma0Code (veblenNote a b)) : Semiterm LRA ℕ 2)]
      simp
    rw [h1, h2]
  rw [hrw, LogicalConnective.HomClass.map_and, eval_precAt₁R_numeral, eval_precAt₁R_numeral]
  rfl

/-- **The semantic bridge for the segment.** -/
theorem precNSegVebR_code_iff (a b : Gamma0Note) (x y : VeblenBelow a b) :
    precNSegVebR a b (gamma0Code x.1) (gamma0Code y.1) ↔ x < y := by
  unfold precNSegVebR
  rw [precN₁_code_iff, precN₁_code_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩

/-- **The coded ordering of the notations below `φ_a(b)`, for `0 < a`, in the
ramified language.**  The first-order analogue of `vebSegOrder₂`. -/
def vebSegOrderR (a b : Gamma0Note) (_ha : 0 < a) : CodedOrderR (VeblenBelow a b) where
  prec := precSegVebR a b
  xfree_prec := XFree_precSegVebR a b
  freeVariables_prec := freeVariables_precSegVebR a b
  code := fun x => gamma0Code x.1
  precN := precNSegVebR a b
  eval_precAt_numeral := fun s₂ m n f => eval_precSegVebR a b s₂ m n f
  precN_code_iff := precNSegVebR_code_iff a b

@[simp] theorem vebSegOrderR_prec (a b : Gamma0Note) (ha : 0 < a) :
    (vebSegOrderR a b ha).prec = precSegVebR a b := rfl

@[simp] theorem vebSegOrderR_code (a b : Gamma0Note) (ha : 0 < a) (x : VeblenBelow a b) :
    (vebSegOrderR a b ha).code x = gamma0Code x.1 := rfl

/-! ### Height transport into a segment's own notation system

`Ordinal/BelowDerivation.lean`'s `OmegaDerivable.toBelow`, ported to
`OmegaDerivableR`: the rules mention the height only through `<`, so a
derivation of height below `ε` is, verbatim, a derivation in `Below ε`. -/

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

namespace OmegaDerivableR

/-- **Restriction to the notations below `ε`.**  A derivation of height below
`ε` is a derivation in `Below ε`, at the same cut rank, of the same sequent. -/
theorem toBelow {ε : O} [OrdinalNotation (Below ε)] {A : Literals LRA} {I : InstantiationR}
    {ρ : Gamma0Note} :
    ∀ {α : O} {Γ : Sequent LRA}, OmegaDerivableR A I ρ α Γ →
      ∀ (hα : α < ε), OmegaDerivableR (O := Below ε) A I ρ (Below.mk α hα) Γ := by
  intro α Γ h
  induction h with
  | atom hφ => intro _; exact atom hφ
  | identity rl v => intro _; exact identity rl v
  | verum => intro _; exact verum
  | or hβ _ ih =>
      intro hα
      exact or (Below.mk_lt_mk _ _ hβ) (ih (lt_trans hβ hα))
  | and hβ hγ _ _ ihφ ihψ =>
      intro hα
      exact and (Below.mk_lt_mk _ _ hβ) (Below.mk_lt_mk _ _ hγ)
        (ihφ (lt_trans hβ hα)) (ihψ (lt_trans hγ hα))
  | omegaRule β hβ _ ih =>
      intro hα
      exact omegaRule (fun n => Below.mk (β n) (lt_trans (hβ n) hα))
        (fun n => Below.mk_lt_mk _ _ (hβ n)) (fun n => ih n (lt_trans (hβ n) hα))
  | exs n hβ _ ih =>
      intro hα
      exact exs n (Below.mk_lt_mk _ _ hβ) (ih (lt_trans hβ hα))
  | contraction ss _ ih => intro hα; exact contraction ss (ih hα)
  | cut hc hβ hγ _ _ ihφ ihψ =>
      intro hα
      exact cut hc (Below.mk_lt_mk _ _ hβ) (Below.mk_lt_mk _ _ hγ)
        (ihφ (lt_trans hβ hα)) (ihψ (lt_trans hγ hα))
  | pr ha hβ _ ih =>
      intro hα
      exact pr ha (Below.mk_lt_mk _ _ hβ) (ih (lt_trans hβ hα))
  | npr ha hβ _ ih =>
      intro hα
      exact npr ha (Below.mk_lt_mk _ _ hβ) (ih (lt_trans hβ hα))

end OmegaDerivableR

end Ramified

end OrdinalAnalysis
