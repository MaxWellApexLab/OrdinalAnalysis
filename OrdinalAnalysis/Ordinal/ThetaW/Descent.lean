/-
  The multi-level ϑ-order on normal terms of all levels is not well founded.

  With unrestricted arguments of the collapsing functions and no bound on the levels, the
  clause at one level (`ϑ_k α ≺ ϑ_k β` if `α ≺ β` and `E_k(α) ≺* ϑ_k β`) admits the
  descending sequence
    `ϑ₀(Ω₂) ≻ ϑ₀(ϑ₁(Ω₃)) ≻ ϑ₀(ϑ₁(ϑ₂(Ω₄))) ≻ ⋯`,
  whose `m`-th term is `ϑ₀(ϑ₁(⋯ ϑ_{m-1}(Ω_{m+1}) ⋯))`.  Each step is the clause at level
  `0, 1, …` in turn, with the coefficient sets empty: the innermost comparison is
  `ϑ_m(Ω_{m+2}) ≺ Ω_{m+1}`, and `E_k` of a term all of whose collapses have level `> k` is
  empty.  All terms of the sequence lie below `Ω₁`, and all lie below the two-level term
  `ϑ₀(Ω₂)`; the `m`-th term uses the levels `0, …, m`.

  So well-foundedness can only hold for fragments with a bound on the levels (the two-level
  fragment is treated in the companion module on well-foundedness), or for a system with a
  side condition on the arguments of the higher collapses: G. Wilken, arXiv:2410.15953,
  §2.1, bounds the argument of `ϑ_j` by `Ω_{j+2}`, and in the simultaneous version
  (Definition 2.7 and Lemma 2.13 there) `α` is in the domain of `ϑ_m` only if the arguments of
  the collapses of level `> m` in `α` are below `α`, as in Buchholz's normal form for `D_v b`
  (all arguments of collapses of level `≥ v` inside `b` are below `b`).
-/
import OrdinalAnalysis.Ordinal.ThetaW.Order

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

/-- `tower j m = ϑ_j(ϑ_{j+1}(⋯ ϑ_{j+m-1}(Ω_{j+m+1}) ⋯))`, with `m` collapses. -/
def tower (j : ℕ) : ℕ → ThetaWTerm
  | 0 => Omega j
  | m + 1 => theta j (tower (j + 1) m)

@[simp] theorem tower_zero (j : ℕ) : tower j 0 = Omega j := rfl

@[simp] theorem tower_succ (j m : ℕ) : tower j (m + 1) = theta j (tower (j + 1) m) := rfl

theorem nf_tower : ∀ (m j : ℕ), NF (tower j m)
  | 0, j => nf_Omega j
  | m + 1, j => (nf_theta_iff j _).mpr (nf_tower m (j + 1))

/-- A term all of whose collapses have level `> k` has no level-`k` coefficients. -/
theorem E_tower_of_lt : ∀ (m : ℕ) {k j : ℕ}, k < j → E k (tower j m) = []
  | 0, _, _, _ => E_Omega _ _
  | m + 1, k, j, h => by
    rw [tower_succ, E_theta_of_lt h]
    exact E_tower_of_lt m (by omega)

/-- Each tower is below the previous one: `tower j (m+1) ≺ tower j m`. -/
theorem tower_succ_lt : ∀ (m j : ℕ), tower j (m + 1) < tower j m
  | 0, j => (theta_lt_Omega_iff j j _).mpr le_rfl
  | m + 1, j => by
    rw [tower_succ j (m + 1), tower_succ j m]
    refine theta_lt_theta_of_lt (tower_succ_lt m (j + 1)) ?_
    rw [E_tower_of_lt (m + 1) (Nat.lt_succ_self j)]
    simp

/-- The towers from level `0` on are countable terms: `tower 0 (m+1) ≺ Ω₁`. -/
theorem tower_zero_succ_lt_Omega0 (m : ℕ) : tower 0 (m + 1) < Omega 0 :=
  (theta_lt_Omega_iff 0 0 _).mpr le_rfl

end ThetaWTerm

namespace ThetaWNote

/-- The descending sequence `ϑ₀(Ω₂) ≻ ϑ₀(ϑ₁(Ω₃)) ≻ ⋯` as notations. -/
def descSeq (m : ℕ) : ThetaWNote :=
  ⟨ThetaWTerm.tower 0 (m + 1), ThetaWTerm.nf_tower (m + 1) 0⟩

theorem descSeq_succ_lt (m : ℕ) : descSeq (m + 1) < descSeq m :=
  ThetaWTerm.tower_succ_lt (m + 1) 0

private theorem not_acc_of_desc {β : Type} {r : β → β → Prop} (f : ℕ → β)
    (hf : ∀ n, r (f (n + 1)) (f n)) {a : β} (ha : Acc r a) : ∀ n, f n ≠ a := by
  induction ha with
  | intro a _ ih =>
  intro n hn
  exact ih (f (n + 1)) (hn ▸ hf n) (n + 1) rfl

/-- **The order on normal terms of all levels is not well founded.** -/
theorem not_wellFoundedLT : ¬ WellFoundedLT ThetaWNote := by
  intro h
  exact not_acc_of_desc descSeq descSeq_succ_lt (h.wf.apply (descSeq 0)) 0 rfl

end ThetaWNote

end OrdinalAnalysis
