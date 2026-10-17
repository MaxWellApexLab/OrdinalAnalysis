/-
  `ϑ₀ 0` is the least fixed point of `ω^·` on the domained multi-level ϑ-notation, and the
  supremum of the ω-tower over `0`.

  On `ThetaWNoteD` the fixed points of `omegaPow` are exactly the principal terms
  (`omegaPow_eq_self_iff`), so `ϑ₀ 0` is a fixed point by the normal form.  This file adds the
  two facts that make `ϑ₀ 0` the notation's own `ε₀`, stated against the notation's order and
  its own `omegaPow`, with no reading into `Ordinal`:

  * `isLeast_epsilonZero`: `ϑ₀ 0` is the *least* fixed point of `omegaPow`.  It rests on the
    raw-term form `ThetaWTerm.theta_zero_zero_le_of_ofList_eq` (every term `t` with
    `ofList [t] = t` satisfies `ϑ₀ 0 ≤ t`, no normal-form or domain hypothesis): such a `t` is
    `Ω_j`, `ϑ_j β` with `j > 0`, or `ϑ₀ β`, and each of these lies at or above `ϑ₀ 0` by a
    clause of the raw term order (`theta_lt_Omega_iff`, `theta_lt_theta_of_lt_level`,
    `theta_lt_theta_of_lt`).  Well-foundedness is not used, and the raw form uses no
    `Classical.choice`.
  * `exists_lt_omegaTower_of_lt_epsilonZero`: every notation below `ϑ₀ 0` lies below
    `ω_m(0)` for some `m` (`omegaTower`, `HullCofinal.lean`), and conversely every `ω_m(0)`
    lies below `ϑ₀ 0` (`omegaTower_zero_lt_epsilonZero`).  The proof is induction on the term
    length: a notation below `ϑ₀ 0` is not principal (by leastness), so it is a Cantor sum whose
    entries lie below `ϑ₀ 0` (`lt_prin_iff`), each entry is below some stage by induction, and
    the sum lies below `ω^·` of the largest of those stages (`lt_omegaPow_iff`).
-/
import OrdinalAnalysis.Ordinal.ThetaW.HullCofinal

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

/-- Raw form of leastness: every term that `ofList [·]` fixes lies at or above `ϑ₀ 0`. -/
theorem theta_zero_zero_le_of_ofList_eq {t : ThetaWTerm} (h : ofList [t] = t) :
    theta 0 zero ≤ t := by
  cases t with
  | Omega j => exact Or.inl ((theta_lt_Omega_iff 0 j _).mpr (Nat.zero_le j))
  | theta j b =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · by_cases hb : b = sum []
      · subst hb; exact Or.inr rfl
      · left
        apply theta_lt_theta_of_lt (nil_lt_of_ne hb)
        intro g hg
        simp at hg
    · exact Or.inl (theta_lt_theta_of_lt_level _ _ hj)
  | sum xs =>
    exfalso
    have hof : ofList [sum xs] = sum [sum xs] := rfl
    rw [hof] at h
    injection h with h
    have := congrArg sizeOf h
    simp at this
    omega

end ThetaWTerm

namespace ThetaWNoteD

open ThetaWTerm

/-! ### The notation `ϑ₀ 0` -/

theorem dom_theta_zero_zero : ThetaWTerm.Dom (ThetaWTerm.theta 0 ThetaWTerm.zero) :=
  ThetaWTerm.dom_theta_of_G_nil ThetaWTerm.dom_zero (ThetaWTerm.G_nil 0)

/-- `ϑ₀ 0`, the notation for `ε₀`. -/
def epsilonZero : ThetaWNoteD :=
  ⟨ThetaWTerm.theta 0 ThetaWTerm.zero,
    (ThetaWTerm.nf_theta_iff _ _).mpr ThetaWTerm.nf_zero, dom_theta_zero_zero⟩

theorem epsilonZero_val : epsilonZero.1 = ThetaWTerm.theta 0 ThetaWTerm.zero := rfl

theorem isPrin_epsilonZero : ThetaWTerm.IsPrin epsilonZero.1 := trivial

/-! ### `ϑ₀ 0` is the least fixed point of `omegaPow` -/

/-- `ω^(ϑ₀ 0) = ϑ₀ 0`. -/
theorem omegaPow_epsilonZero : omegaPow epsilonZero = epsilonZero :=
  omegaPow_eq_self_iff.mpr isPrin_epsilonZero

/-- Every fixed point of `omegaPow` lies at or above `ϑ₀ 0`. -/
theorem epsilonZero_le_of_omegaPow_eq {a : ThetaWNoteD} (h : omegaPow a = a) :
    epsilonZero ≤ a :=
  le_iff.mpr (ThetaWTerm.theta_zero_zero_le_of_ofList_eq (congrArg Subtype.val h))

/-- **`ϑ₀ 0` is the least fixed point of `ω^·`.** -/
theorem isLeast_epsilonZero : IsLeast {a : ThetaWNoteD | omegaPow a = a} epsilonZero :=
  ⟨omegaPow_epsilonZero, fun _ ha => epsilonZero_le_of_omegaPow_eq ha⟩

/-- No notation below `ϑ₀ 0` is a fixed point of `ω^·`. -/
theorem omegaPow_ne_self_of_lt_epsilonZero {a : ThetaWNoteD} (ha : a < epsilonZero) :
    omegaPow a ≠ a :=
  fun h => absurd (epsilonZero_le_of_omegaPow_eq h) (not_le.mpr ha)

/-! ### `ϑ₀ 0` is the supremum of the ω-tower over `0` -/

theorem omegaTower_zero_lt_succ : ∀ m : ℕ, omegaTower m zero < omegaTower (m + 1) zero
  | 0 => zero_lt_one
  | m + 1 => omegaPow_lt_omegaPow (omegaTower_zero_lt_succ m)

theorem omegaTower_zero_mono {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    omegaTower m₁ zero ≤ omegaTower m₂ zero := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (le_of_lt (omegaTower_zero_lt_succ _))

/-- Every stage `ω_m(0)` of the tower lies below `ϑ₀ 0`. -/
theorem omegaTower_zero_lt_epsilonZero : ∀ m : ℕ, omegaTower m zero < epsilonZero
  | 0 => lt_iff.mpr (ThetaWTerm.nil_lt_theta 0 _)
  | m + 1 => omegaPow_lt_prin (p := epsilonZero) isPrin_epsilonZero
      (omegaTower_zero_lt_epsilonZero m)

/-- A finite list of terms, each below some stage of the tower, lies below a single stage. -/
theorem exists_omegaTower_zero_bound (xs : List ThetaWTerm)
    (h : ∀ e ∈ xs, ∃ m, e < (omegaTower m zero).1) :
    ∃ M, ∀ e ∈ xs, e < (omegaTower M zero).1 := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
    obtain ⟨m, hm⟩ := h x (by simp)
    obtain ⟨M, hM⟩ := ih (fun e he => h e (by simp [he]))
    refine ⟨max m M, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ThetaWTerm.lt_of_lt_of_le' hm (le_iff.mp (omegaTower_zero_mono (le_max_left _ _)))
    · exact ThetaWTerm.lt_of_lt_of_le' (hM e he)
        (le_iff.mp (omegaTower_zero_mono (le_max_right _ _)))

theorem exists_lt_omegaTower_of_lt_epsilonZero_aux (N : ℕ) :
    ∀ a : ThetaWNoteD, ThetaWTerm.l a.1 ≤ N → a < epsilonZero →
      ∃ m, a < omegaTower m zero := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro a hl ha
  have hnp : ¬ ThetaWTerm.IsPrin a.1 := fun hp =>
    omegaPow_ne_self_of_lt_epsilonZero ha (omegaPow_eq_self_iff.mpr hp)
  have hbelow := (lt_prin_iff (p := epsilonZero) isPrin_epsilonZero).mp ha
  have hent : ∀ e ∈ a.entries, ∃ m, e < (omegaTower m zero).1 := by
    intro e he
    obtain ⟨t, hnf, hdom⟩ := a
    cases t with
    | Omega k => exact absurd trivial hnp
    | theta k b => exact absurd trivial hnp
    | sum xs =>
      have hex : e ∈ xs := he
      have hle : ThetaWTerm.l e < N := lt_of_lt_of_le (ThetaWTerm.l_lt_of_mem hex) hl
      let e' : ThetaWNoteD :=
        ⟨e, (cnf_entries ⟨_, hnf, hdom⟩).nf he, dom_entries ⟨_, hnf, hdom⟩ e he⟩
      exact ih (ThetaWTerm.l e) hle e' le_rfl (hbelow e he)
  obtain ⟨M, hM⟩ := exists_omegaTower_zero_bound a.entries hent
  exact ⟨M + 1, lt_omegaPow_iff.mpr hM⟩

/-- **`ϑ₀ 0` is the supremum of `0, ω^0, ω^ω^0, …`**: every notation below it lies below
some stage of the tower. -/
theorem exists_lt_omegaTower_of_lt_epsilonZero {a : ThetaWNoteD} (ha : a < epsilonZero) :
    ∃ m, a < omegaTower m zero :=
  exists_lt_omegaTower_of_lt_epsilonZero_aux _ a le_rfl ha

/-- Below `ϑ₀ 0` means below some stage of the ω-tower over `0`. -/
theorem lt_epsilonZero_iff {a : ThetaWNoteD} :
    a < epsilonZero ↔ ∃ m, a < omegaTower m zero :=
  ⟨exists_lt_omegaTower_of_lt_epsilonZero,
    fun ⟨m, hm⟩ => lt_trans hm (omegaTower_zero_lt_epsilonZero m)⟩

end ThetaWNoteD

end OrdinalAnalysis
