/-
  Discreteness of the order on `ThetaWNoteD`: `a ≺ b → succ a ≼ b`, i.e. no domain notation
  sits strictly between `a` and `a + 1`.

  This is pure order combinatorics on Cantor-normal-form exponent lists: `ThetaW/Arith.lean`
  already gives `lt_iff_entries`/`le_iff_entries` (the order of domain notations is the
  lexicographic order of their exponent lists), `succ a := nadd a one` and
  `entries_nadd_one : (succ a).entries = a.entries ++ [sum []]` (appending one more trailing
  `0`-exponent). The content here is the generic list fact `sum xs < sum ys → sum (xs ++
  [sum []]) ≤ sum ys`: a strict lexicographic increase between two exponent lists always leaves
  room for one more trailing zero exponent on the smaller side (proved by induction on `xs`,
  following the same case split as `ThetaW/Basic.lean`'s `cons_lt_cons_iff`).

  Not needed by the direct proof of Buchholz 1992's `φ.4` (`phi_lt_phi_of_lt_left`,
  `ThetaW/VeblenOrder2.lean`) — that proof instead bounds `phiArg`'s "`ρ`-part" and "`β`-part"
  directly via `omegaMulOmega_lt_omegaMulOmega` and a generic append-domination lemma, sidestepping
  the "successor gap" `omegaMulOmega k ρ + Ω_{k+1} ≤ omegaMulOmega k ρ'` that an earlier route
  anticipated needing this lemma for. Proved here anyway, as a reusable discreteness fact.
-/
import OrdinalAnalysis.Ordinal.ThetaW.Arith

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWTerm

/-- A strict lexicographic increase between two Cantor-exponent lists leaves room for one more
trailing `0`-exponent on the smaller side: `sum xs ≺ sum ys → sum (xs ++ [sum []]) ≼ sum ys`.
Induction on `xs` (generalizing `ys`), following the case split of `cons_lt_cons_iff`: whenever
the lexicographic comparison is decided by a strict difference at some position, appending a
trailing `sum []` (the global minimum, `nil_le`) after the shorter list cannot push it past `ys`;
whenever `xs` runs out first (forcing `ys` to continue), the extra trailing `sum []` competes
against `ys`'s next entry via the same `nil_le`/`cons_lt_cons_iff` step one level down. -/
theorem sum_append_nil_le_of_lt :
    ∀ {xs ys : List ThetaWTerm}, sum xs < sum ys → sum (xs ++ [sum []]) ≤ sum ys
  | [], ys, h => by
      cases ys with
      | nil => exact absurd h not_nil_lt_nil
      | cons y ys' =>
        rcases nil_le y with hlt | heq
        · exact le_of_lt' ((cons_lt_cons_iff _ _ _ _).mpr (Or.inl hlt))
        · subst heq
          cases ys' with
          | nil => exact le_refl' _
          | cons y' ys'' =>
              exact le_of_lt' ((cons_lt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, nil_lt_cons _ _⟩))
  | x :: xs', ys, h => by
      cases ys with
      | nil => exact absurd h (not_cons_lt_nil x xs')
      | cons y ys' =>
        show sum (x :: (xs' ++ [sum ([] : List ThetaWTerm)])) ≤ sum (y :: ys')
        rcases (cons_lt_cons_iff _ _ _ _).mp h with hxy | ⟨rfl, hrest⟩
        · exact le_of_lt' ((cons_lt_cons_iff _ _ _ _).mpr (Or.inl hxy))
        · rcases sum_append_nil_le_of_lt hrest with ihlt | iheq
          · exact le_of_lt' ((cons_lt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, ihlt⟩))
          · rw [sum.inj iheq]

end ThetaWTerm

namespace ThetaWNoteD

open ThetaWTerm

/-- **Discreteness**: `a ≺ b → succ a ≼ b` for domain notations — no domain notation lies
strictly between `a` and `succ a = a ⊕ 1`. -/
theorem succ_le_of_lt {a b : ThetaWNoteD} (h : a < b) : succ a ≤ b := by
  rw [le_iff_entries, succ, entries_nadd_one]
  exact ThetaWTerm.sum_append_nil_le_of_lt (lt_iff_entries.mp h)

end ThetaWNoteD

end OrdinalAnalysis
