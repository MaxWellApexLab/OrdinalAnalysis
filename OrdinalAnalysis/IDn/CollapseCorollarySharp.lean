/-
  **The sharp multi-level collapsing corollary** for `IDn n (WForms orderFormulas n)`,
  discharging `IDn.CollapseCorollarySharp` (`IDn/LowerSharp.lean`), and the sharp theorem
  `idn_theorem_sharp'` with `EmbedHyps` as its only hypothesis.

  Route (Freund, arXiv:2204.09321, Corollary 7.2, per level; Buchholz 1992, Theorem 4.8):

  1. The embedding (`Embed.lean`, sharp form) gives, at every nice operator, cut rank
     `OmegaPlus m = Ω_n + m` and height `Ω_n·2 + r` (Lean `Omega (n - 1)`, the top level).
     Take the operator `H_0 = HopS 0`.
  2. Raise the cut rank to `Ω_n + (m+1) = Ω̄_n + m` and run `elimination_iter` `m` times
     (Freund Exercise 7.1 (c)): none of the ranks `Ω̄_n + i = Ω_n + 1 + i` is an `Ω_{j+1}`,
     `j < n`. Result: cut rank `Ω̄_n = muBar n`, height `ω_m(Ω_n·2 + r)`.
  3. `collapse_zero_bound` at level `0` gives `b = ψ_0(ω^{Ω̄_n + Ω̄_n + ω_m(Ω_n·2+r)})`, and
     `psi0_hat_lt_c` bounds it by `c_n = ϑ_0(ϑ_n 0)`: the height lies below the principal
     `ϑ_n(0)` (`Ω_n ≺ ϑ_n(0)`, closure under `+`, `ω^·`) and has no level-`0` subterm.

  No predicative cut elimination and no `φ`-closed base are needed: the cut rank already sits
  inside `[Ω_n, Ω_n + ω)`, one level below the old (loose) `Ω_{n+1} + m`.
-/
import OrdinalAnalysis.IDn.LowerSharp
import OrdinalAnalysis.IDn.PredCut
import OrdinalAnalysis.IDn.Elimination

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.IDn.Upper

variable {n : ℕ}

/-! ### Cut ranks: `Ω_n + (m+1) = Ω̄_n + m`, and `Ω̄_n + i` is never an `Ω_{j+1}` -/

/-- `Ω_n + (m + 1) = Ω̄_n + m` (Lean: `Omega (n-1) + ofNat (m+1) = (Omega (n-1) + one) + ofNat m`). -/
theorem OmegaPlus_succ_eq_muBar_add (hn : 0 < n) (m : ℕ) :
    OmegaPlus (n := n) (m + 1) = Collapsing.muBar n + ThetaWNoteD.ofNat m := by
  obtain ⟨s, rfl⟩ : ∃ s, n = s + 1 := ⟨n - 1, by omega⟩
  show ThetaWNoteD.Omega (s + 1 - 1) + ThetaWNoteD.ofNat (m + 1) = _
  rw [Nat.add_sub_cancel, Collapsing.muBar_succ, ThetaWNoteD.add_assoc, ← ThetaWNoteD.ofNat_one,
    ThetaWNoteD.ofNat_add_ofNat_red, Nat.add_comm 1 m]

/-- `Ω̄_n + i ≠ Ω_{j+1}` for every level `j < n` (Lean `Omega j.val`): every such `Ω` is
`≤ Ω_n < Ω_n + 1 ≤ Ω̄_n + i`. -/
theorem muBar_add_ofNat_ne_Omega (hn : 0 < n) (i : ℕ) (j : Fin n) :
    Collapsing.muBar n + ThetaWNoteD.ofNat i ≠ ThetaWNoteD.Omega j.val := by
  intro heq
  obtain ⟨s, rfl⟩ : ∃ s, n = s + 1 := ⟨n - 1, by omega⟩
  rw [Collapsing.muBar_succ] at heq
  have hle : ThetaWNoteD.Omega j.val ≤ ThetaWNoteD.Omega s := by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ j.isLt) with h | h
    · exact le_of_lt (ThetaWNoteD.Omega_lt_Omega_iff.mpr h)
    · rw [h]
  have h1 : ThetaWNoteD.Omega s < ThetaWNoteD.Omega s + ThetaWNoteD.one + ThetaWNoteD.ofNat i :=
    lt_of_lt_of_le (ThetaWNoteD.Omega_lt_Omega_add_one s) (ThetaWNoteD.le_self_add_red _ _)
  rw [heq] at h1
  exact absurd (lt_of_le_of_lt hle h1) (lt_irrefl _)

/-! ### Heights: `ω_m(Ω_n·2 + r) ≺ ϑ_n(0)`, with no level-`0` subterm -/

/-- `Ω_n·2 + r ≺ ϑ_n(0)` (Lean `thetaZero (n-1)`): `Ω_n ≺ ϑ_n(0)`, which is principal. -/
theorem OmegaTwo_add_ofNat_lt_thetaZero (r : ℕ) :
    OmegaTwo (n := n) + ThetaWNoteD.ofNat r < ThetaWNoteD.thetaZero (n - 1) := by
  have hp := ThetaWNoteD.isPrin_thetaZero (n - 1)
  have hΩ := ThetaWNoteD.Omega_lt_thetaZero (n - 1)
  exact ThetaWNoteD.add_lt_prin hp (ThetaWNoteD.add_lt_prin hp hΩ hΩ)
    (ThetaWNoteD.ofNat_lt_prin hp r)

/-- A finite `ω`-tower over anything below `ϑ_{k+1}(0)` stays below it. -/
theorem omegaTower_lt_thetaZero_of_lt {k : ℕ} {x : ThetaWNoteD}
    (hx : x < ThetaWNoteD.thetaZero k) : ∀ m : ℕ, ThetaWNoteD.omegaTower m x < ThetaWNoteD.thetaZero k
  | 0 => hx
  | m + 1 => by
      rw [ThetaWNoteD.omegaTower_succ]
      exact ThetaWNoteD.omegaPow_lt_prin (ThetaWNoteD.isPrin_thetaZero k)
        (omegaTower_lt_thetaZero_of_lt hx m)

/-- `E_0` vanishes along a finite `ω`-tower. -/
theorem Ehull_omegaTower_eq_empty {x : ThetaWNoteD} (hx : ThetaWNoteD.Ehull 0 x = ∅) :
    ∀ m : ℕ, ThetaWNoteD.Ehull 0 (ThetaWNoteD.omegaTower m x) = ∅
  | 0 => hx
  | m + 1 => by
      rw [ThetaWNoteD.omegaTower_succ, ThetaWNoteD.Ehull_omegaPow_hull]
      exact Ehull_omegaTower_eq_empty hx m

/-- `E_0(Ω_n·2 + r) = ∅`. -/
theorem Ehull_OmegaTwo_add_ofNat (r : ℕ) :
    ThetaWNoteD.Ehull 0 (OmegaTwo (n := n) + ThetaWNoteD.ofNat r) = ∅ :=
  ThetaWNoteD.Ehull_add_eq_empty
    (ThetaWNoteD.Ehull_add_eq_empty (ThetaWNoteD.Ehull_Omega_hull 0 _)
      (ThetaWNoteD.Ehull_Omega_hull 0 _))
    (ThetaWNoteD.Ehull_ofNat_hull 0 r)

/-! ### The sharp collapsing corollary -/

/-- **The multi-level collapsing corollary at the sharp bound `c n`** (`CollapseCorollarySharp`,
proved): embedding output at `H_0`, `m`-fold predicative cut elimination below `Ω_n + ω`
down to `Ω̄_n`, collapsing at level `0`, and `psi0_hat_lt_c`. -/
theorem collapseCorollarySharp (hn : 0 < n) : CollapseCorollarySharp hn := by
  intro m r φ hφ d
  have hyp : Collapsing.CollapseHyps (WForms orderFormulas n) :=
    collapseHyps_of_levelBounded (wForms_positive orderFormulas n)
      (wForms_levelBounded orderFormulas n)
  have hN := ThetaWNoteD.HopS_nice ThetaWNoteD.zero
  -- cut rank `Ω_n + m ≤ Ω_n + (m+1) = Ω̄_n + m`
  have d₀ : IDnDerivable (WForms orderFormulas n) (Collapsing.muBar n + ThetaWNoteD.ofNat m)
      (ThetaWNoteD.HopS ThetaWNoteD.zero) (OmegaTwo (n := n) + ThetaWNoteD.ofNat r) [φ] := by
    rw [← OmegaPlus_succ_eq_muBar_add hn m]
    exact (d _ hN).mono_rank (OmegaPlus_le (Nat.le_succ m))
  -- `m` rounds of Freund Exercise 7.1 (c), down to cut rank `Ω̄_n`
  have d₁ := IDnDerivable.elimination_iter hN (wForms_levelBounded orderFormulas n) m
    (fun i _ j => muBar_add_ofNat_ne_Omega hn i j) d₀
  -- collapsing and boundedness at level `0`
  obtain ⟨b, hb, D⟩ := Collapsing.collapse_zero_bound hyp (le_refl n) (lvl0 hn) hφ d₁
  refine ⟨b, _, ThetaWNoteD.HopS_nice _, ?_, D⟩
  rw [hb, ← Collapsing.hat_zero]
  exact psi0_hat_lt_c hn le_rfl
    (omegaTower_lt_thetaZero_of_lt (OmegaTwo_add_ofNat_lt_thetaZero r) m)
    (Ehull_omegaTower_eq_empty (Ehull_OmegaTwo_add_ofNat r) m)

/-! ### The sharp theorem, `EmbedHyps` only -/

/-- **`IDn n (WForms orderFormulas n) ⊬ TI_{c n}(≺, X)`**, given `EmbedHyps` only. -/
theorem idn_lower_bound_sharp' (hn : 0 < n) (hyps : EmbedHyps (WForms orderFormulas n)) :
    ¬ IDn n (WForms orderFormulas n) ⊢ tiUptoSentence orderFormulas (Fin n) (ThetaWNoteD.c n) :=
  idn_lower_bound_sharp hn hyps (collapseCorollarySharp hn)

/-- **The Buchholz–Pohlers analysis of `ID_n`, sharp, given `EmbedHyps` only**: `ID_n` proves
transfinite induction up to every `a ≺ c_n`, and not up to `c_n = ϑ₀(ϑ_n 0)` itself. -/
theorem idn_theorem_sharp' (hn : 0 < n) (hyps : EmbedHyps (WForms orderFormulas n)) :
    (∀ a : ThetaWNoteD, a < ThetaWNoteD.c n →
        IDn n (WForms orderFormulas n) ⊢ tiUptoSentence orderFormulas (Fin n) a) ∧
      ¬ IDn n (WForms orderFormulas n) ⊢
        tiUptoSentence orderFormulas (Fin n) (ThetaWNoteD.c n) :=
  idn_theorem_sharp hn hyps (collapseCorollarySharp hn)

end IDn

end OrdinalAnalysis
