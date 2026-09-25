/-
  **The multi-level collapsing corollary** for `IDn n (WForms orderFormulas n)`, discharging
  `IDn.CollapseCorollary` (`IDn/LowerBound.lean`), and the lower bound without that hypothesis.

  Route (Buchholz 1992, Theorem 3.16 + Theorem 4.8; Freund, arXiv:2204.09321, Corollary 7.2):

  1. `embedding_theorem_xfree` gives, at every nice operator, cut rank `OmegaPlus m = Ω_n + m`
     and height `Ω_n·2 + r` (Lean `Omega (n - 1)`; this file's looser level-`n+1` route still
     applies, see `CollapseCorollarySharp.lean` for the sharp one).
  2. At the operator `H_{γ₀}`, `γ₀ = ω^{(Ω_{n+2}+1)+(Ω_{n+2}+1)}` (so `H_{γ₀}` is
     `φ_{n+1}`-closed, `phiClosed_HopS`), predicative cut elimination on the window
     `[Ω̄_n, Ω_{n+2})` (no `(Fix)`-level `Ω_{j+1}`, `j < n`, lies there) lowers the cut rank to
     `Ω̄_n = muBar n`.
  3. Theorem 4.8 (`Collapsing.collapse`) at level `0`, `γ = γ₀`, `Θ = ∅`, then boundedness
     (`CollapseHyps.bound`) caps the formula at the collapsed height `b = ψ_0(α̂) < Ω_1`, with
     operator `H_{α̂}`.
-/
import OrdinalAnalysis.IDn.LowerBound
import OrdinalAnalysis.IDn.PredCut

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.IDn.Upper

variable {n : ℕ}

/-- The base `γ₀ = ω^{(Ω_{n+2}+1)+(Ω_{n+2}+1)}` (Lean `Omega (n+1)`) of the operator at which
predicative cut elimination runs. -/
def collGamma0 (n : ℕ) : ThetaWNoteD :=
  ThetaWNoteD.omegaPow ((ThetaWNoteD.Omega (n + 1) + ThetaWNoteD.one) +
    (ThetaWNoteD.Omega (n + 1) + ThetaWNoteD.one))

theorem collGamma0_mem (n : ℕ) (X : Set ThetaWNoteD) :
    collGamma0 n ∈ ThetaWNoteD.HopS (collGamma0 n) X := by
  have h := ThetaWNoteD.HopS_nice (collGamma0 n)
  exact h.omegaPow_mem (h.add_mem (h.add_mem (h.Omega_mem _) h.one_mem)
    (h.add_mem (h.Omega_mem _) h.one_mem))

theorem phiClosed_collGamma0 (n : ℕ) :
    ThetaWNoteD.PhiClosed (n + 1) (ThetaWNoteD.HopS (collGamma0 n)) :=
  ThetaWNoteD.phiClosed_HopS le_rfl

/-- `[Ω̄_n, Ω_{n+2})` (Lean `[muBar n, Omega (n+1))`) contains no `Ω_{j+1}`, `j < n`. -/
theorem noOmega_muBar_top (hn : 0 < n) :
    ∀ c : ThetaWNoteD, Collapsing.muBar n ≤ c → c < ThetaWNoteD.Omega (n + 1) →
      ∀ j : Fin n, c ≠ ThetaWNoteD.Omega j.val := by
  intro c h1 _ j heq
  subst heq
  obtain ⟨s, rfl⟩ : ∃ s, n = s + 1 := ⟨n - 1, by omega⟩
  rw [Collapsing.muBar_succ] at h1
  have hle : ThetaWNoteD.Omega j.val ≤ ThetaWNoteD.Omega s := by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ j.isLt) with h | h
    · exact le_of_lt (ThetaWNoteD.Omega_lt_Omega_iff.mpr h)
    · rw [h]
  exact absurd (lt_of_le_of_lt hle (lt_of_lt_of_le (ThetaWNoteD.Omega_lt_Omega_add_one s) h1))
    (lt_irrefl _)

theorem Omega_lt_Omega_succ (n : ℕ) : ThetaWNoteD.Omega n < ThetaWNoteD.Omega (n + 1) :=
  ThetaWNoteD.Omega_lt_Omega_iff.mpr (Nat.lt_succ_self n)

theorem Omega_pred_lt_Omega_succ (n : ℕ) :
    ThetaWNoteD.Omega (n - 1) < ThetaWNoteD.Omega (n + 1) :=
  ThetaWNoteD.Omega_lt_Omega_iff.mpr (by omega)

theorem OmegaPlus_lt_Omega_succ (m : ℕ) :
    OmegaPlus (n := n) m < ThetaWNoteD.Omega (n + 1) :=
  ThetaWNoteD.add_lt_Omega (Omega_pred_lt_Omega_succ n)
    (ThetaWNoteD.ofNat_lt_prin (p := ThetaWNoteD.Omega (n + 1)) trivial m)

theorem OmegaTwo_add_lt_Omega_succ (r : ℕ) :
    OmegaTwo (n := n) + ThetaWNoteD.ofNat r < ThetaWNoteD.Omega (n + 1) :=
  ThetaWNoteD.add_lt_Omega
    (ThetaWNoteD.add_lt_Omega (Omega_pred_lt_Omega_succ n) (Omega_pred_lt_Omega_succ n))
    (ThetaWNoteD.ofNat_lt_prin (p := ThetaWNoteD.Omega (n + 1)) trivial r)

/-- **The multi-level collapsing corollary** (`CollapseCorollary`, proved). -/
theorem collapseCorollary (hn : 0 < n) : CollapseCorollary hn := by
  intro m r φ hφ d
  have hyp : Collapsing.CollapseHyps (WForms orderFormulas n) :=
    collapseHyps_of_levelBounded (wForms_positive orderFormulas n)
      (wForms_levelBounded orderFormulas n)
  have hN := ThetaWNoteD.HopS_nice (collGamma0 n)
  -- predicative cut elimination on `[Ω̄_n, Ω_{n+2})`
  have d₂ := predicative_cut_elim (wForms_levelBounded orderFormulas n) (noOmega_muBar_top hn)
    (OmegaPlus (n := n) m) (OmegaPlus_lt_Omega_succ m) (d _ hN) hN (phiClosed_collGamma0 n)
    (OmegaPlus_mem hN m) (OmegaTwo_add_lt_Omega_succ r)
  -- collapsing at level `0`
  have hΓ : ∀ ψ ∈ [φ], SigmaW (lvl0 hn) ψ := fun ψ hψ => by
    rw [List.mem_singleton.mp hψ]; exact hφ
  have hX : ThetaWNoteD.HullHypGe (lvl0 hn).val (collGamma0 n) ∅ :=
    fun _ _ _ _ _ => Set.empty_subset _
  have D := Collapsing.collapse hyp (le_refl n) (k := lvl0 hn) (γ := collGamma0 n) (X := ∅) hΓ
    (collGamma0_mem n ∅) hX (by rw [Collapsing.Hg_empty_eq]; exact d₂)
  rw [Collapsing.Hg_empty_eq] at D
  -- boundedness at the collapsed height
  let η := Collapsing.hat (collGamma0 n) (Collapsing.muBar n)
    (ThetaWNoteD.phiN (n + 1) (OmegaPlus (n := n) m) (OmegaTwo (n := n) + ThetaWNoteD.ofNat r))
  let b : StageAt (lvl0 hn).val :=
    ⟨Collapsing.psi (lvl0 hn).val η, le_of_lt (Collapsing.psi_lt_Omega _ _)⟩
  have hbH : b.1 ∈ ThetaWNoteD.HopS η ∅ :=
    Collapsing.psi_hat_mem hX (collGamma0_mem n ∅) d₂.height_mem
  exact ⟨b, ThetaWNoteD.HopS η, ThetaWNoteD.HopS_nice η, Collapsing.psi_lt_Omega _ _,
    hyp.bound (lvl0 hn) b (ThetaWNoteD.HopS_isOperator _) hbH le_rfl
      (Collapsing.psi_lt_Omega _ _) D⟩

/-- **`IDn n (WForms orderFormulas n) ⊬ TI_{Ω_1}(≺, X)`**, given `EmbedHyps` only. -/
theorem idn_lower_bound' (hn : 0 < n) (hyps : EmbedHyps (WForms orderFormulas n)) :
    ¬ IDn n (WForms orderFormulas n) ⊢
      tiUptoSentence orderFormulas (Fin n) (ThetaWNoteD.Omega 0) :=
  idn_lower_bound hn hyps (collapseCorollary hn)

end IDn

end OrdinalAnalysis
