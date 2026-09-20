/-
  The second cut-elimination theorem for `ACA_∞` (Afshari–Rathjen 2012, Thm 4):

      ⊢^α_ω Γ   ⇒   ⊢^{ε_α}_0 Γ.

  A derivation at rank `ω` has cuts on arithmetical formulas only — every
  set-quantifier cut has already been removed by the first cut-elimination
  theorem, which brings any rank `ω + k` down to `ω` at the cost of a `k`-fold
  `ω`-tower.  What is left is the elimination of the *finitely ranked* cuts, and
  the point is that it costs `α ↦ ε_α` rather than another tower: by induction
  on the derivation, a cut on `φ` of finite rank between two already cut-free
  premises at heights `ε_β`, `ε_γ` (`β, γ < α`) is reduced once and then its
  finitely many residual rank levels are eliminated, landing at height
  `ω_k(ε_β ⊕ ε_γ ⊕ ε_β ⊕ ε_γ)`, which is below `ε_α` because `ε_α` is an
  ε-number — closed under `ω ^ ·` and the natural sum — and `ε` is monotone.

  That is the whole mechanism of `ε₀ → ε_{ε₀}`, and it uses exactly three
  facts about `ε`, collected in `EpsilonStructure`; `Gamma0Note` supplies them
  from `Ordinal/Veblen/Epsilon.lean`.  The finitely many residual levels are
  walked with `Chain`, and the one fact about `NONote` needed is that every
  notation below `ω` is reached from `0` by finitely many predecessor steps
  (`chain_of_lt_omegaN`), read off `ONote.repr_ofNat`.
-/
import OrdinalAnalysis.ACAOmega.Reduction
import OrdinalAnalysis.Ordinal.Veblen.Instance

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA

variable {L : FirstOrder.Language}

/-! ### ε-numbers, abstractly -/

/-- An ε-operation on a notation system: strictly monotone, with every value
closed under `ω ^ ·` and the natural sum.  These are the only properties of
`α ↦ ε_α` the second cut-elimination theorem uses. -/
structure EpsilonStructure (O : Type) [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O] where
  epsilon : O → O
  epsilon_lt_epsilon : ∀ {a b : O}, a < b → epsilon a < epsilon b
  omegaPow_lt_epsilon : ∀ {a x : O}, x < epsilon a → OrdinalNotation.omegaPow x < epsilon a
  nadd_lt_epsilon : ∀ {a x y : O}, x < epsilon a → y < epsilon a →
    OrdinalNotation.nadd x y < epsilon a

namespace EpsilonStructure

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- The `ω`-tower does not escape an ε-number. -/
theorem omegaTower_lt_epsilon (E : EpsilonStructure O) {a : O} :
    ∀ (k : ℕ) (x : O), x < E.epsilon a → OrdinalNotation.omegaTower k x < E.epsilon a
  | 0, _, h => h
  | (k + 1), x, h => by
    rw [OrdinalNotation.omegaTower_succ]
    exact E.omegaTower_lt_epsilon k _ (E.omegaPow_lt_epsilon h)

/-- The reduction lemma's doubled bound does not escape an ε-number. -/
theorem redOrd_lt_epsilon (E : EpsilonStructure O) {a x y : O} (hx : x < E.epsilon a)
    (hy : y < E.epsilon a) : OrdinalNotation.redOrd x y < E.epsilon a := by
  have h₁ : OrdinalNotation.nadd x y < E.epsilon a := E.nadd_lt_epsilon hx hy
  exact E.nadd_lt_epsilon h₁ h₁

end EpsilonStructure

/-- `Gamma0Note` carries the ε-numbers. -/
def Gamma0Note.epsilonStructure : EpsilonStructure Gamma0Note where
  epsilon := Gamma0Note.epsilonNote
  epsilon_lt_epsilon := fun h => Gamma0Note.epsilon_lt_epsilon h
  omegaPow_lt_epsilon := fun h => Gamma0Note.omegaPow_lt_epsilon h
  nadd_lt_epsilon := fun hx hy => Gamma0Note.nadd_lt_epsilon hx hy

/-! ### Finite ranks are finitely many predecessor steps from `0` -/

namespace OmegaDerivable₂

/-- A notation whose value is the natural number `n` is reached from `0` in `n`
predecessor steps. -/
theorem chain_of_repr : ∀ (n : ℕ) (a : NONote), NONote.repr a = n → Chain n 0 a
  | 0, a, h => by
      show NONote.repr a ≤ NONote.repr 0
      rw [h]
      simp
  | n + 1, a, h => by
      have hr : NONote.repr (NONote.ofNat n) = n := ONote.repr_ofNat n
      refine ⟨NONote.ofNat n, ?_, chain_of_repr n (NONote.ofNat n) hr⟩
      intro b hb
      show NONote.repr b ≤ NONote.repr (NONote.ofNat n)
      have hb' : NONote.repr b < NONote.repr a := hb
      rw [h, Nat.cast_succ, Ordinal.add_one_eq_succ] at hb'
      rw [hr]
      exact Order.lt_succ_iff.mp hb'

theorem repr_omegaN : NONote.repr omegaN = Ordinal.omega0 := by
  show ONote.repr (NONote.omegaPow (NONote.ofNat 1)).1 = _
  rw [NONote.repr_omegaPow]
  have h1 : ONote.repr (NONote.ofNat 1).1 = 1 := by
    show ONote.repr (ONote.ofNat 1) = 1
    simp
  rw [h1, Ordinal.opow_one]

/-- **Every rank below `ω` is a finite chain from `0`.** -/
theorem chain_of_lt_omegaN (a : NONote) (h : a < omegaN) : ∃ k, Chain k 0 a := by
  have h' : NONote.repr a < Ordinal.omega0 := by
    have : NONote.repr a < NONote.repr omegaN := h
    rwa [repr_omegaN] at this
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp h'
  exact ⟨n, chain_of_repr n a hn⟩

/-! ### The theorem -/

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals₂ L} {I : Instantiation₂ L}

/-- **The second cut-elimination theorem** (Afshari–Rathjen Thm 4).  A derivation
at rank `ω` — cuts on arithmetical formulas only — at height `α` becomes cut free
at height `ε_α`. -/
theorem secondCutElimination (P : SubstProvider A I) (E : EpsilonStructure O) :
    ∀ {α : O} {Γ : SecondOrder.Sequent L}, OmegaDerivable₂ A I omegaN α Γ →
      OmegaDerivable₂ A I 0 (E.epsilon α) Γ := by
  intro α Γ h
  induction h with
  | atom h => exact .atom h
  | identity φ => exact .identity φ
  | verum => exact .verum
  | or hlt _ ih => exact .or (E.epsilon_lt_epsilon hlt) ih
  | and hb hc _ _ ihp ihq =>
      exact .and (E.epsilon_lt_epsilon hb) (E.epsilon_lt_epsilon hc) ihp ihq
  | omegaRule f hf _ ih =>
      exact .omegaRule (fun n => E.epsilon (f n)) (fun n => E.epsilon_lt_epsilon (hf n)) ih
  | exs n hlt _ ih => exact .exs n (E.epsilon_lt_epsilon hlt) ih
  | all₂ hlt _ ih => exact .all₂ (E.epsilon_lt_epsilon hlt) ih
  | exs₂ hψ hlt _ ih => exact .exs₂ hψ (E.epsilon_lt_epsilon hlt) ih
  | contraction ss _ ih => exact .contraction ss ih
  | @cut α' β' γ' φ Γ₁ Γ₂ hrank hb hc _ _ ihp ihn =>
      -- Reduce the cut at its own rank, then walk the finitely many levels down.
      obtain ⟨k, hch⟩ := chain_of_lt_omegaN (rank φ) hrank
      have hkey := reduction P (E.epsilon β') (E.epsilon γ') (Θ := Γ₁ ++ Γ₂) le_rfl
        (ihp.mono_rank (NONote.zero_le' _))
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr (List.mem_append_left _ hx))
        (ihn.mono_rank (NONote.zero_le' _))
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr (List.mem_append_right _ hx))
      have hfree := cutElimination_chain P k hch hkey
      refine hfree.mono_ord (le_of_lt (E.omegaTower_lt_epsilon k _ ?_))
      exact E.redOrd_lt_epsilon (E.epsilon_lt_epsilon hb) (E.epsilon_lt_epsilon hc)

/-- **Both theorems together.**  Rank `ω + k` at height `α` becomes cut free at
height `ε_{ω_k(α)}`. -/
theorem cutElimination_epsilon (P : SubstProvider A I) (E : EpsilonStructure O)
    {k : ℕ} {ρ' : NONote} (hch : Chain k omegaN ρ') {α : O} {Γ : SecondOrder.Sequent L}
    (h : OmegaDerivable₂ A I ρ' α Γ) :
    OmegaDerivable₂ A I 0 (E.epsilon (OrdinalNotation.omegaTower k α)) Γ :=
  secondCutElimination P E (cutElimination_chain P k hch h)

/-- The second cut-elimination theorem at heights in `Gamma0Note`. -/
theorem secondCutElimination_Gamma0 (P : SubstProvider A I) {α : Gamma0Note}
    {Γ : SecondOrder.Sequent L} (h : OmegaDerivable₂ A I omegaN α Γ) :
    OmegaDerivable₂ A I 0 (Gamma0Note.epsilonNote α) Γ :=
  secondCutElimination P Gamma0Note.epsilonStructure h

/-- The raw instantiation: both theorems, unconditionally. -/
theorem cutElimination_epsilon_raw (num : ℕ → FirstOrder.SyntacticTerm L)
    {k : ℕ} {ρ' : NONote} (hch : Chain k omegaN ρ') {α : Gamma0Note}
    {Γ : SecondOrder.Sequent L} (h : OmegaDerivable₂ A (Instantiation₂.raw num) ρ' α Γ) :
    OmegaDerivable₂ A (Instantiation₂.raw num) 0
      (Gamma0Note.epsilonNote (OrdinalNotation.omegaTower k α)) Γ :=
  cutElimination_epsilon (rawProvider A num) Gamma0Note.epsilonStructure hch h

end OmegaDerivable₂

end OrdinalAnalysis.ACAOmega
