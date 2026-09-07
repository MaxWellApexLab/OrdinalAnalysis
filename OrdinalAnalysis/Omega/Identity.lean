/-
  The identity sequent for arbitrary formulas.

  The calculus has identity only for atoms.  Every formula `φ` still has a
  derivation of `φ, ∼φ`, by induction on `φ`, at a finite height: each
  connective costs two inferences, and for the quantifiers the ω-rule's
  premises are the instances, whose complexity is that of the body — the one
  property the instantiation is required to have.

  This is what the replay of the induction axiom consumes: it needs `ψ(n̄+1)`
  from `∼ψ(n̄+1)`, for a `ψ` that may contain `X` and is not an atom.
-/
import OrdinalAnalysis.Omega.Calculus

namespace OrdinalAnalysis

open LO LO.FirstOrder

variable {L : Language}

namespace OmegaDerivable

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals L} {I : Instantiation L}

/-- **Identity, for members.**  A sequent containing a formula of complexity at
most `c` together with its negation is derivable at height `2c`. -/
theorem identity_of_mem {r : ℕ} :
    ∀ (c : ℕ) (φ : Proposition L), φ.complexity ≤ c →
      ∀ {Θ : Sequent L}, φ ∈ Θ → ∼φ ∈ Θ →
        OmegaDerivable A I r (OrdinalNotation.ofNat (2 * c) : O) Θ := by
  intro c
  induction c with
  | zero =>
      intro φ hc Θ h₁ h₂
      cases φ with
      | verum => exact of_mem_verum h₁
      | falsum => exact of_mem_verum h₂
      | rel rl v => exact of_mem_identity rl v h₁ h₂
      | nrel rl v => exact of_mem_identity rl v h₂ h₁
      | and φ ψ => simp at hc
      | or φ ψ => simp at hc
      | all φ => simp at hc
      | exs φ => simp at hc
  | succ c ih =>
      intro φ hc Θ h₁ h₂
      have hlt₁ : (OrdinalNotation.ofNat (2 * c) : O) < OrdinalNotation.ofNat (2 * c + 1) :=
        OrdinalNotation.ofNat_lt_ofNat (by omega)
      have hlt₂ : (OrdinalNotation.ofNat (2 * c + 1) : O) < OrdinalNotation.ofNat (2 * (c + 1)) :=
        OrdinalNotation.ofNat_lt_ofNat (by omega)
      cases φ with
      | verum => exact of_mem_verum h₁
      | falsum => exact of_mem_verum h₂
      | rel rl v => exact of_mem_identity rl v h₁ h₂
      | nrel rl v => exact of_mem_identity rl v h₂ h₁
      | and φ ψ =>
          simp only [Semiformula.complexity_and'] at hc
          have h₂' : (∼φ ⋎ ∼ψ) ∈ Θ := h₂
          -- `or` on `∼φ ⋎ ∼ψ`, then `and` on `φ ⋏ ψ` inside the enlarged context.
          refine drop_head (OmegaDerivable.or hlt₂ ?_) h₂'
          refine drop_head (OmegaDerivable.and (Γ := ∼φ :: ∼ψ :: Θ) hlt₁ hlt₁ ?_ ?_)
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h₁))
          · exact ih φ (by omega) List.mem_cons_self (by simp)
          · exact ih ψ (by omega) List.mem_cons_self (by simp)
      | or φ ψ =>
          simp only [Semiformula.complexity_or'] at hc
          have h₂' : (∼φ ⋏ ∼ψ) ∈ Θ := h₂
          refine drop_head (OmegaDerivable.and hlt₂ hlt₂ ?_ ?_) h₂'
          · refine drop_head (OmegaDerivable.or (Γ := ∼φ :: Θ) hlt₁ ?_)
              (List.mem_cons_of_mem _ h₁)
            exact ih φ (by omega) List.mem_cons_self (by simp)
          · refine drop_head (OmegaDerivable.or (Γ := ∼ψ :: Θ) hlt₁ ?_)
              (List.mem_cons_of_mem _ h₁)
            exact ih ψ (by omega) (by simp) (by simp)
      | all φ =>
          simp only [Semiformula.complexity_all'] at hc
          have h₂' : (∃¹ ∼φ) ∈ Θ := h₂
          refine drop_head (OmegaDerivable.omegaRule (Γ := Θ)
            (fun _ => OrdinalNotation.ofNat (2 * c + 1)) (fun _ => hlt₂) (fun n => ?_)) h₁
          refine drop_head (OmegaDerivable.exs (Γ := I.inst φ n :: Θ) n hlt₁ ?_)
            (List.mem_cons_of_mem _ h₂')
          rw [Instantiation.inst_neg]
          exact ih (I.inst φ n) (by rw [Instantiation.complexity_inst]; omega)
            (by simp) List.mem_cons_self
      | exs φ =>
          simp only [Semiformula.complexity_exs'] at hc
          have h₂' : (∀¹ ∼φ) ∈ Θ := h₂
          refine drop_head (OmegaDerivable.omegaRule (Γ := Θ)
            (fun _ => OrdinalNotation.ofNat (2 * c + 1)) (fun _ => hlt₂) (fun n => ?_)) h₂'
          rw [Instantiation.inst_neg]
          refine drop_head (OmegaDerivable.exs (Γ := ∼I.inst φ n :: Θ) n hlt₁ ?_)
            (List.mem_cons_of_mem _ h₁)
          exact ih (I.inst φ n) (by rw [Instantiation.complexity_inst]; omega)
            List.mem_cons_self (by simp)

/-- **Identity.** -/
theorem identity_general {r : ℕ} (φ : Proposition L) :
    OmegaDerivable A I r (OrdinalNotation.ofNat (2 * φ.complexity) : O) [φ, ∼φ] :=
  identity_of_mem φ.complexity φ le_rfl (by simp) (by simp)

end OmegaDerivable

end OrdinalAnalysis
