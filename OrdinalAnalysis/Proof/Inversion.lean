/-
  Inversion for the invertible rules.

  The reduction lemma needs to take a derivation that has a disjunction
  available in its sequent and turn it into one that has the two disjuncts
  available.  In a one-sided Tait calculus the disjunction rule is invertible,
  and inverting it costs nothing in either index.

  The statement is in *membership* form — `φ ⋎ ψ ∈ Γ` rather than `Γ = (φ ⋎ ψ) :: Γ'`
  — because Foundation's structural rule is subset-based.  With a head-shaped
  statement the `contraction` case is unprovable: from `Δ ⊆ (φ ⋎ ψ) :: Γ'` one
  learns nothing about the shape of `Δ`.
-/
import OrdinalAnalysis.Proof.Weakening

namespace OrdinalAnalysis

open LO LO.FirstOrder LO.FirstOrder.Derivation
open ONote

variable {L : Language}

namespace BoundedDerivable

/-- Inversion for `⋎`: if a sequent containing `φ ⋎ ψ` is derivable, then so is
the sequent with `φ` and `ψ` made available, at the same ordinal and rank.

`φ` and `ψ` are quantified *inside* the induction.  They have to be: the `∀`
rule shifts its context, so the induction hypothesis is applied at `shift φ`
and `shift ψ`, not at `φ` and `ψ`. -/
theorem inv_or {r : ℕ} :
    ∀ {α : NONote} {Γ : Sequent L}, BoundedDerivable r α Γ →
      ∀ {φ ψ : Proposition L}, (φ ⋎ ψ) ∈ Γ →
        BoundedDerivable r α (φ :: ψ :: Γ) := by
  intro α Γ h
  induction h with
  | identity rl v =>
      intro φ ψ _
      exact .contraction (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
        (.identity rl v)
  | verum =>
      intro φ ψ _
      exact .contraction (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) .verum
  | @or α β χ ρ Γ' hlt hd ih =>
      intro φ ψ hmem
      by_cases hcase : (φ ⋎ ψ) = (χ ⋎ ρ)
      · have hφ : φ = χ := by injection hcase
        have hψ : ψ = ρ := by injection hcase
        subst hφ; subst hψ
        refine .contraction ?_ (hd.mono_ord (le_of_lt hlt))
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      · have hmem' : (φ ⋎ ψ) ∈ χ :: ρ :: Γ' := by
          simp only [List.mem_cons] at hmem ⊢
          rcases hmem with h | h
          · exact absurd h hcase
          · tauto
        have key := ih hmem'
        have step : BoundedDerivable r β (χ :: ρ :: (φ :: ψ :: Γ')) := by
          refine .contraction ?_ key
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
        refine .contraction ?_ (BoundedDerivable.or hlt step)
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @and α β γ χ ρ Γ' hβ hγ hdp hdq ihp ihq =>
      intro φ ψ hmem
      have hmemΓ : (φ ⋎ ψ) ∈ Γ' := by
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h
        · exact absurd h (by simp)
        · exact h
      have kp : BoundedDerivable r β (χ :: (φ :: ψ :: Γ')) := by
        refine .contraction ?_ (ihp (by simp only [List.mem_cons]; tauto))
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      have kq : BoundedDerivable r γ (ρ :: (φ :: ψ :: Γ')) := by
        refine .contraction ?_ (ihq (by simp only [List.mem_cons]; tauto))
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      refine .contraction ?_ (BoundedDerivable.and hβ hγ kp kq)
      intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @all α β χ Γ' hlt hd ih =>
      intro φ ψ hmem
      have hmemΓ : (φ ⋎ ψ) ∈ Γ' := by
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h
        · exact absurd h (by simp)
        · exact h
      have hshift : (Rewriting.shift φ ⋎ Rewriting.shift ψ) ∈ Γ'⁺ := by
        have h0 : (Rewriting.shift (φ ⋎ ψ)) ∈ Γ'⁺ :=
          LawfulSyntacticRewriting.mem_shifts_iff.mpr hmemΓ
        simpa using h0
      have key := ih (by simp only [List.mem_cons]; exact Or.inr hshift)
      have step : BoundedDerivable r β (χ.free :: (φ :: ψ :: Γ')⁺) := by
        refine .contraction ?_ key
        intro x hx; simp only [Rewriting.shifts_cons, List.mem_cons] at hx ⊢; tauto
      refine .contraction ?_ (BoundedDerivable.all hlt step)
      intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @exs α β χ Γ' t hlt hd ih =>
      intro φ ψ hmem
      have hmemΓ : (φ ⋎ ψ) ∈ Γ' := by
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih (by simp only [List.mem_cons]; tauto)
      have step : BoundedDerivable r β (χ/[t] :: (φ :: ψ :: Γ')) := by
        refine .contraction ?_ key
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      refine .contraction ?_ (BoundedDerivable.exs t hlt step)
      intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @contraction α Δ Γ' ss hd ih =>
      intro φ ψ hmem
      by_cases hin : (φ ⋎ ψ) ∈ Δ
      · refine .contraction ?_ (ih hin)
        intro x hx; simp only [List.mem_cons] at hx ⊢
        rcases hx with h | h | h
        · tauto
        · tauto
        · exact Or.inr (Or.inr (ss h))
      · refine .contraction ?_ hd
        intro x hx
        simp only [List.mem_cons]
        exact Or.inr (Or.inr (ss hx))
  | @cut α β γ χ Γ₁ Γ₂ hc hβ hγ hdp hdn ihp ihn =>
      intro φ ψ hmem
      rcases List.mem_append.mp hmem with h | h
      · have key := ihp (by simp only [List.mem_cons]; tauto)
        have step : BoundedDerivable r β (χ :: (φ :: ψ :: Γ₁)) := by
          refine .contraction ?_ key
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
        refine .contraction ?_ (BoundedDerivable.cut hc hβ hγ step hdn)
        intro x hx
        simp only [List.mem_cons, List.mem_append] at hx ⊢
        rcases hx with (h | h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      · have key := ihn (by simp only [List.mem_cons]; tauto)
        have step : BoundedDerivable r γ (∼χ :: (φ :: ψ :: Γ₂)) := by
          refine .contraction ?_ key
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with h | h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr h))
        refine .contraction ?_ (BoundedDerivable.cut hc hβ hγ hdp step)
        intro x hx
        simp only [List.mem_cons, List.mem_append] at hx ⊢
        rcases hx with h | (h | h | h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))

/-- Inversion for `⋏`, left component. -/
theorem inv_and_left {r : ℕ} :
    ∀ {α : NONote} {Γ : Sequent L}, BoundedDerivable r α Γ →
      ∀ {φ ψ : Proposition L}, (φ ⋏ ψ) ∈ Γ →
        BoundedDerivable r α (φ :: Γ) := by
  intro α Γ h
  induction h with
  | identity rl v =>
      intro φ ψ _
      exact .contraction (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
        (.identity rl v)
  | verum =>
      intro φ ψ _
      exact .contraction (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) .verum
  | @or α β χ ρ Γ' hlt hd ih =>
      intro φ ψ hmem
      have hmemΓ : (φ ⋏ ψ) ∈ Γ' := by
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih (φ := φ) (ψ := ψ) (by simp only [List.mem_cons]; tauto)
      have step : BoundedDerivable r β (χ :: ρ :: (φ :: Γ')) := by
        refine .contraction ?_ key
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      refine .contraction ?_ (BoundedDerivable.or hlt step)
      intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @and α β γ χ ρ Γ' hβ hγ hdp hdq ihp ihq =>
      intro φ ψ hmem
      by_cases hcase : (φ ⋏ ψ) = (χ ⋏ ρ)
      · have hφ : φ = χ := by injection hcase
        subst hφ
        refine .contraction ?_ (hdp.mono_ord (le_of_lt hβ))
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      · have hmemΓ : (φ ⋏ ψ) ∈ Γ' := by
          simp only [List.mem_cons] at hmem
          rcases hmem with h | h
          · exact absurd h hcase
          · exact h
        have kp : BoundedDerivable r β (χ :: (φ :: Γ')) := by
          refine .contraction ?_ (ihp (φ := φ) (ψ := ψ) (by simp only [List.mem_cons]; tauto))
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
        have kq : BoundedDerivable r γ (ρ :: (φ :: Γ')) := by
          refine .contraction ?_ (ihq (φ := φ) (ψ := ψ) (by simp only [List.mem_cons]; tauto))
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
        refine .contraction ?_ (BoundedDerivable.and hβ hγ kp kq)
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @all α β χ Γ' hlt hd ih =>
      intro φ ψ hmem
      have hmemΓ : (φ ⋏ ψ) ∈ Γ' := by
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h
        · exact absurd h (by simp)
        · exact h
      have hshift : (Rewriting.shift φ ⋏ Rewriting.shift ψ) ∈ Γ'⁺ := by
        have h0 : (Rewriting.shift (φ ⋏ ψ)) ∈ Γ'⁺ :=
          LawfulSyntacticRewriting.mem_shifts_iff.mpr hmemΓ
        simpa using h0
      have key := ih (by simp only [List.mem_cons]; exact Or.inr hshift)
      have step : BoundedDerivable r β (χ.free :: (φ :: Γ')⁺) := by
        refine .contraction ?_ key
        intro x hx; simp only [Rewriting.shifts_cons, List.mem_cons] at hx ⊢; tauto
      refine .contraction ?_ (BoundedDerivable.all hlt step)
      intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @exs α β χ Γ' t hlt hd ih =>
      intro φ ψ hmem
      have hmemΓ : (φ ⋏ ψ) ∈ Γ' := by
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih (φ := φ) (ψ := ψ) (by simp only [List.mem_cons]; tauto)
      have step : BoundedDerivable r β (χ/[t] :: (φ :: Γ')) := by
        refine .contraction ?_ key
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      refine .contraction ?_ (BoundedDerivable.exs t hlt step)
      intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @contraction α Δ Γ' ss hd ih =>
      intro φ ψ hmem
      by_cases hin : (φ ⋏ ψ) ∈ Δ
      · refine .contraction ?_ (ih hin)
        intro x hx; simp only [List.mem_cons] at hx ⊢
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr (ss h)
      · refine .contraction ?_ hd
        intro x hx
        simp only [List.mem_cons]
        exact Or.inr (ss hx)
  | @cut α β γ χ Γ₁ Γ₂ hc hβ hγ hdp hdn ihp ihn =>
      intro φ ψ hmem
      rcases List.mem_append.mp hmem with h | h
      · have key := ihp (φ := φ) (ψ := ψ) (by simp only [List.mem_cons]; tauto)
        have step : BoundedDerivable r β (χ :: (φ :: Γ₁)) := by
          refine .contraction ?_ key
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
        refine .contraction ?_ (BoundedDerivable.cut hc hβ hγ step hdn)
        intro x hx
        simp only [List.mem_cons, List.mem_append] at hx ⊢
        rcases hx with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · have key := ihn (φ := φ) (ψ := ψ) (by simp only [List.mem_cons]; tauto)
        have step : BoundedDerivable r γ (∼χ :: (φ :: Γ₂)) := by
          refine .contraction ?_ key
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
        refine .contraction ?_ (BoundedDerivable.cut hc hβ hγ hdp step)
        intro x hx
        simp only [List.mem_cons, List.mem_append] at hx ⊢
        rcases hx with h | (h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

/-- Inversion for `⋏`, right component. -/
theorem inv_and_right {r : ℕ} :
    ∀ {α : NONote} {Γ : Sequent L}, BoundedDerivable r α Γ →
      ∀ {φ ψ : Proposition L}, (φ ⋏ ψ) ∈ Γ →
        BoundedDerivable r α (ψ :: Γ) := by
  intro α Γ h
  induction h with
  | identity rl v =>
      intro φ ψ _
      exact .contraction (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
        (.identity rl v)
  | verum =>
      intro φ ψ _
      exact .contraction (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) .verum
  | @or α β χ ρ Γ' hlt hd ih =>
      intro φ ψ hmem
      have hmemΓ : (φ ⋏ ψ) ∈ Γ' := by
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih (φ := φ) (ψ := ψ) (by simp only [List.mem_cons]; tauto)
      have step : BoundedDerivable r β (χ :: ρ :: (ψ :: Γ')) := by
        refine .contraction ?_ key
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      refine .contraction ?_ (BoundedDerivable.or hlt step)
      intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @and α β γ χ ρ Γ' hβ hγ hdp hdq ihp ihq =>
      intro φ ψ hmem
      by_cases hcase : (φ ⋏ ψ) = (χ ⋏ ρ)
      · have hψ : ψ = ρ := by injection hcase
        subst hψ
        refine .contraction ?_ (hdq.mono_ord (le_of_lt hγ))
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      · have hmemΓ : (φ ⋏ ψ) ∈ Γ' := by
          simp only [List.mem_cons] at hmem
          rcases hmem with h | h
          · exact absurd h hcase
          · exact h
        have kp : BoundedDerivable r β (χ :: (ψ :: Γ')) := by
          refine .contraction ?_ (ihp (φ := φ) (ψ := ψ) (by simp only [List.mem_cons]; tauto))
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
        have kq : BoundedDerivable r γ (ρ :: (ψ :: Γ')) := by
          refine .contraction ?_ (ihq (φ := φ) (ψ := ψ) (by simp only [List.mem_cons]; tauto))
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
        refine .contraction ?_ (BoundedDerivable.and hβ hγ kp kq)
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @all α β χ Γ' hlt hd ih =>
      intro φ ψ hmem
      have hmemΓ : (φ ⋏ ψ) ∈ Γ' := by
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h
        · exact absurd h (by simp)
        · exact h
      have hshift : (Rewriting.shift φ ⋏ Rewriting.shift ψ) ∈ Γ'⁺ := by
        have h0 : (Rewriting.shift (φ ⋏ ψ)) ∈ Γ'⁺ :=
          LawfulSyntacticRewriting.mem_shifts_iff.mpr hmemΓ
        simpa using h0
      have key := ih (by simp only [List.mem_cons]; exact Or.inr hshift)
      have step : BoundedDerivable r β (χ.free :: (ψ :: Γ')⁺) := by
        refine .contraction ?_ key
        intro x hx; simp only [Rewriting.shifts_cons, List.mem_cons] at hx ⊢; tauto
      refine .contraction ?_ (BoundedDerivable.all hlt step)
      intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @exs α β χ Γ' t hlt hd ih =>
      intro φ ψ hmem
      have hmemΓ : (φ ⋏ ψ) ∈ Γ' := by
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih (φ := φ) (ψ := ψ) (by simp only [List.mem_cons]; tauto)
      have step : BoundedDerivable r β (χ/[t] :: (ψ :: Γ')) := by
        refine .contraction ?_ key
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      refine .contraction ?_ (BoundedDerivable.exs t hlt step)
      intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @contraction α Δ Γ' ss hd ih =>
      intro φ ψ hmem
      by_cases hin : (φ ⋏ ψ) ∈ Δ
      · refine .contraction ?_ (ih hin)
        intro x hx; simp only [List.mem_cons] at hx ⊢
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr (ss h)
      · refine .contraction ?_ hd
        intro x hx
        simp only [List.mem_cons]
        exact Or.inr (ss hx)
  | @cut α β γ χ Γ₁ Γ₂ hc hβ hγ hdp hdn ihp ihn =>
      intro φ ψ hmem
      rcases List.mem_append.mp hmem with h | h
      · have key := ihp (φ := φ) (ψ := ψ) (by simp only [List.mem_cons]; tauto)
        have step : BoundedDerivable r β (χ :: (ψ :: Γ₁)) := by
          refine .contraction ?_ key
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
        refine .contraction ?_ (BoundedDerivable.cut hc hβ hγ step hdn)
        intro x hx
        simp only [List.mem_cons, List.mem_append] at hx ⊢
        rcases hx with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · have key := ihn (φ := φ) (ψ := ψ) (by simp only [List.mem_cons]; tauto)
        have step : BoundedDerivable r γ (∼χ :: (ψ :: Γ₂)) := by
          refine .contraction ?_ key
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
        refine .contraction ?_ (BoundedDerivable.cut hc hβ hγ hdp step)
        intro x hx
        simp only [List.mem_cons, List.mem_append] at hx ⊢
        rcases hx with h | (h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

end BoundedDerivable

end OrdinalAnalysis
