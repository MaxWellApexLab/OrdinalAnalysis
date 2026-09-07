import OrdinalAnalysis.Proof.Substitution
import OrdinalAnalysis.Proof.Inversion
import OrdinalAnalysis.Proof.InversionAll

namespace OrdinalAnalysis
open LO LO.FirstOrder LO.FirstOrder.Derivation

variable {L : Language}

namespace BoundedDerivable

theorem inv_all {r : ℕ} :
    ∀ {α : NONote} {Γ : Sequent L}, BoundedDerivable r α Γ →
      ∀ {ψ : Semiproposition L 1}, (∀¹ ψ) ∈ Γ →
        ∀ t : SyntacticTerm L, BoundedDerivable r α (ψ/[t] :: Γ) := by
  intro α Γ h
  induction h with
  | identity rl v =>
      intro ψ _ t
      exact .contraction (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
        (.identity rl v)
  | verum =>
      intro ψ _ t
      exact .contraction (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) .verum
  | @or α β χ ρ Γ' hlt hd ih =>
      intro ψ hmem t
      have hmemΓ : (∀¹ ψ) ∈ Γ' := by
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih (ψ := ψ) (by simp only [List.mem_cons]; tauto) t
      have step : BoundedDerivable r β (χ :: ρ :: (ψ/[t] :: Γ')) := by
        refine .contraction ?_ key
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      refine .contraction ?_ (BoundedDerivable.or hlt step)
      intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @and α β γ χ ρ Γ' hβ hγ hdp hdq ihp ihq =>
      intro ψ hmem t
      have hmemΓ : (∀¹ ψ) ∈ Γ' := by
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h
        · exact absurd h (by simp)
        · exact h
      have kp := ihp (ψ := ψ) (by simp only [List.mem_cons]; tauto) t
      have kq := ihq (ψ := ψ) (by simp only [List.mem_cons]; tauto) t
      have sp : BoundedDerivable r β (χ :: (ψ/[t] :: Γ')) := by
        refine .contraction ?_ kp
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      have sq : BoundedDerivable r γ (ρ :: (ψ/[t] :: Γ')) := by
        refine .contraction ?_ kq
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      refine .contraction ?_ (BoundedDerivable.and hβ hγ sp sq)
      intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @all α β χ Γ' hlt hd ih =>
      intro ψ hmem t
      by_cases hcase : (∀¹ ψ) = (∀¹ χ)
      · have hψ : ψ = χ := (Semiformula.all_inj _ _).mp hcase
        subst hψ
        refine .contraction ?_ ((all_premise_subst hd t).mono_ord (le_of_lt hlt))
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      · have hmemΓ : (∀¹ ψ) ∈ Γ' := by
          simp only [List.mem_cons] at hmem
          rcases hmem with h | h
          · exact absurd h hcase
          · exact h
        have hshift : (∀¹ (Rewriting.shift ψ)) ∈ Γ'⁺ := by
          have h0 : Rewriting.shift (∀¹ ψ) ∈ Γ'⁺ :=
            LawfulSyntacticRewriting.mem_shifts_iff.mpr hmemΓ
          simpa using h0
        have key := ih (ψ := Rewriting.shift ψ)
          (by simp only [List.mem_cons]; exact Or.inr hshift) (Rew.shift t)
        have hinst : (Rewriting.shift (ψ/[t]) : Proposition L) =
            (Rewriting.shift ψ)/[Rew.shift t] := by
          show Rew.shift ▹ (Rew.subst ![t] ▹ ψ) =
            Rew.subst ![Rew.shift t] ▹ (Rew.shift ▹ ψ)
          rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app,
            Rew.shift_comp_subst1]
        rw [← hinst] at key
        have step : BoundedDerivable r β (χ.free :: (ψ/[t] :: Γ')⁺) := by
          refine .contraction ?_ key
          intro x hx
          simp only [Rewriting.shifts_cons, List.mem_cons] at hx ⊢
          tauto
        refine .contraction ?_ (BoundedDerivable.all hlt step)
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @exs α β χ Γ' s hlt hd ih =>
      intro ψ hmem t
      have hmemΓ : (∀¹ ψ) ∈ Γ' := by
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h
        · exact absurd h (by simp)
        · exact h
      have key := ih (ψ := ψ) (by simp only [List.mem_cons]; tauto) t
      have step : BoundedDerivable r β (χ/[s] :: (ψ/[t] :: Γ')) := by
        refine .contraction ?_ key
        intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
      refine .contraction ?_ (BoundedDerivable.exs s hlt step)
      intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  | @contraction α Δ Γ' ss hd ih =>
      intro ψ hmem t
      by_cases hin : (∀¹ ψ) ∈ Δ
      · refine .contraction ?_ (ih hin t)
        intro x hx; simp only [List.mem_cons] at hx ⊢
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr (ss h)
      · refine .contraction ?_ hd
        intro x hx
        simp only [List.mem_cons]
        exact Or.inr (ss hx)
  | @cut α β γ χ Γ₁ Γ₂ hc hβ hγ hdp hdn ihp ihn =>
      intro ψ hmem t
      rcases List.mem_append.mp hmem with h | h
      · have key := ihp (ψ := ψ) (by simp only [List.mem_cons]; tauto) t
        have step : BoundedDerivable r β (χ :: (ψ/[t] :: Γ₁)) := by
          refine .contraction ?_ key
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
        refine .contraction ?_ (BoundedDerivable.cut hc hβ hγ step hdn)
        intro x hx
        simp only [List.mem_cons, List.mem_append] at hx ⊢
        rcases hx with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · have key := ihn (ψ := ψ) (by simp only [List.mem_cons]; tauto) t
        have step : BoundedDerivable r γ (∼χ :: (ψ/[t] :: Γ₂)) := by
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
