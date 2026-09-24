/-
  Standard notations inside models of `IΣ₁`: the codes of the tower `ω_n(Ω + 1)` and the order
  between standard codes.

  The tower `WellOrdering.tau` (`τ_0 = ⟨Ω, 0⟩`, `τ_{n+1} = ⟨τ_n⟩`) is, in every
  model `V` of `IΣ₁`, the standard code of `ω_n(Ω + 1) = ThetaNote.omegaTower n (Ω + 1)`
  (`mc_omegaTower`).  With the cofinality lemma `ThetaNote.exists_lt_theta_omegaTower` (every
  notation below `Ω` lies below some `ϑ(ω_n(Ω + 1))`, Freund, arXiv:2204.09321, Definition 3.1
  (ii')) this gives, for a standard notation `a ≺ Ω`, a standard `n` with `⌜a⌝ ≺ ϑ(τ_n)`
  inside `V` (`exists_lt_theta_tau`).
-/
import OrdinalAnalysis.ID1.WellOrdering
import OrdinalAnalysis.Ordinal.Theta.HullCofinal

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

namespace WellOrdering

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.ID1.Internal
open ThetaNote (omegaTower)

/-- `Ω + 1 = ⟨Ω, 0⟩`. -/
theorem omega_add_one_val :
    (ThetaNote.Omega + ThetaNote.one).1 = ThetaTerm.sum [ThetaTerm.Omega, ThetaTerm.sum []] := by
  show ThetaTerm.ofList (ThetaTerm.addL [ThetaTerm.Omega] [ThetaTerm.sum []]) = _
  have h : ThetaTerm.geb ThetaTerm.Omega (ThetaTerm.sum []) = true := by
    simp only [ThetaTerm.geb, decide_eq_true_eq]
    exact Or.inl ThetaTerm.nil_lt_Omega
  rw [ThetaTerm.addL_cons, List.filter_singleton, h]
  rfl

/-- The tower is a tower of sums. -/
theorem omegaTower_val (n : ℕ) :
    ∃ xs, (omegaTower n (ThetaNote.Omega + ThetaNote.one)).1 = ThetaTerm.sum xs := by
  cases n with
  | zero => exact ⟨_, omega_add_one_val⟩
  | succ n =>
    obtain ⟨xs, hxs⟩ := omegaTower_val n
    refine ⟨[(omegaTower n (ThetaNote.Omega + ThetaNote.one)).1], ?_⟩
    show ThetaTerm.ofList [(omegaTower n (ThetaNote.Omega + ThetaNote.one)).1] = _
    rw [ThetaTerm.ofList_singleton_not_prin (by rw [hxs]; exact id)]

/-- `ω_{n+1}(Ω + 1) = ⟨ω_n(Ω + 1)⟩`. -/
theorem omegaTower_succ_val (n : ℕ) :
    (omegaTower (n + 1) (ThetaNote.Omega + ThetaNote.one)).1 =
      ThetaTerm.sum [(omegaTower n (ThetaNote.Omega + ThetaNote.one)).1] := by
  obtain ⟨xs, hxs⟩ := omegaTower_val n
  show ThetaTerm.ofList [(omegaTower n (ThetaNote.Omega + ThetaNote.one)).1] = _
  rw [ThetaTerm.ofList_singleton_not_prin (by rw [hxs]; exact id)]

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The tower `τ_n` is the code of `ω_n(Ω + 1)`.** -/
theorem mc_omegaTower (n : ℕ) :
    mc (V := V) (omegaTower n (ThetaNote.Omega + ThetaNote.one)).1 = tau n := by
  induction n with
  | zero =>
    rw [omegaTower, omega_add_one_val, mc_cons, mc_cons, mc_Omega, mc_nil]
    rfl
  | succ n ih =>
    rw [omegaTower_succ_val, mc_cons, ih, mc_nil]
    rfl

/-- **Cofinality inside `V`**: for a notation `a ≺ Ω`, its code is a normal form below the
code of `ϑ(τ_n)` for some standard `n`. -/
theorem exists_lt_theta_tau {a : ThetaNote} (ha : a < ThetaNote.Omega) :
    ∃ n : ℕ, isNF (mc (V := V) a.1) ∧ iltb (mc (V := V) a.1) (tcTheta (tau n)) = 1 := by
  obtain ⟨n, hn⟩ := ThetaNote.exists_lt_theta_omegaTower ha
  refine ⟨n, (isNF_mc a.1).mpr a.2, ?_⟩
  rw [← mc_omegaTower n, ← mc_theta, iltb_mc]
  exact hn

end Model

end WellOrdering

end InductiveDef

end OrdinalAnalysis
