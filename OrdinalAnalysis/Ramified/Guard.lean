/-
  The arithmetical guard of the naming schema.

  The naming schema of `Ramified/Theory.lean` has one pair of axioms per formula
  `A` and level `μ`, uniform in the code: for every `c`, `p`, `s` such that

      c = ⟨μ, s, ⌜A⌝, p⟩   and   A.complexity + stage p < s,

  the code `c` names `{x | A(x, p)}`.  This file writes that condition as a
  formula of arithmetic, `guardDef`, through Foundation's graph of the Cantor
  pairing (`pairDef`), and proves the three facts about it the rest of the
  development consumes:

  * in `ℕ` it says exactly `c = mkCodeN ⌜μ⌝ s ⌜A⌝ p ∧ A.complexity + stage p < s`
    (`eval_guardDef_nat`), so the infinitary calculus can decide it by looking
    at numbers;
  * it is total in its first and third arguments, provably in `IΣ₁`
    (`guardTotal_provable`): every parameter has a code at some stage — this is
    what turns the schema into a comprehension principle;
  * its true numeral instances are provable in `PA⁻` (`guardAt_provable`), by
    `Σ₁`-completeness — this is what lets a particular code be used.
-/
import OrdinalAnalysis.Ramified.Code
import Foundation.FirstOrder.Arithmetic.HFS

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- **The guard**, with arguments `c p s m e k`:
`c = ⟨m, s, e, p⟩ ∧ k + stage p < s`, where `stage p` is the first component of
the second component of `p`. -/
def guardDef : 𝚺₁.Semisentence 6 := .mkSigma
  “c p s m e k. ∃ c₁, !pairDef c m c₁ ∧ ∃ c₂, !pairDef c₁ s c₂ ∧ !pairDef c₂ e p ∧
    ∃ y, ∃ z, !pairDef p y z ∧ ∃ t, ∃ w, !pairDef z t w ∧ k + t < s”

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The guard in a model of `IΣ₁`, in terms of Foundation's pairing. -/
@[simp] theorem eval_guardDef (c p s m e k : V) : guardDef.val.Evalb ![c, p, s, m, e, k] ↔
    ∃ c₁, c = ⟪m, c₁⟫ ∧ ∃ c₂, c₁ = ⟪s, c₂⟫ ∧ c₂ = ⟪e, p⟫ ∧
      ∃ y z, p = ⟪y, z⟫ ∧ ∃ t w, z = ⟪t, w⟫ ∧ k + t < s := by
  simp [guardDef, pair_defined.iff]

end Model

/-- **The guard in `ℕ`**: exactly the code condition of `Ramified/Code.lean`. -/
theorem eval_guardDef_nat (c p s m e k : ℕ) : guardDef.val.Evalb ![c, p, s, m, e, k] ↔
    c = mkCodeN m s e p ∧ k + stage p < s := by
  rw [eval_guardDef]
  simp only [nat_pair_eq]
  constructor
  · rintro ⟨c₁, rfl, c₂, rfl, rfl, y, z, rfl, t, w, rfl, hlt⟩
    refine ⟨rfl, ?_⟩
    simpa [stage] using hlt
  · rintro ⟨rfl, hlt⟩
    refine ⟨_, rfl, _, rfl, rfl, p.unpair.1, p.unpair.2, (Nat.pair_unpair p).symm,
      p.unpair.2.unpair.1, p.unpair.2.unpair.2, (Nat.pair_unpair _).symm, ?_⟩
    simpa [stage] using hlt

/-! ### Totality -/

/-- `∀m e k p ∃c s. guard(c, p, s, m, e, k)`. -/
def guardTotal : ArithmeticSentence :=
  “∀ m, ∀ e, ∀ k, ∀ p, ∃ c, ∃ s, !guardDef.val c p s m e k”

/-- **Every parameter has a code, at a large enough stage**, provably in `IΣ₁`:
`s := k + stage p + 1` and `c := ⟨m, s, e, p⟩`. -/
theorem guardTotal_provable : 𝗜𝚺₁ ⊢ guardTotal := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simp only [models_iff, guardTotal, Semiformula.eval_all, Semiformula.eval_ex,
    Semiformula.eval_substs]
  intro m e k p
  refine ⟨⟪m, ⟪k + π₁ (π₂ p) + 1, ⟪e, p⟫⟫⟫, k + π₁ (π₂ p) + 1, ?_⟩
  have hv : (Semiterm.val ![k + π₁ (π₂ p) + 1, ⟪m, ⟪k + π₁ (π₂ p) + 1, ⟪e, p⟫⟫⟫, p, k, e, m]
      Empty.elim ∘ ![(#1 : Semiterm ℒₒᵣ Empty 6), #2, #0, #5, #4, #3])
      = ![⟪m, ⟪k + π₁ (π₂ p) + 1, ⟪e, p⟫⟫⟫, p, k + π₁ (π₂ p) + 1, m, e, k] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  exact (eval_guardDef _ _ _ _ _ _).mpr ⟨_, rfl, _, rfl, rfl, π₁ p, π₂ p, (pair_unpair p).symm,
    π₁ (π₂ p), π₂ (π₂ p), (pair_unpair _).symm, lt_add_one _⟩

/-! ### Numeral instances -/

/-- The guard at numerals. -/
def guardAt (c p s m e k : ℕ) : ArithmeticSentence :=
  Rew.subst ![(c : Semiterm ℒₒᵣ Empty 0), (p : Semiterm ℒₒᵣ Empty 0), (s : Semiterm ℒₒᵣ Empty 0),
    (m : Semiterm ℒₒᵣ Empty 0), (e : Semiterm ℒₒᵣ Empty 0), (k : Semiterm ℒₒᵣ Empty 0)] ▹
    guardDef.val

theorem models_guardAt_iff (c p s m e k : ℕ) :
    ℕ↓[ℒₒᵣ] ⊧ guardAt c p s m e k ↔ c = mkCodeN m s e p ∧ k + stage p < s := by
  rw [← eval_guardDef_nat]
  simp only [guardAt, models_iff, Semiformula.eval_rew, Function.comp_def]
  apply iff_of_eq
  congr 2
  funext x
  fin_cases x <;> simp [Rew.subst_bvar]

/-- **A true numeral instance of the guard is provable in `PA⁻`**
(`Σ₁`-completeness). -/
theorem guardAt_provable {c p s m e k : ℕ} (hc : c = mkCodeN m s e p) (hs : k + stage p < s) :
    𝗣𝗔⁻ ⊢ guardAt c p s m e k :=
  sigma_one_completeness (by simp [guardAt]) ((models_guardAt_iff c p s m e k).mpr ⟨hc, hs⟩)

end Ramified

end OrdinalAnalysis
