/-
  Course-of-values tables inside models of `IΣ₁`, generically.

  Given a two-place function `step` with a `Σ₁` graph `stepDef`, the table of length `n + 1`
  is the sequence whose entry at position `0` is `step 0 0` and whose entry at position
  `m + 1` is `step (m + 1) t`, where `t` is the table of length `m + 1`.  The value at
  position `m` is `covVal step stepDef m`; it satisfies

  * `covVal 0 = step 0 0`,
  * `covVal (M + 1) = step (M + 1) (covTable M)`, and
  * `znth (covTable N) k = covVal k` for every `k ≤ N`,

  so a step function that reads its table argument only at positions below the current one
  defines a recursion on positions.  Positions will be single codes or pairs `⟪c₁, c₂⟫` of
  codes.  The table and the value function have `Σ₁` graphs, uniformly in the model.

  The second part provides `0/1`-valued boolean connectives with `Σ₀` graphs.
-/
import OrdinalAnalysis.Gentzen.InternalONote

set_option autoImplicit false

namespace OrdinalAnalysis.ID1.Internal

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.Gentzen.InternalONote

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Course-of-values tables -/

section Cov
def covBlueprint (stepDef : 𝚺₁.Semisentence 3) : PR.Blueprint 0 where
  zero := .mkSigma “y. ∃ v, !stepDef v 0 0 ∧ !mkSeq₁Def y v”
  succ := .mkSigma “y ih n. ∃ v, !stepDef v (n + 1) ih ∧ !seqConsDef y ih v”

variable (step : V → V → V) (stepDef : 𝚺₁.Semisentence 3)

noncomputable def covConstruction [h : 𝚺₁-Function₂ step via stepDef] :
    PR.Construction V (covBlueprint stepDef) where
  zero := fun _ ↦ !⟦step 0 0⟧
  succ := fun _ n ih ↦ seqCons ih (step (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [covBlueprint, mkSeq₁Def, h.iff, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [covBlueprint, h.iff, seqCons_defined.iff]


variable [hs : 𝚺₁-Function₂ step via stepDef]

/-- The course-of-values table of length `n + 1`. -/
noncomputable def covTable (n : V) : V := (covConstruction step stepDef).result ![] n

/-- The value at position `m`. -/
noncomputable def covVal (m : V) : V := znth (covTable step stepDef m) m

@[simp] lemma covTable_zero : covTable step stepDef (0 : V) = !⟦step 0 0⟧ := by
  simp [covTable, covConstruction]

@[simp] lemma covTable_succ (n : V) :
    covTable step stepDef (n + 1)
      = seqCons (covTable step stepDef n) (step (n + 1) (covTable step stepDef n)) := by
  simp [covTable, covConstruction]

def covTableDef : 𝚺₁.Semisentence 2 :=
  (covBlueprint stepDef).resultDef.rew (Rew.subst ![#0, #1])

instance covTable_defined :
    𝚺₁-Function₁ (covTable step stepDef : V → V) via covTableDef stepDef := .mk fun v ↦ by
  simp [(covConstruction step stepDef).result_defined_iff, covTableDef]; rfl

instance covTable_definable : 𝚺₁-Function₁ (covTable step stepDef : V → V) :=
  (covTable_defined step stepDef).to_definable

def covValDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y m. ∃ t, !(covTableDef stepDef) t m ∧ !znthDef y t m”

instance covVal_defined :
    𝚺₁-Function₁ (covVal step stepDef : V → V) via covValDef stepDef := .mk fun v ↦ by
  simp [covValDef, covVal, (covTable_defined step stepDef).iff, znth_defined.iff]

instance covVal_definable : 𝚺₁-Function₁ (covVal step stepDef : V → V) :=
  (covVal_defined step stepDef).to_definable

private lemma def_covTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ covTable step stepDef (v i)) :=
  DefinableFunction₁.comp (F := covTable step stepDef) (DefinableFunction.var i)

private lemma def_covVal {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ covVal step stepDef (v i)) :=
  DefinableFunction₁.comp (F := covVal step stepDef) (DefinableFunction.var i)

@[simp] lemma covTable_seq (n : V) : Seq (covTable step stepDef n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_covTable step stepDef 0)
  case zero => simp
  case succ n ih => rw [covTable_succ]; exact ih.seqCons _

@[simp] lemma covTable_lh (n : V) : lh (covTable step stepDef n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_covTable step stepDef 0))
      (by definability)
  case zero => simp
  case succ n ih => rw [covTable_succ, Seq.lh_seqCons _ (covTable_seq step stepDef n), ih]

lemma znth_covTable_succ {n k : V} (hk : k < n + 1) :
    znth (covTable step stepDef (n + 1)) k = znth (covTable step stepDef n) k := by
  rw [covTable_succ]
  exact znth_seqCons_of_lt (covTable_seq step stepDef n) _ (by rw [covTable_lh]; exact hk)

/-- Every entry of a table is the value at that position. -/
lemma znth_covTable :
    ∀ N : V, ∀ k ≤ N, znth (covTable step stepDef N) k = covVal step stepDef k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_covTable step stepDef 1) (DefinableFunction.var 0))
      (def_covVal step stepDef 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_covTable_succ step stepDef hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

lemma covVal_zero : covVal step stepDef (0 : V) = step 0 0 := by
  simp only [covVal, covTable_zero]
  exact (singleton_seq _).znth_eq_of_mem ((mem_singleton_seq_iff _ _).mpr rfl)

lemma covVal_succ (M : V) :
    covVal step stepDef (M + 1) = step (M + 1) (covTable step stepDef M) := by
  simp only [covVal]
  rw [covTable_succ]
  have := znth_seqCons_self (covTable_seq step stepDef M) (step (M + 1) (covTable step stepDef M))
  rwa [covTable_lh] at this

/-- **The recursion law of a table**: the value at `m` is the step at `m` applied to a
sequence whose entries below `m` are the values there. -/
lemma covVal_unfold (m : V) :
    ∃ S : V, covVal step stepDef m = step m S ∧
      ∀ k < m, znth S k = covVal step stepDef k := by
  rcases eq_or_ne m 0 with rfl | hm
  · exact ⟨0, covVal_zero step stepDef, fun k hk => absurd hk (by simp)⟩
  · obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 :=
      ⟨m - 1, (sub_add_self_of_le (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hm))).symm⟩
    exact ⟨covTable step stepDef M, covVal_succ step stepDef M,
      fun k hk => znth_covTable step stepDef M k (le_iff_lt_succ.mpr hk)⟩

end Cov

/-! ## Boolean connectives on `0/1` flags -/

/-- Disjunction of flags: `1` iff one of the arguments is `1`. -/
noncomputable def bor (a b : V) : V := if a = 1 ∨ b = 1 then 1 else 0

/-- Conjunction of flags: `1` iff both arguments are `1`. -/
noncomputable def band (a b : V) : V := if a = 1 ∧ b = 1 then 1 else 0

/-- Equality flag: `1` iff the arguments are equal. -/
noncomputable def beq (a b : V) : V := if a = b then 1 else 0

def borDef : 𝚺₀.Semisentence 3 := .mkSigma
  “y a b. ((a = 1 ∨ b = 1) ∧ y = 1) ∨ (a ≠ 1 ∧ b ≠ 1 ∧ y = 0)”

def bandDef : 𝚺₀.Semisentence 3 := .mkSigma
  “y a b. (a = 1 ∧ b = 1 ∧ y = 1) ∨ ((a ≠ 1 ∨ b ≠ 1) ∧ y = 0)”

def beqDef : 𝚺₀.Semisentence 3 := .mkSigma
  “y a b. (a = b ∧ y = 1) ∨ (a ≠ b ∧ y = 0)”

instance bor_defined : 𝚺₀-Function₂ (bor : V → V → V) via borDef := .mk fun v ↦ by
  simp only [borDef, bor]
  by_cases h1 : v 1 = 1 <;> by_cases h2 : v 2 = 1 <;> simp [h1, h2]

instance band_defined : 𝚺₀-Function₂ (band : V → V → V) via bandDef := .mk fun v ↦ by
  simp only [bandDef, band]
  by_cases h1 : v 1 = 1 <;> by_cases h2 : v 2 = 1 <;> simp [h1, h2]

instance beq_defined : 𝚺₀-Function₂ (beq : V → V → V) via beqDef := .mk fun v ↦ by
  simp only [beqDef, beq]
  by_cases h : v 1 = v 2 <;> simp [h]

instance bor_definable : 𝚺₀-Function₂ (bor : V → V → V) := bor_defined.to_definable
instance band_definable : 𝚺₀-Function₂ (band : V → V → V) := band_defined.to_definable
instance beq_definable : 𝚺₀-Function₂ (beq : V → V → V) := beq_defined.to_definable

instance bor_definable' (Γ) : Γ-Function₂ (bor : V → V → V) := bor_definable.of_zero
instance band_definable' (Γ) : Γ-Function₂ (band : V → V → V) := band_definable.of_zero
instance beq_definable' (Γ) : Γ-Function₂ (beq : V → V → V) := beq_definable.of_zero

@[simp] lemma bor_eq_one {a b : V} : bor a b = 1 ↔ a = 1 ∨ b = 1 := by
  unfold bor; split_ifs with h <;> simp [h]

@[simp] lemma band_eq_one {a b : V} : band a b = 1 ↔ a = 1 ∧ b = 1 := by
  unfold band; split_ifs with h <;> simp [h]

@[simp] lemma beq_eq_one {a b : V} : beq a b = 1 ↔ a = b := by
  unfold beq; split_ifs with h <;> simp [h]

end OrdinalAnalysis.ID1.Internal
