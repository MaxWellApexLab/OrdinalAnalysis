/-
  Slot check for `IDw`: the one way the uniform binary construction could silently go wrong
  is a swapped or shifted slot -- `J`'s level argument read as its element argument, the
  form's `#0`/`#1` (`x`/`y`) exchanged, or `Q`'s guard `s < y` off by one. Each is caught by a
  direct evaluation on concrete data.

    * `slotCheck_Jat_reads_its_own_column`: `Jat s t` reads column `s` (its FIRST argument)
      of the environment, `t` being the element, for two different columns.
    * `slotA := (#1 = 1 ∧ #0 = 0) ∨ Q(1, #0)`: `#1` is the level `y`, `#0` the element `x`,
      `Q(1, ·)` reads level `1` strictly below `y`. `mem_opJ_slotA` computes the operator
      (`x ∈ opJ y ↔ (y = 1 ∧ x = 0) ∨ (1 < y ∧ x ∈ S 1)`); `slotA_J_iff` computes the whole
      iterated fixed point, `J(y, x) ↔ 1 ≤ y ∧ x = 0`. A swapped `x`/`y` would give
      `y = 0 ∧ x = 1` instead; an off-by-one guard would change the threshold `1 ≤ y`.
    * `slotA_consistent`: the soundness machine instantiates on this concrete form.
-/
import OrdinalAnalysis.IDw.Sound

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- **`Jat s t` reads column `s` of the environment** (its first argument is the level),
for every pair of columns, checked at `0` versus `1`. -/
theorem slotCheck_Jat_reads_its_own_column (P : ℕ → Prop) (S : ℕ → Set ℕ)
    (h0 : 5 ∉ S 0) (h1 : 5 ∈ S 1) :
    ¬Semiformula.Eval (s := stdJ P S) ![5] Empty.elim
        (Jat ((0 : ℕ) : Semiterm LXJ Empty 1) #0) ∧
      Semiformula.Eval (s := stdJ P S) ![5] Empty.elim
        (Jat ((1 : ℕ) : Semiterm LXJ Empty 1) #0) := by
  constructor
  · rw [eval_Jat]; exact h0
  · rw [eval_Jat]; exact h1

/-- Equality of two terms, in the schema language. -/
def eqF {ξ : Type*} {n : ℕ} (s t : Semiterm LForm ξ n) : Semiformula LForm ξ n :=
  Semiformula.rel Language.Eq.eq ![s, t]
def slotA : FormJ := (eqF #1 ((1 : ℕ) : Semiterm LForm Empty 2) ⋏ eqF #0 ((0 : ℕ) : Semiterm LForm Empty 2)) ⋎ Qat ((1 : ℕ) : Semiterm LForm Empty 2) #0

theorem eval_eq_inl_fn (P : ℕ → Prop) (S : ℕ → Set ℕ) {ξ : Type*} {n : ℕ}
    (v : Fin 2 → Semiterm LXJ ξ n) (e : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdJ P S) e f (Semiformula.rel (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2)) v) ↔
      Semiterm.val (s := stdJ P S) e f (v 0) = Semiterm.val (s := stdJ P S) e f (v 1) := by
  show Structure.rel (M := ℕ) (Language.Eq.eq : (ℒₒᵣ).Rel 2)
      (fun i => Semiterm.val (s := stdJ P S) e f (v i)) ↔ _
  exact Structure.eq_lang

theorem val_termCast_bvar (P : ℕ → Prop) (S : ℕ → Set ℕ) {n : ℕ} (e : Fin n → ℕ) (f : Empty → ℕ)
    (i : Fin n) : Semiterm.val (s := stdJ P S) e f (termCast (#i : Semiterm LForm Empty n)) = e i :=
  rfl
theorem val_termCast_zero (P : ℕ → Prop) (S : ℕ → Set ℕ) {n : ℕ} (e : Fin n → ℕ) (f : Empty → ℕ) :
    Semiterm.val (s := stdJ P S) e f (termCast (((0 : ℕ) : Semiterm LForm Empty n))) = 0 := rfl
theorem val_termCast_one (P : ℕ → Prop) (S : ℕ → Set ℕ) {n : ℕ} (e : Fin n → ℕ) (f : Empty → ℕ) :
    Semiterm.val (s := stdJ P S) e f (termCast (((1 : ℕ) : Semiterm LForm Empty n))) = 1 := rfl

theorem eval_AAt_eqF (P : ℕ → Prop) (S : ℕ → Set ℕ) {n : ℕ} (F : Semiformula LXJ Empty 2)
    (Y : Semiterm LXJ Empty n) (s t : Semiterm LForm Empty n) (e : Fin n → ℕ) (f : Empty → ℕ) :
    Semiformula.Eval (s := stdJ P S) e f (AAt F Y (eqF s t)) ↔
      Semiterm.val (s := stdJ P S) e f (termCast s) = Semiterm.val (s := stdJ P S) e f (termCast t) :=
  eval_eq_inl_fn P S (fun i => termCast (![s, t] i)) e f

theorem eval_AAt_Qat (P : ℕ → Prop) (S : ℕ → Set ℕ) {n : ℕ} (F : Semiformula LXJ Empty 2)
    (Y : Semiterm LXJ Empty n) (s t : Semiterm LForm Empty n) (e : Fin n → ℕ) (f : Empty → ℕ) :
    Semiformula.Eval (s := stdJ P S) e f (AAt F Y (Qat s t)) ↔
      Semiterm.val (s := stdJ P S) e f (termCast s) < Semiterm.val (s := stdJ P S) e f Y ∧
        Semiterm.val (s := stdJ P S) e f (termCast t) ∈
          S (Semiterm.val (s := stdJ P S) e f (termCast s)) := by
  show Semiformula.Eval (s := stdJ P S) e f
    (ltAt (termCast s) Y ⋏ Jat (termCast s) (termCast t)) ↔ _
  simp only [LogicalConnective.HomClass.map_and, eval_Jat, eval_ltAt]
  exact Iff.rfl

theorem mem_opJ_slotA (P : ℕ → Prop) (S : ℕ → Set ℕ) (x y : ℕ) (T : Set ℕ) :
    x ∈ opJ P slotA S y T ↔ (y = 1 ∧ x = 0) ∨ (1 < y ∧ x ∈ S 1) := by
  unfold opJ slotA
  simp only [AAt, Set.mem_ofPred_eq, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_or, eval_AAt_eqF, eval_AAt_Qat]
  simp only [val_termCast_bvar, val_termCast_zero, val_termCast_one]
  show ((y = 1 ∧ x = 0) ∨ (1 < y ∧ x ∈ Function.update S y T 1)) ↔ _
  by_cases hy : y = 1
  · subst hy; simp
  · rw [Function.update_of_ne (Ne.symm hy)]

theorem slotA_positive : PositiveP slotA := ⟨⟨trivial, trivial⟩, trivial⟩

theorem lfpChain_slotA (P : ℕ → Prop) (y : ℕ) :
    lfpChain P slotA y = {x | 1 ≤ y ∧ x = 0} := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
  set lower : ℕ → Set ℕ := fun j => if _ : j < y then lfpChain P slotA j else ∅ with hlower
  have hl1 : 1 < y → ∀ x, x ∈ lower 1 ↔ x = 0 := by
    intro h x
    simp only [hlower, dif_pos h]
    rw [ih 1 h]
    simp
  apply Set.Subset.antisymm
  · rw [lfpChain_eq]
    refine lfpAt_subset P slotA lower y ?_
    intro x hx
    rw [mem_opJ_slotA] at hx
    rcases hx with ⟨hy, hx0⟩ | ⟨hy, hx1⟩
    · subst hy; exact ⟨le_rfl, hx0⟩
    · exact ⟨hy.le, (hl1 hy x).mp hx1⟩
  · rintro x ⟨hy1, rfl⟩
    rw [lfpChain_eq]
    refine opJ_lfpAt_subset P slotA slotA_positive lower y ?_
    rw [mem_opJ_slotA]
    rcases eq_or_lt_of_le hy1 with h | h
    · exact Or.inl ⟨h.symm, rfl⟩
    · right
      refine ⟨h, ?_⟩
      exact (hl1 h 0).mpr rfl

/-- **The slot check on the iterated fixed point**: `J(y, x)` holds exactly when `1 ≤ y`
and `x = 0` — `y`-slot threshold `1`, `x`-slot value `0`. -/
theorem slotA_J_iff (P : ℕ → Prop) (y x : ℕ) :
    x ∈ lfpChain P slotA y ↔ 1 ≤ y ∧ x = 0 := by
  rw [lfpChain_slotA]; rfl

theorem slotA_consistent : Entailment.Consistent (IDw slotA) :=
  IDw_consistent slotA slotA_positive

end OrdinalAnalysis.IDw
