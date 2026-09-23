/-
  Ground terms of the ramified language and their values.

  The rank of a set atom `t ∈̇_μ s` depends on the *value* of its set argument
  `s` when `s` is ground (`Ramified/Rank.lean`): a level-`μ` name is a numeral
  coding a predicator, and the rank reads the stage recorded in that code.  So
  the notions this file provides — ground terms, their values in the standard
  model of arithmetic, and the numerals of `LRA` at every level — have to be
  available before the rank is defined.  They are independent of the reading
  of the fresh symbols: `LRA` has no function symbols beyond those of
  arithmetic, so a term's value never sees `X` or `∈̇_ν`.

  `Ramified/Evaluate.lean` builds the closed-term evaluator on top of this file.
-/
import OrdinalAnalysis.Ramified.Language

set_option autoImplicit false
set_option warn.classDefReducibility false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic


/-! ### A reading of `LRA`

Arithmetic standard, the fresh symbols empty.  Deliberately not an instance. -/

/-- The fresh symbols, read as empty.  `RALang` has no function symbols. -/
def raStruc : Structure RALang ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ _ _ => False

/-- **A standard model of `LRA`**: arithmetic standard, `X` and every `∈̇_ν`
empty. -/
def stdLRA : Structure LRA ℕ := Structure.add ℒₒᵣ RALang ℕ (str₂ := raStruc)

/-! ### Standard models of `LRA`

`LRA = Language.add ℒₒᵣ RALang`, and Foundation builds a structure for a sum of
languages out of structures for the summands (`Structure.add`).  The arithmetic
summand is always `Arithmetic.standardModel ℕ`; the fresh summand is a parameter
throughout this file, because nothing the evaluator does can see it. -/

/-- **A standard model of `LRA`**: arithmetic standard, the fresh symbols read by
`s₂`.  `Ramified/Literals.lean`'s `stdLRA` is the case `s₂ = raStruc`. -/
def raStd (s₂ : Structure RALang ℕ) : Structure LRA ℕ :=
  Structure.add ℒₒᵣ RALang ℕ (str₂ := s₂)

theorem stdLRA_eq_raStd : stdLRA = raStd raStruc := rfl

/-- The fresh symbols read by a unary `P` (for `X`) and a level-indexed family of
binary `M ν` (for `∈̇_ν`) — the family the boundedness port reinterprets. -/
def raStrucOf (P : ℕ → Prop) (M : Lv → ℕ → ℕ → Prop) : Structure RALang ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ r v =>
    match r with
    | RARel.X => P (v 0)
    | RARel.mem ν => M ν (v 0) (v 1)

/-- **The parametric standard model of `LRA`.** -/
def stdR (P : ℕ → Prop) (M : Lv → ℕ → ℕ → Prop) : Structure LRA ℕ := raStd (raStrucOf P M)

section StdR

variable (s₂ s₂' : Structure RALang ℕ)

/-- Every `raStd s₂` has the same function symbols: the arithmetic ones come from
the same `standardModel ℕ`, and `RALang` contributes none.  This is what makes
term values blind to the reading of `X` and of `∈̇`. -/
theorem raStd_func {k : ℕ} (fn : LRA.Func k) (w : Fin k → ℕ) :
    (raStd s₂).func fn w = (raStd s₂').func fn w := by
  rcases fn with fn | fn
  · rfl
  · exact PEmpty.elim fn

/-- A term of arithmetic transported to `LRA` keeps its value. -/
@[simp] theorem val_lMap_toLRA {n : ℕ} (t : Semiterm ℒₒᵣ ℕ n) (e : Fin n → ℕ) (f : ℕ → ℕ) :
    Semiterm.val (s := raStd s₂) e f (Semiterm.lMap toLRA t) = Semiterm.val (M := ℕ) e f t :=
  Structure.val_lMap_add₁ (str₂ := s₂) t e f

/-- A formula of arithmetic transported to `LRA` says in `raStd s₂` exactly what
it says in the standard model of arithmetic. -/
@[simp] theorem eval_lMap_toLRA {n : ℕ} (φ : Semiformula ℒₒᵣ ℕ n) (e : Fin n → ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := raStd s₂) e f (Semiformula.lMap toLRA φ)
      ↔ Semiformula.Eval (M := ℕ) e f φ :=
  Structure.eval_lMap_add₁ (str₂ := s₂) φ e f

/-- The reading of `∈̇_ν` in `stdR P M` is `M ν`. -/
theorem stdR_rel_mem (P : ℕ → Prop) (M : Lv → ℕ → ℕ → Prop) (ν : Lv) (v : Fin 2 → ℕ) :
    (stdR P M).rel (Sum.inr (RARel.mem ν)) v ↔ M ν (v 0) (v 1) := Iff.rfl

/-- The reading of `X` in `stdR P M` is `P`. -/
theorem stdR_rel_X (P : ℕ → Prop) (M : Lv → ℕ → ℕ → Prop) (v : Fin 1 → ℕ) :
    (stdR P M).rel (Sum.inr RARel.X) v ↔ P (v 0) := Iff.rfl

end StdR

/-! ### The numerals of `LRA` come from the numerals of `ℒₒᵣ`

`Ramified/Language.lean` proves this and keeps it `private` (it needed it only
for `num_injective`).  Reproved here, because `evTermR_numAtR` — "`m̄` denotes
`m`", at *every* level — is the one fact of this file that is not formal. -/

section LMapNumeral

variable {ξ : Type*} {n : ℕ}

private lemma lMapNum_zero :
    Semiterm.lMap toLRA ((0 : ℕ) : Semiterm ℒₒᵣ ξ n) = ((0 : ℕ) : Semiterm LRA ξ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, toLRA]

private lemma lMapNum_one :
    Semiterm.lMap toLRA ((1 : ℕ) : Semiterm ℒₒᵣ ξ n) = ((1 : ℕ) : Semiterm LRA ξ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, toLRA]

private lemma lMapNum_add (v : Fin 2 → Semiterm ℒₒᵣ ξ n) :
    Semiterm.lMap toLRA (Semiterm.Operator.Add.add.operator v) =
      Semiterm.Operator.Add.add.operator (Semiterm.lMap toLRA ∘ v) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, toLRA]
  funext i
  simp

private lemma numeral_succ_succ (L : Language) [L.Zero] [L.One] [L.Add] (k : ℕ) :
    ((k + 1 + 1 : ℕ) : Semiterm L ξ n) =
      Semiterm.Operator.Add.add.operator
        ![((k + 1 : ℕ) : Semiterm L ξ n), ((1 : ℕ) : Semiterm L ξ n)] := by
  have h : k + 1 ≠ 0 := Nat.succ_ne_zero k
  simp only [Semiterm.numeral, Semiterm.Operator.const,
    Semiterm.Operator.numeral_succ h, Semiterm.Operator.operator_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **The numeral of `LRA` is the `toLRA`-image of the numeral of `ℒₒᵣ`**, at
every level and over every free-variable type. -/
theorem lMap_toLRA_numeral (k : ℕ) :
    Semiterm.lMap toLRA ((k : ℕ) : Semiterm ℒₒᵣ ξ n) = ((k : ℕ) : Semiterm LRA ξ n) := by
  induction k with
  | zero => exact lMapNum_zero
  | succ k ih =>
    cases k with
    | zero => exact lMapNum_one
    | succ k =>
      rw [numeral_succ_succ ℒₒᵣ k, numeral_succ_succ LRA k, lMapNum_add]
      congr 1
      funext i
      fin_cases i
      · exact ih
      · exact lMapNum_one

end LMapNumeral

/-! ### Ground terms -/

/-- `t` contains neither a bound nor a free variable. -/
def GroundR {n : ℕ} (t : Semiterm LRA ℕ n) : Prop :=
  t.bv = ∅ ∧ t.freeVariables = ∅

instance instDecidableGroundR {n : ℕ} (t : Semiterm LRA ℕ n) : Decidable (GroundR t) := by
  unfold GroundR
  infer_instance

theorem not_groundR_bvar {n : ℕ} (x : Fin n) : ¬GroundR (#x : Semiterm LRA ℕ n) := by
  rintro ⟨hb, -⟩
  rw [Semiterm.bv_bvar] at hb
  exact absurd hb (Finset.singleton_ne_empty x)

theorem not_groundR_fvar {n : ℕ} (x : ℕ) : ¬GroundR (&x : Semiterm LRA ℕ n) := by
  rintro ⟨-, hf⟩
  rw [Semiterm.freeVariables_fvar] at hf
  exact absurd hf (Finset.singleton_ne_empty x)

/-- Groundness is componentwise. -/
theorem groundR_func_iff {n k : ℕ} (fn : LRA.Func k) (v : Fin k → Semiterm LRA ℕ n) :
    GroundR (Semiterm.func fn v) ↔ ∀ i, GroundR (v i) := by
  simp only [GroundR, Semiterm.bv_func, Semiterm.freeVariables_func,
    Finset.eq_empty_iff_forall_notMem, Finset.mem_biUnion, Finset.mem_univ, true_and,
    not_exists]
  constructor
  · rintro ⟨hb, hf⟩ i
    exact ⟨fun x => hb x i, fun x => hf x i⟩
  · intro h
    exact ⟨fun x i => (h i).1 x, fun x i => (h i).2 x⟩

/-- **At level `0`, closed and ground agree.** -/
theorem groundR_of_closed {t : SyntacticTerm LRA} (h : t.freeVariables = ∅) : GroundR t :=
  ⟨Finset.eq_empty_iff_forall_notMem.mpr fun x => x.elim0, h⟩

theorem freeVariables_of_groundR {n : ℕ} {t : Semiterm LRA ℕ n} (h : GroundR t) :
    t.freeVariables = ∅ := h.2

/-! ### The value of a ground term -/

/-- **The value of a ground term.**  Taken in `stdLRA`, which is `raStd raStruc`;
`val_groundR` says the choice is invisible. -/
def evTermR {n : ℕ} (t : Semiterm LRA ℕ n) : ℕ :=
  Semiterm.val (s := stdLRA) (fun _ => 0) (fun _ => 0) t

/-- A ground term has the same value in every `raStd s₂` and under every pair of
environments. -/
theorem val_groundR_congr (s₂ s₂' : Structure RALang ℕ) {n : ℕ} (e e' : Fin n → ℕ)
    (f f' : ℕ → ℕ) :
    ∀ {t : Semiterm LRA ℕ n}, GroundR t →
      Semiterm.val (s := raStd s₂) e f t = Semiterm.val (s := raStd s₂') e' f' t := by
  intro t
  induction t with
  | bvar x => exact fun h => absurd h (not_groundR_bvar x)
  | fvar x => exact fun h => absurd h (not_groundR_fvar x)
  | func fn v ih =>
      intro h
      have hv := (groundR_func_iff fn v).mp h
      have key : (fun i => Semiterm.val (s := raStd s₂) e f (v i))
          = (fun i => Semiterm.val (s := raStd s₂') e' f' (v i)) := funext fun i => ih i (hv i)
      simp only [Semiterm.val_func, Function.comp_def]
      rw [key]
      exact raStd_func s₂ s₂' fn _

/-- The value of a ground term *is* `evTermR`, in every standard structure. -/
theorem val_groundR (s₂ : Structure RALang ℕ) {n : ℕ} {t : Semiterm LRA ℕ n} (h : GroundR t)
    (e : Fin n → ℕ) (f : ℕ → ℕ) :
    Semiterm.val (s := raStd s₂) e f t = evTermR t :=
  val_groundR_congr s₂ raStruc e (fun _ => 0) f (fun _ => 0) h

/-- Groundness survives every rewriting. -/
theorem groundR_rew {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) :
    ∀ {t : Semiterm LRA ℕ n₁}, GroundR t → GroundR (ω t) := by
  intro t
  induction t with
  | bvar x => exact fun h => absurd h (not_groundR_bvar x)
  | fvar x => exact fun h => absurd h (not_groundR_fvar x)
  | func fn v ih =>
      intro h
      have hv := (groundR_func_iff fn v).mp h
      rw [ω.func' fn v]
      exact (groundR_func_iff fn _).mpr fun i => ih i (hv i)

/-- **A rewriting fixes a ground term.** -/
theorem rew_of_groundR {n : ℕ} (ω : Rew LRA ℕ n ℕ n) :
    ∀ {t : Semiterm LRA ℕ n}, GroundR t → ω t = t := by
  intro t
  induction t with
  | bvar x => exact fun h => absurd h (not_groundR_bvar x)
  | fvar x => exact fun h => absurd h (not_groundR_fvar x)
  | func fn v ih =>
      intro h
      have hv := (groundR_func_iff fn v).mp h
      rw [ω.func' fn v]
      exact congrArg (Semiterm.func fn) (funext fun i => ih i (hv i))

/-- …and so does its value. -/
theorem evTermR_rew {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) {t : Semiterm LRA ℕ n₁}
    (h : GroundR t) : evTermR (ω t) = evTermR t := by
  unfold evTermR
  rw [Semiterm.val_rew]
  exact val_groundR_congr _ _ _ _ _ _ h

/-! ### Numerals at every level -/

/-- The numeral `m̄`, as a term with `n` bound variables.  `numAtR (n := 0)` is
`Ramified/Language.lean`'s `num` on the nose. -/
def numAtR {n : ℕ} (m : ℕ) : Semiterm LRA ℕ n := Semiterm.numeral m

@[simp] theorem numAtR_zero (m : ℕ) : (numAtR m : SyntacticTerm LRA) = num m := rfl

/-- A numeral is a constant, so no rewriting moves it. -/
@[simp] theorem rew_numAtR {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (m : ℕ) :
    ω (numAtR m : Semiterm LRA ℕ n₁) = numAtR m := by
  simp [numAtR]

/-- A term coming from a *sentence* term by embedding and substituting the empty
vector is ground — the shape `Semiterm.Operator.operator` gives a constant. -/
theorem groundR_subst_emb {n : ℕ} :
    ∀ t : Semiterm LRA Empty 0,
      GroundR ((Rew.subst (![] : Fin 0 → Semiterm LRA ℕ n)) (Rew.emb t : Semiterm LRA ℕ 0)) := by
  intro t
  induction t with
  | bvar x => exact x.elim0
  | fvar x => exact x.elim
  | func fn v ih =>
      have h1 : (Rew.emb (Semiterm.func fn v) : Semiterm LRA ℕ 0)
          = Semiterm.func fn fun i => (Rew.emb (v i) : Semiterm LRA ℕ 0) :=
        Rew.func' _ fn v
      have h2 : (Rew.subst (![] : Fin 0 → Semiterm LRA ℕ n))
            (Semiterm.func fn fun i => (Rew.emb (v i) : Semiterm LRA ℕ 0))
          = Semiterm.func fn fun i =>
              (Rew.subst (![] : Fin 0 → Semiterm LRA ℕ n)) (Rew.emb (v i)) :=
        Rew.func' _ fn _
      rw [h1, h2]
      exact (groundR_func_iff fn _).mpr ih

@[simp] theorem groundR_numAtR {n : ℕ} (m : ℕ) : GroundR (numAtR m : Semiterm LRA ℕ n) :=
  groundR_subst_emb (Semiterm.Operator.numeral LRA m).term

@[simp] theorem groundR_num (m : ℕ) : GroundR (num m) := groundR_numAtR m

/-- **`m̄` denotes `m`**, at every level. -/
@[simp] theorem evTermR_numAtR {n : ℕ} (m : ℕ) : evTermR (numAtR m : Semiterm LRA ℕ n) = m := by
  have h : (numAtR m : Semiterm LRA ℕ n) = Semiterm.lMap toLRA ((m : ℕ) : Semiterm ℒₒᵣ ℕ n) :=
    (lMap_toLRA_numeral m).symm
  unfold evTermR
  rw [stdLRA_eq_raStd, h, val_lMap_toLRA]
  simp

@[simp] theorem evTermR_num (m : ℕ) : evTermR (num m) = m := evTermR_numAtR m

/-- The value of a compound term, componentwise. -/
theorem evTermR_func {n k : ℕ} (f : LRA.Func k) (v : Fin k → Semiterm LRA ℕ n) :
    evTermR (Semiterm.func f v) = stdLRA.func f fun i => evTermR (v i) := rfl

end Ramified

end OrdinalAnalysis
