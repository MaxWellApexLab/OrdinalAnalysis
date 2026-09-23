/-
  Closed-term evaluation for the ramified language (design **D2**).

  This is `Gentzen/Evaluate.lean` transported from `LX = ℒₒᵣ + {X}` to
  `LRA = ℒₒᵣ + {X} ∪ {∈̇_ν}`.  The mathematics is unchanged, because the
  evaluator only ever touches *terms*, and `RALang` contributes no function
  symbols at all (`RALang.Func k = PEmpty`, `Ramified/Language.lean`): a set atom
  `t ∈̇_ν s` is an ordinary binary relation atom whose two arguments happen to be
  numbers, and `evR` evaluates both of them exactly as it evaluates the two
  arguments of `t = s`.  That is the whole of what D2's new atom kinds cost here,
  and it is the reason the design note's `{Evaluate,NumSubst,Embed}` row is a
  *port* rather than new mathematics; the second-order design D1 would instead
  have had to evaluate underneath a set variable.

  Four things about the shape, three of them inherited.

  * The value of a term is taken in a standard model of `LRA`.  Which reading of
    the fresh symbols is irrelevant, and the file says so by being parametric:
    every statement is over `raStd s₂` for an arbitrary `Structure RALang ℕ`.
    `Ramified/Literals.lean`'s `stdLRA` is `raStd raStruc` on the nose, and
    `stdR P M` — `X ↦ P`, `∈̇_ν ↦ M ν` — is the family the boundedness port will
    want, supplied here because `Language.lean` has none.

  * "Closed" is replaced by **ground** — no free *and* no bound variables — so
    that the evaluator can act underneath a quantifier.  `groundR_of_closed` is
    the level-`0` coincidence.

  * `evTR` is **deep**: a ground term becomes the numeral of its value, a
    non-ground compound term is rebuilt from its evaluated arguments.

  * The naive substitution law `evR (φ/[t]) = (evR φ)/[n̄]` is false for every
    evaluator whatsoever (`Gentzen/Evaluate.lean`'s header has the counterexample
    and it survives the change of language verbatim).  What holds, and what the
    ω-calculus consumes, is the *normalised* law
    `evR (φ/[t]) = evR ((evR φ)/[n̄])` — `evR_subst_key`.

  The one genuinely ramified addition is the rank/level pair:

      rank  (evR φ) = rank  φ            `rank_evR`
      lvlOf (evR φ) = lvlOf φ            `lvlOf_evR`

  both immediate, because `Ramified/Rank.lean`'s `rank` and `Ramified/Code.lean`'s
  `lvlOf` read a *relation symbol* and `evR` never touches one.  `rank_evR` is
  what `InstantiationR.rank_nf` asks for and is the reason `evInstR` exists at
  all: `Instantiation.complexity_nf` is the wrong law once cuts are ranked by an
  ordinal.
-/
import OrdinalAnalysis.Ramified.Literals

set_option autoImplicit false
set_option warn.classDefReducibility false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

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

/-! ### The term evaluator -/

/-- **The term evaluator**: ground ↦ the numeral of its value, and otherwise
evaluate the arguments and rebuild. -/
def evTR {n : ℕ} : Semiterm LRA ℕ n → Semiterm LRA ℕ n
  | #x => #x
  | &x => &x
  | Semiterm.func f v =>
      if GroundR (Semiterm.func f v) then numAtR (evTermR (Semiterm.func f v))
      else Semiterm.func f fun i => evTR (v i)

@[simp] theorem evTR_bvar {n : ℕ} (x : Fin n) : evTR (#x : Semiterm LRA ℕ n) = #x := rfl

@[simp] theorem evTR_fvar {n : ℕ} (x : ℕ) : evTR (&x : Semiterm LRA ℕ n) = &x := rfl

theorem evTR_func {n k : ℕ} (f : LRA.Func k) (v : Fin k → Semiterm LRA ℕ n) :
    evTR (Semiterm.func f v)
      = if GroundR (Semiterm.func f v) then numAtR (evTermR (Semiterm.func f v))
        else Semiterm.func f fun i => evTR (v i) := rfl

/-- The defining clause on a ground term. -/
theorem evTR_of_groundR {n : ℕ} {t : Semiterm LRA ℕ n} (h : GroundR t) :
    evTR t = numAtR (evTermR t) := by
  cases t with
  | bvar x => exact absurd h (not_groundR_bvar x)
  | fvar x => exact absurd h (not_groundR_fvar x)
  | func f v => rw [evTR_func]; exact if_pos h

/-- The defining clause on a non-ground compound term. -/
theorem evTR_func_of_not_groundR {n k : ℕ} (f : LRA.Func k) (v : Fin k → Semiterm LRA ℕ n)
    (h : ¬GroundR (Semiterm.func f v)) :
    evTR (Semiterm.func f v) = Semiterm.func f fun i => evTR (v i) := by
  rw [evTR_func]; exact if_neg h

@[simp] theorem evTR_numAtR {n : ℕ} (m : ℕ) : evTR (numAtR m : Semiterm LRA ℕ n) = numAtR m := by
  rw [evTR_of_groundR (groundR_numAtR m), evTermR_numAtR]

@[simp] theorem evTR_num (m : ℕ) : evTR (num m) = num m := evTR_numAtR m

/-- **`evTR` neither creates nor destroys groundness.** -/
@[simp] theorem groundR_evTR_iff {n : ℕ} {t : Semiterm LRA ℕ n} :
    GroundR (evTR t) ↔ GroundR t := by
  induction t with
  | bvar x => rw [evTR_bvar]
  | fvar x => rw [evTR_fvar]
  | func f v ih =>
      by_cases h : GroundR (Semiterm.func f v)
      · exact iff_of_true (by rw [evTR_of_groundR h]; exact groundR_numAtR _) h
      · rw [evTR_func_of_not_groundR f v h, groundR_func_iff, groundR_func_iff]
        exact forall_congr' fun i => ih i

theorem groundR_evTR {n : ℕ} {t : Semiterm LRA ℕ n} (h : GroundR t) : GroundR (evTR t) :=
  groundR_evTR_iff.mpr h

@[simp] theorem evTR_idem {n : ℕ} (t : Semiterm LRA ℕ n) : evTR (evTR t) = evTR t := by
  induction t with
  | bvar x => rw [evTR_bvar, evTR_bvar]
  | fvar x => rw [evTR_fvar, evTR_fvar]
  | func f v ih =>
      by_cases h : GroundR (Semiterm.func f v)
      · rw [evTR_of_groundR h, evTR_numAtR]
      · have hn : ¬GroundR (Semiterm.func f fun i => evTR (v i)) := by
          rw [groundR_func_iff]
          intro hc
          exact h ((groundR_func_iff f v).mpr fun i => groundR_evTR_iff.mp (hc i))
        rw [evTR_func_of_not_groundR f v h, evTR_func_of_not_groundR f _ hn]
        exact congrArg (Semiterm.func f) (funext fun i => ih i)

/-- **`evTR` does not change what a term denotes**, under every environment. -/
theorem val_evTR (s₂ : Structure RALang ℕ) {n : ℕ} (t : Semiterm LRA ℕ n) (e : Fin n → ℕ)
    (f : ℕ → ℕ) :
    Semiterm.val (s := raStd s₂) e f (evTR t) = Semiterm.val (s := raStd s₂) e f t := by
  induction t with
  | bvar x => rw [evTR_bvar]
  | fvar x => rw [evTR_fvar]
  | func fn v ih =>
      by_cases h : GroundR (Semiterm.func fn v)
      · rw [evTR_of_groundR h, val_groundR s₂ (groundR_numAtR _) e f, evTermR_numAtR,
          val_groundR s₂ h e f]
      · rw [evTR_func_of_not_groundR fn v h]
        simp only [Semiterm.val_func, Function.comp_def]
        exact congrArg ((raStd s₂).func fn) (funext fun i => ih i)

theorem evTermR_evTR {n : ℕ} (t : Semiterm LRA ℕ n) : evTermR (evTR t) = evTermR t :=
  val_evTR raStruc t _ _

/-- **`evTR` does not move the free variables.** -/
@[simp] theorem freeVariables_evTR {n : ℕ} (t : Semiterm LRA ℕ n) :
    (evTR t).freeVariables = t.freeVariables := by
  induction t with
  | bvar x => rw [evTR_bvar]
  | fvar x => rw [evTR_fvar]
  | func fn v ih =>
      by_cases h : GroundR (Semiterm.func fn v)
      · rw [evTR_of_groundR h, (groundR_numAtR (n := n) (evTermR (Semiterm.func fn v))).2, h.2]
      · rw [evTR_func_of_not_groundR fn v h, Semiterm.freeVariables_func,
          Semiterm.freeVariables_func]
        exact congrArg (Finset.biUnion Finset.univ) (funext fun i => ih i)

/-! ### The formula evaluator -/

/-- **The formula evaluator**: every argument of every atom is evaluated by
`evTR` — including *both* arguments of a set atom `t ∈̇_ν s` — while the
connectives, the quantifiers and the relation symbols are untouched. -/
def evR : {n : ℕ} → Semiformula LRA ℕ n → Semiformula LRA ℕ n
  | _, Semiformula.verum => Semiformula.verum
  | _, Semiformula.falsum => Semiformula.falsum
  | _, Semiformula.rel r v => Semiformula.rel r fun i => evTR (v i)
  | _, Semiformula.nrel r v => Semiformula.nrel r fun i => evTR (v i)
  | _, Semiformula.and φ ψ => Semiformula.and (evR φ) (evR ψ)
  | _, Semiformula.or φ ψ => Semiformula.or (evR φ) (evR ψ)
  | _, Semiformula.all φ => Semiformula.all (evR φ)
  | _, Semiformula.exs φ => Semiformula.exs (evR φ)

@[simp] theorem evR_verum {n : ℕ} : evR (⊤ : Semiformula LRA ℕ n) = ⊤ := rfl

@[simp] theorem evR_falsum {n : ℕ} : evR (⊥ : Semiformula LRA ℕ n) = ⊥ := rfl

@[simp] theorem evR_rel {n k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    evR (Semiformula.rel r v) = Semiformula.rel r fun i => evTR (v i) := rfl

@[simp] theorem evR_nrel {n k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    evR (Semiformula.nrel r v) = Semiformula.nrel r fun i => evTR (v i) := rfl

@[simp] theorem evR_and {n : ℕ} (φ ψ : Semiformula LRA ℕ n) : evR (φ ⋏ ψ) = evR φ ⋏ evR ψ := rfl

@[simp] theorem evR_or {n : ℕ} (φ ψ : Semiformula LRA ℕ n) : evR (φ ⋎ ψ) = evR φ ⋎ evR ψ := rfl

@[simp] theorem evR_all {n : ℕ} (φ : Semiformula LRA ℕ (n + 1)) : evR (∀¹ φ) = ∀¹ (evR φ) := rfl

@[simp] theorem evR_exs {n : ℕ} (φ : Semiformula LRA ℕ (n + 1)) : evR (∃¹ φ) = ∃¹ (evR φ) := rfl

/-- **`evR` commutes with negation.** -/
@[simp] theorem evR_neg {n : ℕ} (φ : Semiformula LRA ℕ n) : evR (∼φ) = ∼(evR φ) := by
  induction φ using Semiformula.rec' <;> simp [*]

@[simp] theorem evR_imp {n : ℕ} (φ ψ : Semiformula LRA ℕ n) :
    evR (φ 🡒 ψ) = evR φ 🡒 evR ψ := by
  simp [Semiformula.imp_eq]

/-- **`evR` is idempotent.** -/
@[simp] theorem evR_idem {n : ℕ} (φ : Semiformula LRA ℕ n) : evR (evR φ) = evR φ := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => exact congrArg (Semiformula.rel r) (funext fun i => evTR_idem (v i))
  | hnrel r v => exact congrArg (Semiformula.nrel r) (funext fun i => evTR_idem (v i))
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

/-- **`evR` does not change the logical shape of a formula.** -/
@[simp] theorem complexity_evR {n : ℕ} (φ : Semiformula LRA ℕ n) :
    (evR φ).complexity = φ.complexity := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => rfl
  | hnrel r v => rfl
  | hand φ ψ ihφ ihψ =>
      rw [evR_and, Semiformula.complexity_and, Semiformula.complexity_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
      rw [evR_or, Semiformula.complexity_or, Semiformula.complexity_or, ihφ, ihψ]
  | hall φ ih => rw [evR_all, Semiformula.complexity_all, Semiformula.complexity_all, ih]
  | hexs φ ih => rw [evR_exs, Semiformula.complexity_exs, Semiformula.complexity_exs, ih]

/-! ### The two ramified invariants

`rank` and `lvlOf` read a *relation symbol* and `evR` rewrites only inside the
argument vectors, so both are literally blind to the evaluation.  `rank_evR` is
`InstantiationR.rank_nf` — the field `Instantiation` does not have and an
ordinal-ranked calculus must. -/

/-- **`evR` preserves the cut rank.** -/
@[simp] theorem rank_evR {n : ℕ} (φ : Semiformula LRA ℕ n) : rank (evR φ) = rank φ := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => rfl
  | hnrel r v => rfl
  | hand φ ψ ihφ ihψ => rw [evR_and, rank_and, rank_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ => rw [evR_or, rank_or, rank_or, ihφ, ihψ]
  | hall φ ih => rw [evR_all, rank_all, rank_all, ih]
  | hexs φ ih => rw [evR_exs, rank_exs, rank_exs, ih]

/-- **`evR` preserves the level.** -/
@[simp] theorem lvlOf_evR {n : ℕ} (φ : Semiformula LRA ℕ n) : lvlOf (evR φ) = lvlOf φ := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => rfl
  | hnrel r v => rfl
  | hand φ ψ ihφ ihψ => rw [evR_and, lvlOf_and, lvlOf_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ => rw [evR_or, lvlOf_or, lvlOf_or, ihφ, ihψ]
  | hall φ ih => rw [evR_all, lvlOf_all, lvlOf_all, ih]
  | hexs φ ih => rw [evR_exs, lvlOf_exs, lvlOf_exs, ih]

/-- An atom whose arguments are numerals is a fixed point of `evR`. -/
@[simp] theorem evR_rel_numAtR {n k : ℕ} (r : LRA.Rel k) (w : Fin k → ℕ) :
    evR (Semiformula.rel r fun i => (numAtR (w i) : Semiterm LRA ℕ n))
      = Semiformula.rel r fun i => (numAtR (w i) : Semiterm LRA ℕ n) :=
  congrArg (Semiformula.rel r) (funext fun i => evTR_numAtR (w i))

@[simp] theorem evR_nrel_numAtR {n k : ℕ} (r : LRA.Rel k) (w : Fin k → ℕ) :
    evR (Semiformula.nrel r fun i => (numAtR (w i) : Semiterm LRA ℕ n))
      = Semiformula.nrel r fun i => (numAtR (w i) : Semiterm LRA ℕ n) :=
  congrArg (Semiformula.nrel r) (funext fun i => evTR_numAtR (w i))

/-- **`evR` does not move the free variables.** -/
@[simp] theorem freeVariables_evR {n : ℕ} (φ : Semiformula LRA ℕ n) :
    (evR φ).freeVariables = φ.freeVariables := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
      rw [evR_rel, Semiformula.freeVariables_rel, Semiformula.freeVariables_rel]
      exact congrArg (Finset.biUnion Finset.univ) (funext fun i => freeVariables_evTR (v i))
  | hnrel r v =>
      rw [evR_nrel, Semiformula.freeVariables_nrel, Semiformula.freeVariables_nrel]
      exact congrArg (Finset.biUnion Finset.univ) (funext fun i => freeVariables_evTR (v i))
  | hand φ ψ ihφ ihψ =>
      rw [evR_and, Semiformula.freeVariables_and, Semiformula.freeVariables_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
      rw [evR_or, Semiformula.freeVariables_or, Semiformula.freeVariables_or, ihφ, ihψ]
  | hall φ ih => exact ih
  | hexs φ ih => exact ih

/-! ### The set atoms

`Semiformula.rel`'s arity is an index, so a term carrying
`Sum.inr (RARel.mem ν) : LRA.Rel 2` is not type-correct at implicit
transparency and neither `rw` nor `simp` will enter it — the `Idiom.Xrel` trap,
recorded in `Ramified/Language.lean` for the injectivity lemmas.  Both equations
below are therefore `congrArg`s. -/

/-- **`evR` on a set atom evaluates both arguments.**  A level-`ν` membership
atom is an ordinary binary relation atom; this is the whole of what D2's new
atom kinds cost the evaluator. -/
theorem evR_memAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    evR (memAt ν t s) = memAt ν (evTR t) (evTR s) := by
  have h : (fun i => evTR ((![t, s] : Fin 2 → Semiterm LRA ℕ n) i)) = ![evTR t, evTR s] := by
    funext i
    fin_cases i <;> rfl
  exact congrArg (Semiformula.rel (Sum.inr (RARel.mem ν))) h

/-- The negated form. -/
theorem evR_nmemAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    evR (nmemAt ν t s) = nmemAt ν (evTR t) (evTR s) := by
  have h : (fun i => evTR ((![t, s] : Fin 2 → Semiterm LRA ℕ n) i)) = ![evTR t, evTR s] := by
    funext i
    fin_cases i <;> rfl
  exact congrArg (Semiformula.nrel (Sum.inr (RARel.mem ν))) h

/-- A set atom between numerals is a fixed point — the shape a (Pr) inference
concludes. -/
@[simp] theorem evR_memAt_num {n : ℕ} (ν : Lv) (k m : ℕ) :
    evR (memAt ν (numAtR k : Semiterm LRA ℕ n) (numAtR m)) = memAt ν (numAtR k) (numAtR m) := by
  rw [evR_memAt, evTR_numAtR, evTR_numAtR]

@[simp] theorem evR_nmemAt_num {n : ℕ} (ν : Lv) (k m : ℕ) :
    evR (nmemAt ν (numAtR k : Semiterm LRA ℕ n) (numAtR m)) = nmemAt ν (numAtR k) (numAtR m) := by
  rw [evR_nmemAt, evTR_numAtR, evTR_numAtR]

/-- `evR` on the fresh unary predicate. -/
theorem evR_Xat {n : ℕ} (t : Semiterm LRA ℕ n) : evR (Xat t) = Xat (evTR t) := by
  have h : (fun i => evTR ((![t] : Fin 1 → Semiterm LRA ℕ n) i)) = ![evTR t] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  exact congrArg (Semiformula.rel (Sum.inr RARel.X)) h

@[simp] theorem evR_Xat_num {n : ℕ} (m : ℕ) :
    evR (Xat (numAtR m : Semiterm LRA ℕ n)) = Xat (numAtR m) := by
  rw [evR_Xat, evTR_numAtR]

/-! ### Truth is preserved

Unconditional: every level, every reading of the fresh symbols, every
environment.  A numeral denotes its value, so replacing a ground subterm by the
numeral of its value cannot change the value of an atom — and a set atom is an
atom like any other. -/

/-- **`evR` preserves truth in every standard model of `LRA`.** -/
theorem eval_evR (s₂ : Structure RALang ℕ) (f : ℕ → ℕ) :
    ∀ {n : ℕ} (φ : Semiformula LRA ℕ n) (e : Fin n → ℕ),
      (Semiformula.Eval (s := raStd s₂) e f (evR φ)
        ↔ Semiformula.Eval (s := raStd s₂) e f φ) := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro e; simp
  | hfalsum => intro e; simp
  | hrel r v =>
      intro e
      simp only [evR_rel, Semiformula.eval_rel, Function.comp_def]
      exact Iff.of_eq (congrArg ((raStd s₂).rel r) (funext fun i => val_evTR s₂ (v i) e f))
  | hnrel r v =>
      intro e
      simp only [evR_nrel, Semiformula.eval_nrel, Function.comp_def]
      exact not_congr
        (Iff.of_eq (congrArg ((raStd s₂).rel r) (funext fun i => val_evTR s₂ (v i) e f)))
  | hand φ ψ ihφ ihψ => intro e; simp only [evR_and, LogicalConnective.HomClass.map_and]
                        exact and_congr (ihφ e) (ihψ e)
  | hor φ ψ ihφ ihψ => intro e; simp only [evR_or, LogicalConnective.HomClass.map_or]
                       exact or_congr (ihφ e) (ihψ e)
  | hall φ ih =>
      intro e
      simp only [evR_all, Semiformula.eval_all]
      exact forall_congr' fun x => ih (x :> e)
  | hexs φ ih =>
      intro e
      simp only [evR_exs, Semiformula.eval_ex]
      exact exists_congr fun x => ih (x :> e)

/-- The form the ω-completeness lemma uses. -/
theorem eval_evR_zero (s₂ : Structure RALang ℕ) (f : ℕ → ℕ) (φ : Proposition LRA) :
    Semiformula.Eval (s := raStd s₂) ![] f (evR φ)
      ↔ Semiformula.Eval (s := raStd s₂) ![] f φ :=
  eval_evR s₂ f φ ![]

/-- The same in the parametric family. -/
theorem eval_evR_stdR (P : ℕ → Prop) (M : Lv → ℕ → ℕ → Prop) (f : ℕ → ℕ)
    {n : ℕ} (φ : Semiformula LRA ℕ n) (e : Fin n → ℕ) :
    Semiformula.Eval (s := stdR P M) e f (evR φ)
      ↔ Semiformula.Eval (s := stdR P M) e f φ :=
  eval_evR (raStrucOf P M) f φ e

/-! ### Congruence: normalising before a rewriting does not change the result -/

theorem val_rew_evTR (s₂ : Structure RALang ℕ) {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂)
    (t : Semiterm LRA ℕ n₁) (e : Fin n₂ → ℕ) (f : ℕ → ℕ) :
    Semiterm.val (s := raStd s₂) e f (ω (evTR t))
      = Semiterm.val (s := raStd s₂) e f (ω t) := by
  rw [Semiterm.val_rew, Semiterm.val_rew]
  exact val_evTR s₂ t _ _

theorem evTermR_rew_evTR {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (t : Semiterm LRA ℕ n₁) :
    evTermR (ω (evTR t)) = evTermR (ω t) := by
  unfold evTermR
  exact val_rew_evTR raStruc ω t _ _

/-- `evTR` under a rewriting does not change groundness either. -/
theorem groundR_rew_evTR_iff {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (t : Semiterm LRA ℕ n₁) :
    GroundR (ω (evTR t)) ↔ GroundR (ω t) := by
  induction t with
  | bvar x => rw [evTR_bvar]
  | fvar x => rw [evTR_fvar]
  | func f v ih =>
      by_cases h : GroundR (Semiterm.func f v)
      · exact iff_of_true (by rw [evTR_of_groundR h, rew_numAtR]; exact groundR_numAtR _)
          (groundR_rew ω h)
      · rw [evTR_func_of_not_groundR f v h, ω.func' f fun i => evTR (v i), ω.func' f v,
          groundR_func_iff, groundR_func_iff]
        exact forall_congr' fun i => ih i

/-- **The term-level congruence.** -/
theorem evTR_rew_evTR {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (t : Semiterm LRA ℕ n₁) :
    evTR (ω (evTR t)) = evTR (ω t) := by
  induction t with
  | bvar x => rw [evTR_bvar]
  | fvar x => rw [evTR_fvar]
  | func f v ih =>
      by_cases h : GroundR (Semiterm.func f v)
      · rw [evTR_of_groundR h, rew_numAtR, evTR_numAtR, evTR_of_groundR (groundR_rew ω h),
          evTermR_rew ω h]
      · have hiff : GroundR (Semiterm.func f fun i => ω (evTR (v i)))
            ↔ GroundR (Semiterm.func f fun i => ω (v i)) := by
          rw [groundR_func_iff, groundR_func_iff]
          exact forall_congr' fun i => groundR_rew_evTR_iff ω (v i)
        rw [evTR_func_of_not_groundR f v h, ω.func' f fun i => evTR (v i), ω.func' f v]
        by_cases hg : GroundR (Semiterm.func f fun i => ω (v i))
        · have hval : evTermR (Semiterm.func f fun i => ω (evTR (v i)))
              = evTermR (Semiterm.func f fun i => ω (v i)) := by
            have hx := evTermR_rew_evTR ω (Semiterm.func f v)
            rwa [evTR_func_of_not_groundR f v h, ω.func' f fun i => evTR (v i),
              ω.func' f v] at hx
          rw [evTR_of_groundR (hiff.mpr hg), evTR_of_groundR hg, hval]
        · rw [evTR_func_of_not_groundR f _ fun hc => hg (hiff.mp hc),
            evTR_func_of_not_groundR f _ hg]
          exact congrArg (Semiterm.func f) (funext fun i => ih i)

/-- **The formula-level congruence.** -/
theorem evR_rew_evR {n₁ : ℕ} :
    ∀ (φ : Semiformula LRA ℕ n₁) (n₂ : ℕ) (ω : Rew LRA ℕ n₁ ℕ n₂),
      evR (ω ▹ evR φ) = evR (ω ▹ φ) := by
  intro φ
  induction φ using Semiformula.rec' with
  | hverum => intro n₂ ω; simp
  | hfalsum => intro n₂ ω; simp
  | hrel r v =>
      intro n₂ ω
      simp only [evR_rel, Semiformula.rew_rel]
      exact congrArg (Semiformula.rel r) (funext fun i => evTR_rew_evTR ω (v i))
  | hnrel r v =>
      intro n₂ ω
      simp only [evR_nrel, Semiformula.rew_nrel]
      exact congrArg (Semiformula.nrel r) (funext fun i => evTR_rew_evTR ω (v i))
  | hand φ ψ ihφ ihψ =>
      intro n₂ ω
      simp only [LogicalConnective.HomClass.map_and, evR_and, ihφ n₂ ω, ihψ n₂ ω]
  | hor φ ψ ihφ ihψ =>
      intro n₂ ω
      simp only [LogicalConnective.HomClass.map_or, evR_or, ihφ n₂ ω, ihψ n₂ ω]
  | hall φ ih =>
      intro n₂ ω
      simp only [Rewriting.app_all, evR_all, ih (n₂ + 1) ω.q]
  | hexs φ ih =>
      intro n₂ ω
      simp only [Rewriting.app_exs, evR_exs, ih (n₂ + 1) ω.q]

/-! ### Value dependence -/

theorem val_congr_of_evTR (s₂ : Structure RALang ℕ) {n : ℕ} {t u : Semiterm LRA ℕ n}
    (h : evTR t = evTR u) (e : Fin n → ℕ) (f : ℕ → ℕ) :
    Semiterm.val (s := raStd s₂) e f t = Semiterm.val (s := raStd s₂) e f u := by
  rw [← val_evTR s₂ t e f, ← val_evTR s₂ u e f, h]

theorem evTermR_congr_of_evTR {n : ℕ} {t u : Semiterm LRA ℕ n} (h : evTR t = evTR u) :
    evTermR t = evTermR u := val_congr_of_evTR raStruc h _ _

theorem evTR_rew_congr {n₁ n₂ : ℕ} (ρ : Rew LRA ℕ n₁ ℕ n₂) {t u : Semiterm LRA ℕ n₁}
    (h : evTR t = evTR u) : evTR (ρ t) = evTR (ρ u) := by
  rw [← evTR_rew_evTR ρ t, ← evTR_rew_evTR ρ u, h]

/-- **Two rewritings the evaluator cannot tell apart.** -/
def RewEqR {n₁ n₂ : ℕ} (ω ω' : Rew LRA ℕ n₁ ℕ n₂) : Prop :=
  (∀ i : Fin n₁, evTR (ω #i) = evTR (ω' #i)) ∧ ∀ x : ℕ, evTR (ω &x) = evTR (ω' &x)

/-- `RewEqR` survives lifting under a binder. -/
theorem RewEqR.q {n₁ n₂ : ℕ} {ω ω' : Rew LRA ℕ n₁ ℕ n₂} (h : RewEqR ω ω') :
    RewEqR ω.q ω'.q := by
  constructor
  · intro i
    induction i using Fin.cases with
    | zero => rw [Rew.q_bvar_zero, Rew.q_bvar_zero]
    | succ j =>
        rw [Rew.q_bvar_succ, Rew.q_bvar_succ]
        exact evTR_rew_congr Rew.bShift (h.1 j)
  · intro x
    rw [Rew.q_fvar, Rew.q_fvar]
    exact evTR_rew_congr Rew.bShift (h.2 x)

/-- **The term-level value dependence.** -/
theorem evTR_congr {n₁ n₂ : ℕ} {ω ω' : Rew LRA ℕ n₁ ℕ n₂} (h : RewEqR ω ω')
    (t : Semiterm LRA ℕ n₁) : evTR (ω t) = evTR (ω' t) := by
  induction t with
  | bvar x => exact h.1 x
  | fvar x => exact h.2 x
  | func f v ih =>
      have hgi : ∀ i, (GroundR (ω (v i)) ↔ GroundR (ω' (v i))) := fun i => by
        have e1 : GroundR (evTR (ω (v i))) ↔ GroundR (ω (v i)) := groundR_evTR_iff
        have e2 : GroundR (evTR (ω' (v i))) ↔ GroundR (ω' (v i)) := groundR_evTR_iff
        rw [← e1, ← e2, ih i]
      rw [ω.func' f v, ω'.func' f v]
      by_cases hg : GroundR (Semiterm.func f fun i => ω (v i))
      · have hg' : GroundR (Semiterm.func f fun i => ω' (v i)) :=
          (groundR_func_iff f _).mpr fun i => (hgi i).mp ((groundR_func_iff f _).mp hg i)
        rw [evTR_of_groundR hg, evTR_of_groundR hg', evTermR_func, evTermR_func]
        exact congrArg (fun m => (numAtR m : Semiterm LRA ℕ n₂))
          (congrArg (stdLRA.func f)
            (funext fun i => evTermR_congr_of_evTR (ih i)))
      · have hg' : ¬GroundR (Semiterm.func f fun i => ω' (v i)) := fun hc =>
          hg ((groundR_func_iff f _).mpr fun i => (hgi i).mpr ((groundR_func_iff f _).mp hc i))
        rw [evTR_func_of_not_groundR f _ hg, evTR_func_of_not_groundR f _ hg']
        exact congrArg (Semiterm.func f) (funext fun i => ih i)

/-- **The formula-level value dependence.** -/
theorem evR_rew_congr {n₁ : ℕ} :
    ∀ (φ : Semiformula LRA ℕ n₁) (n₂ : ℕ) (ω ω' : Rew LRA ℕ n₁ ℕ n₂), RewEqR ω ω' →
      evR (ω ▹ φ) = evR (ω' ▹ φ) := by
  intro φ
  induction φ using Semiformula.rec' with
  | hverum => intro n₂ ω ω' _; simp
  | hfalsum => intro n₂ ω ω' _; simp
  | hrel r v =>
      intro n₂ ω ω' h
      simp only [Semiformula.rew_rel, evR_rel]
      exact congrArg (Semiformula.rel r) (funext fun i => evTR_congr h (v i))
  | hnrel r v =>
      intro n₂ ω ω' h
      simp only [Semiformula.rew_nrel, evR_nrel]
      exact congrArg (Semiformula.nrel r) (funext fun i => evTR_congr h (v i))
  | hand φ ψ ihφ ihψ =>
      intro n₂ ω ω' h
      simp only [LogicalConnective.HomClass.map_and, evR_and, ihφ n₂ ω ω' h, ihψ n₂ ω ω' h]
  | hor φ ψ ihφ ihψ =>
      intro n₂ ω ω' h
      simp only [LogicalConnective.HomClass.map_or, evR_or, ihφ n₂ ω ω' h, ihψ n₂ ω ω' h]
  | hall φ ih =>
      intro n₂ ω ω' h
      simp only [Rewriting.app_all, evR_all, ih (n₂ + 1) ω.q ω'.q h.q]
  | hexs φ ih =>
      intro n₂ ω ω' h
      simp only [Rewriting.app_exs, evR_exs, ih (n₂ + 1) ω.q ω'.q h.q]

/-- **Simultaneous substitution of ground terms depends only on their values.** -/
theorem evR_substs_ground {k : ℕ} {w w' : Fin k → SyntacticTerm LRA}
    (hw : ∀ i, GroundR (w i)) (hw' : ∀ i, GroundR (w' i))
    (hval : ∀ i, evTermR (w i) = evTermR (w' i)) (φ : Semiformula LRA ℕ k) :
    evR (Rew.subst w ▹ φ) = evR (Rew.subst w' ▹ φ) := by
  refine evR_rew_congr φ 0 (Rew.subst w) (Rew.subst w') ⟨fun i => ?_, fun x => ?_⟩
  · rw [Rew.subst_bvar, Rew.subst_bvar, evTR_of_groundR (hw i), evTR_of_groundR (hw' i), hval i]
  · rw [Rew.subst_fvar, Rew.subst_fvar]

/-- **Single substitution of a ground term depends only on its value.** -/
theorem evR_subst_ground {t : SyntacticTerm LRA} (ht : GroundR t) (φ : Semiproposition LRA 1) :
    evR (φ/[t]) = evR (φ/[num (evTermR t)]) := by
  refine evR_substs_ground (w := ![t]) (w' := ![num (evTermR t)]) (fun i => ?_) (fun i => ?_)
    (fun i => ?_) φ
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi; simpa using ht
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi; simp
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi; simp

/-- **A free-variable assignment by ground terms depends only on their values.** -/
theorem evR_rewrite_ground {n : ℕ} {g g' : ℕ → Semiterm LRA ℕ n}
    (hg : ∀ x, GroundR (g x)) (hg' : ∀ x, GroundR (g' x))
    (hval : ∀ x, evTermR (g x) = evTermR (g' x)) (φ : Semiformula LRA ℕ n) :
    evR (Rew.rewrite g ▹ φ) = evR (Rew.rewrite g' ▹ φ) := by
  refine evR_rew_congr φ n (Rew.rewrite g) (Rew.rewrite g') ⟨fun i => ?_, fun x => ?_⟩
  · rw [Rew.rewrite_bvar, Rew.rewrite_bvar]
  · rw [Rew.rewrite_fvar, Rew.rewrite_fvar, evTR_of_groundR (hg x), evTR_of_groundR (hg' x),
      hval x]

/-! ### The key law -/

/-- **The normalised substitution law.**  For a ground `t` of value `n`,
evaluating `φ/[t]` is evaluating the numeral instance of the *evaluated* `φ`.
This is the equation that turns Foundation's arbitrary-term `exs` into the
ω-calculus's numeral `exs`. -/
theorem evR_subst_key {t : SyntacticTerm LRA} (ht : GroundR t) (φ : Semiproposition LRA 1) :
    evR (φ/[t]) = evR ((evR φ)/[num (evTermR t)]) := by
  rw [evR_subst_ground ht φ]
  exact (evR_rew_evR φ 0 (Rew.subst ![num (evTermR t)])).symm

/-- Substituting a ground term and substituting the numeral of its value give
formulas true together — for *every* `φ`. -/
theorem eval_subst_ground (s₂ : Structure RALang ℕ) (f : ℕ → ℕ) {n : ℕ}
    (φ : Semiformula LRA ℕ 1) (e : Fin n → ℕ) {t : Semiterm LRA ℕ n} (ht : GroundR t) :
    (Semiformula.Eval (s := raStd s₂) e f (φ/[t])
      ↔ Semiformula.Eval (s := raStd s₂) e f (φ/[numAtR (evTermR t)])) := by
  rw [Semiformula.eval_substs, Semiformula.eval_substs]
  refine iff_of_eq
    (congrArg (fun w => Semiformula.Eval (s := raStd s₂) w f φ) (funext fun i => ?_))
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp only [Function.comp_def, Matrix.cons_val_zero]
  rw [val_groundR s₂ (groundR_numAtR _) e f, evTermR_numAtR, val_groundR s₂ ht e f]

/-! ### The atomic axioms are closed under `evR`

The ramified calculus takes the true closed *arithmetic* literals as axioms
(`Ramified/Literals.lean`).  Evaluating one keeps it an axiom: the relation
symbol is untouched (so the `Sum.inl` tag — and with it `MemFree` and
`xfree` — survives), `freeVariables_evTR` keeps the arguments closed, and
truth-preservation keeps it true. -/

/-- `evR` stays inside the closed arithmetic literals.  Built by hand rather than
by `rw`/`simp`: a term containing `Sum.inl r : LRA.Rel k` is not type-correct at
implicit transparency, so the two `rfl`s are supplied as the disjuncts directly. -/
theorem isArithLitR_evR {φ : Proposition LRA} (h : IsArithLitR φ) : IsArithLitR (evR φ) := by
  obtain ⟨k, r, v, (rfl | rfl), hcl⟩ := h
  · exact ⟨k, r, fun i => evTR (v i), Or.inl rfl,
      fun i => by rw [freeVariables_evTR]; exact hcl i⟩
  · exact ⟨k, r, fun i => evTR (v i), Or.inr rfl,
      fun i => by rw [freeVariables_evTR]; exact hcl i⟩

/-- `evR` preserves truth in `ℕ`. -/
theorem trueNR_evR (φ : Proposition LRA) : TrueNR (evR φ) ↔ TrueNR φ := by
  unfold TrueNR
  rw [stdLRA_eq_raStd]
  exact eval_evR_zero raStruc (fun _ => 0) φ

/-- **The axiom set is closed under `evR`.** -/
theorem trueArithLitsR_evR {φ : Proposition LRA} (h : trueArithLitsR.T φ) :
    trueArithLitsR.T (evR φ) := by
  rw [trueArithLitsR_T] at h ⊢
  exact ⟨isArithLitR_evR h.1, (trueNR_evR φ).mpr h.2⟩

/-! ### The evaluating instantiation

`InstantiationR` (`Ramified/Calculus.lean`) asks for three things beyond
Foundation's numerals: the normaliser commutes with negation, it preserves
complexity — and, the ramified addition, it preserves the *rank* and sends
distinct numbers to distinct numerals.  `evR_neg`, `complexity_evR`, `rank_evR`
and `num_injective` are those four laws. -/

/-- **The evaluating instantiation of the ramified calculus**: substitute the
numeral, then evaluate every ground term.  Buchholz's convention that closed
terms are identified with their values. -/
def evInstR : InstantiationR where
  num := num
  nf := evR
  nf_neg := fun φ => evR_neg φ
  complexity_nf := fun φ => complexity_evR φ
  rank_nf := fun φ => rank_evR φ
  num_inj := num_injective

@[simp] theorem evInstR_num : evInstR.num = num := rfl

@[simp] theorem evInstR_nf (φ : Proposition LRA) : evInstR.nf φ = evR φ := rfl

theorem evInstR_inst (φ : Semiproposition LRA 1) (n : ℕ) :
    evInstR.inst φ n = evR (φ/[num n]) := rfl

/-- **The instance of an evaluated body is the evaluated instance**: evaluating
the body first changes nothing, by the congruence law.  This is the equation the
ω-rule case of the replay consumes. -/
theorem evInstR_inst_ev (φ : Semiproposition LRA 1) (n : ℕ) :
    evInstR.inst (evR φ) n = evR (φ/[num n]) := by
  rw [evInstR_inst]
  exact evR_rew_evR φ 0 (Rew.subst ![num n])

/-- The (Pr) premise, in the shape the replay will need it: the instance of an
evaluated body at `n` is the evaluated `n`-th instance. -/
theorem evInstR_inst_body (a n : ℕ) :
    evInstR.inst (evR (body a)) n = evR ((body a)/[num n]) := evInstR_inst_ev (body a) n

/-- The (Pr) atom of `evInstR` is a set atom between numerals, hence `evR`-fixed. -/
@[simp] theorem evR_prAtom (a n : ℕ) :
    evR (OmegaDerivableR.prAtom evInstR a n) = OmegaDerivableR.prAtom evInstR a n :=
  evR_memAt_num (n := 0) (lvl a) n a

end Ramified

end OrdinalAnalysis
