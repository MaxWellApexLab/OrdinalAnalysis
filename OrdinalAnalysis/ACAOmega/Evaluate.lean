/-
  The **deep evaluator on Foundation's monadic second-order syntax**, and the
  evaluating instantiation of `ACA_∞`.

  This is the second-order counterpart of `Gentzen/Evaluate.lean`.  The term
  half is that file's, transposed from `LX` to plain `ℒₒᵣ` — the language of
  `ACA/`, whose only "set" is a genuine second-order variable, so there is no
  fresh predicate symbol and no family `stdLX P` of readings to quantify over:
  the standard structure on `ℕ` is the only one in sight.  The formula half is
  new, and it is where the second-order syntax shows up:

  * `ev₂` evaluates every ground number term inside **every** atom — the
    first-order atoms `rel r v`, `nrel r v` *and* the set atoms `t ∈# X`,
    `t ∉# X`, `t ∈& X`, `t ∉& X` — and recurses through both kinds of
    quantifier.  Set variables are names, and are left exactly where they are.

  * Because `ev₂` only ever rewrites inside an atom, it commutes with every
    **renaming** of set variables (`AtomRew`: a second-order rewriting all of
    whose components are set atoms `#0 ∈# Y` / `#0 ∈& Y`).  That covers
    `Rew.rewrite f`, `Rew.free` and `Rew.shift` in one lemma, which is
    `Instantiation₂.nf_rename` together with the two `(∀₂)`-rule equations.

  * The two congruence laws are the point of the file.

      `ev₂_rew_ev₂  : ev₂ (ω ▹ ev₂ φ) = ev₂ (ω ▹ φ)`    (ω a number rewriting)
      `ev₂_app_ev₂  : ev₂ (Ω.app (ev₂ φ)) = ev₂ (Ω.app φ)`   (Ω second-order)

    The second is the genuinely new one, and it is what the `(∃₂)` rule of the
    calculus needs: the premise of a replayed `exs₂` is `ev₂ ((ev₂ χ)/⟦ψ⟧)`,
    and it has to be `ev₂ (χ/⟦ψ⟧)`.  Its atomic case is the first law: after
    `χ/⟦ψ⟧` an atom `t ∈& X` of `χ` has become `ψ/[t]`, and `ev₂ (ψ/[evT t])`
    is `ev₂ (ψ/[t])` by `evT_idem` and the first-order congruence.  Neither law
    is the false raw law `ev₂ (ω ▹ φ) = ω ▹ ev₂ φ`; see the header of
    `Gentzen/Evaluate.lean` for why no evaluator can satisfy that.

  * Alongside `ev₂_app_ev₂` there is congruence in the *rewriting*:
    `SORewEq Ω Ω'` ("`ev₂` cannot tell the components apart") gives
    `ev₂ (Ω.app φ) = ev₂ (Ω'.app φ)`.  That is what makes the witness of an
    `(∃₂)` replaceable by its own normal form, `ev₂ (χ/⟦ev₂ ψ⟧) = ev₂ (χ/⟦ψ⟧)`,
    which the substitution provider of `EvProvider.lean` consumes.

  Contents.

    `Ground`, `evTerm`, `numAt`, `evT`     the term half, as in `Gentzen/`
    `evT_rew_evT`, `RewEq`, `evT_congr`    term congruence and value dependence
    `ev₂`                                  the formula evaluator
    `rank_ev₂`, `complexity_ev₂`, `arith_ev₂`
    `AtomRew`, `ev₂_app_atom`              renamings commute
    `ev₂_rename`, `ev₂_free₁`, `ev₂_shift₁`
    `ev₂_rew_ev₂`, `ev₂_rew_congr`         first-order congruence
    `ev₂_subst_ground`, `ev₂_subst_key`    value dependence
    `ev₂_app_ev₂`, `SORewEq`, `ev₂_app_congr`   second-order congruence
    `ev₂_subst₂_ev₂`                       the law the `(∃₂)` replay needs
    `eval_ev₂`                             truth is preserved
    `trueArithLits₂`, `trueArithLits₂_ev₂` the atomic axioms
    `evInst₂`                              the evaluating instantiation
-/
import OrdinalAnalysis.ACAOmega.Calculus

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA

/-! ### Ground terms

A term is ground when it is built from function symbols alone.  Both halves are
needed: `freeVariables = ∅` alone is the right notion only at level `0`, and the
evaluator has to act underneath quantifiers. -/

/-- `t` contains neither a bound nor a free number variable. -/
def Ground {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : Prop :=
  t.bv = ∅ ∧ t.freeVariables = ∅

instance instDecidableGround {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : Decidable (Ground t) := by
  unfold Ground
  infer_instance

theorem not_ground_bvar {n : ℕ} (x : Fin n) :
    ¬Ground (#x : FirstOrder.Semiterm ℒₒᵣ ℕ n) := by
  rintro ⟨hb, -⟩
  rw [FirstOrder.Semiterm.bv_bvar] at hb
  exact absurd hb (Finset.singleton_ne_empty x)

theorem not_ground_fvar {n : ℕ} (x : ℕ) :
    ¬Ground (&x : FirstOrder.Semiterm ℒₒᵣ ℕ n) := by
  rintro ⟨-, hf⟩
  rw [FirstOrder.Semiterm.freeVariables_fvar] at hf
  exact absurd hf (Finset.singleton_ne_empty x)

/-- Groundness is componentwise. -/
theorem ground_func_iff {n k : ℕ} (fn : (ℒₒᵣ : FirstOrder.Language).Func k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    Ground (FirstOrder.Semiterm.func fn v) ↔ ∀ i, Ground (v i) := by
  simp only [Ground, FirstOrder.Semiterm.bv_func, FirstOrder.Semiterm.freeVariables_func,
    Finset.eq_empty_iff_forall_notMem, Finset.mem_biUnion, Finset.mem_univ, true_and,
    not_exists]
  constructor
  · rintro ⟨hb, hf⟩ i
    exact ⟨fun x => hb x i, fun x => hf x i⟩
  · intro h
    exact ⟨fun x i => (h i).1 x, fun x i => (h i).2 x⟩

/-- **At level `0`, closed and ground agree.** -/
theorem ground_of_closed {t : FirstOrder.SyntacticTerm ℒₒᵣ} (h : t.freeVariables = ∅) :
    Ground t :=
  ⟨Finset.eq_empty_iff_forall_notMem.mpr fun x => x.elim0, h⟩

theorem freeVariables_of_ground {n : ℕ} {t : FirstOrder.Semiterm ℒₒᵣ ℕ n} (h : Ground t) :
    t.freeVariables = ∅ := h.2

/-! ### The value of a ground term -/

/-- **The value of a term in the standard model.**  The assignments are fixed to
the constant zero; for the ground terms this file evaluates neither is visible
(`val_ground`). -/
def evTerm {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : ℕ :=
  FirstOrder.Semiterm.val (M := ℕ) (fun _ => 0) (fun _ => 0) t

/-- A ground term has the same value under every pair of environments. -/
theorem val_ground_congr {n : ℕ} (e e' : Fin n → ℕ) (f f' : ℕ → ℕ) :
    ∀ {t : FirstOrder.Semiterm ℒₒᵣ ℕ n}, Ground t →
      FirstOrder.Semiterm.val (M := ℕ) e f t = FirstOrder.Semiterm.val (M := ℕ) e' f' t := by
  intro t
  induction t with
  | bvar x => exact fun h => absurd h (not_ground_bvar x)
  | fvar x => exact fun h => absurd h (not_ground_fvar x)
  | func fn v ih =>
      intro h
      have hv := (ground_func_iff fn v).mp h
      simp only [FirstOrder.Semiterm.val_func, Function.comp_def]
      exact congrArg (FirstOrder.Structure.func (M := ℕ) fn) (funext fun i => ih i (hv i))

/-- The value of a ground term *is* `evTerm`. -/
theorem val_ground {n : ℕ} {t : FirstOrder.Semiterm ℒₒᵣ ℕ n} (h : Ground t)
    (e : Fin n → ℕ) (f : ℕ → ℕ) :
    FirstOrder.Semiterm.val (M := ℕ) e f t = evTerm t :=
  val_ground_congr e (fun _ => 0) f (fun _ => 0) h

/-- Groundness survives every rewriting. -/
theorem ground_rew {n₁ n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂) :
    ∀ {t : FirstOrder.Semiterm ℒₒᵣ ℕ n₁}, Ground t → Ground (ω t) := by
  intro t
  induction t with
  | bvar x => exact fun h => absurd h (not_ground_bvar x)
  | fvar x => exact fun h => absurd h (not_ground_fvar x)
  | func fn v ih =>
      intro h
      have hv := (ground_func_iff fn v).mp h
      rw [ω.func' fn v]
      exact (ground_func_iff fn _).mpr fun i => ih i (hv i)

/-- **A rewriting fixes a ground term.** -/
theorem rew_of_ground {n : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) :
    ∀ {t : FirstOrder.Semiterm ℒₒᵣ ℕ n}, Ground t → ω t = t := by
  intro t
  induction t with
  | bvar x => exact fun h => absurd h (not_ground_bvar x)
  | fvar x => exact fun h => absurd h (not_ground_fvar x)
  | func fn v ih =>
      intro h
      have hv := (ground_func_iff fn v).mp h
      rw [ω.func' fn v]
      exact congrArg (FirstOrder.Semiterm.func fn) (funext fun i => ih i (hv i))

/-- …and so does its value. -/
theorem evTerm_rew {n₁ n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    {t : FirstOrder.Semiterm ℒₒᵣ ℕ n₁} (h : Ground t) : evTerm (ω t) = evTerm t := by
  unfold evTerm
  rw [FirstOrder.Semiterm.val_rew]
  exact val_ground_congr _ _ _ _ h

/-! ### Numerals at every level -/

/-- The numeral `m̄`, as an `ℒₒᵣ`-term with `n` bound variables. -/
def numAt {n : ℕ} (m : ℕ) : FirstOrder.Semiterm ℒₒᵣ ℕ n := FirstOrder.Semiterm.numeral m

/-- A numeral is a constant, so no rewriting moves it. -/
@[simp] theorem rew_numAt {n₁ n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂) (m : ℕ) :
    ω (numAt m : FirstOrder.Semiterm ℒₒᵣ ℕ n₁) = numAt m := by
  simp [numAt]

/-- A term that comes from a *sentence* term by embedding and substituting the
empty vector is ground. -/
theorem ground_subst_emb {n : ℕ} :
    ∀ t : FirstOrder.Semiterm ℒₒᵣ Empty 0,
      Ground ((FirstOrder.Rew.subst (![] : Fin 0 → FirstOrder.Semiterm ℒₒᵣ ℕ n))
        (FirstOrder.Rew.emb t : FirstOrder.Semiterm ℒₒᵣ ℕ 0)) := by
  intro t
  induction t with
  | bvar x => exact x.elim0
  | fvar x => exact x.elim
  | func fn v ih =>
      have h1 : (FirstOrder.Rew.emb (FirstOrder.Semiterm.func fn v) :
            FirstOrder.Semiterm ℒₒᵣ ℕ 0)
          = FirstOrder.Semiterm.func fn fun i =>
              (FirstOrder.Rew.emb (v i) : FirstOrder.Semiterm ℒₒᵣ ℕ 0) :=
        FirstOrder.Rew.func' _ fn v
      have h2 : (FirstOrder.Rew.subst (![] : Fin 0 → FirstOrder.Semiterm ℒₒᵣ ℕ n))
            (FirstOrder.Semiterm.func fn fun i =>
              (FirstOrder.Rew.emb (v i) : FirstOrder.Semiterm ℒₒᵣ ℕ 0))
          = FirstOrder.Semiterm.func fn fun i =>
              (FirstOrder.Rew.subst (![] : Fin 0 → FirstOrder.Semiterm ℒₒᵣ ℕ n))
                (FirstOrder.Rew.emb (v i)) :=
        FirstOrder.Rew.func' _ fn _
      rw [h1, h2]
      exact (ground_func_iff fn _).mpr ih

@[simp] theorem ground_numAt {n : ℕ} (m : ℕ) :
    Ground (numAt m : FirstOrder.Semiterm ℒₒᵣ ℕ n) :=
  ground_subst_emb (FirstOrder.Semiterm.Operator.numeral ℒₒᵣ m).term

/-- **`m̄` denotes `m`**, at every level. -/
@[simp] theorem evTerm_numAt {n : ℕ} (m : ℕ) :
    evTerm (numAt m : FirstOrder.Semiterm ℒₒᵣ ℕ n) = m := by
  unfold evTerm numAt
  simp

/-- The value of a compound term, componentwise. -/
theorem evTerm_func {n k : ℕ} (f : (ℒₒᵣ : FirstOrder.Language).Func k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    evTerm (FirstOrder.Semiterm.func f v)
      = FirstOrder.Structure.func (M := ℕ) f fun i => evTerm (v i) := rfl

/-! ### The term evaluator -/

/-- **The term evaluator**: ground ↦ the numeral of its value, and otherwise
evaluate the arguments and rebuild. -/
def evT {n : ℕ} : FirstOrder.Semiterm ℒₒᵣ ℕ n → FirstOrder.Semiterm ℒₒᵣ ℕ n
  | #x => #x
  | &x => &x
  | FirstOrder.Semiterm.func f v =>
      if Ground (FirstOrder.Semiterm.func f v)
        then numAt (evTerm (FirstOrder.Semiterm.func f v))
        else FirstOrder.Semiterm.func f fun i => evT (v i)

@[simp] theorem evT_bvar {n : ℕ} (x : Fin n) :
    evT (#x : FirstOrder.Semiterm ℒₒᵣ ℕ n) = #x := rfl

@[simp] theorem evT_fvar {n : ℕ} (x : ℕ) :
    evT (&x : FirstOrder.Semiterm ℒₒᵣ ℕ n) = &x := rfl

theorem evT_func {n k : ℕ} (f : (ℒₒᵣ : FirstOrder.Language).Func k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    evT (FirstOrder.Semiterm.func f v)
      = if Ground (FirstOrder.Semiterm.func f v)
          then numAt (evTerm (FirstOrder.Semiterm.func f v))
          else FirstOrder.Semiterm.func f fun i => evT (v i) := rfl

/-- The defining clause on a ground term. -/
theorem evT_of_ground {n : ℕ} {t : FirstOrder.Semiterm ℒₒᵣ ℕ n} (h : Ground t) :
    evT t = numAt (evTerm t) := by
  cases t with
  | bvar x => exact absurd h (not_ground_bvar x)
  | fvar x => exact absurd h (not_ground_fvar x)
  | func f v => rw [evT_func]; exact if_pos h

/-- The defining clause on a non-ground compound term. -/
theorem evT_func_of_not_ground {n k : ℕ} (f : (ℒₒᵣ : FirstOrder.Language).Func k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) (h : ¬Ground (FirstOrder.Semiterm.func f v)) :
    evT (FirstOrder.Semiterm.func f v) = FirstOrder.Semiterm.func f fun i => evT (v i) := by
  rw [evT_func]; exact if_neg h

@[simp] theorem evT_numAt {n : ℕ} (m : ℕ) :
    evT (numAt m : FirstOrder.Semiterm ℒₒᵣ ℕ n) = numAt m := by
  rw [evT_of_ground (ground_numAt m), evTerm_numAt]

/-- **`evT` neither creates nor destroys groundness.** -/
@[simp] theorem ground_evT_iff {n : ℕ} {t : FirstOrder.Semiterm ℒₒᵣ ℕ n} :
    Ground (evT t) ↔ Ground t := by
  induction t with
  | bvar x => rw [evT_bvar]
  | fvar x => rw [evT_fvar]
  | func f v ih =>
      by_cases h : Ground (FirstOrder.Semiterm.func f v)
      · exact iff_of_true (by rw [evT_of_ground h]; exact ground_numAt _) h
      · rw [evT_func_of_not_ground f v h, ground_func_iff, ground_func_iff]
        exact forall_congr' fun i => ih i

theorem ground_evT {n : ℕ} {t : FirstOrder.Semiterm ℒₒᵣ ℕ n} (h : Ground t) : Ground (evT t) :=
  ground_evT_iff.mpr h

@[simp] theorem evT_idem {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : evT (evT t) = evT t := by
  induction t with
  | bvar x => rw [evT_bvar, evT_bvar]
  | fvar x => rw [evT_fvar, evT_fvar]
  | func f v ih =>
      by_cases h : Ground (FirstOrder.Semiterm.func f v)
      · rw [evT_of_ground h, evT_numAt]
      · have hn : ¬Ground (FirstOrder.Semiterm.func f fun i => evT (v i)) := by
          rw [ground_func_iff]
          intro hc
          exact h ((ground_func_iff f v).mpr fun i => ground_evT_iff.mp (hc i))
        rw [evT_func_of_not_ground f v h, evT_func_of_not_ground f _ hn]
        exact congrArg (FirstOrder.Semiterm.func f) (funext fun i => ih i)

/-- **`evT` does not change what a term denotes.** -/
theorem val_evT {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) (e : Fin n → ℕ) (f : ℕ → ℕ) :
    FirstOrder.Semiterm.val (M := ℕ) e f (evT t)
      = FirstOrder.Semiterm.val (M := ℕ) e f t := by
  induction t with
  | bvar x => rw [evT_bvar]
  | fvar x => rw [evT_fvar]
  | func fn v ih =>
      by_cases h : Ground (FirstOrder.Semiterm.func fn v)
      · rw [evT_of_ground h, val_ground (ground_numAt _) e f, evTerm_numAt, val_ground h e f]
      · rw [evT_func_of_not_ground fn v h]
        simp only [FirstOrder.Semiterm.val_func, Function.comp_def]
        exact congrArg (FirstOrder.Structure.func (M := ℕ) fn) (funext fun i => ih i)

theorem evTerm_evT {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : evTerm (evT t) = evTerm t :=
  val_evT t _ _

/-- **`evT` does not move the free variables.** -/
@[simp] theorem freeVariables_evT {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    (evT t).freeVariables = t.freeVariables := by
  induction t with
  | bvar x => rw [evT_bvar]
  | fvar x => rw [evT_fvar]
  | func fn v ih =>
      by_cases h : Ground (FirstOrder.Semiterm.func fn v)
      · rw [evT_of_ground h, (ground_numAt (n := n) (evTerm (FirstOrder.Semiterm.func fn v))).2,
          h.2]
      · rw [evT_func_of_not_ground fn v h, FirstOrder.Semiterm.freeVariables_func,
          FirstOrder.Semiterm.freeVariables_func]
        exact congrArg (Finset.biUnion Finset.univ) (funext fun i => ih i)

/-! ### Term congruence -/

theorem val_rew_evT {n₁ n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n₁) (e : Fin n₂ → ℕ) (f : ℕ → ℕ) :
    FirstOrder.Semiterm.val (M := ℕ) e f (ω (evT t))
      = FirstOrder.Semiterm.val (M := ℕ) e f (ω t) := by
  rw [FirstOrder.Semiterm.val_rew, FirstOrder.Semiterm.val_rew]
  exact val_evT t _ _

theorem evTerm_rew_evT {n₁ n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n₁) : evTerm (ω (evT t)) = evTerm (ω t) := by
  unfold evTerm
  exact val_rew_evT ω t _ _

theorem ground_rew_evT_iff {n₁ n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n₁) : Ground (ω (evT t)) ↔ Ground (ω t) := by
  induction t with
  | bvar x => rw [evT_bvar]
  | fvar x => rw [evT_fvar]
  | func f v ih =>
      by_cases h : Ground (FirstOrder.Semiterm.func f v)
      · exact iff_of_true (by rw [evT_of_ground h, rew_numAt]; exact ground_numAt _)
          (ground_rew ω h)
      · rw [evT_func_of_not_ground f v h, ω.func' f fun i => evT (v i), ω.func' f v,
          ground_func_iff, ground_func_iff]
        exact forall_congr' fun i => ih i

/-- **The term-level congruence.** -/
theorem evT_rew_evT {n₁ n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n₁) : evT (ω (evT t)) = evT (ω t) := by
  induction t with
  | bvar x => rw [evT_bvar]
  | fvar x => rw [evT_fvar]
  | func f v ih =>
      by_cases h : Ground (FirstOrder.Semiterm.func f v)
      · rw [evT_of_ground h, rew_numAt, evT_numAt, evT_of_ground (ground_rew ω h),
          evTerm_rew ω h]
      · have hiff : Ground (FirstOrder.Semiterm.func f fun i => ω (evT (v i)))
            ↔ Ground (FirstOrder.Semiterm.func f fun i => ω (v i)) := by
          rw [ground_func_iff, ground_func_iff]
          exact forall_congr' fun i => ground_rew_evT_iff ω (v i)
        rw [evT_func_of_not_ground f v h, ω.func' f fun i => evT (v i), ω.func' f v]
        by_cases hg : Ground (FirstOrder.Semiterm.func f fun i => ω (v i))
        · have hval : evTerm (FirstOrder.Semiterm.func f fun i => ω (evT (v i)))
              = evTerm (FirstOrder.Semiterm.func f fun i => ω (v i)) := by
            have hx := evTerm_rew_evT ω (FirstOrder.Semiterm.func f v)
            rwa [evT_func_of_not_ground f v h, ω.func' f fun i => evT (v i),
              ω.func' f v] at hx
          rw [evT_of_ground (hiff.mpr hg), evT_of_ground hg, hval]
        · rw [evT_func_of_not_ground f _ fun hc => hg (hiff.mp hc),
            evT_func_of_not_ground f _ hg]
          exact congrArg (FirstOrder.Semiterm.func f) (funext fun i => ih i)

theorem val_congr_of_evT {n : ℕ} {t u : FirstOrder.Semiterm ℒₒᵣ ℕ n} (h : evT t = evT u)
    (e : Fin n → ℕ) (f : ℕ → ℕ) :
    FirstOrder.Semiterm.val (M := ℕ) e f t = FirstOrder.Semiterm.val (M := ℕ) e f u := by
  rw [← val_evT t e f, ← val_evT u e f, h]

theorem evTerm_congr_of_evT {n : ℕ} {t u : FirstOrder.Semiterm ℒₒᵣ ℕ n} (h : evT t = evT u) :
    evTerm t = evTerm u := val_congr_of_evT h _ _

theorem evT_rew_congr {n₁ n₂ : ℕ} (ρ : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    {t u : FirstOrder.Semiterm ℒₒᵣ ℕ n₁} (h : evT t = evT u) : evT (ρ t) = evT (ρ u) := by
  rw [← evT_rew_evT ρ t, ← evT_rew_evT ρ u, h]

/-- **Two number rewritings the evaluator cannot tell apart.** -/
def RewEq {n₁ n₂ : ℕ} (ω ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂) : Prop :=
  (∀ i : Fin n₁, evT (ω #i) = evT (ω' #i)) ∧ ∀ x : ℕ, evT (ω &x) = evT (ω' &x)

theorem RewEq.q {n₁ n₂ : ℕ} {ω ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂} (h : RewEq ω ω') :
    RewEq ω.q ω'.q := by
  constructor
  · intro i
    induction i using Fin.cases with
    | zero => rw [FirstOrder.Rew.q_bvar_zero, FirstOrder.Rew.q_bvar_zero]
    | succ j =>
        rw [FirstOrder.Rew.q_bvar_succ, FirstOrder.Rew.q_bvar_succ]
        exact evT_rew_congr FirstOrder.Rew.bShift (h.1 j)
  · intro x
    rw [FirstOrder.Rew.q_fvar, FirstOrder.Rew.q_fvar]
    exact evT_rew_congr FirstOrder.Rew.bShift (h.2 x)

/-- **The term-level value dependence.** -/
theorem evT_congr {n₁ n₂ : ℕ} {ω ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂} (h : RewEq ω ω')
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n₁) : evT (ω t) = evT (ω' t) := by
  induction t with
  | bvar x => exact h.1 x
  | fvar x => exact h.2 x
  | func f v ih =>
      have hgi : ∀ i, (Ground (ω (v i)) ↔ Ground (ω' (v i))) := fun i => by
        have e1 : Ground (evT (ω (v i))) ↔ Ground (ω (v i)) := ground_evT_iff
        have e2 : Ground (evT (ω' (v i))) ↔ Ground (ω' (v i)) := ground_evT_iff
        rw [← e1, ← e2, ih i]
      rw [ω.func' f v, ω'.func' f v]
      by_cases hg : Ground (FirstOrder.Semiterm.func f fun i => ω (v i))
      · have hg' : Ground (FirstOrder.Semiterm.func f fun i => ω' (v i)) :=
          (ground_func_iff f _).mpr fun i => (hgi i).mp ((ground_func_iff f _).mp hg i)
        rw [evT_of_ground hg, evT_of_ground hg', evTerm_func, evTerm_func]
        exact congrArg (fun m => (numAt m : FirstOrder.Semiterm ℒₒᵣ ℕ n₂))
          (congrArg (FirstOrder.Structure.func (M := ℕ) f)
            (funext fun i => evTerm_congr_of_evT (ih i)))
      · have hg' : ¬Ground (FirstOrder.Semiterm.func f fun i => ω' (v i)) := fun hc =>
          hg ((ground_func_iff f _).mpr fun i => (hgi i).mpr ((ground_func_iff f _).mp hc i))
        rw [evT_func_of_not_ground f _ hg, evT_func_of_not_ground f _ hg']
        exact congrArg (FirstOrder.Semiterm.func f) (funext fun i => ih i)

/-! ### The formula evaluator

`ev₂` evaluates every argument of every atom — the first-order atoms and the
four set atoms alike — and recurses through the connectives and **both** kinds
of quantifier.  Set variables are names; nothing touches them. -/

/-- **The formula evaluator** on the monadic second-order syntax. -/
def ev₂ {N n : ℕ} : Semiformula ℒₒᵣ ℕ ℕ N n → Semiformula ℒₒᵣ ℕ ℕ N n
  |  .rel r v => .rel r fun i => evT (v i)
  | .nrel r v => .nrel r fun i => evT (v i)
  |    t ∈# X => (evT t) ∈# X
  |    t ∉# X => (evT t) ∉# X
  |    t ∈& X => (evT t) ∈& X
  |    t ∉& X => (evT t) ∉& X
  |         ⊤ => ⊤
  |         ⊥ => ⊥
  |     φ ⋏ ψ => ev₂ φ ⋏ ev₂ ψ
  |     φ ⋎ ψ => ev₂ φ ⋎ ev₂ ψ
  |      ∀¹ φ => ∀¹ (ev₂ φ)
  |      ∃¹ φ => ∃¹ (ev₂ φ)
  |      ∀² φ => ∀² (ev₂ φ)
  |      ∃² φ => ∃² (ev₂ φ)

section EvSimp

variable {N n : ℕ}

@[simp] theorem ev₂_rel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ev₂ (.rel r v : Semiformula ℒₒᵣ ℕ ℕ N n) = .rel r fun i => evT (v i) := rfl

@[simp] theorem ev₂_nrel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ev₂ (.nrel r v : Semiformula ℒₒᵣ ℕ ℕ N n) = .nrel r fun i => evT (v i) := rfl

@[simp] theorem ev₂_bvar (X : Fin N) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ev₂ (t ∈# X : Semiformula ℒₒᵣ ℕ ℕ N n) = (evT t) ∈# X := rfl

@[simp] theorem ev₂_nbvar (X : Fin N) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ev₂ (t ∉# X : Semiformula ℒₒᵣ ℕ ℕ N n) = (evT t) ∉# X := rfl

@[simp] theorem ev₂_fvar (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ev₂ (t ∈& X : Semiformula ℒₒᵣ ℕ ℕ N n) = (evT t) ∈& X := rfl

@[simp] theorem ev₂_nfvar (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ev₂ (t ∉& X : Semiformula ℒₒᵣ ℕ ℕ N n) = (evT t) ∉& X := rfl

@[simp] theorem ev₂_verum : ev₂ (⊤ : Semiformula ℒₒᵣ ℕ ℕ N n) = ⊤ := rfl

@[simp] theorem ev₂_falsum : ev₂ (⊥ : Semiformula ℒₒᵣ ℕ ℕ N n) = ⊥ := rfl

@[simp] theorem ev₂_and (φ ψ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    ev₂ (φ ⋏ ψ) = ev₂ φ ⋏ ev₂ ψ := rfl

@[simp] theorem ev₂_or (φ ψ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    ev₂ (φ ⋎ ψ) = ev₂ φ ⋎ ev₂ ψ := rfl

@[simp] theorem ev₂_all₁ (φ : Semiformula ℒₒᵣ ℕ ℕ N (n + 1)) :
    ev₂ (∀¹ φ) = ∀¹ (ev₂ φ) := rfl

@[simp] theorem ev₂_exs₁ (φ : Semiformula ℒₒᵣ ℕ ℕ N (n + 1)) :
    ev₂ (∃¹ φ) = ∃¹ (ev₂ φ) := rfl

@[simp] theorem ev₂_all₂ (φ : Semiformula ℒₒᵣ ℕ ℕ (N + 1) n) :
    ev₂ (∀² φ) = ∀² (ev₂ φ) := rfl

@[simp] theorem ev₂_exs₂ (φ : Semiformula ℒₒᵣ ℕ ℕ (N + 1) n) :
    ev₂ (∃² φ) = ∃² (ev₂ φ) := rfl

end EvSimp

/-- **`ev₂` commutes with negation.** -/
@[simp] theorem ev₂_neg {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n) : ev₂ (∼φ) = ∼(ev₂ φ) := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **`ev₂` is idempotent.** -/
@[simp] theorem ev₂_idem {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n) : ev₂ (ev₂ φ) = ev₂ φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **`ev₂` does not change the cut rank** — it rewrites inside atoms only. -/
@[simp] theorem rank_ev₂ {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n) : rank (ev₂ φ) = rank φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **`ev₂` does not change the complexity.** -/
@[simp] theorem complexity_ev₂ {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    (ev₂ φ).complexity = φ.complexity := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **`ev₂` preserves and reflects arithmeticity.** -/
@[simp] theorem arith_ev₂ {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    Arith (ev₂ φ) ↔ Arith φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **`ev₂` commutes with renaming the bound set variables.** -/
@[simp] theorem ev₂_bmap {N M n : ℕ} (f : Fin N → Fin M) (φ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    ev₂ (φ.bmap f) = (ev₂ φ).bmap f := by
  induction φ using Semiformula.rec' generalizing M <;> simp [*]

/-! ### Renamings of set variables commute with `ev₂`

A second-order rewriting whose components are all *set atoms* creates no number
term, so `ev₂` passes straight through it.  That single lemma is
`Instantiation₂.nf_rename` and the two `(∀₂)`-rule equations at once. -/

/-- A second-order rewriting all of whose components are set atoms `#0 ∈# Y` or
`#0 ∈& Y` — a renaming of set variables, possibly turning a bound one into a
free one, as `Rew.free` does. -/
def AtomRew {N₁ N₂ : ℕ} (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ) : Prop :=
  (∀ X : Fin N₁, (∃ Y : Fin N₂, Ω.bv X = ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# Y)) ∨
      (∃ Y : ℕ, Ω.bv X = ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& Y))) ∧
  (∀ X : ℕ, (∃ Y : Fin N₂, Ω.fv X = ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# Y)) ∨
      (∃ Y : ℕ, Ω.fv X = ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& Y)))

theorem AtomRew.q {N₁ N₂ : ℕ} {Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ} (h : AtomRew Ω) :
    AtomRew Ω.q := by
  constructor
  · intro X
    induction X using Fin.cases with
    | zero => exact Or.inl ⟨0, rfl⟩
    | succ X =>
        rcases h.1 X with ⟨Y, hY⟩ | ⟨Y, hY⟩
        · refine Or.inl ⟨Y.succ, ?_⟩
          rw [SecondOrder.Rew.q_bv_succ, hY]
          rfl
        · refine Or.inr ⟨Y, ?_⟩
          rw [SecondOrder.Rew.q_bv_succ, hY]
          rfl
  · intro X
    rcases h.2 X with ⟨Y, hY⟩ | ⟨Y, hY⟩
    · refine Or.inl ⟨Y.succ, ?_⟩
      rw [SecondOrder.Rew.q_fv, hY]
      rfl
    · refine Or.inr ⟨Y, ?_⟩
      rw [SecondOrder.Rew.q_fv, hY]
      rfl

/-- **A set-variable renaming commutes with `ev₂`.** -/
theorem ev₂_app_atom : ∀ {N₁ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) (N₂ : ℕ)
    (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ), AtomRew Ω → ev₂ (Ω.app φ) = Ω.app (ev₂ φ) := by
  intro N₁ n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₂ Ω _; simp
  | hNrel r v => intro N₂ Ω _; simp
  | hBvar X t =>
      intro N₂ Ω hΩ
      rcases hΩ.1 X with ⟨Y, hY⟩ | ⟨Y, hY⟩ <;> simp [hY]
  | hNbvar X t =>
      intro N₂ Ω hΩ
      rcases hΩ.1 X with ⟨Y, hY⟩ | ⟨Y, hY⟩ <;> simp [hY]
  | hFvar X t =>
      intro N₂ Ω hΩ
      rcases hΩ.2 X with ⟨Y, hY⟩ | ⟨Y, hY⟩ <;> simp [hY]
  | hNfvar X t =>
      intro N₂ Ω hΩ
      rcases hΩ.2 X with ⟨Y, hY⟩ | ⟨Y, hY⟩ <;> simp [hY]
  | hVerum => intro N₂ Ω _; simp
  | hFalsum => intro N₂ Ω _; simp
  | hAnd φ ψ ihφ ihψ => intro N₂ Ω hΩ; simp [ihφ N₂ Ω hΩ, ihψ N₂ Ω hΩ]
  | hOr φ ψ ihφ ihψ => intro N₂ Ω hΩ; simp [ihφ N₂ Ω hΩ, ihψ N₂ Ω hΩ]
  | hAll₁ φ ih => intro N₂ Ω hΩ; simp [ih N₂ Ω hΩ]
  | hExs₁ φ ih => intro N₂ Ω hΩ; simp [ih N₂ Ω hΩ]
  | hAll₂ φ ih => intro N₂ Ω hΩ; simp [ih (N₂ + 1) Ω.q hΩ.q]
  | hExs₂ φ ih => intro N₂ Ω hΩ; simp [ih (N₂ + 1) Ω.q hΩ.q]

theorem atomRew_rewrite {N : ℕ} (f : ℕ → ℕ) :
    AtomRew (SecondOrder.Rew.rewrite (L := ℒₒᵣ) (ξ := ℕ) (N := N) f) :=
  ⟨fun X => Or.inl ⟨X, rfl⟩, fun X => Or.inr ⟨f X, rfl⟩⟩

theorem atomRew_shift {N : ℕ} :
    AtomRew (SecondOrder.Rew.shift (L := ℒₒᵣ) (ξ := ℕ) (N := N)) :=
  ⟨fun X => Or.inl ⟨X, rfl⟩, fun X => Or.inr ⟨X + 1, rfl⟩⟩

theorem atomRew_free {N : ℕ} :
    AtomRew (SecondOrder.Rew.free (L := ℒₒᵣ) (ξ := ℕ) (N := N)) := by
  refine ⟨fun X => ?_, fun X => Or.inr ⟨X + 1, rfl⟩⟩
  refine Fin.lastCases ?_ ?_ X
  · exact Or.inr ⟨0, SecondOrder.Rew.free_bvar_last N⟩
  · intro Y
    exact Or.inl ⟨Y, SecondOrder.Rew.free_bvar_castSucc_eq Y⟩

/-- **`ev₂` commutes with renaming the free set variables** — the law
`Instantiation₂.nf_rename`. -/
theorem ev₂_rename {N n : ℕ} (f : ℕ → ℕ) (φ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    ev₂ ((SecondOrder.Rew.rewrite f).app φ) = (SecondOrder.Rew.rewrite f).app (ev₂ φ) :=
  ev₂_app_atom φ N (SecondOrder.Rew.rewrite f) (atomRew_rewrite f)

/-- **`ev₂` commutes with `free₁`** — the eigenvariable half of the `(∀₂)` rule. -/
theorem ev₂_free₁ {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ (N + 1) n) :
    ev₂ (SecondOrder.Rew.free.app φ) = SecondOrder.Rew.free.app (ev₂ φ) :=
  ev₂_app_atom φ N SecondOrder.Rew.free atomRew_free

/-- **`ev₂` commutes with `shift₁`** — the context half of the `(∀₂)` rule. -/
theorem ev₂_shift₁ {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    ev₂ (SecondOrder.Rew.shift.app φ) = SecondOrder.Rew.shift.app (ev₂ φ) :=
  ev₂_app_atom φ N SecondOrder.Rew.shift atomRew_shift

theorem ev₂_free₁' (φ : Semiproposition ℒₒᵣ 1 0) :
    ev₂ (Semiproposition.free₁ φ) = Semiproposition.free₁ (ev₂ φ) := ev₂_free₁ φ

theorem ev₂_shift₁' (γ : Proposition ℒₒᵣ) :
    ev₂ (Semiproposition.shift₁ γ) = Semiproposition.shift₁ (ev₂ γ) := ev₂_shift₁ γ

/-! ### First-order congruence and value dependence -/

/-- **The first-order congruence.**  Normalising a formula before a *number*
rewriting does not change the normal form of the result. -/
theorem ev₂_rew_ev₂ : ∀ {N n₁ : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n₁) (n₂ : ℕ)
    (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂), ev₂ (ω ▹ ev₂ φ) = ev₂ (ω ▹ φ) := by
  intro N n₁ φ
  induction φ using Semiformula.rec' with
  | hRel r v =>
      intro n₂ ω
      simp only [ev₂_rel, Semiformula.rew_rel]
      exact congrArg (Semiformula.rel r) (funext fun i => evT_rew_evT ω (v i))
  | hNrel r v =>
      intro n₂ ω
      simp only [ev₂_nrel, Semiformula.rew_nrel]
      exact congrArg (Semiformula.nrel r) (funext fun i => evT_rew_evT ω (v i))
  | hBvar X t => intro n₂ ω; simp [evT_rew_evT ω t]
  | hNbvar X t => intro n₂ ω; simp [evT_rew_evT ω t]
  | hFvar X t => intro n₂ ω; simp [evT_rew_evT ω t]
  | hNfvar X t => intro n₂ ω; simp [evT_rew_evT ω t]
  | hVerum => intro n₂ ω; simp
  | hFalsum => intro n₂ ω; simp
  | hAnd φ ψ ihφ ihψ => intro n₂ ω; simp [ihφ n₂ ω, ihψ n₂ ω]
  | hOr φ ψ ihφ ihψ => intro n₂ ω; simp [ihφ n₂ ω, ihψ n₂ ω]
  | hAll₁ φ ih => intro n₂ ω; simp [ih (n₂ + 1) ω.q]
  | hExs₁ φ ih => intro n₂ ω; simp [ih (n₂ + 1) ω.q]
  | hAll₂ φ ih => intro n₂ ω; simp [ih n₂ ω]
  | hExs₂ φ ih => intro n₂ ω; simp [ih n₂ ω]

/-- **Value dependence for number rewritings.**  `ev₂` cannot tell apart two
rewritings that send each variable to terms with the same normal form. -/
theorem ev₂_rew_congr : ∀ {N n₁ : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n₁) (n₂ : ℕ)
    (ω ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂), RewEq ω ω' → ev₂ (ω ▹ φ) = ev₂ (ω' ▹ φ) := by
  intro N n₁ φ
  induction φ using Semiformula.rec' with
  | hRel r v =>
      intro n₂ ω ω' h
      simp only [Semiformula.rew_rel, ev₂_rel]
      exact congrArg (Semiformula.rel r) (funext fun i => evT_congr h (v i))
  | hNrel r v =>
      intro n₂ ω ω' h
      simp only [Semiformula.rew_nrel, ev₂_nrel]
      exact congrArg (Semiformula.nrel r) (funext fun i => evT_congr h (v i))
  | hBvar X t => intro n₂ ω ω' h; simp [evT_congr h t]
  | hNbvar X t => intro n₂ ω ω' h; simp [evT_congr h t]
  | hFvar X t => intro n₂ ω ω' h; simp [evT_congr h t]
  | hNfvar X t => intro n₂ ω ω' h; simp [evT_congr h t]
  | hVerum => intro n₂ ω ω' _; simp
  | hFalsum => intro n₂ ω ω' _; simp
  | hAnd φ ψ ihφ ihψ => intro n₂ ω ω' h; simp [ihφ n₂ ω ω' h, ihψ n₂ ω ω' h]
  | hOr φ ψ ihφ ihψ => intro n₂ ω ω' h; simp [ihφ n₂ ω ω' h, ihψ n₂ ω ω' h]
  | hAll₁ φ ih => intro n₂ ω ω' h; simp [ih (n₂ + 1) ω.q ω'.q h.q]
  | hExs₁ φ ih => intro n₂ ω ω' h; simp [ih (n₂ + 1) ω.q ω'.q h.q]
  | hAll₂ φ ih => intro n₂ ω ω' h; simp [ih n₂ ω ω' h]
  | hExs₂ φ ih => intro n₂ ω ω' h; simp [ih n₂ ω ω' h]

/-- **A substituted ground term is seen only through its value.** -/
theorem ev₂_subst_ground {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    {t : FirstOrder.Semiterm ℒₒᵣ ℕ n} (ht : Ground t) :
    ev₂ (φ/[t]) = ev₂ (φ/[(numAt (evTerm t) : FirstOrder.Semiterm ℒₒᵣ ℕ n)]) := by
  refine ev₂_rew_congr φ n (FirstOrder.Rew.subst ![t])
    (FirstOrder.Rew.subst ![(numAt (evTerm t) : FirstOrder.Semiterm ℒₒᵣ ℕ n)])
    ⟨fun i => ?_, fun x => ?_⟩
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [FirstOrder.Rew.subst_bvar, FirstOrder.Rew.subst_bvar]
    simp only [Matrix.cons_val_zero]
    rw [evT_of_ground ht, evT_numAt]
  · rw [FirstOrder.Rew.subst_fvar, FirstOrder.Rew.subst_fvar]

/-- **The normalised substitution law.**  For a ground `t` of value `m`,
evaluating `φ/[t]` is evaluating the numeral instance of the *evaluated* `φ`. -/
theorem ev₂_subst_key {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    {t : FirstOrder.Semiterm ℒₒᵣ ℕ n} (ht : Ground t) :
    ev₂ (φ/[t]) = ev₂ ((ev₂ φ)/[(numAt (evTerm t) : FirstOrder.Semiterm ℒₒᵣ ℕ n)]) := by
  rw [ev₂_subst_ground φ ht]
  exact (ev₂_rew_ev₂ φ n (FirstOrder.Rew.subst ![_])).symm

/-! ### The second-order congruence

This is the law the `(∃₂)` rule of the replay needs.  After `χ/⟦ψ⟧` an atom
`t ∈& X` of `χ` has become `ψ/[t]`; normalising `χ` first replaced `t` by
`evT t`, and `ev₂ (ψ/[evT t]) = ev₂ (ψ/[t])` is `ev₂_rew_congr` with
`evT_idem`. -/

/-- **The second-order congruence.**  Normalising a formula before a
*set* substitution does not change the normal form of the result. -/
theorem ev₂_app_ev₂ : ∀ {N₁ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) (N₂ : ℕ)
    (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ), ev₂ (Ω.app (ev₂ φ)) = ev₂ (Ω.app φ) := by
  intro N₁ n φ
  have key : ∀ {N₂ n : ℕ} (χ : Semiformula ℒₒᵣ ℕ ℕ N₂ 1)
      (t : FirstOrder.Semiterm ℒₒᵣ ℕ n), ev₂ (χ/[evT t]) = ev₂ (χ/[t]) := by
    intro N₂ n χ t
    refine ev₂_rew_congr χ n (FirstOrder.Rew.subst ![evT t]) (FirstOrder.Rew.subst ![t])
      ⟨fun i => ?_, fun x => ?_⟩
    · have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rw [FirstOrder.Rew.subst_bvar, FirstOrder.Rew.subst_bvar]
      simp only [Matrix.cons_val_zero]
      exact evT_idem t
    · rw [FirstOrder.Rew.subst_fvar, FirstOrder.Rew.subst_fvar]
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₂ Ω; simp
  | hNrel r v => intro N₂ Ω; simp
  | hBvar X t =>
      intro N₂ Ω
      simp only [ev₂_bvar, SecondOrder.Rew.app_bvar]
      exact key (Ω.bv X) t
  | hNbvar X t =>
      intro N₂ Ω
      simp only [ev₂_nbvar, SecondOrder.Rew.app_nbvar, ev₂_neg]
      exact congrArg (fun χ => ∼χ) (key (Ω.bv X) t)
  | hFvar X t =>
      intro N₂ Ω
      simp only [ev₂_fvar, SecondOrder.Rew.app_fvar]
      exact key (Ω.fv X) t
  | hNfvar X t =>
      intro N₂ Ω
      simp only [ev₂_nfvar, SecondOrder.Rew.app_nfvar, ev₂_neg]
      exact congrArg (fun χ => ∼χ) (key (Ω.fv X) t)
  | hVerum => intro N₂ Ω; simp
  | hFalsum => intro N₂ Ω; simp
  | hAnd φ ψ ihφ ihψ => intro N₂ Ω; simp [ihφ N₂ Ω, ihψ N₂ Ω]
  | hOr φ ψ ihφ ihψ => intro N₂ Ω; simp [ihφ N₂ Ω, ihψ N₂ Ω]
  | hAll₁ φ ih => intro N₂ Ω; simp [ih N₂ Ω]
  | hExs₁ φ ih => intro N₂ Ω; simp [ih N₂ Ω]
  | hAll₂ φ ih => intro N₂ Ω; simp [ih (N₂ + 1) Ω.q]
  | hExs₂ φ ih => intro N₂ Ω; simp [ih (N₂ + 1) Ω.q]

/-- **Two set substitutions the evaluator cannot tell apart.** -/
def SORewEq {N₁ N₂ : ℕ} (Ω Ω' : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ) : Prop :=
  (∀ X, ev₂ (Ω.bv X) = ev₂ (Ω'.bv X)) ∧ ∀ X, ev₂ (Ω.fv X) = ev₂ (Ω'.fv X)

theorem SORewEq.q {N₁ N₂ : ℕ} {Ω Ω' : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ} (h : SORewEq Ω Ω') :
    SORewEq Ω.q Ω'.q := by
  constructor
  · intro X
    induction X using Fin.cases with
    | zero => rw [SecondOrder.Rew.q_bv_zero, SecondOrder.Rew.q_bv_zero]
    | succ X =>
        rw [SecondOrder.Rew.q_bv_succ, SecondOrder.Rew.q_bv_succ, ev₂_bmap, ev₂_bmap, h.1 X]
  · intro X
    rw [SecondOrder.Rew.q_fv, SecondOrder.Rew.q_fv, ev₂_bmap, ev₂_bmap, h.2 X]

/-- **Value dependence for set substitutions.** -/
theorem ev₂_app_congr : ∀ {N₁ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) (N₂ : ℕ)
    (Ω Ω' : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ), SORewEq Ω Ω' →
      ev₂ (Ω.app φ) = ev₂ (Ω'.app φ) := by
  intro N₁ n φ
  have key : ∀ {N₂ n : ℕ} {χ χ' : Semiformula ℒₒᵣ ℕ ℕ N₂ 1}, ev₂ χ = ev₂ χ' →
      ∀ t : FirstOrder.Semiterm ℒₒᵣ ℕ n, ev₂ (χ/[t]) = ev₂ (χ'/[t]) := by
    intro N₂ n χ χ' h t
    rw [← ev₂_rew_ev₂ χ n (FirstOrder.Rew.subst ![t]),
      ← ev₂_rew_ev₂ χ' n (FirstOrder.Rew.subst ![t]), h]
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₂ Ω Ω' _; simp
  | hNrel r v => intro N₂ Ω Ω' _; simp
  | hBvar X t =>
      intro N₂ Ω Ω' h
      simp only [SecondOrder.Rew.app_bvar]
      exact key (h.1 X) t
  | hNbvar X t =>
      intro N₂ Ω Ω' h
      simp only [SecondOrder.Rew.app_nbvar, ev₂_neg]
      exact congrArg (fun χ => ∼χ) (key (h.1 X) t)
  | hFvar X t =>
      intro N₂ Ω Ω' h
      simp only [SecondOrder.Rew.app_fvar]
      exact key (h.2 X) t
  | hNfvar X t =>
      intro N₂ Ω Ω' h
      simp only [SecondOrder.Rew.app_nfvar, ev₂_neg]
      exact congrArg (fun χ => ∼χ) (key (h.2 X) t)
  | hVerum => intro N₂ Ω Ω' _; simp
  | hFalsum => intro N₂ Ω Ω' _; simp
  | hAnd φ ψ ihφ ihψ => intro N₂ Ω Ω' h; simp [ihφ N₂ Ω Ω' h, ihψ N₂ Ω Ω' h]
  | hOr φ ψ ihφ ihψ => intro N₂ Ω Ω' h; simp [ihφ N₂ Ω Ω' h, ihψ N₂ Ω Ω' h]
  | hAll₁ φ ih => intro N₂ Ω Ω' h; simp [ih N₂ Ω Ω' h]
  | hExs₁ φ ih => intro N₂ Ω Ω' h; simp [ih N₂ Ω Ω' h]
  | hAll₂ φ ih => intro N₂ Ω Ω' h; simp [ih (N₂ + 1) Ω.q Ω'.q h.q]
  | hExs₂ φ ih => intro N₂ Ω Ω' h; simp [ih (N₂ + 1) Ω.q Ω'.q h.q]

/-- **The law the `(∃₂)` replay needs**: evaluating the body first changes
nothing. -/
theorem ev₂_subst₂_ev₂ (χ : Semiproposition ℒₒᵣ 1 0) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    ev₂ ((ev₂ χ)/⟦ψ⟧) = ev₂ (χ/⟦ψ⟧) :=
  ev₂_app_ev₂ χ 0 (SecondOrder.Rew.subst ![ψ])

/-- The same for the witness: evaluating `ψ` first changes nothing either. -/
theorem ev₂_subst₂_congr {N : ℕ} (χ : Semiformula ℒₒᵣ ℕ ℕ 1 0)
    (ψ : Semiformula ℒₒᵣ ℕ ℕ N 1) :
    ev₂ (χ/⟦ev₂ ψ⟧) = ev₂ (χ/⟦ψ⟧) := by
  refine ev₂_app_congr χ N (SecondOrder.Rew.subst ![ev₂ ψ]) (SecondOrder.Rew.subst ![ψ])
    ⟨fun X => ?_, fun X => rfl⟩
  have hX : X = 0 := Subsingleton.elim X 0
  subst hX
  simp only [SecondOrder.Rew.subst_bv, Matrix.cons_val_zero]
  exact ev₂_idem ψ

/-! ### Truth is preserved -/

/-- **`ev₂` preserves truth**, at every level, in every second-order structure
over the standard `ℕ`. -/
theorem eval_ev₂ (𝕊 : Set (Set ℕ)) (F : ℕ → Set ℕ) (f : ℕ → ℕ) :
    ∀ {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n) (E : Fin N → Set ℕ) (e : Fin n → ℕ),
      ((ev₂ φ).Eval 𝕊 F f E e ↔ φ.Eval 𝕊 F f E e) := by
  intro N n φ
  induction φ using Semiformula.rec' with
  | hRel r v =>
      intro E e
      simp only [ev₂_rel, Semiformula.eval_rel, Function.comp_def]
      exact Iff.of_eq (congrArg (FirstOrder.Structure.rel (M := ℕ) r)
        (funext fun i => val_evT (v i) e f))
  | hNrel r v =>
      intro E e
      simp only [ev₂_nrel, Semiformula.eval_nrel, Function.comp_def]
      exact not_congr (Iff.of_eq (congrArg (FirstOrder.Structure.rel (M := ℕ) r)
        (funext fun i => val_evT (v i) e f)))
  | hBvar X t => intro E e; simp only [ev₂_bvar, Semiformula.eval_bvar, val_evT]
  | hNbvar X t => intro E e; simp only [ev₂_nbvar, Semiformula.eval_nbvar, val_evT]
  | hFvar X t => intro E e; simp only [ev₂_fvar, Semiformula.eval_fvar, val_evT]
  | hNfvar X t => intro E e; simp only [ev₂_nfvar, Semiformula.eval_nfvar, val_evT]
  | hVerum => intro E e; simp
  | hFalsum => intro E e; simp
  | hAnd φ ψ ihφ ihψ =>
      intro E e
      simp only [ev₂_and, LogicalConnective.HomClass.map_and]
      exact and_congr (ihφ E e) (ihψ E e)
  | hOr φ ψ ihφ ihψ =>
      intro E e
      simp only [ev₂_or, LogicalConnective.HomClass.map_or]
      exact or_congr (ihφ E e) (ihψ E e)
  | hAll₁ φ ih =>
      intro E e
      simp only [ev₂_all₁, Semiformula.eval_fal₀]
      exact forall_congr' fun x => ih E (x :> e)
  | hExs₁ φ ih =>
      intro E e
      simp only [ev₂_exs₁, Semiformula.eval_exs₀]
      exact exists_congr fun x => ih E (x :> e)
  | hAll₂ φ ih =>
      intro E e
      simp only [ev₂_all₂, Semiformula.eval_fal₁]
      exact forall_congr' fun X => imp_congr_right fun _ => ih (X :> E) e
  | hExs₂ φ ih =>
      intro E e
      simp only [ev₂_exs₂, Semiformula.eval_exs₁]
      exact exists_congr fun X => and_congr_right fun _ => ih (X :> E) e

/-! ### Substituting a set variable, evaluating only what is created

A second-order substitution replaces a set atom `t ∈& X` by `(Ω.fv X)/[t]`.
When the component `Ω.fv X` is a bare set atom `#0 ∈& Y` — which is what a
*renaming* component is — nothing has been created: the result is `t ∈& Y`, and
evaluating it would evaluate `t`, which the substitution had no business
touching.  When the component is a genuine formula `ψ`, the instance `ψ/[t]` is
brand new and must be normalised, because the `(∃₂)` premise of the calculus is.

`evSub` makes exactly that distinction, `evApp` is the induced application of a
second-order rewriting, and `evInst₂.inst₂ φ ψ := evApp (Rew.subst ![ψ]) φ`.
Doing it any other way is impossible: a `SubstProvider` has to agree with
`inst₂` on `free₁ φ` and be the identity on `shift₁ γ`, and the two ranges
overlap (`free₁ (t ∈& 5) = shift₁ (t ∈& 5) = t ∈& 6`), so `inst₂` may not move
anything it did not create. -/

/-- `t` is a bound number variable. -/
def isBvar {n : ℕ} : FirstOrder.Semiterm ℒₒᵣ ℕ n → Bool
  |      #_ => true
  |      &_ => false
  | .func _ _ => false

@[simp] theorem isBvar_bvar {n : ℕ} (x : Fin n) :
    isBvar (#x : FirstOrder.Semiterm ℒₒᵣ ℕ n) = true := rfl

@[simp] theorem isBvar_fvar {n : ℕ} (x : ℕ) :
    isBvar (&x : FirstOrder.Semiterm ℒₒᵣ ℕ n) = false := rfl

@[simp] theorem isBvar_func {n k : ℕ} (f : (ℒₒᵣ : FirstOrder.Language).Func k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    isBvar (FirstOrder.Semiterm.func f v) = false := rfl

theorem isBvar_eq_false_of_ground {n : ℕ} {t : FirstOrder.Semiterm ℒₒᵣ ℕ n} (h : Ground t) :
    isBvar t = false := by
  cases t with
  | bvar x => exact absurd h (not_ground_bvar x)
  | fvar x => rfl
  | func f v => rfl

@[simp] theorem isBvar_evT {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    isBvar (evT t) = isBvar t := by
  cases t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v =>
      by_cases h : Ground (FirstOrder.Semiterm.func f v)
      · rw [evT_of_ground h, isBvar_func]
        exact isBvar_eq_false_of_ground (ground_numAt _)
      · rw [evT_func_of_not_ground f v h]
        rfl

/-- A *number* substitution does not turn a non-variable into a bound variable:
it moves `#i`, and fixes `&x` and every compound term. -/
theorem isBvar_subst_of_not {n₁ n₂ : ℕ} (w : Fin n₁ → FirstOrder.Semiterm ℒₒᵣ ℕ n₂)
    {t : FirstOrder.Semiterm ℒₒᵣ ℕ n₁} (h : isBvar t = false) :
    isBvar (FirstOrder.Rew.subst w t) = false := by
  cases t with
  | bvar x => exact absurd h (by simp)
  | fvar x => rw [FirstOrder.Rew.subst_fvar]; rfl
  | func f v => rw [(FirstOrder.Rew.subst w).func' f v]; rfl

/-- `χ` is a bare set atom, one of `#0 ∈# Y`, `#0 ∉# Y`, `#0 ∈& Y`, `#0 ∉& Y`:
a *renaming* component of a second-order rewriting. -/
def isSetAtom {N : ℕ} : Semiformula ℒₒᵣ ℕ ℕ N 1 → Bool
  |  .rel _ _ => false
  | .nrel _ _ => false
  |    t ∈# _ => isBvar t
  |    t ∉# _ => isBvar t
  |    t ∈& _ => isBvar t
  |    t ∉& _ => isBvar t
  |         ⊤ => false
  |         ⊥ => false
  |     _ ⋏ _ => false
  |     _ ⋎ _ => false
  |      ∀¹ _ => false
  |      ∃¹ _ => false
  |      ∀² _ => false
  |      ∃² _ => false

section IsSetAtomSimp

variable {N : ℕ}

@[simp] theorem isSetAtom_rel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ 1) :
    isSetAtom (.rel r v : Semiformula ℒₒᵣ ℕ ℕ N 1) = false := rfl

@[simp] theorem isSetAtom_nrel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ 1) :
    isSetAtom (.nrel r v : Semiformula ℒₒᵣ ℕ ℕ N 1) = false := rfl

@[simp] theorem isSetAtom_bvar (X : Fin N) (t : FirstOrder.Semiterm ℒₒᵣ ℕ 1) :
    isSetAtom (t ∈# X : Semiformula ℒₒᵣ ℕ ℕ N 1) = isBvar t := rfl

@[simp] theorem isSetAtom_nbvar (X : Fin N) (t : FirstOrder.Semiterm ℒₒᵣ ℕ 1) :
    isSetAtom (t ∉# X : Semiformula ℒₒᵣ ℕ ℕ N 1) = isBvar t := rfl

@[simp] theorem isSetAtom_fvar (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ 1) :
    isSetAtom (t ∈& X : Semiformula ℒₒᵣ ℕ ℕ N 1) = isBvar t := rfl

@[simp] theorem isSetAtom_nfvar (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ 1) :
    isSetAtom (t ∉& X : Semiformula ℒₒᵣ ℕ ℕ N 1) = isBvar t := rfl

@[simp] theorem isSetAtom_verum : isSetAtom (⊤ : Semiformula ℒₒᵣ ℕ ℕ N 1) = false := rfl

@[simp] theorem isSetAtom_falsum : isSetAtom (⊥ : Semiformula ℒₒᵣ ℕ ℕ N 1) = false := rfl

@[simp] theorem isSetAtom_and (φ ψ : Semiformula ℒₒᵣ ℕ ℕ N 1) :
    isSetAtom (φ ⋏ ψ) = false := rfl

@[simp] theorem isSetAtom_or (φ ψ : Semiformula ℒₒᵣ ℕ ℕ N 1) :
    isSetAtom (φ ⋎ ψ) = false := rfl

@[simp] theorem isSetAtom_all₁ (φ : Semiformula ℒₒᵣ ℕ ℕ N 2) :
    isSetAtom (∀¹ φ) = false := rfl

@[simp] theorem isSetAtom_exs₁ (φ : Semiformula ℒₒᵣ ℕ ℕ N 2) :
    isSetAtom (∃¹ φ) = false := rfl

@[simp] theorem isSetAtom_all₂ (φ : Semiformula ℒₒᵣ ℕ ℕ (N + 1) 1) :
    isSetAtom (∀² φ) = false := rfl

@[simp] theorem isSetAtom_exs₂ (φ : Semiformula ℒₒᵣ ℕ ℕ (N + 1) 1) :
    isSetAtom (∃² φ) = false := rfl

end IsSetAtomSimp

@[simp] theorem isSetAtom_neg {N : ℕ} (χ : Semiformula ℒₒᵣ ℕ ℕ N 1) :
    isSetAtom (∼χ) = isSetAtom χ := by
  cases χ using Semiformula.cases' <;> simp

@[simp] theorem isSetAtom_ev₂ {N : ℕ} (χ : Semiformula ℒₒᵣ ℕ ℕ N 1) :
    isSetAtom (ev₂ χ) = isSetAtom χ := by
  cases χ using Semiformula.cases' <;> simp

@[simp] theorem isSetAtom_bmap {N M : ℕ} (f : Fin N → Fin M) (χ : Semiformula ℒₒᵣ ℕ ℕ N 1) :
    isSetAtom (χ.bmap f) = isSetAtom χ := by
  cases χ using Semiformula.cases' <;> simp

theorem isSetAtom_subst_of_not {N : ℕ} {χ : Semiformula ℒₒᵣ ℕ ℕ N 1}
    (w : Fin 1 → FirstOrder.Semiterm ℒₒᵣ ℕ 1) (h : isSetAtom χ = false) :
    isSetAtom (FirstOrder.Rew.subst w ▹ χ) = false := by
  cases χ using Semiformula.cases' with
  | hRel r v => simp [Semiformula.rew_rel]
  | hNrel r v => simp [Semiformula.rew_nrel]
  | hBvar X t => simpa using isBvar_subst_of_not w (by simpa using h)
  | hNbvar X t => simpa using isBvar_subst_of_not w (by simpa using h)
  | hFvar X t => simpa using isBvar_subst_of_not w (by simpa using h)
  | hNfvar X t => simpa using isBvar_subst_of_not w (by simpa using h)
  | hVerum => simp
  | hFalsum => simp
  | hAnd φ ψ => simp
  | hOr φ ψ => simp
  | hAll₁ φ => simp
  | hExs₁ φ => simp
  | hAll₂ φ => simp
  | hExs₂ φ => simp

/-- The four shapes a bare set atom can take. -/
theorem eq_of_isSetAtom {N : ℕ} {χ : Semiformula ℒₒᵣ ℕ ℕ N 1} (h : isSetAtom χ = true) :
    (∃ Y : Fin N, χ = ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# Y)) ∨
      (∃ Y : Fin N, χ = ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∉# Y)) ∨
      (∃ Y : ℕ, χ = ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& Y)) ∨
      (∃ Y : ℕ, χ = ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∉& Y)) := by
  have hb : ∀ t : FirstOrder.Semiterm ℒₒᵣ ℕ 1, isBvar t = true →
      t = (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) := by
    intro t ht
    cases t with
    | bvar x => rw [Fin.fin_one_eq_zero x]
    | fvar x => exact absurd ht (by simp)
    | func f v => exact absurd ht (by simp)
  cases χ using Semiformula.cases' with
  | hRel r v => exact absurd h (by simp)
  | hNrel r v => exact absurd h (by simp)
  | hBvar X t => exact Or.inl ⟨X, by rw [hb t (by simpa using h)]⟩
  | hNbvar X t => exact Or.inr (Or.inl ⟨X, by rw [hb t (by simpa using h)]⟩)
  | hFvar X t => exact Or.inr (Or.inr (Or.inl ⟨X, by rw [hb t (by simpa using h)]⟩))
  | hNfvar X t => exact Or.inr (Or.inr (Or.inr ⟨X, by rw [hb t (by simpa using h)]⟩))
  | hVerum => exact absurd h (by simp)
  | hFalsum => exact absurd h (by simp)
  | hAnd φ ψ => exact absurd h (by simp)
  | hOr φ ψ => exact absurd h (by simp)
  | hAll₁ φ => exact absurd h (by simp)
  | hExs₁ φ => exact absurd h (by simp)
  | hAll₂ φ => exact absurd h (by simp)
  | hExs₂ φ => exact absurd h (by simp)

/-- **Substitution into a component**: substitute `t`, and normalise the result
unless the component was a bare set atom, in which case nothing was created. -/
def evSub {N n : ℕ} (χ : Semiformula ℒₒᵣ ℕ ℕ N 1) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    Semiformula ℒₒᵣ ℕ ℕ N n :=
  if isSetAtom χ = true then χ/[t] else ev₂ (χ/[t])

theorem evSub_of_atom {N n : ℕ} {χ : Semiformula ℒₒᵣ ℕ ℕ N 1} (h : isSetAtom χ = true)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : evSub χ t = χ/[t] := by
  simp only [evSub, h, if_true]

theorem evSub_of_not_atom {N n : ℕ} {χ : Semiformula ℒₒᵣ ℕ ℕ N 1} (h : isSetAtom χ = false)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : evSub χ t = ev₂ (χ/[t]) := by
  simp only [evSub, h, Bool.false_eq_true, if_false]

@[simp] theorem evSub_bv {N n : ℕ} (Y : Fin N) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    evSub ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# Y) t = t ∈# Y := by
  rw [evSub_of_atom rfl]; simp

@[simp] theorem evSub_nbv {N n : ℕ} (Y : Fin N) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    evSub ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∉# Y) t = t ∉# Y := by
  rw [evSub_of_atom rfl]; simp

@[simp] theorem evSub_fv {N n : ℕ} (Y : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    evSub ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& Y : Semiformula ℒₒᵣ ℕ ℕ N 1) t = t ∈& Y := by
  rw [evSub_of_atom rfl]; simp

@[simp] theorem evSub_nfv {N n : ℕ} (Y : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    evSub ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∉& Y : Semiformula ℒₒᵣ ℕ ℕ N 1) t = t ∉& Y := by
  rw [evSub_of_atom rfl]; simp

@[simp] theorem evSub_neg {N n : ℕ} (χ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : evSub (∼χ) t = ∼evSub χ t := by
  by_cases h : isSetAtom χ = true
  · rw [evSub_of_atom h, evSub_of_atom (by simpa using h)]
    simp
  · have h' : isSetAtom χ = false := by simpa using h
    rw [evSub_of_not_atom h', evSub_of_not_atom (by simpa using h')]
    simp

/-- **Normalising after `evSub` is normalising after the plain substitution.** -/
@[simp] theorem ev₂_evSub {N n : ℕ} (χ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : ev₂ (evSub χ t) = ev₂ (χ/[t]) := by
  by_cases h : isSetAtom χ = true
  · rw [evSub_of_atom h]
  · rw [evSub_of_not_atom (by simpa using h), ev₂_idem]

@[simp] theorem rank_evSub {N n : ℕ} (χ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : rank (evSub χ t) = rank (χ/[t]) := by
  by_cases h : isSetAtom χ = true
  · rw [evSub_of_atom h]
  · rw [evSub_of_not_atom (by simpa using h), rank_ev₂]

@[simp] theorem arith_evSub {N n : ℕ} (χ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : Arith (evSub χ t) ↔ Arith (χ/[t]) := by
  by_cases h : isSetAtom χ = true
  · rw [evSub_of_atom h]
  · rw [evSub_of_not_atom (by simpa using h), arith_ev₂]

/-- **An already-normalised term is substituted as the plain substitution
would.**  This is what makes `evApp` agree with `ev₂ ∘ app` on normal forms. -/
theorem evSub_evT {N n : ℕ} (χ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : evSub χ (evT t) = ev₂ (χ/[t]) := by
  by_cases h : isSetAtom χ = true
  · rw [evSub_of_atom h]
    rcases eq_of_isSetAtom h with ⟨Y, rfl⟩ | ⟨Y, rfl⟩ | ⟨Y, rfl⟩ | ⟨Y, rfl⟩ <;> simp
  · rw [evSub_of_not_atom (by simpa using h)]
    refine ev₂_rew_congr χ n (FirstOrder.Rew.subst ![evT t]) (FirstOrder.Rew.subst ![t])
      ⟨fun i => ?_, fun x => ?_⟩
    · have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rw [FirstOrder.Rew.subst_bvar, FirstOrder.Rew.subst_bvar]
      simp only [Matrix.cons_val_zero]
      exact evT_idem t
    · rw [FirstOrder.Rew.subst_fvar, FirstOrder.Rew.subst_fvar]

theorem evSub_evSub_bvar {N n : ℕ} (χ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    evSub (evSub χ (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)) t = evSub χ t := by
  by_cases h : isSetAtom χ = true
  · rw [evSub_of_atom h, subst_bvar_self]
  · have h' : isSetAtom χ = false := by simpa using h
    rw [evSub_of_not_atom h', subst_bvar_self,
      evSub_of_not_atom (by rw [isSetAtom_ev₂]; exact h'),
      evSub_of_not_atom h']
    exact ev₂_rew_ev₂ χ n (FirstOrder.Rew.subst ![t])

theorem isSetAtom_evSub_of_not_bvar {N : ℕ} (χ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    {t : FirstOrder.Semiterm ℒₒᵣ ℕ 1} (ht : isBvar t = false) :
    isSetAtom (evSub χ t) = false := by
  by_cases h : isSetAtom χ = true
  · rw [evSub_of_atom h]
    rcases eq_of_isSetAtom h with ⟨Y, rfl⟩ | ⟨Y, rfl⟩ | ⟨Y, rfl⟩ | ⟨Y, rfl⟩ <;> simpa using ht
  · rw [evSub_of_not_atom (by simpa using h), isSetAtom_ev₂]
    exact isSetAtom_subst_of_not _ (by simpa using h)

theorem evSub_bmap {N M n : ℕ} (f : Fin N → Fin M) (χ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : (evSub χ t).bmap f = evSub (χ.bmap f) t := by
  by_cases h : isSetAtom χ = true
  · rw [evSub_of_atom h, evSub_of_atom (by rw [isSetAtom_bmap]; exact h),
      Semiformula.bmap_comm]
  · have h' : isSetAtom χ = false := by simpa using h
    rw [evSub_of_not_atom h', evSub_of_not_atom (by rw [isSetAtom_bmap]; exact h'),
      ← ev₂_bmap, Semiformula.bmap_comm]

/-- A renaming of set variables neither creates nor destroys a bare set atom. -/
theorem isSetAtom_app_atomRew {N₁ N₂ : ℕ} {R : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ}
    (hR : AtomRew R) (χ : Semiformula ℒₒᵣ ℕ ℕ N₁ 1) :
    isSetAtom (R.app χ) = isSetAtom χ := by
  cases χ using Semiformula.cases' with
  | hRel r v => simp
  | hNrel r v => simp
  | hBvar X t => rcases hR.1 X with ⟨Z, hZ⟩ | ⟨Z, hZ⟩ <;> simp [hZ]
  | hNbvar X t => rcases hR.1 X with ⟨Z, hZ⟩ | ⟨Z, hZ⟩ <;> simp [hZ]
  | hFvar X t => rcases hR.2 X with ⟨Z, hZ⟩ | ⟨Z, hZ⟩ <;> simp [hZ]
  | hNfvar X t => rcases hR.2 X with ⟨Z, hZ⟩ | ⟨Z, hZ⟩ <;> simp [hZ]
  | hVerum => simp
  | hFalsum => simp
  | hAnd φ ψ => simp
  | hOr φ ψ => simp
  | hAll₁ φ => simp
  | hExs₁ φ => simp
  | hAll₂ φ => simp
  | hExs₂ φ => simp

theorem evSub_atomRew {N₁ N₂ n : ℕ} {R : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ} (hR : AtomRew R)
    (χ : Semiformula ℒₒᵣ ℕ ℕ N₁ 1) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    R.app (evSub χ t) = evSub (R.app χ) t := by
  by_cases h : isSetAtom χ = true
  · rw [evSub_of_atom h, evSub_of_atom (by rw [isSetAtom_app_atomRew hR]; exact h),
      SecondOrder.Rew.app_comm_subst]
  · have h' : isSetAtom χ = false := by simpa using h
    rw [evSub_of_not_atom h',
      evSub_of_not_atom (by rw [isSetAtom_app_atomRew hR]; exact h'),
      ← ev₂_app_atom _ _ R hR, SecondOrder.Rew.app_comm_subst]

/-! ### The evaluating application of a second-order rewriting -/

/-- **`Ω.app`, normalising exactly what it creates.** -/
def evApp {N₁ N₂ n : ℕ} (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ) :
    Semiformula ℒₒᵣ ℕ ℕ N₁ n → Semiformula ℒₒᵣ ℕ ℕ N₂ n
  |  .rel r v => .rel r v
  | .nrel r v => .nrel r v
  |    t ∈# X => evSub (Ω.bv X) t
  |    t ∉# X => ∼evSub (Ω.bv X) t
  |    t ∈& X => evSub (Ω.fv X) t
  |    t ∉& X => ∼evSub (Ω.fv X) t
  |         ⊤ => ⊤
  |         ⊥ => ⊥
  |     φ ⋏ χ => evApp Ω φ ⋏ evApp Ω χ
  |     φ ⋎ χ => evApp Ω φ ⋎ evApp Ω χ
  |      ∀¹ φ => ∀¹ (evApp Ω φ)
  |      ∃¹ φ => ∃¹ (evApp Ω φ)
  |      ∀² φ => ∀² (evApp Ω.q φ)
  |      ∃² φ => ∃² (evApp Ω.q φ)

section EvAppSimp

variable {N₁ N₂ n : ℕ} (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ)

@[simp] theorem evApp_rel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    evApp Ω (.rel r v : Semiformula ℒₒᵣ ℕ ℕ N₁ n) = .rel r v := rfl

@[simp] theorem evApp_nrel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    evApp Ω (.nrel r v : Semiformula ℒₒᵣ ℕ ℕ N₁ n) = .nrel r v := rfl

@[simp] theorem evApp_bvar (X : Fin N₁) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    evApp Ω (t ∈# X) = evSub (Ω.bv X) t := rfl

@[simp] theorem evApp_nbvar (X : Fin N₁) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    evApp Ω (t ∉# X) = ∼evSub (Ω.bv X) t := rfl

@[simp] theorem evApp_fvar (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    evApp Ω (t ∈& X) = evSub (Ω.fv X) t := rfl

@[simp] theorem evApp_nfvar (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    evApp Ω (t ∉& X) = ∼evSub (Ω.fv X) t := rfl

@[simp] theorem evApp_verum : evApp Ω (⊤ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) = ⊤ := rfl

@[simp] theorem evApp_falsum : evApp Ω (⊥ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) = ⊥ := rfl

@[simp] theorem evApp_and (φ ψ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) :
    evApp Ω (φ ⋏ ψ) = evApp Ω φ ⋏ evApp Ω ψ := rfl

@[simp] theorem evApp_or (φ ψ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) :
    evApp Ω (φ ⋎ ψ) = evApp Ω φ ⋎ evApp Ω ψ := rfl

@[simp] theorem evApp_all₁ (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ (n + 1)) :
    evApp Ω (∀¹ φ) = ∀¹ (evApp Ω φ) := rfl

@[simp] theorem evApp_exs₁ (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ (n + 1)) :
    evApp Ω (∃¹ φ) = ∃¹ (evApp Ω φ) := rfl

@[simp] theorem evApp_all₂ (φ : Semiformula ℒₒᵣ ℕ ℕ (N₁ + 1) n) :
    evApp Ω (∀² φ) = ∀² (evApp Ω.q φ) := rfl

@[simp] theorem evApp_exs₂ (φ : Semiformula ℒₒᵣ ℕ ℕ (N₁ + 1) n) :
    evApp Ω (∃² φ) = ∃² (evApp Ω.q φ) := rfl

end EvAppSimp

@[simp] theorem evApp_neg : ∀ {N₁ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) (N₂ : ℕ)
    (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ), evApp Ω (∼φ) = ∼evApp Ω φ := by
  intro N₁ n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₂ Ω; simp
  | hNrel r v => intro N₂ Ω; simp
  | hBvar X t => intro N₂ Ω; simp
  | hNbvar X t => intro N₂ Ω; simp
  | hFvar X t => intro N₂ Ω; simp
  | hNfvar X t => intro N₂ Ω; simp
  | hVerum => intro N₂ Ω; simp
  | hFalsum => intro N₂ Ω; simp
  | hAnd φ ψ ihφ ihψ => intro N₂ Ω; simp [ihφ N₂ Ω, ihψ N₂ Ω]
  | hOr φ ψ ihφ ihψ => intro N₂ Ω; simp [ihφ N₂ Ω, ihψ N₂ Ω]
  | hAll₁ φ ih => intro N₂ Ω; simp [ih N₂ Ω]
  | hExs₁ φ ih => intro N₂ Ω; simp [ih N₂ Ω]
  | hAll₂ φ ih => intro N₂ Ω; simp [ih (N₂ + 1) Ω.q]
  | hExs₂ φ ih => intro N₂ Ω; simp [ih (N₂ + 1) Ω.q]

/-- **`evApp` has the rank of the plain application.** -/
@[simp] theorem rank_evApp : ∀ {N₁ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) (N₂ : ℕ)
    (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ), rank (evApp Ω φ) = rank (Ω.app φ) := by
  intro N₁ n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₂ Ω; simp
  | hNrel r v => intro N₂ Ω; simp
  | hBvar X t => intro N₂ Ω; simp
  | hNbvar X t => intro N₂ Ω; simp
  | hFvar X t => intro N₂ Ω; simp
  | hNfvar X t => intro N₂ Ω; simp
  | hVerum => intro N₂ Ω; simp
  | hFalsum => intro N₂ Ω; simp
  | hAnd φ ψ ihφ ihψ => intro N₂ Ω; simp [ihφ N₂ Ω, ihψ N₂ Ω]
  | hOr φ ψ ihφ ihψ => intro N₂ Ω; simp [ihφ N₂ Ω, ihψ N₂ Ω]
  | hAll₁ φ ih => intro N₂ Ω; simp [ih N₂ Ω]
  | hExs₁ φ ih => intro N₂ Ω; simp [ih N₂ Ω]
  | hAll₂ φ ih => intro N₂ Ω; simp [ih (N₂ + 1) Ω.q]
  | hExs₂ φ ih => intro N₂ Ω; simp [ih (N₂ + 1) Ω.q]

/-- **`evApp` is arithmetical exactly when the plain application is.** -/
@[simp] theorem arith_evApp : ∀ {N₁ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) (N₂ : ℕ)
    (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ), Arith (evApp Ω φ) ↔ Arith (Ω.app φ) := by
  intro N₁ n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₂ Ω; simp
  | hNrel r v => intro N₂ Ω; simp
  | hBvar X t => intro N₂ Ω; simp
  | hNbvar X t => intro N₂ Ω; simp
  | hFvar X t => intro N₂ Ω; simp
  | hNfvar X t => intro N₂ Ω; simp
  | hVerum => intro N₂ Ω; simp
  | hFalsum => intro N₂ Ω; simp
  | hAnd φ ψ ihφ ihψ => intro N₂ Ω; simp [ihφ N₂ Ω, ihψ N₂ Ω]
  | hOr φ ψ ihφ ihψ => intro N₂ Ω; simp [ihφ N₂ Ω, ihψ N₂ Ω]
  | hAll₁ φ ih => intro N₂ Ω; simp [ih N₂ Ω]
  | hExs₁ φ ih => intro N₂ Ω; simp [ih N₂ Ω]
  | hAll₂ φ ih => intro N₂ Ω; simp [ih (N₂ + 1) Ω.q]
  | hExs₂ φ ih => intro N₂ Ω; simp [ih (N₂ + 1) Ω.q]

/-- **Normalising after `evApp` is normalising after the plain application.** -/
@[simp] theorem ev₂_evApp : ∀ {N₁ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) (N₂ : ℕ)
    (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ), ev₂ (evApp Ω φ) = ev₂ (Ω.app φ) := by
  intro N₁ n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₂ Ω; simp
  | hNrel r v => intro N₂ Ω; simp
  | hBvar X t => intro N₂ Ω; simp
  | hNbvar X t => intro N₂ Ω; simp
  | hFvar X t => intro N₂ Ω; simp
  | hNfvar X t => intro N₂ Ω; simp
  | hVerum => intro N₂ Ω; simp
  | hFalsum => intro N₂ Ω; simp
  | hAnd φ ψ ihφ ihψ => intro N₂ Ω; simp [ihφ N₂ Ω, ihψ N₂ Ω]
  | hOr φ ψ ihφ ihψ => intro N₂ Ω; simp [ihφ N₂ Ω, ihψ N₂ Ω]
  | hAll₁ φ ih => intro N₂ Ω; simp [ih N₂ Ω]
  | hExs₁ φ ih => intro N₂ Ω; simp [ih N₂ Ω]
  | hAll₂ φ ih => intro N₂ Ω; simp [ih (N₂ + 1) Ω.q]
  | hExs₂ φ ih => intro N₂ Ω; simp [ih (N₂ + 1) Ω.q]

/-- **On a normal form, `evApp` is the normalised plain application.**  This is
the bridge between the two: the calculus only ever sees normalised formulas, and
there `evApp` behaves like `ev₂ ∘ app`, which is what the congruence laws
describe. -/
theorem evApp_ev₂ : ∀ {N₁ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) (N₂ : ℕ)
    (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ), evApp Ω (ev₂ φ) = ev₂ (Ω.app φ) := by
  intro N₁ n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₂ Ω; simp
  | hNrel r v => intro N₂ Ω; simp
  | hBvar X t => intro N₂ Ω; simpa using evSub_evT (Ω.bv X) t
  | hNbvar X t =>
      intro N₂ Ω
      simpa using congrArg (fun χ => ∼χ) (evSub_evT (Ω.bv X) t)
  | hFvar X t => intro N₂ Ω; simpa using evSub_evT (Ω.fv X) t
  | hNfvar X t =>
      intro N₂ Ω
      simpa using congrArg (fun χ => ∼χ) (evSub_evT (Ω.fv X) t)
  | hVerum => intro N₂ Ω; simp
  | hFalsum => intro N₂ Ω; simp
  | hAnd φ ψ ihφ ihψ => intro N₂ Ω; simp [ihφ N₂ Ω, ihψ N₂ Ω]
  | hOr φ ψ ihφ ihψ => intro N₂ Ω; simp [ihφ N₂ Ω, ihψ N₂ Ω]
  | hAll₁ φ ih => intro N₂ Ω; simp [ih N₂ Ω]
  | hExs₁ φ ih => intro N₂ Ω; simp [ih N₂ Ω]
  | hAll₂ φ ih => intro N₂ Ω; simp [ih (N₂ + 1) Ω.q]
  | hExs₂ φ ih => intro N₂ Ω; simp [ih (N₂ + 1) Ω.q]

/-- **The identity rewriting is the identity** — nothing is created, so nothing
is evaluated.  This is what makes `ctx` hold for *every* context formula. -/
@[simp] theorem evApp_id : ∀ {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n),
    evApp (SecondOrder.Rew.id) φ = φ := by
  intro N n φ
  induction φ using Semiformula.rec' <;> simp [*]

/-- **A renaming pulled out of `evApp` on the right.** -/
theorem evApp_comp_atomRew : ∀ {N₀ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₀ n) (N₁ N₂ : ℕ)
    (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ) (R : SecondOrder.Rew ℒₒᵣ ℕ N₀ ℕ N₁ ℕ), AtomRew R →
      evApp Ω (R.app φ) = evApp (Ω.comp R) φ := by
  intro N₀ n φ
  have key : ∀ {N₁ N₂ n : ℕ} (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ)
      (c : Semiformula ℒₒᵣ ℕ ℕ N₁ 1) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n),
      (∃ Z : Fin N₁, c = ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# Z)) ∨
        (∃ Z : ℕ, c = ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& Z)) →
      evApp Ω (c/[t]) = evSub (Ω.app c) t := by
    rintro N₁ N₂ n Ω c t (⟨Z, rfl⟩ | ⟨Z, rfl⟩) <;>
      simp only [Semiformula.rew_bvar, Semiformula.rew_fvar, FirstOrder.Rew.subst_bvar,
        Matrix.cons_val_zero, evApp_bvar, evApp_fvar, SecondOrder.Rew.app_bvar,
        SecondOrder.Rew.app_fvar, subst_bvar_self]
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₁ N₂ Ω R _; simp
  | hNrel r v => intro N₁ N₂ Ω R _; simp
  | hBvar X t =>
      intro N₁ N₂ Ω R hR
      simp only [SecondOrder.Rew.app_bvar, evApp_bvar, SecondOrder.Rew.comp_bv]
      exact key Ω (R.bv X) t (hR.1 X)
  | hNbvar X t =>
      intro N₁ N₂ Ω R hR
      simp only [SecondOrder.Rew.app_nbvar, evApp_nbvar, SecondOrder.Rew.comp_bv,
        evApp_neg]
      exact congrArg (fun χ => ∼χ) (key Ω (R.bv X) t (hR.1 X))
  | hFvar X t =>
      intro N₁ N₂ Ω R hR
      simp only [SecondOrder.Rew.app_fvar, evApp_fvar, SecondOrder.Rew.comp_fv]
      exact key Ω (R.fv X) t (hR.2 X)
  | hNfvar X t =>
      intro N₁ N₂ Ω R hR
      simp only [SecondOrder.Rew.app_nfvar, evApp_nfvar, SecondOrder.Rew.comp_fv,
        evApp_neg]
      exact congrArg (fun χ => ∼χ) (key Ω (R.fv X) t (hR.2 X))
  | hVerum => intro N₁ N₂ Ω R _; simp
  | hFalsum => intro N₁ N₂ Ω R _; simp
  | hAnd φ ψ ihφ ihψ => intro N₁ N₂ Ω R hR; simp [ihφ N₁ N₂ Ω R hR, ihψ N₁ N₂ Ω R hR]
  | hOr φ ψ ihφ ihψ => intro N₁ N₂ Ω R hR; simp [ihφ N₁ N₂ Ω R hR, ihψ N₁ N₂ Ω R hR]
  | hAll₁ φ ih => intro N₁ N₂ Ω R hR; simp [ih N₁ N₂ Ω R hR]
  | hExs₁ φ ih => intro N₁ N₂ Ω R hR; simp [ih N₁ N₂ Ω R hR]
  | hAll₂ φ ih =>
      intro N₁ N₂ Ω R hR
      simp only [SecondOrder.Rew.app_all₁, evApp_all₂, SecondOrder.Rew.q_comp_eq]
      exact congrArg (fun χ => ∀² χ) (ih (N₁ + 1) (N₂ + 1) Ω.q R.q hR.q)
  | hExs₂ φ ih =>
      intro N₁ N₂ Ω R hR
      simp only [SecondOrder.Rew.app_exs₁, evApp_exs₂, SecondOrder.Rew.q_comp_eq]
      exact congrArg (fun χ => ∃² χ) (ih (N₁ + 1) (N₂ + 1) Ω.q R.q hR.q)

/-- **A renaming pulled into `evApp` on the left.** -/
theorem evApp_atomRew_comp : ∀ {N₁ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) (N₂ N₃ : ℕ)
    (R : SecondOrder.Rew ℒₒᵣ ℕ N₂ ℕ N₃ ℕ) (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ), AtomRew R →
      R.app (evApp Ω φ) = evApp (R.comp Ω) φ := by
  intro N₁ n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₂ N₃ R Ω _; simp
  | hNrel r v => intro N₂ N₃ R Ω _; simp
  | hBvar X t =>
      intro N₂ N₃ R Ω hR
      simpa using evSub_atomRew hR (Ω.bv X) t
  | hNbvar X t =>
      intro N₂ N₃ R Ω hR
      simpa using congrArg (fun χ => ∼χ) (evSub_atomRew hR (Ω.bv X) t)
  | hFvar X t =>
      intro N₂ N₃ R Ω hR
      simpa using evSub_atomRew hR (Ω.fv X) t
  | hNfvar X t =>
      intro N₂ N₃ R Ω hR
      simpa using congrArg (fun χ => ∼χ) (evSub_atomRew hR (Ω.fv X) t)
  | hVerum => intro N₂ N₃ R Ω _; simp
  | hFalsum => intro N₂ N₃ R Ω _; simp
  | hAnd φ ψ ihφ ihψ => intro N₂ N₃ R Ω hR; simp [ihφ N₂ N₃ R Ω hR, ihψ N₂ N₃ R Ω hR]
  | hOr φ ψ ihφ ihψ => intro N₂ N₃ R Ω hR; simp [ihφ N₂ N₃ R Ω hR, ihψ N₂ N₃ R Ω hR]
  | hAll₁ φ ih => intro N₂ N₃ R Ω hR; simp [ih N₂ N₃ R Ω hR]
  | hExs₁ φ ih => intro N₂ N₃ R Ω hR; simp [ih N₂ N₃ R Ω hR]
  | hAll₂ φ ih =>
      intro N₂ N₃ R Ω hR
      simp only [evApp_all₂, SecondOrder.Rew.app_all₁, SecondOrder.Rew.q_comp_eq]
      exact congrArg (fun χ => ∀² χ) (ih (N₂ + 1) (N₃ + 1) R.q Ω.q hR.q)
  | hExs₂ φ ih =>
      intro N₂ N₃ R Ω hR
      simp only [evApp_exs₂, SecondOrder.Rew.app_exs₁, SecondOrder.Rew.q_comp_eq]
      exact congrArg (fun χ => ∃² χ) (ih (N₂ + 1) (N₃ + 1) R.q Ω.q hR.q)

/-- The bookkeeping identity behind `inst₂_rename`: a renaming commutes with a
set substitution. -/
theorem comp_subst₂_eq (Ω : SecondOrder.Rew ℒₒᵣ ℕ 0 ℕ 0 ℕ)
    (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    Ω.comp (SecondOrder.Rew.subst ![ψ]) = (SecondOrder.Rew.subst ![Ω.app ψ]).comp Ω.q := by
  ext X
  · cases X using Fin.cases with
    | zero => simp
    | succ X => exact X.elim0
  · simp only [SecondOrder.Rew.comp_fv, SecondOrder.Rew.subst_fv, SecondOrder.Rew.app_fvar,
      SecondOrder.Rew.q_fv, SecondOrder.Rew.bmap_app_eq, subst_bRight_succ,
      SecondOrder.Rew.app_id, subst_bvar_self]

/-! ### The atomic axioms

The true closed arithmetic literals of `ℒₒᵣ`, in **evaluated** form: every
argument is already a numeral.  That extra clause is what makes the axioms
fixed points of the substitution families of `EvProvider.lean` — a set atom
never occurs in one, and `ev₂` cannot move what is already normal. -/

/-- `φ` is a first-order literal with closed arguments.  Set atoms are excluded
by the shape: `rel`/`nrel` carry a relation symbol of `ℒₒᵣ`, never a set
variable. -/
def IsArithLit₂ (φ : Proposition ℒₒᵣ) : Prop :=
  ∃ (k : ℕ) (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.SyntacticTerm ℒₒᵣ),
      (φ = Semiformula.rel r v ∨ φ = Semiformula.nrel r v) ∧ ∀ i, (v i).freeVariables = ∅

theorem isArithLit₂_rel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.SyntacticTerm ℒₒᵣ) (hv : ∀ i, (v i).freeVariables = ∅) :
    IsArithLit₂ (Semiformula.rel r v) := ⟨k, r, v, Or.inl rfl, hv⟩

theorem isArithLit₂_nrel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.SyntacticTerm ℒₒᵣ) (hv : ∀ i, (v i).freeVariables = ∅) :
    IsArithLit₂ (Semiformula.nrel r v) := ⟨k, r, v, Or.inr rfl, hv⟩

theorem isArithLit₂_neg {φ : Proposition ℒₒᵣ} (h : IsArithLit₂ φ) : IsArithLit₂ (∼φ) := by
  obtain ⟨k, r, v, (rfl | rfl), hcl⟩ := h
  · exact ⟨k, r, v, Or.inr rfl, hcl⟩
  · exact ⟨k, r, v, Or.inl rfl, hcl⟩

theorem isArithLit₂_ev₂ {φ : Proposition ℒₒᵣ} (h : IsArithLit₂ φ) : IsArithLit₂ (ev₂ φ) := by
  obtain ⟨k, r, v, (rfl | rfl), hcl⟩ := h
  · exact ⟨k, r, fun i => evT (v i), Or.inl rfl,
      fun i => by rw [freeVariables_evT]; exact hcl i⟩
  · exact ⟨k, r, fun i => evT (v i), Or.inr rfl,
      fun i => by rw [freeVariables_evT]; exact hcl i⟩

/-- Truth in the full ω-model, with every set variable read as `∅` and every
number variable as `0`.  For the closed first-order literals the axiom set is
built from, neither choice is visible. -/
def TrueN₂ (φ : Proposition ℒₒᵣ) : Prop :=
  φ.Eval (Set.univ : Set (Set ℕ)) (fun _ => (∅ : Set ℕ)) (fun _ => 0) ![] ![]

@[simp] theorem trueN₂_neg (φ : Proposition ℒₒᵣ) : TrueN₂ (∼φ) ↔ ¬TrueN₂ φ := by
  simp [TrueN₂]

theorem trueN₂_ev₂ (φ : Proposition ℒₒᵣ) : TrueN₂ (ev₂ φ) ↔ TrueN₂ φ :=
  eval_ev₂ _ _ _ φ ![] ![]

/-- **The atomic axioms of `ACA_∞` under the evaluating instantiation**: the
closed true arithmetic literals, in normal form. -/
def trueArithLits₂ : Literals₂ ℒₒᵣ where
  T φ := IsArithLit₂ φ ∧ TrueN₂ φ ∧ ev₂ φ = φ
  literal := by
    rintro φ ⟨⟨k, r, v, hv, -⟩, -, -⟩
    exact ⟨k, r, v, hv⟩
  consistent := by
    rintro φ ⟨-, ht, -⟩ ⟨-, hf, -⟩
    exact (trueN₂_neg φ).mp hf ht

@[simp] theorem trueArithLits₂_T (φ : Proposition ℒₒᵣ) :
    trueArithLits₂.T φ ↔ IsArithLit₂ φ ∧ TrueN₂ φ ∧ ev₂ φ = φ := Iff.rfl

/-- **Every true closed literal becomes an axiom once evaluated.** -/
theorem trueArithLits₂_ev₂ {φ : Proposition ℒₒᵣ} (h : IsArithLit₂ φ) (ht : TrueN₂ φ) :
    trueArithLits₂.T (ev₂ φ) :=
  ⟨isArithLit₂_ev₂ h, (trueN₂_ev₂ φ).mpr ht, ev₂_idem φ⟩

/-- Every axiom is a fixed point of `ev₂`. -/
theorem trueArithLits₂_fixed {φ : Proposition ℒₒᵣ} (h : trueArithLits₂.T φ) : ev₂ φ = φ := h.2.2

/-- …hence the axiom set is closed under `ev₂`. -/
theorem trueArithLits₂_closed {φ : Proposition ℒₒᵣ} (h : trueArithLits₂.T φ) :
    trueArithLits₂.T (ev₂ φ) := by
  rw [h.2.2]; exact h

/-! ### The evaluating instantiation -/

/-- **Substitute the numeral, then evaluate the ground terms**; and for a set
quantifier, substitute the witness, normalising exactly the instances it
creates. -/
def evInst₂ : Instantiation₂ ℒₒᵣ where
  num m := numAt m
  nf := ev₂
  nf_neg φ := ev₂_neg φ
  rank_nf φ := rank_ev₂ φ
  nf_rename f φ := ev₂_rename f φ
  inst₂ φ ψ := evApp (SecondOrder.Rew.subst ![ψ]) φ
  inst₂_neg φ ψ := evApp_neg φ 0 (SecondOrder.Rew.subst ![ψ])
  rank_inst₂ φ ψ := rank_evApp φ 0 (SecondOrder.Rew.subst ![ψ])
  inst₂_rename f φ ψ := by
    rw [evApp_atomRew_comp φ 0 0 (SecondOrder.Rew.rewrite f) (SecondOrder.Rew.subst ![ψ])
        (atomRew_rewrite f),
      evApp_comp_atomRew φ 1 0 (SecondOrder.Rew.subst ![(SecondOrder.Rew.rewrite f).app ψ])
        (SecondOrder.Rew.rewrite f) (atomRew_rewrite f),
      comp_subst₂_eq (SecondOrder.Rew.rewrite f) ψ, SecondOrder.Rew.q_rewrite]

@[simp] theorem evInst₂_num (m : ℕ) : evInst₂.num m = numAt m := rfl

@[simp] theorem evInst₂_nf (φ : Proposition ℒₒᵣ) : evInst₂.nf φ = ev₂ φ := rfl

theorem evInst₂_inst (φ : Semiproposition ℒₒᵣ 0 1) (m : ℕ) :
    evInst₂.inst φ m = ev₂ (φ/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)]) := rfl

/-- The instance of an **evaluated** body is the evaluated instance. -/
theorem evInst₂_inst_ev (φ : Semiproposition ℒₒᵣ 0 1) (m : ℕ) :
    evInst₂.inst (ev₂ φ) m = ev₂ (φ/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)]) := by
  rw [evInst₂_inst]
  exact ev₂_rew_ev₂ φ 0 (FirstOrder.Rew.subst ![_])

theorem evInst₂_inst₂ (φ : Semiproposition ℒₒᵣ 1 0) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    evInst₂.inst₂ φ ψ = evApp (SecondOrder.Rew.subst ![ψ]) φ := rfl

/-- **The law the replay of a finitary `exs₂` needs.**  The `(∃₂)` instance of
an **evaluated** body is the evaluated plain instance: `evApp` normalises what
it creates, and `ev₂ χ` has already normalised the rest. -/
theorem evInst₂_inst₂_ev (φ : Semiproposition ℒₒᵣ 1 0) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    evInst₂.inst₂ (ev₂ φ) ψ = ev₂ (φ/⟦ψ⟧) :=
  evApp_ev₂ φ 0 (SecondOrder.Rew.subst ![ψ])

/-- Normalising an `(∃₂)` instance is normalising the plain instance. -/
theorem ev₂_evInst₂_inst₂ (φ : Semiproposition ℒₒᵣ 1 0) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    ev₂ (evInst₂.inst₂ φ ψ) = ev₂ (φ/⟦ψ⟧) :=
  ev₂_evApp φ 0 (SecondOrder.Rew.subst ![ψ])

/-- An `(∃₂)` instance is already in normal form as soon as the body is. -/
theorem evInst₂_inst₂_ev_fixed (φ : Semiproposition ℒₒᵣ 1 0)
    (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    ev₂ (evInst₂.inst₂ (ev₂ φ) ψ) = evInst₂.inst₂ (ev₂ φ) ψ := by
  rw [evInst₂_inst₂_ev, ev₂_idem]

/-- The instance produced by an arbitrary-term `∃¹` of the finitary calculus is
the numeral instance of the evaluated body. -/
theorem evInst₂_inst_of_ground (φ : Semiproposition ℒₒᵣ 0 1)
    {t : FirstOrder.SyntacticTerm ℒₒᵣ} (ht : Ground t) :
    evInst₂.inst (ev₂ φ) (evTerm t) = ev₂ (φ/[t]) := by
  rw [evInst₂_inst_ev]
  exact (ev₂_subst_ground φ ht).symm

end OrdinalAnalysis.ACAOmega
