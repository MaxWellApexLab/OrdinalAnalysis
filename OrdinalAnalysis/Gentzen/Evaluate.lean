/-
  Closed-term evaluation: replacing a ground term by the numeral of its value.

  The ω-calculus of `Omega/Calculus.lean` quantifies over *numerals*: its `exs`
  rule admits `(∃¹ φ) :: Γ` only from a premise `inst φ n :: Γ`, and its
  `omegaRule` produces premises `inst φ n :: Γ`, one for each `n : ℕ`.
  Foundation's finitary `LK` (Basic/Calculus.lean:55-63) is not so disciplined:
  its `exs` rule takes an *arbitrary* term `t` as the witness.  Replaying an `LK`
  derivation inside the ω-calculus therefore needs a map that turns `φ/[t]` into
  the numeral instance — the evaluator of this file.

  Three things about the shape.

  * The value of a term is taken in `stdLX P₀` for one fixed reading `P₀` of `X`.
    That is not a choice: `X` contributes no *function* symbols to `LX`
    (`XLang.Func k = PEmpty`, Setup.lean), so `val_stdLX_congr` says term values
    do not see `P` at all.  `val_ground` upgrades this to independence of the
    two environments as well, for the terms that matter.

  * "Closed" is replaced by **ground** — no free variables *and* no bound
    variables (`Semiterm.bv t = ∅ ∧ t.freeVariables = ∅`).  At level `0` the two
    notions agree (`ground_of_closed`), but `ev` must also act underneath a
    quantifier, where `#0` is present and closedness alone would be the wrong
    test.  Ground is decidable, which is what lets `evT` be an honest `if` rather
    than a classical one, and hence lets `simp` compute with it.

  * `evT` is **deep**: a ground term becomes the numeral of its value, and a
    non-ground compound term is rebuilt from its evaluated arguments, so that a
    ground subterm sitting inside a non-ground one is normalised too
    (`&y + (2̄ + 3̄) ↦ &y + 5̄`).  Only the variables are left alone.

  ## Why the raw substitution law is false, and what replaces it

  The naive law `ev (φ/[t]) = (ev φ)/[n̄]`, with `n` the value of the ground term
  `t`, is **false for every evaluator whatsoever** — the obstacle is the
  statement, not the definition.  Take `φ := R(#0 + 1̄) : Semiformula LX ℕ 1` and
  a ground `t` of value `m`.  Then `φ/[t] = R(t + 1̄)` is ground, so any evaluator
  worth the name sends it to `R((m+1)‾)`; while `ev φ` must be some `R(s)` with
  `s/[m̄] = (m+1)‾` **for every `m`** — and no single term does that, since the
  numeral of `m + 1` is not a term-forming operation applied to the numeral of
  `m`.  (The previous, shallow `evT` avoided the issue by restricting to *flat*
  formulas, whose atoms carry no compound term in a bound variable.  That
  restriction is gone.)

  The ω-calculus instead instantiates its quantifier rules by substitution
  **followed by normalisation**, `inst φ n := ev (φ/[n̄])`.  What has to hold is
  then the *normalised* law

      ev (φ/[t]) = ev ((ev φ)/[n̄]),                                  `ev_subst_key`

  and that is a theorem, unconditionally, for the deep evaluator.  It is one line
  from two facts, each of independent use:

  * **congruence**, `ev_rew_ev : ev (ω ▹ ev φ) = ev (ω ▹ φ)` — normalising before
    a rewriting does not change the normal form afterwards;
  * **value dependence**, `ev_subst_ground : ev (φ/[t]) = ev (φ/[n̄])` — a
    substituted ground term is seen only through its value.

  Contents.

    `Ground`, `ground_of_closed`      ground terms, and closed = ground at level 0
    `evTerm`, `val_ground`            the value of a ground term, seen by nothing
    `numAt`, `evTerm_numAt`           numerals at every level; `n̄` denotes `n`
    `evT`                             the deep term evaluator
    `val_evT`, `freeVariables_evT`    what `evT` leaves alone
    `ev`                              the formula evaluator
    `eval_ev`                         **LAW 2** — `ev` preserves truth, unconditionally
    `evT_rew_evT`, `ev_rew_ev`        **congruence**
    `RewEq`, `evT_congr`, `ev_rew_congr`
                                      two rewritings that agree up to value
    `ev_subst_ground`, `ev_substs_ground`, `ev_rewrite_ground`
    `ev_subst_key`                    **the normalised substitution law**
    `eval_subst_ground`               the semantic form of the same
    `ev_idem`, `complexity_ev`, `freeVariables_ev`, `ev_Xat`
    `isArithLit_ev`, `trueN_ev`, `trueArithLits_ev`
-/
import OrdinalAnalysis.Gentzen.StandardLX

set_option autoImplicit false
set_option warn.classDefReducibility false

namespace OrdinalAnalysis

namespace Gentzen

namespace Evaluate

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.StandardLX

/-! ### Ground terms

A term is ground when it is built from function symbols alone.  Both halves are
needed: `freeVariables = ∅` alone is the right notion only at level `0`, and the
evaluator has to act underneath quantifiers. -/

/-- `t` contains neither a bound nor a free variable. -/
def Ground {n : ℕ} (t : Semiterm LX ℕ n) : Prop :=
  t.bv = ∅ ∧ t.freeVariables = ∅

instance instDecidableGround {n : ℕ} (t : Semiterm LX ℕ n) : Decidable (Ground t) := by
  unfold Ground
  infer_instance

theorem not_ground_bvar {n : ℕ} (x : Fin n) : ¬Ground (#x : Semiterm LX ℕ n) := by
  rintro ⟨hb, -⟩
  rw [Semiterm.bv_bvar] at hb
  exact absurd hb (Finset.singleton_ne_empty x)

theorem not_ground_fvar {n : ℕ} (x : ℕ) : ¬Ground (&x : Semiterm LX ℕ n) := by
  rintro ⟨-, hf⟩
  rw [Semiterm.freeVariables_fvar] at hf
  exact absurd hf (Finset.singleton_ne_empty x)

/-- Groundness is componentwise: `bv` and `freeVariables` of a compound term are
the unions of those of its arguments. -/
theorem ground_func_iff {n k : ℕ} (fn : LX.Func k) (v : Fin k → Semiterm LX ℕ n) :
    Ground (Semiterm.func fn v) ↔ ∀ i, Ground (v i) := by
  simp only [Ground, Semiterm.bv_func, Semiterm.freeVariables_func,
    Finset.eq_empty_iff_forall_notMem, Finset.mem_biUnion, Finset.mem_univ, true_and,
    not_exists]
  constructor
  · rintro ⟨hb, hf⟩ i
    exact ⟨fun x => hb x i, fun x => hf x i⟩
  · intro h
    exact ⟨fun x i => (h i).1 x, fun x i => (h i).2 x⟩

/-- **At level `0`, closed and ground agree.**  The bound variables of a
`SyntacticTerm` are indexed by `Fin 0`, so there are none to exclude. -/
theorem ground_of_closed {t : SyntacticTerm LX} (h : t.freeVariables = ∅) : Ground t :=
  ⟨Finset.eq_empty_iff_forall_notMem.mpr fun x => x.elim0, h⟩

theorem freeVariables_of_ground {n : ℕ} {t : Semiterm LX ℕ n} (h : Ground t) :
    t.freeVariables = ∅ := h.2

/-! ### The value of a ground term -/

/-- **The value of a closed term in the standard structure.**  The reading of
`X` is fixed to the empty one and the assignment to the constant zero; for the
ground terms this file evaluates, neither choice is visible — that is
`val_ground`.  `X` contributes no function symbols to `LX`, so the reading of
`X` is invisible to *every* term (`val_stdLX_congr`). -/
def evTerm {n : ℕ} (t : Semiterm LX ℕ n) : ℕ :=
  Semiterm.val (s := stdLX fun _ => False) (fun _ => 0) (fun _ => 0) t

/-- A ground term has the same value in every `stdLX P` and under every pair of
environments.  Proved by induction, not by `Semiterm.val_eq_of_funEqOn`, because
independence of the *bound*-variable environment is also needed. -/
theorem val_ground_congr (P Q : ℕ → Prop) {n : ℕ} (e e' : Fin n → ℕ) (f f' : ℕ → ℕ) :
    ∀ {t : Semiterm LX ℕ n}, Ground t →
      Semiterm.val (s := stdLX P) e f t = Semiterm.val (s := stdLX Q) e' f' t := by
  intro t
  induction t with
  | bvar x => exact fun h => absurd h (not_ground_bvar x)
  | fvar x => exact fun h => absurd h (not_ground_fvar x)
  | func fn v ih =>
      intro h
      have hv := (ground_func_iff fn v).mp h
      have key : (fun i => Semiterm.val (s := stdLX P) e f (v i))
          = (fun i => Semiterm.val (s := stdLX Q) e' f' (v i)) := funext fun i => ih i (hv i)
      simp only [Semiterm.val_func, Function.comp_def]
      rw [key]
      exact stdLX_func P Q fn _

/-- The value of a ground term *is* `evTerm`, in every standard structure. -/
theorem val_ground (P : ℕ → Prop) {n : ℕ} {t : Semiterm LX ℕ n} (h : Ground t)
    (e : Fin n → ℕ) (f : ℕ → ℕ) :
    Semiterm.val (s := stdLX P) e f t = evTerm t :=
  val_ground_congr P (fun _ => False) e (fun _ => 0) f (fun _ => 0) h

/-- Groundness survives every rewriting: a rewriting only touches variables, and
a ground term has none. -/
theorem ground_rew {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) :
    ∀ {t : Semiterm LX ℕ n₁}, Ground t → Ground (ω t) := by
  intro t
  induction t with
  | bvar x => exact fun h => absurd h (not_ground_bvar x)
  | fvar x => exact fun h => absurd h (not_ground_fvar x)
  | func fn v ih =>
      intro h
      have hv := (ground_func_iff fn v).mp h
      rw [ω.func' fn v]
      exact (ground_func_iff fn _).mpr fun i => ih i (hv i)

/-- **A rewriting fixes a ground term.**  A rewriting acts on the variables and
nothing else, and a ground term has none, so it is not merely the *groundness*
that survives but the term itself.  The two levels have to agree for the
statement to typecheck at all; across levels, `ground_rew` together with
`evTerm_rew` says everything this says. -/
theorem rew_of_ground {n : ℕ} (ω : Rew LX ℕ n ℕ n) :
    ∀ {t : Semiterm LX ℕ n}, Ground t → ω t = t := by
  intro t
  induction t with
  | bvar x => exact fun h => absurd h (not_ground_bvar x)
  | fvar x => exact fun h => absurd h (not_ground_fvar x)
  | func fn v ih =>
      intro h
      have hv := (ground_func_iff fn v).mp h
      rw [ω.func' fn v]
      exact congrArg (Semiterm.func fn) (funext fun i => ih i (hv i))

/-- …and so does its value. -/
theorem evTerm_rew {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) {t : Semiterm LX ℕ n₁} (h : Ground t) :
    evTerm (ω t) = evTerm t := by
  unfold evTerm
  rw [Semiterm.val_rew]
  exact val_ground_congr _ _ _ _ _ _ h

/-! ### Numerals at every level -/

/-- The numeral `m̄`, as a term with `n` bound variables.  `numAt (n := 0)` is
`StandardLX.numLX` on the nose. -/
def numAt {n : ℕ} (m : ℕ) : Semiterm LX ℕ n := Semiterm.numeral m

@[simp] theorem numAt_zero (m : ℕ) : (numAt m : SyntacticTerm LX) = numLX m := rfl

/-- A numeral is a constant, so no rewriting moves it. -/
@[simp] theorem rew_numAt {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) (m : ℕ) :
    ω (numAt m : Semiterm LX ℕ n₁) = numAt m := by
  simp [numAt]

/-- A term that comes from a *sentence* term by embedding and substituting the
empty vector is ground.  This is the shape `Semiterm.Operator.operator` gives a
constant, and it is how numerals are seen to be ground without an induction on
the numeral. -/
theorem ground_subst_emb {n : ℕ} :
    ∀ t : Semiterm LX Empty 0,
      Ground ((Rew.subst (![] : Fin 0 → Semiterm LX ℕ n)) (Rew.emb t : Semiterm LX ℕ 0)) := by
  intro t
  induction t with
  | bvar x => exact x.elim0
  | fvar x => exact x.elim
  | func fn v ih =>
      have h1 : (Rew.emb (Semiterm.func fn v) : Semiterm LX ℕ 0)
          = Semiterm.func fn fun i => (Rew.emb (v i) : Semiterm LX ℕ 0) :=
        Rew.func' _ fn v
      have h2 : (Rew.subst (![] : Fin 0 → Semiterm LX ℕ n))
            (Semiterm.func fn fun i => (Rew.emb (v i) : Semiterm LX ℕ 0))
          = Semiterm.func fn fun i =>
              (Rew.subst (![] : Fin 0 → Semiterm LX ℕ n)) (Rew.emb (v i)) :=
        Rew.func' _ fn _
      rw [h1, h2]
      exact (ground_func_iff fn _).mpr ih

@[simp] theorem ground_numAt {n : ℕ} (m : ℕ) : Ground (numAt m : Semiterm LX ℕ n) :=
  ground_subst_emb (Semiterm.Operator.numeral LX m).term

@[simp] theorem ground_numLX (m : ℕ) : Ground (numLX m) := ground_numAt m

/-- **`m̄` denotes `m`**, at every level.  `StandardLX.val_numLX` is the case
`n = 0`; the proof is the same, and possible at all levels only because
`Gentzen.lMap_toLX_numeral` (Code.lean:296) is stated for general `ξ` and `n`. -/
@[simp] theorem evTerm_numAt {n : ℕ} (m : ℕ) : evTerm (numAt m : Semiterm LX ℕ n) = m := by
  have h : (numAt m : Semiterm LX ℕ n) = Semiterm.lMap toLX ((m : ℕ) : Semiterm ℒₒᵣ ℕ n) :=
    (lMap_toLX_numeral m).symm
  unfold evTerm
  rw [h, val_lMap_toLX]
  simp

@[simp] theorem evTerm_numLX (m : ℕ) : evTerm (numLX m) = m := evTerm_numAt m

/-- The value of a compound term, componentwise. -/
theorem evTerm_func {n k : ℕ} (f : LX.Func k) (v : Fin k → Semiterm LX ℕ n) :
    evTerm (Semiterm.func f v)
      = (stdLX fun _ => False).func f fun i => evTerm (v i) := rfl

/-! ### The term evaluator

`evT` is **deep**.  A ground term is replaced by the numeral of its value; a
non-ground compound term is rebuilt from its evaluated arguments, so a ground
subterm inside a non-ground term is normalised as well.  Only variables are
returned untouched, and they have to be: nothing else could be. -/

/-- **The term evaluator**: ground ↦ the numeral of its value, and otherwise
evaluate the arguments and rebuild. -/
def evT {n : ℕ} : Semiterm LX ℕ n → Semiterm LX ℕ n
  | #x => #x
  | &x => &x
  | Semiterm.func f v =>
      if Ground (Semiterm.func f v) then numAt (evTerm (Semiterm.func f v))
      else Semiterm.func f fun i => evT (v i)

@[simp] theorem evT_bvar {n : ℕ} (x : Fin n) : evT (#x : Semiterm LX ℕ n) = #x := rfl

@[simp] theorem evT_fvar {n : ℕ} (x : ℕ) : evT (&x : Semiterm LX ℕ n) = &x := rfl

theorem evT_func {n k : ℕ} (f : LX.Func k) (v : Fin k → Semiterm LX ℕ n) :
    evT (Semiterm.func f v)
      = if Ground (Semiterm.func f v) then numAt (evTerm (Semiterm.func f v))
        else Semiterm.func f fun i => evT (v i) := rfl

/-- The defining clause on a ground term. -/
theorem evT_of_ground {n : ℕ} {t : Semiterm LX ℕ n} (h : Ground t) :
    evT t = numAt (evTerm t) := by
  cases t with
  | bvar x => exact absurd h (not_ground_bvar x)
  | fvar x => exact absurd h (not_ground_fvar x)
  | func f v => rw [evT_func]; exact if_pos h

/-- The defining clause on a non-ground compound term. -/
theorem evT_func_of_not_ground {n k : ℕ} (f : LX.Func k) (v : Fin k → Semiterm LX ℕ n)
    (h : ¬Ground (Semiterm.func f v)) :
    evT (Semiterm.func f v) = Semiterm.func f fun i => evT (v i) := by
  rw [evT_func]; exact if_neg h

@[simp] theorem evT_numAt {n : ℕ} (m : ℕ) : evT (numAt m : Semiterm LX ℕ n) = numAt m := by
  rw [evT_of_ground (ground_numAt m), evTerm_numAt]

@[simp] theorem evT_numLX (m : ℕ) : evT (numLX m) = numLX m := evT_numAt m

/-- **`evT` neither creates nor destroys groundness.**  One direction is the
first clause of the definition; the other says the second clause cannot turn a
non-ground term into a ground one, because it keeps the variables where they
are. -/
@[simp] theorem ground_evT_iff {n : ℕ} {t : Semiterm LX ℕ n} : Ground (evT t) ↔ Ground t := by
  induction t with
  | bvar x => rw [evT_bvar]
  | fvar x => rw [evT_fvar]
  | func f v ih =>
      by_cases h : Ground (Semiterm.func f v)
      · exact iff_of_true (by rw [evT_of_ground h]; exact ground_numAt _) h
      · rw [evT_func_of_not_ground f v h, ground_func_iff, ground_func_iff]
        exact forall_congr' fun i => ih i

theorem ground_evT {n : ℕ} {t : Semiterm LX ℕ n} (h : Ground t) : Ground (evT t) :=
  ground_evT_iff.mpr h

@[simp] theorem evT_idem {n : ℕ} (t : Semiterm LX ℕ n) : evT (evT t) = evT t := by
  induction t with
  | bvar x => rw [evT_bvar, evT_bvar]
  | fvar x => rw [evT_fvar, evT_fvar]
  | func f v ih =>
      by_cases h : Ground (Semiterm.func f v)
      · rw [evT_of_ground h, evT_numAt]
      · have hn : ¬Ground (Semiterm.func f fun i => evT (v i)) := by
          rw [ground_func_iff]
          intro hc
          exact h ((ground_func_iff f v).mpr fun i => ground_evT_iff.mp (hc i))
        rw [evT_func_of_not_ground f v h, evT_func_of_not_ground f _ hn]
        exact congrArg (Semiterm.func f) (funext fun i => ih i)

/-- **`evT` does not change what a term denotes**, under *every* environment —
the term half of LAW 2.  This is what makes the deep evaluator harmless: the
numerals it introduces denote exactly the subterms they replace. -/
theorem val_evT (P : ℕ → Prop) {n : ℕ} (t : Semiterm LX ℕ n) (e : Fin n → ℕ) (f : ℕ → ℕ) :
    Semiterm.val (s := stdLX P) e f (evT t) = Semiterm.val (s := stdLX P) e f t := by
  induction t with
  | bvar x => rw [evT_bvar]
  | fvar x => rw [evT_fvar]
  | func fn v ih =>
      by_cases h : Ground (Semiterm.func fn v)
      · rw [evT_of_ground h, val_ground P (ground_numAt _) e f, evTerm_numAt, val_ground P h e f]
      · rw [evT_func_of_not_ground fn v h]
        simp only [Semiterm.val_func, Function.comp_def]
        exact congrArg ((stdLX P).func fn) (funext fun i => ih i)

theorem evTerm_evT {n : ℕ} (t : Semiterm LX ℕ n) : evTerm (evT t) = evTerm t :=
  val_evT _ t _ _

/-- **`evT` does not move the free variables.**  It removes a ground subterm,
which had none, and leaves every variable exactly where it was. -/
@[simp] theorem freeVariables_evT {n : ℕ} (t : Semiterm LX ℕ n) :
    (evT t).freeVariables = t.freeVariables := by
  induction t with
  | bvar x => rw [evT_bvar]
  | fvar x => rw [evT_fvar]
  | func fn v ih =>
      by_cases h : Ground (Semiterm.func fn v)
      · rw [evT_of_ground h, (ground_numAt (n := n) (evTerm (Semiterm.func fn v))).2, h.2]
      · rw [evT_func_of_not_ground fn v h, Semiterm.freeVariables_func,
          Semiterm.freeVariables_func]
        exact congrArg (Finset.biUnion Finset.univ) (funext fun i => ih i)

/-! ### The formula evaluator -/

/-- **The formula evaluator**: every argument of every atom is evaluated by
`evT`; the connectives, the quantifiers and the relation symbols are untouched. -/
def ev : {n : ℕ} → Semiformula LX ℕ n → Semiformula LX ℕ n
  | _, Semiformula.verum => Semiformula.verum
  | _, Semiformula.falsum => Semiformula.falsum
  | _, Semiformula.rel r v => Semiformula.rel r fun i => evT (v i)
  | _, Semiformula.nrel r v => Semiformula.nrel r fun i => evT (v i)
  | _, Semiformula.and φ ψ => Semiformula.and (ev φ) (ev ψ)
  | _, Semiformula.or φ ψ => Semiformula.or (ev φ) (ev ψ)
  | _, Semiformula.all φ => Semiformula.all (ev φ)
  | _, Semiformula.exs φ => Semiformula.exs (ev φ)

@[simp] theorem ev_verum {n : ℕ} : ev (⊤ : Semiformula LX ℕ n) = ⊤ := rfl

@[simp] theorem ev_falsum {n : ℕ} : ev (⊥ : Semiformula LX ℕ n) = ⊥ := rfl

@[simp] theorem ev_rel {n k : ℕ} (r : LX.Rel k) (v : Fin k → Semiterm LX ℕ n) :
    ev (Semiformula.rel r v) = Semiformula.rel r fun i => evT (v i) := rfl

@[simp] theorem ev_nrel {n k : ℕ} (r : LX.Rel k) (v : Fin k → Semiterm LX ℕ n) :
    ev (Semiformula.nrel r v) = Semiformula.nrel r fun i => evT (v i) := rfl

@[simp] theorem ev_and {n : ℕ} (φ ψ : Semiformula LX ℕ n) : ev (φ ⋏ ψ) = ev φ ⋏ ev ψ := rfl

@[simp] theorem ev_or {n : ℕ} (φ ψ : Semiformula LX ℕ n) : ev (φ ⋎ ψ) = ev φ ⋎ ev ψ := rfl

@[simp] theorem ev_all {n : ℕ} (φ : Semiformula LX ℕ (n + 1)) : ev (∀¹ φ) = ∀¹ (ev φ) := rfl

@[simp] theorem ev_exs {n : ℕ} (φ : Semiformula LX ℕ (n + 1)) : ev (∃¹ φ) = ∃¹ (ev φ) := rfl

/-- **`ev` commutes with negation.**  De Morgan for `Semiformula.neg` swaps
`rel` with `nrel` and `∀¹` with `∃¹`, and `ev` treats the members of each pair
alike. -/
@[simp] theorem ev_neg {n : ℕ} (φ : Semiformula LX ℕ n) : ev (∼φ) = ∼(ev φ) := by
  induction φ using Semiformula.rec' <;> simp [*]

@[simp] theorem ev_imp {n : ℕ} (φ ψ : Semiformula LX ℕ n) : ev (φ 🡒 ψ) = ev φ 🡒 ev ψ := by
  simp [Semiformula.imp_eq]

/-- **`ev` is idempotent**: a formula all of whose ground subterms are already
numerals is a fixed point. -/
@[simp] theorem ev_idem {n : ℕ} (φ : Semiformula LX ℕ n) : ev (ev φ) = ev φ := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => exact congrArg (Semiformula.rel r) (funext fun i => evT_idem (v i))
  | hnrel r v => exact congrArg (Semiformula.nrel r) (funext fun i => evT_idem (v i))
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

/-- **`ev` does not change the logical shape of a formula.**  It rewrites only
inside atoms, so the quantifier/connective skeleton — and hence the cut rank of
a derivation that mentions it — is preserved. -/
@[simp] theorem complexity_ev {n : ℕ} (φ : Semiformula LX ℕ n) :
    (ev φ).complexity = φ.complexity := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => rfl
  | hnrel r v => rfl
  | hand φ ψ ihφ ihψ =>
      rw [ev_and, Semiformula.complexity_and, Semiformula.complexity_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
      rw [ev_or, Semiformula.complexity_or, Semiformula.complexity_or, ihφ, ihψ]
  | hall φ ih => rw [ev_all, Semiformula.complexity_all, Semiformula.complexity_all, ih]
  | hexs φ ih => rw [ev_exs, Semiformula.complexity_exs, Semiformula.complexity_exs, ih]

/-- An atom whose arguments are numerals is a fixed point of `ev`.  With the
connective and quantifier clauses, which are `rfl`, this settles every member of
the class `C` of the boundedness lemma. -/
@[simp] theorem ev_rel_numAt {n k : ℕ} (r : LX.Rel k) (w : Fin k → ℕ) :
    ev (Semiformula.rel r fun i => (numAt (w i) : Semiterm LX ℕ n))
      = Semiformula.rel r fun i => (numAt (w i) : Semiterm LX ℕ n) :=
  congrArg (Semiformula.rel r) (funext fun i => evT_numAt (w i))

@[simp] theorem ev_nrel_numAt {n k : ℕ} (r : LX.Rel k) (w : Fin k → ℕ) :
    ev (Semiformula.nrel r fun i => (numAt (w i) : Semiterm LX ℕ n))
      = Semiformula.nrel r fun i => (numAt (w i) : Semiterm LX ℕ n) :=
  congrArg (Semiformula.nrel r) (funext fun i => evT_numAt (w i))

/-- **`ev` does not move the free variables** — it only ever replaces a ground
subterm, which has none, by a numeral, which has none either. -/
@[simp] theorem freeVariables_ev {n : ℕ} (φ : Semiformula LX ℕ n) :
    (ev φ).freeVariables = φ.freeVariables := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
      rw [ev_rel, Semiformula.freeVariables_rel, Semiformula.freeVariables_rel]
      exact congrArg (Finset.biUnion Finset.univ) (funext fun i => freeVariables_evT (v i))
  | hnrel r v =>
      rw [ev_nrel, Semiformula.freeVariables_nrel, Semiformula.freeVariables_nrel]
      exact congrArg (Finset.biUnion Finset.univ) (funext fun i => freeVariables_evT (v i))
  | hand φ ψ ihφ ihψ =>
      rw [ev_and, Semiformula.freeVariables_and, Semiformula.freeVariables_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
      rw [ev_or, Semiformula.freeVariables_or, Semiformula.freeVariables_or, ihφ, ihψ]
  | hall φ ih => exact ih
  | hexs φ ih => exact ih

/-! ### LAW 2: truth is preserved

Unconditional: every level, every reading of `X`, every environment.  A numeral
denotes its value, so replacing a ground subterm by the numeral of its value
cannot change the value of an atom. -/

/-- **LAW 2.**  `ev` preserves truth in every standard model. -/
theorem eval_ev (P : ℕ → Prop) (f : ℕ → ℕ) :
    ∀ {n : ℕ} (φ : Semiformula LX ℕ n) (e : Fin n → ℕ),
      (Semiformula.Eval (s := stdLX P) e f (ev φ) ↔ Semiformula.Eval (s := stdLX P) e f φ) := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro e; simp
  | hfalsum => intro e; simp
  | hrel r v =>
      intro e
      simp only [ev_rel, Semiformula.eval_rel, Function.comp_def]
      exact Iff.of_eq (congrArg ((stdLX P).rel r) (funext fun i => val_evT P (v i) e f))
  | hnrel r v =>
      intro e
      simp only [ev_nrel, Semiformula.eval_nrel, Function.comp_def]
      exact not_congr (Iff.of_eq (congrArg ((stdLX P).rel r) (funext fun i => val_evT P (v i) e f)))
  | hand φ ψ ihφ ihψ => intro e; simp only [ev_and, LogicalConnective.HomClass.map_and]
                        exact and_congr (ihφ e) (ihψ e)
  | hor φ ψ ihφ ihψ => intro e; simp only [ev_or, LogicalConnective.HomClass.map_or]
                       exact or_congr (ihφ e) (ihψ e)
  | hall φ ih =>
      intro e
      simp only [ev_all, Semiformula.eval_all]
      exact forall_congr' fun x => ih (x :> e)
  | hexs φ ih =>
      intro e
      simp only [ev_exs, Semiformula.eval_ex]
      exact exists_congr fun x => ih (x :> e)

/-- The form the ω-completeness lemma uses: a closed formula and its evaluation
are true together. -/
theorem eval_ev_zero (P : ℕ → Prop) (f : ℕ → ℕ) (φ : Proposition LX) :
    Semiformula.Eval (s := stdLX P) ![] f (ev φ) ↔ Semiformula.Eval (s := stdLX P) ![] f φ :=
  eval_ev P f φ ![]

/-! ### Congruence: normalising before a rewriting does not change the result

`evT (ω t)` and `evT (ω (evT t))` are equal for *every* rewriting `ω` and every
term `t`.  This is what the raw substitution law wanted to be and could not: the
outer `evT` on the left is what repairs the failure, because it re-normalises
the ground subterms that `ω` has just created. -/

/-- `evT` under a rewriting does not change the value, whatever the environment
— `val_evT` transported along `Semiterm.val_rew`. -/
theorem val_rew_evT (P : ℕ → Prop) {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂)
    (t : Semiterm LX ℕ n₁) (e : Fin n₂ → ℕ) (f : ℕ → ℕ) :
    Semiterm.val (s := stdLX P) e f (ω (evT t))
      = Semiterm.val (s := stdLX P) e f (ω t) := by
  rw [Semiterm.val_rew, Semiterm.val_rew]
  exact val_evT P t _ _

theorem evTerm_rew_evT {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) (t : Semiterm LX ℕ n₁) :
    evTerm (ω (evT t)) = evTerm (ω t) := by
  unfold evTerm
  exact val_rew_evT _ ω t _ _

/-- `evT` under a rewriting does not change groundness either.  Both directions
matter in `evT_rew_evT`, where the two sides have to take the same branch. -/
theorem ground_rew_evT_iff {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) (t : Semiterm LX ℕ n₁) :
    Ground (ω (evT t)) ↔ Ground (ω t) := by
  induction t with
  | bvar x => rw [evT_bvar]
  | fvar x => rw [evT_fvar]
  | func f v ih =>
      by_cases h : Ground (Semiterm.func f v)
      · exact iff_of_true (by rw [evT_of_ground h, rew_numAt]; exact ground_numAt _)
          (ground_rew ω h)
      · rw [evT_func_of_not_ground f v h, ω.func' f fun i => evT (v i), ω.func' f v,
          ground_func_iff, ground_func_iff]
        exact forall_congr' fun i => ih i

/-- **The term-level congruence.**  Evaluating, rewriting and evaluating again
is evaluating after the rewriting.  Note that this is *not* the false raw law
`evT (ω t) = ω (evT t)`: the outer `evT` on the left is essential, and is exactly
what the ω-calculus supplies by instantiating with `ev (φ/[n̄])`. -/
theorem evT_rew_evT {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) (t : Semiterm LX ℕ n₁) :
    evT (ω (evT t)) = evT (ω t) := by
  induction t with
  | bvar x => rw [evT_bvar]
  | fvar x => rw [evT_fvar]
  | func f v ih =>
      by_cases h : Ground (Semiterm.func f v)
      · rw [evT_of_ground h, rew_numAt, evT_numAt, evT_of_ground (ground_rew ω h),
          evTerm_rew ω h]
      · have hiff : Ground (Semiterm.func f fun i => ω (evT (v i)))
            ↔ Ground (Semiterm.func f fun i => ω (v i)) := by
          rw [ground_func_iff, ground_func_iff]
          exact forall_congr' fun i => ground_rew_evT_iff ω (v i)
        rw [evT_func_of_not_ground f v h, ω.func' f fun i => evT (v i), ω.func' f v]
        by_cases hg : Ground (Semiterm.func f fun i => ω (v i))
        · have hval : evTerm (Semiterm.func f fun i => ω (evT (v i)))
              = evTerm (Semiterm.func f fun i => ω (v i)) := by
            have hx := evTerm_rew_evT ω (Semiterm.func f v)
            rwa [evT_func_of_not_ground f v h, ω.func' f fun i => evT (v i),
              ω.func' f v] at hx
          rw [evT_of_ground (hiff.mpr hg), evT_of_ground hg, hval]
        · rw [evT_func_of_not_ground f _ fun hc => hg (hiff.mp hc),
            evT_func_of_not_ground f _ hg]
          exact congrArg (Semiterm.func f) (funext fun i => ih i)

/-- **The formula-level congruence.**  Normalising a formula before rewriting it
does not change the normal form of the result.  The general statement is about
an arbitrary rewriting because the quantifier case replaces `ω` by `ω.q`. -/
theorem ev_rew_ev {n₁ : ℕ} :
    ∀ (φ : Semiformula LX ℕ n₁) (n₂ : ℕ) (ω : Rew LX ℕ n₁ ℕ n₂),
      ev (ω ▹ ev φ) = ev (ω ▹ φ) := by
  intro φ
  induction φ using Semiformula.rec' with
  | hverum => intro n₂ ω; simp
  | hfalsum => intro n₂ ω; simp
  | hrel r v =>
      intro n₂ ω
      simp only [ev_rel, Semiformula.rew_rel]
      exact congrArg (Semiformula.rel r) (funext fun i => evT_rew_evT ω (v i))
  | hnrel r v =>
      intro n₂ ω
      simp only [ev_nrel, Semiformula.rew_nrel]
      exact congrArg (Semiformula.nrel r) (funext fun i => evT_rew_evT ω (v i))
  | hand φ ψ ihφ ihψ =>
      intro n₂ ω
      simp only [LogicalConnective.HomClass.map_and, ev_and, ihφ n₂ ω, ihψ n₂ ω]
  | hor φ ψ ihφ ihψ =>
      intro n₂ ω
      simp only [LogicalConnective.HomClass.map_or, ev_or, ihφ n₂ ω, ihψ n₂ ω]
  | hall φ ih =>
      intro n₂ ω
      simp only [Rewriting.app_all, ev_all, ih (n₂ + 1) ω.q]
  | hexs φ ih =>
      intro n₂ ω
      simp only [Rewriting.app_exs, ev_exs, ih (n₂ + 1) ω.q]

/-! ### Value dependence: a substituted ground term is seen only through its value

`ev` cannot tell two rewritings apart when they send each variable to terms with
the same normal form.  `evT t = evT u` is the right hypothesis rather than "both
ground with the same value" because it is *stable under rewriting*, which is what
the quantifier case of the induction needs — and it follows from congruence, so
this whole section costs nothing beyond what is already proved. -/

/-- Terms with the same normal form denote the same thing. -/
theorem val_congr_of_evT (P : ℕ → Prop) {n : ℕ} {t u : Semiterm LX ℕ n} (h : evT t = evT u)
    (e : Fin n → ℕ) (f : ℕ → ℕ) :
    Semiterm.val (s := stdLX P) e f t = Semiterm.val (s := stdLX P) e f u := by
  rw [← val_evT P t e f, ← val_evT P u e f, h]

theorem evTerm_congr_of_evT {n : ℕ} {t u : Semiterm LX ℕ n} (h : evT t = evT u) :
    evTerm t = evTerm u := val_congr_of_evT _ h _ _

/-- Having the same normal form is preserved by every rewriting.  This is
`evT_rew_evT` used twice, and it is the fact that makes `RewEq` liftable under a
binder. -/
theorem evT_rew_congr {n₁ n₂ : ℕ} (ρ : Rew LX ℕ n₁ ℕ n₂) {t u : Semiterm LX ℕ n₁}
    (h : evT t = evT u) : evT (ρ t) = evT (ρ u) := by
  rw [← evT_rew_evT ρ t, ← evT_rew_evT ρ u, h]

/-- **Two rewritings the evaluator cannot tell apart**: on every variable their
images have the same normal form.  Substituting two ground terms of equal value
is the case of interest, but the relation has to be this one to survive `Rew.q`. -/
def RewEq {n₁ n₂ : ℕ} (ω ω' : Rew LX ℕ n₁ ℕ n₂) : Prop :=
  (∀ i : Fin n₁, evT (ω #i) = evT (ω' #i)) ∧ ∀ x : ℕ, evT (ω &x) = evT (ω' &x)

/-- `RewEq` survives lifting under a binder: `Rew.q` keeps `#0` and `bShift`s
everything else, and both operations preserve normal forms. -/
theorem RewEq.q {n₁ n₂ : ℕ} {ω ω' : Rew LX ℕ n₁ ℕ n₂} (h : RewEq ω ω') :
    RewEq ω.q ω'.q := by
  constructor
  · intro i
    induction i using Fin.cases with
    | zero => rw [Rew.q_bvar_zero, Rew.q_bvar_zero]
    | succ j =>
        rw [Rew.q_bvar_succ, Rew.q_bvar_succ]
        exact evT_rew_congr Rew.bShift (h.1 j)
  · intro x
    rw [Rew.q_fvar, Rew.q_fvar]
    exact evT_rew_congr Rew.bShift (h.2 x)

/-- **The term-level value dependence.**  `RewEq` rewritings give terms with the
same normal form. -/
theorem evT_congr {n₁ n₂ : ℕ} {ω ω' : Rew LX ℕ n₁ ℕ n₂} (h : RewEq ω ω')
    (t : Semiterm LX ℕ n₁) : evT (ω t) = evT (ω' t) := by
  induction t with
  | bvar x => exact h.1 x
  | fvar x => exact h.2 x
  | func f v ih =>
      have hgi : ∀ i, (Ground (ω (v i)) ↔ Ground (ω' (v i))) := fun i => by
        have e1 : Ground (evT (ω (v i))) ↔ Ground (ω (v i)) := ground_evT_iff
        have e2 : Ground (evT (ω' (v i))) ↔ Ground (ω' (v i)) := ground_evT_iff
        rw [← e1, ← e2, ih i]
      rw [ω.func' f v, ω'.func' f v]
      by_cases hg : Ground (Semiterm.func f fun i => ω (v i))
      · have hg' : Ground (Semiterm.func f fun i => ω' (v i)) :=
          (ground_func_iff f _).mpr fun i => (hgi i).mp ((ground_func_iff f _).mp hg i)
        rw [evT_of_ground hg, evT_of_ground hg', evTerm_func, evTerm_func]
        exact congrArg (fun m => (numAt m : Semiterm LX ℕ n₂))
          (congrArg ((stdLX fun _ => False).func f)
            (funext fun i => evTerm_congr_of_evT (ih i)))
      · have hg' : ¬Ground (Semiterm.func f fun i => ω' (v i)) := fun hc =>
          hg ((ground_func_iff f _).mpr fun i => (hgi i).mpr ((ground_func_iff f _).mp hc i))
        rw [evT_func_of_not_ground f _ hg, evT_func_of_not_ground f _ hg']
        exact congrArg (Semiterm.func f) (funext fun i => ih i)

/-- **The formula-level value dependence.** -/
theorem ev_rew_congr {n₁ : ℕ} :
    ∀ (φ : Semiformula LX ℕ n₁) (n₂ : ℕ) (ω ω' : Rew LX ℕ n₁ ℕ n₂), RewEq ω ω' →
      ev (ω ▹ φ) = ev (ω' ▹ φ) := by
  intro φ
  induction φ using Semiformula.rec' with
  | hverum => intro n₂ ω ω' _; simp
  | hfalsum => intro n₂ ω ω' _; simp
  | hrel r v =>
      intro n₂ ω ω' h
      simp only [Semiformula.rew_rel, ev_rel]
      exact congrArg (Semiformula.rel r) (funext fun i => evT_congr h (v i))
  | hnrel r v =>
      intro n₂ ω ω' h
      simp only [Semiformula.rew_nrel, ev_nrel]
      exact congrArg (Semiformula.nrel r) (funext fun i => evT_congr h (v i))
  | hand φ ψ ihφ ihψ =>
      intro n₂ ω ω' h
      simp only [LogicalConnective.HomClass.map_and, ev_and, ihφ n₂ ω ω' h, ihψ n₂ ω ω' h]
  | hor φ ψ ihφ ihψ =>
      intro n₂ ω ω' h
      simp only [LogicalConnective.HomClass.map_or, ev_or, ihφ n₂ ω ω' h, ihψ n₂ ω ω' h]
  | hall φ ih =>
      intro n₂ ω ω' h
      simp only [Rewriting.app_all, ev_all, ih (n₂ + 1) ω.q ω'.q h.q]
  | hexs φ ih =>
      intro n₂ ω ω' h
      simp only [Rewriting.app_exs, ev_exs, ih (n₂ + 1) ω.q ω'.q h.q]

/-- **Simultaneous substitution of ground terms depends only on their values.** -/
theorem ev_substs_ground {k : ℕ} {w w' : Fin k → SyntacticTerm LX}
    (hw : ∀ i, Ground (w i)) (hw' : ∀ i, Ground (w' i))
    (hval : ∀ i, evTerm (w i) = evTerm (w' i)) (φ : Semiformula LX ℕ k) :
    ev (Rew.subst w ▹ φ) = ev (Rew.subst w' ▹ φ) := by
  refine ev_rew_congr φ 0 (Rew.subst w) (Rew.subst w') ⟨fun i => ?_, fun x => ?_⟩
  · rw [Rew.subst_bvar, Rew.subst_bvar, evT_of_ground (hw i), evT_of_ground (hw' i), hval i]
  · rw [Rew.subst_fvar, Rew.subst_fvar]

/-- **Single substitution of a ground term depends only on its value.**  This is
the half of the key law that does *not* need the formula to be normalised first. -/
theorem ev_subst_ground {t : SyntacticTerm LX} (ht : Ground t) (φ : Semiproposition LX 1) :
    ev (φ/[t]) = ev (φ/[numLX (evTerm t)]) := by
  refine ev_substs_ground (w := ![t]) (w' := ![numLX (evTerm t)]) (fun i => ?_) (fun i => ?_)
    (fun i => ?_) φ
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi; simpa using ht
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi; simp
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi; simp

/-- **A free-variable assignment by ground terms depends only on their values** —
the form needed when a derivation's free variables are replaced by numerals. -/
theorem ev_rewrite_ground {n : ℕ} {g g' : ℕ → Semiterm LX ℕ n}
    (hg : ∀ x, Ground (g x)) (hg' : ∀ x, Ground (g' x))
    (hval : ∀ x, evTerm (g x) = evTerm (g' x)) (φ : Semiformula LX ℕ n) :
    ev (Rew.rewrite g ▹ φ) = ev (Rew.rewrite g' ▹ φ) := by
  refine ev_rew_congr φ n (Rew.rewrite g) (Rew.rewrite g') ⟨fun i => ?_, fun x => ?_⟩
  · rw [Rew.rewrite_bvar, Rew.rewrite_bvar]
  · rw [Rew.rewrite_fvar, Rew.rewrite_fvar, evT_of_ground (hg x), evT_of_ground (hg' x), hval x]

/-! ### The key law

This is the equation that turns Foundation's arbitrary-term `exs` into the
ω-calculus's numeral `exs`, once the ω-calculus instantiates its quantifier rules
with `inst φ n = ev (φ/[n̄])`.  The raw law without the outer `ev` on the right is
false; see the header. -/

/-- **The normalised substitution law.**  For a ground `t` of value `n`,
evaluating `φ/[t]` is evaluating the numeral instance of the *evaluated* `φ`. -/
theorem ev_subst_key {t : SyntacticTerm LX} (ht : Ground t) (φ : Semiproposition LX 1) :
    ev (φ/[t]) = ev ((ev φ)/[numLX (evTerm t)]) := by
  rw [ev_subst_ground ht φ]
  exact (ev_rew_ev φ 0 (Rew.subst ![numLX (evTerm t)])).symm

/-! ### The unrestricted semantic form

Substituting a ground term and substituting the numeral of its value give
formulas true together, in every standard model and at every level: a numeral
denotes its value, and `Semiformula.Eval` of a substitution instance depends on
the substituted term only through its value. -/

/-- Substituting a ground term and substituting the numeral of its value give
formulas true together — for *every* `φ`. -/
theorem eval_subst_ground (P : ℕ → Prop) (f : ℕ → ℕ) {n : ℕ} (φ : Semiformula LX ℕ 1)
    (e : Fin n → ℕ) {t : Semiterm LX ℕ n} (ht : Ground t) :
    (Semiformula.Eval (s := stdLX P) e f (φ/[t])
      ↔ Semiformula.Eval (s := stdLX P) e f (φ/[numAt (evTerm t)])) := by
  rw [Semiformula.eval_substs, Semiformula.eval_substs]
  refine iff_of_eq (congrArg (fun w => Semiformula.Eval (s := stdLX P) w f φ) (funext fun i => ?_))
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp only [Function.comp_def, Matrix.cons_val_zero]
  rw [val_ground P (ground_numAt _) e f, evTerm_numAt, val_ground P ht e f]

/-! ### The specific formulas of the lower bound -/

/-- `ev` on the fresh predicate.  Stated and proved through `congrArg`, never
`rw`: a term containing `Sum.inr XRel.X : LX.Rel 1` is not type-correct at
implicit transparency, so `rw` and `simp` refuse to enter it (the trap recorded
for `Idiom.Xrel`). -/
theorem ev_Xat {n : ℕ} (t : Semiterm LX ℕ n) : ev (Xat t) = Xat (evT t) := by
  have h : (fun i => evT ((![t] : Fin 1 → Semiterm LX ℕ n) i)) = ![evT t] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  exact congrArg (Semiformula.rel (Sum.inr XRel.X)) h

/-- `X(n̄)` is a fixed point of `ev`. -/
@[simp] theorem ev_Xat_numLX (m : ℕ) : ev (Xat (numLX m)) = Xat (numLX m) := by
  rw [ev_Xat, evT_numLX]

/-! ### The atomic axioms are closed under `ev`

The ω-calculus takes its true closed arithmetic literals as axioms.  Evaluating
one keeps it an axiom: the relation symbol is untouched, `freeVariables_evT`
keeps the arguments closed, and `eval_ev_zero` keeps it true. -/

/-- `ev` stays inside the closed `X`-free literals.  Built by hand rather than
by `rw`/`simp`: a term containing `Sum.inl r : LX.Rel k` is not type-correct at
implicit transparency (the `Idiom.Xrel` trap, here for the arithmetic half of
the sum), so the two `rfl`s below are supplied as the disjuncts directly. -/
theorem isArithLit_ev {φ : Proposition LX} (h : IsArithLit φ) : IsArithLit (ev φ) := by
  obtain ⟨k, r, v, (rfl | rfl), hcl⟩ := h
  · exact ⟨k, r, fun i => evT (v i), Or.inl rfl,
      fun i => by rw [freeVariables_evT]; exact hcl i⟩
  · exact ⟨k, r, fun i => evT (v i), Or.inr rfl,
      fun i => by rw [freeVariables_evT]; exact hcl i⟩

/-- `ev` preserves truth in `ℕ` — the case of LAW 2 that `TrueN` is. -/
theorem trueN_ev (φ : Proposition LX) : TrueN (ev φ) ↔ TrueN φ := by
  unfold TrueN
  exact eval_ev_zero (fun _ => False) (fun _ => 0) φ

/-- **The axiom set is closed under `ev`.** -/
theorem trueArithLits_ev {φ : Proposition LX} (h : trueArithLits.T φ) :
    trueArithLits.T (ev φ) := by
  rw [trueArithLits_T] at h ⊢
  exact ⟨isArithLit_ev h.1, (trueN_ev φ).mpr h.2⟩


end Evaluate

end Gentzen

end OrdinalAnalysis
