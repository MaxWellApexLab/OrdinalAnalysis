/-
  Coded orderings for the ramified calculus `RA_∞` over `LRA`.

  This is `Gentzen/CodedOrder.lean` transposed from `LX = ℒₒᵣ + {X}` to
  `LRA = ℒₒᵣ + {X} ∪ {∈̇_ν}` (`Ramified/Language.lean`).  Nothing in the
  boundedness argument uses anything about a coded ordering beyond the four
  facts `CodedOrderR` collects — the ordering's formula, its coding of a
  notation system `O` by numbers, the reading of the formula in `ℕ`, and the
  two bridges between them — so the structure is carried over verbatim, field
  for field.

  Three points of departure from the first-order file, all forced by the
  larger language.

  * **`XFree` now also excludes every `∈̇_ν`.**  Its defining clause is
    unchanged (`the head relation symbol is `Sum.inl`), and that clause was
    already strong enough: `LRA`'s fresh summand `RALang` carries *both* `X`
    and every `∈̇_ν`, so "not the fresh summand" excludes both without any
    extra case.  `XFree` therefore means exactly "pure arithmetic formula",
    which is what the coded ordering's own formula must be (it is built from
    a `Γ₀`-arithmetic graph formula by `Semiformula.lMap toLRA`, and no
    lifting from arithmetic can ever mention `X` or `∈̇_ν`).  The weaker
    predicate that excludes only `∈̇_ν` and permits `X` — needed for the class
    of the boundedness lemma, whose named members *do* mention `X` — is
    `SetFree`, defined in `Ramified/LowerClass.lean` where it is first used.

  * **The syntactic bridge is stated over an arbitrary reading of *both*
    fresh symbols**, `raStd s₂` for `s₂ : Structure RALang ℕ`, rather than
    over a reading of `X` alone: `Ramified/Evaluate.lean`'s `raStd`/`stdR`
    already package exactly this, and a `CodedOrderR`'s `prec` is `XFree`, so
    the reading is invisible to it regardless.

  * **The coded ordering itself is reconstructed directly, not transported
    generically.**  A generic transport of `Gentzen.CodedOrder O` along a
    language map `LX →ᵥ LRA` would need a Structure-level compatibility lemma
    for that map (`Structure.lMap` agreeing with `raStd`), which is more
    machinery than the coded ordering below actually needs: `gamma0OrderR` is
    built by replaying `Gentzen/CodedVeblen.lean`'s construction of
    `gamma0Order` with `toLX` replaced by `toLRA` (`Ramified/Language.lean`),
    reusing the arithmetic-level facts `precDef₁`, `gamma0Code`, `precN₁` and
    `precN₁_code_iff` from `Gentzen.CodedVeblen`/`Gentzen.VNoteBridge`
    unchanged — they are statements about `ℕ` alone and know nothing about
    which language they were phrased in.  The one bridge lemma that *does*
    depend on the language, `eval_precAt_numeral`, is proved the same way
    `Gentzen.CodedVeblen.eval_precAt₁_numeral` is, with `eval_lMap_toLX`
    replaced by `Ramified.Evaluate.eval_lMap_toLRA`.

  Also defined here, exactly as `Gentzen/Setup.lean` and `Gentzen/LowerSyntax.lean`
  define them for `LX`: the shapes `precAt`/`below`/`Prog`/`TIR` built from a
  coded ordering's formula, and their substitution and closedness lemmas.  Only
  what the boundedness lemma needs is carried over — `TIupto` and the
  `complexity`/`univCl` bookkeeping of the first-order file have no use here
  and are omitted.
-/
import OrdinalAnalysis.Ramified.Evaluate
import OrdinalAnalysis.Gentzen.CodedVeblen

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### Not mentioning `X` or `∈̇_ν`

Moved here from `Gentzen/CodedOrder.lean`'s `LowerClass.XFree`, unchanged
except for the language: `LRA.Rel k = ℒₒᵣ.Rel k ⊕ RARel k`, and the fresh
summand `RARel` carries *both* `X` and every `∈̇_ν`, so excluding `Sum.inr`
excludes both at once. -/

/-- `φ` does not mention `X` or any `∈̇_ν`: every relation symbol occurring in
it is arithmetic. -/
def XFree {n : ℕ} : Semiformula LRA ℕ n → Prop
  |                   ⊤ => True
  |                   ⊥ => True
  |  .rel (arity := k) r _ => ∃ r' : (ℒₒᵣ : Language).Rel k, r = Sum.inl r'
  | .nrel (arity := k) r _ => ∃ r' : (ℒₒᵣ : Language).Rel k, r = Sum.inl r'
  |               φ ⋏ ψ => XFree φ ∧ XFree ψ
  |               φ ⋎ ψ => XFree φ ∧ XFree ψ
  |                ∀¹ φ => XFree φ
  |                ∃¹ φ => XFree φ

@[simp] theorem XFree_verum {n : ℕ} : XFree (⊤ : Semiformula LRA ℕ n) := trivial

@[simp] theorem XFree_falsum {n : ℕ} : XFree (⊥ : Semiformula LRA ℕ n) := trivial

@[simp] theorem XFree_rel {n k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    XFree (Semiformula.rel r v) ↔ ∃ r' : (ℒₒᵣ : Language).Rel k, r = Sum.inl r' := Iff.rfl

@[simp] theorem XFree_nrel {n k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    XFree (Semiformula.nrel r v) ↔ ∃ r' : (ℒₒᵣ : Language).Rel k, r = Sum.inl r' := Iff.rfl

@[simp] theorem XFree_and {n : ℕ} (φ ψ : Semiformula LRA ℕ n) :
    XFree (φ ⋏ ψ) ↔ XFree φ ∧ XFree ψ := Iff.rfl

@[simp] theorem XFree_or {n : ℕ} (φ ψ : Semiformula LRA ℕ n) :
    XFree (φ ⋎ ψ) ↔ XFree φ ∧ XFree ψ := Iff.rfl

@[simp] theorem XFree_all {n : ℕ} (φ : Semiformula LRA ℕ (n + 1)) :
    XFree (∀¹ φ) ↔ XFree φ := Iff.rfl

@[simp] theorem XFree_exs {n : ℕ} (φ : Semiformula LRA ℕ (n + 1)) :
    XFree (∃¹ φ) ↔ XFree φ := Iff.rfl

/-- **`X(t)` is never `XFree`.**  As in `Gentzen/CodedOrder.lean`,
`Sum.noConfusion` leaves a universe metavariable unsolved on a symbol of type
`LRA.Rel 1`; the `reduceCtorEq` simproc, reached through `simp`, settles it. -/
@[simp] theorem not_XFree_Xat {n : ℕ} (t : Semiterm LRA ℕ n) : ¬ XFree (Xat t) := by
  intro h
  obtain ⟨r, hr⟩ : ∃ r : (ℒₒᵣ : Language).Rel 1, (Sum.inr RARel.X : LRA.Rel 1) = Sum.inl r := h
  simp at hr

/-- **A level-`ν` set atom is never `XFree`.** -/
@[simp] theorem not_XFree_memAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    ¬ XFree (memAt ν t s) := by
  intro h
  obtain ⟨r, hr⟩ :
      ∃ r : (ℒₒᵣ : Language).Rel 2, (Sum.inr (RARel.mem ν) : LRA.Rel 2) = Sum.inl r := h
  simp at hr

/-- The negated form. -/
@[simp] theorem not_XFree_nmemAt {n : ℕ} (ν : Lv) (t s : Semiterm LRA ℕ n) :
    ¬ XFree (nmemAt ν t s) := by
  intro h
  obtain ⟨r, hr⟩ :
      ∃ r : (ℒₒᵣ : Language).Rel 2, (Sum.inr (RARel.mem ν) : LRA.Rel 2) = Sum.inl r := h
  simp at hr

/-- `X`/`∈̇`-freeness is invariant under negation: `∼` only swaps `rel` and
`nrel`. -/
@[simp] theorem XFree_neg {n : ℕ} (φ : Semiformula LRA ℕ n) : XFree (∼φ) ↔ XFree φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **Invariant under every rewriting.**  Rewritings move terms, never
relation symbols; this is what makes the class of the boundedness lemma
closed under the substitutions the ω-rule and the (Pr) rule perform. -/
@[simp] theorem XFree_rew {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (φ : Semiformula LRA ℕ n₁) :
    XFree (ω ▹ φ) ↔ XFree φ := by
  induction φ using Semiformula.rec' generalizing n₂ <;> simp [*]

/-- **Everything transported from arithmetic is `XFree`.** -/
theorem XFree_lMap_toLRA {n : ℕ} (φ : Semiformula ℒₒᵣ ℕ n) :
    XFree (Semiformula.lMap toLRA φ) := by
  induction φ using Semiformula.rec' <;> simp [*]
  case hrel k r v => exact ⟨r, rfl⟩
  case hnrel k r v => exact ⟨r, rfl⟩

/-! ### Generic closedness lemmas

Specialised directly to `LRA`, `ξ := ℕ`; the underlying facts
(`Semiterm.fvar?_rew`, `Semiformula.fvar?_rew`) are Foundation's and hold for
any language. -/

private theorem freeVariables_rew_eq_empty {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂)
    {φ : Semiformula LRA ℕ n₁} (hφ : φ.freeVariables = ∅)
    (hb : ∀ i : Fin n₁, (ω #i).freeVariables = ∅) :
    (ω ▹ φ).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := ω) (φ := φ) (x := x) hx with ⟨i, hi⟩ | ⟨z, hz, _⟩
  · rw [Semiterm.FVar?, hb i] at hi
    exact Finset.notMem_empty x hi
  · rw [Semiformula.FVar?, hφ] at hz
    exact Finset.notMem_empty z hz

/-! ### `X(t)` under rewriting

Stated with `Xat t` on the left so that no later `rw`/`simp` has to unfold
`Sum.inr RARel.X`. -/

@[simp] theorem rew_Xat {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (t : Semiterm LRA ℕ n₁) :
    ω ▹ (Xat t) = Xat (ω t) :=
  Semiformula.rew_rel1 ω

@[simp] theorem freeVariables_Xat {n : ℕ} (t : Semiterm LRA ℕ n) :
    (Xat t).freeVariables = t.freeVariables := by
  ext x
  have h : (Xat t).FVar? x ↔ ∃ i : Fin 1, ((![t] : Fin 1 → Semiterm LRA ℕ n) i).FVar? x :=
    Semiformula.fvar?_rel
  simpa using h

/-! ### `precAt`, `below`, `Prog`, `TIR`

`Gentzen/Setup.lean`'s `precAt`/`below`/`Prog`/`TI`, symbol for symbol, with
`LRA` for `LX`.  `TIupto` has no use in the boundedness lemma and is omitted. -/

variable (prec : Semiformula LRA ℕ 2)

/-- `y ≺ x`, with `y` the innermost bound variable. -/
def precAt {n : ℕ} (y x : Semiterm LRA ℕ n) : Semiformula LRA ℕ n :=
  Rew.subst ![y, x] ▹ prec

/-- `∀ y ≺ x, X y` — the hypothesis of progressiveness at `x`. -/
def below : Semiformula LRA ℕ 1 :=
  ∀¹ (∼(precAt prec (#0 : Semiterm LRA ℕ 2) #1) ⋎ Xat #0)

/-- `Prog(≺) :≡ ∀ x ((∀ y ≺ x, X y) → X x)`. -/
def Prog : Semiformula LRA ℕ 0 :=
  ∀¹ (∼(below prec) ⋎ Xat #0)

/-- `TI(≺) :≡ Prog(≺) → ∀ x, X x`, exactly as `Gentzen.TI`. -/
def TIR : Proposition LRA :=
  ∼(Prog prec) ⋎ (∀¹ (Xat #0))

/-- Rewriting commutes with `precAt`, for any rewriting that fixes the free
variables. -/
theorem rew_precAt {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂) (hω : ∀ z : ℕ, ω &z = &z)
    (y x : Semiterm LRA ℕ n₁) :
    ω ▹ (precAt prec y x) = precAt prec (ω y) (ω x) := by
  have h : ω.comp (Rew.subst ![y, x]) = Rew.subst ![ω y, ω x] := by
    ext i
    case hb =>
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> simp [Rew.comp_app]
    case hf => simp [Rew.comp_app, hω]
  show (Rew.subst ![y, x] ▹ prec |> (Rewriting.app ω)) = Rew.subst ![ω y, ω x] ▹ prec
  rw [← TransitiveRewriting.comp_app, h]

/-- The instance used throughout: substitution commutes with `precAt`. -/
@[simp] theorem subst_precAt {n₁ n₂ : ℕ} (w : Fin n₁ → Semiterm LRA ℕ n₂)
    (y x : Semiterm LRA ℕ n₁) :
    (Rew.subst w) ▹ (precAt prec y x) = precAt prec (Rew.subst w y) (Rew.subst w x) :=
  rew_precAt prec _ (fun z => by simp) y x

/-- `Rew.bShift` commutes with `precAt` too. -/
@[simp] theorem bShift_precAt {n : ℕ} (y x : Semiterm LRA ℕ n) :
    (Rew.bShift : Rew LRA ℕ n ℕ (n + 1)) ▹ (precAt prec y x)
      = precAt prec (Rew.bShift y) (Rew.bShift x) :=
  rew_precAt prec _ (fun z => by simp) y x

theorem freeVariables_precAt_eq_empty (hprec : prec.freeVariables = ∅) {n : ℕ}
    {y x : Semiterm LRA ℕ n} (hy : y.freeVariables = ∅) (hx : x.freeVariables = ∅) :
    (precAt prec y x).freeVariables = ∅ := by
  refine freeVariables_rew_eq_empty _ hprec ?_
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · simpa using hy
  · simpa using hx

/-! One substitution into `below`, and the two steps the ω-calculus performs
to reach the fully instantiated form: first at `below`, then at its body. -/

theorem subst_below (t : Semiterm LRA ℕ 0) :
    (below prec)/[t] =
      ∀¹ (∼(precAt prec (#0 : Semiterm LRA ℕ 1) (Rew.bShift t)) ⋎
          Xat (#0 : Semiterm LRA ℕ 1)) := by
  simp [below, Rew.q_subst]

@[simp] theorem subst_below_numeral (k : ℕ) :
    (below prec)/[numAtR k] =
      ∀¹ (∼(precAt prec (#0 : Semiterm LRA ℕ 1) (numAtR k : Semiterm LRA ℕ 1)) ⋎
          Xat (#0 : Semiterm LRA ℕ 1)) := by
  rw [subst_below, rew_numAtR]

@[simp] theorem subst_belowBody_numeral (k m : ℕ) :
    (∼(precAt prec (#0 : Semiterm LRA ℕ 1) (numAtR k : Semiterm LRA ℕ 1)) ⋎
      Xat (#0 : Semiterm LRA ℕ 1))/[(numAtR m : Semiterm LRA ℕ 0)] =
      ∼(precAt prec (numAtR m : Semiterm LRA ℕ 0) (numAtR k : Semiterm LRA ℕ 0)) ⋎
        Xat (numAtR m : Semiterm LRA ℕ 0) := by
  simp [-numAtR_zero]

theorem subst_Xat_bvar_numeral (k : ℕ) :
    (Xat (#0 : Semiterm LRA ℕ 1))/[(numAtR k : Semiterm LRA ℕ 0)] =
      Xat (numAtR k : Semiterm LRA ℕ 0) := by simp [-numAtR_zero]

/-! ### De Morgan normal form -/

theorem neg_Prog : ∼(Prog prec) = ∃¹ ((below prec) ⋏ ∼(Xat (#0 : Semiterm LRA ℕ 1))) := by
  simp [Prog]

/-! ### Closedness -/

theorem freeVariables_below (hprec : prec.freeVariables = ∅) : (below prec).freeVariables = ∅ := by
  have h : (precAt prec (#0 : Semiterm LRA ℕ 2) #1).freeVariables = ∅ :=
    freeVariables_precAt_eq_empty prec hprec (by simp) (by simp)
  simp [Ramified.below, h]

theorem freeVariables_Prog (hprec : prec.freeVariables = ∅) : (Prog prec).freeVariables = ∅ := by
  have h := freeVariables_below prec hprec
  simp [Ramified.Prog, h]

theorem freeVariables_TIR (hprec : prec.freeVariables = ∅) : (TIR prec).freeVariables = ∅ := by
  have h := freeVariables_Prog prec hprec
  simp [Ramified.TIR, h]

/-! ### The structure -/

/-- A **coded ordering** on a notation system `O`, for the ramified language
`LRA`: an `XFree` closed formula of two variables, a coding of `O` by numbers,
the reading of the formula in `ℕ`, and the two bridges between them — exactly
`Gentzen.CodedOrder` transposed to `LRA`. -/
structure CodedOrderR (O : Type) [LinearOrder O] where
  /-- The ordering, as a formula of `LRA` in two variables. -/
  prec : Semiformula LRA ℕ 2
  /-- It mentions neither `X` nor any `∈̇_ν`. -/
  xfree_prec : XFree prec
  /-- It has no free variables. -/
  freeVariables_prec : prec.freeVariables = ∅
  /-- The coding of the notations by numbers. -/
  code : O → ℕ
  /-- The ordering read in `ℕ`. -/
  precN : ℕ → ℕ → Prop
  /-- **The syntactic bridge.**  At a pair of numerals, in any reading of the
  fresh symbols, `prec` says `precN`. -/
  eval_precAt_numeral : ∀ (s₂ : Structure RALang ℕ) (m n : ℕ) (f : ℕ → ℕ),
    Semiformula.Eval (s := raStd s₂) ![] f (precAt prec (numAtR m) (numAtR n)) ↔ precN m n
  /-- **The semantic bridge.**  Standard codes are ordered as the notations
  are. -/
  precN_code_iff : ∀ a b : O, precN (code a) (code b) ↔ a < b

namespace CodedOrderR

variable {O : Type} [LinearOrder O] (C : CodedOrderR O)

theorem precN_code_of_lt {a b : O} (h : a < b) : C.precN (C.code a) (C.code b) :=
  (C.precN_code_iff a b).mpr h

theorem lt_of_precN_code {a b : O} (h : C.precN (C.code a) (C.code b)) : a < b :=
  (C.precN_code_iff a b).mp h

@[simp] theorem freeVariables_precAt {n : ℕ} {y x : Semiterm LRA ℕ n}
    (hy : y.freeVariables = ∅) (hx : x.freeVariables = ∅) :
    (Ramified.precAt C.prec y x).freeVariables = ∅ :=
  Ramified.freeVariables_precAt_eq_empty C.prec C.freeVariables_prec hy hx

@[simp] theorem freeVariables_below : (Ramified.below C.prec).freeVariables = ∅ :=
  Ramified.freeVariables_below C.prec C.freeVariables_prec

@[simp] theorem freeVariables_Prog : (Ramified.Prog C.prec).freeVariables = ∅ :=
  Ramified.freeVariables_Prog C.prec C.freeVariables_prec

@[simp] theorem freeVariables_TIR : (TIR C.prec).freeVariables = ∅ :=
  Ramified.freeVariables_TIR C.prec C.freeVariables_prec

end CodedOrderR

/-! ### The `Γ₀` instance

`Gentzen/CodedVeblen.lean`'s construction of `gamma0Order`, with `toLX`
replaced by `toLRA`.  `precDef₁`, `gamma0Code`, `precN₁` and
`precN₁_code_iff` are reused unchanged: they are statements about `ℕ` alone. -/

open OrdinalAnalysis.Gentzen.InternalVNote (precDef₁)
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)
open OrdinalAnalysis.Gentzen.CodedVeblen (precN₁ precN₁_code_iff)

/-- **The coded Veblen ordering** `≺₁`, transported into `LRA`. -/
def precCode₁R : Semiformula LRA ℕ 2 :=
  Semiformula.lMap toLRA (Rewriting.emb (precDef₁ : ArithmeticSemisentence 2))

@[simp] theorem XFree_precCode₁R : XFree precCode₁R :=
  XFree_lMap_toLRA _

@[simp] theorem freeVariables_precCode₁R : precCode₁R.freeVariables = ∅ := by
  simp [precCode₁R]

/-- `precCode₁R` evaluates in any standard structure of `LRA` as `precN₁`,
whatever the fresh symbols are read as. -/
theorem eval_precCode₁R (s₂ : Structure RALang ℕ) (m n : ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := raStd s₂) ![m, n] f precCode₁R ↔ precN₁ m n := by
  unfold precCode₁R precN₁
  rw [eval_lMap_toLRA]
  simp

@[simp] theorem val_numAtR (s₂ : Structure RALang ℕ) {n : ℕ} (m : ℕ) (e : Fin n → ℕ)
    (f : ℕ → ℕ) : Semiterm.val (s := raStd s₂) e f (numAtR m : Semiterm LRA ℕ n) = m := by
  rw [val_groundR s₂ (groundR_numAtR m) e f, evTermR_numAtR]

/-- **The instance the boundedness induction meets.** -/
theorem eval_precAt₁R_numeral (s₂ : Structure RALang ℕ) (m n : ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := raStd s₂) ![] f
      (precAt precCode₁R (numAtR m) (numAtR n)) ↔ precN₁ m n := by
  unfold precAt
  rw [Semiformula.eval_rew]
  have e₁ : (Semiterm.val (s := raStd s₂) ![] f ∘
      ⇑(Rew.subst ![(numAtR m : Semiterm LRA ℕ 0), numAtR n]) ∘ Semiterm.bvar) = ![m, n] := by
    funext i
    revert i
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> simp [-numAtR_zero]
  have e₂ : (Semiterm.val (s := raStd s₂) ![] f ∘
      ⇑(Rew.subst ![(numAtR m : Semiterm LRA ℕ 0), numAtR n]) ∘ Semiterm.fvar) = f := by
    funext x; simp [-numAtR_zero]
  rw [e₁, e₂]
  exact eval_precCode₁R s₂ m n f

/-- **The coded ordering of the Veblen notations below `Γ₀`, for `LRA`.** -/
def gamma0OrderR : CodedOrderR Gamma0Note where
  prec := precCode₁R
  xfree_prec := XFree_precCode₁R
  freeVariables_prec := freeVariables_precCode₁R
  code := gamma0Code
  precN := precN₁
  eval_precAt_numeral := eval_precAt₁R_numeral
  precN_code_iff := precN₁_code_iff

@[simp] theorem gamma0OrderR_prec : gamma0OrderR.prec = precCode₁R := rfl

@[simp] theorem gamma0OrderR_code : gamma0OrderR.code = gamma0Code := rfl

@[simp] theorem gamma0OrderR_precN : gamma0OrderR.precN = precN₁ := rfl

end Ramified

end OrdinalAnalysis
