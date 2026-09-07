/-
  Coded orderings, abstractly.

  The lower-bound pipeline — `LowerClass.lean`, `LowerClassEv.lean`,
  `Boundedness.lean`, `LowerBound.lean` — was written with one ordering
  hard-wired into it: `precCode`, the ℒₒᵣ-definable ordering of the notations
  below `ε₀` (`Gentzen/CodedNotation.lean`), read in `ℕ` as `PrecStandard.precN`
  and matched to `NONote` by `NotationBridge.nonoteCode`.  Nothing in the
  argument uses anything about that ordering beyond four facts, and the next
  theorem — `|PA + TI(ε₀)| = ε₁` — runs the very same argument on the
  `ε₁`-segment of the Γ₀ notations.  So this file isolates the four facts as a
  structure, exactly as `Ordinal/Notation.lean` isolated what the infinitary
  calculus needs of its heights, and re-installs the `ε₀` case as an instance.

  What the structure carries:

  * a formula `prec` in two variables which does not mention `X` and has no
    free variables — the *syntax* the class `C` of the boundedness lemma is
    built from;
  * a coding `code : O → ℕ` of the notations, and the reading `precN` of `prec`
    in `ℕ`;
  * the two bridges: `prec` evaluated at a pair of numerals in the standard
    structure *is* `precN`, and `precN` on standard codes *is* the order of
    `O`.

  Everything else — that `≺` is transitive, that `code` is injective or
  surjective, that `O` has any particular order type — is not needed and is not
  asked for.

  Two placement decisions.

  * **`XFree` lives here.**  It was defined in `LowerClass.lean`, but the
    structure has to speak of it and `LowerClass.lean` now imports this file.
    It keeps its namespace `OrdinalAnalysis.Gentzen.LowerClass` and every one of
    its names, so nothing downstream can tell it moved.  (The alternative,
    `OmegaTruth.XFree`, would have needed a translation lemma: its atomic clause
    is `IsArithRel r`, not `∃ r', r = Sum.inl r'`.)

  * **`le_of_forall_lt_lt` lives here too**, generically.  It was stated for
    `NONote` in `PrecStandard.lean`; it is true in any linear order, and the
    boundedness lemma needs it at `O`.
-/
import OrdinalAnalysis.Gentzen.PrecStandard

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.CodedNotation
open OrdinalAnalysis.Gentzen.LowerSyntax
open OrdinalAnalysis.Gentzen.StandardLX (stdLX)

/-! ### Not mentioning `X`

Moved verbatim from `LowerClass.lean`; the namespace and every name are
unchanged.

`LX.Rel k` is `ℒₒᵣ.Rel k ⊕ XRel k`, and the fresh predicate is the single
symbol `Sum.inr XRel.X`.  A formula is `X`-free when every relation symbol it
carries is on the left.  Stated so that `simp` never has to look at
`Sum.inr XRel.X`: the atom clause quantifies over a *variable* symbol. -/

namespace LowerClass

/-- `φ` does not mention the fresh predicate `X`. -/
def XFree {n : ℕ} : Semiformula LX ℕ n → Prop
  |                   ⊤ => True
  |                   ⊥ => True
  |  .rel (arity := k) r _ => ∃ r' : (ℒₒᵣ : Language).Rel k, r = Sum.inl r'
  | .nrel (arity := k) r _ => ∃ r' : (ℒₒᵣ : Language).Rel k, r = Sum.inl r'
  |               φ ⋏ ψ => XFree φ ∧ XFree ψ
  |               φ ⋎ ψ => XFree φ ∧ XFree ψ
  |                ∀¹ φ => XFree φ
  |                ∃¹ φ => XFree φ

@[simp] theorem XFree_verum {n : ℕ} : XFree (⊤ : Semiformula LX ℕ n) := trivial

@[simp] theorem XFree_falsum {n : ℕ} : XFree (⊥ : Semiformula LX ℕ n) := trivial

@[simp] theorem XFree_rel {n k : ℕ} (r : LX.Rel k) (v : Fin k → Semiterm LX ℕ n) :
    XFree (Semiformula.rel r v) ↔ ∃ r' : (ℒₒᵣ : Language).Rel k, r = Sum.inl r' := Iff.rfl

@[simp] theorem XFree_nrel {n k : ℕ} (r : LX.Rel k) (v : Fin k → Semiterm LX ℕ n) :
    XFree (Semiformula.nrel r v) ↔ ∃ r' : (ℒₒᵣ : Language).Rel k, r = Sum.inl r' := Iff.rfl

@[simp] theorem XFree_and {n : ℕ} (φ ψ : Semiformula LX ℕ n) :
    XFree (φ ⋏ ψ) ↔ XFree φ ∧ XFree ψ := Iff.rfl

@[simp] theorem XFree_or {n : ℕ} (φ ψ : Semiformula LX ℕ n) :
    XFree (φ ⋎ ψ) ↔ XFree φ ∧ XFree ψ := Iff.rfl

@[simp] theorem XFree_all {n : ℕ} (φ : Semiformula LX ℕ (n + 1)) :
    XFree (∀¹ φ) ↔ XFree φ := Iff.rfl

@[simp] theorem XFree_exs {n : ℕ} (φ : Semiformula LX ℕ (n + 1)) :
    XFree (∃¹ φ) ↔ XFree φ := Iff.rfl

/-- **`X(t)` is never `X`-free.**  `Sum.noConfusion` cannot be applied here (its
universe metavariable stays unsolved on a symbol of type `LX.Rel 1`); the
`reduceCtorEq` simproc can. -/
@[simp] theorem not_XFree_Xat {n : ℕ} (t : Semiterm LX ℕ n) : ¬ XFree (Xat t) := by
  intro h
  obtain ⟨r, hr⟩ : ∃ r : (ℒₒᵣ : Language).Rel 1, (Sum.inr XRel.X : LX.Rel 1) = Sum.inl r := h
  simp at hr

/-- `X`-freeness is invariant under negation: `∼` only swaps `rel` and `nrel`. -/
@[simp] theorem XFree_neg {n : ℕ} (φ : Semiformula LX ℕ n) : XFree (∼φ) ↔ XFree φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **`X`-freeness is invariant under every rewriting.**  Rewritings move terms,
never relation symbols; this is what makes the class `C` closed under the
substitutions the ω-rule performs. -/
@[simp] theorem XFree_rew {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) (φ : Semiformula LX ℕ n₁) :
    XFree (ω ▹ φ) ↔ XFree φ := by
  induction φ using Semiformula.rec' generalizing n₂ <;> simp [*]

/-- Everything transported from arithmetic is `X`-free — in particular
`precCode`. -/
theorem XFree_lMap_toLX {n : ℕ} (φ : Semiformula ℒₒᵣ ℕ n) :
    XFree (Semiformula.lMap toLX φ) := by
  induction φ using Semiformula.rec' <;> simp [*]
  case hrel k r v => exact ⟨r, rfl⟩
  case hnrel k r v => exact ⟨r, rfl⟩

@[simp] theorem XFree_precCode : XFree precCode :=
  XFree_lMap_toLX _

end LowerClass

/-! ### Linearity, in the form the ω-rule case uses

Stated for `NONote` in `PrecStandard.lean` until the pipeline was
parametrised; the proof never used anything but linearity. -/

/-- **If every element below `o` is below `γ`, then `o ≤ γ`.**  This is the step
that turns "every predecessor is small" into "`o` is small" in the ω-rule case
of the boundedness lemma, and it is the only place linearity of the notations is
used. -/
theorem le_of_forall_lt_lt {O : Type} [LinearOrder O] {o γ : O}
    (h : ∀ o' : O, o' < o → o' < γ) : o ≤ γ := by
  by_contra hlt
  exact lt_irrefl γ (h γ (not_le.mp hlt))

/-! ### The structure -/

/-- A **coded ordering** on a notation system `O`: an `X`-free closed formula of
two variables, a coding of `O` by numbers, the reading of the formula in `ℕ`,
and the two bridges between them.

Only `[LinearOrder O]` is required.  Well-foundedness and the arithmetic of
`Ordinal/Notation.lean` are what the *heights* of the calculus need, not what
the ordering needs, and keeping them off this structure lets `LowerClass.lean`
and `LowerClassEv.lean` — which never mention a height — stay free of them. -/
structure CodedOrder (O : Type) [LinearOrder O] where
  /-- The ordering, as a formula of `LX` in two variables. -/
  prec : Semiformula LX ℕ 2
  /-- It does not mention the fresh predicate. -/
  xfree_prec : LowerClass.XFree prec
  /-- It has no free variables. -/
  freeVariables_prec : prec.freeVariables = ∅
  /-- The coding of the notations by numbers. -/
  code : O → ℕ
  /-- The ordering read in `ℕ`. -/
  precN : ℕ → ℕ → Prop
  /-- **The syntactic bridge.**  At a pair of numerals, in the standard
  structure and for any reading `P` of `X`, `prec` says `precN`. -/
  eval_precAt_numeral : ∀ (P : ℕ → Prop) (m n : ℕ) (f : ℕ → ℕ),
    Semiformula.Eval (s := stdLX P) ![] f
      (precAt prec (LowerSyntax.numLX m) (LowerSyntax.numLX n)) ↔ precN m n
  /-- **The semantic bridge.**  Standard codes are ordered as the notations
  are. -/
  precN_code_iff : ∀ a b : O, precN (code a) (code b) ↔ a < b

namespace CodedOrder

variable {O : Type} [LinearOrder O] (C : CodedOrder O)

theorem precN_code_of_lt {a b : O} (h : a < b) : C.precN (C.code a) (C.code b) :=
  (C.precN_code_iff a b).mpr h

theorem lt_of_precN_code {a b : O} (h : C.precN (C.code a) (C.code b)) : a < b :=
  (C.precN_code_iff a b).mp h

/-! ### Closedness of the formulas built from `prec`

The `precCode` instances of `LowerSyntax.lean`, once per shape. -/

@[simp] theorem freeVariables_precAt {n : ℕ} {y x : Semiterm LX ℕ n}
    (hy : y.freeVariables = ∅) (hx : x.freeVariables = ∅) :
    (precAt C.prec y x).freeVariables = ∅ :=
  LowerSyntax.freeVariables_precAt_eq_empty C.freeVariables_prec hy hx

@[simp] theorem freeVariables_below : (below C.prec).freeVariables = ∅ :=
  LowerSyntax.freeVariables_below C.freeVariables_prec

@[simp] theorem freeVariables_Prog : (Prog C.prec).freeVariables = ∅ :=
  LowerSyntax.freeVariables_Prog C.freeVariables_prec

@[simp] theorem freeVariables_TI : (TI C.prec).freeVariables = ∅ :=
  LowerSyntax.freeVariables_TI C.freeVariables_prec

/-! ### `univCl` is a typing wrapper

The `LowerSyntax.lean` interchange lemmas, for a general coded ordering. -/

/-- `univCl'` is the identity on `TI C.prec`. -/
theorem univCl'_TI : (TI C.prec).univCl' = TI C.prec :=
  Semiformula.univCl'_eq_self_of _ C.freeVariables_TI

/-- **The interchange lemma.**  Embedding the sentence `(TI C.prec).univCl` back
into `Semiformula LX ℕ 0` returns `TI C.prec` on the nose. -/
@[simp] theorem emb_univCl_TI :
    (Rewriting.emb ((TI C.prec).univCl) : Semiformula LX ℕ 0) = TI C.prec := by
  have h : ((TI C.prec).univCl : Semiformula LX ℕ 0) = (TI C.prec).univCl' :=
    Semiformula.coe_univCl_eq_univCl' _
  rw [show (Rewriting.emb ((TI C.prec).univCl) : Semiformula LX ℕ 0)
        = ((TI C.prec).univCl : Semiformula LX ℕ 0) from rfl, h, C.univCl'_TI]

end CodedOrder

namespace LowerClass

/-- The ordering at a pair of terms is `X`-free: `precAt` is a substitution
instance, and rewriting does not move relation symbols. -/
@[simp] theorem XFree_precAt {O : Type} [LinearOrder O] (C : CodedOrder O) {n : ℕ}
    (y x : Semiterm LX ℕ n) : XFree (precAt C.prec y x) := by
  simp only [precAt, XFree_rew]
  exact C.xfree_prec

end LowerClass

/-! ### The `ε₀` case

Every field is a definition or lemma already proved; nothing is re-proved. -/

/-- **The coded ordering of the notations below `ε₀`**: Gentzen's `≺`. -/
def epsilon0Order : CodedOrder NONote where
  prec := precCode
  xfree_prec := LowerClass.XFree_precCode
  freeVariables_prec := LowerSyntax.freeVariables_precCode
  code := NotationBridge.nonoteCode
  precN := PrecStandard.precN
  eval_precAt_numeral := PrecStandard.eval_precAt_numeral
  precN_code_iff := PrecStandard.precN_code_iff

@[simp] theorem epsilon0Order_prec : epsilon0Order.prec = precCode := rfl

@[simp] theorem epsilon0Order_code : epsilon0Order.code = NotationBridge.nonoteCode := rfl

@[simp] theorem epsilon0Order_precN : epsilon0Order.precN = PrecStandard.precN := rfl

end OrdinalAnalysis.Gentzen
