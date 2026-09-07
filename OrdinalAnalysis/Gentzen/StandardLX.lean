/-
  The standard model of `LX`, and the atomic axioms of the ω-calculus.

  The ω-calculus of `Omega/Calculus.lean` needs three things beyond pure logic:
  a family of numerals, a set of true closed literals to start derivations from,
  and — for the lower bound — a *semantics* in which "true" is meant.  This file
  supplies all three for the language `LX = ℒₒᵣ + X` of `Setup.lean`.

  Three things about the shape.

  * The interpretation of the fresh predicate is a **parameter** `P : ℕ → Prop`,
    not a fixed choice.  The lower-bound argument reinterprets `X` — Buchholz's
    boundedness lemma reads it as an initial segment of the notations, and that
    segment shrinks as the ordinal height shrinks — so the standard model must
    come as a family `stdLX P`, one for each reading of `X`, with the arithmetic
    part held fixed.  `stdLX_lMap_toLX` is exactly the statement that the
    arithmetic part does not move.

  * The atomic axioms are the **`X`-free** true closed literals.  Nothing else
    would be sound for the whole family: an `X`-literal true under one `P` is
    false under another.  `trueArithLits_xfree` turns that slogan into a
    theorem, and it is proved *semantically* — the axioms are `P`-independent
    (`eval_indep_of_isArithLit`) while `X(t)` is not — so no syntactic
    injectivity for the dependently typed constructor `Semiformula.rel` is
    needed anywhere.

  * `P`-independence is genuinely a lemma, not a definitional triviality.  Term
    values are computed against the whole structure, and `stdLX P` and `stdLX Q`
    are different structures; that their `func` fields agree — `XLang` has no
    function symbols — is `stdLX_func`, and the induction that lifts it to all
    terms is `val_stdLX_congr`.  Independence of the *assignment* is separate,
    and comes from closedness of the arguments through
    `Semiterm.val_eq_of_funEqOn`.

  Contents.

    `stdLX P`                    the standard `LX`-structure on `ℕ` reading `X` by `P`
    `stdLX_lMap_toLX`            its arithmetic reduct is Foundation's `standardModel ℕ`
    `eval_Xat_std`               `X(t)` evaluates to `P` at the value of `t`
    `val_stdLX_congr`            term values do not see `P`
    `numLX`, `val_numLX`         the numerals, and that `n̄` denotes `n`
    `IsArithLit`                 closed `X`-free literal
    `eval_indep_of_isArithLit`   such a formula's truth sees neither `P` nor the assignment
    `trueArithLits`              the atomic axioms, with `literal` and `consistent`
    `trueArithLits_xfree`        no axiom is `X(t)` or `∼X(t)`
    `trueArithLits_of_true`      the two directions the ω-completeness lemma calls
    `trueArithLits_neg_of_false`
-/
import OrdinalAnalysis.Omega.Calculus
import OrdinalAnalysis.Gentzen.Idiom
import OrdinalAnalysis.Gentzen.Code

set_option autoImplicit false
set_option warn.classDefReducibility false

namespace OrdinalAnalysis

namespace Gentzen

namespace StandardLX

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### The standard model of `LX`

`LX = Language.add ℒₒᵣ XLang`, and Foundation builds a structure for a sum of
languages out of structures for the summands: `Structure.add`
(Foundation/FirstOrder/Basic/Model.lean:92).  The arithmetic summand is
`Arithmetic.standardModel ℕ` (Arithmetic/Basic/Model.lean:25) — the *canonical*
`ℒₒᵣ`-structure Foundation puts on any `[ORingStructure M]`, and hence on `ℕ`.
The `XLang` summand is the only free choice, and it is kept as a parameter. -/

/-- The fresh predicate read by `P`.  `XLang` has no function symbols
(`XLang.Func k = PEmpty`), so `func` is vacuous and, in particular, does not
depend on `P` — which is what makes `val_stdLX_congr` below true. -/
def xStruc (P : ℕ → Prop) : Structure XLang ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ r v => match r with | XRel.X => P (v 0)

/-- **The standard model of `LX`**: arithmetic standard, `X` read by `P`. -/
def stdLX (P : ℕ → Prop) : Structure LX ℕ :=
  Structure.add ℒₒᵣ XLang ℕ (str₂ := xStruc P)

variable (P Q : ℕ → Prop)

/-- The arithmetic reduct of `stdLX P` is Foundation's canonical structure on
`ℕ`, *on the nose*.  `Structure.lMap_add₁` (Model.lean:108) is `rfl`, and
`toLX = Language.Hom.add₁ ℒₒᵣ XLang` (Setup.lean:74), so the reduct is literally
the `str₁` argument that `Structure.add` was given.

This is the fact every arithmetic lemma of Foundation is transported by: an
`ℒₒᵣ`-formula `φ` satisfies
`(Semiformula.lMap toLX φ).Eval (s := stdLX P) e f ↔ φ.Eval e f`
(`Structure.eval_lMap_add₁`, Model.lean:124), the right-hand side being
evaluation in the standard model of arithmetic. -/
theorem stdLX_lMap_toLX : (stdLX P).lMap toLX = Arithmetic.standardModel ℕ := rfl

/-- A term of arithmetic transported to `LX` keeps its value: the term half of
`stdLX_lMap_toLX`, and the reason the numerals of `LX` denote what the numerals
of `ℒₒᵣ` denote. -/
@[simp] theorem val_lMap_toLX {n : ℕ} (t : Semiterm ℒₒᵣ ℕ n) (e : Fin n → ℕ) (f : ℕ → ℕ) :
    Semiterm.val (s := stdLX P) e f (Semiterm.lMap toLX t) = Semiterm.val (M := ℕ) e f t :=
  Structure.val_lMap_add₁ (str₂ := xStruc P) t e f

/-- A formula of arithmetic transported to `LX` says in `stdLX P` exactly what
it says in the standard model of arithmetic; the reading of `X` cannot
interfere.  Every axiom of `Theory.lMap toLX 𝗣𝗔⁻` is checked through this
(`Structure.eval_lMap_add₁`, Foundation/FirstOrder/Basic/Model.lean:124). -/
@[simp] theorem eval_lMap_toLX {n : ℕ} (φ : Semiformula ℒₒᵣ ℕ n) (e : Fin n → ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := stdLX P) e f (Semiformula.lMap toLX φ)
      ↔ Semiformula.Eval (M := ℕ) e f φ :=
  Structure.eval_lMap_add₁ (str₂ := xStruc P) φ e f

/-- The arithmetic relations of `stdLX P` are the standard ones. -/
theorem stdLX_rel_inl {k : ℕ} (r : (ℒₒᵣ : Language).Rel k) (v : Fin k → ℕ) :
    (stdLX P).rel (Sum.inl r) v ↔ Structure.rel (M := ℕ) r v := Iff.rfl

/-- The fresh relation of `stdLX P` is `P`. -/
theorem stdLX_rel_X (v : Fin 1 → ℕ) :
    (stdLX P).rel (Sum.inr XRel.X) v ↔ P (v 0) := Iff.rfl

/-- `Idiom.Xrel`, the interpretation of `X` in an arbitrary `LX`-structure, is
`P` in `stdLX P`.  Stated with the instance argument written out, because
`stdLX` is deliberately *not* an instance: the whole point is that `P` varies. -/
theorem xrel_stdLX (x : ℕ) : @Idiom.Xrel ℕ (stdLX P) x ↔ P x := Iff.rfl

/-- `X(t)` evaluates to `P` at the value of `t`.  This mirrors `Idiom.eval_Xat`
and is proved the same way: by definitional unfolding (`Semiformula.eval_rel` is
`Iff.of_eq rfl`) plus one `funext`.  Neither `rw` nor `simp` can do the step,
because the symbol `Sum.inr XRel.X : LX.Rel 1` is only type-correct after
`XLang.Rel 1` is unfolded to `XRel 1` at default transparency — see the note on
`Idiom.Xrel`. -/
theorem eval_Xat_std {n : ℕ} (t : Semiterm LX ℕ n) (e : Fin n → ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := stdLX P) e f (Xat t) ↔ P (Semiterm.val (s := stdLX P) e f t) := by
  have h : (Semiterm.val (s := stdLX P) e f ∘ ![t] : Fin 1 → ℕ)
      = ![Semiterm.val (s := stdLX P) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg ((stdLX P).rel (Sum.inr XRel.X)) h)

/-! ### Term values do not see `P`

`Semiterm.val` consumes the whole structure, so a term value under `stdLX P`
and under `stdLX Q` are not the same expression; but they *are* equal, because
the two structures differ only in the interpretation of a relation symbol. -/

/-- `stdLX P` and `stdLX Q` have the same function symbols: the arithmetic ones
come from the same `standardModel ℕ`, and `XLang` contributes none. -/
theorem stdLX_func {k : ℕ} (fn : LX.Func k) (w : Fin k → ℕ) :
    (stdLX P).func fn w = (stdLX Q).func fn w := by
  rcases fn with fn | fn
  · rfl
  · exact PEmpty.elim fn

/-- Consequently every term has the same value in `stdLX P` and in `stdLX Q`. -/
theorem val_stdLX_congr {n : ℕ} (e : Fin n → ℕ) (f : ℕ → ℕ) (t : Semiterm LX ℕ n) :
    Semiterm.val (s := stdLX P) e f t = Semiterm.val (s := stdLX Q) e f t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func fn v ih =>
      simp only [Semiterm.val_func, Function.comp_def, ih]
      exact stdLX_func P Q fn _

/-- A closed term has the same value under every assignment.  `Semiterm.FVar?`
is membership in `Semiterm.freeVariables`, which is the closedness notion for
terms; the bound variables of a `SyntacticTerm` are indexed by `Fin 0` and so
never occur. -/
theorem val_assign_congr {n : ℕ} (e : Fin n → ℕ) (f g : ℕ → ℕ) {t : Semiterm LX ℕ n}
    (ht : t.freeVariables = ∅) :
    Semiterm.val (s := stdLX P) e f t = Semiterm.val (s := stdLX P) e g t := by
  refine Semiterm.val_eq_of_funEqOn (s := stdLX P) t ?_
  intro x hx
  have hx' : x ∈ t.freeVariables := hx
  rw [ht] at hx'
  simp at hx'

/-- The value of a closed term is independent of both parameters. -/
theorem val_closed_std {n : ℕ} (e : Fin n → ℕ) (f g : ℕ → ℕ) {t : Semiterm LX ℕ n}
    (ht : t.freeVariables = ∅) :
    Semiterm.val (s := stdLX P) e f t = Semiterm.val (s := stdLX Q) e g t := by
  rw [val_stdLX_congr P Q e f t, val_assign_congr Q e f g ht]

/-! ### Numerals -/

/-- The numerals of `LX`: Foundation's ordered-ring numerals, available because
`Language.ORing LX` is an instance (Setup.lean:59).  They are closed terms, and
that is what makes them usable as the witnesses of the ω-rule. -/
def numLX : ℕ → SyntacticTerm LX := fun n => Semiterm.numeral n

/-- `n̄` is a closed term. -/
@[simp] theorem freeVariables_numLX (n : ℕ) : (numLX n).freeVariables = ∅ := by
  simp [numLX, Semiterm.Operator.operator]

/-- **`n̄` denotes `n`.**  The numeral of `LX` is the `toLX`-image of the
numeral of `ℒₒᵣ` (`lMap_toLX_numeral`, Gentzen/Code.lean:295), so
`Structure.val_lMap_add₁` sends the computation into the arithmetic reduct,
where `Structure.numeral_eq_numeral` (Arithmetic/Basic/Misc.lean:138) and
`Nat.numeral_eq` (ibid.:34) finish it. -/
@[simp] theorem val_numLX (n : ℕ) (f : ℕ → ℕ) :
    Semiterm.val (s := stdLX P) ![] f (numLX n) = n := by
  have h : (numLX n : Semiterm LX ℕ 0)
      = Semiterm.lMap toLX ((n : ℕ) : Semiterm ℒₒᵣ ℕ 0) := (lMap_toLX_numeral n).symm
  have key : Semiterm.val (s := stdLX P) ![] f (Semiterm.lMap toLX ((n : ℕ) : Semiterm ℒₒᵣ ℕ 0))
      = Semiterm.val (M := ℕ) ![] f ((n : ℕ) : Semiterm ℒₒᵣ ℕ 0) :=
    Structure.val_lMap_add₁ (str₂ := xStruc P) _ _ _
  rw [h, key]
  simp

/-! ### The atomic axioms

The true closed literals of the *arithmetic* part of `LX`. -/

/-- `φ` is an arithmetic literal with closed arguments: `rel r v` or `nrel r v`
with `r` a relation symbol of `ℒₒᵣ` — that is, of the form `Sum.inl r`, so
never the fresh `X` — and every `v i` closed. -/
def IsArithLit (φ : Proposition LX) : Prop :=
  ∃ (k : ℕ) (r : (ℒₒᵣ : Language).Rel k) (v : Fin k → SyntacticTerm LX),
    (φ = Semiformula.rel (Sum.inl r) v ∨ φ = Semiformula.nrel (Sum.inl r) v) ∧
      ∀ i, (v i).freeVariables = ∅

/-- The positive introduction rule for `IsArithLit`. -/
theorem isArithLit_rel {k : ℕ} (r : (ℒₒᵣ : Language).Rel k) (v : Fin k → SyntacticTerm LX)
    (hv : ∀ i, (v i).freeVariables = ∅) : IsArithLit (Semiformula.rel (Sum.inl r) v) :=
  ⟨k, r, v, Or.inl rfl, hv⟩

/-- The negative introduction rule for `IsArithLit`. -/
theorem isArithLit_nrel {k : ℕ} (r : (ℒₒᵣ : Language).Rel k) (v : Fin k → SyntacticTerm LX)
    (hv : ∀ i, (v i).freeVariables = ∅) : IsArithLit (Semiformula.nrel (Sum.inl r) v) :=
  ⟨k, r, v, Or.inr rfl, hv⟩

/-- An arithmetic literal is closed: its free variables are those of its
arguments, and those are none.  (`Semiformula.freeVariables_rel`/`_nrel`,
Foundation/FirstOrder/Basic/Syntax/Formula.lean:396,398.)

The two `rfl`-lemmas are applied by `Eq.trans`, not by `rw`: a term containing
`Sum.inl r : LX.Rel k` is not type-correct at `implicit` transparency — the trap
of `Idiom.Xrel`, here for the *arithmetic* half of the sum — so `rw` and `simp`
refuse to look inside it. -/
theorem freeVariables_of_isArithLit {φ : Proposition LX} (h : IsArithLit φ) :
    φ.freeVariables = ∅ := by
  have hb : ∀ (k : ℕ) (v : Fin k → SyntacticTerm LX), (∀ i, (v i).freeVariables = ∅) →
      (Finset.biUnion Finset.univ fun i => (v i).freeVariables) = (∅ : Finset ℕ) := by
    intro k v hv
    ext x
    simp [hv]
  obtain ⟨k, r, v, (rfl | rfl), hcl⟩ := h
  · exact (Semiformula.freeVariables_rel _ v).trans (hb k v hcl)
  · exact (Semiformula.freeVariables_nrel _ v).trans (hb k v hcl)

/-- The class is closed under negation: `∼(rel r v) = nrel r v` and
`∼(nrel r v) = rel r v` (Foundation/FirstOrder/Basic/Syntax/Formula.lean:112,114). -/
theorem isArithLit_neg {φ : Proposition LX} (h : IsArithLit φ) : IsArithLit (∼φ) := by
  obtain ⟨k, r, v, (rfl | rfl), hcl⟩ := h
  · exact ⟨k, r, v, Or.inr (Semiformula.neg_rel _ _), hcl⟩
  · exact ⟨k, r, v, Or.inl (Semiformula.neg_nrel _ _), hcl⟩

/-- **A closed `X`-free literal sees neither the reading of `X` nor the
assignment.**  This is the soundness invariant of the whole construction: the
atomic axioms may be used in a derivation whose `X` is later reinterpreted. -/
theorem eval_indep_of_isArithLit {φ : Proposition LX} (h : IsArithLit φ) (f g : ℕ → ℕ) :
    Semiformula.Eval (s := stdLX P) ![] f φ ↔ Semiformula.Eval (s := stdLX Q) ![] g φ := by
  obtain ⟨k, r, v, hφ, hcl⟩ := h
  have hv : ∀ i, Semiterm.val (s := stdLX P) ![] f (v i)
      = Semiterm.val (s := stdLX Q) ![] g (v i) := fun i => val_closed_std P Q _ f g (hcl i)
  have key : Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdLX P) ![] f (v i))
      = Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdLX Q) ![] g (v i)) :=
    congrArg (Structure.rel (M := ℕ) r) (funext hv)
  rcases hφ with rfl | rfl
  · exact Iff.of_eq key
  · exact not_congr (Iff.of_eq key)

/-- Truth in the standard model, with `X` empty and every free variable sent to
`0`.  For the formulas the axiom set is built from — closed and `X`-free — both
choices are irrelevant, by `eval_indep_of_isArithLit`; fixing them keeps the
axiom set a predicate on formulas alone. -/
def TrueN (φ : Proposition LX) : Prop :=
  Semiformula.Eval (s := stdLX fun _ => False) ![] (fun _ => 0) φ

@[simp] theorem trueN_neg (φ : Proposition LX) : TrueN (∼φ) ↔ ¬TrueN φ := by
  simp [TrueN]

/-- **The atomic axioms of the ω-calculus for `PA[X]`**: the closed arithmetic
literals true in `ℕ`.

`literal` is the first conjunct with the arithmetic symbol re-tagged by
`Sum.inl`.  `consistent` is `Eval` of a negation being the negation of `Eval`. -/
def trueArithLits : Literals LX where
  T := fun φ => IsArithLit φ ∧ TrueN φ
  literal := by
    rintro φ ⟨⟨k, r, v, hv, -⟩, -⟩
    exact ⟨k, Sum.inl r, v, hv⟩
  consistent := by
    rintro φ ⟨-, ht⟩ ⟨-, hf⟩
    exact (trueN_neg φ).mp hf ht

@[simp] theorem trueArithLits_T (φ : Proposition LX) :
    trueArithLits.T φ ↔ IsArithLit φ ∧ TrueN φ := Iff.rfl

/-! ### The interface the rest of the lower bound uses -/

/-- An axiom holds in **every** standard model, under every assignment: the
axiom set is sound for the whole family `stdLX P`. -/
theorem eval_of_trueArithLits {φ : Proposition LX} (h : trueArithLits.T φ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := stdLX P) ![] f φ :=
  (eval_indep_of_isArithLit (fun _ => False) P h.1 (fun _ => 0) f).mp h.2

/-- No axiom is an `X`-atom.  Proved semantically: an axiom's truth value does
not depend on `P`, while `X(t)` reads `P` at the value of `t`. -/
theorem trueArithLits_ne_Xat {φ : Proposition LX} (h : trueArithLits.T φ)
    (t : SyntacticTerm LX) : φ ≠ Xat t := by
  rintro rfl
  have key := eval_indep_of_isArithLit (fun _ => True) (fun _ => False)
    (φ := Xat t) h.1 (fun _ => 0) (fun _ => 0)
  rw [eval_Xat_std, eval_Xat_std] at key
  exact key.mp trivial

/-- No axiom is a negated `X`-atom either. -/
theorem trueArithLits_ne_neg_Xat {φ : Proposition LX} (h : trueArithLits.T φ)
    (t : SyntacticTerm LX) : φ ≠ ∼(Xat t) := by
  rintro rfl
  have key := eval_indep_of_isArithLit (fun _ => False) (fun _ => True)
    (φ := ∼(Xat t)) h.1 (fun _ => 0) (fun _ => 0)
  simp only [LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq,
    eval_Xat_std] at key
  exact (key.mp not_false) trivial

/-- **The axiom set is `X`-free.**  This is what makes `∼X(t)` dischargeable
only by the identity rule, which is disjunct (f) of the boundedness lemma. -/
theorem trueArithLits_xfree {φ : Proposition LX} (h : trueArithLits.T φ)
    (t : SyntacticTerm LX) : φ ≠ Xat t ∧ φ ≠ ∼(Xat t) :=
  ⟨trueArithLits_ne_Xat h t, trueArithLits_ne_neg_Xat h t⟩

/-- **First direction for ω-completeness**: a closed `X`-free literal true in
`ℕ` — under *any* reading of `X` and any assignment, which by
`eval_indep_of_isArithLit` is no extra generality — is an axiom, hence has an
ω-derivation of height `0` by `OmegaDerivable.atom`. -/
theorem trueArithLits_of_true {φ : Proposition LX} (h : IsArithLit φ) {f : ℕ → ℕ}
    (ht : Semiformula.Eval (s := stdLX P) ![] f φ) : trueArithLits.T φ :=
  ⟨h, (eval_indep_of_isArithLit P (fun _ => False) h f (fun _ => 0)).mp ht⟩

/-- **Second direction for ω-completeness**: a closed `X`-free literal *false*
in `ℕ` has a true negation, which is again a closed `X`-free literal, hence an
axiom. -/
theorem trueArithLits_neg_of_false {φ : Proposition LX} (h : IsArithLit φ) {f : ℕ → ℕ}
    (ht : ¬Semiformula.Eval (s := stdLX P) ![] f φ) : trueArithLits.T (∼φ) := by
  refine trueArithLits_of_true P (isArithLit_neg h) (f := f) ?_
  simpa using ht

end StandardLX

end Gentzen

end OrdinalAnalysis
