/-
  Task 4 of the lower bound: **ω-completeness for true closed `X`-free arithmetic**.

  Every closed, `X`-free formula of `LX` that is true in the standard model has a
  cut-free derivation in the ω-calculus over the atomic axioms `trueArithLits`.
  This is the master lemma of `gentzen_lower_spec.md` §B.1: it discharges every
  row of the axiom table except `succInd`, and it is what makes the embedding of
  `paLX` into the ω-calculus possible at all.

  Three things about the shape.

  * **The height is finite.**  `Semiformula.complexity` drops strictly at every
    rule the proof fires, and — this is the point — `Semiformula.complexity_rew`
    says a rewriting does not change it, so the ω-rule's premises
    `φ/[n̄]` all have complexity `φ.complexity`, *uniformly in `n`*.  A single
    finite bound therefore lies above every instance, and the height can be taken
    to be `NONote.ofNat φ.complexity`.  No `ω`-power, no natural sum, no
    successor tower: the ω-rule needs individual premise ordinals only when the
    premises really do grow with `n`, which happens for the induction axiom
    (task 7) and not here.  `hgt_lt_omega` records that the bound is `< ω`,
    which is what the spec's axiom table claims for the `𝗣𝗔⁻` and `𝗘𝗤` rows.

  * **`X`-freeness must be syntactic.**  The atomic case hands
    `StandardLX.trueArithLits_of_true` an `IsArithLit`, and that is a statement
    about the *symbol* `Sum.inl r`, not about truth values.  A semantic reading
    of "`φ` does not see `P`" — the reading `StandardLX` uses for its own
    soundness lemmas — would be closed under substitution just as well but
    could not produce an axiom.  So `XFree` is defined by recursion on the
    formula, with `IsArithRel` at the leaves.

  * **Every sequent is a singleton.**  The induction derives `[φ]` and nothing
    else; the only structural step is the weakening `[φ] ⊆ [φ, ψ]` that the `or`
    rule needs, and `OmegaDerivable.contraction` supplies it.  In particular no
    context has to be carried through the ω-rule, which is where a context would
    have cost a substitution lemma.

  Contents.

    `IsArithRel`, `XFree`         `X`-freeness, and its closure under `∼` and rewriting
    `xFree_lMap_toLX`             everything transported from arithmetic is `X`-free
    `isArithLit_of_xFree_rel`     the bridge to `StandardLX.IsArithLit` at the leaves
    `eval_all_numLX`              `⊨ ∀¹ φ ↔ ∀ n, ⊨ φ/[n̄]` — the ω-rule's semantics
    `hgt`, `hgt_lt_omega`         the height, and that it is finite
    `omega_complete`              **the master lemma**
    `omega_complete_neg`          its negative form
    `omega_complete_sentence`     the shape `Theory.lMap toLX 𝗣𝗔⁻` arrives in
-/
import OrdinalAnalysis.Gentzen.StandardLX
import OrdinalAnalysis.Gentzen.LowerSyntax

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Gentzen

namespace OmegaTruth

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.StandardLX

/-! ### Finite heights

`NONote.ofNat` is mathlib's embedding of `ℕ` into the notations
(`Mathlib/SetTheory/Ordinal/Notation.lean`), and `ONote.repr_ofNat` computes its
`repr`.  Since the order on `NONote` *is* the order on `repr`, both facts below
are one unfolding away. -/

theorem ofNat_lt_ofNat {m n : ℕ} (h : m < n) :
    NONote.ofNat m < NONote.ofNat n := by
  show ONote.repr (ONote.ofNat m) < ONote.repr (ONote.ofNat n)
  rw [ONote.repr_ofNat, ONote.repr_ofNat]
  exact_mod_cast h

/-- `ω`, as a normal-form notation.  Defined here rather than imported: the only
thing needed of it is that it lies above every `NONote.ofNat n`. -/
def omegaNO : NONote := NONote.omegaPow (NONote.ofNat 1)

theorem ofNat_lt_omegaNO (n : ℕ) : NONote.ofNat n < omegaNO := by
  have h1 : ONote.repr (NONote.ofNat 1).1 = 1 := by
    show ONote.repr (ONote.ofNat 1) = 1
    simp
  show ONote.repr (ONote.ofNat n) < ONote.repr (NONote.omegaPow (NONote.ofNat 1)).1
  rw [NONote.repr_omegaPow, h1, ONote.repr_ofNat, Ordinal.opow_one]
  exact Ordinal.natCast_lt_omega0 n

/-! ### `X`-freeness

The fresh predicate enters `LX = Language.add ℒₒᵣ XLang` as `Sum.inr XRel.X`, so
"`φ` does not mention `X`" is "every relation symbol of `φ` is a `Sum.inl`". -/

/-- `r` is an arithmetic relation symbol of `LX` — not the fresh `X`. -/
def IsArithRel {k : ℕ} (r : LX.Rel k) : Prop :=
  ∃ r' : (ℒₒᵣ : Language).Rel k, r = Sum.inl r'

/-- The introduction rule.  Written out because a term containing
`Sum.inl r : LX.Rel k` is not type-correct at `implicit` transparency, so `simp`
will not build it by unfolding `IsArithRel` itself (a known pitfall). -/
@[simp] theorem isArithRel_inl {k : ℕ} (r : (ℒₒᵣ : Language).Rel k) :
    IsArithRel (Sum.inl r : LX.Rel k) := ⟨r, rfl⟩

/-- **`φ` mentions no `X`.**  Structural — so that it is closed under
substitution of numerals, and so that its atomic case produces a
`StandardLX.IsArithLit`.

Stated for an arbitrary variable type `ξ`, not just for `ℕ`: the embedding of
`paLX` (task 6) has to know that `X`-freeness survives `Rewriting.emb`, which
crosses from `Sentence LX` to `Proposition LX`, and that is the same lemma as
survival of `Rew.subst`. -/
def XFree {ξ : Type*} {n : ℕ} : Semiformula LX ξ n → Prop
  |                   ⊤ => True
  |                   ⊥ => True
  | Semiformula.rel r _ => IsArithRel r
  | Semiformula.nrel r _ => IsArithRel r
  |               φ ⋏ ψ => XFree φ ∧ XFree ψ
  |               φ ⋎ ψ => XFree φ ∧ XFree ψ
  |                ∀¹ φ => XFree φ
  |                ∃¹ φ => XFree φ

@[simp] theorem xFree_verum {ξ : Type*} {n : ℕ} : XFree (⊤ : Semiformula LX ξ n) := trivial

@[simp] theorem xFree_falsum {ξ : Type*} {n : ℕ} : XFree (⊥ : Semiformula LX ξ n) := trivial

@[simp] theorem xFree_rel {ξ : Type*} {n k : ℕ} (r : LX.Rel k) (v : Fin k → Semiterm LX ξ n) :
    XFree (Semiformula.rel r v) ↔ IsArithRel r := Iff.rfl

@[simp] theorem xFree_nrel {ξ : Type*} {n k : ℕ} (r : LX.Rel k) (v : Fin k → Semiterm LX ξ n) :
    XFree (Semiformula.nrel r v) ↔ IsArithRel r := Iff.rfl

@[simp] theorem xFree_and {ξ : Type*} {n : ℕ} (φ ψ : Semiformula LX ξ n) :
    XFree (φ ⋏ ψ) ↔ XFree φ ∧ XFree ψ := Iff.rfl

@[simp] theorem xFree_or {ξ : Type*} {n : ℕ} (φ ψ : Semiformula LX ξ n) :
    XFree (φ ⋎ ψ) ↔ XFree φ ∧ XFree ψ := Iff.rfl

@[simp] theorem xFree_all {ξ : Type*} {n : ℕ} (φ : Semiformula LX ξ (n + 1)) :
    XFree (∀¹ φ) ↔ XFree φ := Iff.rfl

@[simp] theorem xFree_exs {ξ : Type*} {n : ℕ} (φ : Semiformula LX ξ (n + 1)) :
    XFree (∃¹ φ) ↔ XFree φ := Iff.rfl

/-- `X`-freeness is closed under negation: de Morgan swaps `rel` with `nrel` and
the quantifiers with each other, and none of that touches a symbol. -/
@[simp] theorem xFree_neg {ξ : Type*} {n : ℕ} (φ : Semiformula LX ξ n) :
    XFree (∼φ) ↔ XFree φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **`X`-freeness is closed under rewriting.**  This is what the ω-rule needs:
the premises `φ/[n̄]` are `X`-free whenever `∀¹ φ` is.  It also covers
`Rewriting.emb`, `Rew.free`, `Rew.shift` and `Rew.rewrite`, which is what the
embedding of `paLX` will apply it to. -/
theorem xFree_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LX ξ₁ n₁ ξ₂ n₂)
    {φ : Semiformula LX ξ₁ n₁} (h : XFree φ) : XFree (ω ▹ φ) := by
  revert h
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => intro _; simp
  | hfalsum => intro _; simp
  | hrel r v => intro h; rw [Semiformula.rew_rel]; simpa using h
  | hnrel r v => intro h; rw [Semiformula.rew_nrel]; simpa using h
  | hand φ ψ ihφ ihψ => intro h; simp only [LogicalConnective.HomClass.map_and, xFree_and]
                        exact ⟨ihφ ω h.1, ihψ ω h.2⟩
  | hor φ ψ ihφ ihψ => intro h; simp only [LogicalConnective.HomClass.map_or, xFree_or]
                       exact ⟨ihφ ω h.1, ihψ ω h.2⟩
  | hall φ ih => intro h; simp only [Rewriting.app_all, xFree_all]; exact ih ω.q h
  | hexs φ ih => intro h; simp only [Rewriting.app_exs, xFree_exs]; exact ih ω.q h

/-- A sentence embedded as a proposition stays `X`-free. -/
theorem xFree_emb {ξ : Type*} {n : ℕ} {σ : Semiformula LX Empty n} (h : XFree σ) :
    XFree (Rewriting.emb σ : Semiformula LX ξ n) :=
  xFree_rew Rew.emb h

/-- **Everything transported from arithmetic is `X`-free.**

`toLX = Language.Hom.add₁ ℒₒᵣ XLang` tags every symbol with `Sum.inl`
(`Language.rel_add₁`), which is exactly `IsArithRel`.  This is how the axioms of
`Theory.lMap toLX 𝗣𝗔⁻` — and the arithmetic half of `𝗘𝗤 LX` — reach the master
lemma without any further syntactic analysis. -/
@[simp] theorem xFree_lMap_toLX {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) :
    XFree (Semiformula.lMap toLX φ) := by
  induction φ using Semiformula.rec' with
  | hverum => simp only [LogicalConnective.HomClass.map_top]; exact xFree_verum
  | hfalsum => simp only [LogicalConnective.HomClass.map_bot]; exact xFree_falsum
  | hrel r v => simp only [Semiformula.lMap_rel, xFree_rel]; exact ⟨r, rfl⟩
  | hnrel r v => simp only [Semiformula.lMap_nrel, xFree_nrel]; exact ⟨r, rfl⟩
  | hand φ ψ ihφ ihψ =>
      simp only [LogicalConnective.HomClass.map_and, xFree_and]; exact ⟨ihφ, ihψ⟩
  | hor φ ψ ihφ ihψ =>
      simp only [LogicalConnective.HomClass.map_or, xFree_or]; exact ⟨ihφ, ihψ⟩
  | hall φ ih => simp only [Semiformula.lMap_all, xFree_all]; exact ih
  | hexs φ ih => simp only [Semiformula.lMap_exs, xFree_exs]; exact ih

/-! ### From an `X`-free closed atom to an axiom

`StandardLX.IsArithLit` wants the symbol in the form `Sum.inl r'` *and* every
argument closed.  The second half has to be extracted before `IsArithRel` is
destructed: once the symbol has been rewritten to `Sum.inl r'` the term is no
longer type-correct at `implicit` transparency and `rw` refuses to look at it
(a known pitfall). -/

private theorem closed_args {k : ℕ} {v : Fin k → SyntacticTerm LX}
    (hc : (Finset.biUnion Finset.univ fun i => (v i).freeVariables) = (∅ : Finset ℕ))
    (i : Fin k) : (v i).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hmem : x ∈ (Finset.biUnion Finset.univ fun i => (v i).freeVariables) :=
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  rw [hc] at hmem
  exact Finset.notMem_empty x hmem

theorem isArithLit_of_xFree_rel {k : ℕ} (r : LX.Rel k) (v : Fin k → SyntacticTerm LX)
    (hX : IsArithRel r) (hc : (Semiformula.rel r v).freeVariables = ∅) :
    IsArithLit (Semiformula.rel r v) := by
  have hv : ∀ i, (v i).freeVariables = ∅ :=
    closed_args ((Semiformula.freeVariables_rel r v).symm.trans hc)
  obtain ⟨r', rfl⟩ := hX
  exact isArithLit_rel r' v hv

theorem isArithLit_of_xFree_nrel {k : ℕ} (r : LX.Rel k) (v : Fin k → SyntacticTerm LX)
    (hX : IsArithRel r) (hc : (Semiformula.nrel r v).freeVariables = ∅) :
    IsArithLit (Semiformula.nrel r v) := by
  have hv : ∀ i, (v i).freeVariables = ∅ :=
    closed_args ((Semiformula.freeVariables_nrel r v).symm.trans hc)
  obtain ⟨r', rfl⟩ := hX
  exact isArithLit_nrel r' v hv

/-- The converse direction at the leaves: `StandardLX`'s own notion of a closed
`X`-free literal is `X`-free in the sense of this file. -/
theorem xFree_of_isArithLit {φ : Proposition LX} (h : IsArithLit φ) : XFree φ := by
  obtain ⟨k, r, v, (rfl | rfl), -⟩ := h
  · exact ⟨r, rfl⟩
  · exact ⟨r, rfl⟩

/-! ### Evaluation

The universe of `stdLX P` is `ℕ`, and `numLX n` denotes `n` (`val_numLX`), so
*every* element of the universe is the value of a numeral.  That is the whole
content of the ω-rule's soundness, and the two lemmas below are the only place
the standard model is used. -/

variable (P : ℕ → Prop) (f : ℕ → ℕ)

@[simp] theorem eval_falsum_iff :
    ¬ Semiformula.Eval (s := stdLX P) ![] f (⊥ : Proposition LX) := by simp

theorem eval_and_iff (φ ψ : Proposition LX) :
    Semiformula.Eval (s := stdLX P) ![] f (φ ⋏ ψ)
      ↔ Semiformula.Eval (s := stdLX P) ![] f φ ∧ Semiformula.Eval (s := stdLX P) ![] f ψ := by
  simp

theorem eval_or_iff (φ ψ : Proposition LX) :
    Semiformula.Eval (s := stdLX P) ![] f (φ ⋎ ψ)
      ↔ Semiformula.Eval (s := stdLX P) ![] f φ ∨ Semiformula.Eval (s := stdLX P) ![] f ψ := by
  simp

theorem eval_neg_iff (φ : Proposition LX) :
    Semiformula.Eval (s := stdLX P) ![] f (∼φ)
      ↔ ¬ Semiformula.Eval (s := stdLX P) ![] f φ := by
  simp

/-- Substituting the numeral `n̄` is evaluating at `n`. -/
theorem eval_subst_numLX (φ : Semiproposition LX 1) (n : ℕ) :
    Semiformula.Eval (s := stdLX P) ![] f (φ/[numLX n])
      ↔ Semiformula.Eval (s := stdLX P) ![(n : ℕ)] f φ := by
  have h : (Semiterm.val (s := stdLX P) ![] f ∘ ![numLX n] : Fin 1 → ℕ) = ![(n : ℕ)] := by
    have h₁ : (Semiterm.val (s := stdLX P) ![] f ∘ ![numLX n] : Fin 1 → ℕ)
        = ![Semiterm.val (s := stdLX P) ![] f (numLX n)] := Matrix.comp₁ _
    rw [h₁, val_numLX]
  rw [Semiformula.eval_substs, h]

/-- **The ω-rule is sound and complete for the standard model**: `∀¹ φ` is true
exactly when every numeral instance is. -/
theorem eval_all_numLX (φ : Semiproposition LX 1) :
    Semiformula.Eval (s := stdLX P) ![] f (∀¹ φ)
      ↔ ∀ n : ℕ, Semiformula.Eval (s := stdLX P) ![] f (φ/[numLX n]) := by
  simp only [Semiformula.eval_all, eval_subst_numLX]

/-- The dual: `∃¹ φ` is true exactly when some numeral instance is. -/
theorem eval_exs_numLX (φ : Semiproposition LX 1) :
    Semiformula.Eval (s := stdLX P) ![] f (∃¹ φ)
      ↔ ∃ n : ℕ, Semiformula.Eval (s := stdLX P) ![] f (φ/[numLX n]) := by
  simp only [Semiformula.eval_ex, eval_subst_numLX]

/-! ### Case analysis on a proposition

`Semiformula.cases'` is stated for the whole family `∀ n, Semiformula L ξ n`,
which does not fit a goal whose index is the literal `0`.  The specialisation
below is stated in *connective* form — `φ ⋏ ψ` rather than `Semiformula.and φ ψ`
— so that the `simp` lemmas of `XFree`, `freeVariables` and `Eval`, all of which
are indexed by the connective, fire on the resulting goals. -/

theorem cases0 {C : Proposition LX → Prop}
    (hverum : C ⊤) (hfalsum : C ⊥)
    (hrel : ∀ (k : ℕ) (r : LX.Rel k) (v : Fin k → SyntacticTerm LX),
      C (Semiformula.rel r v))
    (hnrel : ∀ (k : ℕ) (r : LX.Rel k) (v : Fin k → SyntacticTerm LX),
      C (Semiformula.nrel r v))
    (hand : ∀ φ ψ : Proposition LX, C (φ ⋏ ψ))
    (hor : ∀ φ ψ : Proposition LX, C (φ ⋎ ψ))
    (hall : ∀ φ : Semiproposition LX 1, C (∀¹ φ))
    (hexs : ∀ φ : Semiproposition LX 1, C (∃¹ φ)) :
    ∀ φ : Proposition LX, C φ
  | Semiformula.verum => hverum
  | Semiformula.falsum => hfalsum
  | Semiformula.rel r v => hrel _ r v
  | Semiformula.nrel r v => hnrel _ r v
  | Semiformula.and φ ψ => hand φ ψ
  | Semiformula.or φ ψ => hor φ ψ
  | Semiformula.all φ => hall φ
  | Semiformula.exs φ => hexs φ

/-! ### The master lemma -/

/-- The ω-height assigned to a formula: its complexity, as a notation.

Strictly decreasing at every rule of the proof below, and — by
`Semiformula.complexity_rew` — *constant* across the premises of the ω-rule,
which is what lets a single finite ordinal bound all of them. -/
def hgt (φ : Proposition LX) : NONote := NONote.ofNat φ.complexity

theorem hgt_lt_omega (φ : Proposition LX) : hgt φ < omegaNO :=
  ofNat_lt_omegaNO _

@[simp] theorem hgt_neg (φ : Proposition LX) : hgt (∼φ) = hgt φ := by
  simp [hgt]

/-- The induction, with the height fixed by an external bound on the complexity
so that the recursion is on `ℕ` rather than on the formula. -/
private theorem omega_complete_aux :
    ∀ (c : ℕ) (φ : Proposition LX), φ.complexity ≤ c → XFree φ → φ.freeVariables = ∅ →
      Semiformula.Eval (s := stdLX P) ![] f φ →
      OmegaDerivable trueArithLits (Instantiation.raw numLX) 0 (NONote.ofNat c) [φ] := by
  intro c
  induction c with
  | zero =>
      intro φ
      refine cases0 (C := fun φ => φ.complexity ≤ 0 → XFree φ → φ.freeVariables = ∅ →
        Semiformula.Eval (s := stdLX P) ![] f φ →
        OmegaDerivable trueArithLits (Instantiation.raw numLX) 0 (NONote.ofNat 0) [φ])
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ φ
      · intro _ _ _ _; exact .verum
      · intro _ _ _ ht; exact absurd ht (by simp)
      · intro k r v _ hX hc ht
        exact .atom (trueArithLits_of_true P (isArithLit_of_xFree_rel r v hX hc) ht)
      · intro k r v _ hX hc ht
        exact .atom (trueArithLits_of_true P (isArithLit_of_xFree_nrel r v hX hc) ht)
      · intro φ' ψ' hcx _ _ _; simp at hcx
      · intro φ' ψ' hcx _ _ _; simp at hcx
      · intro φ' hcx _ _ _; simp at hcx
      · intro φ' hcx _ _ _; simp at hcx
  | succ c ih =>
      intro φ
      refine cases0 (C := fun φ => φ.complexity ≤ c + 1 → XFree φ → φ.freeVariables = ∅ →
        Semiformula.Eval (s := stdLX P) ![] f φ →
        OmegaDerivable trueArithLits (Instantiation.raw numLX) 0 (NONote.ofNat (c + 1)) [φ])
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ φ
      · intro _ _ _ _; exact .verum
      · intro _ _ _ ht; exact absurd ht (by simp)
      · intro k r v _ hX hc ht
        exact .atom (trueArithLits_of_true P (isArithLit_of_xFree_rel r v hX hc) ht)
      · intro k r v _ hX hc ht
        exact .atom (trueArithLits_of_true P (isArithLit_of_xFree_nrel r v hX hc) ht)
      · -- `φ ⋏ ψ`: both conjuncts are true, and both premises are needed.
        intro φ' ψ' hcx hX hc ht
        simp only [Semiformula.complexity_and] at hcx
        simp only [xFree_and] at hX
        simp only [Semiformula.freeVariables_and, Finset.union_eq_empty] at hc
        rw [eval_and_iff] at ht
        exact .and (ofNat_lt_ofNat (Nat.lt_succ_self c)) (ofNat_lt_ofNat (Nat.lt_succ_self c))
          (ih φ' (by omega) hX.1 hc.1 ht.1) (ih ψ' (by omega) hX.2 hc.2 ht.2)
      · -- `φ ⋎ ψ`: one disjunct is true; the other is added by weakening.
        intro φ' ψ' hcx hX hc ht
        simp only [Semiformula.complexity_or] at hcx
        simp only [xFree_or] at hX
        simp only [Semiformula.freeVariables_or, Finset.union_eq_empty] at hc
        refine .or (ofNat_lt_ofNat (Nat.lt_succ_self c)) ?_
        rcases (eval_or_iff P f φ' ψ').mp ht with h | h
        · exact .contraction (by simp) (ih φ' (by omega) hX.1 hc.1 h)
        · exact .contraction (by simp) (ih ψ' (by omega) hX.2 hc.2 h)
      · -- `∀¹ φ`: every numeral instance is true, closed and `X`-free.
        intro φ' hcx hX hc ht
        simp only [Semiformula.complexity_all] at hcx
        simp only [xFree_all] at hX
        simp only [Semiformula.freeVariables_all] at hc
        refine .omegaRule (fun _ => NONote.ofNat c)
          (fun _ => ofNat_lt_ofNat (Nat.lt_succ_self c)) (fun n => ?_)
        refine ih (φ'/[numLX n]) ?_ (xFree_rew _ hX) ?_ ((eval_all_numLX P f φ').mp ht n)
        · simp only [Semiformula.complexity_rew]; omega
        · refine LowerSyntax.freeVariables_rew_eq_empty _ hc ?_
          intro i
          have hi : i = 0 := Subsingleton.elim i 0
          subst hi
          simp
      · -- `∃¹ φ`: some numeral instance is true.
        intro φ' hcx hX hc ht
        simp only [Semiformula.complexity_exs] at hcx
        simp only [xFree_exs] at hX
        simp only [Semiformula.freeVariables_exs] at hc
        obtain ⟨n, hn⟩ := (eval_exs_numLX P f φ').mp ht
        refine .exs n (ofNat_lt_ofNat (Nat.lt_succ_self c)) ?_
        refine ih (φ'/[numLX n]) ?_ (xFree_rew _ hX) ?_ hn
        · simp only [Semiformula.complexity_rew]; omega
        · refine LowerSyntax.freeVariables_rew_eq_empty _ hc ?_
          intro i
          have hi : i = 0 := Subsingleton.elim i 0
          subst hi
          simp

/-- **ω-completeness for true closed `X`-free arithmetic.**

Every closed, `X`-free formula true in a standard model `stdLX P` has a cut-free
ω-derivation over the true closed arithmetic literals, of height its own
complexity — in particular of finite height (`hgt_lt_omega`).

The reading `P` of `X` and the assignment `f` are free parameters and neither
occurs in the conclusion: for an `X`-free closed formula the truth value does
not depend on them (`StandardLX.eval_indep_of_isArithLit` is the atomic case of
that fact), so any choice may be used to *establish* the hypothesis. -/
theorem omega_complete (φ : Proposition LX) (hX : XFree φ) (hc : φ.freeVariables = ∅)
    (ht : Semiformula.Eval (s := stdLX P) ![] f φ) :
    OmegaDerivable trueArithLits (Instantiation.raw numLX) 0 (hgt φ) [φ] :=
  omega_complete_aux P f φ.complexity φ le_rfl hX hc ht

/-- The same at any height above `hgt φ`; `mono_ord` in the form the embedding
uses, where a single ordinal has to cover a whole finite set of axioms. -/
theorem omega_complete_of_le (φ : Proposition LX) (hX : XFree φ) (hc : φ.freeVariables = ∅)
    (ht : Semiformula.Eval (s := stdLX P) ![] f φ) {α : NONote} (hα : hgt φ ≤ α) :
    OmegaDerivable trueArithLits (Instantiation.raw numLX) 0 α [φ] :=
  (omega_complete P f φ hX hc ht).mono_ord hα

/-- **The negative form**: a closed `X`-free formula *false* in the standard
model has its negation derived, at the same height.  Immediate from the positive
form, since `∼φ` is closed, `X`-free and true exactly when `φ` is false. -/
theorem omega_complete_neg (φ : Proposition LX) (hX : XFree φ) (hc : φ.freeVariables = ∅)
    (hf : ¬ Semiformula.Eval (s := stdLX P) ![] f φ) :
    OmegaDerivable trueArithLits (Instantiation.raw numLX) 0 (hgt φ) [∼φ] := by
  have h := omega_complete P f (∼φ) (by simpa using hX) (by simpa using hc)
    ((eval_neg_iff P f φ).mpr hf)
  simpa using h

/-- The version stated against `StandardLX.TrueN`, the fixed reading of "true in
`ℕ`" that the axiom set `trueArithLits` is defined by.  This is the form the
axiom table of §B.1 consumes. -/
theorem omega_complete_trueN (φ : Proposition LX) (hX : XFree φ) (hc : φ.freeVariables = ∅)
    (ht : TrueN φ) :
    OmegaDerivable trueArithLits (Instantiation.raw numLX) 0 (hgt φ) [φ] :=
  omega_complete (fun _ => False) (fun _ => 0) φ hX hc ht

/-- The negative form against `TrueN`. -/
theorem omega_complete_trueN_neg (φ : Proposition LX) (hX : XFree φ)
    (hc : φ.freeVariables = ∅) (hf : ¬ TrueN φ) :
    OmegaDerivable trueArithLits (Instantiation.raw numLX) 0 (hgt φ) [∼φ] :=
  omega_complete_neg (fun _ => False) (fun _ => 0) φ hX hc hf

/-- **The form the axiom table of §B.1 consumes.**  An arithmetic *sentence*
true in `ℕ`, transported into `LX` and embedded as a proposition, has a cut-free
ω-derivation.  `X`-freeness is `xFree_lMap_toLX`, closedness is
`Semiformula.freeVariables_emb`, and truth transfers by
`StandardLX.eval_lMap_toLX`.

This is the `Theory.lMap toLX 𝗣𝗔⁻` row of the axiom table, and — the arithmetic
axioms of `𝗘𝗤 LX` having the same shape — most of the row below it. -/
theorem omega_complete_sentence (σ : Sentence ℒₒᵣ)
    (h : Semiformula.Eval (M := ℕ) ![] Empty.elim σ) :
    OmegaDerivable trueArithLits (Instantiation.raw numLX) 0
      (hgt (Rewriting.emb (Semiformula.lMap toLX σ)))
      [(Rewriting.emb (Semiformula.lMap toLX σ) : Proposition LX)] := by
  have e : (Rewriting.emb (Semiformula.lMap toLX σ) : Proposition LX)
      = Semiformula.lMap toLX (Rewriting.emb σ : Semiformula ℒₒᵣ ℕ 0) :=
    (Semiformula.lMap_emb σ).symm
  rw [e]
  refine omega_complete (fun _ => False) (fun _ => 0) _ (xFree_lMap_toLX _) (by simp) ?_
  simpa using h

end OmegaTruth

end Gentzen

end OrdinalAnalysis
