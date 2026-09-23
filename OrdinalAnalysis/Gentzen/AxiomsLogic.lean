/-
  **The logical axioms of `PA[X]`**.

  `paLX = 𝗘𝗤 LX ∪ (Theory.lMap toLX 𝗣𝗔⁻ ∪ InductionScheme LX Set.univ)`, and
  `Embed.lean` replays a `paLX`-derivation in the ω-calculus rule by rule,
  appealing at each leaf to a derivation of the axiom used there.  This file
  supplies those derivations for the first two of the three blocks; the
  induction scheme is the one that needs height `ω + c` and is done separately.

  Both blocks land in the *evaluating* calculus
  `OmegaDerivable trueArithLits evInst`, the one the embedding produces, both
  are cut-free (rank `0`), and both are of finite height.  The height is
  existentially quantified: the caller takes the maximum over the finitely many
  axioms of the derivation it is replaying.

  Three things about the shape.

  * **`𝗣𝗔⁻` is free.**  Its axioms arrive as `Semiformula.lMap toLX τ` for a
    `τ ∈ 𝗣𝗔⁻`, `τ` is true in `ℕ`, and `EvInst.omega_complete_sentence_ev` is
    exactly the statement that such a sentence has a cut-free ω-derivation.
    Nothing else happens.

  * **`𝗘𝗤 LX` splits.**  Four of the five axiom shapes — `refl`, `symm`,
    `trans`, `funcExt f`, and `relExt r` for an *arithmetic* `r` — contain no
    relation symbol but `=`, so they are `X`-free (`OmegaTruth.XFree`) and go
    through the same ω-completeness lemma.  `funcExt` needs no case analysis on
    `f`: a function symbol is invisible to `XFree`, so the fresh ones (there are
    none, but the proof does not have to know that) cost nothing.  Truth is
    uniform over the whole family `stdLX P` and is Foundation's own
    `Structure.Eq.models_eq`, because `stdLX P` reads `=` as equality on `ℕ` on
    the nose — `⟨fun _ _ => iff_of_eq rfl⟩`, the very proof Foundation gives for
    `standardModel`.

  * **`relExt X` is the exception**, and the only point of the whole lower bound
    where an axiom mentioning the fresh predicate has to be derived by hand.  It
    is `∀x ∀y ((x = y ⋏ ⊤) → (X x → X y))`.  Two ω-rules instantiate it at
    numerals `m̄` and `n̄`, three `or` rules expose the members, and then the
    argument splits: if `m = n` the identity rule discharges `∼X(n̄), X(n̄)`; if
    `m ≠ n` then `n̄ = m̄` is a false closed arithmetic literal, so `∼(n̄ = m̄)` is
    an axiom of `trueArithLits`.  The ω-rules' premises do not grow with the
    numeral — the case split changes the derivation but not its height — so the
    whole thing stays finite, at `NONote.ofNat 5`.

  The `⊥` coming from `∼⊤` is a passenger throughout: carried in the context,
  never used.

  Two traps of the pitfall notes govern the proofs.  The symbol
  `Sum.inr XRel.X : LX.Rel 1` is not type-correct at `implicit` transparency, so
  `rw`/`simp` must never see `Semiformula.rel (Sum.inr XRel.X) ![t]`: the atoms
  are wrapped in the opaque `XA`/`nXA` of this file (and, for symmetry,
  `eqA`/`neqA`), every passage into that shape is a `congrArg` discharged by
  `exact`, and afterwards `simp` matches on those heads alone.  And `![v 0]` is
  never definitionally `v` for `v : Fin 1 → _`; Foundation writes the matrices of
  `Eq.relExt` as `fun i ↦ #(i.addCast k)`, so reaching `![#0]` costs a `funext`.

  Contents.

    `eval_of_eqAxiom`                  every `𝗘𝗤 LX` axiom holds in every `stdLX P`
    `xFree_eqRefl` … `xFree_relExt_inl` the four `X`-free axiom shapes
    `derivable_of_xFree_eqAxiom`       the ω-completeness route
    `paMinus_axiom_derivable`          **the `𝗣𝗔⁻` half**
    `eqA`, `neqA`, `XA`, `nXA`         the atoms, kept opaque
    `relExtX_eq`, `emb_relExtX`        `relExt X` in explicit form
    `subst_relX2`, `subst_relX1`       the two numeral instantiations
    `relX0_base`, `relX0_derivable`    the sequent both ω-rules reduce to
    `relExtX_derivable`                `relExt X`, by hand
    `eq_axiom_derivable`               **the `𝗘𝗤 LX` half**
-/
import OrdinalAnalysis.Gentzen.EvInst

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.AxiomsLogic

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen OrdinalAnalysis.Gentzen.StandardLX
open OrdinalAnalysis.Gentzen.Evaluate OrdinalAnalysis.Gentzen.OmegaTruth
open OrdinalAnalysis.Gentzen.EvInst

/-! ### Truth of the equality axioms

`stdLX P` reads `=` as equality on `ℕ` — its arithmetic reduct is
`Arithmetic.standardModel ℕ` on the nose (`StandardLX.stdLX_lMap_toLX` is
`rfl`) — so it models `𝗘𝗤 LX` for every reading `P` of the fresh predicate.
That includes `relExt X`, which is true there even though it is not `X`-free;
the reason `relExt X` still has to be derived by hand is that ω-completeness,
not truth, is what fails for it. -/

set_option linter.style.haveILetI false in
/-- **Every axiom of `𝗘𝗤 LX` holds in `stdLX P`.**

`letI`, not `have`: the local instance must keep its body, or the conclusion's
`(s := stdLX P)` stops matching the one `Theory.models` produces. -/
theorem eval_of_eqAxiom (P : ℕ → Prop) {σ : Sentence LX} (h : σ ∈ 𝗘𝗤 LX) :
    Semiformula.Eval (s := stdLX P) ![] Empty.elim σ := by
  letI : Structure LX ℕ := stdLX P
  haveI : Structure.Eq LX ℕ := ⟨fun _ _ => iff_of_eq rfl⟩
  haveI : ℕ↓[LX] ⊧* 𝗘𝗤 LX := Structure.Eq.models_eq LX ℕ
  exact Theory.models ℕ (𝗘𝗤 LX) h

/-! ### `X`-freeness helpers

`XFree` is structural, so it has to be pushed through the shapes the axioms of
`𝗘𝗤` are built from: the equality *operator*, implication, the universal
closure, and `Matrix.conj`.  The last two are recursions on the arity, and both
defining equations (`allClosure_succ`, `Matrix.conj_cons`) are `rfl`. -/

/-- The symbol `=` of `LX` is arithmetic: the `Language.ORing LX` instance of
`Setup.lean` sets it to `Sum.inl Language.Eq.eq`. -/
theorem isArithRel_eq : IsArithRel (Language.Eq.eq : LX.Rel 2) :=
  ⟨Language.Eq.eq, rfl⟩

/-- An equality atom is `X`-free.  The binder notation `“t = u”` produces the
*operator*, and `Semiformula.Operator.eq_def` is what turns it back into a
relation symbol; this is the only leaf the axioms of `𝗘𝗤` have. -/
theorem xFree_eqOp {ξ : Type*} {n : ℕ} (t u : Semiterm LX ξ n) :
    XFree ((Semiformula.Operator.Eq.eq : Semiformula.Operator LX 2).operator ![t, u]) := by
  rw [Semiformula.Operator.eq_def]
  exact isArithRel_eq

/-- Not `Iff.rfl`: `φ 🡒 ψ = ∼φ ⋎ ψ` *is* `rfl`, but `XFree (∼φ)` reduces to
`XFree φ` only through `xFree_neg`. -/
theorem xFree_imp {ξ : Type*} {n : ℕ} (φ ψ : Semiformula LX ξ n) :
    XFree (φ 🡒 ψ) ↔ XFree φ ∧ XFree ψ := by
  have h : (φ 🡒 ψ) = ∼φ ⋎ ψ := rfl
  rw [h, xFree_or, xFree_neg]

/-- `X`-freeness survives the universal closure. -/
theorem xFree_allClosure {ξ : Type*} :
    ∀ {n : ℕ} (φ : Semiformula LX ξ n), XFree φ → XFree (∀¹* φ)
  | 0, _, h => h
  | _ + 1, φ, h => xFree_allClosure (∀¹ φ) h

/-- `X`-freeness of a finite conjunction. -/
theorem xFree_conj {ξ : Type*} {n : ℕ} :
    ∀ {k : ℕ} (v : Fin k → Semiformula LX ξ n), (∀ i, XFree (v i)) → XFree (Matrix.conj v)
  | 0, _, _ => trivial
  | _ + 1, v, h => ⟨h 0, xFree_conj (Matrix.vecTail v) fun i => h i.succ⟩

/-! ### The `X`-free equality axioms

Every axiom of `𝗘𝗤 LX` except `relExt (Sum.inr XRel.X)` is `X`-free.  For
`funcExt f` this holds for *every* `f`, the fresh function symbols included:
`XFree` never looks at a function symbol, so no `PEmpty.elim` is needed. -/

theorem xFree_eqRefl : XFree (Theory.Eq.refl LX) := by
  simpa using xFree_eqOp (ξ := Empty) (#0 : Semiterm LX Empty 1) #0

theorem xFree_eqSymm : XFree (Theory.Eq.symm LX) := by
  refine (xFree_all _).mpr ((xFree_all _).mpr ((xFree_imp _ _).mpr ⟨?_, ?_⟩)) <;>
    exact xFree_eqOp _ _

theorem xFree_eqTrans : XFree (Theory.Eq.trans LX) := by
  refine (xFree_all _).mpr ((xFree_all _).mpr ((xFree_all _).mpr
    ((xFree_imp _ _).mpr ⟨?_, (xFree_imp _ _).mpr ⟨?_, ?_⟩⟩))) <;>
    exact xFree_eqOp _ _

theorem xFree_funcExt {k : ℕ} (f : LX.Func k) : XFree (Theory.Eq.funcExt f) := by
  refine xFree_allClosure _ ((xFree_imp _ _).mpr ⟨xFree_conj _ (fun i => ?_), ?_⟩) <;>
    exact xFree_eqOp _ _

theorem xFree_relExt_inl {k : ℕ} (r : (ℒₒᵣ : Language).Rel k) :
    XFree (Theory.Eq.relExt (Sum.inl r : LX.Rel k)) := by
  refine xFree_allClosure _ ((xFree_imp _ _).mpr
    ⟨xFree_conj _ (fun i => xFree_eqOp _ _), (xFree_imp _ _).mpr ⟨?_, ?_⟩⟩) <;>
    exact ⟨r, rfl⟩

/-! ### The two routes through ω-completeness -/

/-- An `X`-free equality axiom is derivable: it is closed (a sentence embeds to
a closed formula) and true in `stdLX`, which is what `omega_complete_ev` asks
for. -/
theorem derivable_of_xFree_eqAxiom {σ : Sentence LX} (h : σ ∈ 𝗘𝗤 LX) (hX : XFree σ) :
    ∃ β : NONote, OmegaDerivable trueArithLits evInst 0 β
      [ev (Rewriting.emb σ : Proposition LX)] := by
  refine ⟨_, omega_complete_ev (fun _ => False) (fun _ => 0) _ (xFree_emb hX) (by simp) ?_⟩
  simp only [Semiformula.eval_emb]
  exact eval_of_eqAxiom _ h

/-- **The `𝗣𝗔⁻` half.**  An axiom of `Theory.lMap toLX 𝗣𝗔⁻` is
`Semiformula.lMap toLX τ` for a `τ ∈ 𝗣𝗔⁻`, and `ℕ↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻`
(Foundation, PeanoMinus/Basic.lean:150); `EvInst.omega_complete_sentence_ev` is
the rest. -/
theorem paMinus_axiom_derivable (σ : Sentence LX) (h : σ ∈ Theory.lMap toLX 𝗣𝗔⁻) :
    ∃ β : NONote, OmegaDerivable trueArithLits evInst 0 β
      [ev (Rewriting.emb σ : Proposition LX)] := by
  obtain ⟨τ, hτ, rfl⟩ := h
  exact ⟨_, omega_complete_sentence_ev τ (Theory.models ℕ 𝗣𝗔⁻ hτ)⟩

/-! ### Atoms, at an arbitrary variable type

The four atoms `relExt X` is built from, each behind an opaque head so that
`rw`/`simp` never have to traverse `Sum.inr XRel.X` (a known pitfall).  The rewriting
and evaluation laws below are the whole interface; past this point no proof in
the file mentions a relation symbol. -/

/-- `t = u`. -/
def eqA {ξ : Type*} {n : ℕ} (t u : Semiterm LX ξ n) : Semiformula LX ξ n :=
  Semiformula.rel (Language.Eq.eq : LX.Rel 2) ![t, u]

/-- `t ≠ u`. -/
def neqA {ξ : Type*} {n : ℕ} (t u : Semiterm LX ξ n) : Semiformula LX ξ n :=
  Semiformula.nrel (Language.Eq.eq : LX.Rel 2) ![t, u]

/-- `X(t)`, at an arbitrary variable type — `Setup.Xat` is the case `ξ = ℕ`. -/
def XA {ξ : Type*} {n : ℕ} (t : Semiterm LX ξ n) : Semiformula LX ξ n :=
  Semiformula.rel (Sum.inr XRel.X) ![t]

/-- `∼X(t)`. -/
def nXA {ξ : Type*} {n : ℕ} (t : Semiterm LX ξ n) : Semiformula LX ξ n :=
  Semiformula.nrel (Sum.inr XRel.X) ![t]

@[simp] theorem neg_eqA {ξ : Type*} {n : ℕ} (t u : Semiterm LX ξ n) :
    ∼(eqA t u) = neqA t u := rfl

@[simp] theorem neg_XA {ξ : Type*} {n : ℕ} (t : Semiterm LX ξ n) : ∼(XA t) = nXA t := rfl

@[simp] theorem rew_eqA {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LX ξ₁ n₁ ξ₂ n₂)
    (t u : Semiterm LX ξ₁ n₁) : ω ▹ (eqA t u) = eqA (ω t) (ω u) :=
  Semiformula.rew_rel2 ω

@[simp] theorem rew_XA {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LX ξ₁ n₁ ξ₂ n₂)
    (t : Semiterm LX ξ₁ n₁) : ω ▹ (XA t) = XA (ω t) :=
  Semiformula.rew_rel1 ω

@[simp] theorem rew_neqA {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LX ξ₁ n₁ ξ₂ n₂)
    (t u : Semiterm LX ξ₁ n₁) : ω ▹ (neqA t u) = neqA (ω t) (ω u) :=
  Semiformula.rew_nrel2 ω

@[simp] theorem rew_nXA {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LX ξ₁ n₁ ξ₂ n₂)
    (t : Semiterm LX ξ₁ n₁) : ω ▹ (nXA t) = nXA (ω t) :=
  Semiformula.rew_nrel1 ω

@[simp] theorem ev_eqA {n : ℕ} (t u : Semiterm LX ℕ n) : ev (eqA t u) = eqA (evT t) (evT u) :=
  congrArg (Semiformula.rel (Language.Eq.eq : LX.Rel 2))
    (funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩))

@[simp] theorem ev_neqA {n : ℕ} (t u : Semiterm LX ℕ n) :
    ev (neqA t u) = neqA (evT t) (evT u) :=
  congrArg (Semiformula.nrel (Language.Eq.eq : LX.Rel 2))
    (funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩))

@[simp] theorem ev_XA {n : ℕ} (t : Semiterm LX ℕ n) : ev (XA t) = XA (evT t) := by
  have h : (fun i : Fin 1 => evT (![t] i)) = ![evT t] :=
    funext (Fin.forall_fin_one.mpr rfl)
  exact congrArg
    (fun v : Fin 1 → Semiterm LX ℕ n => Semiformula.rel (Sum.inr XRel.X : LX.Rel 1) v) h

@[simp] theorem ev_nXA {n : ℕ} (t : Semiterm LX ℕ n) : ev (nXA t) = nXA (evT t) := by
  have h : (fun i : Fin 1 => evT (![t] i)) = ![evT t] :=
    funext (Fin.forall_fin_one.mpr rfl)
  exact congrArg
    (fun v : Fin 1 → Semiterm LX ℕ n => Semiformula.nrel (Sum.inr XRel.X : LX.Rel 1) v) h

/-- The bridge between `StandardLX.numLX` — a `def`, and the shape `evInst`
substitutes — and `Evaluate.numAt`, the shape the `simp` set is stated in.
Without it a `bShift` of a numeral coming out of `Rew.q_subst` is not
recognised as a numeral. -/
@[simp] theorem rew_numLX {n : ℕ} (ω : Rew LX ℕ 0 ℕ n) (m : ℕ) :
    ω (numLX m) = (numAt m : Semiterm LX ℕ n) := rew_numAt ω m

/-! ### `relExt X`, spelled out

Foundation defines `Eq.relExt r = ∀¹* σ` with `σ` a formula in `k + k`
variables; for `k = 1` that closure is literally `∀¹ ∀¹ σ` (`allClosure_succ`
and `allClosure_zero` are both `rfl`) and `σ` is `(#0 = #1 ⋏ ⊤) 🡒 X(#0) 🡒 X(#1)`
— the `⊤` being what `Matrix.conj` leaves behind at arity one.  The only step
that is not `rfl` is the passage from Foundation's matrices
`fun i : Fin 1 ↦ #(i.addCast 1)` to `![#0]`, which needs a `funext` and is
therefore done by `congrArg`, never by `rw`. -/

/-- The matrix of `relExt X`, as a sentence. -/
def relX2S : Semisentence LX 2 :=
  ∼(eqA (#0 : Semiterm LX Empty 2) #1 ⋏ ⊤)
    ⋎ (∼(XA (#0 : Semiterm LX Empty 2)) ⋎ XA (#1 : Semiterm LX Empty 2))

/-- The matrix of `relExt X`, as a proposition. -/
def relX2 : Semiformula LX ℕ 2 :=
  ∼(eqA (#0 : Semiterm LX ℕ 2) #1 ⋏ ⊤)
    ⋎ (∼(XA (#0 : Semiterm LX ℕ 2)) ⋎ XA (#1 : Semiterm LX ℕ 2))

theorem relExtX_eq :
    (Theory.Eq.relExt (Sum.inr XRel.X : LX.Rel 1) : Sentence LX) = ∀¹ (∀¹ relX2S) := by
  have hv0 : (fun i : Fin 1 ↦ (#(i.addCast 1) : Semiterm LX Empty 2))
      = ![(#0 : Semiterm LX Empty 2)] := funext (Fin.forall_fin_one.mpr rfl)
  have hv1 : (fun i : Fin 1 ↦ (#(i.addNat 1) : Semiterm LX Empty 2))
      = ![(#1 : Semiterm LX Empty 2)] := funext (Fin.forall_fin_one.mpr rfl)
  have hB : Semiformula.rel (Sum.inr XRel.X : LX.Rel 1)
        (fun i : Fin 1 ↦ (#(i.addCast 1) : Semiterm LX Empty 2))
      = XA (#0 : Semiterm LX Empty 2) :=
    congrArg (fun v : Fin 1 → Semiterm LX Empty 2 =>
        Semiformula.rel (Sum.inr XRel.X : LX.Rel 1) v) hv0
  have hC : Semiformula.rel (Sum.inr XRel.X : LX.Rel 1)
        (fun i : Fin 1 ↦ (#(i.addNat 1) : Semiterm LX Empty 2))
      = XA (#1 : Semiterm LX Empty 2) :=
    congrArg (fun v : Fin 1 → Semiterm LX Empty 2 =>
        Semiformula.rel (Sum.inr XRel.X : LX.Rel 1) v) hv1
  exact congrArg (fun ψ : Semisentence LX 2 => ∀¹ (∀¹ ψ))
    ((congrArg (fun B : Semisentence LX 2 =>
        ∼(eqA (#0 : Semiterm LX Empty 2) #1 ⋏ ⊤) ⋎
          (∼B ⋎ Semiformula.rel (Sum.inr XRel.X : LX.Rel 1)
            (fun i : Fin 1 ↦ (#(i.addNat 1) : Semiterm LX Empty 2)))) hB).trans
      (congrArg (fun C : Semisentence LX 2 =>
        ∼(eqA (#0 : Semiterm LX Empty 2) #1 ⋏ ⊤) ⋎
          (∼(XA (#0 : Semiterm LX Empty 2)) ⋎ C)) hC))

/-- The embedding only has to cross the connectives and the four atoms. -/
theorem emb_relX2 : (Rewriting.emb relX2S : Semiformula LX ℕ 2) = relX2 := by
  simp [relX2S, relX2]

/-- `relExt X` as a proposition.  `Rewriting.emb` does *not* commute with `∀¹`
definitionally: `Rew.q_emb` is a lemma, not `rfl`. -/
theorem emb_relExtX :
    (Rewriting.emb (Theory.Eq.relExt (Sum.inr XRel.X : LX.Rel 1)) : Proposition LX)
      = ∀¹ (∀¹ relX2) := by
  rw [relExtX_eq]
  simp only [Rewriting.app_all, Rew.q_emb]
  exact congrArg (fun ψ : Semiformula LX ℕ 2 => ∀¹ (∀¹ ψ)) emb_relX2

/-- The matrix after the outer instantiation, which substitutes `#1`. -/
def relX1 (m : ℕ) : Semiformula LX ℕ 1 :=
  ∼(eqA (#0 : Semiterm LX ℕ 1) (numAt m) ⋏ ⊤)
    ⋎ (∼(XA (#0 : Semiterm LX ℕ 1)) ⋎ XA (numAt m))

/-- The matrix after both instantiations. -/
def relX0 (m n : ℕ) : Proposition LX :=
  ∼(eqA (numLX n) (numLX m) ⋏ ⊤) ⋎ (∼(XA (numLX n)) ⋎ XA (numLX m))

/-- The outer ω-rule.  `Rew.q_subst` produces a `bShift` of the numeral, which
collapses because a numeral is a constant. -/
theorem subst_relX2 (m : ℕ) : (∀¹ relX2)/[numLX m] = ∀¹ (relX1 m) := by
  simp [relX2, relX1, Rew.q_subst]

/-- The inner ω-rule. -/
theorem subst_relX1 (m n : ℕ) : (relX1 m)/[numLX n] = relX0 m n := by
  simp [relX1, relX0]

/-- Every term of the doubly instantiated matrix is already a numeral, so the
evaluator fixes it.  This is what lets the ω-rule of the *evaluating* calculus
be fed with it. -/
theorem ev_relX0 (m n : ℕ) : ev (relX0 m n) = relX0 m n := by
  simp [relX0]

/-! ### The derivation of `relExt X`

Two ω-rules, three `or` rules, and then a two-way split: `m = n` is the identity
rule on `X(n̄)`, and `m ≠ n` makes `∼(n̄ = m̄)` a true closed arithmetic literal,
hence an axiom.  Both branches sit at height `0`, so the ω-rules' premises are
uniform and every height is finite. -/

/-- Evaluating an equality atom is comparing the values of its arguments — on
the nose, because the arithmetic reduct of `stdLX P` *is* `standardModel ℕ`. -/
theorem eval_eqA_iff (P : ℕ → Prop) (f : ℕ → ℕ) {k : ℕ} (e : Fin k → ℕ)
    (t u : Semiterm LX ℕ k) :
    Semiformula.Eval (s := stdLX P) e f (eqA t u)
      ↔ Semiterm.val (s := stdLX P) e f t = Semiterm.val (s := stdLX P) e f u := Iff.rfl

/-- `∼(n̄ = m̄)` is an atomic axiom whenever `n ≠ m`: it is a closed `X`-free
literal, and it is false in `ℕ`. -/
theorem trueArithLits_neqA {n m : ℕ} (h : n ≠ m) :
    trueArithLits.T (neqA (numLX n) (numLX m)) := by
  have hv : ∀ i, ((![numLX n, numLX m] : Fin 2 → SyntacticTerm LX) i).freeVariables = ∅ :=
    Fin.forall_fin_two.mpr ⟨freeVariables_numLX n, freeVariables_numLX m⟩
  have hlit : IsArithLit (eqA (numLX n) (numLX m)) :=
    isArithLit_rel Language.Eq.eq ![numLX n, numLX m] hv
  refine trueArithLits_neg_of_false (fun _ => False) hlit (f := fun _ => 0) ?_
  rw [eval_eqA_iff]
  simpa using h

/-- The sequent both ω-rules reduce to, at height `0`.  The two branches are the
whole content of the axiom: congruence for `X` holds because either the two
numerals are the same symbol, or the premise `n̄ = m̄` is refutable outright. -/
theorem relX0_base (m n : ℕ) :
    OmegaDerivable trueArithLits evInst 0 (NONote.ofNat 0)
      [nXA (numLX n), XA (numLX m), neqA (numLX n) (numLX m), (⊥ : Proposition LX)] := by
  by_cases h : n = m
  · subst h
    exact OmegaDerivable.of_mem_identity (Sum.inr XRel.X : LX.Rel 1) ![numLX n]
      (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
  · refine OmegaDerivable.contraction ?_ (OmegaDerivable.atom (trueArithLits_neqA h))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact absurd hx (by simp)

/-- The three `or` rules, with one reordering: `∼X(n̄) ⋎ X(m̄)` has to reach the
head of the sequent before it can be introduced, and afterwards it has to go
back behind `∼(n̄ = m̄)`. -/
theorem relX0_derivable (m n : ℕ) :
    OmegaDerivable trueArithLits evInst 0 (NONote.ofNat 3) [relX0 m n] := by
  have d1 : OmegaDerivable trueArithLits evInst 0 (NONote.ofNat 1)
      [nXA (numLX n) ⋎ XA (numLX m), neqA (numLX n) (numLX m), (⊥ : Proposition LX)] :=
    OmegaDerivable.or (ofNat_lt_ofNat (by omega)) (relX0_base m n)
  have d2 : OmegaDerivable trueArithLits evInst 0 (NONote.ofNat 1)
      [neqA (numLX n) (numLX m), (⊥ : Proposition LX), nXA (numLX n) ⋎ XA (numLX m)] := by
    refine OmegaDerivable.contraction ?_ d1
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact absurd hx (by simp)
  have d3 : OmegaDerivable trueArithLits evInst 0 (NONote.ofNat 2)
      [neqA (numLX n) (numLX m) ⋎ (⊥ : Proposition LX), nXA (numLX n) ⋎ XA (numLX m)] :=
    OmegaDerivable.or (ofNat_lt_ofNat (by omega)) d2
  exact OmegaDerivable.or (ofNat_lt_ofNat (by omega)) d3

/-- **`relExt X`.**  The one axiom of `𝗘𝗤 LX` that mentions the fresh predicate,
derived by hand, cut-free, at height `NONote.ofNat 5`. -/
theorem relExtX_derivable :
    ∃ β : NONote, OmegaDerivable trueArithLits evInst 0 β
      [ev (Rewriting.emb (Theory.Eq.relExt (Sum.inr XRel.X : LX.Rel 1)) : Proposition LX)] := by
  refine ⟨NONote.ofNat 5, ?_⟩
  rw [emb_relExtX, ev_all]
  refine OmegaDerivable.omegaRule (fun _ => NONote.ofNat 4)
    (fun _ => ofNat_lt_ofNat (by omega)) (fun m => ?_)
  rw [evInst_inst_ev, subst_relX2, ev_all]
  refine OmegaDerivable.omegaRule (fun _ => NONote.ofNat 3)
    (fun _ => ofNat_lt_ofNat (by omega)) (fun n => ?_)
  rw [evInst_inst_ev, subst_relX1, ev_relX0]
  exact relX0_derivable m n

/-- Extensionality for an *arithmetic* relation symbol.  Split off so that the
language of `Theory.eqAxiom.relExt` can be given explicitly: an ascription
`(Sum.inl r : LX.Rel k)` elaborates to a bare `⊕`, which no longer unifies with
`Language.Rel ?L ?k`. -/
theorem relExt_inl_derivable {k : ℕ} (r : (ℒₒᵣ : Language).Rel k) :
    ∃ β : NONote, OmegaDerivable trueArithLits evInst 0 β
      [ev (Rewriting.emb (Theory.Eq.relExt (Sum.inl r : LX.Rel k)) : Proposition LX)] :=
  derivable_of_xFree_eqAxiom (Theory.eqAxiom.relExt (L := LX) (Sum.inl r))
    (xFree_relExt_inl r)

/-! ### The theorem -/

/-- **The `𝗘𝗤 LX` half.**  `cases`, not `rcases`: `rcases` keeps destructing
through `Sum` and then through the constructors of `ORing.Func`/`ORing.Rel`,
which is four unnecessary cases and loses the names. -/
theorem eq_axiom_derivable (σ : Sentence LX) (h : σ ∈ 𝗘𝗤 LX) :
    ∃ β : NONote, OmegaDerivable trueArithLits evInst 0 β
      [ev (Rewriting.emb σ : Proposition LX)] := by
  cases h with
  | refl => exact derivable_of_xFree_eqAxiom Theory.eqAxiom.refl xFree_eqRefl
  | symm => exact derivable_of_xFree_eqAxiom Theory.eqAxiom.symm xFree_eqSymm
  | trans => exact derivable_of_xFree_eqAxiom Theory.eqAxiom.trans xFree_eqTrans
  | funcExt f => exact derivable_of_xFree_eqAxiom (Theory.eqAxiom.funcExt f) (xFree_funcExt f)
  | relExt r =>
      cases r with
      | inl r => exact relExt_inl_derivable r
      | inr rX =>
          cases rX
          exact relExtX_derivable

end OrdinalAnalysis.Gentzen.AxiomsLogic
