/-
  The logical axioms of `RA Λ`, replayed in the ramified ω-calculus (design D2).

  This is `Gentzen/AxiomsLogic.lean` transported from `LX` to `LRA`, with one
  genuine addition: `𝗘𝗤 LRA` has a congruence axiom for *every* relation symbol
  of `LRA`, and `LRA` has one more family of relation symbols than `LX` did —
  the level-indexed membership symbols `∈̇_ν`, one for every level `ν`.  So where
  `Gentzen/AxiomsLogic.lean` has one hand-derived axiom (`relExt X`), this file
  has two: `relExt X` (ported essentially unchanged) and `relExt (∈̇_ν)` for an
  arbitrary `ν` (the same idea, doubled — the congruence is now in *two*
  arguments, so it needs two ω-rules on each side of the naive one-argument
  version, i.e. four ω-rules in total, and the case split is on whether *both*
  argument pairs agree rather than on whether one numeral pair agrees).

  Both blocks land in the *evaluating* calculus `OmegaDerivableR trueArithLitsR
  evInstR`, both are cut-free (rank `0`).  Heights are stated in `Gamma0Note`,
  not in a generic `[OrdinalNotation O]`: the `OrdinalNotation` class
  deliberately has no `0` (`Ordinal/Notation.lean`'s own comment — "the class
  has no `0`, so nothing forces `ω ^ ·` to land above `one`"), and the
  `relExt (∈̇_ν)` derivation needs a `k`-fold closure lemma
  (`allClosureR_derivable`) whose statement is `nadd β (ofNat k)`; folding in
  the base case needs `nadd β (ofNat 0) = β`, which is **not** a theorem of the
  generic class.  `ACAOmega/AxiomsInduction₂.lean` — one of this file's own
  templates — hits exactly the same wall and settles it the same way: the
  *single-step* lemmas stay generic, the *closure* lemmas fix the concrete
  notation system.  `Gamma0Note` is what `Ramified/Rank.lean` already commits
  the cut rank to, so this loses no generality that the rest of the design
  did not already spend.

  Three things about the shape, the first two ported and the third new.

  * **`RFree`** is `Gentzen/AxiomsLogic.lean`'s `XFree`, widened: a formula is
    `RFree` when every relation symbol it uses is arithmetic (`Sum.inl`), i.e.
    it mentions neither `X` nor any `∈̇_ν`.  This is exactly "no fresh symbol at
    all", the right freeness notion for `LRA` because both fresh symbol
    *families* (unary `X`, binary `∈̇_ν`) are tagged `Sum.inr` and so are
    excluded by the same one check.  `omega_completeR` is `RFree`'s
    ω-completeness lemma, proved directly against `evInstR`/`evR` (no separate
    `Transfer` step is needed — `ACAOmega/OmegaTruth₂.lean`'s file header notes
    the same shortcut for the very same reason: the induction can run directly
    against the evaluating instantiation because every clause of `evR` is one
    of the calculus's own equations).

  * **`relExt X`** is `Gentzen/AxiomsLogic.lean`'s `relExtX_derivable`, ported
    verbatim in spirit: two ω-rules, three `or`s, a case split on `m = n`.

  * **`relExt (∈̇_ν)`**, the new block.  `Eq.relExt r` for a binary `r` is
    `∀¹* ((x₀ = y₀ ⋏ (x₁ = y₁ ⋏ ⊤)) → (r x₀ x₁ → r y₀ y₁))`, a closure over four
    variables.  Rather than hand-unfold the closure via four *sequential*
    substitutions (fragile: the outer/inner order of the four ω-rules and the
    resulting argument positions have to be tracked by hand, and a `Fin.succ`
    mismatch defeats `simp`'s automatic matching at every layer), this file
    proves a general `allClosureR_derivable`: an `LRA` analogue of
    `Gentzen/AxiomsInduction.lean`'s `allClosure_derivable`, closing a `k`-ary
    matrix at once from a hypothesis indexed by a *simultaneous* assignment
    `w : Fin k → ℕ`.  Simultaneous substitution assigns each `#i` directly by
    index, which is what makes the four-variable case no harder to state than
    the one-variable case that `Gentzen/AxiomsInduction.lean` already needed for
    the induction scheme's own closure — and `Ramified/AxiomsInduction.lean`
    reuses this same lemma for exactly that purpose, by importing this file.

  Contents.

    `IsArithRelR`, `RFree`             the freeness notion, and its closure laws
    `isArithLitR_of_rFree_{rel,nrel}`  the bridge to `Literals.lean`'s literals
    `eval_all_numAtR`, `eval_exs_numAtR`  the ω-rule's semantics for `stdLRA`
    `hgtR`, `omega_completeR`          **the master lemma**
    `omega_completeR_sentence`         the shape `Theory.lMap toLRA 𝗣𝗔⁻` arrives in
    `eval_of_eqAxiom`                  every `𝗘𝗤 LRA` axiom holds in `stdLRA`
    `rFree_eqRefl` … `rFree_relExt_inl`  the `RFree` axiom shapes
    `derivable_of_rFree_eqAxiom`       the ω-completeness route
    `paMinus_axiom_derivable`          **the `𝗣𝗔⁻` half**
    `XAG`, `nXAG`, `eqA`, `neqA`       the atoms of `relExt X`, kept opaque
    `relExtX_derivable`                `relExt X`, by hand
    `subst_q_substR`, `allClosureR_{aux,derivable}`
                                       **the general `k`-fold closure lemma**
    `memAtG`, `nmemAtG`, `memX4`, `memX0_derivable`
                                       the matrix of `relExt (∈̇_ν)`, by hand
    `relExtMem_derivable`              `relExt (∈̇_ν)`, for an arbitrary `ν`
    `eq_axiom_derivable`               **the `𝗘𝗤 LRA` half**
-/
import OrdinalAnalysis.Ramified.Evaluate
import OrdinalAnalysis.Ramified.NumSubst

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

/-- **A rewriting fixes a numeral, one level up.**  `numAtR_zero` identifies
`num m` with `numAtR m` only at arity `0`; the ω-rule's substitutions and the
embedding cross a binder, landing the numeral at arity `1`, where the bridge
has to be made explicit once.  Tagged `@[simp]` because it is the missing link
every `Rew.bShift`/`Rew.emb`/`Rew.subst` computation below needs. -/
@[simp] theorem rew_num_eq_numAtR {n₂ : ℕ} (ω : Rew LRA ℕ 0 ℕ n₂) (m : ℕ) :
    ω (num m) = numAtR m := by
  rw [← numAtR_zero]; exact rew_numAtR ω m

/-! ### `R`-freeness: no fresh symbol at all

`X` is `Sum.inr RARel.X` and every `∈̇_ν` is `Sum.inr (RARel.mem ν)`; both fresh
families are tagged `Sum.inr`, so "no fresh symbol" is one check on the tag,
exactly as `Gentzen/AxiomsLogic.lean`'s `XFree` is for the single fresh
predicate of `LX`. -/

/-- `r` is an arithmetic relation symbol of `LRA` — neither `X` nor a set atom
of any level. -/
def IsArithRelR {k : ℕ} (r : LRA.Rel k) : Prop :=
  ∃ r' : (ℒₒᵣ : Language).Rel k, r = Sum.inl r'

/-- The introduction rule.  Written out because a term containing
`Sum.inl r : LRA.Rel k` is not type-correct at `implicit` transparency. -/
@[simp] theorem isArithRelR_inl {k : ℕ} (r : (ℒₒᵣ : Language).Rel k) :
    IsArithRelR (Sum.inl r : LRA.Rel k) := ⟨r, rfl⟩

/-- **`φ` mentions no fresh symbol.**  Structural, so that it survives
substitution of numerals and so that its atomic case produces an
`IsArithLitR`. -/
def RFree {ξ : Type*} {n : ℕ} : Semiformula LRA ξ n → Prop
  |                   ⊤ => True
  |                   ⊥ => True
  | Semiformula.rel r _ => IsArithRelR r
  | Semiformula.nrel r _ => IsArithRelR r
  |               φ ⋏ ψ => RFree φ ∧ RFree ψ
  |               φ ⋎ ψ => RFree φ ∧ RFree ψ
  |                ∀¹ φ => RFree φ
  |                ∃¹ φ => RFree φ

@[simp] theorem rFree_verum {ξ : Type*} {n : ℕ} : RFree (⊤ : Semiformula LRA ξ n) := trivial

@[simp] theorem rFree_falsum {ξ : Type*} {n : ℕ} : RFree (⊥ : Semiformula LRA ξ n) := trivial

@[simp] theorem rFree_rel {ξ : Type*} {n k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ξ n) :
    RFree (Semiformula.rel r v) ↔ IsArithRelR r := Iff.rfl

@[simp] theorem rFree_nrel {ξ : Type*} {n k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ξ n) :
    RFree (Semiformula.nrel r v) ↔ IsArithRelR r := Iff.rfl

@[simp] theorem rFree_and {ξ : Type*} {n : ℕ} (φ ψ : Semiformula LRA ξ n) :
    RFree (φ ⋏ ψ) ↔ RFree φ ∧ RFree ψ := Iff.rfl

@[simp] theorem rFree_or {ξ : Type*} {n : ℕ} (φ ψ : Semiformula LRA ξ n) :
    RFree (φ ⋎ ψ) ↔ RFree φ ∧ RFree ψ := Iff.rfl

@[simp] theorem rFree_all {ξ : Type*} {n : ℕ} (φ : Semiformula LRA ξ (n + 1)) :
    RFree (∀¹ φ) ↔ RFree φ := Iff.rfl

@[simp] theorem rFree_exs {ξ : Type*} {n : ℕ} (φ : Semiformula LRA ξ (n + 1)) :
    RFree (∃¹ φ) ↔ RFree φ := Iff.rfl

/-- `R`-freeness is closed under negation: de Morgan swaps `rel` with `nrel`
and the quantifiers with each other, and none of that touches a symbol. -/
@[simp] theorem rFree_neg {ξ : Type*} {n : ℕ} (φ : Semiformula LRA ξ n) : RFree (∼φ) ↔ RFree φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **`R`-freeness is closed under rewriting.**  This is what the ω-rule
needs: the premises `φ/[n̄]` are `R`-free whenever `∀¹ φ` is. -/
theorem rFree_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LRA ξ₁ n₁ ξ₂ n₂)
    {φ : Semiformula LRA ξ₁ n₁} (h : RFree φ) : RFree (ω ▹ φ) := by
  revert h
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => intro _; simp
  | hfalsum => intro _; simp
  | hrel r v => intro h; rw [Semiformula.rew_rel]; simpa using h
  | hnrel r v => intro h; rw [Semiformula.rew_nrel]; simpa using h
  | hand φ ψ ihφ ihψ => intro h; simp only [LogicalConnective.HomClass.map_and, rFree_and]
                        exact ⟨ihφ ω h.1, ihψ ω h.2⟩
  | hor φ ψ ihφ ihψ => intro h; simp only [LogicalConnective.HomClass.map_or, rFree_or]
                       exact ⟨ihφ ω h.1, ihψ ω h.2⟩
  | hall φ ih => intro h; simp only [Rewriting.app_all, rFree_all]; exact ih ω.q h
  | hexs φ ih => intro h; simp only [Rewriting.app_exs, rFree_exs]; exact ih ω.q h

/-- A sentence embedded as a proposition stays `R`-free. -/
theorem rFree_emb {ξ : Type*} {n : ℕ} {σ : Semiformula LRA Empty n} (h : RFree σ) :
    RFree (Rewriting.emb σ : Semiformula LRA ξ n) :=
  rFree_rew Rew.emb h

/-- **Everything transported from arithmetic is `R`-free.**  `toLRA` tags every
symbol `Sum.inl`. -/
@[simp] theorem rFree_lMap_toLRA {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) :
    RFree (Semiformula.lMap toLRA φ) := by
  induction φ using Semiformula.rec' with
  | hverum => simp only [LogicalConnective.HomClass.map_top]; exact rFree_verum
  | hfalsum => simp only [LogicalConnective.HomClass.map_bot]; exact rFree_falsum
  | hrel r v => simp only [Semiformula.lMap_rel, rFree_rel]; exact ⟨r, rfl⟩
  | hnrel r v => simp only [Semiformula.lMap_nrel, rFree_nrel]; exact ⟨r, rfl⟩
  | hand φ ψ ihφ ihψ =>
      simp only [LogicalConnective.HomClass.map_and, rFree_and]; exact ⟨ihφ, ihψ⟩
  | hor φ ψ ihφ ihψ =>
      simp only [LogicalConnective.HomClass.map_or, rFree_or]; exact ⟨ihφ, ihψ⟩
  | hall φ ih => simp only [Semiformula.lMap_all, rFree_all]; exact ih
  | hexs φ ih => simp only [Semiformula.lMap_exs, rFree_exs]; exact ih

/-! ### From an `R`-free closed atom to an axiom -/

theorem isArithLitR_of_rFree_rel {k : ℕ} (r : LRA.Rel k) (v : Fin k → SyntacticTerm LRA)
    (hR : IsArithRelR r) (hc : (Semiformula.rel r v).freeVariables = ∅) :
    IsArithLitR (Semiformula.rel r v) := by
  obtain ⟨r', rfl⟩ := hR
  refine isArithLitR_rel r' v (fun i => ?_)
  have hu := (Semiformula.freeVariables_rel (Sum.inl r' : LRA.Rel k) v).symm.trans hc
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  exact Finset.notMem_empty x (hu ▸ Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)

theorem isArithLitR_of_rFree_nrel {k : ℕ} (r : LRA.Rel k) (v : Fin k → SyntacticTerm LRA)
    (hR : IsArithRelR r) (hc : (Semiformula.nrel r v).freeVariables = ∅) :
    IsArithLitR (Semiformula.nrel r v) := by
  obtain ⟨r', rfl⟩ := hR
  refine isArithLitR_nrel r' v (fun i => ?_)
  have hu := (Semiformula.freeVariables_nrel (Sum.inl r' : LRA.Rel k) v).symm.trans hc
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  exact Finset.notMem_empty x (hu ▸ Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)

/-! ### The ω-rule's semantics for `stdLRA` -/

theorem eval_all_numAtR (f : ℕ → ℕ) (φ : Semiproposition LRA 1) :
    Semiformula.Eval (s := stdLRA) ![] f (∀¹ φ)
      ↔ ∀ n : ℕ, Semiformula.Eval (s := stdLRA) ![] f (φ/[(num n : SyntacticTerm LRA)]) := by
  simp only [Semiformula.eval_all]
  refine forall_congr' (fun n => ?_)
  rw [Semiformula.eval_substs]
  refine iff_of_eq (congrArg (fun w => Semiformula.Eval (s := stdLRA) w f φ) (funext fun i => ?_))
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp only [Function.comp_def, Matrix.cons_val_zero]
  show n = Semiterm.val (s := stdLRA) ![] f (num n)
  rw [stdLRA_eq_raStd, val_groundR raStruc (groundR_num n) ![] f, evTermR_num]

theorem eval_exs_numAtR (f : ℕ → ℕ) (φ : Semiproposition LRA 1) :
    Semiformula.Eval (s := stdLRA) ![] f (∃¹ φ)
      ↔ ∃ n : ℕ, Semiformula.Eval (s := stdLRA) ![] f (φ/[(num n : SyntacticTerm LRA)]) := by
  simp only [Semiformula.eval_ex]
  refine exists_congr (fun n => ?_)
  rw [Semiformula.eval_substs]
  refine iff_of_eq (congrArg (fun w => Semiformula.Eval (s := stdLRA) w f φ) (funext fun i => ?_))
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp only [Function.comp_def, Matrix.cons_val_zero]
  show n = Semiterm.val (s := stdLRA) ![] f (num n)
  rw [stdLRA_eq_raStd, val_groundR raStruc (groundR_num n) ![] f, evTermR_num]

/-- A rewriting whose bound-variable images are closed keeps a closed formula
closed.  Ported from `Gentzen/LowerSyntax.lean`'s lemma of the same shape,
language-generic there and here alike. -/
theorem freeVariables_rewR_eq_empty {n₁ n₂ : ℕ} (ω : Rew LRA ℕ n₁ ℕ n₂)
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

/-- Case analysis on a proposition of `LRA`, in connective form so that the
`simp` lemmas of `RFree`, `freeVariables` and `evR` fire on the results. -/
theorem cases0R {C : Proposition LRA → Prop}
    (hverum : C ⊤) (hfalsum : C ⊥)
    (hrel : ∀ (k : ℕ) (r : LRA.Rel k) (v : Fin k → SyntacticTerm LRA), C (Semiformula.rel r v))
    (hnrel : ∀ (k : ℕ) (r : LRA.Rel k) (v : Fin k → SyntacticTerm LRA), C (Semiformula.nrel r v))
    (hand : ∀ φ ψ : Proposition LRA, C (φ ⋏ ψ))
    (hor : ∀ φ ψ : Proposition LRA, C (φ ⋎ ψ))
    (hall : ∀ φ : Semiproposition LRA 1, C (∀¹ φ))
    (hexs : ∀ φ : Semiproposition LRA 1, C (∃¹ φ)) :
    ∀ φ : Proposition LRA, C φ
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
Constant across the premises of the ω-rule (`Semiformula.complexity_rew`), which
is what lets a single finite ordinal bound all of them. -/
def hgtR (φ : Proposition LRA) : Gamma0Note := OrdinalNotation.ofNat φ.complexity

/-- The induction, with the height fixed by an external bound on the
complexity so that the recursion is on `ℕ` rather than on the formula. -/
private theorem omega_completeR_aux :
    ∀ (c : ℕ) (φ : Proposition LRA), φ.complexity ≤ c → RFree φ → φ.freeVariables = ∅ →
      Semiformula.Eval (s := stdLRA) ![] (fun _ => 0) φ →
      OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat c) [evR φ] := by
  intro c
  induction c with
  | zero =>
      intro φ
      refine cases0R (C := fun φ => φ.complexity ≤ 0 → RFree φ → φ.freeVariables = ∅ →
        Semiformula.Eval (s := stdLRA) ![] (fun _ => 0) φ →
        OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 0) [evR φ])
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ φ
      · intro _ _ _ _; rw [evR_verum]; exact .verum
      · intro _ _ _ ht; exact absurd ht (by simp)
      · intro k r v _ hR hc ht
        exact .atom (trueArithLitsR_evR ⟨isArithLitR_of_rFree_rel r v hR hc, ht⟩)
      · intro k r v _ hR hc ht
        exact .atom (trueArithLitsR_evR ⟨isArithLitR_of_rFree_nrel r v hR hc, ht⟩)
      · intro φ' ψ' hcx _ _ _; simp at hcx
      · intro φ' ψ' hcx _ _ _; simp at hcx
      · intro φ' hcx _ _ _; simp at hcx
      · intro φ' hcx _ _ _; simp at hcx
  | succ c ih =>
      intro φ
      refine cases0R (C := fun φ => φ.complexity ≤ c + 1 → RFree φ → φ.freeVariables = ∅ →
        Semiformula.Eval (s := stdLRA) ![] (fun _ => 0) φ →
        OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat (c + 1)) [evR φ])
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ φ
      · intro _ _ _ _; rw [evR_verum]; exact .verum
      · intro _ _ _ ht; exact absurd ht (by simp)
      · intro k r v _ hR hc ht
        exact .atom (trueArithLitsR_evR ⟨isArithLitR_of_rFree_rel r v hR hc, ht⟩)
      · intro k r v _ hR hc ht
        exact .atom (trueArithLitsR_evR ⟨isArithLitR_of_rFree_nrel r v hR hc, ht⟩)
      · -- `φ ⋏ ψ`: both conjuncts are true, and both premises are needed.
        intro φ' ψ' hcx hR hc ht
        simp only [Semiformula.complexity_and] at hcx
        simp only [rFree_and] at hR
        simp only [Semiformula.freeVariables_and, Finset.union_eq_empty] at hc
        rw [LogicalConnective.HomClass.map_and] at ht
        rw [evR_and]
        exact .and (OrdinalNotation.ofNat_lt_ofNat (Nat.lt_succ_self c))
          (OrdinalNotation.ofNat_lt_ofNat (Nat.lt_succ_self c))
          (ih φ' (by omega) hR.1 hc.1 ht.1) (ih ψ' (by omega) hR.2 hc.2 ht.2)
      · -- `φ ⋎ ψ`: one disjunct is true; the other is added by weakening.
        intro φ' ψ' hcx hR hc ht
        simp only [Semiformula.complexity_or] at hcx
        simp only [rFree_or] at hR
        simp only [Semiformula.freeVariables_or, Finset.union_eq_empty] at hc
        rw [LogicalConnective.HomClass.map_or] at ht
        rw [evR_or]
        refine .or (OrdinalNotation.ofNat_lt_ofNat (Nat.lt_succ_self c)) ?_
        rcases ht with h | h
        · exact .contraction (by simp) (ih φ' (by omega) hR.1 hc.1 h)
        · exact .contraction (by simp) (ih ψ' (by omega) hR.2 hc.2 h)
      · -- `∀¹ φ`: every numeral instance is true, closed and `R`-free.
        intro φ' hcx hR hc ht
        simp only [Semiformula.complexity_all] at hcx
        simp only [rFree_all] at hR
        simp only [Semiformula.freeVariables_all] at hc
        rw [eval_all_numAtR] at ht
        rw [evR_all]
        refine .omegaRule (fun _ => OrdinalNotation.ofNat c)
          (fun _ => OrdinalNotation.ofNat_lt_ofNat (Nat.lt_succ_self c)) (fun n => ?_)
        rw [evInstR_inst_ev]
        refine ih (φ'/[(num n : SyntacticTerm LRA)]) ?_ (rFree_rew _ hR) ?_ (ht n)
        · simp only [Semiformula.complexity_rew]; omega
        · refine freeVariables_rewR_eq_empty _ hc ?_
          intro i
          have hi : i = 0 := Subsingleton.elim i 0
          subst hi; simp
      · -- `∃¹ φ`: some numeral instance is true.
        intro φ' hcx hR hc ht
        simp only [Semiformula.complexity_exs] at hcx
        simp only [rFree_exs] at hR
        simp only [Semiformula.freeVariables_exs] at hc
        rw [eval_exs_numAtR] at ht
        rw [evR_exs]
        obtain ⟨n, hn⟩ := ht
        refine .exs n (OrdinalNotation.ofNat_lt_ofNat (Nat.lt_succ_self c)) ?_
        rw [evInstR_inst_ev]
        refine ih (φ'/[(num n : SyntacticTerm LRA)]) ?_ (rFree_rew _ hR) ?_ hn
        · simp only [Semiformula.complexity_rew]; omega
        · refine freeVariables_rewR_eq_empty _ hc ?_
          intro i
          have hi : i = 0 := Subsingleton.elim i 0
          subst hi; simp

/-- **ω-completeness for the `R`-free fragment.**

Every closed, `R`-free formula true in `stdLRA` has a cut-free derivation of its
own evaluation, at height its own complexity — in particular a *finite*
height.  This discharges every `𝗘𝗤 LRA` axiom shape but `relExt X` and
`relExt (∈̇_ν)`, and the whole of `𝗣𝗔⁻`. -/
theorem omega_completeR (φ : Proposition LRA) (hR : RFree φ) (hc : φ.freeVariables = ∅)
    (ht : Semiformula.Eval (s := stdLRA) ![] (fun _ => 0) φ) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (hgtR φ) [evR φ] :=
  omega_completeR_aux φ.complexity φ le_rfl hR hc ht

/-- **The form `Theory.lMap toLRA 𝗣𝗔⁻` arrives in.**  A lifted `ℒₒᵣ`-sentence
true in `ℕ` is `R`-free (`rFree_lMap_toLRA`) and its truth transfers along
`eval_lMap_toLRA`. -/
theorem omega_completeR_sentence (σ : Sentence ℒₒᵣ)
    (h : Semiformula.Eval (M := ℕ) ![] Empty.elim σ) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
      (hgtR (Rewriting.emb (Semiformula.lMap toLRA σ)))
      [evR (Rewriting.emb (Semiformula.lMap toLRA σ) : Proposition LRA)] := by
  have e : (Rewriting.emb (Semiformula.lMap toLRA σ) : Proposition LRA)
      = Semiformula.lMap toLRA (Rewriting.emb σ : Semiformula ℒₒᵣ ℕ 0) :=
    (Semiformula.lMap_emb σ).symm
  rw [e]
  refine omega_completeR _ (rFree_lMap_toLRA _) (by simp) ?_
  show Semiformula.Eval (s := stdLRA) ![] (fun _ => 0)
    (Semiformula.lMap toLRA (Rewriting.emb σ : Semiformula ℒₒᵣ ℕ 0))
  rw [stdLRA_eq_raStd, eval_lMap_toLRA]
  simpa using h

/-! ### `𝗣𝗔⁻` -/

/-- **The `𝗣𝗔⁻` half.**  An axiom of `Theory.lMap toLRA 𝗣𝗔⁻` is
`Semiformula.lMap toLRA τ` for a `τ ∈ 𝗣𝗔⁻`, true in `ℕ`
(`Foundation`'s `PeanoMinus/Basic.lean`); `omega_completeR_sentence` is the rest. -/
theorem paMinus_axiom_derivable {σ : Sentence LRA} (h : σ ∈ Theory.lMap toLRA 𝗣𝗔⁻) :
    ∃ β : Gamma0Note, OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb σ : Proposition LRA)] := by
  obtain ⟨τ, hτ, rfl⟩ := h
  exact ⟨_, omega_completeR_sentence τ (Theory.models ℕ 𝗣𝗔⁻ hτ)⟩

/-! ### Truth of the equality axioms -/

set_option linter.style.haveILetI false in
/-- **Every axiom of `𝗘𝗤 LRA` holds in `stdLRA`.**  `stdLRA` reads `=` as
equality on `ℕ` (`Structure.add`'s arithmetic summand is
`Arithmetic.standardModel ℕ`), so it models `𝗘𝗤 LRA` — including `relExt X` and
`relExt (∈̇_ν)`, which are true here even though ω-completeness fails for
them. -/
theorem eval_of_eqAxiom {σ : Sentence LRA} (h : σ ∈ 𝗘𝗤 LRA) :
    Semiformula.Eval (s := stdLRA) ![] Empty.elim σ := by
  letI : Structure LRA ℕ := stdLRA
  haveI : Structure.Eq LRA ℕ := ⟨fun _ _ => iff_of_eq rfl⟩
  haveI : ℕ↓[LRA] ⊧* 𝗘𝗤 LRA := Structure.Eq.models_eq LRA ℕ
  exact Theory.models ℕ (𝗘𝗤 LRA) h

/-! ### The `R`-free equality axioms

Every axiom of `𝗘𝗤 LRA` except `relExt (Sum.inr _)` is `R`-free: `refl`,
`symm`, `trans` and `funcExt f` (for every `f`, the fresh function symbols
included — there are none, but the proof does not need to know that) mention
only `=`, and `relExt r` for an *arithmetic* `r` mentions only `=` and `r`. -/

theorem isArithRel_eq : IsArithRelR (Language.Eq.eq : LRA.Rel 2) := ⟨Language.Eq.eq, rfl⟩

theorem rFree_eqOp {ξ : Type*} {n : ℕ} (t u : Semiterm LRA ξ n) :
    RFree ((Semiformula.Operator.Eq.eq : Semiformula.Operator LRA 2).operator ![t, u]) := by
  rw [Semiformula.Operator.eq_def]
  exact isArithRel_eq

theorem rFree_imp {ξ : Type*} {n : ℕ} (φ ψ : Semiformula LRA ξ n) :
    RFree (φ 🡒 ψ) ↔ RFree φ ∧ RFree ψ := by
  have h : (φ 🡒 ψ) = ∼φ ⋎ ψ := rfl
  rw [h, rFree_or, rFree_neg]

theorem rFree_allClosure {ξ : Type*} :
    ∀ {n : ℕ} (φ : Semiformula LRA ξ n), RFree φ → RFree (∀¹* φ)
  | 0, _, h => h
  | _ + 1, φ, h => rFree_allClosure (∀¹ φ) h

theorem rFree_conj {ξ : Type*} {n : ℕ} :
    ∀ {k : ℕ} (v : Fin k → Semiformula LRA ξ n), (∀ i, RFree (v i)) → RFree (Matrix.conj v)
  | 0, _, _ => trivial
  | _ + 1, v, h => ⟨h 0, rFree_conj (Matrix.vecTail v) fun i => h i.succ⟩

theorem rFree_eqRefl : RFree (Theory.Eq.refl LRA) := by
  simpa using rFree_eqOp (ξ := Empty) (#0 : Semiterm LRA Empty 1) #0

theorem rFree_eqSymm : RFree (Theory.Eq.symm LRA) := by
  refine (rFree_all _).mpr ((rFree_all _).mpr ((rFree_imp _ _).mpr ⟨?_, ?_⟩)) <;>
    exact rFree_eqOp _ _

theorem rFree_eqTrans : RFree (Theory.Eq.trans LRA) := by
  refine (rFree_all _).mpr ((rFree_all _).mpr ((rFree_all _).mpr
    ((rFree_imp _ _).mpr ⟨?_, (rFree_imp _ _).mpr ⟨?_, ?_⟩⟩))) <;>
    exact rFree_eqOp _ _

theorem rFree_funcExt {k : ℕ} (f : LRA.Func k) : RFree (Theory.Eq.funcExt f) := by
  refine rFree_allClosure _ ((rFree_imp _ _).mpr ⟨rFree_conj _ (fun i => ?_), ?_⟩) <;>
    exact rFree_eqOp _ _

theorem rFree_relExt_inl {k : ℕ} (r : (ℒₒᵣ : Language).Rel k) :
    RFree (Theory.Eq.relExt (Sum.inl r : LRA.Rel k)) := by
  refine rFree_allClosure _ ((rFree_imp _ _).mpr
    ⟨rFree_conj _ (fun i => rFree_eqOp _ _), (rFree_imp _ _).mpr ⟨?_, ?_⟩⟩) <;>
    exact ⟨r, rfl⟩

/-! ### The route through ω-completeness -/

/-- An `R`-free equality axiom is derivable: it is closed (a sentence embeds to
a closed formula) and true in `stdLRA`. -/
theorem derivable_of_rFree_eqAxiom {σ : Sentence LRA} (h : σ ∈ 𝗘𝗤 LRA) (hR : RFree σ) :
    ∃ β : Gamma0Note, OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb σ : Proposition LRA)] :=
  ⟨_, omega_completeR (Rewriting.emb σ : Proposition LRA) (rFree_emb hR) (by simp)
    (by simpa only [Semiformula.eval_emb] using eval_of_eqAxiom h)⟩

/-! ### `relExt X`, by hand

The one axiom of `𝗘𝗤 LRA` at arity `1` that mentions a fresh symbol; ported
from `Gentzen/AxiomsLogic.lean`'s `relExtX_derivable` essentially unchanged. -/

/-- `X(t)`, at an arbitrary variable type — `Language.lean`'s `Xat` is the case
`ξ = ℕ`. -/
def XAG {ξ : Type*} {n : ℕ} (t : Semiterm LRA ξ n) : Semiformula LRA ξ n :=
  Semiformula.rel (Sum.inr RARel.X : LRA.Rel 1) ![t]

/-- `∼X(t)`. -/
def nXAG {ξ : Type*} {n : ℕ} (t : Semiterm LRA ξ n) : Semiformula LRA ξ n :=
  Semiformula.nrel (Sum.inr RARel.X : LRA.Rel 1) ![t]

/-- `t = u`, at an arbitrary variable type. -/
def eqA {ξ : Type*} {n : ℕ} (t u : Semiterm LRA ξ n) : Semiformula LRA ξ n :=
  Semiformula.rel (Language.Eq.eq : LRA.Rel 2) ![t, u]

/-- `t ≠ u`. -/
def neqA {ξ : Type*} {n : ℕ} (t u : Semiterm LRA ξ n) : Semiformula LRA ξ n :=
  Semiformula.nrel (Language.Eq.eq : LRA.Rel 2) ![t, u]

@[simp] theorem neg_eqA {ξ : Type*} {n : ℕ} (t u : Semiterm LRA ξ n) : ∼(eqA t u) = neqA t u := rfl

@[simp] theorem neg_XAG {ξ : Type*} {n : ℕ} (t : Semiterm LRA ξ n) : ∼(XAG t) = nXAG t := rfl

@[simp] theorem rew_eqA {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LRA ξ₁ n₁ ξ₂ n₂)
    (t u : Semiterm LRA ξ₁ n₁) : ω ▹ (eqA t u) = eqA (ω t) (ω u) := Semiformula.rew_rel2 ω

@[simp] theorem rew_neqA {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LRA ξ₁ n₁ ξ₂ n₂)
    (t u : Semiterm LRA ξ₁ n₁) : ω ▹ (neqA t u) = neqA (ω t) (ω u) := Semiformula.rew_nrel2 ω

@[simp] theorem rew_XAG {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LRA ξ₁ n₁ ξ₂ n₂)
    (t : Semiterm LRA ξ₁ n₁) : ω ▹ (XAG t) = XAG (ω t) := Semiformula.rew_rel1 ω

@[simp] theorem rew_nXAG {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LRA ξ₁ n₁ ξ₂ n₂)
    (t : Semiterm LRA ξ₁ n₁) : ω ▹ (nXAG t) = nXAG (ω t) := Semiformula.rew_nrel1 ω

@[simp] theorem ev_eqA {n : ℕ} (t u : Semiterm LRA ℕ n) : evR (eqA t u) = eqA (evTR t) (evTR u) :=
  congrArg (Semiformula.rel (Language.Eq.eq : LRA.Rel 2))
    (funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩))

@[simp] theorem ev_neqA {n : ℕ} (t u : Semiterm LRA ℕ n) : evR (neqA t u) = neqA (evTR t) (evTR u) :=
  congrArg (Semiformula.nrel (Language.Eq.eq : LRA.Rel 2))
    (funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩))

@[simp] theorem ev_XAG {n : ℕ} (t : Semiterm LRA ℕ n) : evR (XAG t) = XAG (evTR t) := by
  have h : (fun i : Fin 1 => evTR ((![t] : Fin 1 → Semiterm LRA ℕ n) i)) = ![evTR t] :=
    funext (Fin.forall_fin_one.mpr rfl)
  exact congrArg (Semiformula.rel (Sum.inr RARel.X : LRA.Rel 1)) h

@[simp] theorem ev_nXAG {n : ℕ} (t : Semiterm LRA ℕ n) : evR (nXAG t) = nXAG (evTR t) := by
  have h : (fun i : Fin 1 => evTR ((![t] : Fin 1 → Semiterm LRA ℕ n) i)) = ![evTR t] :=
    funext (Fin.forall_fin_one.mpr rfl)
  exact congrArg (Semiformula.nrel (Sum.inr RARel.X : LRA.Rel 1)) h

/-- The matrix of `relExt X`, as a sentence. -/
def relX2S : Semisentence LRA 2 :=
  ∼(eqA (#0 : Semiterm LRA Empty 2) #1 ⋏ ⊤)
    ⋎ (∼(XAG (#0 : Semiterm LRA Empty 2)) ⋎ XAG (#1 : Semiterm LRA Empty 2))

/-- The matrix of `relExt X`, as a proposition. -/
def relX2 : Semiformula LRA ℕ 2 :=
  ∼(eqA (#0 : Semiterm LRA ℕ 2) #1 ⋏ ⊤)
    ⋎ (∼(XAG (#0 : Semiterm LRA ℕ 2)) ⋎ XAG (#1 : Semiterm LRA ℕ 2))

theorem relExtX_eq :
    (Theory.Eq.relExt (Sum.inr RARel.X : LRA.Rel 1) : Sentence LRA) = ∀¹ (∀¹ relX2S) := by
  have hv0 : (fun i : Fin 1 ↦ (#(i.addCast 1) : Semiterm LRA Empty 2))
      = ![(#0 : Semiterm LRA Empty 2)] := funext (Fin.forall_fin_one.mpr rfl)
  have hv1 : (fun i : Fin 1 ↦ (#(i.addNat 1) : Semiterm LRA Empty 2))
      = ![(#1 : Semiterm LRA Empty 2)] := funext (Fin.forall_fin_one.mpr rfl)
  have hB : Semiformula.rel (Sum.inr RARel.X : LRA.Rel 1)
        (fun i : Fin 1 ↦ (#(i.addCast 1) : Semiterm LRA Empty 2))
      = XAG (#0 : Semiterm LRA Empty 2) :=
    congrArg (fun v : Fin 1 → Semiterm LRA Empty 2 =>
        Semiformula.rel (Sum.inr RARel.X : LRA.Rel 1) v) hv0
  have hC : Semiformula.rel (Sum.inr RARel.X : LRA.Rel 1)
        (fun i : Fin 1 ↦ (#(i.addNat 1) : Semiterm LRA Empty 2))
      = XAG (#1 : Semiterm LRA Empty 2) :=
    congrArg (fun v : Fin 1 → Semiterm LRA Empty 2 =>
        Semiformula.rel (Sum.inr RARel.X : LRA.Rel 1) v) hv1
  show (∀¹* ((Matrix.conj fun i : Fin 1 ↦
      (eqA (#(i.addCast 1) : Semiterm LRA Empty 2) (#(i.addNat 1)))) 🡒
      (Semiformula.rel (Sum.inr RARel.X : LRA.Rel 1)
          (fun i : Fin 1 ↦ (#(i.addCast 1) : Semiterm LRA Empty 2)) 🡒
        Semiformula.rel (Sum.inr RARel.X : LRA.Rel 1)
          (fun i : Fin 1 ↦ (#(i.addNat 1) : Semiterm LRA Empty 2)))) : Sentence LRA)
      = ∀¹ (∀¹ relX2S)
  rw [hB, hC]
  rfl

theorem emb_relX2 : (Rewriting.emb relX2S : Semiformula LRA ℕ 2) = relX2 := by
  simp [relX2S, relX2]

theorem emb_relExtX :
    (Rewriting.emb (Theory.Eq.relExt (Sum.inr RARel.X : LRA.Rel 1)) : Proposition LRA)
      = ∀¹ (∀¹ relX2) := by
  rw [relExtX_eq]
  simp only [Rewriting.app_all, Rew.q_emb]
  exact congrArg (fun ψ : Semiformula LRA ℕ 2 => ∀¹ (∀¹ ψ)) emb_relX2

/-- The matrix after the outer instantiation, which substitutes `#1`. -/
def relX1 (m : ℕ) : Semiformula LRA ℕ 1 :=
  ∼(eqA (#0 : Semiterm LRA ℕ 1) (numAtR m) ⋏ ⊤) ⋎ (∼(XAG (#0 : Semiterm LRA ℕ 1)) ⋎ XAG (numAtR m))

/-- The matrix after both instantiations. -/
def relX0 (m n : ℕ) : Proposition LRA :=
  ∼(eqA (numAtR n : SyntacticTerm LRA) (numAtR m) ⋏ ⊤)
    ⋎ (∼(XAG (numAtR n : SyntacticTerm LRA)) ⋎ XAG (numAtR m))

theorem subst_relX2 (m : ℕ) : (∀¹ relX2)/[(num m : SyntacticTerm LRA)] = ∀¹ (relX1 m) := by
  show (Rew.subst ![(num m : SyntacticTerm LRA)]) ▹ (∀¹ relX2) = ∀¹ (relX1 m)
  rw [Rewriting.app_all]
  refine congrArg (fun ψ : Semiformula LRA ℕ 1 => ∀¹ ψ) ?_
  have h0 : ((Rew.subst ![(num m : SyntacticTerm LRA)]).q : Rew LRA ℕ 2 ℕ 1) #0 = #0 :=
    Rew.q_bvar_zero _
  have h1 : ((Rew.subst ![(num m : SyntacticTerm LRA)]).q : Rew LRA ℕ 2 ℕ 1) #1 = numAtR m := by
    have hs : (1 : Fin 2) = Fin.succ 0 := rfl
    rw [hs, Rew.q_bvar_succ]
    simp only [Rew.subst_bvar, Matrix.cons_val_zero, rew_num_eq_numAtR]
  show ((Rew.subst ![(num m : SyntacticTerm LRA)]).q ▹ relX2 : Semiformula LRA ℕ 1) = relX1 m
  simp only [relX2, relX1, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_top, rew_eqA, rew_XAG, h0, h1]

theorem subst_relX1 (m n : ℕ) : (relX1 m)/[(num n : SyntacticTerm LRA)] = relX0 m n := by
  show (Rew.subst ![(num n : SyntacticTerm LRA)]) ▹ (relX1 m) = relX0 m n
  simp only [relX1, relX0, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_top, rew_eqA, rew_XAG,
    Rew.subst_bvar, Matrix.cons_val_zero, rew_numAtR, ← numAtR_zero]

theorem ev_relX0 (m n : ℕ) : evR (relX0 m n) = relX0 m n := by simp [relX0]

/-- `∼(n̄ = m̄)` is an atomic axiom whenever `n ≠ m`: it is a closed literal, and
it is false in `ℕ`. -/
theorem trueArithLitsR_neqA {n m : ℕ} (h : n ≠ m) :
    trueArithLitsR.T (neqA (numAtR n : SyntacticTerm LRA) (numAtR m)) := by
  have hlit : IsArithLitR (eqA (numAtR n : SyntacticTerm LRA) (numAtR m)) :=
    isArithLitR_rel (Language.Eq.eq : (ℒₒᵣ : Language).Rel 2) ![numAtR n, numAtR m]
      (fun i => by fin_cases i <;> exact (groundR_numAtR _).2)
  refine ⟨isArithLitR_neg hlit, ?_⟩
  show TrueNR (∼(eqA (numAtR n : SyntacticTerm LRA) (numAtR m)))
  rw [trueNR_neg]
  show ¬ Semiformula.Eval (s := stdLRA) ![] (fun _ => 0) (eqA (numAtR n : SyntacticTerm LRA) (numAtR m))
  simp only [eqA, Semiformula.eval_rel, Function.comp_def]
  have henv : (![] : Fin 0 → ℕ) = (fun _ => (0 : ℕ)) := Subsingleton.elim _ _
  rw [show (fun i => Semiterm.val (s := stdLRA) ![] (fun _ => (0 : ℕ))
      ((![(numAtR n : SyntacticTerm LRA), numAtR m] : Fin 2 → SyntacticTerm LRA) i))
      = ![n, m] from by funext i; fin_cases i <;> · rw [henv]; exact evTermR_numAtR _]
  exact h

/-- The sequent both ω-rules reduce to, at height `0`. -/
theorem relX0_base (m n : ℕ) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 0)
      [nXAG (numAtR n : SyntacticTerm LRA), XAG (numAtR m : SyntacticTerm LRA),
       neqA (numAtR n : SyntacticTerm LRA) (numAtR m), (⊥ : Proposition LRA)] := by
  by_cases h : n = m
  · subst h
    exact OmegaDerivableR.of_mem_identity (Sum.inr RARel.X : LRA.Rel 1) ![numAtR n]
      (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
  · exact OmegaDerivableR.contraction (by intro x hx; simp at hx ⊢; tauto)
      (OmegaDerivableR.atom (trueArithLitsR_neqA h))

/-- The three `or` rules. -/
theorem relX0_derivable (m n : ℕ) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 3)
      [relX0 m n] := by
  have d1 : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 1)
      [nXAG (numAtR n : SyntacticTerm LRA) ⋎ XAG (numAtR m : SyntacticTerm LRA),
       neqA (numAtR n : SyntacticTerm LRA) (numAtR m), (⊥ : Proposition LRA)] :=
    OmegaDerivableR.or (OrdinalNotation.ofNat_lt_ofNat (by omega)) (relX0_base m n)
  have d2 : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 1)
      [neqA (numAtR n : SyntacticTerm LRA) (numAtR m), (⊥ : Proposition LRA),
       nXAG (numAtR n : SyntacticTerm LRA) ⋎ XAG (numAtR m : SyntacticTerm LRA)] :=
    OmegaDerivableR.contraction (by intro x hx; simp at hx ⊢; tauto) d1
  have d3 : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 2)
      [neqA (numAtR n : SyntacticTerm LRA) (numAtR m) ⋎ (⊥ : Proposition LRA),
       nXAG (numAtR n : SyntacticTerm LRA) ⋎ XAG (numAtR m : SyntacticTerm LRA)] :=
    OmegaDerivableR.or (OrdinalNotation.ofNat_lt_ofNat (by omega)) d2
  exact OmegaDerivableR.or (OrdinalNotation.ofNat_lt_ofNat (by omega)) d3

/-- **`relExt X`.**  The one axiom of `𝗘𝗤 LRA` of arity `1` that mentions a
fresh symbol, derived by hand, cut-free, at height `ofNat 5`. -/
theorem relExtX_derivable :
    ∃ β : Gamma0Note, OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb (Theory.Eq.relExt (Sum.inr RARel.X : LRA.Rel 1)) : Proposition LRA)] := by
  refine ⟨OrdinalNotation.ofNat 5, ?_⟩
  rw [emb_relExtX, evR_all]
  refine OmegaDerivableR.omegaRule (fun _ => OrdinalNotation.ofNat 4)
    (fun _ => OrdinalNotation.ofNat_lt_ofNat (by omega)) (fun m => ?_)
  rw [evInstR_inst_ev, subst_relX2, evR_all]
  refine OmegaDerivableR.omegaRule (fun _ => OrdinalNotation.ofNat 3)
    (fun _ => OrdinalNotation.ofNat_lt_ofNat (by omega)) (fun n => ?_)
  rw [evInstR_inst_ev, subst_relX1, ev_relX0]
  exact relX0_derivable m n

/-! ### The general `k`-fold closure lemma

The `LRA` analogue of `Gentzen/AxiomsInduction.lean`'s `allClosure_derivable`:
a `k`-ary matrix `σ` is derivable once every *simultaneous* numeral instance
`σ ⇜ w` is, at `k` more than their common height.  `Ramified/AxiomsInduction.lean`
reuses this for the induction scheme's own closure. -/

/-- Composing a lifted `k`-ary substitution with a further one-point
substitution is a single `(k + 1)`-ary substitution. -/
theorem subst_q_substR {k : ℕ} (σ : Semiformula LRA ℕ (k + 1)) (v : Fin k → SyntacticTerm LRA)
    (t : SyntacticTerm LRA) :
    ((Rew.subst v).q ▹ σ)/[t] = σ ⇜ (t :> v) := by
  have hrew : (Rew.subst ![t]).comp ((Rew.subst v).q) = Rew.subst (t :> v) := by
    rw [Rew.q_subst, Rew.subst_comp_subst]
    congr 1
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  simpa [← comp_app] using smul_ext' (φ := σ) hrew

/-- `OrdinalNotation.ofNat 0` is the zero of `Gamma0Note`; the closure's base
case needs this once, to identify `nadd β (ofNat 0)` with `β`. -/
theorem ofNat_zero_R : (OrdinalNotation.ofNat 0 : Gamma0Note) = 0 := rfl

theorem allClosureR_aux (β : Gamma0Note) :
    ∀ (k j : ℕ) (σ : Semiformula LRA ℕ k),
      (∀ w : Fin k → ℕ, OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
          (OrdinalNotation.nadd β (OrdinalNotation.ofNat j))
          [evR (σ ⇜ fun i => (numAtR (w i) : SyntacticTerm LRA))]) →
      OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
        (OrdinalNotation.nadd β (OrdinalNotation.ofNat (j + k))) [evR (∀¹* σ)] := by
  intro k
  induction k with
  | zero =>
      intro j σ h
      simpa using h ![]
  | succ k ih =>
      intro j σ h
      have harith : j + (k + 1) = (j + 1) + k := by omega
      rw [harith]
      refine ih (j + 1) (∀¹ σ) (fun w => ?_)
      have hlt : OrdinalNotation.nadd β (OrdinalNotation.ofNat j)
          < OrdinalNotation.nadd β (OrdinalNotation.ofNat (j + 1)) :=
        OrdinalNotation.nadd_lt_nadd_right β (OrdinalNotation.ofNat_lt_ofNat (by omega))
      have hall : ((∀¹ σ) ⇜ fun i => (numAtR (w i) : SyntacticTerm LRA))
          = ∀¹ ((Rew.subst fun i => (numAtR (w i) : SyntacticTerm LRA)).q ▹ σ) := by simp
      rw [hall, evR_all]
      refine OmegaDerivableR.omegaRule (Γ := [])
        (fun _ => OrdinalNotation.nadd β (OrdinalNotation.ofNat j)) (fun _ => hlt) (fun n => ?_)
      rw [evInstR_inst_ev, subst_q_substR]
      have hv : ((num n : SyntacticTerm LRA) :> fun i => (numAtR (w i) : SyntacticTerm LRA))
          = fun i => (numAtR (((n :> w) : Fin (k + 1) → ℕ) i) : SyntacticTerm LRA) := by
        funext i
        induction i using Fin.cases with
        | zero => simp
        | succ j => simp
      rw [hv]
      exact h (n :> w)

/-- **The `k`-fold closure.** -/
theorem allClosureR_derivable {k : ℕ} (σ : Semiformula LRA ℕ k) {β : Gamma0Note}
    (h : ∀ w : Fin k → ℕ, OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 β
        [evR (σ ⇜ fun i => (numAtR (w i) : SyntacticTerm LRA))]) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0
      (OrdinalNotation.nadd β (OrdinalNotation.ofNat k)) [evR (∀¹* σ)] := by
  have key := allClosureR_aux β k 0 σ (by
    intro w
    have hw := h w
    rw [ofNat_zero_R]
    simpa using hw)
  simpa using key

/-! ### `relExt (∈̇_ν)`, by hand

The congruence axiom of the level-`ν` membership symbol, for an arbitrary `ν`.
Same idea as `relExt X`, doubled: the matrix has four bound variables (two per
side of the binary relation), so `allClosureR_derivable` peels them all at
once via a simultaneous numeral assignment `w : Fin 4 → ℕ`, and the leaf case
splits on whether *both* argument pairs agree. -/

/-- `t ∈̇_ν s`, at an arbitrary variable type — `Language.lean`'s `memAt` is the
case `ξ = ℕ`. -/
def memAtG {ξ : Type*} {n : ℕ} (ν : Lv) (t s : Semiterm LRA ξ n) : Semiformula LRA ξ n :=
  Semiformula.rel (Sum.inr (RARel.mem ν) : LRA.Rel 2) ![t, s]

/-- `t ∉̇_ν s`. -/
def nmemAtG {ξ : Type*} {n : ℕ} (ν : Lv) (t s : Semiterm LRA ξ n) : Semiformula LRA ξ n :=
  Semiformula.nrel (Sum.inr (RARel.mem ν) : LRA.Rel 2) ![t, s]

@[simp] theorem rew_memAtG (ν : Lv) {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LRA ξ₁ n₁ ξ₂ n₂)
    (t u : Semiterm LRA ξ₁ n₁) : ω ▹ (memAtG ν t u) = memAtG ν (ω t) (ω u) := Semiformula.rew_rel2 ω

@[simp] theorem rew_nmemAtG (ν : Lv) {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LRA ξ₁ n₁ ξ₂ n₂)
    (t u : Semiterm LRA ξ₁ n₁) : ω ▹ (nmemAtG ν t u) = nmemAtG ν (ω t) (ω u) := Semiformula.rew_nrel2 ω

/-- The matrix of `relExt (∈̇_ν)`, as a sentence in the four variables
`x₀ x₁ y₀ y₁` (`addCast` gives the low, `x`, positions; `addNat` the high, `y`,
positions — `Foundation`'s `Eq.relExt` convention). -/
def memX4S (ν : Lv) : Semisentence LRA 4 :=
  ∼(eqA (#0 : Semiterm LRA Empty 4) #2 ⋏ (eqA (#1 : Semiterm LRA Empty 4) #3 ⋏ ⊤))
    ⋎ (∼(memAtG ν (#0 : Semiterm LRA Empty 4) (#1 : Semiterm LRA Empty 4))
        ⋎ memAtG ν (#2 : Semiterm LRA Empty 4) (#3 : Semiterm LRA Empty 4))

theorem memExt_eq (ν : Lv) :
    (Theory.Eq.relExt (Sum.inr (RARel.mem ν) : LRA.Rel 2) : Sentence LRA)
      = ∀¹ (∀¹ (∀¹ (∀¹ (memX4S ν)))) := by
  have hv0 : (fun i : Fin 2 ↦ (#(i.addCast 2) : Semiterm LRA Empty 4))
      = ![(#0 : Semiterm LRA Empty 4), #1] := by funext i; fin_cases i <;> rfl
  have hv1 : (fun i : Fin 2 ↦ (#(i.addNat 2) : Semiterm LRA Empty 4))
      = ![(#2 : Semiterm LRA Empty 4), #3] := by funext i; fin_cases i <;> rfl
  have hB : Semiformula.rel (Sum.inr (RARel.mem ν) : LRA.Rel 2)
        (fun i : Fin 2 ↦ (#(i.addCast 2) : Semiterm LRA Empty 4))
      = memAtG ν (#0 : Semiterm LRA Empty 4) (#1 : Semiterm LRA Empty 4) :=
    congrArg (fun v : Fin 2 → Semiterm LRA Empty 4 =>
        Semiformula.rel (Sum.inr (RARel.mem ν) : LRA.Rel 2) v) hv0
  have hC : Semiformula.rel (Sum.inr (RARel.mem ν) : LRA.Rel 2)
        (fun i : Fin 2 ↦ (#(i.addNat 2) : Semiterm LRA Empty 4))
      = memAtG ν (#2 : Semiterm LRA Empty 4) (#3 : Semiterm LRA Empty 4) :=
    congrArg (fun v : Fin 2 → Semiterm LRA Empty 4 =>
        Semiformula.rel (Sum.inr (RARel.mem ν) : LRA.Rel 2) v) hv1
  show (∀¹* ((Matrix.conj fun i : Fin 2 ↦
      (eqA (#(i.addCast 2) : Semiterm LRA Empty 4) (#(i.addNat 2)))) 🡒
      (Semiformula.rel (Sum.inr (RARel.mem ν) : LRA.Rel 2)
          (fun i : Fin 2 ↦ (#(i.addCast 2) : Semiterm LRA Empty 4)) 🡒
        Semiformula.rel (Sum.inr (RARel.mem ν) : LRA.Rel 2)
          (fun i : Fin 2 ↦ (#(i.addNat 2) : Semiterm LRA Empty 4)))) : Sentence LRA)
      = ∀¹ (∀¹ (∀¹ (∀¹ (memX4S ν))))
  rw [hB, hC]
  rfl

/-- The matrix of `relExt (∈̇_ν)`, as a proposition. -/
def memX4 (ν : Lv) : Semiformula LRA ℕ 4 :=
  ∼(eqA (#0 : Semiterm LRA ℕ 4) #2 ⋏ (eqA (#1 : Semiterm LRA ℕ 4) #3 ⋏ ⊤))
    ⋎ (∼(memAtG ν (#0 : Semiterm LRA ℕ 4) (#1 : Semiterm LRA ℕ 4))
        ⋎ memAtG ν (#2 : Semiterm LRA ℕ 4) (#3 : Semiterm LRA ℕ 4))

theorem emb_eqA {n : ℕ} (t u : Semiterm LRA Empty n) :
    (Rewriting.emb (eqA t u) : Semiformula LRA ℕ n) = eqA (Rew.emb t) (Rew.emb u) := by
  have h : (fun i : Fin 2 => Rew.emb ((![t, u] : Fin 2 → Semiterm LRA Empty n) i)
        : Fin 2 → Semiterm LRA ℕ n) = ![Rew.emb t, Rew.emb u] := by
    funext i; fin_cases i <;> rfl
  exact congrArg (Semiformula.rel (Language.Eq.eq : LRA.Rel 2)) h

theorem emb_memAtG (ν : Lv) {n : ℕ} (t u : Semiterm LRA Empty n) :
    (Rewriting.emb (memAtG ν t u) : Semiformula LRA ℕ n) = memAtG ν (Rew.emb t) (Rew.emb u) := by
  have h : (fun i : Fin 2 => Rew.emb ((![t, u] : Fin 2 → Semiterm LRA Empty n) i)
        : Fin 2 → Semiterm LRA ℕ n) = ![Rew.emb t, Rew.emb u] := by
    funext i; fin_cases i <;> rfl
  exact congrArg (Semiformula.rel (Sum.inr (RARel.mem ν) : LRA.Rel 2)) h

theorem emb_memX4S (ν : Lv) : (Rewriting.emb (memX4S ν) : Semiformula LRA ℕ 4) = memX4 ν := by
  simp only [memX4S, memX4, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_top, emb_eqA, emb_memAtG]
  rfl

theorem emb_memExt (ν : Lv) :
    (Rewriting.emb (Theory.Eq.relExt (Sum.inr (RARel.mem ν) : LRA.Rel 2)) : Proposition LRA)
      = ∀¹ (∀¹ (∀¹ (∀¹ (memX4 ν)))) := by
  rw [memExt_eq]
  simp only [Rewriting.app_all, Rew.q_emb]
  exact congrArg (fun ψ : Semiformula LRA ℕ 4 => ∀¹ (∀¹ (∀¹ (∀¹ ψ)))) (emb_memX4S ν)

/-- The five-element base case, at height `0`: a false-equality axiom or the
identity rule, depending on whether the two argument pairs agree. -/
theorem memX0_base (ν : Lv) (a b c d : ℕ) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 0)
      [neqA (numAtR a : SyntacticTerm LRA) (numAtR c), neqA (numAtR b : SyntacticTerm LRA) (numAtR d),
       (⊥ : Proposition LRA), nmemAtG ν (numAtR a : SyntacticTerm LRA) (numAtR b),
       memAtG ν (numAtR c : SyntacticTerm LRA) (numAtR d)] := by
  by_cases hac : a = c
  · by_cases hbd : b = d
    · subst hac; subst hbd
      exact OmegaDerivableR.contraction (by intro x hx; simp at hx ⊢; tauto)
        (OmegaDerivableR.identity (Sum.inr (RARel.mem ν) : LRA.Rel 2) ![numAtR a, numAtR b])
    · exact OmegaDerivableR.contraction (by intro x hx; simp at hx ⊢; tauto)
        (OmegaDerivableR.atom (trueArithLitsR_neqA hbd))
  · exact OmegaDerivableR.contraction (by intro x hx; simp at hx ⊢; tauto)
      (OmegaDerivableR.atom (trueArithLitsR_neqA hac))

/-- The four `or`-introductions flattening `memX0_base`'s sequent into the
shape `evR (memX4 ν ⇜ w)` reduces to. -/
theorem memX0_derivable (ν : Lv) (a b c d : ℕ) :
    OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 4)
      [(∼(eqA (numAtR a : SyntacticTerm LRA) (numAtR c) ⋏ (eqA (numAtR b) (numAtR d) ⋏ ⊤)))
        ⋎ (∼(memAtG ν (numAtR a : SyntacticTerm LRA) (numAtR b)) ⋎ memAtG ν (numAtR c) (numAtR d))] := by
  have h01 : (OrdinalNotation.ofNat 0 : Gamma0Note) < OrdinalNotation.ofNat 1 :=
    OrdinalNotation.ofNat_lt_ofNat (by omega)
  have h12 : (OrdinalNotation.ofNat 1 : Gamma0Note) < OrdinalNotation.ofNat 2 :=
    OrdinalNotation.ofNat_lt_ofNat (by omega)
  have h23 : (OrdinalNotation.ofNat 2 : Gamma0Note) < OrdinalNotation.ofNat 3 :=
    OrdinalNotation.ofNat_lt_ofNat (by omega)
  have h34 : (OrdinalNotation.ofNat 3 : Gamma0Note) < OrdinalNotation.ofNat 4 :=
    OrdinalNotation.ofNat_lt_ofNat (by omega)
  -- Step A: `neqA b d ⋎ ⊥`, with the rest reordered behind it.
  have dA0 : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 0)
      [neqA (numAtR b : SyntacticTerm LRA) (numAtR d), (⊥ : Proposition LRA),
       neqA (numAtR a : SyntacticTerm LRA) (numAtR c),
       nmemAtG ν (numAtR a : SyntacticTerm LRA) (numAtR b), memAtG ν (numAtR c : SyntacticTerm LRA) (numAtR d)] :=
    OmegaDerivableR.contraction (by intro x hx; simp at hx ⊢; tauto) (memX0_base ν a b c d)
  have dA1 : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 1)
      [neqA (numAtR b : SyntacticTerm LRA) (numAtR d) ⋎ (⊥ : Proposition LRA),
       neqA (numAtR a : SyntacticTerm LRA) (numAtR c),
       nmemAtG ν (numAtR a : SyntacticTerm LRA) (numAtR b), memAtG ν (numAtR c : SyntacticTerm LRA) (numAtR d)] :=
    OmegaDerivableR.or h01 dA0
  -- Step B: `neqA a c ⋎ (neqA b d ⋎ ⊥)` =: `A`, with the rest reordered behind it.
  have dB0 : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 1)
      [neqA (numAtR a : SyntacticTerm LRA) (numAtR c),
       neqA (numAtR b : SyntacticTerm LRA) (numAtR d) ⋎ (⊥ : Proposition LRA),
       nmemAtG ν (numAtR a : SyntacticTerm LRA) (numAtR b), memAtG ν (numAtR c : SyntacticTerm LRA) (numAtR d)] :=
    OmegaDerivableR.contraction (by intro x hx; simp at hx ⊢; tauto) dA1
  have dB1 : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 2)
      [neqA (numAtR a : SyntacticTerm LRA) (numAtR c) ⋎ (neqA (numAtR b) (numAtR d) ⋎ (⊥ : Proposition LRA)),
       nmemAtG ν (numAtR a : SyntacticTerm LRA) (numAtR b), memAtG ν (numAtR c : SyntacticTerm LRA) (numAtR d)] :=
    OmegaDerivableR.or h12 dB0
  -- Step C: `nmemAtG a b ⋎ memAtG c d` =: `B`, with `A` reordered behind it.
  have dC0 : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 2)
      [nmemAtG ν (numAtR a : SyntacticTerm LRA) (numAtR b), memAtG ν (numAtR c : SyntacticTerm LRA) (numAtR d),
       neqA (numAtR a : SyntacticTerm LRA) (numAtR c) ⋎ (neqA (numAtR b) (numAtR d) ⋎ (⊥ : Proposition LRA))] :=
    OmegaDerivableR.contraction (by intro x hx; simp at hx ⊢; tauto) dB1
  have dC1 : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 3)
      [nmemAtG ν (numAtR a : SyntacticTerm LRA) (numAtR b) ⋎ memAtG ν (numAtR c : SyntacticTerm LRA) (numAtR d),
       neqA (numAtR a : SyntacticTerm LRA) (numAtR c) ⋎ (neqA (numAtR b) (numAtR d) ⋎ (⊥ : Proposition LRA))] :=
    OmegaDerivableR.or h23 dC0
  -- Step D: `A ⋎ B`.
  have dD0 : OmegaDerivableR (O := Gamma0Note) trueArithLitsR evInstR 0 (OrdinalNotation.ofNat 3)
      [neqA (numAtR a : SyntacticTerm LRA) (numAtR c) ⋎ (neqA (numAtR b) (numAtR d) ⋎ (⊥ : Proposition LRA)),
       nmemAtG ν (numAtR a : SyntacticTerm LRA) (numAtR b) ⋎ memAtG ν (numAtR c : SyntacticTerm LRA) (numAtR d)] :=
    OmegaDerivableR.contraction (by intro x hx; simp at hx ⊢; tauto) dC1
  exact OmegaDerivableR.or h34 dD0

/-- **`relExt (∈̇_ν)`.**  The congruence axiom of the level-`ν` membership
symbol, for an arbitrary `ν`, derived by hand, cut-free, at height
`nadd (ofNat 4) (ofNat 4)`. -/
theorem relExtMem_derivable (ν : Lv) :
    ∃ β : Gamma0Note, OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb (Theory.Eq.relExt (Sum.inr (RARel.mem ν) : LRA.Rel 2)) : Proposition LRA)] := by
  refine ⟨OrdinalNotation.nadd (OrdinalNotation.ofNat 4) (OrdinalNotation.ofNat 4), ?_⟩
  rw [emb_memExt]
  refine allClosureR_derivable (memX4 ν) (β := OrdinalNotation.ofNat 4) (fun w => ?_)
  have hw : (memX4 ν ⇜ fun i => (numAtR (w i) : SyntacticTerm LRA))
      = (∼(eqA (numAtR (w 0) : SyntacticTerm LRA) (numAtR (w 2))
            ⋏ (eqA (numAtR (w 1) : SyntacticTerm LRA) (numAtR (w 3)) ⋏ ⊤)))
        ⋎ (∼(memAtG ν (numAtR (w 0) : SyntacticTerm LRA) (numAtR (w 1)))
            ⋎ memAtG ν (numAtR (w 2) : SyntacticTerm LRA) (numAtR (w 3))) := by
    simp [memX4, rew_memAtG]
  rw [hw]
  have hmem1 : evR (memAtG ν (numAtR (w 0) : SyntacticTerm LRA) (numAtR (w 1)))
      = memAtG ν (numAtR (w 0) : SyntacticTerm LRA) (numAtR (w 1)) := by
    have h : (fun i : Fin 2 => evTR ((![(numAtR (w 0) : SyntacticTerm LRA), numAtR (w 1)]
        : Fin 2 → SyntacticTerm LRA) i)) = ![numAtR (w 0), numAtR (w 1)] := by
      funext i; fin_cases i <;> simp
    exact congrArg (Semiformula.rel (Sum.inr (RARel.mem ν) : LRA.Rel 2)) h
  have hmem2 : evR (memAtG ν (numAtR (w 2) : SyntacticTerm LRA) (numAtR (w 3)))
      = memAtG ν (numAtR (w 2) : SyntacticTerm LRA) (numAtR (w 3)) := by
    have h : (fun i : Fin 2 => evTR ((![(numAtR (w 2) : SyntacticTerm LRA), numAtR (w 3)]
        : Fin 2 → SyntacticTerm LRA) i)) = ![numAtR (w 2), numAtR (w 3)] := by
      funext i; fin_cases i <;> simp
    exact congrArg (Semiformula.rel (Sum.inr (RARel.mem ν) : LRA.Rel 2)) h
  have heq1 : evR (eqA (numAtR (w 0) : SyntacticTerm LRA) (numAtR (w 2)))
      = eqA (numAtR (w 0) : SyntacticTerm LRA) (numAtR (w 2)) := by
    have h : (fun i : Fin 2 => evTR ((![(numAtR (w 0) : SyntacticTerm LRA), numAtR (w 2)]
        : Fin 2 → SyntacticTerm LRA) i)) = ![numAtR (w 0), numAtR (w 2)] := by
      funext i; fin_cases i <;> simp
    exact congrArg (Semiformula.rel (Language.Eq.eq : LRA.Rel 2)) h
  have heq2 : evR (eqA (numAtR (w 1) : SyntacticTerm LRA) (numAtR (w 3)))
      = eqA (numAtR (w 1) : SyntacticTerm LRA) (numAtR (w 3)) := by
    have h : (fun i : Fin 2 => evTR ((![(numAtR (w 1) : SyntacticTerm LRA), numAtR (w 3)]
        : Fin 2 → SyntacticTerm LRA) i)) = ![numAtR (w 1), numAtR (w 3)] := by
      funext i; fin_cases i <;> simp
    exact congrArg (Semiformula.rel (Language.Eq.eq : LRA.Rel 2)) h
  simp only [evR_or, evR_and, evR_neg, evR_verum, hmem1, hmem2, heq1, heq2]
  exact memX0_derivable ν (w 0) (w 1) (w 2) (w 3)

/-! ### The theorem -/

/-- Extensionality for an *arithmetic* relation symbol.  Split off so that the
language of `Theory.eqAxiom.relExt` can be given explicitly: an ascription
`(Sum.inl r : LRA.Rel k)` elaborates to a bare `⊕`, which no longer unifies
with `Language.Rel ?L ?k`. -/
theorem relExt_inl_derivable {k : ℕ} (r : (ℒₒᵣ : Language).Rel k) :
    ∃ β : Gamma0Note, OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb (Theory.Eq.relExt (Sum.inl r : LRA.Rel k)) : Proposition LRA)] :=
  derivable_of_rFree_eqAxiom (Theory.eqAxiom.relExt (L := LRA) (Sum.inl r)) (rFree_relExt_inl r)

/-- **The `𝗘𝗤 LRA` half.**  `cases`, not `rcases`: `rcases` would keep
destructing through `Sum` and then through the constructors of the ambient
`ORing.Func`/`ORing.Rel`, which loses the names. -/
theorem eq_axiom_derivable {σ : Sentence LRA} (h : σ ∈ 𝗘𝗤 LRA) :
    ∃ β : Gamma0Note, OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb σ : Proposition LRA)] := by
  cases h with
  | refl => exact derivable_of_rFree_eqAxiom Theory.eqAxiom.refl rFree_eqRefl
  | symm => exact derivable_of_rFree_eqAxiom Theory.eqAxiom.symm rFree_eqSymm
  | trans => exact derivable_of_rFree_eqAxiom Theory.eqAxiom.trans rFree_eqTrans
  | funcExt f => exact derivable_of_rFree_eqAxiom (Theory.eqAxiom.funcExt f) (rFree_funcExt f)
  | relExt r =>
      cases r with
      | inl r => exact relExt_inl_derivable r
      | inr rX =>
          cases rX with
          | X => exact relExtX_derivable
          | mem ν => exact relExtMem_derivable ν

end Ramified

end OrdinalAnalysis
