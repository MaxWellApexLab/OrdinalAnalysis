/-
  The logical axioms of `ACA`, replayed in the evaluating ω-calculus.

  `ACA₀`'s first three blocks are `eqAxioms`, `paMinus` and `setExt`.  The first
  two are lifts of first-order `ℒₒᵣ`-sentences true in `ℕ`, so
  `OmegaTruth₂.omega_complete₂_liftEmb` disposes of them outright; the third is
  the one axiom of the block that mentions a set variable, and it is derived by
  hand.

  `setExt` is `∀²X ∀x ∀y (x = y → x ∈ X → y ∈ X)`, the second-order counterpart
  of the first-order `relExt X` axiom that `Gentzen/AxiomsLogic.lean` had to
  derive by hand for exactly the same reason.  The derivation is five inferences
  deep and completely finite:

    (∀₂)   strips `∀²X`, replacing the bound set variable by the free `0`;
    (ω)    twice, instantiating `y` at `ā` and `x` at `b̄`;
    (⋎)    twice, exposing the three members of
           `¬(b̄ = ā) ⋎ (b̄ ∉ X ⋎ ā ∈ X)`;

  and then the argument splits.  If `b ≠ a`, `¬(b̄ = ā)` is a *true closed
  arithmetic literal* and hence an axiom of `trueArithLits₂`.  If `b = a`, the
  remaining two members are `∼(ā ∈ X)` and `ā ∈ X`, and the general `identity`
  rule of `ACA_∞` closes the sequent.  Neither branch grows with the numerals,
  so the whole derivation sits at height `ofNat 5`.

  Two things are easier here than in the first-order file.

  * **No opaque atoms are needed.**  The first-order development had to hide
    `Sum.inr XRel.X : LX.Rel 1` behind opaque heads, because a term containing it
    is not type-correct at `implicit` transparency.  A second-order set atom is a
    *constructor* (`Semiformula.fvar`), so `simp` may look at it freely.

  * **`identity` is general**, so the `b = a` branch is a leaf at height `0`
    rather than a derivation of height `2·complexity`.

  Contents.

    `liftSentence_eq`                  `liftSentence` in `OmegaTruth₂`'s spelling
    `derivable_of_true_sentence`       the ω-completeness route
    `eq_axiom_derivable`               **the `𝗘𝗤 ℒₒᵣ` block**
    `paMinus_axiom_derivable`          **the `𝗣𝗔⁻` block**
    `eqLit`, `neqLit`, `memX`, `nmemX` the four atoms of the leaf
    `extBody`, `extLeaf`               `setExt` after `(∀₂)`, and after the ω-rules
    `free₁_setExtBody`, `subst_extBody` the two computations
    `extLeaf_derivable`                the leaf, by the case split on `b = a`
    `setExt_derivable`                 **`setExt`, at height `ofNat 5`**
-/
import OrdinalAnalysis.ACAOmega.OmegaTruth₂
import OrdinalAnalysis.ACA.LK

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA
open OrdinalAnalysis.ACAOmega.OmegaTruth₂

namespace AxiomsLogic₂

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-! ### The two lifted blocks -/

/-- `ACA.liftSentence` in the spelling `OmegaTruth₂` states its lemma in. -/
theorem liftSentence_eq (σ : FirstOrder.Sentence ℒₒᵣ) :
    liftSentence σ =
      (lift (FirstOrder.Rewriting.emb σ : FirstOrder.Semiformula ℒₒᵣ ℕ 0) :
        Proposition ℒₒᵣ) := rfl

/-- **A lifted first-order sentence true in `ℕ` is cut-free derivable**, at
height its own complexity. -/
theorem derivable_of_true_sentence (σ : FirstOrder.Sentence ℒₒᵣ)
    (h : FirstOrder.Semiformula.Eval (M := ℕ) ![] Empty.elim σ) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (hgt₂ (liftSentence σ))
      [ev₂ (liftSentence σ)] := by
  rw [liftSentence_eq]
  exact omega_complete₂_liftEmb σ h

/-- **The equality axioms.** -/
theorem eq_axiom_derivable (χ : Proposition ℒₒᵣ) (h : χ ∈ eqAxioms) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (hgt₂ χ) [ev₂ χ] := by
  obtain ⟨σ, hσ, rfl⟩ := h
  exact derivable_of_true_sentence σ (FirstOrder.Theory.models ℕ (𝗘𝗤 ℒₒᵣ) hσ)

/-- **The `PA⁻` axioms.** -/
theorem paMinus_axiom_derivable (χ : Proposition ℒₒᵣ) (h : χ ∈ paMinus) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (hgt₂ χ) [ev₂ χ] := by
  obtain ⟨σ, hσ, rfl⟩ := h
  exact derivable_of_true_sentence σ (FirstOrder.Theory.models ℕ 𝗣𝗔⁻ hσ)

/-! ### The atoms of the `setExt` leaf -/

/-- `b̄ = ā`. -/
def eqLit (b a : ℕ) : Proposition ℒₒᵣ :=
  Semiformula.rel FirstOrder.Language.Eq.eq
    ![(numAt b : FirstOrder.SyntacticTerm ℒₒᵣ), (numAt a : FirstOrder.SyntacticTerm ℒₒᵣ)]

/-- `¬(b̄ = ā)`. -/
def neqLit (b a : ℕ) : Proposition ℒₒᵣ :=
  Semiformula.nrel FirstOrder.Language.Eq.eq
    ![(numAt b : FirstOrder.SyntacticTerm ℒₒᵣ), (numAt a : FirstOrder.SyntacticTerm ℒₒᵣ)]

/-- `ā ∈ X`, with `X` the free set variable `0`. -/
def memX (a : ℕ) : Proposition ℒₒᵣ := (numAt a : FirstOrder.SyntacticTerm ℒₒᵣ) ∈& 0

/-- `ā ∉ X`. -/
def nmemX (a : ℕ) : Proposition ℒₒᵣ := (numAt a : FirstOrder.SyntacticTerm ℒₒᵣ) ∉& 0

@[simp] theorem neg_eqLit (b a : ℕ) : ∼eqLit b a = neqLit b a := rfl

@[simp] theorem neg_memX (a : ℕ) : ∼memX a = nmemX a := rfl

@[simp] theorem ev₂_neqLit (b a : ℕ) : ev₂ (neqLit b a) = neqLit b a := by
  rw [neqLit, ev₂_nrel]
  refine congrArg (fun v : Fin 2 → FirstOrder.SyntacticTerm ℒₒᵣ =>
    (Semiformula.nrel FirstOrder.Language.Eq.eq v : Proposition ℒₒᵣ)) ?_
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ j =>
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      simp

@[simp] theorem ev₂_memX (a : ℕ) : ev₂ (memX a) = memX a := by simp [memX]

@[simp] theorem ev₂_nmemX (a : ℕ) : ev₂ (nmemX a) = nmemX a := by simp [nmemX]

/-- **The false equality is an axiom.**  When `b ≠ a` the literal `¬(b̄ = ā)` is
closed, true in `ℕ`, and already in normal form. -/
theorem trueArithLits₂_neqLit {b a : ℕ} (h : b ≠ a) : trueArithLits₂.T (neqLit b a) := by
  refine ⟨isArithLit₂_nrel _ _ (fun i => ?_), ?_, ev₂_neqLit b a⟩
  · induction i using Fin.cases with
    | zero => simp
    | succ j =>
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        simp
  · simp [TrueN₂, neqLit, h]

/-! ### Set extensionality -/

/-- The matrix of `setExt`, *before* the `∀²` is stripped. -/
def setExtBody : Semiproposition ℒₒᵣ 1 0 :=
  ∀¹ (∀¹
    ((Semiformula.rel FirstOrder.Language.Eq.eq
        ![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2), (#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2)] :
        Semiproposition ℒₒᵣ 1 2) 🡒
      (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) ∈# (0 : Fin 1)) 🡒
        ((#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) ∈# (0 : Fin 1)))))

theorem setExt_eq : setExt = ∀² setExtBody := rfl

/-- The matrix of `setExt` *after* the `∀²` is stripped: the bound set variable
has become the free set variable `0`. -/
def extBody : Semiproposition ℒₒᵣ 0 2 :=
  (Semiformula.rel FirstOrder.Language.Eq.eq
      ![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2), (#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2)] :
      Semiproposition ℒₒᵣ 0 2) 🡒
    (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) ∈& 0) 🡒 ((#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) ∈& 0))

/-- **Stripping the `∀²`.** -/
theorem free₁_setExtBody : Semiproposition.free₁ setExtBody = ∀¹ (∀¹ extBody) := by
  simp [setExtBody, extBody, LogicalConnective.DeMorgan.imply, SecondOrder.Rew.free]

/-- The leaf the two ω-rules reduce `setExt` to: the instance at `x := b̄`,
`y := ā`. -/
def extLeaf (b a : ℕ) : Proposition ℒₒᵣ := neqLit b a ⋎ (nmemX b ⋎ memX a)

/-- **The leaf is derivable at height `0`.** -/
theorem extLeaf_base (b a : ℕ) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (OrdinalNotation.ofNat 0)
      [neqLit b a, nmemX b, memX a] := by
  by_cases h : b = a
  · subst h
    exact OmegaDerivable₂.of_mem_identity (memX b) (by simp) (by simp)
  · exact OmegaDerivable₂.contraction (by simp) (.atom (trueArithLits₂_neqLit h))

/-- **The leaf.** -/
theorem extLeaf_derivable (b a : ℕ) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (OrdinalNotation.ofNat 2)
      [extLeaf b a] := by
  have h01 : (OrdinalNotation.ofNat 0 : O) < OrdinalNotation.ofNat 1 :=
    OrdinalNotation.ofNat_lt_ofNat (by omega)
  have h12 : (OrdinalNotation.ofNat 1 : O) < OrdinalNotation.ofNat 2 :=
    OrdinalNotation.ofNat_lt_ofNat (by omega)
  have d0 : OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (OrdinalNotation.ofNat 0)
      [nmemX b, memX a, neqLit b a] :=
    OmegaDerivable₂.contraction (by intro x hx; simp at hx ⊢; tauto) (extLeaf_base b a)
  have d1 : OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (OrdinalNotation.ofNat 1)
      [nmemX b ⋎ memX a, neqLit b a] := OmegaDerivable₂.or h01 d0
  have d2 : OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (OrdinalNotation.ofNat 1)
      [neqLit b a, nmemX b ⋎ memX a] :=
    OmegaDerivable₂.contraction (by intro x hx; simp at hx ⊢; tauto) d1
  exact OmegaDerivable₂.or h12 d2

/-! ### The two instantiations -/

/-- Substituting a term under a lifted one-point substitution is a single
two-point substitution — the second-order copy of
`Gentzen/AxiomsInduction.lean`'s `subst_q_subst`. -/
theorem subst_q_subst {N : ℕ} (σ : Semiformula ℒₒᵣ ℕ ℕ N 2)
    (t u : FirstOrder.SyntacticTerm ℒₒᵣ) :
    ((FirstOrder.Rew.subst ![u]).q ▹ σ)/[t] = FirstOrder.Rew.subst ![t, u] ▹ σ := by
  have hrew : (FirstOrder.Rew.subst ![t]).comp ((FirstOrder.Rew.subst ![u]).q)
      = FirstOrder.Rew.subst ![t, u] := by
    rw [FirstOrder.Rew.q_subst, FirstOrder.Rew.subst_comp_subst]
    congr 1
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j =>
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        simp
  show FirstOrder.Rew.subst ![t] ▹ (FirstOrder.Rew.subst ![u]).q ▹ σ = _
  rw [← FirstOrder.TransitiveRewriting.comp_app, hrew]

/-- The equality atom, rewritten and evaluated. -/
theorem subst_eqAtom (b a : ℕ) :
    ev₂ (FirstOrder.Rew.subst
        ![(numAt b : FirstOrder.SyntacticTerm ℒₒᵣ), (numAt a : FirstOrder.SyntacticTerm ℒₒᵣ)]
      ▹ (Semiformula.rel FirstOrder.Language.Eq.eq
          ![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2), (#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2)] :
          Semiproposition ℒₒᵣ 0 2)) = eqLit b a := by
  rw [Semiformula.rew_rel, ev₂_rel, eqLit]
  refine congrArg (fun v : Fin 2 → FirstOrder.SyntacticTerm ℒₒᵣ =>
    (Semiformula.rel FirstOrder.Language.Eq.eq v : Proposition ℒₒᵣ)) ?_
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ j =>
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      simp

/-- **The double instantiation.**  Substituting `ā` for `y` and then `b̄` for `x`
turns the matrix into the leaf. -/
theorem subst_extBody (b a : ℕ) :
    ev₂ (FirstOrder.Rew.subst
        ![(numAt b : FirstOrder.SyntacticTerm ℒₒᵣ), (numAt a : FirstOrder.SyntacticTerm ℒₒᵣ)]
      ▹ extBody) = extLeaf b a := by
  have hatom := subst_eqAtom b a
  simp only [extBody, LogicalConnective.DeMorgan.imply,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    ev₂_or, ev₂_neg, hatom, extLeaf, neg_eqLit]
  simp [memX, nmemX]

/-! ### The derivation -/

/-- **Set extensionality is cut-free derivable at height `ofNat 5`.** -/
theorem setExt_derivable :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (OrdinalNotation.ofNat 5)
      [ev₂ setExt] := by
  have hlt : ∀ {m n : ℕ}, m < n →
      (OrdinalNotation.ofNat m : O) < OrdinalNotation.ofNat n :=
    fun h => OrdinalNotation.ofNat_lt_ofNat h
  -- the inner ω-rule, at a fixed `a`
  have dinner : ∀ a : ℕ, OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0
      (OrdinalNotation.ofNat 3)
      [ev₂ ((∀¹ extBody)/[(numAt a : FirstOrder.SyntacticTerm ℒₒᵣ)])] := by
    intro a
    have he : ev₂ ((∀¹ extBody)/[(numAt a : FirstOrder.SyntacticTerm ℒₒᵣ)])
        = ∀¹ (ev₂ ((FirstOrder.Rew.subst ![numAt a]).q ▹ extBody)) := by
      simp
    rw [he]
    refine OmegaDerivable₂.omegaRule (Γ := []) (fun _ => OrdinalNotation.ofNat 2)
      (fun _ => hlt (by omega)) (fun b => ?_)
    rw [evInst₂_inst_ev, subst_q_subst, subst_extBody]
    exact extLeaf_derivable b a
  -- the outer ω-rule
  have douter : OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0
      (OrdinalNotation.ofNat 4) [ev₂ (∀¹ (∀¹ extBody))] := by
    rw [ev₂_all₁]
    refine OmegaDerivable₂.omegaRule (Γ := []) (fun _ => OrdinalNotation.ofNat 3)
      (fun _ => hlt (by omega)) (fun a => ?_)
    rw [evInst₂_inst_ev]
    exact dinner a
  -- the `(∀₂)` rule
  rw [setExt_eq, ev₂_all₂]
  refine OmegaDerivable₂.all₂ (Γ := []) (hlt (show 4 < 5 by omega)) ?_
  rw [SecondOrder.Sequent.shift₁_nil, ← ev₂_free₁', free₁_setExtBody]
  exact douter

end AxiomsLogic₂

end OrdinalAnalysis.ACAOmega
