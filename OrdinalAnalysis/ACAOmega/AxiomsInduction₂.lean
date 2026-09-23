/-
  The induction and comprehension axioms of `ACA`, replayed in the evaluating
  ω-calculus.

  `setInduction` is derived outright.  For the *schemata* — `indScheme₂ φ` and
  `arithComp₂ ψ`, both of which `ACA/LK.lean` closes universally over arbitrary
  numbers of set and number parameters (`allSets (allNums body)`) — what is
  delivered is the **machinery**, not a wrapper tied to one shape:

  * `all₂_step`  — one `∀²`, by the eigenvariable rule, at a singleton sequent;
  * `all₁_step`  — one `∀¹`, by the ω-rule;
  * `exs₁_step`, `exs₂_step` — the two existential rules, in the same shape;
  * `allN₁_derivable` — `k` nested `∀¹`s at once, by `k` ω-rules, with the
    premises given as the *simultaneous* numeral instances (the second-order
    copy of `Gentzen/AxiomsInduction.lean`'s `allClosure_derivable`);
  * `allN₂_derivable` — `M` nested `∀²`s at once, by `M` eigenvariable rules,
    with the premise given as the formula with all `M` set variables freed;
    `allN₂_eq_allSets` and `allN₁_eq_allNums` identify the two closures with
    `ACA/LK.lean`'s `allSets` and `allNums`, and `freeN₁_allN₁` says the two
    prefixes may be peeled independently;
  * `chain₂`, `succInd₂_derivable` — **the induction axiom for an arbitrary
    one-variable body**, at height `ω ⊕ 2`;
  * `iff_self_derivable` — the leaf every comprehension instance reduces to.

  Four things about the shape.

  * **No cut.**  The chain runs from `¬ψ(0̄)` and the negated induction step to
    `ψ(n̄)` by `n` applications of `exs`, with `and` joining the induction
    hypothesis to an identity sequent on `ψ(n+1‾)`.  The cut rank stays `0`.

  * **The chain is shorter than in the first order.**  `Gentzen`'s chain pays
    `2·complexity ψ` at every leaf, because its calculus has only *atomic*
    identity and has to build `[ψ, ∼ψ]` by hand.  `ACA_∞`'s `identity` is
    general and available at every height, so each leaf is at height `0` and the
    whole chain sits at `ofNat (2n)` — no `complexity` anywhere, hence no
    `irreducible_def` bookkeeping either.

  * **The evaluator does the arithmetic.**  The step's `n`-th instance mentions
    `ψ(n̄ + 1)` and the chain needs `ψ(n+1‾)`; `evInst₂` normalises `n̄ + 1` to
    `(n+1)‾` after substituting.  That is `inst_stepBody₂`.

  * **Comprehension is an identity.**  Once the witness `ψ` has been substituted
    for the comprehended set `Y`, the biconditional `x ∈ Y ↔ ψ(x)` has the same
    formula on both sides, and `iff_self_derivable` closes it at height
    `ofNat 2`.  All that a wrapper has to supply is the computation identifying
    the substituted instance with `θ 🡘 θ`.

  Contents.

    `omegaG`, `ofNat_lt_omegaG`      `ω`, as a `Gamma0Note`
    `all₂_step`, `all₁_step`, `exs₁_step`, `exs₂_step`
                                     the four quantifier rules, at singletons
    `iff_self_derivable`             **the comprehension leaf**
    `subst_subst₂`, `subst_q_substN` composing substitutions
    `allN₁`, `allN₁_derivable`       **the `∀¹`-closure, `k` at a time**
    `allN₂`, `freeN₁`, `freeN₁'`     the `∀²`-closure and its two iterations
    `freeN₁_all₂`, `freeN₁_free₁`    the two commutation lemmas it turns on
    `allN₂_derivable`                **the `∀²`-closure, `M` at a time**
    `freeN₁_all₁`, `freeN₁_allN₁`    freeing commutes with the `∀¹`-closure
    `allN₂_eq_allSets`, `allN₁_eq_allNums`
                                     the bridges to `ACA/LK.lean`'s spellings
    `succT`/`zeroT` arithmetic       `(#0+1)[n̄]` is ground and denotes `n+1`
    `stepBody₂`, `inst_stepBody₂`    the negated induction step and its instances
    `chain₂_aux`, `chain₂`           **the chain**, height `ofNat (2n)`
    `succInd₂`, `succInd₂_derivable` **the induction axiom**, height `ω ⊕ 2`
    `setInduction_derivable`         **`setInduction`**, height `ω ⊕ 3`
-/
import OrdinalAnalysis.ACAOmega.AxiomsLogic₂
import OrdinalAnalysis.Ordinal.Veblen.Instance

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA
open OrdinalAnalysis.ACAOmega.OmegaTruth₂

namespace AxiomsInduction₂

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-! ### `ω`, as a `Gamma0Note` -/

/-- `ω = ω ^ 1`, as a Veblen notation. -/
def omegaG : Gamma0Note := Gamma0Note.omegaPow 1

theorem ofNat_lt_omegaG (n : ℕ) : (OrdinalNotation.ofNat n : Gamma0Note) < omegaG := by
  show Gamma0Note.ofNat n < omegaG
  rw [Gamma0Note.lt_def, Gamma0Note.repr_ofNat, omegaG, Gamma0Note.repr_omegaPow,
    Gamma0Note.repr_one, Ordinal.opow_one]
  exact Ordinal.natCast_lt_omega0 n

theorem ofNat_zero_G : (OrdinalNotation.ofNat 0 : Gamma0Note) = 0 := rfl

theorem lt_nadd_ofNat {a : Gamma0Note} {j k : ℕ} (h : j < k) :
    OrdinalNotation.nadd a (OrdinalNotation.ofNat j)
      < OrdinalNotation.nadd a (OrdinalNotation.ofNat k) :=
  OrdinalNotation.nadd_lt_nadd_right a (OrdinalNotation.ofNat_lt_ofNat h)

theorem lt_nadd_one {a : Gamma0Note} : a < OrdinalNotation.nadd a (OrdinalNotation.ofNat 1) := by
  have h := lt_nadd_ofNat (a := a) (show 0 < 1 by omega)
  rw [ofNat_zero_G] at h
  simpa using h

/-! ### The four quantifier rules, at a singleton sequent

Each is the corresponding rule of `ACA_∞` with the context taken to be empty and
the conclusion evaluated; these are the primitives every axiom derivation in this
file and its successors is built from. -/

/-- **One `∀²`.** -/
theorem all₂_step {φ : Semiproposition ℒₒᵣ 1 0} {β α : O} (hlt : β < α)
    (h : OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ (Semiproposition.free₁ φ)]) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 α [ev₂ (∀² φ)] := by
  rw [ev₂_all₂]
  refine OmegaDerivable₂.all₂ (Γ := []) hlt ?_
  rw [SecondOrder.Sequent.shift₁_nil, ← ev₂_free₁']
  exact h

/-- **One `∀¹`, by the ω-rule.** -/
theorem all₁_step {φ : Semiproposition ℒₒᵣ 0 1} {α : O} (β : ℕ → O) (hlt : ∀ m, β m < α)
    (h : ∀ m : ℕ, OmegaDerivable₂ trueArithLits₂ evInst₂ 0 (β m)
      [ev₂ (φ/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)])]) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 α [ev₂ (∀¹ φ)] := by
  rw [ev₂_all₁]
  refine OmegaDerivable₂.omegaRule (Γ := []) β hlt (fun m => ?_)
  rw [evInst₂_inst_ev]
  exact h m

/-- **One `∃¹`.** -/
theorem exs₁_step {φ : Semiproposition ℒₒᵣ 0 1} {β α : O} (m : ℕ) (hlt : β < α)
    (h : OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β
      [ev₂ (φ/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)])]) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 α [ev₂ (∃¹ φ)] := by
  rw [ev₂_exs₁]
  refine OmegaDerivable₂.exs (Γ := []) m hlt ?_
  rw [evInst₂_inst_ev]
  exact h

/-- **One `∃²`, at an arithmetical witness.** -/
theorem exs₂_step {φ : Semiproposition ℒₒᵣ 1 0} {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1}
    (hψ : Arith ψ) {β α : O} (hlt : β < α)
    (h : OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ (φ/⟦ψ⟧)]) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 α [ev₂ (∃² φ)] := by
  rw [ev₂_exs₂]
  refine OmegaDerivable₂.exs₂ (Γ := []) hψ hlt ?_
  rw [evInst₂_inst₂_ev]
  exact h

/-! ### The comprehension leaf

Once the witness has been substituted for the comprehended set, the two sides of
`x ∈ Y ↔ ψ(x)` are the *same* formula, and general identity closes the sequent.
This is the whole content of an arithmetical comprehension instance; a wrapper
only has to identify the substituted instance with `θ 🡘 θ`. -/

/-- **`θ ↔ θ` is derivable at height `ofNat 2`**, cut-free. -/
theorem iff_self_derivable (θ : Proposition ℒₒᵣ) {α : O}
    (hlt : (OrdinalNotation.ofNat 2 : O) ≤ α) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 α [θ 🡘 θ] := by
  have h01 : (OrdinalNotation.ofNat 0 : O) < OrdinalNotation.ofNat 1 :=
    OrdinalNotation.ofNat_lt_ofNat (by omega)
  have h12 : (OrdinalNotation.ofNat 1 : O) < OrdinalNotation.ofNat 2 :=
    OrdinalNotation.ofNat_lt_ofNat (by omega)
  have hid : OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (OrdinalNotation.ofNat 0)
      [∼θ, θ] := OmegaDerivable₂.identity θ |>.contraction (by intro x hx; simp at hx ⊢; tauto)
  have hor : OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (OrdinalNotation.ofNat 1)
      [∼θ ⋎ θ] := OmegaDerivable₂.or (Γ := []) h01 hid
  refine OmegaDerivable₂.mono_ord ?_ hlt
  show OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (OrdinalNotation.ofNat 2)
    [(θ 🡒 θ) ⋏ (θ 🡒 θ)]
  exact OmegaDerivable₂.and (Γ := []) h12 h12 hor hor

/-! ### Composing substitutions -/

/-- Substituting into a substitution instance is a single substitution. -/
theorem subst_subst₂ {N n : ℕ} (ψ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (s : FirstOrder.Semiterm ℒₒᵣ ℕ 1) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    FirstOrder.Rew.subst ![t] ▹ (ψ/[s]) = ψ/[FirstOrder.Rew.subst ![t] s] := by
  have hrew : (FirstOrder.Rew.subst ![t]).comp (FirstOrder.Rew.subst ![s])
      = FirstOrder.Rew.subst ![FirstOrder.Rew.subst ![t] s] := by
    rw [FirstOrder.Rew.subst_comp_subst]
    congr 1
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp
  show FirstOrder.Rew.subst ![t] ▹ FirstOrder.Rew.subst ![s] ▹ ψ = _
  rw [← FirstOrder.TransitiveRewriting.comp_app, hrew]

theorem subst_bvar_subst₂ {N n : ℕ} (ψ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    FirstOrder.Rew.subst ![t] ▹ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)]) = ψ/[t] := by
  rw [subst_subst₂]
  simp

/-- Substituting a term under a lifted simultaneous substitution is a single
simultaneous substitution with the term prepended. -/
theorem subst_q_substN {N k : ℕ} (σ : Semiformula ℒₒᵣ ℕ ℕ N (k + 1))
    (v : Fin k → FirstOrder.SyntacticTerm ℒₒᵣ) (t : FirstOrder.SyntacticTerm ℒₒᵣ) :
    ((FirstOrder.Rew.subst v).q ▹ σ)/[t] = FirstOrder.Rew.subst (t :> v) ▹ σ := by
  have hrew : (FirstOrder.Rew.subst ![t]).comp ((FirstOrder.Rew.subst v).q)
      = FirstOrder.Rew.subst (t :> v) := by
    rw [FirstOrder.Rew.q_subst, FirstOrder.Rew.subst_comp_subst]
    congr 1
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  show FirstOrder.Rew.subst ![t] ▹ (FirstOrder.Rew.subst v).q ▹ σ = _
  rw [← FirstOrder.TransitiveRewriting.comp_app, hrew]

/-! ### The `∀¹`-closure, `k` quantifiers at a time -/

/-- `∀¹` repeated `k` times.  Unlike the `∀²`-closure this needs no dependent
index juggling: the number of *set* variables is untouched. -/
def allN₁ {N : ℕ} : (k : ℕ) → Semiformula ℒₒᵣ ℕ ℕ N k → Semiformula ℒₒᵣ ℕ ℕ N 0
  | 0, σ => σ
  | k + 1, σ => allN₁ k (∀¹ σ)

@[simp] theorem allN₁_zero {N : ℕ} (σ : Semiformula ℒₒᵣ ℕ ℕ N 0) : allN₁ 0 σ = σ := rfl

@[simp] theorem allN₁_succ {N k : ℕ} (σ : Semiformula ℒₒᵣ ℕ ℕ N (k + 1)) :
    allN₁ (k + 1) σ = allN₁ k (∀¹ σ) := rfl

/-- **The `∀¹`-closure, with the bookkeeping index made explicit.**  The
second-order copy of `Gentzen/AxiomsInduction.lean`'s `allClosure_aux`. -/
theorem allN₁_aux (β : Gamma0Note) :
    ∀ (k j : ℕ) (σ : Semiproposition ℒₒᵣ 0 k),
      (∀ w : Fin k → ℕ, OmegaDerivable₂ trueArithLits₂ evInst₂ 0
          (OrdinalNotation.nadd β (OrdinalNotation.ofNat j))
          [ev₂ (FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))
            ▹ σ)]) →
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0
        (OrdinalNotation.nadd β (OrdinalNotation.ofNat (j + k))) [ev₂ (allN₁ k σ)] := by
  intro k
  induction k with
  | zero =>
      intro j σ h
      have h0 := h ![]
      have he : (FirstOrder.Rew.subst (fun i : Fin 0 =>
          (numAt (![] i) : FirstOrder.SyntacticTerm ℒₒᵣ)) ▹ σ) = σ := by
        have : (FirstOrder.Rew.subst (fun i : Fin 0 =>
            (numAt (![] i) : FirstOrder.SyntacticTerm ℒₒᵣ))
              : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) = FirstOrder.Rew.id := by
          rw [← FirstOrder.Rew.subst_eq_id]
          congr 1
          funext i
          exact i.elim0
        rw [this]
        simp
      rw [allN₁_zero]
      simpa [he] using h0
  | succ k ih =>
      intro j σ h
      have harith : j + (k + 1) = (j + 1) + k := by omega
      rw [allN₁_succ, harith]
      refine ih (j + 1) (∀¹ σ) (fun w => ?_)
      have hall : (FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))
            ▹ (∀¹ σ))
          = ∀¹ ((FirstOrder.Rew.subst
              (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q ▹ σ) := by
        simp
      rw [hall]
      refine all₁_step (fun _ => OrdinalNotation.nadd β (OrdinalNotation.ofNat j))
        (fun _ => lt_nadd_ofNat (by omega)) (fun m => ?_)
      rw [subst_q_substN]
      have hv : (numAt m :> fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))
          = fun i => (numAt (((m :> w) : Fin (k + 1) → ℕ) i) :
            FirstOrder.SyntacticTerm ℒₒᵣ) := by
        funext i
        induction i using Fin.cases with
        | zero => simp
        | succ j => simp
      rw [hv]
      exact h (m :> w)

/-- **The `∀¹`-closure.**  A `k`-fold universal closure is derivable once every
simultaneous numeral instance is, at `k` more than their common height. -/
theorem allN₁_derivable {k : ℕ} (σ : Semiproposition ℒₒᵣ 0 k) {β : Gamma0Note}
    (h : ∀ w : Fin k → ℕ, OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β
        [ev₂ (FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))
          ▹ σ)]) :
    OmegaDerivable₂ trueArithLits₂ evInst₂ 0
      (OrdinalNotation.nadd β (OrdinalNotation.ofNat k)) [ev₂ (allN₁ k σ)] := by
  have key := allN₁_aux β k 0 σ (by
    intro w
    have hw := h w
    rw [ofNat_zero_G]
    simpa using hw)
  simpa using key

/-! ### The successor term -/

/-- The successor term with a numeral substituted is ground. -/
theorem ground_subst_succT (n : ℕ) :
    Ground (FirstOrder.Rew.subst ![(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)] succT) := by
  refine ground_of_closed
    (Gentzen.LowerSyntax.freeVariables_rew_term_eq_empty _ ?_ (fun i => ?_))
  · simp only [succT, FirstOrder.Semiterm.Operator.operator,
      FirstOrder.Semiterm.Operator.Add.term_eq, FirstOrder.Rew.func,
      FirstOrder.Semiterm.freeVariables_func, Finset.biUnion_eq_empty,
      Finset.mem_univ, forall_const]
    intro i
    induction i using Fin.cases with
    | zero => simp
    | succ j =>
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        simp only [Function.comp_apply, FirstOrder.Rew.emb_bvar, FirstOrder.Rew.subst_bvar]
        exact Gentzen.LowerSyntax.freeVariables_rew_term_eq_empty _
          FirstOrder.Semiterm.freeVariables_emb (fun i => i.elim0)
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp

/-- …and denotes `n + 1`. -/
theorem evTerm_subst_succT (n : ℕ) :
    evTerm (FirstOrder.Rew.subst ![(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)] succT) = n + 1 := by
  rw [evTerm, FirstOrder.Semiterm.val_rew]
  simp [succT]

/-- `0` in `succInd₂` is the numeral `0̄`. -/
theorem zeroT_eq : (zeroT : FirstOrder.SyntacticTerm ℒₒᵣ) = numAt 0 := by
  simp [zeroT, numAt]

/-! ### The chain -/

/-- The body of the existential that the negated induction step is. -/
def stepBody₂ (ψ : Semiproposition ℒₒᵣ 0 1) : Semiproposition ℒₒᵣ 0 1 :=
  ev₂ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)]) ⋏ ∼ev₂ (ψ/[succT])

/-- The negation of the (evaluated) induction step, in the shape the `exs` rule
takes. -/
theorem neg_step₂ (ψ : Semiproposition ℒₒᵣ 0 1) :
    ∼ev₂ (∀¹ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)] 🡒 ψ/[succT])) = ∃¹ stepBody₂ ψ := by
  simp [stepBody₂, LogicalConnective.DeMorgan.imply]

/-- **The instance computation.**  This is where the `n̄ + 1` of the syntax and
the `(n+1)‾` of the ω-rule are reconciled: the evaluator absorbs the
difference. -/
theorem inst_stepBody₂ (ψ : Semiproposition ℒₒᵣ 0 1) (n : ℕ) :
    evInst₂.inst (stepBody₂ ψ) n
      = ev₂ (ψ/[(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)])
        ⋏ ∼ev₂ (ψ/[(numAt (n + 1) : FirstOrder.SyntacticTerm ℒₒᵣ)]) := by
  have hA : ev₂ ((ev₂ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)]))/[
      (numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)])
      = ev₂ (ψ/[(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)]) := by
    rw [ev₂_rew_ev₂ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)]) 0
      (FirstOrder.Rew.subst ![(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)])]
    exact congrArg ev₂ (subst_bvar_subst₂ ψ (numAt n))
  have hB : ev₂ ((ev₂ (ψ/[succT]))/[(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)])
      = ev₂ (ψ/[(numAt (n + 1) : FirstOrder.SyntacticTerm ℒₒᵣ)]) := by
    rw [ev₂_rew_ev₂ (ψ/[succT]) 0
      (FirstOrder.Rew.subst ![(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)])]
    rw [subst_subst₂ ψ succT (numAt n), ev₂_subst_ground ψ (ground_subst_succT n),
      evTerm_subst_succT]
  rw [evInst₂_inst, stepBody₂]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg,
    ev₂_and, ev₂_neg, hA, hB]

/-- **The chain, in membership form.**  From `¬ψ(0̄)`, the negated induction step
and `ψ(n̄)` in the sequent, a cut-free derivation of height `2n`. -/
theorem chain₂_aux (ψ : Semiproposition ℒₒᵣ 0 1) :
    ∀ (n : ℕ) (Γ : SecondOrder.Sequent ℒₒᵣ),
      ∼ev₂ (ψ/[(zeroT : FirstOrder.SyntacticTerm ℒₒᵣ)]) ∈ Γ → (∃¹ stepBody₂ ψ) ∈ Γ →
      ev₂ (ψ/[(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)]) ∈ Γ →
      OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0
        (OrdinalNotation.ofNat (2 * n)) Γ := by
  intro n
  induction n with
  | zero =>
      intro Γ hZ _ hP
      refine OmegaDerivable₂.of_mem_identity
        (ev₂ (ψ/[(numAt 0 : FirstOrder.SyntacticTerm ℒₒᵣ)])) hP ?_
      rw [← zeroT_eq]
      exact hZ
  | succ n ih =>
      intro Γ hZ hS hP
      have hlt₁ : (OrdinalNotation.ofNat (2 * n) : O)
          < OrdinalNotation.ofNat (2 * n + 1) := OrdinalNotation.ofNat_lt_ofNat (by omega)
      have hlt₂ : (OrdinalNotation.ofNat 0 : O)
          < OrdinalNotation.ofNat (2 * n + 1) := OrdinalNotation.ofNat_lt_ofNat (by omega)
      have hlt₃ : (OrdinalNotation.ofNat (2 * n + 1) : O)
          < OrdinalNotation.ofNat (2 * (n + 1)) := OrdinalNotation.ofNat_lt_ofNat (by omega)
      have d₁ : OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0
          (OrdinalNotation.ofNat (2 * n))
          (ev₂ (ψ/[(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)]) :: Γ) :=
        ih _ (List.mem_cons_of_mem _ hZ) (List.mem_cons_of_mem _ hS) List.mem_cons_self
      have d₂ : OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0
          (OrdinalNotation.ofNat 0)
          (∼ev₂ (ψ/[(numAt (n + 1) : FirstOrder.SyntacticTerm ℒₒᵣ)]) :: Γ) :=
        OmegaDerivable₂.of_mem_identity
          (ev₂ (ψ/[(numAt (n + 1) : FirstOrder.SyntacticTerm ℒₒᵣ)]))
          (List.mem_cons_of_mem _ hP) List.mem_cons_self
      have d₃ : OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0
          (OrdinalNotation.ofNat (2 * n + 1)) (evInst₂.inst (stepBody₂ ψ) n :: Γ) := by
        rw [inst_stepBody₂]
        exact OmegaDerivable₂.and hlt₁ hlt₂ d₁ d₂
      exact OmegaDerivable₂.drop_head (OmegaDerivable₂.exs n hlt₃ d₃) hS

/-- **The chain**, as a three-element sequent. -/
theorem chain₂ (ψ : Semiproposition ℒₒᵣ 0 1) (n : ℕ) :
    OmegaDerivable₂ (O := O) trueArithLits₂ evInst₂ 0 (OrdinalNotation.ofNat (2 * n))
      [∼ev₂ (ψ/[(zeroT : FirstOrder.SyntacticTerm ℒₒᵣ)]),
       ∼ev₂ (∀¹ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)] 🡒 ψ/[succT])),
       ev₂ (ψ/[(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)])] :=
  chain₂_aux ψ n _ (by simp) (by rw [← neg_step₂]; simp) (by simp)

/-! ### The induction axiom for an arbitrary body -/

/-- The induction axiom for the one-variable body `ψ`. -/
def succInd₂ (ψ : Semiproposition ℒₒᵣ 0 1) : Proposition ℒₒᵣ :=
  ((ψ/[(zeroT : FirstOrder.SyntacticTerm ℒₒᵣ)]) ⋏
      (∀¹ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)] 🡒 ψ/[succT])))
    🡒 ∀¹ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)])

/-- `ev₂` of an induction axiom, in the shape the two `or` rules produce. -/
theorem ev₂_succInd₂ (ψ : Semiproposition ℒₒᵣ 0 1) :
    ev₂ (succInd₂ ψ)
      = (∼ev₂ (ψ/[(zeroT : FirstOrder.SyntacticTerm ℒₒᵣ)]) ⋎
          ∼ev₂ (∀¹ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)] 🡒 ψ/[succT])))
        ⋎ (∀¹ (ev₂ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)]))) := by
  simp [succInd₂, LogicalConnective.DeMorgan.imply]

/-- **The induction axiom for an arbitrary body is cut-free derivable at height
`ω ⊕ 2`.** -/
theorem succInd₂_derivable (ψ : Semiproposition ℒₒᵣ 0 1) :
    OmegaDerivable₂ trueArithLits₂ evInst₂ 0
      (OrdinalNotation.nadd omegaG (OrdinalNotation.ofNat 2)) [ev₂ (succInd₂ ψ)] := by
  have h1 : omegaG < OrdinalNotation.nadd omegaG (OrdinalNotation.ofNat 1) := lt_nadd_one
  have h2 : OrdinalNotation.nadd omegaG (OrdinalNotation.ofNat 1)
      < OrdinalNotation.nadd omegaG (OrdinalNotation.ofNat 2) := lt_nadd_ofNat (by omega)
  have hinst : ∀ n : ℕ,
      evInst₂.inst (ev₂ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)])) n
        = ev₂ (ψ/[(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)]) := by
    intro n
    rw [evInst₂_inst_ev]
    exact congrArg ev₂ (subst_bvar_subst₂ ψ (numAt n))
  -- the ω-rule
  have dω : OmegaDerivable₂ trueArithLits₂ evInst₂ 0 omegaG
      ((∀¹ (ev₂ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)])))
        :: [∼ev₂ (ψ/[(zeroT : FirstOrder.SyntacticTerm ℒₒᵣ)]),
            ∼ev₂ (∀¹ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)] 🡒 ψ/[succT]))]) := by
    refine OmegaDerivable₂.omegaRule
      (fun n => OrdinalNotation.ofNat (2 * n)) (fun n => ofNat_lt_omegaG _) (fun n => ?_)
    rw [hinst n]
    exact OmegaDerivable₂.contraction (by intro x hx; simp at hx ⊢; tauto) (chain₂ ψ n)
  -- the first `or`, joining the two negated hypotheses
  have d₁ : OmegaDerivable₂ trueArithLits₂ evInst₂ 0
      (OrdinalNotation.nadd omegaG (OrdinalNotation.ofNat 1))
      [∼ev₂ (ψ/[(zeroT : FirstOrder.SyntacticTerm ℒₒᵣ)]) ⋎
          ∼ev₂ (∀¹ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)] 🡒 ψ/[succT])),
       ∀¹ (ev₂ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)]))] :=
    OmegaDerivable₂.or h1
      (OmegaDerivable₂.contraction (by intro x hx; simp at hx ⊢; tauto) dω)
  -- the second `or`
  have d₂ : OmegaDerivable₂ trueArithLits₂ evInst₂ 0
      (OrdinalNotation.nadd omegaG (OrdinalNotation.ofNat 2))
      [(∼ev₂ (ψ/[(zeroT : FirstOrder.SyntacticTerm ℒₒᵣ)]) ⋎
          ∼ev₂ (∀¹ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)] 🡒 ψ/[succT])))
        ⋎ (∀¹ (ev₂ (ψ/[(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1)])))] :=
    OmegaDerivable₂.or (Γ := []) h2 d₁
  rw [ev₂_succInd₂]
  exact d₂

/-! ### The `∀²`-closure, `M` quantifiers at a time

The `∀²`-closure is the one place where the dependent index gets in the way:
`allN₂ (M+1) φ = allN₂ M (∀² φ)` applies `∀²` *innermost first*, while the
`(∀₂)` rule of the calculus introduces the *outermost* one.  The two are
reconciled by `freeN₁'`, the iteration of `free₁` that stops one set binder
short, together with the two commutation lemmas `freeN₁_all₂` and
`freeN₁_free₁`: `free₁` commutes with `∀²` (because `Rew.free` is its own `q`),
so pushing `M` copies of `free₁` past one `∀²` costs nothing. -/

/-- `∀²` repeated `M` times. -/
def allN₂ {n : ℕ} : (M : ℕ) → Semiproposition ℒₒᵣ M n → Semiproposition ℒₒᵣ 0 n
  | 0, φ => φ
  | M + 1, φ => allN₂ M (∀² φ)

@[simp] theorem allN₂_zero {n : ℕ} (φ : Semiproposition ℒₒᵣ 0 n) : allN₂ 0 φ = φ := rfl

@[simp] theorem allN₂_succ {M n : ℕ} (φ : Semiproposition ℒₒᵣ (M + 1) n) :
    allN₂ (M + 1) φ = allN₂ M (∀² φ) := rfl

/-- `free₁` repeated `M` times. -/
def freeN₁ {n : ℕ} : (M : ℕ) → Semiproposition ℒₒᵣ M n → Semiproposition ℒₒᵣ 0 n
  | 0, φ => φ
  | M + 1, φ => freeN₁ M (Semiproposition.free₁ φ)

@[simp] theorem freeN₁_zero {n : ℕ} (φ : Semiproposition ℒₒᵣ 0 n) : freeN₁ 0 φ = φ := rfl

@[simp] theorem freeN₁_succ {M n : ℕ} (φ : Semiproposition ℒₒᵣ (M + 1) n) :
    freeN₁ (M + 1) φ = freeN₁ M (Semiproposition.free₁ φ) := rfl

/-- `free₁` repeated `M` times, stopping one set binder short. -/
def freeN₁' {n : ℕ} : (M : ℕ) → Semiproposition ℒₒᵣ (M + 1) n → Semiproposition ℒₒᵣ 1 n
  | 0, φ => φ
  | M + 1, φ => freeN₁' M (Semiproposition.free₁ φ)

@[simp] theorem freeN₁'_zero {n : ℕ} (φ : Semiproposition ℒₒᵣ 1 n) : freeN₁' 0 φ = φ := rfl

@[simp] theorem freeN₁'_succ {M n : ℕ} (φ : Semiproposition ℒₒᵣ (M + 2) n) :
    freeN₁' (M + 1) φ = freeN₁' M (Semiproposition.free₁ φ) := rfl

/-- **`free₁` commutes with `∀²`**, because `Rew.free` is its own `q`. -/
theorem free₁_all₂ {M n : ℕ} (φ : Semiproposition ℒₒᵣ (M + 2) n) :
    Semiproposition.free₁ (∀² φ : Semiproposition ℒₒᵣ (M + 1) n)
      = ∀² (Semiproposition.free₁ φ) := by
  show SecondOrder.Rew.free.app (∀² φ) = ∀² (SecondOrder.Rew.free.app φ)
  rw [SecondOrder.Rew.app_all₁, SecondOrder.Rew.q_free]

/-- **`free₁` commutes with `∀¹`** — a set rewriting does not see a number
binder. -/
theorem free₁_all₁ {M n : ℕ} (φ : Semiproposition ℒₒᵣ (M + 1) (n + 1)) :
    Semiproposition.free₁ (∀¹ φ) = ∀¹ (Semiproposition.free₁ φ) := rfl

/-- The first commutation lemma: `M` copies of `free₁` pass through one `∀²`. -/
theorem freeN₁_all₂ {n : ℕ} :
    ∀ (M : ℕ) (φ : Semiproposition ℒₒᵣ (M + 1) n),
      freeN₁ M (∀² φ) = ∀² (freeN₁' M φ)
  | 0, _ => rfl
  | M + 1, φ => by
      rw [freeN₁_succ, free₁_all₂, freeN₁_all₂ M (Semiproposition.free₁ φ), freeN₁'_succ]

/-- The second commutation lemma: `M + 1` copies of `free₁` split as `M` copies
followed by one. -/
theorem freeN₁_free₁ {n : ℕ} :
    ∀ (M : ℕ) (φ : Semiproposition ℒₒᵣ (M + 1) n),
      freeN₁ M (Semiproposition.free₁ φ) = Semiproposition.free₁ (freeN₁' M φ)
  | 0, _ => rfl
  | M + 1, φ => by
      rw [freeN₁_succ, freeN₁_free₁ M (Semiproposition.free₁ φ), freeN₁'_succ]

/-- **The `∀²`-closure, with the bookkeeping index made explicit.** -/
theorem allN₂_aux (β : Gamma0Note) :
    ∀ (M j : ℕ) (φ : Semiproposition ℒₒᵣ M 0),
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0
        (OrdinalNotation.nadd β (OrdinalNotation.ofNat j)) [ev₂ (freeN₁ M φ)] →
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0
        (OrdinalNotation.nadd β (OrdinalNotation.ofNat (j + M))) [ev₂ (allN₂ M φ)] := by
  intro M
  induction M with
  | zero => intro j φ h; simpa using h
  | succ M ih =>
      intro j φ h
      have harith : j + (M + 1) = (j + 1) + M := by omega
      rw [allN₂_succ, harith]
      refine ih (j + 1) (∀² φ) ?_
      rw [freeN₁_all₂]
      refine all₂_step (β := OrdinalNotation.nadd β (OrdinalNotation.ofNat j))
        (lt_nadd_ofNat (by omega)) ?_
      rw [← freeN₁_free₁]
      exact h

/-- **The `∀²`-closure.**  An `M`-fold set-quantifier closure is derivable once
the formula with all `M` set variables freed is, at `M` more than its height.

This is the missing half of the universal-closure machinery: together with
`allN₁_derivable` it reduces any axiom of the shape `∀²…∀² ∀¹…∀¹ body` to its
fully instantiated bodies. -/
theorem allN₂_derivable {M : ℕ} (φ : Semiproposition ℒₒᵣ M 0) {β : Gamma0Note}
    (h : OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ (freeN₁ M φ)]) :
    OmegaDerivable₂ trueArithLits₂ evInst₂ 0
      (OrdinalNotation.nadd β (OrdinalNotation.ofNat M)) [ev₂ (allN₂ M φ)] := by
  have key := allN₂_aux β M 0 φ (by rw [ofNat_zero_G]; simpa using h)
  simpa using key

/-- `M` copies of `free₁` pass through one `∀¹`. -/
theorem freeN₁_all₁ {n : ℕ} : ∀ (M : ℕ) (φ : Semiproposition ℒₒᵣ M (n + 1)),
    freeN₁ M (∀¹ φ) = ∀¹ (freeN₁ M φ)
  | 0, _ => rfl
  | M + 1, φ => by
      rw [freeN₁_succ, free₁_all₁, freeN₁_all₁ M (Semiproposition.free₁ φ), freeN₁_succ]

/-- **Freeing the set variables commutes with the `∀¹`-closure.**  This is what
lets an axiom `∀²…∀² ∀¹…∀¹ body` be attacked set quantifiers first: the
`∀¹`-prefix is untouched by the eigenvariable rule. -/
theorem freeN₁_allN₁ {M : ℕ} : ∀ (k : ℕ) (φ : Semiproposition ℒₒᵣ M k),
    freeN₁ M (allN₁ k φ) = allN₁ k (freeN₁ M φ)
  | 0, _ => rfl
  | k + 1, φ => by
      rw [allN₁_succ, freeN₁_allN₁ k (∀¹ φ), freeN₁_all₁, allN₁_succ]

/-- `allN₂` is `ACA/LK.lean`'s `allSets`. -/
theorem allN₂_eq_allSets {n : ℕ} : ∀ (M : ℕ) (φ : Semiproposition ℒₒᵣ M n),
    allN₂ M φ = allSets φ
  | 0, _ => rfl
  | M + 1, φ => allN₂_eq_allSets M (∀² φ)

/-- `allN₁` is `ACA/LK.lean`'s `allNums`. -/
theorem allN₁_eq_allNums {N : ℕ} : ∀ (k : ℕ) (φ : Semiproposition ℒₒᵣ N k),
    allN₁ k φ = allNums φ
  | 0, _ => rfl
  | k + 1, φ => allN₁_eq_allNums k (∀¹ φ)

/-! ### `setInduction` -/

/-- The body of `setInduction` after the `∀²` has been stripped: induction for
the formula `x ∈ X`, with `X` the free set variable `0`. -/
def memBody : Semiproposition ℒₒᵣ 0 1 := (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0

/-- The matrix of `setInduction`, before the `∀²` is stripped. -/
def setInductionBody : Semiproposition ℒₒᵣ 1 0 :=
  (((zeroT : FirstOrder.Semiterm ℒₒᵣ ℕ 0) ∈# (0 : Fin 1)) ⋏
      (∀¹ (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)) 🡒
        ((succT : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)))))
    🡒 (∀¹ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)))

theorem setInduction_eq : setInduction = ∀² setInductionBody := rfl

/-- **Stripping the `∀²` turns `setInduction` into `succInd₂ memBody`.** -/
theorem free₁_setInductionBody :
    Semiproposition.free₁ setInductionBody = succInd₂ memBody := by
  simp [setInductionBody, succInd₂, memBody, LogicalConnective.DeMorgan.imply,
    SecondOrder.Rew.free]

/-- **`setInduction` is cut-free derivable at height `ω ⊕ 3`.** -/
theorem setInduction_derivable :
    OmegaDerivable₂ trueArithLits₂ evInst₂ 0
      (OrdinalNotation.nadd omegaG (OrdinalNotation.ofNat 3)) [ev₂ setInduction] := by
  rw [setInduction_eq]
  refine all₂_step (β := OrdinalNotation.nadd omegaG (OrdinalNotation.ofNat 2))
    (lt_nadd_ofNat (by omega)) ?_
  rw [free₁_setInductionBody]
  exact succInd₂_derivable memBody

end AxiomsInduction₂

end OrdinalAnalysis.ACAOmega
