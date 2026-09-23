/-
  The induction axioms of `PA[X]`, replayed in the ω-calculus.

  Every other axiom of `paLX` — the equality axioms, `PA⁻` transported along
  `toLX` — is a true closed `X`-free sentence, and `OmegaTruth.omega_complete`
  derives those at a *finite* height.  The induction schema is the exception, and
  it is the reason the calculus exists: the ω-rule replaces induction, and the
  price is that the derivation of the `n`-th instance is `n` inferences long, so
  the height is `ω + 2` rather than a natural number.  This is the one place
  where the ω-rule's *individual* premise ordinals (`Calculus.lean`) are used.

  Four things about the shape.

  * **No cut.**  The chain runs from `¬ψ(0̄)` and the negated induction step to
    `ψ(n̄)` by `n` applications of `exs` — one for each instance of the step —
    with `and` joining the induction hypothesis to an identity sequent on
    `ψ(n+1‾)`.  The textbook argument cuts on `ψ(n̄)`; here the `and` rule of the
    one-sided calculus does the same work with no cut formula at all, which is
    what keeps the cut rank at `0`.

  * **The evaluator does the arithmetic.**  The step's `n`-th instance mentions
    `ψ(n̄ + 1)`, and the chain needs `ψ(n+1‾)`; those are different formulas, and
    the calculus has no equality reasoning about `X` to bridge them
   .  What bridges them is that the instantiation is
    `evInst`: it normalises `n̄ + 1` to `(n+1)‾` after substituting.  That is
    `inst_stepBody`, and it is the whole content of the successor step.

  * **The three occurrences of the body are all the same substitution.**  `succInd`
    is built from `ψ/[0̄]`, `ψ/[#0]`, `ψ/[#0 + 1]` and `ψ/[#0]`; composing a
    substitution with any of them is a single substitution (`subst_subst`), which
    is what turns the ω-rule's premises into the members of the chain.

  * **The universal closure is peeled by the ω-rule too.**  An axiom of
    `InductionScheme LX Set.univ` is `univCl (succInd φ)`, and `univCl` closes
    over the free variables of `succInd φ` — of which there may be any number.
    `allClosure_derivable` discharges them one at a time, each by an ω-rule, and
    `subst_comp_fixitr_eq_map` identifies the resulting numeral instances with
    numeral *assignments*, at which point `numSubst_succInd` says an assignment
    passes through `succInd` untouched.  So the final height is `ω + 2 + k` for
    `k` the number of variables closed over — but only its existence is claimed,
    because that is all the embedding needs.

  Contents.

    `sucT`, `zeroT`              the two closed pieces of `succInd`
    `subst_sucT`, `evTerm_subst_sucT`
                                 `(#0 + 1)[n̄]` is ground and denotes `n + 1`
    `subst_subst`                composing two substitutions
    `stepBody`, `neg_step`       the negated induction step is an `∃`
    `inst_stepBody`              **its `n`-th instance is `ψ(n̄) ⋏ ¬ψ(n+1‾)`**
    `chain_aux`, `chain`         **Step 1** — the chain, height `2c + 2n`
    `ev_succInd`, `succInd_derivable`
                                 **Step 2** — the closed axiom, height `ω + 2`
    `subst_q_subst`, `allClosure_aux`, `allClosure_derivable`
                                 **Step 3** — peeling a universal closure
    `numSubst_succInd`           a numeral assignment passes through `succInd`
    `induction_axiom_derivable`  **Step 4** — every induction axiom of `PA[X]`
-/
import OrdinalAnalysis.Gentzen.EvInst
import OrdinalAnalysis.Gentzen.NumSubst
import OrdinalAnalysis.Omega.Identity

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.AxiomsInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open OrdinalAnalysis.Gentzen OrdinalAnalysis.Gentzen.StandardLX
open OrdinalAnalysis.Gentzen.Evaluate OrdinalAnalysis.Gentzen.OmegaTruth
open OrdinalAnalysis.Gentzen.EvInst

/-- the successor term `#0 + 1` at level 1 -/
def sucT : Semiterm LX ℕ 1 := ‘(#0 + 1)’

/-- the constant `0` as it occurs in `succInd` -/
def zeroT : SyntacticTerm LX := ((0 : ℕ) : SyntacticTerm LX)

theorem zeroT_eq : zeroT = numLX 0 := by simp [zeroT, numLX]

/-- `+` in operator form is `+` in function form. -/
theorem add_operator_eq_func {n : ℕ} (a b : Semiterm LX ℕ n) :
    Semiterm.Operator.Add.add.operator ![a, b]
      = Semiterm.func (Language.Add.add : LX.Func 2) ![a, b] := by
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func]
  exact congrArg (Semiterm.func (Language.Add.add : LX.Func 2))
    (by funext i; fin_cases i <;> simp)

/-- The successor term with a numeral substituted. -/
theorem subst_sucT (n : ℕ) :
    Rew.subst ![numLX n] sucT
      = Semiterm.func (Language.Add.add : LX.Func 2) ![numLX n, numLX 1] := by
  rw [← add_operator_eq_func]
  simp [sucT, numLX]

theorem ground_subst_sucT (n : ℕ) : Ground (Rew.subst ![numLX n] sucT) := by
  rw [subst_sucT]
  refine (ground_func_iff _ _).mpr fun i => ?_
  fin_cases i <;> simp

theorem evTerm_subst_sucT (n : ℕ) : evTerm (Rew.subst ![numLX n] sucT) = n + 1 := by
  rw [subst_sucT, evTerm_func]
  have h : (fun i => evTerm ((![numLX n, numLX 1] : Fin 2 → SyntacticTerm LX) i))
      = ![n, 1] := by
    funext i
    fin_cases i <;> simp
  rw [h]
  rfl

/-! ### Composing substitutions -/

/-- Substituting into a substitution instance is a single substitution. -/
theorem subst_subst {n : ℕ} (ψ : Semiformula LX ℕ 1) (s : Semiterm LX ℕ 1)
    (t : Semiterm LX ℕ n) :
    Rew.subst ![t] ▹ (ψ/[s]) = ψ/[Rew.subst ![t] s] := by
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]

theorem subst_bvar_subst {n : ℕ} (ψ : Semiformula LX ℕ 1) (t : Semiterm LX ℕ n) :
    Rew.subst ![t] ▹ (ψ/[(#0 : Semiterm LX ℕ 1)]) = ψ/[t] := by
  rw [subst_subst]
  simp

/-! ### The chain -/

/-- The complexity of an evaluated instance is that of the body. -/
theorem complexity_ev_subst (ψ : Semiproposition LX 1) (t : SyntacticTerm LX) :
    (ev (ψ/[t])).complexity = ψ.complexity := by
  rw [complexity_ev, Semiformula.complexity_rew]

/-- The body of the existential that the negated induction step is. -/
def stepBody (ψ : Semiproposition LX 1) : Semiproposition LX 1 :=
  ev (ψ/[(#0 : Semiterm LX ℕ 1)]) ⋏ ∼ev (ψ/[sucT])

/-- The negation of the (evaluated) induction step, in the shape the `exs` rule
of the calculus takes. -/
theorem neg_step (ψ : Semiproposition LX 1) :
    ∼ev (∀¹ (ψ/[(#0 : Semiterm LX ℕ 1)] 🡒 ψ/[sucT])) = ∃¹ stepBody ψ := by
  simp [stepBody, Semiformula.imp_eq]

/-- **The instance computation.**  This is where the `n̄ + 1` of the syntax and
the `(n+1)‾` of the ω-rule are reconciled: the evaluator absorbs the difference. -/
theorem inst_stepBody (ψ : Semiproposition LX 1) (n : ℕ) :
    evInst.inst (stepBody ψ) n = ev (ψ/[numLX n]) ⋏ ∼ev (ψ/[numLX (n + 1)]) := by
  have hA : ev ((ev (ψ/[(#0 : Semiterm LX ℕ 1)]))/[numLX n]) = ev (ψ/[numLX n]) := by
    rw [ev_rew_ev (ψ/[(#0 : Semiterm LX ℕ 1)]) 0 (Rew.subst ![numLX n])]
    exact congrArg ev (subst_bvar_subst ψ (numLX n))
  have hB : ev ((ev (ψ/[sucT]))/[numLX n]) = ev (ψ/[numLX (n + 1)]) := by
    rw [ev_rew_ev (ψ/[sucT]) 0 (Rew.subst ![numLX n])]
    have h1 : Rew.subst ![numLX n] ▹ (ψ/[sucT]) = ψ/[Rew.subst ![numLX n] sucT] :=
      subst_subst ψ sucT (numLX n)
    rw [h1, ev_subst_ground (ground_subst_sucT n) ψ, evTerm_subst_sucT]
  rw [evInst_inst, stepBody]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg,
    ev_and, ev_neg, hA, hB]

/-- **Step 1, in membership form.**  From `¬ψ(0̄)`, the negated induction step and
`ψ(n̄)` in the sequent, a cut-free derivation of height `2·complexity + 2n`. -/
theorem chain_aux (ψ : Semiproposition LX 1) :
    ∀ (n : ℕ) (Γ : Sequent LX), ∼ev (ψ/[zeroT]) ∈ Γ → (∃¹ stepBody ψ) ∈ Γ →
      ev (ψ/[numLX n]) ∈ Γ →
      OmegaDerivable trueArithLits evInst 0 (NONote.ofNat (2 * ψ.complexity + 2 * n)) Γ := by
  intro n
  induction n with
  | zero =>
      intro Γ hZ _ hP
      have harith : 2 * ψ.complexity + 2 * 0 = 2 * ψ.complexity := by omega
      rw [harith]
      refine OmegaDerivable.identity_of_mem ψ.complexity (ev (ψ/[numLX 0]))
        (le_of_eq (complexity_ev_subst ψ (numLX 0))) hP ?_
      rw [← zeroT_eq]
      exact hZ
  | succ n ih =>
      intro Γ hZ hS hP
      have hlt₁ : NONote.ofNat (2 * ψ.complexity + 2 * n)
          < NONote.ofNat (2 * ψ.complexity + 2 * n + 1) := ofNat_lt_ofNat (by omega)
      have hlt₂ : NONote.ofNat (2 * ψ.complexity)
          < NONote.ofNat (2 * ψ.complexity + 2 * n + 1) := ofNat_lt_ofNat (by omega)
      have hlt₃ : NONote.ofNat (2 * ψ.complexity + 2 * n + 1)
          < NONote.ofNat (2 * ψ.complexity + 2 * (n + 1)) := ofNat_lt_ofNat (by omega)
      -- the left premise of the `and`: the induction hypothesis, in a larger context
      have d₁ : OmegaDerivable trueArithLits evInst 0
          (NONote.ofNat (2 * ψ.complexity + 2 * n)) (ev (ψ/[numLX n]) :: Γ) :=
        ih _ (List.mem_cons_of_mem _ hZ) (List.mem_cons_of_mem _ hS) List.mem_cons_self
      -- the right premise: identity on `ψ(n+1‾)`
      have d₂ : OmegaDerivable trueArithLits evInst 0
          (NONote.ofNat (2 * ψ.complexity)) (∼ev (ψ/[numLX (n + 1)]) :: Γ) :=
        OmegaDerivable.identity_of_mem ψ.complexity (ev (ψ/[numLX (n + 1)]))
          (le_of_eq (complexity_ev_subst ψ (numLX (n + 1))))
          (List.mem_cons_of_mem _ hP) List.mem_cons_self
      have d₃ : OmegaDerivable trueArithLits evInst 0
          (NONote.ofNat (2 * ψ.complexity + 2 * n + 1)) (evInst.inst (stepBody ψ) n :: Γ) := by
        rw [inst_stepBody]
        exact OmegaDerivable.and hlt₁ hlt₂ d₁ d₂
      exact OmegaDerivable.drop_head (OmegaDerivable.exs n hlt₃ d₃) hS

/-- **Step 1.**  The chain, as a three-element sequent. -/
theorem chain (ψ : Semiproposition LX 1) (n : ℕ) :
    OmegaDerivable trueArithLits evInst 0 (NONote.ofNat (2 * ψ.complexity + 2 * n))
      [∼ev (ψ/[zeroT]),
       ∼ev (∀¹ (ψ/[(#0 : Semiterm LX ℕ 1)] 🡒 ψ/[sucT])),
       ev (ψ/[numLX n])] :=
  chain_aux ψ n _ (by simp) (by rw [← neg_step]; simp) (by simp)

/-! ### Step 2: the closed induction axiom -/

theorem ofNat_zero : NONote.ofNat 0 = 0 := rfl

/-- `ev` of an induction axiom, in the shape the two `or` rules produce. -/
theorem ev_succInd (ψ : Semiproposition LX 1) :
    ev (succInd ψ)
      = ∼ev (ψ/[zeroT]) ⋎ (∼ev (∀¹ (ψ/[(#0 : Semiterm LX ℕ 1)] 🡒 ψ/[sucT]))
          ⋎ (∀¹ (ev (ψ/[(#0 : Semiterm LX ℕ 1)])))) := by
  show ev ((ψ/[zeroT]) 🡒 (∀¹ (ψ/[(#0 : Semiterm LX ℕ 1)] 🡒 ψ/[sucT]))
      🡒 ∀¹ (ψ/[(#0 : Semiterm LX ℕ 1)])) = _
  simp [Semiformula.imp_eq]

/-- **Step 2.**  Every induction axiom with a *closed* body is derivable, cut-free,
at height `ω + 2`. -/
theorem succInd_derivable (ψ : Semiproposition LX 1) :
    OmegaDerivable trueArithLits evInst 0 (NONote.nadd omegaNO (NONote.ofNat 2))
      [ev (succInd ψ)] := by
  have h1 : omegaNO < NONote.nadd omegaNO (NONote.ofNat 1) := by
    have h := NONote.nadd_lt_nadd_right omegaNO (ofNat_lt_ofNat (show (0 : ℕ) < 1 by omega))
    simpa [ofNat_zero] using h
  have h2 : NONote.nadd omegaNO (NONote.ofNat 1) < NONote.nadd omegaNO (NONote.ofNat 2) :=
    NONote.nadd_lt_nadd_right omegaNO (ofNat_lt_ofNat (show (1 : ℕ) < 2 by omega))
  have hinst : ∀ n : ℕ, evInst.inst (ev (ψ/[(#0 : Semiterm LX ℕ 1)])) n = ev (ψ/[numLX n]) := by
    intro n
    rw [evInst_inst_ev]
    exact congrArg ev (subst_bvar_subst ψ (numLX n))
  -- the ω-rule
  have dω : OmegaDerivable trueArithLits evInst 0 omegaNO
      ((∀¹ (ev (ψ/[(#0 : Semiterm LX ℕ 1)])))
        :: [∼ev (ψ/[zeroT]), ∼ev (∀¹ (ψ/[(#0 : Semiterm LX ℕ 1)] 🡒 ψ/[sucT]))]) := by
    refine OmegaDerivable.omegaRule
      (fun n => NONote.ofNat (2 * ψ.complexity + 2 * n)) (fun n => ofNat_lt_omegaNO _)
      (fun n => ?_)
    rw [hinst n]
    exact OmegaDerivable.contraction (by intro x hx; simp at hx ⊢; tauto) (chain ψ n)
  -- the first `or`
  have d₁ : OmegaDerivable trueArithLits evInst 0 (NONote.nadd omegaNO (NONote.ofNat 1))
      [∼ev (∀¹ (ψ/[(#0 : Semiterm LX ℕ 1)] 🡒 ψ/[sucT])) ⋎ (∀¹ (ev (ψ/[(#0 : Semiterm LX ℕ 1)]))),
       ∼ev (ψ/[zeroT])] :=
    OmegaDerivable.or h1
      (OmegaDerivable.contraction (by intro x hx; simp at hx ⊢; tauto) dω)
  -- the second `or`
  have d₂ : OmegaDerivable trueArithLits evInst 0 (NONote.nadd omegaNO (NONote.ofNat 2))
      [∼ev (ψ/[zeroT]) ⋎ (∼ev (∀¹ (ψ/[(#0 : Semiterm LX ℕ 1)] 🡒 ψ/[sucT]))
        ⋎ (∀¹ (ev (ψ/[(#0 : Semiterm LX ℕ 1)]))))] :=
    OmegaDerivable.or h2
      (OmegaDerivable.contraction (by intro x hx; simp at hx ⊢; tauto) d₁)
  rw [ev_succInd]
  exact d₂

/-! ### Step 3: peeling the universal closure -/

/-- Substituting a term under a lifted simultaneous substitution is a single
simultaneous substitution with the term prepended. -/
theorem subst_q_subst {k : ℕ} (σ : Semiformula LX ℕ (k + 1)) (v : Fin k → SyntacticTerm LX)
    (t : SyntacticTerm LX) :
    ((Rew.subst v).q ▹ σ)/[t] = σ ⇜ (t :> v) := by
  have hrew : (Rew.subst ![t]).comp ((Rew.subst v).q) = Rew.subst (t :> v) := by
    rw [Rew.q_subst, Rew.subst_comp_subst]
    congr 1
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  simpa [← comp_app] using smul_ext' (φ := σ) hrew

/-- **Step 3, with the bookkeeping index made explicit.** -/
theorem allClosure_aux (β : NONote) :
    ∀ (k j : ℕ) (σ : Semiformula LX ℕ k),
      (∀ w : Fin k → ℕ, OmegaDerivable trueArithLits evInst 0
          (NONote.nadd β (NONote.ofNat j)) [ev (σ ⇜ fun i => numLX (w i))]) →
      OmegaDerivable trueArithLits evInst 0 (NONote.nadd β (NONote.ofNat (j + k)))
        [ev (∀¹* σ)] := by
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
      have hlt : NONote.nadd β (NONote.ofNat j) < NONote.nadd β (NONote.ofNat (j + 1)) :=
        NONote.nadd_lt_nadd_right β (ofNat_lt_ofNat (by omega))
      have hall : ((∀¹ σ) ⇜ fun i => numLX (w i))
          = ∀¹ ((Rew.subst fun i => numLX (w i)).q ▹ σ) := by simp
      rw [hall, ev_all]
      refine OmegaDerivable.omegaRule (Γ := [])
        (fun _ => NONote.nadd β (NONote.ofNat j)) (fun _ => hlt) (fun n => ?_)
      rw [evInst_inst_ev, subst_q_subst]
      have hv : (numLX n :> fun i => numLX (w i)) = fun i => numLX ((n :> w) i) := by
        funext i
        induction i using Fin.cases with
        | zero => simp
        | succ j => simp
      rw [hv]
      exact h (n :> w)

/-- **Step 3.**  A universal closure is derivable once every numeral instance is,
at `k` more than the common height of the instances. -/
theorem allClosure_derivable {k : ℕ} (σ : Semiformula LX ℕ k) {β : NONote}
    (h : ∀ w : Fin k → ℕ, OmegaDerivable trueArithLits evInst 0 β
        [ev (σ ⇜ fun i => numLX (w i))]) :
    OmegaDerivable trueArithLits evInst 0 (NONote.nadd β (NONote.ofNat k)) [ev (∀¹* σ)] := by
  have key := allClosure_aux β k 0 σ (by simpa [ofNat_zero] using h)
  simpa using key

/-! ### Step 4: the induction axioms of `PA[X]` -/

/-- Substituting `#0` for the bound variable is the identity. -/
theorem subst_bvar_self (ψ : Semiformula LX ℕ 1) : ψ/[(#0 : Semiterm LX ℕ 1)] = ψ := by simp

/-- A numeral assignment commutes with substitution one binder down. -/
theorem numSubst₁_subst (a : ℕ → ℕ) (s : Semiterm LX ℕ 1) (φ : Semiformula LX ℕ 1) :
    NumSubst.numSubst₁ a ▹ (φ/[s]) = (NumSubst.numSubst₁ a ▹ φ)/[NumSubst.numSubst₁ a s] := by
  simpa [← comp_app] using smul_ext' (φ := φ) <| by
    ext x <;> simp [Rew.comp_app, NumSubst.numSubst₁]

theorem numSubst₁_sucT (a : ℕ → ℕ) : NumSubst.numSubst₁ a sucT = sucT := by
  simp [sucT, NumSubst.numSubst₁]

theorem numSubst_zeroT (a : ℕ → ℕ) : NumSubst.numSubst a zeroT = zeroT := by
  simp [zeroT, NumSubst.numSubst]

/-- A numeral assignment lifted under a binder is the one-binder-down version. -/
@[simp] theorem numSubst_q (a : ℕ → ℕ) :
    (NumSubst.numSubst a).q = NumSubst.numSubst₁ a := by
  simp only [NumSubst.numSubst, NumSubst.numSubst₁]
  ext x <;> simp [numLX]

/-- **A numeral assignment passes through an induction axiom**: the three
occurrences of the body are all substituted, and the closed terms `0̄`, `#0` and
`#0 + 1` are all fixed. -/
theorem numSubst_succInd (a : ℕ → ℕ) (φ : Semiproposition LX 1) :
    NumSubst.numSubst a ▹ succInd φ = succInd (NumSubst.numSubst₁ a ▹ φ) := by
  show NumSubst.numSubst a ▹ ((φ/[zeroT])
      🡒 (∀¹ (φ/[(#0 : Semiterm LX ℕ 1)] 🡒 φ/[sucT]))
      🡒 ∀¹ (φ/[(#0 : Semiterm LX ℕ 1)]))
    = ((NumSubst.numSubst₁ a ▹ φ)/[zeroT])
      🡒 (∀¹ ((NumSubst.numSubst₁ a ▹ φ)/[(#0 : Semiterm LX ℕ 1)]
            🡒 (NumSubst.numSubst₁ a ▹ φ)/[sucT]))
      🡒 ∀¹ ((NumSubst.numSubst₁ a ▹ φ)/[(#0 : Semiterm LX ℕ 1)])
  simp [Semiformula.imp_eq, NumSubst.numSubst_subst,
    numSubst_zeroT, numSubst₁_subst, numSubst₁_sucT]

/-- **Step 4.**  Every axiom of the induction schema of `PA[X]` has a cut-free
derivation in the ω-calculus. -/
theorem induction_axiom_derivable (σ : Sentence LX) (h : σ ∈ InductionScheme LX Set.univ) :
    ∃ β : NONote, OmegaDerivable trueArithLits evInst 0 β
      [ev (Rewriting.emb σ : Proposition LX)] := by
  obtain ⟨φ, -, rfl⟩ := h
  refine ⟨NONote.nadd (NONote.nadd omegaNO (NONote.ofNat 2))
      (NONote.ofNat (0 + (succInd φ).fvSup)), ?_⟩
  have hemb : (Rewriting.emb (Semiformula.univCl (succInd φ)) : Proposition LX)
      = ∀¹* (Rew.fixitr 0 (succInd φ).fvSup ▹ (succInd φ)) := by
    simp [Semiformula.univCl']
  rw [hemb]
  refine allClosure_derivable (Rew.fixitr 0 (succInd φ).fvSup ▹ (succInd φ)) (fun w => ?_)
  have key : (Rew.fixitr 0 (succInd φ).fvSup ▹ (succInd φ))
        ⇜ (fun i : Fin (0 + (succInd φ).fvSup) => numLX (w i))
      = Rew.rewrite (fun y => numLX (if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0))
          ▹ (succInd φ) := by
    have hvec : (fun i : Fin (0 + (succInd φ).fvSup) => numLX (w i))
        = (fun i : Fin (0 + (succInd φ).fvSup) =>
            (fun y => numLX (if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0)) (i : ℕ)) := by
      funext i
      simp only [dif_pos i.isLt, Fin.eta]
    rw [hvec]
    exact Semiformula.subst_comp_fixitr_eq_map (succInd φ)
      (fun y => numLX (if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0))
  have hns : Rew.rewrite
        (fun y => numLX (if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0))
      = NumSubst.numSubst
          (fun y => if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0) := rfl
  rw [key, hns, numSubst_succInd]
  exact succInd_derivable _

end OrdinalAnalysis.Gentzen.AxiomsInduction
