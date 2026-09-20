/-
  Every axiom of the transfinite-induction *scheme* is cut-free derivable below `ε₁`.

  `Epsilon1UpperBound.paLX₁` is `paLX` together with the whole scheme

      tiScheme₀ = { closedTI₁ φ ε₀̄ | φ : Semiformula LX ℕ 1 },
      closedTI₁ φ a = (Prog(≺₁, φ) → ∀ x ≺₁ a, φ(x)).univCl,

  one axiom for each unary formula of `LX`, and not merely the single instance
  `TI₀` for the fresh predicate `X`.  The scheme is what the upper bound needs
  (the single `X`-instance does not prove the ones for compound formulas — see
  the design notes, design decision 4), so it is the theory the
  lower bound has to be run against too, and the lower bound's cut-away step
  demands a cut-free ω-derivation of every axiom at a height below `ε₁`.

  There is exactly one derivation to build, and the rest is substitution.
  `Epsilon1Axiom.TI₀_derivable_at` derives the `X`-instance at `ε₀ + 1`;
  `OmegaDerivable.substX` replaces `X` by any closed unary `ψ` at the cost of
  `2·complexity ψ`; and the free variables of a general `φ` are discharged by
  the ω-rule, one at a time, exactly as `AxiomsInduction.allClosure_derivable`
  discharges those of an induction axiom.

  Three things about the shape.

  * **`allClosure_derivable` is re-proved generically.**  The version in
    `AxiomsInduction.lean` has its heights in `NONote`, and the instances here
    live at `ε₀ + 1 + 2c`, above `ε₀`.  Transporting along `ofNONote` is not
    available for that reason, so the ω-rule iteration is repeated with the
    height system as a parameter.  The one `NONote`-specific step of the
    original — `nadd β (ofNat 0) = β` — is replaced by `mono_ord` along
    `le_nadd_left`, since the class has no `0`.

  * **`substX ψ (TIupto prec t) = tiUptoAt prec ψ t`.**  The generic
    `tiUptoAt` of `Jump.lean` and the `X`-specific `TIupto` of `Setup.lean` are
    the same formula with `X(·)` in place of `ψ(·)`; `substX` turns the second
    into the first, needing only that `prec` is `X`-free.  No closedness of `ψ`
    is used here — that is needed only for `substX` to commute with rewriting.

  * **The numeral assignment is carried at every level.**  `numSubstAt f n`
    sends `&x` to the numeral of `f x` and fixes the bound variables; it is
    `NumSubst.numSubst f` at level `0` and `NumSubst.numSubst₁ f` at level `1`.
    Its `q` is itself one level up, which is what lets it be pushed through the
    two binders of `progAt`/`belowAt` in three lines.

  Contents.

    `allClosure_aux`, `allClosure_derivable`   the ω-rule iteration, generic in `O`
    `substX_precAt`, `substX_TIupto`           `substX` turns `TIupto` into `tiUptoAt`
    `numSubstAt`, `numSubstAt_tiUptoAt`        a numeral assignment passes through
    `freeVariables_numSubstAt`                 its image is closed
    `univCl'_derivable_of`                     the universal closure, below `ε₁`
    `instance_derivable`                       one numeral instance of a scheme axiom
    `scheme_axiom_derivable`                   **every axiom of `tiScheme₀`**
-/
import OrdinalAnalysis.Gentzen.SubstX
import OrdinalAnalysis.Gentzen.Epsilon1Axiom
import OrdinalAnalysis.Gentzen.Epsilon1UpperBound
import OrdinalAnalysis.Gentzen.AxiomsInduction
import OrdinalAnalysis.Gentzen.NumSubst
import OrdinalAnalysis.Ordinal.Veblen.EpsilonBelow

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.Epsilon1Scheme

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.StandardLX (trueArithLits numLX)
open OrdinalAnalysis.Gentzen.Evaluate OrdinalAnalysis.Gentzen.EvInst
open OrdinalAnalysis.Gentzen.SubstX
open OrdinalAnalysis.Gentzen.CodedVeblen
open OrdinalAnalysis.Gamma0Note

/-! ### The universal closure, generically in the height system

`AxiomsInduction.allClosure_aux` with `NONote` replaced by an arbitrary
notation system.  The proof is the original one; only the arithmetic of the
heights is restated through the class. -/

section AllClosure

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- **The ω-rule iteration**, with the bookkeeping index made explicit. -/
theorem allClosure_aux (β : O) :
    ∀ (k j : ℕ) (σ : Semiformula LX ℕ k),
      (∀ w : Fin k → ℕ, OmegaDerivable trueArithLits evInst 0
          (OrdinalNotation.nadd β (OrdinalNotation.ofNat j))
          [ev (σ ⇜ fun i => numLX (w i))]) →
      OmegaDerivable trueArithLits evInst 0
        (OrdinalNotation.nadd β (OrdinalNotation.ofNat (j + k))) [ev (∀¹* σ)] := by
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
      have hall : ((∀¹ σ) ⇜ fun i => numLX (w i))
          = ∀¹ ((Rew.subst fun i => numLX (w i)).q ▹ σ) := by simp
      rw [hall, ev_all]
      refine OmegaDerivable.omegaRule (Γ := [])
        (fun _ => OrdinalNotation.nadd β (OrdinalNotation.ofNat j)) (fun _ => hlt) (fun n => ?_)
      rw [evInst_inst_ev, AxiomsInduction.subst_q_subst]
      have hv : (numLX n :> fun i => numLX (w i)) = fun i => numLX ((n :> w) i) := by
        funext i
        induction i using Fin.cases with
        | zero => simp
        | succ j => simp
      rw [hv]
      exact h (n :> w)

/-- **The universal closure**, once every numeral instance is derivable at a
common height. -/
theorem allClosure_derivable {k : ℕ} (σ : Semiformula LX ℕ k) {β : O}
    (h : ∀ w : Fin k → ℕ, OmegaDerivable trueArithLits evInst 0 β
        [ev (σ ⇜ fun i => numLX (w i))]) :
    OmegaDerivable trueArithLits evInst 0
      (OrdinalNotation.nadd β (OrdinalNotation.ofNat k)) [ev (∀¹* σ)] := by
  have key := allClosure_aux β k 0 σ
    (fun w => (h w).mono_ord (OrdinalNotation.le_nadd_left β _))
  rwa [Nat.zero_add] at key

end AllClosure

/-! ### `substX` turns `TIupto` into `tiUptoAt`

`TIupto prec t` (Setup.lean) and `tiUptoAt prec ψ t` (Jump.lean) are the same
formula, the first with the atom `X(·)` where the second has `ψ(·)`.  Nothing
about `ψ` is needed; only that `prec` does not itself mention `X`. -/

/-- A comparison is `X`-free, so `substX` fixes it. -/
theorem substX_precAt {prec : Semiformula LX ℕ 2} (hprec : LowerClass.XFree prec)
    (ψ : Semiformula LX ℕ 1) {n : ℕ} (y x : Semiterm LX ℕ n) :
    substX ψ (precAt prec y x) = precAt prec y x :=
  substX_of_XFree ψ (precAt prec y x) (by simpa [precAt] using hprec)

theorem bShift_bvar_zero :
    Rew.bShift (#0 : Semiterm LX ℕ 1) = (#1 : Semiterm LX ℕ 2) := rfl

/-- **`substX ψ (TIupto prec t) = tiUptoAt prec ψ t`.** -/
theorem substX_TIupto {prec : Semiformula LX ℕ 2} (hprec : LowerClass.XFree prec)
    (ψ : Semiformula LX ℕ 1) (t : Semiterm LX ℕ 0) :
    substX ψ (TIupto prec t) = tiUptoAt prec ψ t := by
  have hb : substX ψ (below prec) = belowAt prec ψ (#0 : Semiterm LX ℕ 1) := by
    unfold below belowAt
    rw [substX_all, substX_or, substX_neg, substX_precAt hprec ψ, substX_Xat,
      bShift_bvar_zero]
  have hprog : substX ψ (Prog prec) = progAt prec ψ := by
    unfold Prog progAt
    rw [substX_all, substX_or, substX_neg, hb, substX_Xat]
  unfold TIupto tiUptoAt
  rw [substX_or, substX_neg, hprog]
  show ∼(progAt prec ψ) ⋎ substX ψ (∀¹ (∼(precAt prec (#0 : Semiterm LX ℕ 1) (Rew.bShift t))
      ⋎ Xat #0)) = ∼(progAt prec ψ) ⋎ belowAt prec ψ t
  unfold belowAt
  rw [substX_all, substX_or, substX_neg, substX_precAt hprec ψ, substX_Xat]

/-! ### Numeral assignments at every level

The replay of a finitary proof substitutes numerals for the free variables; the
universal closure of a scheme axiom is discharged by the ω-rule in the same way.
Either way the assignment has to be pushed through `tiUptoAt`, which carries two
binders, so it is needed at every level. -/

/-- The assignment `&x ↦ f x‾`, as a rewriting of level-`n` formulas. -/
def numSubstAt (f : ℕ → ℕ) (n : ℕ) : Rew LX ℕ n ℕ n :=
  Rew.rewrite fun x => (Semiterm.numeral (f x) : Semiterm LX ℕ n)

@[simp] theorem numSubstAt_bvar (f : ℕ → ℕ) {n : ℕ} (i : Fin n) :
    numSubstAt f n #i = #i := rfl

@[simp] theorem numSubstAt_fvar (f : ℕ → ℕ) {n : ℕ} (x : ℕ) :
    numSubstAt f n &x = (Semiterm.numeral (f x) : Semiterm LX ℕ n) := rfl

theorem numSubstAt_zero_eq (f : ℕ → ℕ) : numSubstAt f 0 = NumSubst.numSubst f := rfl

@[simp] theorem numSubstAt_q (f : ℕ → ℕ) (n : ℕ) :
    (numSubstAt f n).q = numSubstAt f (n + 1) := by
  simp only [numSubstAt, Rew.q_rewrite]
  congr 1
  funext x
  simp

theorem numSubstAt_bShift (f : ℕ → ℕ) {n : ℕ} (t : Semiterm LX ℕ n) :
    numSubstAt f (n + 1) (Rew.bShift t) = Rew.bShift (numSubstAt f n t) := by
  have h : (numSubstAt f (n + 1)).comp Rew.bShift = Rew.bShift.comp (numSubstAt f n) := by
    ext x <;> simp [numSubstAt, Rew.comp_app]
  simpa [Rew.comp_app] using congrArg (fun ω : Rew LX ℕ n ℕ (n + 1) => ω t) h

/-- A closed comparison formula sees only the substituted terms. -/
theorem numSubstAt_precAt {prec : Semiformula LX ℕ 2} (hprec : prec.freeVariables = ∅)
    (f : ℕ → ℕ) {n : ℕ} (y x : Semiterm LX ℕ n) :
    numSubstAt f n ▹ (precAt prec y x)
      = precAt prec (numSubstAt f n y) (numSubstAt f n x) := by
  have hv : (fun i => numSubstAt f n ((![y, x] : Fin 2 → Semiterm LX ℕ n) i))
      = ![numSubstAt f n y, numSubstAt f n x] := by
    funext i
    fin_cases i <;> rfl
  show numSubstAt f n ▹ (Rew.subst ![y, x] ▹ prec)
      = Rew.subst ![numSubstAt f n y, numSubstAt f n x] ▹ prec
  rw [rew_subst_closed hprec (numSubstAt f n) ![y, x], hv]

/-- **The assignment passes through an instance**: the body is assigned one
level down, the argument at the level it sits at. -/
theorem numSubstAt_formulaAt (f : ℕ → ℕ) {n : ℕ} (φ : Semiformula LX ℕ 1)
    (s : Semiterm LX ℕ n) :
    numSubstAt f n ▹ (formulaAt φ s) = formulaAt (numSubstAt f 1 ▹ φ) (numSubstAt f n s) := by
  have hrew : (numSubstAt f n).comp (Rew.subst ![s])
      = (Rew.subst ![numSubstAt f n s]).comp (numSubstAt f 1) := by
    ext x <;> simp [Rew.comp_app, numSubstAt]
  show numSubstAt f n ▹ (Rew.subst ![s] ▹ φ)
      = Rew.subst ![numSubstAt f n s] ▹ (numSubstAt f 1 ▹ φ)
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, hrew]

theorem numSubstAt_belowAt {prec : Semiformula LX ℕ 2} (hprec : prec.freeVariables = ∅)
    (f : ℕ → ℕ) {n : ℕ} (φ : Semiformula LX ℕ 1) (b : Semiterm LX ℕ n) :
    numSubstAt f n ▹ (belowAt prec φ b)
      = belowAt prec (numSubstAt f 1 ▹ φ) (numSubstAt f n b) := by
  unfold belowAt
  rw [Rewriting.app_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, numSubstAt_q, numSubstAt_precAt hprec,
    numSubstAt_formulaAt, numSubstAt_bvar, numSubstAt_bShift]

theorem numSubstAt_progAt {prec : Semiformula LX ℕ 2} (hprec : prec.freeVariables = ∅)
    (f : ℕ → ℕ) {n : ℕ} (φ : Semiformula LX ℕ 1) :
    numSubstAt f n ▹ (progAt prec φ : Semiformula LX ℕ n)
      = progAt prec (numSubstAt f 1 ▹ φ) := by
  unfold progAt
  rw [Rewriting.app_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, numSubstAt_q, numSubstAt_belowAt hprec,
    numSubstAt_formulaAt, numSubstAt_bvar]

/-- **The assignment passes through a transfinite-induction axiom.** -/
theorem numSubstAt_tiUptoAt {prec : Semiformula LX ℕ 2} (hprec : prec.freeVariables = ∅)
    (f : ℕ → ℕ) {n : ℕ} (φ : Semiformula LX ℕ 1) (a : Semiterm LX ℕ n) :
    numSubstAt f n ▹ (tiUptoAt prec φ a)
      = tiUptoAt prec (numSubstAt f 1 ▹ φ) (numSubstAt f n a) := by
  unfold tiUptoAt
  rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    numSubstAt_progAt hprec, numSubstAt_belowAt hprec]

/-- **The image of a numeral assignment is closed**: every free variable has
been replaced by a numeral, and the bound variables stay bound. -/
theorem freeVariables_numSubstAt {n : ℕ} (f : ℕ → ℕ) (χ : Semiformula LX ℕ n) :
    (numSubstAt f n ▹ χ).freeVariables = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  rcases Semiformula.fvar?_rew (φ := χ) (ω := numSubstAt f n) hx with ⟨i, hi⟩ | ⟨z, -, hz⟩
  · have hi' : x ∈ ((#i : Semiterm LX ℕ n)).freeVariables := hi
    simp at hi'
  · have hz' : x ∈ ((Semiterm.numeral (f z) : Semiterm LX ℕ n)).freeVariables := hz
    rw [LowerSyntax.freeVariables_numeral] at hz'
    exact Finset.notMem_empty x hz'

/-! ### The closure step, below `ε₁` -/

/-- **A universal closure is derivable below `ε₁`** once every numeral
assignment of the body is, at a common height below `ε₁`.

Stated with `Θ` a variable: the concrete `Θ` of the application carries
`precCode₁`, whose normal form is enormous, and nothing here may be forced to
look at it. -/
theorem univCl'_derivable_of (Θ : Proposition LX) (β : Gamma0Note) (hβ : β < epsilonNote 1)
    (h : ∀ f : ℕ → ℕ, OmegaDerivable trueArithLits evInst 0 β [ev (numSubstAt f 0 ▹ Θ)]) :
    ∃ γ : Gamma0Note, γ < epsilonNote 1 ∧
      OmegaDerivable trueArithLits evInst 0 γ [ev (Θ.univCl' : Proposition LX)] := by
  refine ⟨OrdinalNotation.nadd β (OrdinalNotation.ofNat (0 + Θ.fvSup)),
    nadd_lt_epsilon hβ (ofNat_lt_epsilon _ 1), ?_⟩
  have hemb : (Θ.univCl' : Proposition LX) = ∀¹* (Rew.fixitr 0 Θ.fvSup ▹ Θ) := rfl
  rw [hemb]
  refine allClosure_derivable (Rew.fixitr 0 Θ.fvSup ▹ Θ) (fun w => ?_)
  have key : (Rew.fixitr 0 Θ.fvSup ▹ Θ) ⇜ (fun i : Fin (0 + Θ.fvSup) => numLX (w i))
      = numSubstAt (fun y => if hy : y < 0 + Θ.fvSup then w ⟨y, hy⟩ else 0) 0 ▹ Θ := by
    have hvec : (fun i : Fin (0 + Θ.fvSup) => numLX (w i))
        = (fun i : Fin (0 + Θ.fvSup) =>
            (fun y => numLX (if hy : y < 0 + Θ.fvSup then w ⟨y, hy⟩ else 0)) (i : ℕ)) := by
      funext i
      simp only [dif_pos i.isLt, Fin.eta]
    rw [hvec]
    exact Semiformula.subst_comp_fixitr_eq_map Θ
      (fun y => numLX (if hy : y < 0 + Θ.fvSup then w ⟨y, hy⟩ else 0))
  rw [key]
  exact h _

/-! ### The scheme -/

/-- The two spellings of the numeral of a Veblen notation agree. -/
theorem gamma0Term_eq (a : Gamma0Note) :
    Epsilon1UpperBound.gamma0Term a = Epsilon1Axiom.gamma0Term a := rfl

/-- **One instance of a scheme axiom.**  Assign numerals to the free variables
of `φ`, substitute the result for `X` in the derivation of `TI₀`, and read the
conclusion back as the corresponding instance of `tiUptoAt`. -/
theorem instance_derivable (φ : Semiformula LX ℕ 1) (f : ℕ → ℕ) :
    OmegaDerivable trueArithLits evInst 0
      (OrdinalNotation.nadd (OrdinalNotation.succ (epsilonNote 0))
        (OrdinalNotation.ofNat (2 * φ.complexity)))
      [ev (numSubstAt f 0 ▹ (tiUptoAt precCode₁ φ
        (Epsilon1UpperBound.gamma0Term (epsilonNote 0))))] := by
  set ψ : Semiformula LX ℕ 1 := numSubstAt f 1 ▹ φ with hψdef
  have hψ : ψ.freeVariables = ∅ := freeVariables_numSubstAt f φ
  have hc : ψ.complexity = φ.complexity := by
    rw [hψdef]; exact Semiformula.complexity_rew _ _
  -- the assignment passes through the axiom, and fixes the closed numeral
  have hterm : numSubstAt f 0 (Epsilon1UpperBound.gamma0Term (epsilonNote 0))
      = Epsilon1UpperBound.gamma0Term (epsilonNote 0) := by
    rw [gamma0Term_eq, Epsilon1Axiom.gamma0Term_eq]
    simp
  have hpass : numSubstAt f 0 ▹ (tiUptoAt precCode₁ φ
        (Epsilon1UpperBound.gamma0Term (epsilonNote 0)))
      = tiUptoAt precCode₁ ψ (Epsilon1UpperBound.gamma0Term (epsilonNote 0)) := by
    rw [numSubstAt_tiUptoAt freeVariables_precCode₁, hterm]
  rw [hpass, ← hc]
  -- the `X`-instance, with `ψ` substituted for `X`
  have hd := OmegaDerivable.substX (O := Gamma0Note) ψ hψ Epsilon1Axiom.TI₀_derivable_at
  simp only [List.map_cons, List.map_nil] at hd
  rw [Epsilon1Axiom.emb_TI₀, ev_substX_ev,
    substX_TIupto XFree_precCode₁ ψ (Epsilon1Axiom.gamma0Term (epsilonNote 0))] at hd
  exact hd

/-- **Every axiom of the scheme `tiScheme₀` is cut-free derivable below `ε₁`.** -/
theorem scheme_axiom_derivable (φ : Semiformula LX ℕ 1) :
    ∃ β : Gamma0Note, β < epsilonNote 1 ∧
      OmegaDerivable trueArithLits evInst 0 β
        [ev (Rewriting.emb (Epsilon1UpperBound.closedTI₁ φ
          (Epsilon1UpperBound.gamma0Term (epsilonNote 0))) : Proposition LX)] := by
  have hemb : (Rewriting.emb (Epsilon1UpperBound.closedTI₁ φ
        (Epsilon1UpperBound.gamma0Term (epsilonNote 0))) : Proposition LX)
      = ((tiUptoAt precCode₁ φ
          (Epsilon1UpperBound.gamma0Term (epsilonNote 0))).univCl' : Proposition LX) :=
    Semiformula.coe_univCl_eq_univCl' _
  rw [hemb]
  refine univCl'_derivable_of _
    (OrdinalNotation.nadd (OrdinalNotation.succ (epsilonNote 0))
      (OrdinalNotation.ofNat (2 * φ.complexity))) ?_ (instance_derivable φ)
  exact nadd_lt_epsilon Epsilon1Axiom.succ_epsilon0_lt_epsilon1 (ofNat_lt_epsilon _ 1)

end OrdinalAnalysis.Gentzen.Epsilon1Scheme
