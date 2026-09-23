/-
  **Every axiom of `ACA + TI(<Γ₀)` is cut-free derivable in `ACA_∞`**.

  `ACAOmega/SchemeAxioms₂.lean` did this for `ACA`; this file does it for the
  new block `ACA/TIGamma.lean` adds.  The shape of the argument is
  `indScheme₂_derivable_lt_eps₀`'s, verbatim:

      allN₂_derivable    peel the `∀²`-prefix by `N` eigenvariable rules
      allN₁_derivable    peel the `∀¹`-prefix by `n` ω-rules
      the leaf           `Climb₂.TIupto₂_derivable_at` + `SubstX₂.substX₂`

  and the two computations that connect them are the same two:

  * **`freeN₁_tiUptoBody`** — freeing the set parameters slides through the
    body, because the body is built from `⋎`/`∼`/`∀¹`, two first-order
    substitutions and the comparison `precG`, and a set rewriting sees none of
    them (`precG` is a `lift`; `app_lift`).
  * **`subst_tiUptoBody`** — substituting a vector of numerals turns the freed
    body into `SubstX₂.TIuptoψ₂` of the substituted formula.  It rests on the
    two composite-`Rew` identities `comp_belowSub` and `comp_atSub`, each proved
    by `Rew.ext` and `Fin.cases` exactly as `SchemeAxioms₂.comp_indZeroSub` is.

  ### The height

  The leaf sits at `ω^(a ⊕ 1) + 1` (`Climb₂.TIupto₂_derivable_at`; `substX₂`
  costs nothing), and the two prefixes add `n` and `N`, so the axiom
  `tiUptoScheme a ψ` is derivable at

      ((ω^(a ⊕ 1) + 1) ⊕ n) ⊕ N   <   ε_{a ⊕ 1}   =   φ_1(a ⊕ 1)   <   Γ₀ .

  Unlike the `ACA` half, **no uniform bound is needed**: `cut_axioms₂_of` takes
  its axiom heights in the same notation system the derivation runs in, and here
  that system is all of `Gamma0Note` — every height is below `Γ₀` by its type.
  The `< ε_{a ⊕ 1}` form is kept for the segment corollaries of
  `Gamma0Theorem.lean`.

  Contents.

    `app_lift`, `free₁_precG`            a lift is fixed by a set rewriting
    `free₁_belowG`, `free₁_progG`, `free₁_tiUptoBody`, `freeN₁_tiUptoBody`
    `comp_belowSub`, `comp_atSub`        the two composite identities
    `subst_belowG`, `subst_tiUptoBody`   **the instantiation computation**
    `TIuptoψ₂_derivable_at`              the leaf, at an explicit height
    `tiUptoScheme_derivable`             **the new axiom block**
    `acaΓ_axiom_derivable`               **every axiom of `ACAΓ`**
-/
import OrdinalAnalysis.ACA.TIGamma
import OrdinalAnalysis.ACAOmega.Climb₂
import OrdinalAnalysis.ACAOmega.SchemeAxioms₂

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA
open OrdinalAnalysis.ACAOmega.AxiomsInduction₂
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)

namespace AxiomsTI₂

/-! ### A lifted formula is fixed by every set-variable rewriting

`SubstX₂.app_of_setFree` says this for rewritings that keep the number of set
slots; `free₁` changes it, so the lemma is re-proved here in the form the
freeing needs.  The induction is on the *first-order* formula, so every clause
is structural. -/

/-- **A lift is fixed by every second-order rewriting**, at any pair of set-slot
counts. -/
theorem app_lift {N₁ N₂ : ℕ} (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ) :
    ∀ {n : ℕ} (φ : FirstOrder.Semiformula ℒₒᵣ ℕ n),
      Ω.app (lift φ : Semiproposition ℒₒᵣ N₁ n) = (lift φ : Semiproposition ℒₒᵣ N₂ n) := by
  intro n φ
  induction φ using FirstOrder.Semiformula.rec' <;> simp [*]

theorem free₁_precG {N n : ℕ} (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    Semiproposition.free₁ (precG y x : Semiproposition ℒₒᵣ (N + 1) n) = precG y x := by
  show SecondOrder.Rew.free.app (lift _ : Semiproposition ℒₒᵣ (N + 1) n) = _
  exact app_lift _ _

/-! ### Freeing the set parameters slides through the body -/

theorem free₁_or {N n : ℕ} (φ χ : Semiproposition ℒₒᵣ (N + 1) n) :
    Semiproposition.free₁ (φ ⋎ χ)
      = Semiproposition.free₁ φ ⋎ Semiproposition.free₁ χ := by
  show SecondOrder.Rew.free.app (φ ⋎ χ) = _
  rw [LogicalConnective.HomClass.map_or]

theorem free₁_neg {N n : ℕ} (φ : Semiproposition ℒₒᵣ (N + 1) n) :
    Semiproposition.free₁ (∼φ) = ∼(Semiproposition.free₁ φ) := by
  show SecondOrder.Rew.free.app (∼φ) = _
  rw [LogicalConnective.HomClass.map_neg]

theorem free₁_belowG {N n : ℕ} (ψ : Semiproposition ℒₒᵣ (N + 1) (n + 1)) :
    Semiproposition.free₁ (belowG ψ) = belowG (Semiproposition.free₁ ψ) := by
  rw [belowG, free₁_all₁, free₁_or, free₁_neg, free₁_precG, SchemeAxioms₂.free₁_subst, belowG]

theorem free₁_progG {N n : ℕ} (ψ : Semiproposition ℒₒᵣ (N + 1) (n + 1)) :
    Semiproposition.free₁ (progG ψ) = progG (Semiproposition.free₁ ψ) := by
  rw [progG, free₁_all₁, free₁_or, free₁_neg, free₁_belowG, progG]

theorem free₁_tiUptoBody {N n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n)
    (ψ : Semiproposition ℒₒᵣ (N + 1) (n + 1)) :
    Semiproposition.free₁ (tiUptoBody t ψ) = tiUptoBody t (Semiproposition.free₁ ψ) := by
  rw [tiUptoBody, free₁_or, free₁_neg, free₁_progG, SchemeAxioms₂.free₁_subst,
    free₁_belowG, tiUptoBody]

/-- **Freeing every set parameter slides through the body.** -/
theorem freeN₁_tiUptoBody {n : ℕ} (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ∀ (N : ℕ) (ψ : Semiproposition ℒₒᵣ N (n + 1)),
      freeN₁ N (tiUptoBody t ψ) = tiUptoBody t (freeN₁ N ψ)
  | 0, _ => rfl
  | N + 1, ψ => by
      rw [freeN₁_succ, free₁_tiUptoBody,
        freeN₁_tiUptoBody t N (Semiproposition.free₁ ψ), freeN₁_succ]

/-! ### The instantiation computation -/

section Inst

variable {n : ℕ} (w : Fin n → ℕ)

/-- Both sides send `#0 ↦ #0`, `#(i+1) ↦ w i` and `&x ↦ &x`. -/
theorem comp_belowSub :
    ((FirstOrder.Rew.subst
        (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q).q.comp
        (FirstOrder.Rew.subst (belowSub n))
      = (FirstOrder.Rew.subst ![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2)]).comp
        (FirstOrder.Rew.subst
          (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q := by
  ext x
  · cases x using Fin.cases with
    | zero => simp [FirstOrder.Rew.comp_app]
    | succ i => simp [FirstOrder.Rew.comp_app]
  · simp [FirstOrder.Rew.comp_app]

/-- Both sides send `#0 ↦ t`, `#(i+1) ↦ w i` and `&x ↦ &x`. -/
theorem comp_atSub (c : ℕ) :
    (FirstOrder.Rew.subst
        (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).comp
        (FirstOrder.Rew.subst (atSub (numAt c)))
      = (FirstOrder.Rew.subst ![(numAt c : FirstOrder.SyntacticTerm ℒₒᵣ)]).comp
        (FirstOrder.Rew.subst
          (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q := by
  ext x
  · cases x using Fin.cases with
    | zero => simp [FirstOrder.Rew.comp_app]
    | succ i => simp [FirstOrder.Rew.comp_app]
  · simp [FirstOrder.Rew.comp_app]

/-- **The instantiation computation for `belowG`.** -/
theorem subst_belowG (ψ : Semiproposition ℒₒᵣ 0 (n + 1)) :
    (FirstOrder.Rew.subst
        (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q ▹ (belowG ψ)
      = belowψ₂ gamma0Order₂.prec
        ((FirstOrder.Rew.subst
          (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q ▹ ψ) := by
  have hp : ((FirstOrder.Rew.subst
        (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q).q
        ▹ (precG (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 2)) #1 : Semiproposition ℒₒᵣ 0 (n + 2))
      = precAt₂ gamma0Order₂.prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) #1 := by
    rw [precG_zero, rew_precAt₂ _ _ (fun z => by simp)]
    simp [FirstOrder.Rew.q_subst]
  have hs : ((FirstOrder.Rew.subst
        (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q).q
        ▹ ((FirstOrder.Rew.subst (belowSub n) : FirstOrder.Rew ℒₒᵣ ℕ (n + 1) ℕ (n + 2)) ▹ ψ)
      = ((FirstOrder.Rew.subst
          (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q ▹ ψ)/[
            (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2)] := by
    show _ = FirstOrder.Rew.subst ![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2)] ▹ _
    rw [← FirstOrder.TransitiveRewriting.comp_app, ← FirstOrder.TransitiveRewriting.comp_app,
      comp_belowSub]
  rw [belowG, Semiformula.rew_all₀, FirstOrder.Rew.q_subst]
  show ∀¹ (_ ▹ (∼(precG _ _) ⋎ _)) = _
  rw [← FirstOrder.Rew.q_subst, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, hp, hs, belowψ₂]

/-- **The instantiation computation for the body.** -/
theorem subst_tiUptoBody (c : ℕ) (ψ : Semiproposition ℒₒᵣ 0 (n + 1)) :
    FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))
        ▹ (tiUptoBody (numAt c) ψ)
      = TIuptoψ₂ gamma0Order₂.prec
          ((FirstOrder.Rew.subst
            (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q ▹ ψ)
          (numAt c) := by
  have hprog : FirstOrder.Rew.subst
        (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ)) ▹ (progG ψ)
      = Progψ₂ gamma0Order₂.prec
        ((FirstOrder.Rew.subst
          (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q ▹ ψ) := by
    rw [progG, Semiformula.rew_all₀]
    show ∀¹ (_ ▹ (∼(belowG ψ) ⋎ ψ)) = _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
      subst_belowG, Progψ₂]
  have hbelow : FirstOrder.Rew.subst
        (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))
        ▹ ((FirstOrder.Rew.subst (atSub (numAt c)) : FirstOrder.Rew ℒₒᵣ ℕ (n + 1) ℕ n)
          ▹ (belowG ψ))
      = (belowψ₂ gamma0Order₂.prec
          ((FirstOrder.Rew.subst
            (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))).q ▹ ψ))/[
              (numAt c : FirstOrder.SyntacticTerm ℒₒᵣ)] := by
    rw [← FirstOrder.TransitiveRewriting.comp_app, comp_atSub,
      FirstOrder.TransitiveRewriting.comp_app, subst_belowG]
  show FirstOrder.Rew.subst _ ▹ (∼(progG ψ) ⋎ _) = _
  rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, hprog, hbelow,
    TIuptoψ₂]

end Inst

/-! ### The leaf, at an explicit height

`Climb₂.TIuptoψ₂_derivable` produces its height existentially; `allN₁_derivable`
needs one height common to every numeral instance, so the explicit form is
restated here. -/

/-- **`TIupto(≺₁, ā, ψ)` is cut-free derivable at height `ω^(a ⊕ 1) + 1`**, for
every arithmetical unary `ψ`. -/
theorem TIuptoψ₂_derivable_at (a : Gamma0Note) {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1}
    (hψ : Arith ψ) :
    OmegaDerivable₂ trueArithLits₂ evInst₂ 0
      (OrdinalNotation.succ (Gamma0Note.omegaPow (Gamma0Note.nadd a 1)))
      [ev₂ (TIuptoψ₂ gamma0Order₂.prec ψ (numAt (gamma0Code a)))] := by
  have h := OmegaDerivable₂.substX₂ (O := Gamma0Note) hψ (Climb₂.TIupto₂_derivable_at a)
  simp only [List.map_cons, List.map_nil] at h
  rwa [substX₂_ev₂_TIupto₂ gamma0Order₂.setFree_prec] at h

/-! ### The new axiom block -/

/-- **Every instance of the transfinite-induction scheme below `ā` is cut-free
derivable**, at `((ω^(a ⊕ 1) + 1) ⊕ n) ⊕ N`. -/
theorem tiUptoScheme_derivable_at {N n : ℕ} (a : Gamma0Note)
    (ψ : Semiproposition ℒₒᵣ N (n + 1)) (hψ : Arith ψ) :
    OmegaDerivable₂ trueArithLits₂ evInst₂ 0
      (OrdinalNotation.nadd (OrdinalNotation.nadd
        (OrdinalNotation.succ (Gamma0Note.omegaPow (Gamma0Note.nadd a 1)))
        (OrdinalNotation.ofNat n)) (OrdinalNotation.ofNat N))
      [ev₂ (tiUptoScheme a ψ)] := by
  have hbody : ∀ w : Fin n → ℕ, OmegaDerivable₂ trueArithLits₂ evInst₂ 0
      (OrdinalNotation.succ (Gamma0Note.omegaPow (Gamma0Note.nadd a 1)))
      [ev₂ (FirstOrder.Rew.subst (fun i => (numAt (w i) : FirstOrder.SyntacticTerm ℒₒᵣ))
        ▹ (freeN₁ N (tiUptoBody (numAt (gamma0Code a)) ψ)))] := by
    intro w
    rw [freeN₁_tiUptoBody, subst_tiUptoBody]
    exact TIuptoψ₂_derivable_at a
      ((arith_rew _ _).mpr (SchemeAxioms₂.arith_freeN₁ N hψ))
  have h1 := allN₁_derivable (freeN₁ N (tiUptoBody (numAt (gamma0Code a)) ψ)) hbody
  rw [← freeN₁_allN₁] at h1
  have h2 := allN₂_derivable (allN₁ n (tiUptoBody (numAt (gamma0Code a)) ψ)) h1
  rw [allN₁_eq_allNums, allN₂_eq_allSets] at h2
  exact h2

/-- **The new axiom is derivable below `ε_{a ⊕ 1} = φ_1(a ⊕ 1)`**, hence far
below `Γ₀`. -/
theorem tiUptoScheme_derivable_lt {N n : ℕ} (a : Gamma0Note)
    (ψ : Semiproposition ℒₒᵣ N (n + 1)) (hψ : Arith ψ) :
    ∃ β : Gamma0Note, β < Gamma0Note.veblenNote 1 (Gamma0Note.nadd a 1) ∧
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ (tiUptoScheme a ψ)] := by
  set b : Gamma0Note := Gamma0Note.nadd a 1 with hb
  have h1 : (1 : Gamma0Note) < Gamma0Note.epsilonNote b := Gamma0Note.one_lt_epsilon b
  have ha : a < Gamma0Note.epsilonNote b :=
    lt_of_lt_of_le (Gamma0Note.lt_nadd_one a) (Gamma0Note.le_epsilon_self b)
  have hn : Gamma0Note.nadd a 1 < Gamma0Note.epsilonNote b :=
    Gamma0Note.nadd_lt_epsilon ha h1
  have hw : Gamma0Note.omegaPow (Gamma0Note.nadd a 1) < Gamma0Note.epsilonNote b :=
    Gamma0Note.omegaPow_lt_epsilon hn
  refine ⟨_, ?_, tiUptoScheme_derivable_at a ψ hψ⟩
  exact Gamma0Note.nadd_lt_epsilon (Gamma0Note.nadd_lt_epsilon
    (Gamma0Note.nadd_lt_epsilon hw h1) (Gamma0Note.ofNat_lt_epsilon n b))
    (Gamma0Note.ofNat_lt_epsilon N b)

/-! ### Every axiom of `ACAΓ` -/

/-- **Every axiom of `ACA + TI(<Γ₀)` is cut-free derivable at some height in
`Gamma0Note`** — that is, below `Γ₀` by its type.  This is the hypothesis
`Axioms₂.cut_axioms₂_of` consumes; no uniform bound is needed, because
`not_derivable_TI₂_gamma0` refutes the conclusion at *every* height in
`Gamma0Note`. -/
theorem acaΓ_axiom_derivable (σ : Proposition ℒₒᵣ) (h : σ ∈ ACAΓ) :
    ∃ β : Gamma0Note, OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ σ] := by
  rcases h with h | ⟨N, n, a, ψ, hψ, -, -, rfl⟩
  · obtain ⟨β, -, hd⟩ := SchemeAxioms₂.aca_axiom_derivable σ h
    exact ⟨β, hd⟩
  · exact ⟨_, tiUptoScheme_derivable_at a ψ hψ⟩

/-- The old axioms, restated in the same shape. -/
theorem aca_axiom_derivable (σ : Proposition ℒₒᵣ) (h : σ ∈ ACA) :
    ∃ β : Gamma0Note, OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ σ] :=
  acaΓ_axiom_derivable σ (ACA_subset_ACAΓ h)

end AxiomsTI₂

end OrdinalAnalysis.ACAOmega
