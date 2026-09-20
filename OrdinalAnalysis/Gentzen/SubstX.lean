/-
  Substituting a formula for the set variable `X`.

  `LX` is arithmetic together with one fresh unary predicate `X`.  The lower
  bound at `ε₁` has to cut away every axiom of `PA[X] + TI(ε₀)`, and in the
  *scheme* formulation that theory has one transfinite-induction axiom for each
  unary formula `φ`, not just the single instance for `X`.  Only the `X`
  instance has been derived in the ω-calculus (`Epsilon1Axiom.TI₀_derivable`),
  and the derivations of the other instances are obtained from it by
  substitution: replace the atom `X(t)` everywhere by `φ(t)`.

  Three things about the shape.

  * **`substX` is a syntactic operation, defined by structural recursion**, and
    it is *not* a rewriting: it replaces a relation symbol, not a term.  The
    atom clause is where everything happens,

        X(t)  ↦  φ(t)  =  formulaAt φ t,        ∼X(t) ↦ ∼φ(t),

    and every arithmetic atom is left alone.  Because negation on
    `Semiformula` is a *function* (de Morgan is computed, not asserted), the
    `nrel` clause is stated as `∼(atom clause)` and `substX_neg` is then an
    easy induction.

  * **`substX` does not preserve complexity**, and it cannot: `φ` carries its
    own quantifiers.  What the height argument needs instead is that the
    identity sequent on a substituted atom costs `2·complexity φ`, which is
    `complexity_formulaAt`.

  * **The evaluator must be re-applied after substituting.**  The sequents in a
    derivation are not `ev`-normal — the rules do not force it — and `substX`
    creates new ground terms inside `φ` where `X`'s argument used to be.  So
    the transformation carried along a derivation is `φ ↦ ev (substX ψ φ)`, and
    the law that makes the induction go through is

        ev (substX ψ (ev φ)) = ev (substX ψ φ),                `ev_substX_ev`

    proved at *every* level, because the binder cases pass through level `n+1`
    even when only level `0` is wanted.  Its atomic content is
    `ev (formulaAt ψ (evT t)) = ev (formulaAt ψ t)`, which is one application
    of the value-dependence law `ev_rew_congr` of `Evaluate.lean`: the two
    substitutions `![evT t]` and `![t]` are `RewEq`, by `evT_idem`.

  Contents.

    `substXrel`, `substX`            the definition
    `substX_neg`                     de Morgan
    `substX_of_XFree`                `X`-free formulas are fixed
    `substX_of_isArithLit`           in particular the atomic axioms
    `rew_subst_closed`, `rew_formulaAt`
                                     a rewriting passes a closed formula's
                                     substitution instance
    `substX_rew`, `substX_subst₁`    **commutation with rewriting**, for closed `ψ`
    `ev_formulaAt_evT`, `ev_substXrel_evT`, `ev_substX_ev`
                                     **the key law**
    `inst_substX`                    the ω-rule's instances commute too
    `OmegaDerivable.substX`          **the transformation of derivations**
-/
import OrdinalAnalysis.Gentzen.EvInst
import OrdinalAnalysis.Gentzen.Jump
import OrdinalAnalysis.Gentzen.CodedOrder
import OrdinalAnalysis.Omega.Identity

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.SubstX

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.Evaluate
open OrdinalAnalysis.Gentzen.StandardLX (trueArithLits numLX IsArithLit)
open OrdinalAnalysis.Gentzen.EvInst

/-! ### The definition -/

/-- **The atom clause.**  An arithmetic atom is returned unchanged; the fresh
predicate `X(v 0)` becomes `ψ(v 0)`.  Matching `Sum.inr XRel.X` forces the
arity to be `1`, which is why `v 0` is well typed. -/
def substXrel {n : ℕ} (ψ : Semiformula LX ℕ 1) :
    {k : ℕ} → LX.Rel k → (Fin k → Semiterm LX ℕ n) → Semiformula LX ℕ n
  | _, Sum.inl r, v => Semiformula.rel (Sum.inl r) v
  | _, Sum.inr XRel.X, v => formulaAt ψ (v 0)

theorem substXrel_inl {n k : ℕ} (ψ : Semiformula LX ℕ 1) (r : (ℒₒᵣ : Language).Rel k)
    (v : Fin k → Semiterm LX ℕ n) :
    substXrel ψ (Sum.inl r) v = Semiformula.rel (Sum.inl r) v := rfl

theorem substXrel_X {n : ℕ} (ψ : Semiformula LX ℕ 1) (v : Fin 1 → Semiterm LX ℕ n) :
    substXrel ψ (Sum.inr XRel.X) v = formulaAt ψ (v 0) := rfl

/-- **Substitution of `ψ` for `X`.**  Structural, homomorphic on the
connectives and quantifiers; the whole content is `substXrel`. -/
def substX (ψ : Semiformula LX ℕ 1) : {n : ℕ} → Semiformula LX ℕ n → Semiformula LX ℕ n
  | _, Semiformula.verum => ⊤
  | _, Semiformula.falsum => ⊥
  | _, Semiformula.rel r v => substXrel ψ r v
  | _, Semiformula.nrel r v => ∼(substXrel ψ r v)
  | _, Semiformula.and φ χ => substX ψ φ ⋏ substX ψ χ
  | _, Semiformula.or φ χ => substX ψ φ ⋎ substX ψ χ
  | _, Semiformula.all φ => ∀¹ (substX ψ φ)
  | _, Semiformula.exs φ => ∃¹ (substX ψ φ)

variable (ψ : Semiformula LX ℕ 1)

@[simp] theorem substX_verum {n : ℕ} : substX ψ (⊤ : Semiformula LX ℕ n) = ⊤ := rfl

@[simp] theorem substX_falsum {n : ℕ} : substX ψ (⊥ : Semiformula LX ℕ n) = ⊥ := rfl

@[simp] theorem substX_rel {n k : ℕ} (r : LX.Rel k) (v : Fin k → Semiterm LX ℕ n) :
    substX ψ (Semiformula.rel r v) = substXrel ψ r v := rfl

@[simp] theorem substX_nrel {n k : ℕ} (r : LX.Rel k) (v : Fin k → Semiterm LX ℕ n) :
    substX ψ (Semiformula.nrel r v) = ∼(substXrel ψ r v) := rfl

@[simp] theorem substX_and {n : ℕ} (φ χ : Semiformula LX ℕ n) :
    substX ψ (φ ⋏ χ) = substX ψ φ ⋏ substX ψ χ := rfl

@[simp] theorem substX_or {n : ℕ} (φ χ : Semiformula LX ℕ n) :
    substX ψ (φ ⋎ χ) = substX ψ φ ⋎ substX ψ χ := rfl

@[simp] theorem substX_all {n : ℕ} (φ : Semiformula LX ℕ (n + 1)) :
    substX ψ (∀¹ φ) = ∀¹ (substX ψ φ) := rfl

@[simp] theorem substX_exs {n : ℕ} (φ : Semiformula LX ℕ (n + 1)) :
    substX ψ (∃¹ φ) = ∃¹ (substX ψ φ) := rfl

/-- `substX ψ (Xat t) = ψ(t)`: the clause the whole construction exists for. -/
@[simp] theorem substX_Xat {n : ℕ} (t : Semiterm LX ℕ n) :
    substX ψ (Xat t) = formulaAt ψ t := rfl

/-- Substituting `X(#0)` itself for `X` changes nothing. -/
theorem substX_Xat_bvar : substX ψ (Xat (#0 : Semiterm LX ℕ 1)) = ψ := by
  rw [substX_Xat]
  show Rew.subst ![(#0 : Semiterm LX ℕ 1)] ▹ ψ = ψ
  simp

/-! ### De Morgan -/

/-- **`substX` commutes with negation.**  The `nrel` clause was stated as the
negation of the `rel` clause precisely so that this is an induction with no
content. -/
@[simp] theorem substX_neg {n : ℕ} (φ : Semiformula LX ℕ n) :
    substX ψ (∼φ) = ∼(substX ψ φ) := by
  induction φ using Semiformula.rec' <;> simp [*]

/-! ### What `substX` fixes -/

/-- **An `X`-free formula is a fixed point.** -/
theorem substX_of_XFree {n : ℕ} :
    ∀ (φ : Semiformula LX ℕ n), LowerClass.XFree φ → substX ψ φ = φ := by
  intro φ
  induction φ using Semiformula.rec' with
  | hverum => intro _; rfl
  | hfalsum => intro _; rfl
  | hrel r v =>
      intro h
      obtain ⟨r', rfl⟩ := (LowerClass.XFree_rel r v).mp h
      rfl
  | hnrel r v =>
      intro h
      obtain ⟨r', rfl⟩ := (LowerClass.XFree_nrel r v).mp h
      rfl
  | hand φ χ ihφ ihχ =>
      intro h
      rw [substX_and, ihφ h.1, ihχ h.2]
  | hor φ χ ihφ ihχ =>
      intro h
      rw [substX_or, ihφ h.1, ihχ h.2]
  | hall φ ih => intro h; rw [substX_all, ih h]
  | hexs φ ih => intro h; rw [substX_exs, ih h]

/-- **The atomic axioms of the ω-calculus are fixed.**  They are closed
arithmetic literals, and `substX` never touches an arithmetic atom. -/
theorem substX_of_isArithLit {φ : Proposition LX} (h : IsArithLit φ) :
    substX ψ φ = φ := by
  obtain ⟨k, r, v, (rfl | rfl), -⟩ := h
  · rfl
  · rfl

/-! ### Complexity -/

/-- An instance of `ψ` has the complexity of `ψ`: a rewriting does not change
the logical skeleton.  This is the number the identity sequents cost. -/
@[simp] theorem complexity_formulaAt {n : ℕ} (t : Semiterm LX ℕ n) :
    (formulaAt ψ t).complexity = ψ.complexity := by
  simp [formulaAt]

/-! ### Commutation with rewriting

`substX` commutes with every rewriting, provided `ψ` has no *free* variables:
the rewriting would move them, while the copy of `ψ` planted at an `X`-atom is
insulated from the outer substitution.  Bound variables of `ψ` are no
obstacle — `ψ` has one, `#0`, and it is filled by `X`'s argument. -/

/-- A rewriting passes through the substitution instance of a closed formula:
only the substituted terms are seen. -/
theorem rew_subst_closed {m : ℕ} {θ : Semiformula LX ℕ m} (hθ : θ.freeVariables = ∅)
    {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) (v : Fin m → Semiterm LX ℕ n₁) :
    ω ▹ (Rew.subst v ▹ θ) = Rew.subst (fun i => ω (v i)) ▹ θ := by
  rw [← TransitiveRewriting.comp_app]
  refine Semiformula.rew_eq_of_funEqOn ?_ ?_
  · intro x
    simp [Rew.comp_app]
  · intro x hx
    have hx' : x ∈ θ.freeVariables := hx
    rw [hθ] at hx'
    exact absurd hx' (by simp)

variable {ψ}

/-- **A rewriting passes through an instance of a closed `ψ`.** -/
theorem rew_formulaAt (hψ : ψ.freeVariables = ∅) {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂)
    (t : Semiterm LX ℕ n₁) : ω ▹ (formulaAt ψ t) = formulaAt ψ (ω t) := by
  have hv : (fun i => ω ((![t] : Fin 1 → Semiterm LX ℕ n₁) i)) = ![ω t] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  show ω ▹ (Rew.subst ![t] ▹ ψ) = Rew.subst ![ω t] ▹ ψ
  rw [rew_subst_closed hψ ω ![t], hv]

/-- The atom clause commutes with every rewriting. -/
theorem rew_substXrel (hψ : ψ.freeVariables = ∅) {n₁ n₂ k : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂)
    (r : LX.Rel k) (v : Fin k → Semiterm LX ℕ n₁) :
    substXrel ψ r (fun i => ω (v i)) = ω ▹ (substXrel ψ r v) := by
  rcases r with r' | x
  · exact (Semiformula.rew_rel ω (Sum.inl r') v).symm
  · cases x
    exact (rew_formulaAt hψ ω (v 0)).symm

/-- **`substX` commutes with every rewriting**, for a `ψ` with no free
variables. -/
theorem substX_rew (hψ : ψ.freeVariables = ∅) {n₁ : ℕ} :
    ∀ (φ : Semiformula LX ℕ n₁) (n₂ : ℕ) (ω : Rew LX ℕ n₁ ℕ n₂),
      substX ψ (ω ▹ φ) = ω ▹ substX ψ φ := by
  intro φ
  induction φ using Semiformula.rec' with
  | hverum => intro n₂ ω; simp
  | hfalsum => intro n₂ ω; simp
  | hrel r v =>
      intro n₂ ω
      rw [Semiformula.rew_rel ω r v, substX_rel, substX_rel]
      exact rew_substXrel hψ ω r v
  | hnrel r v =>
      intro n₂ ω
      rw [Semiformula.rew_nrel ω r v, substX_nrel, substX_nrel,
        LogicalConnective.HomClass.map_neg]
      exact congrArg (∼·) (rew_substXrel hψ ω r v)
  | hand φ χ ihφ ihχ =>
      intro n₂ ω
      simp only [LogicalConnective.HomClass.map_and, substX_and, ihφ n₂ ω, ihχ n₂ ω]
  | hor φ χ ihφ ihχ =>
      intro n₂ ω
      simp only [LogicalConnective.HomClass.map_or, substX_or, ihφ n₂ ω, ihχ n₂ ω]
  | hall φ ih =>
      intro n₂ ω
      simp only [Rewriting.app_all, substX_all, ih (n₂ + 1) ω.q]
  | hexs φ ih =>
      intro n₂ ω
      simp only [Rewriting.app_exs, substX_exs, ih (n₂ + 1) ω.q]

/-- The single-substitution form, which is what the ω-rule consumes. -/
theorem substX_subst₁ (hψ : ψ.freeVariables = ∅) (φ : Semiproposition LX 1)
    (t : SyntacticTerm LX) : substX ψ (φ/[t]) = (substX ψ φ)/[t] :=
  substX_rew hψ φ 0 (Rew.subst ![t])

/-! ### The key law

The sequents of a derivation are not `ev`-normal, so the transformation carried
along it has to normalise after substituting; the law below says that
normalising *before* substituting changes nothing. -/

/-- The atomic content: substituting a term and substituting its normal form
give instances with the same normal form.  One application of the
value-dependence law, with `evT_idem` supplying `RewEq`. -/
theorem ev_formulaAt_evT {n : ℕ} (t : Semiterm LX ℕ n) :
    ev (formulaAt ψ (evT t)) = ev (formulaAt ψ t) := by
  refine ev_rew_congr ψ n (Rew.subst ![evT t]) (Rew.subst ![t]) ⟨fun i => ?_, fun x => ?_⟩
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp only [Rew.subst_bvar, Matrix.cons_val_zero]
    exact evT_idem t
  · simp only [Rew.subst_fvar]

/-- The atom clause of the key law. -/
theorem ev_substXrel_evT {n k : ℕ} (r : LX.Rel k) (v : Fin k → Semiterm LX ℕ n) :
    ev (substXrel ψ r (fun i => evT (v i))) = ev (substXrel ψ r v) := by
  rcases r with r' | x
  · exact (congrArg ev (ev_rel (Sum.inl r') v).symm).trans (ev_idem _)
  · cases x
    exact ev_formulaAt_evT (v 0)

/-- **The key law.**  Evaluating before substituting does not change the
evaluated result — at every level, because the binder cases of the induction
pass through level `n + 1`. -/
theorem ev_substX_ev : ∀ {n : ℕ} (φ : Semiformula LX ℕ n),
    ev (substX ψ (ev φ)) = ev (substX ψ φ) := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => exact ev_substXrel_evT r v
  | hnrel r v =>
      simp only [ev_nrel, substX_nrel, ev_neg]
      rw [ev_substXrel_evT r v]
  | hand φ χ ihφ ihχ => simp only [ev_and, substX_and, ihφ, ihχ]
  | hor φ χ ihφ ihχ => simp only [ev_or, substX_or, ihφ, ihχ]
  | hall φ ih => simp only [ev_all, substX_all, ih]
  | hexs φ ih => simp only [ev_exs, substX_exs, ih]

/-- **The ω-rule's instances commute with the transformation.**  Read from
right to left: the `n`-th instance of the transformed body is the transform of
the `n`-th instance. -/
theorem inst_substX (hψ : ψ.freeVariables = ∅) (φ : Semiproposition LX 1) (n : ℕ) :
    evInst.inst (ev (substX ψ φ)) n = ev (substX ψ (evInst.inst φ n)) :=
  calc evInst.inst (ev (substX ψ φ)) n
      = ev ((substX ψ φ)/[numLX n]) := evInst_inst_ev _ _
    _ = ev (substX ψ (φ/[numLX n])) := (congrArg ev (substX_subst₁ hψ φ (numLX n))).symm
    _ = ev (substX ψ (ev (φ/[numLX n]))) := (ev_substX_ev _).symm
    _ = ev (substX ψ (evInst.inst φ n)) := rfl

end OrdinalAnalysis.Gentzen.SubstX

/-! ### The transformation of derivations -/

namespace OrdinalAnalysis.OmegaDerivable

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.Evaluate
open OrdinalAnalysis.Gentzen.StandardLX (trueArithLits numLX)
open OrdinalAnalysis.Gentzen.EvInst
open OrdinalAnalysis.Gentzen.SubstX

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- **Substituting `ψ` for `X` in a cut-free derivation.**

Every rule survives.  The atomic axioms are closed arithmetic literals, which
`substX` fixes and `ev` keeps axioms.  An identity sequent on an arithmetic
atom is again an identity sequent; an identity sequent on `X(t)` becomes one on
`ψ(t)`, which is no longer atomic and costs `2·complexity ψ` — that, and
nothing else, is why the height grows, and why it grows by a *constant*
independent of the derivation.  The quantifier rules go through by
`inst_substX`, and `cut` cannot occur at rank `0`. -/
theorem substX (ψ : Semiformula LX ℕ 1) (hψ : ψ.freeVariables = ∅) :
    ∀ {α : O} {Γ : Sequent LX},
      OmegaDerivable trueArithLits evInst 0 α Γ →
      OmegaDerivable trueArithLits evInst 0
        (OrdinalNotation.nadd α (OrdinalNotation.ofNat (2 * ψ.complexity)))
        (Γ.map fun φ => ev (SubstX.substX ψ φ)) := by
  intro α Γ h
  induction h with
  | @atom α φ hφ =>
      simp only [List.map_cons, List.map_nil, SubstX.substX_of_isArithLit ψ hφ.1]
      exact OmegaDerivable.atom (trueArithLits_ev hφ)
  | @identity α k rl v =>
      simp only [List.map_cons, List.map_nil]
      rcases rl with r' | x
      · exact OmegaDerivable.identity (O := O) (Sum.inl r') (fun i => evT (v i))
      · cases x
        show OmegaDerivable trueArithLits evInst 0
          (OrdinalNotation.nadd α (OrdinalNotation.ofNat (2 * ψ.complexity)))
          [ev (formulaAt ψ (v 0)), ev (∼(formulaAt ψ (v 0)))]
        rw [ev_neg]
        refine OmegaDerivable.mono_ord
          (OmegaDerivable.identity_of_mem ψ.complexity (ev (formulaAt ψ (v 0)))
            (le_of_eq (by simp)) (by simp) (by simp))
          (OrdinalNotation.le_nadd_right α _)
  | @verum α => exact OmegaDerivable.verum
  | @or α β φ χ Γ hlt _ ih =>
      have e : ev (SubstX.substX ψ (φ ⋎ χ))
          = ev (SubstX.substX ψ φ) ⋎ ev (SubstX.substX ψ χ) := rfl
      simp only [List.map_cons, e]
      exact OmegaDerivable.or (OrdinalNotation.nadd_lt_nadd_left _ hlt)
        (by simpa only [List.map_cons] using ih)
  | @and α β γ φ χ Γ hβ hγ _ _ ihφ ihχ =>
      have e : ev (SubstX.substX ψ (φ ⋏ χ))
          = ev (SubstX.substX ψ φ) ⋏ ev (SubstX.substX ψ χ) := rfl
      simp only [List.map_cons, e]
      exact OmegaDerivable.and (OrdinalNotation.nadd_lt_nadd_left _ hβ)
        (OrdinalNotation.nadd_lt_nadd_left _ hγ)
        (by simpa only [List.map_cons] using ihφ)
        (by simpa only [List.map_cons] using ihχ)
  | @omegaRule α φ Γ β hβ _ ih =>
      have e : ev (SubstX.substX ψ (∀¹ φ)) = ∀¹ (ev (SubstX.substX ψ φ)) := rfl
      simp only [List.map_cons, e]
      refine OmegaDerivable.omegaRule
        (fun n => OrdinalNotation.nadd (β n) (OrdinalNotation.ofNat (2 * ψ.complexity)))
        (fun n => OrdinalNotation.nadd_lt_nadd_left _ (hβ n)) (fun n => ?_)
      rw [SubstX.inst_substX hψ φ n]
      exact (by simpa only [List.map_cons] using ih n)
  | @exs α β φ Γ n hlt _ ih =>
      have e : ev (SubstX.substX ψ (∃¹ φ)) = ∃¹ (ev (SubstX.substX ψ φ)) := rfl
      simp only [List.map_cons, e]
      refine OmegaDerivable.exs n (OrdinalNotation.nadd_lt_nadd_left _ hlt) ?_
      rw [SubstX.inst_substX hψ φ n]
      exact (by simpa only [List.map_cons] using ih)
  | @contraction α Δ Γ ss _ ih =>
      exact OmegaDerivable.contraction (List.map_subset _ ss) ih
  | cut hc _ _ _ _ _ _ => exact absurd hc (Nat.not_lt_zero _)

end OrdinalAnalysis.OmegaDerivable
