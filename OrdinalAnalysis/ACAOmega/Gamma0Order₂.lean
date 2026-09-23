/-
  The unsegmented coded Veblen ordering `gamma0Order₂ : CodedOrder₂ Gamma0Note`, and its
  restriction to the segment below a Veblen value `φ_a(b)`.

  `gamma0Order₂` is `ACAOmega/CodedOrder₂.lean`'s `epsilonSegOrder₂` with the second conjunct
  dropped: the ordering is `precFO₁` itself, lifted, read over *all* of `Gamma0Note` rather
  than a bounded segment.  Every field is the one `epsilonSegOrder₂` already uses for its
  first conjunct — `precFO₁`, `eval_precFO₁`, `freeVariables_precFO₁`,
  `eval_precAt₂_lift`, `precN₁_code_iff` (`Gentzen/CodedVeblen.lean`) — so nothing here is new
  syntax, only a smaller structure.

  `vebSegOrder₂ a b` is `epsilonSegOrder₂ a` with `epsilonNote a` replaced by `veblenNote a b`
  throughout: the segment `x ≺₁ y ∧ y ≺₁ (code of φ_a(b))`, read on
  `Gamma0Note.VeblenBelow a b`.  It needs no hypothesis on `a` to *build* (a `CodedOrder₂`
  is just a `LinearOrder`-indexed structure, and `VeblenBelow a b` carries one unconditionally
  via `Below`), but the boundedness corollary `not_derivable_TI₂_vebSeg` runs the generic
  `not_derivable_TI₂` at height type `VeblenBelow a b`, which needs an `OrdinalNotation`
  instance — and *that* needs `0 < a` (`Ordinal/Veblen/VeblenBelow.lean`'s
  `closed_veblenNote`), so `ha` travels with the segment order from here on.  Because that
  instance is a `def` (`Gamma0Note.VeblenBelow.ordinalNotation`), not a global `instance` —
  the same reason `closed_veblenNote`'s bound is `def`, not `instance` — the corollary takes
  `[OrdinalNotation (Gamma0Note.VeblenBelow a b)]` as an ordinary parameter, exactly as
  `Boundedness₂.lean`'s `not_derivable_TI₂` is generic in `[OrdinalNotation O]`; callers
  supply it with `letI := Gamma0Note.VeblenBelow.ordinalNotation a b ha`.
-/
import OrdinalAnalysis.ACAOmega.Boundedness₂
import OrdinalAnalysis.Ordinal.Veblen.VeblenBelow

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA
open OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.CodedVeblen (precN₁ precN₁_code_iff)
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)
open OrdinalAnalysis.Gamma0Note (veblenNote VeblenBelow)

/-! ### The unsegmented coded ordering of all of `Gamma0Note` -/

/-- **The coded ordering of the notations below `Γ₀`, second-order, unsegmented.**  The
`Γ₀` analogue of `CodedVeblen.gamma0Order`, in the syntax `Boundedness₂.lean` consumes. -/
def gamma0Order₂ : CodedOrder₂ Gamma0Note where
  prec := lift precFO₁
  prec₀ := precFO₁
  prec_eq := rfl
  freeVariables_prec₀ := freeVariables_precFO₁
  code := gamma0Code
  precN := precN₁
  eval_precAt_numeral := by
    intro 𝕊 F f m n
    rw [eval_precAt₂_lift]
    rw [val_numAt, val_numAt]
    exact eval_precFO₁ m n f
  precN_code_iff := precN₁_code_iff

@[simp] theorem gamma0Order₂_prec : gamma0Order₂.prec = lift precFO₁ := rfl

@[simp] theorem gamma0Order₂_code : gamma0Order₂.code = gamma0Code := rfl

@[simp] theorem gamma0Order₂_precN : gamma0Order₂.precN = precN₁ := rfl

/-- **`TI₂(≺₁, X)` has no cut-free `ACA_∞`-derivation at any height in `Gamma0Note`.**  The
`a := Γ₀` reading of `not_derivable_TI₂_epsilonSeg`/`not_derivable_TI₂_gamma0` — except there
is no segment here at all: this is the full, unbounded Veblen ordering. -/
theorem not_derivable_TI₂_gamma0 (α : Gamma0Note) :
    ¬ OmegaDerivable₂ trueArithLits₂ evInst₂ 0 α [ev₂ (TI₂ gamma0Order₂.prec)] :=
  not_derivable_TI₂ gamma0Order₂ α

/-! ### The segment below `φ_a(b)` -/

/-- `≺₁`'s segment below `φ_a(b)`, as a first-order formula: `x ≺₁ y ∧ y ≺₁ (code of
φ_a(b))`.  `ACAOmega/CodedOrder₂.lean`'s `precSeg₀` with `epsilonNote a` replaced by
`veblenNote a b`. -/
def precSegVeb₀ (a b : Gamma0Note) : FirstOrder.Semiformula ℒₒᵣ ℕ 2 :=
  precFO₁ ⋏ (FirstOrder.Rew.subst
    ![(#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2),
      (numAt (gamma0Code (veblenNote a b)) : FirstOrder.Semiterm ℒₒᵣ ℕ 2)] ▹ precFO₁)

theorem freeVariables_precSegVeb₀ (a b : Gamma0Note) :
    (precSegVeb₀ a b).freeVariables = ∅ := by
  have h : (FirstOrder.Rew.subst
      ![(#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2),
        (numAt (gamma0Code (veblenNote a b)) : FirstOrder.Semiterm ℒₒᵣ ℕ 2)]
      ▹ precFO₁).freeVariables = ∅ := by
    refine LowerSyntax.freeVariables_rew_eq_empty _ freeVariables_precFO₁ ?_
    refine Fin.forall_fin_two.mpr ⟨by simp, ?_⟩
    simp only [FirstOrder.Rew.subst_bvar, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    simp [numAt]
  simp [precSegVeb₀, h]

/-- `m ≺ₐ,ᵦ' n`: `m ≺₁ n` and `n ≺₁ (code of φ_a(b))`. -/
def precNSegVeb (a b : Gamma0Note) (m n : ℕ) : Prop :=
  precN₁ m n ∧ precN₁ n (gamma0Code (veblenNote a b))

theorem eval_precSegVeb₀ (a b : Gamma0Note) (m n : ℕ) (f : ℕ → ℕ) :
    FirstOrder.Semiformula.Eval (M := ℕ) ![m, n] f (precSegVeb₀ a b) ↔
      precNSegVeb a b m n := by
  have hsub : FirstOrder.Semiformula.Eval (M := ℕ) ![m, n] f
      (FirstOrder.Rew.subst
        ![(#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2),
          (numAt (gamma0Code (veblenNote a b)) : FirstOrder.Semiterm ℒₒᵣ ℕ 2)]
        ▹ precFO₁)
      ↔ precN₁ n (gamma0Code (veblenNote a b)) := by
    rw [FirstOrder.Semiformula.eval_rew]
    have e₁ : (FirstOrder.Semiterm.val (M := ℕ) ![m, n] f ∘
        ⇑(FirstOrder.Rew.subst
          ![(#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2),
            (numAt (gamma0Code (veblenNote a b)) : FirstOrder.Semiterm ℒₒᵣ ℕ 2)]) ∘
        FirstOrder.Semiterm.bvar) = ![n, gamma0Code (veblenNote a b)] := by
      funext i
      revert i
      refine Fin.forall_fin_two.mpr ⟨by simp, by simp⟩
    have e₂ : (FirstOrder.Semiterm.val (M := ℕ) ![m, n] f ∘
        ⇑(FirstOrder.Rew.subst
          ![(#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2),
            (numAt (gamma0Code (veblenNote a b)) : FirstOrder.Semiterm ℒₒᵣ ℕ 2)]) ∘
        FirstOrder.Semiterm.fvar) = f := by
      funext x; simp
    rw [e₁, e₂]
    exact eval_precFO₁ _ _ f
  simp only [precSegVeb₀, LogicalConnective.HomClass.map_and, eval_precFO₁, hsub]
  rfl

/-- **The semantic bridge for the segment below `φ_a(b)`.** -/
theorem precNSegVeb_code_iff (a b : Gamma0Note) (x y : VeblenBelow a b) :
    precNSegVeb a b (gamma0Code x.1) (gamma0Code y.1) ↔ x < y := by
  unfold precNSegVeb
  rw [precN₁_code_iff, precN₁_code_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩

/-- **The coded ordering of the notations below `φ_a(b)`, for `0 < a`.**  `epsilonSegOrder₂`
with `epsilonNote a` replaced by `veblenNote a b`; `ha` is not used by any field here (a
`CodedOrder₂` needs no closure), but travels with the order because
`not_derivable_TI₂_vebSeg` needs it. -/
def vebSegOrder₂ (a b : Gamma0Note) (ha : 0 < a) : CodedOrder₂ (VeblenBelow a b) where
  prec := lift (precSegVeb₀ a b)
  prec₀ := precSegVeb₀ a b
  prec_eq := rfl
  freeVariables_prec₀ := freeVariables_precSegVeb₀ a b
  code := fun x => gamma0Code x.1
  precN := precNSegVeb a b
  eval_precAt_numeral := by
    intro 𝕊 F f m n
    rw [eval_precAt₂_lift]
    rw [val_numAt, val_numAt]
    exact eval_precSegVeb₀ a b m n f
  precN_code_iff := precNSegVeb_code_iff a b

@[simp] theorem vebSegOrder₂_prec (a b : Gamma0Note) (ha : 0 < a) :
    (vebSegOrder₂ a b ha).prec = lift (precSegVeb₀ a b) := rfl

@[simp] theorem vebSegOrder₂_code (a b : Gamma0Note) (ha : 0 < a) (x : VeblenBelow a b) :
    (vebSegOrder₂ a b ha).code x = gamma0Code x.1 := rfl

@[simp] theorem vebSegOrder₂_precN (a b : Gamma0Note) (ha : 0 < a) :
    (vebSegOrder₂ a b ha).precN = precNSegVeb a b := rfl

/-- **`TI₂(≺₁, X)` has no cut-free `ACA_∞`-derivation at any height below `φ_a(b)`, for
`0 < a`.**  The `Γ₀` boundedness lemma at the segment `φ_a(0)` mentioned in the design notes
is the case `b := 0`. -/
theorem not_derivable_TI₂_vebSeg (a b : Gamma0Note) (ha : 0 < a)
    [OrdinalNotation (VeblenBelow a b)] (α : VeblenBelow a b) :
    ¬ OmegaDerivable₂ trueArithLits₂ evInst₂ 0 α [ev₂ (TI₂ (vebSegOrder₂ a b ha).prec)] :=
  not_derivable_TI₂ (vebSegOrder₂ a b ha) α

end OrdinalAnalysis.ACAOmega
