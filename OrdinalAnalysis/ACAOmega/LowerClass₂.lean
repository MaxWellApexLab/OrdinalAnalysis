/-
  The class `C` of the boundedness lemma, second-order and already evaluated.

  This is `Gentzen/LowerClass.lean` and `Gentzen/LowerClassEv.lean` merged and
  transposed to the monadic second-order syntax.  The merge is possible because
  the second-order evaluator `ev₂` fixes the three atomic shapes on the nose
  (`xat`, `nxat`, `allXat₂`), so there is no longer any reason to keep a "raw"
  class and its image side by side: the class below is the evaluated one, and
  the first-order file's `InC` has no second-order counterpart.

  The members, nine shapes as in §C of the specification:

  | shape                           | first-order original            |
  |---------------------------------|---------------------------------|
  | `SetFree φ`                     | `IsXFreeClosed φ`               |
  | `ev₂ (TI₂ C.prec)`              | `ev (TI C.prec)`                |
  | `ev₂ (∼Prog₂ C.prec)`           | `ev (∼Prog C.prec)`             |
  | `allXat₂`                       | `allXat`                        |
  | `ev₂ (belowAt₂ C n)`            | `ev (LowerClass.belowAt C n)`   |
  | `xat n`   (`n̄ ∈ X`)             | `Xat (numLX n)`                 |
  | `nxat n`  (`n̄ ∉ X`)             | `∼(Xat (numLX n))`              |
  | `ev₂ (P₂ C n)`                  | `ev (LowerClass.P C n)`         |
  | `ev₂ (precOrXat₂ C k n)`        | `ev (precOrXat C k n)`          |

  Three things are new relative to the first-order files.

  * **`head₂` has fourteen tags**, not eight: Foundation's second-order
    `Semiformula` has four atomic set constructors and two more quantifiers.
    `head₂_ev₂` is `rfl` in every case, so the whole clash machinery lifts.

  * **`SetFree` decides more than `head₂` can.**  The two shapes
    `ev₂ (below₂ C.prec)` and `ev₂ (precAt₂ C.prec #0 n̄)` can have the *same*
    head — the ordering is an arbitrary lifted formula, so `precAt₂` may well be
    a `∀¹` — and nothing about the head separates them.  What separates them is
    that the first mentions the set variable and the second does not.  Every
    "these two shapes cannot be equal" step that `head₂` does not settle is
    settled by `SetFree`.

  * **General identity needs `InCe₂.neg_cases`.**  The second-order calculus has
    `identity φ : ⊢ [φ, ∼φ]` for *every* `φ`, so the boundedness induction meets
    a sequent both of whose members are in the class.  `neg_cases` says that can
    only happen for the set-free members and the two atoms — the six remaining
    shapes have a negation that is not in the class at all, which is what the
    six `not_inCe₂_*` lemmas below say.
-/
import OrdinalAnalysis.ACAOmega.CodedOrder₂

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA

variable {O : Type} [LinearOrder O] {C : CodedOrder₂ O}

/-! ### Head tags

`⋏`, `⋎`, `∀¹`, `∃¹`, `∀²`, `∃²` are `LogicalConnective`/`Quantifier` notation,
not constructors, so `injection` cannot be pointed at an equation between two of
them (a known pitfall).  A numeric tag reduces every impossible case to
arithmetic. -/

/-- The outermost constructor of a second-order formula, as a numeric tag. -/
def head₂ {N n : ℕ} : Semiformula ℒₒᵣ ℕ ℕ N n → ℕ
  |  .rel _ _ => 0
  | .nrel _ _ => 1
  |    _ ∈# _ => 2
  |    _ ∉# _ => 3
  |    _ ∈& _ => 4
  |    _ ∉& _ => 5
  |         ⊤ => 6
  |         ⊥ => 7
  |     _ ⋏ _ => 8
  |     _ ⋎ _ => 9
  |      ∀¹ _ => 10
  |      ∃¹ _ => 11
  |      ∀² _ => 12
  |      ∃² _ => 13

section HeadSimp

variable {N n : ℕ}

@[simp] theorem head₂_rel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    head₂ (.rel r v : Semiformula ℒₒᵣ ℕ ℕ N n) = 0 := rfl

@[simp] theorem head₂_nrel {k : ℕ} (r : (ℒₒᵣ : FirstOrder.Language).Rel k)
    (v : Fin k → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    head₂ (.nrel r v : Semiformula ℒₒᵣ ℕ ℕ N n) = 1 := rfl

@[simp] theorem head₂_bvar (X : Fin N) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    head₂ (t ∈# X : Semiformula ℒₒᵣ ℕ ℕ N n) = 2 := rfl

@[simp] theorem head₂_nbvar (X : Fin N) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    head₂ (t ∉# X : Semiformula ℒₒᵣ ℕ ℕ N n) = 3 := rfl

@[simp] theorem head₂_fvar (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    head₂ (t ∈& X : Semiformula ℒₒᵣ ℕ ℕ N n) = 4 := rfl

@[simp] theorem head₂_nfvar (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    head₂ (t ∉& X : Semiformula ℒₒᵣ ℕ ℕ N n) = 5 := rfl

@[simp] theorem head₂_verum : head₂ (⊤ : Semiformula ℒₒᵣ ℕ ℕ N n) = 6 := rfl

@[simp] theorem head₂_falsum : head₂ (⊥ : Semiformula ℒₒᵣ ℕ ℕ N n) = 7 := rfl

@[simp] theorem head₂_and (φ ψ : Semiformula ℒₒᵣ ℕ ℕ N n) : head₂ (φ ⋏ ψ) = 8 := rfl

@[simp] theorem head₂_or (φ ψ : Semiformula ℒₒᵣ ℕ ℕ N n) : head₂ (φ ⋎ ψ) = 9 := rfl

@[simp] theorem head₂_all₁ (φ : Semiformula ℒₒᵣ ℕ ℕ N (n + 1)) : head₂ (∀¹ φ) = 10 := rfl

@[simp] theorem head₂_exs₁ (φ : Semiformula ℒₒᵣ ℕ ℕ N (n + 1)) : head₂ (∃¹ φ) = 11 := rfl

@[simp] theorem head₂_all₂ (φ : Semiformula ℒₒᵣ ℕ ℕ (N + 1) n) : head₂ (∀² φ) = 12 := rfl

@[simp] theorem head₂_exs₂ (φ : Semiformula ℒₒᵣ ℕ ℕ (N + 1) n) : head₂ (∃² φ) = 13 := rfl

end HeadSimp

/-- **`ev₂` does not change the head constructor.**  Every case is `rfl`. -/
@[simp] theorem head₂_ev₂ {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    head₂ (ev₂ φ) = head₂ φ := by
  induction φ using Semiformula.rec' <;> rfl

/-- The tactic for "this shape is not that shape": compare heads. -/
theorem ne_of_head₂ {N n : ℕ} {φ ψ : Semiformula ℒₒᵣ ℕ ℕ N n} (h : head₂ φ ≠ head₂ ψ) :
    φ ≠ ψ := fun e => h (congrArg head₂ e)

/-! ### The named members -/

/-- `n̄ ∈ X`. -/
def xat (n : ℕ) : Proposition ℒₒᵣ := ((numAt n : FirstOrder.SyntacticTerm ℒₒᵣ) ∈& 0)

/-- `n̄ ∉ X`; this *is* `∼(xat n)`, on the nose. -/
def nxat (n : ℕ) : Proposition ℒₒᵣ := ((numAt n : FirstOrder.SyntacticTerm ℒₒᵣ) ∉& 0)

@[simp] theorem neg_xat (n : ℕ) : ∼(xat n) = nxat n := rfl

@[simp] theorem neg_nxat (n : ℕ) : ∼(nxat n) = xat n := rfl

/-- `(∀ y ≺ x, y ∈ X)` at the numeral `n̄`. -/
def belowAt₂ (C : CodedOrder₂ O) (n : ℕ) : Proposition ℒₒᵣ :=
  (below₂ C.prec)/[(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)]

/-- Its body: `∼(#0 ≺ n̄) ⋎ #0 ∈ X`. -/
def belowBody₂ (C : CodedOrder₂ O) (n : ℕ) : Semiproposition ℒₒᵣ 0 1 :=
  ∼(precAt₂ C.prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) (numAt n)) ⋎
    ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0)

/-- `P n := (∀ y ≺ n̄, y ∈ X) ⋏ n̄ ∉ X` — the body of `∼Prog₂` at `n̄`. -/
def P₂ (C : CodedOrder₂ O) (n : ℕ) : Proposition ℒₒᵣ := belowAt₂ C n ⋏ nxat n

/-- `∼(k̄ ≺ n̄) ⋎ k̄ ∈ X` — the ω-premises of `belowAt₂ C n`. -/
def precOrXat₂ (C : CodedOrder₂ O) (k n : ℕ) : Proposition ℒₒᵣ :=
  ∼(precAt₂ C.prec (numAt k) (numAt n)) ⋎ xat k

theorem belowAt₂_eq (n : ℕ) : belowAt₂ C n = ∀¹ (belowBody₂ C n) :=
  subst_below₂_numeral C.prec n

theorem P₂_eq (n : ℕ) : P₂ C n = belowAt₂ C n ⋏ nxat n := rfl

theorem precOrXat₂_eq (k n : ℕ) :
    precOrXat₂ C k n = ∼(precAt₂ C.prec (numAt k) (numAt n)) ⋎ xat k := rfl

/-- The `exs`-premise of `∼Prog₂(≺)` at `n̄` is `P₂ C n`. -/
theorem subst_negProg₂_body (n : ℕ) :
    ((below₂ C.prec) ⋏ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∉& 0))
        /[(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)] = P₂ C n := by
  show (below₂ C.prec)/[(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)] ⋏
    (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∉& 0) : Semiformula ℒₒᵣ ℕ ℕ 0 1)
      /[(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)] = P₂ C n
  rw [P₂_eq, belowAt₂]
  rfl

/-- The `omegaRule`-premises of `belowAt₂ C n` are the `precOrXat₂ C m n`. -/
theorem subst_belowBody₂ (m n : ℕ) :
    (belowBody₂ C n)/[(numAt m : FirstOrder.SyntacticTerm ℒₒᵣ)] = precOrXat₂ C m n :=
  subst_belowBody₂_numeral C.prec n m

/-! ### The shapes after evaluation -/

@[simp] theorem ev₂_xat (n : ℕ) : ev₂ (xat n) = xat n := by simp [xat]

@[simp] theorem ev₂_allXat₂ : ev₂ allXat₂ = allXat₂ := by simp [allXat₂]

/-- Deliberately *not* `@[simp]`: `ev₂_neg` is, so the left-hand side is not in
simp normal form and the lemma would silently never fire. -/
theorem ev₂_nxat (n : ℕ) : ev₂ (nxat n) = nxat n := by
  rw [← neg_xat, ev₂_neg, ev₂_xat, neg_xat]

theorem ev₂_TI₂_eq : ev₂ (TI₂ C.prec) = ev₂ (∼(Prog₂ C.prec)) ⋎ allXat₂ := by
  rw [TI₂_eq, ev₂_or, ev₂_allXat₂]

theorem ev₂_negProg₂_eq :
    ev₂ (∼(Prog₂ C.prec)) =
      ∃¹ (ev₂ ((below₂ C.prec) ⋏ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∉& 0))) := by
  rw [neg_Prog₂, ev₂_exs₁]

theorem ev₂_Prog₂_eq :
    ev₂ (Prog₂ C.prec) =
      ∀¹ (∼(ev₂ (below₂ C.prec)) ⋎ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0)) := by
  show ev₂ (∀¹ (∼(below₂ C.prec) ⋎ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0))) = _
  simp

theorem ev₂_belowAt₂_eq (n : ℕ) : ev₂ (belowAt₂ C n) = ∀¹ (ev₂ (belowBody₂ C n)) := by
  rw [belowAt₂_eq, ev₂_all₁]

theorem ev₂_belowBody₂_eq (n : ℕ) :
    ev₂ (belowBody₂ C n) =
      ∼(ev₂ (precAt₂ C.prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) (numAt n))) ⋎
        ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0) := by
  show ev₂ (∼(precAt₂ C.prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) (numAt n)) ⋎
    ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0)) = _
  simp

theorem ev₂_P₂_eq (n : ℕ) : ev₂ (P₂ C n) = ev₂ (belowAt₂ C n) ⋏ nxat n := by
  rw [P₂_eq, ev₂_and, ev₂_nxat]

theorem ev₂_precOrXat₂_eq (k n : ℕ) :
    ev₂ (precOrXat₂ C k n) =
      ev₂ (∼(precAt₂ C.prec (numAt k) (numAt n))) ⋎ xat k := by
  rw [precOrXat₂_eq, ev₂_or, ev₂_xat]

theorem neg_allXat₂ :
    ∼allXat₂ = ∃¹ ((((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∉& 0)) : Semiformula ℒₒᵣ ℕ ℕ 0 1) := rfl

/-! ### The evaluated premise computations -/

/-- **The `exs`-premise of `ev₂ (∼Prog₂)` at `n` is `ev₂ (P₂ C n)`.** -/
theorem inst_negProg₂_body (n : ℕ) :
    evInst₂.inst (ev₂ ((below₂ C.prec) ⋏ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∉& 0))) n
      = ev₂ (P₂ C n) := by
  rw [evInst₂_inst_ev, subst_negProg₂_body]

/-- **The `omegaRule`-premises of `ev₂ (belowAt₂ C n)`.** -/
theorem inst_belowBody₂ (n k : ℕ) :
    evInst₂.inst (ev₂ (belowBody₂ C n)) k = ev₂ (precOrXat₂ C k n) := by
  rw [evInst₂_inst_ev, subst_belowBody₂]

/-- **The `omegaRule`-premises of `∀ x, x ∈ X` are the atoms `k̄ ∈ X`.** -/
theorem inst_allXat₂_body (n : ℕ) :
    evInst₂.inst (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0) : Semiformula ℒₒᵣ ℕ ℕ 0 1) n
      = xat n := by
  rw [evInst₂_inst, subst_allXat₂_body]
  exact ev₂_xat n

/-! ### Head tags of the named members -/

@[simp] theorem head₂_xat (n : ℕ) : head₂ (xat n) = 4 := rfl

@[simp] theorem head₂_nxat (n : ℕ) : head₂ (nxat n) = 5 := rfl

@[simp] theorem head₂_allXat₂ : head₂ allXat₂ = 10 := rfl

@[simp] theorem head₂_neg_allXat₂ : head₂ (∼allXat₂) = 11 := rfl

@[simp] theorem head₂_TI₂ : head₂ (TI₂ C.prec) = 9 := rfl

@[simp] theorem head₂_P₂ (n : ℕ) : head₂ (P₂ C n) = 8 := rfl

@[simp] theorem head₂_precOrXat₂ (k n : ℕ) : head₂ (precOrXat₂ C k n) = 9 := rfl

@[simp] theorem head₂_belowAt₂ (n : ℕ) : head₂ (belowAt₂ C n) = 10 := by
  rw [belowAt₂_eq]; rfl

@[simp] theorem head₂_belowBody₂ (n : ℕ) : head₂ (belowBody₂ C n) = 9 := rfl

@[simp] theorem head₂_negProg₂ : head₂ (∼(Prog₂ C.prec)) = 11 := by
  rw [neg_Prog₂]; rfl

@[simp] theorem head₂_neg_ev₂_Prog₂ : head₂ (∼(ev₂ (Prog₂ C.prec))) = 11 := by
  rw [← ev₂_neg, head₂_ev₂, head₂_negProg₂]

/-! ### Set-freeness of the named members

The discriminator `head₂` cannot see: `precAt₂ C.prec y x` is an arbitrary
lifted formula and can have any head at all.  Set-freeness can. -/

@[simp] theorem not_setFree_xat (n : ℕ) : ¬ SetFree (xat n) := by simp [xat]

@[simp] theorem not_setFree_nxat (n : ℕ) : ¬ SetFree (nxat n) := by simp [nxat]

@[simp] theorem setFree_ev₂_precAt {n : ℕ} (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    SetFree (ev₂ (precAt₂ C.prec y x)) := by simp

@[simp] theorem setFree_ev₂_neg_precAt {n : ℕ} (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    SetFree (ev₂ (∼(precAt₂ C.prec y x))) := by simp

@[simp] theorem not_setFree_belowBody₂ (n : ℕ) : ¬ SetFree (belowBody₂ C n) := by
  simp [belowBody₂]

@[simp] theorem not_setFree_belowAt₂ (n : ℕ) : ¬ SetFree (belowAt₂ C n) := by
  rw [belowAt₂_eq]; simp

@[simp] theorem not_setFree_P₂ (n : ℕ) : ¬ SetFree (P₂ C n) := by
  rw [P₂_eq]; simp

@[simp] theorem not_setFree_precOrXat₂ (k n : ℕ) : ¬ SetFree (precOrXat₂ C k n) := by
  rw [precOrXat₂_eq]; simp

/-! ### Injectivity -/

@[simp] theorem xat_inj {k k' : ℕ} : xat k = xat k' ↔ k = k' := by
  constructor
  · intro h
    have h' : (numAt k : FirstOrder.SyntacticTerm ℒₒᵣ) = numAt k' := by
      injection h
    exact numAt_injective h'
  · rintro rfl; rfl

@[simp] theorem nxat_inj {k k' : ℕ} : nxat k = nxat k' ↔ k = k' := by
  constructor
  · intro h
    have h' : (numAt k : FirstOrder.SyntacticTerm ℒₒᵣ) = numAt k' := by
      injection h
    exact numAt_injective h'
  · rintro rfl; rfl

/-! ### Truth of the arithmetic member -/

theorem trueN₂_ev₂_neg_precAt (k n : ℕ) :
    TrueN₂ (ev₂ (∼(precAt₂ C.prec (numAt k) (numAt n)))) ↔ ¬ C.precN k n := by
  rw [trueN₂_ev₂]
  exact C.trueN₂_neg_precAt k n

theorem ev₂_precOrXat₂_inj {k n k' n' : ℕ}
    (h : ev₂ (precOrXat₂ C k n) = ev₂ (precOrXat₂ C k' n')) :
    k = k' ∧ (C.precN k n ↔ C.precN k' n') := by
  rw [ev₂_precOrXat₂_eq, ev₂_precOrXat₂_eq] at h
  obtain ⟨h₁, h₂⟩ := Semiformula.or_inj.mp h
  refine ⟨xat_inj.mp h₂, ?_⟩
  have := congrArg TrueN₂ h₁
  simp only [trueN₂_ev₂_neg_precAt] at this
  exact not_iff_not.mp (iff_of_eq this)

theorem ev₂_P₂_inj {n n' : ℕ} (h : ev₂ (P₂ C n) = ev₂ (P₂ C n')) : n = n' := by
  rw [ev₂_P₂_eq, ev₂_P₂_eq] at h
  exact nxat_inj.mp (Semiformula.and_inj.mp h).2

/-- Two `below` formulas with the same evaluation have the same predecessors. -/
theorem ev₂_belowAt₂_precN_iff {n n' : ℕ}
    (h : ev₂ (belowAt₂ C n) = ev₂ (belowAt₂ C n')) (k : ℕ) :
    C.precN k n ↔ C.precN k n' := by
  rw [ev₂_belowAt₂_eq, ev₂_belowAt₂_eq] at h
  have h' := Semiformula.all₁_inj.mp h
  have h'' := congrArg (fun χ : Semiproposition ℒₒᵣ 0 1 => evInst₂.inst χ k) h'
  simp only [inst_belowBody₂] at h''
  exact (ev₂_precOrXat₂_inj h'').2

/-! ### The class -/

/-- **The class `C`**: the shapes that can occur in a sequent of a cut-free
`ACA_∞`-derivation of `ev₂ (TI₂ C.prec)` under the evaluating instantiation.
It contains no set quantifier: every member is either set-free — and `SetFree`
rules out `∀²`/`∃²` — or one of the eight named shapes. -/
inductive InCe₂ {O : Type} [LinearOrder O] (C : CodedOrder₂ O) : Proposition ℒₒᵣ → Prop
  /-- every set-free formula -/
  | setFree {φ : Proposition ℒₒᵣ} : SetFree φ → InCe₂ C φ
  /-- `ev₂ (TI₂(≺, X))` -/
  | ti : InCe₂ C (ev₂ (TI₂ C.prec))
  /-- `ev₂ (∼Prog₂(≺, X))` -/
  | negProg : InCe₂ C (ev₂ (∼(Prog₂ C.prec)))
  /-- `∀ x, x ∈ X` — a fixed point of `ev₂` -/
  | allX : InCe₂ C allXat₂
  /-- `ev₂ (∀ y ≺ n̄, y ∈ X)` -/
  | belowNum (n : ℕ) : InCe₂ C (ev₂ (belowAt₂ C n))
  /-- `n̄ ∈ X` — a fixed point of `ev₂` -/
  | xatNum (n : ℕ) : InCe₂ C (xat n)
  /-- `n̄ ∉ X` — a fixed point of `ev₂` -/
  | nxatNum (n : ℕ) : InCe₂ C (nxat n)
  /-- `ev₂ (P₂ C n)` -/
  | pNum (n : ℕ) : InCe₂ C (ev₂ (P₂ C n))
  /-- `ev₂ (∼(k̄ ≺ n̄) ⋎ k̄ ∈ X)` -/
  | precOrX (k n : ℕ) : InCe₂ C (ev₂ (precOrXat₂ C k n))

/-- **The decision lemma**: membership inverted once and for all into a
disjunction of equations. -/
theorem InCe₂.exhaustive {φ : Proposition ℒₒᵣ} (h : InCe₂ C φ) :
    SetFree φ ∨
    φ = ev₂ (TI₂ C.prec) ∨
    φ = ev₂ (∼(Prog₂ C.prec)) ∨
    φ = allXat₂ ∨
    (∃ n, φ = ev₂ (belowAt₂ C n)) ∨
    (∃ n, φ = xat n) ∨
    (∃ n, φ = nxat n) ∨
    (∃ n, φ = ev₂ (P₂ C n)) ∨
    (∃ k n, φ = ev₂ (precOrXat₂ C k n)) := by
  cases h with
  | setFree hx => exact Or.inl hx
  | ti => exact Or.inr (Or.inl rfl)
  | negProg => exact Or.inr (Or.inr (Or.inl rfl))
  | allX => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | belowNum n => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))
  | xatNum n => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))
  | nxatNum n =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))))
  | pNum n =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))))
  | precOrX k n =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, n, rfl⟩)))))))

/-! ### Which member is it?

One lemma per constructor shape a *head* formula can have. -/

/-- The members with an `⋎` head. -/
theorem InCe₂.or_cases {φ ψ : Proposition ℒₒᵣ} (h : InCe₂ C (φ ⋎ ψ)) :
    SetFree (φ ⋎ ψ) ∨
    (φ = ev₂ (∼(Prog₂ C.prec)) ∧ ψ = allXat₂) ∨
    (∃ k n, φ = ev₂ (∼(precAt₂ C.prec (numAt k) (numAt n))) ∧ ψ = xat k) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact Or.inl hx
  · rw [ev₂_TI₂_eq] at he
    obtain ⟨rfl, rfl⟩ := Semiformula.or_inj.mp he
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · rw [ev₂_precOrXat₂_eq] at he
    obtain ⟨rfl, rfl⟩ := Semiformula.or_inj.mp he
    exact Or.inr (Or.inr ⟨k, n, rfl, rfl⟩)

/-- The members with an `⋏` head. -/
theorem InCe₂.and_cases {φ ψ : Proposition ℒₒᵣ} (h : InCe₂ C (φ ⋏ ψ)) :
    SetFree (φ ⋏ ψ) ∨
    (∃ n, φ = ev₂ (belowAt₂ C n) ∧ ψ = nxat n) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact Or.inl hx
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · rw [ev₂_P₂_eq] at he
    obtain ⟨rfl, rfl⟩ := Semiformula.and_inj.mp he
    exact Or.inr ⟨n, rfl, rfl⟩
  · exact absurd (congrArg head₂ he) (by simp)

/-- The members with a `∀¹` head. -/
theorem InCe₂.all_cases {φ : Semiproposition ℒₒᵣ 0 1} (h : InCe₂ C (∀¹ φ)) :
    SetFree (∀¹ φ) ∨
    φ = (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0) : Semiformula ℒₒᵣ ℕ ℕ 0 1) ∨
    (∃ n, φ = ev₂ (belowBody₂ C n)) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact Or.inl hx
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · rw [allXat₂_eq] at he
    obtain rfl := Semiformula.all₁_inj.mp he
    exact Or.inr (Or.inl rfl)
  · rw [ev₂_belowAt₂_eq] at he
    obtain rfl := Semiformula.all₁_inj.mp he
    exact Or.inr (Or.inr ⟨n, rfl⟩)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)

/-- The members with an `∃¹` head. -/
theorem InCe₂.exs_cases {φ : Semiproposition ℒₒᵣ 0 1} (h : InCe₂ C (∃¹ φ)) :
    SetFree (∃¹ φ) ∨
      φ = ev₂ ((below₂ C.prec) ⋏ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∉& 0)) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact Or.inl hx
  · exact absurd (congrArg head₂ he) (by simp)
  · rw [ev₂_negProg₂_eq] at he
    obtain rfl := Semiformula.exs₁_inj.mp he
    exact Or.inr rfl
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)

/-- The members with a `∀²` head: there are none. -/
theorem InCe₂.not_all₂ {φ : Semiproposition ℒₒᵣ 1 0} (h : InCe₂ C (∀² φ)) : False := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact absurd hx (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)

/-- The members with an `∃²` head: there are none. -/
theorem InCe₂.not_exs₂ {φ : Semiproposition ℒₒᵣ 1 0} (h : InCe₂ C (∃² φ)) : False := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact absurd hx (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · exact absurd (congrArg head₂ he) (by simp)

/-! ### The six shapes whose negation is not in the class

The general `identity` rule puts `φ` and `∼φ` in the same sequent.  These are
the members for which that cannot happen. -/

theorem not_inCe₂_neg_ev₂_TI₂ : ¬ InCe₂ C (∼(ev₂ (TI₂ C.prec))) := by
  intro h
  have he : ∼(ev₂ (TI₂ C.prec)) = ev₂ (Prog₂ C.prec) ⋏ ∼allXat₂ := by
    rw [ev₂_TI₂_eq]
    show ∼(ev₂ (∼(Prog₂ C.prec))) ⋏ ∼allXat₂ = _
    rw [ev₂_neg, Semiformula.neg_neg]
  rw [he] at h
  rcases h.and_cases with hx | ⟨n, -, h₂⟩
  · exact absurd hx (by simp)
  · exact absurd (congrArg head₂ h₂) (by simp)

theorem not_inCe₂_ev₂_Prog₂ : ¬ InCe₂ C (ev₂ (Prog₂ C.prec)) := by
  intro h
  rw [ev₂_Prog₂_eq] at h
  rcases h.all_cases with hx | he | ⟨n, he⟩
  · exact absurd hx (by simp)
  · exact absurd (congrArg head₂ he) (by simp)
  · rw [ev₂_belowBody₂_eq] at he
    have h₁ := (Semiformula.or_inj.mp he).1
    have h₂ : ev₂ (below₂ C.prec) =
        ev₂ (precAt₂ C.prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) (numAt n)) :=
      neg_injective h₁
    have : SetFree (ev₂ (below₂ C.prec)) := by rw [h₂]; simp
    exact absurd this (by simp)

theorem not_inCe₂_neg_allXat₂ : ¬ InCe₂ C (∼allXat₂) := by
  intro h
  rw [neg_allXat₂] at h
  rcases h.exs_cases with hx | he
  · exact absurd hx (by simp)
  · exact absurd (congrArg head₂ he) (by simp)

theorem not_inCe₂_neg_ev₂_belowAt₂ (n : ℕ) : ¬ InCe₂ C (∼(ev₂ (belowAt₂ C n))) := by
  intro h
  have he : ∼(ev₂ (belowAt₂ C n)) =
      ∃¹ (ev₂ (precAt₂ C.prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) (numAt n)) ⋏
        ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∉& 0)) := by
    rw [ev₂_belowAt₂_eq, ev₂_belowBody₂_eq]
    show ∃¹ (∼(∼(ev₂ (precAt₂ C.prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) (numAt n)))) ⋏
      ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∉& 0)) = _
    rw [Semiformula.neg_neg]
  rw [he] at h
  rcases h.exs_cases with hx | he'
  · exact absurd hx (by simp)
  · rw [ev₂_and] at he'
    have h₂ : ev₂ (precAt₂ C.prec (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) (numAt n))
        = ev₂ (below₂ C.prec) := (Semiformula.and_inj.mp he').1
    have : SetFree (ev₂ (below₂ C.prec)) := by rw [← h₂]; simp
    exact absurd this (by simp)

theorem not_inCe₂_neg_ev₂_P₂ (n : ℕ) : ¬ InCe₂ C (∼(ev₂ (P₂ C n))) := by
  intro h
  have he : ∼(ev₂ (P₂ C n)) = ∼(ev₂ (belowAt₂ C n)) ⋎ xat n := by
    rw [ev₂_P₂_eq]; rfl
  rw [he] at h
  rcases h.or_cases with hx | ⟨-, h₂⟩ | ⟨k, m, h₁, -⟩
  · exact absurd hx (by simp)
  · exact absurd (congrArg head₂ h₂) (by simp)
  · have h₂ : ev₂ (belowAt₂ C n) = ev₂ (precAt₂ C.prec (numAt k) (numAt m)) := by
      refine neg_injective ?_
      rw [h₁, ev₂_neg]
    have : SetFree (ev₂ (belowAt₂ C n)) := by rw [h₂]; simp
    exact absurd this (by simp)

theorem not_inCe₂_neg_ev₂_precOrXat₂ (k n : ℕ) :
    ¬ InCe₂ C (∼(ev₂ (precOrXat₂ C k n))) := by
  intro h
  have he : ∼(ev₂ (precOrXat₂ C k n)) =
      ev₂ (precAt₂ C.prec (numAt k) (numAt n)) ⋏ nxat k := by
    rw [ev₂_precOrXat₂_eq]
    show ∼(ev₂ (∼(precAt₂ C.prec (numAt k) (numAt n)))) ⋏ nxat k = _
    rw [ev₂_neg, Semiformula.neg_neg]
  rw [he] at h
  rcases h.and_cases with hx | ⟨m, h₁, -⟩
  · exact absurd hx (by simp)
  · have : SetFree (ev₂ (belowAt₂ C m)) := by rw [← h₁]; simp
    exact absurd this (by simp)

/-- **The general-identity lemma.**  If a formula and its negation are both in
the class, the formula is set-free or one of the two atoms. -/
theorem InCe₂.neg_cases {φ : Proposition ℒₒᵣ} (h : InCe₂ C φ) (hn : InCe₂ C (∼φ)) :
    SetFree φ ∨ (∃ n, φ = xat n) ∨ (∃ n, φ = nxat n) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact Or.inl hx
  · subst he; exact absurd hn not_inCe₂_neg_ev₂_TI₂
  · subst he
    rw [ev₂_neg, Semiformula.neg_neg] at hn
    exact absurd hn not_inCe₂_ev₂_Prog₂
  · subst he; exact absurd hn not_inCe₂_neg_allXat₂
  · subst he; exact absurd hn (not_inCe₂_neg_ev₂_belowAt₂ n)
  · exact Or.inr (Or.inl ⟨n, he⟩)
  · exact Or.inr (Or.inr ⟨n, he⟩)
  · subst he; exact absurd hn (not_inCe₂_neg_ev₂_P₂ n)
  · subst he; exact absurd hn (not_inCe₂_neg_ev₂_precOrXat₂ k n)

/-! ### Closure under premise-formation -/

/-- Set-freeness survives a numeral instance. -/
@[simp] theorem setFree_subst {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : SetFree (φ/[t]) ↔ SetFree φ :=
  setFree_rew _ φ

theorem setFree_inst {φ : Semiproposition ℒₒᵣ 0 1} (h : SetFree φ) (n : ℕ) :
    SetFree (evInst₂.inst φ n) := by
  rw [evInst₂_inst, setFree_ev₂, setFree_subst]
  exact h

/-- **`or`.** -/
theorem InCe₂.of_or {φ ψ : Proposition ℒₒᵣ} (h : InCe₂ C (φ ⋎ ψ)) :
    InCe₂ C φ ∧ InCe₂ C ψ := by
  rcases h.or_cases with hx | ⟨rfl, rfl⟩ | ⟨k, n, rfl, rfl⟩
  · exact ⟨.setFree (setFree_or _ _ |>.mp hx).1, .setFree (setFree_or _ _ |>.mp hx).2⟩
  · exact ⟨.negProg, .allX⟩
  · exact ⟨.setFree (setFree_ev₂_neg_precAt (numAt k) (numAt n)), .xatNum k⟩

/-- **`and`.** -/
theorem InCe₂.of_and {φ ψ : Proposition ℒₒᵣ} (h : InCe₂ C (φ ⋏ ψ)) :
    InCe₂ C φ ∧ InCe₂ C ψ := by
  rcases h.and_cases with hx | ⟨n, rfl, rfl⟩
  · exact ⟨.setFree (setFree_and _ _ |>.mp hx).1, .setFree (setFree_and _ _ |>.mp hx).2⟩
  · exact ⟨.belowNum n, .nxatNum n⟩

/-- **`omegaRule`.** -/
theorem InCe₂.of_all {φ : Semiproposition ℒₒᵣ 0 1} (h : InCe₂ C (∀¹ φ)) (n : ℕ) :
    InCe₂ C (evInst₂.inst φ n) := by
  rcases h.all_cases with hx | rfl | ⟨m, rfl⟩
  · exact .setFree (setFree_inst ((setFree_all₁ _).mp hx) n)
  · rw [inst_allXat₂_body]; exact .xatNum n
  · rw [inst_belowBody₂]; exact .precOrX n m

/-- **`exs`.** -/
theorem InCe₂.of_exs {φ : Semiproposition ℒₒᵣ 0 1} (h : InCe₂ C (∃¹ φ)) (n : ℕ) :
    InCe₂ C (evInst₂.inst φ n) := by
  rcases h.exs_cases with hx | rfl
  · exact .setFree (setFree_inst ((setFree_exs₁ _).mp hx) n)
  · rw [inst_negProg₂_body]; exact .pNum n

/-! ### Sequents -/

/-- A sequent all of whose formulas are in the class. -/
def InCeSeq₂ (C : CodedOrder₂ O) (Γ : SecondOrder.Sequent ℒₒᵣ) : Prop :=
  ∀ φ ∈ Γ, InCe₂ C φ

@[simp] theorem inCeSeq₂_nil : InCeSeq₂ C [] := by
  intro φ hφ
  simp at hφ

@[simp] theorem inCeSeq₂_cons {φ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ} :
    InCeSeq₂ C (φ :: Γ) ↔ InCe₂ C φ ∧ InCeSeq₂ C Γ := by
  constructor
  · intro h
    exact ⟨h φ List.mem_cons_self, fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)⟩
  · rintro ⟨hφ, hΓ⟩ ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact hφ
    · exact hΓ ψ hψ

/-- **`contraction`.** -/
theorem InCeSeq₂.of_subset {Γ Δ : SecondOrder.Sequent ℒₒᵣ} (h : InCeSeq₂ C Γ)
    (hs : Δ ⊆ Γ) : InCeSeq₂ C Δ := fun φ hφ => h φ (hs hφ)

/-- **`or`, at the level of sequents.** -/
theorem InCeSeq₂.of_or {φ ψ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (h : InCeSeq₂ C (φ ⋎ ψ :: Γ)) : InCeSeq₂ C (φ :: ψ :: Γ) := by
  rw [inCeSeq₂_cons] at h
  obtain ⟨hor, hΓ⟩ := h
  obtain ⟨h₁, h₂⟩ := hor.of_or
  simp [h₁, h₂, hΓ]

/-- **`and`, at the level of sequents**: both premises at once. -/
theorem InCeSeq₂.of_and {φ ψ : Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (h : InCeSeq₂ C (φ ⋏ ψ :: Γ)) : InCeSeq₂ C (φ :: Γ) ∧ InCeSeq₂ C (ψ :: Γ) := by
  rw [inCeSeq₂_cons] at h
  obtain ⟨hand, hΓ⟩ := h
  obtain ⟨h₁, h₂⟩ := hand.of_and
  exact ⟨by simp [h₁, hΓ], by simp [h₂, hΓ]⟩

/-- **`omegaRule`, at the level of sequents**: every premise, one per numeral. -/
theorem InCeSeq₂.of_all {φ : Semiproposition ℒₒᵣ 0 1} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (h : InCeSeq₂ C ((∀¹ φ) :: Γ)) (n : ℕ) : InCeSeq₂ C (evInst₂.inst φ n :: Γ) := by
  rw [inCeSeq₂_cons] at h
  obtain ⟨hall, hΓ⟩ := h
  simp [hall.of_all n, hΓ]

/-- **`exs`, at the level of sequents.** -/
theorem InCeSeq₂.of_exs {φ : Semiproposition ℒₒᵣ 0 1} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (h : InCeSeq₂ C ((∃¹ φ) :: Γ)) (n : ℕ) : InCeSeq₂ C (evInst₂.inst φ n :: Γ) := by
  rw [inCeSeq₂_cons] at h
  obtain ⟨hexs, hΓ⟩ := h
  simp [hexs.of_exs n, hΓ]

end OrdinalAnalysis.ACAOmega
