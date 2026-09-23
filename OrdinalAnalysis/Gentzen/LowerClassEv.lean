/-
  The class `C` of the boundedness lemma, lifted along the evaluator.

  The boundedness lemma is an induction over cut-free derivations
  `OmegaDerivable trueArithLits evInst 0 α Γ`.  Under `evInst` a quantifier is
  instantiated by *substituting the numeral and then evaluating*
  (`evInst.inst φ n = ev (φ/[n̄])`, `EvInst.lean`), so the premises the induction
  meets are never the raw formulas of `LowerClass.lean` but their images under
  `ev`.  The class the induction hypothesis has to be closed under is therefore
  not `InC` but the evaluated class `InCe` of this file.

  Nothing here is new mathematics.  `ev` is structural on the connectives and on
  the quantifiers (`ev_or`, `ev_and`, `ev_all`, `ev_exs` are all `rfl`), it is the
  identity on `X(n̄)` (`ev_Xat_numLX`) and on `X(#0)`, and it commutes with
  negation.  So every fact `LowerClass.lean` proves about `InC` transports:

  * the discriminator `head` is unchanged — `head_ev` is `rfl` in every case, and
    with it every "these two shapes cannot be equal" step is again the numeric
    clash of the pitfall notes;
  * the shapes of the evaluated members are the evaluated shapes of the members
    (`ev_TI_eq`, `ev_negProg_eq`, `ev_belowAt_eq`, `ev_P_eq`, `ev_precOrXat_eq`);
  * the premise computations of `LowerClass.lean` become premise computations for
    `evInst.inst` by one application of `evInst_inst_ev`, which is the congruence
    law `ev (ω ▹ ev φ) = ev (ω ▹ φ)` of `Evaluate.lean`.

  Two traps govern the spelling, both recorded in
  the design notes.

  * **`XLang` is a `def`.**  `simp`/`rw` refuse to enter a term containing
    `Sum.inr XRel.X : LX.Rel 1`, so — exactly as in `LowerSyntax.lean` and
    `Evaluate.lean` — every `X`-facing step is a `rw` at the head symbol `Xat`
    (never unfolding it) or a `congrArg (Semiformula.rel (Sum.inr XRel.X))`.
  * **There are two numerals.**  `LowerSyntax.numLX` is an `abbrev`,
    `StandardLX.numLX` a `def`; `LowerClass` speaks the first and
    `Evaluate`/`EvInst` the second.  They are definitionally equal but not
    interchangeable under `rw`/`simp`, whose matching is at *reducible*
    transparency: only the abbrev unfolds.  Every lemma of `EvInst` used below is
    therefore first restated as a `have` in the `LowerSyntax` spelling — `have`
    and `exact` unify at default transparency, where the two agree — and only
    then rewritten with.  For the same reason `StandardLX` is opened
    *selectively*: a wholesale `open` would make the bare name `numLX`
    ambiguous.
-/
import OrdinalAnalysis.Gentzen.LowerClass
import OrdinalAnalysis.Gentzen.EvInst
import OrdinalAnalysis.Gentzen.PrecStandard

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.LowerClassEv

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
-- `Gentzen.belowAt` (Jump.lean) is a *different* formula of the same name, and it
-- is visible here through the enclosing namespace, which no `open … hiding` can
-- suppress.  So `belowAt` is written `LowerClass.belowAt` throughout.
open OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.CodedNotation
open OrdinalAnalysis.Gentzen.LowerSyntax
open OrdinalAnalysis.Gentzen.LowerClass
open OrdinalAnalysis.Gentzen.Evaluate
open OrdinalAnalysis.Gentzen.EvInst
open OrdinalAnalysis.Gentzen.PrecStandard
open OrdinalAnalysis.Gentzen.StandardLX (TrueN trueArithLits stdLX)

variable {O : Type} [LinearOrder O] {C : CodedOrder O}

/-! ### (a) `ev` preserves the `X`-free closed class

`ev` rewrites inside atoms and touches nothing else: it keeps the relation
symbol of an atom, and `freeVariables_ev` says it keeps the free variables.  So
both halves of `IsXFreeClosed` are invariant. -/

/-- **`ev` neither creates nor destroys occurrences of `X`.**  Every clause is
structural; the atomic clause holds because `ev` keeps the relation symbol. -/
@[simp] theorem xFree_ev {n : ℕ} (φ : Semiformula LX ℕ n) : XFree (ev φ) ↔ XFree φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **`ev` preserves `X`-free closedness**, in both directions. -/
@[simp] theorem isXFreeClosed_ev (φ : Proposition LX) :
    IsXFreeClosed (ev φ) ↔ IsXFreeClosed φ := by
  simp only [IsXFreeClosed, xFree_ev, freeVariables_ev]

/-- **`omegaRule`-premises, evaluated.**  A numeral instance — in the evaluating
sense — of an `X`-free closed `∀¹` is `X`-free closed. -/
theorem isXFreeClosed_inst {φ : Semiformula LX ℕ 1} (h : IsXFreeClosed (∀¹ φ)) (n : ℕ) :
    IsXFreeClosed (evInst.inst φ n) := by
  have he : evInst.inst φ n = ev (φ/[numLX n]) := evInst_inst φ n
  rw [he, isXFreeClosed_ev]
  exact isXFreeClosed_all h n

/-- **`exs`-premises, evaluated.** -/
theorem isXFreeClosed_inst_exs {φ : Semiformula LX ℕ 1} (h : IsXFreeClosed (∃¹ φ)) (n : ℕ) :
    IsXFreeClosed (evInst.inst φ n) := by
  have he : evInst.inst φ n = ev (φ/[numLX n]) := evInst_inst φ n
  rw [he, isXFreeClosed_ev]
  exact isXFreeClosed_exs h n

/-! ### The discriminator survives evaluation

`ev` rewrites only inside atoms, so it leaves the outermost connective alone.
This one lemma carries the whole `head`-clash machinery of `LowerClass.lean`
over to the evaluated shapes. -/

/-- **`ev` does not change the head symbol.**  Each case is `rfl`: `ev` maps
every constructor to itself. -/
@[simp] theorem head_ev {n : ℕ} (φ : Semiformula LX ℕ n) : head (ev φ) = head φ := by
  induction φ using Semiformula.rec' <;> rfl

/-! ### (b) The evaluated shapes

The formulas the induction actually meets, each written as an equation whose
right-hand side is again built from the named members. -/

/-- The body of `LowerClass.belowAt C n`: `LowerClass.belowAt C n = ∀¹ (belowBody C n)` by
`LowerSyntax.subst_below_numeral`. -/
def belowBody (C : CodedOrder O) (n : ℕ) : Semiformula LX ℕ 1 :=
  ∼(precAt C.prec (#0 : Semiterm LX ℕ 1) (Semiterm.numeral n)) ⋎
    Xat (#0 : Semiterm LX ℕ 1)

/-- `LowerClass.belowAt C n` is the universal closure of `belowBody C n`. -/
theorem belowAt_eq_all (n : ℕ) : LowerClass.belowAt C n = ∀¹ (belowBody C n) :=
  LowerClass.belowAt_eq n

/-- The `omegaRule`-premises of `LowerClass.belowAt C n`, before evaluation. -/
theorem subst_belowBody (m n : ℕ) : (belowBody C n)/[numLX m] = precOrXat C m n :=
  LowerClass.subst_belowAt_body m n

/-- `X(n̄)` is a fixed point of `ev` — restated in the `LowerSyntax` numeral, the
spelling every `LowerClass` shape uses. -/
@[simp] theorem ev_Xat_num (n : ℕ) : ev (Xat (numLX n)) = Xat (numLX n) :=
  Evaluate.ev_Xat_numLX n

/-- So is `∼X(n̄)`.  Deliberately *not* `@[simp]`: `ev_neg` is, so its left-hand
side is not in simp-normal form and the lemma would silently never fire (the
trap recorded for the premise computations of `LowerClass.lean`).  `simp` reaches
the same result through `ev_neg` and `ev_Xat_num`. -/
theorem ev_neg_Xat_num (n : ℕ) : ev (∼(Xat (numLX n))) = ∼(Xat (numLX n)) := by
  rw [ev_neg, ev_Xat_num]

/-- **`∀ x, X x` is a fixed point of `ev`**: its only term is the bound variable
`#0`, which `evT` leaves alone. -/
@[simp] theorem ev_allXat : ev allXat = allXat := by
  rw [allXat_eq, ev_all, ev_Xat, evT_bvar]

/-- `ev (TI(≺)) = ev (∼Prog(≺)) ⋎ ∀ x X x`. -/
theorem ev_TI_eq : ev (TI C.prec) = ev (∼(Prog C.prec)) ⋎ allXat := by
  rw [TI_eq, ev_or, ev_allXat]

/-- `ev (∼Prog(≺))` is an `∃¹` whose body is the evaluated body of `∼Prog(≺)`. -/
theorem ev_negProg_eq :
    ev (∼(Prog C.prec)) =
      ∃¹ (ev ((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LX ℕ 1)))) := by
  rw [negProg_eq, ev_exs]

/-- The head of `ev (∼Prog(≺))`, stated on the shape `simp` actually produces.

`ev_neg` is a `simp` lemma, so `simp` turns `ev (∼(Prog C.prec))` into
`∼(ev (Prog C.prec))` before `head_ev` can fire, and `head` cannot reduce a
negation of an opaque formula.  Stating the tag on the *normalised* term is what
keeps every head-clash in `(d)` a one-line `simp`. -/
@[simp] theorem head_neg_ev_Prog : head (∼(ev (Prog C.prec))) = 7 := by
  have h : ∼(ev (Prog C.prec)) = ev (∼(Prog C.prec)) := (ev_neg _).symm
  rw [h, ev_negProg_eq]
  simp

/-- `ev (LowerClass.belowAt C n)` is a `∀¹` whose body is the evaluated `belowBody C n`. -/
theorem ev_belowAt_eq (n : ℕ) : ev (LowerClass.belowAt C n) = ∀¹ (ev (belowBody C n)) := by
  rw [belowAt_eq_all, ev_all]

/-- `ev (P C n) = ev (∀ y ≺ n̄, X y) ⋏ ∼X(n̄)`. -/
theorem ev_P_eq (n : ℕ) : ev (P C n) = ev (LowerClass.belowAt C n) ⋏ ∼(Xat (numLX n)) := by
  rw [P_eq, ev_and, ev_neg, ev_Xat_num]

/-- `ev (precOrXat C k n) = ev (∼(k̄ ≺ n̄)) ⋎ X(k̄)`. -/
theorem ev_precOrXat_eq (k n : ℕ) :
    ev (precOrXat C k n) = ev (∼(precAt C.prec (numLX k) (numLX n))) ⋎ Xat (numLX k) := by
  rw [precOrXat_eq, ev_or, ev_Xat_num]

/-! ### The evaluated premise computations

Each is one application of `evInst_inst_ev` — "instantiating an already
evaluated body is evaluating the raw instance" — followed by the corresponding
substitution normal form of `LowerClass.lean`.  The `have`s are what bridge the
two spellings of the numeral; see the header. -/

/-- **The `exs`-premise of `ev (∼Prog(≺))` at `n` is `ev (P C n)`.** -/
theorem inst_negProg_body (n : ℕ) :
    evInst.inst (ev ((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LX ℕ 1)))) n = ev (P C n) := by
  have he : evInst.inst (ev ((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LX ℕ 1)))) n
      = ev (((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LX ℕ 1)))/[numLX n]) :=
    evInst_inst_ev _ n
  rw [he, subst_negProg_body]

/-- **The `omegaRule`-premises of `ev (LowerClass.belowAt C n)` are the `ev (precOrXat C k n)`.** -/
theorem inst_belowBody (n k : ℕ) :
    evInst.inst (ev (belowBody C n)) k = ev (precOrXat C k n) := by
  have he : evInst.inst (ev (belowBody C n)) k = ev ((belowBody C n)/[numLX k]) :=
    evInst_inst_ev _ k
  rw [he, subst_belowBody]

/-- **The `omegaRule`-premises of `∀ x, X x` are the atoms `X(n̄)`** — already
evaluated, since a numeral is its own evaluation. -/
theorem inst_allXat_body (n : ℕ) :
    evInst.inst (Xat (#0 : Semiterm LX ℕ 1)) n = Xat (numLX n) := by
  have he : evInst.inst (Xat (#0 : Semiterm LX ℕ 1)) n
      = ev ((Xat (#0 : Semiterm LX ℕ 1))/[numLX n]) :=
    evInst_inst _ n
  rw [he, subst_allXat_body, ev_Xat_num]

/-! ### (e) The evaluated arithmetic piece

The left disjunct of `ev (precOrXat C k n)`.  It is the only `X`-free member among
the named shapes, and the `or` case of the boundedness induction has to decide
its truth: the induction hypothesis says every `X`-free member of the sequent is
*false* in `ℕ`, so meeting `ev (∼(k̄ ≺ n̄))` there forces `k ≺ n`. -/

/-- `ev (∼(k̄ ≺ n̄))` is `X`-free and closed. -/
theorem isXFreeClosed_ev_neg_precAt (k n : ℕ) :
    IsXFreeClosed (ev (∼(precAt C.prec (numLX k) (numLX n)))) :=
  (isXFreeClosed_ev _).mpr (isXFreeClosed_neg_precAt k n)

/-- **`ev (∼(k̄ ≺ n̄))` is true in `ℕ` exactly when `k ≺ n` fails.**  `ev`
preserves truth (`trueN_ev`), `TrueN` of a negation is the negation of `TrueN`,
and `PrecStandard.eval_precAt_numeral` reads the atom off as `precN`. -/
theorem trueN_ev_neg_precAt (k n : ℕ) :
    TrueN (ev (∼(precAt C.prec (numLX k) (numLX n)))) ↔ ¬ C.precN k n := by
  rw [trueN_ev, StandardLX.trueN_neg]
  exact not_congr (C.eval_precAt_numeral (fun _ => False) k n (fun _ => 0))

/-! ### (c) The evaluated class

The image of `LowerClass.InC` under `ev`, written out as nine shapes rather than
as `∃ ψ, InC ψ ∧ φ = ev ψ`: the three shapes that `ev` fixes on the nose
(`allXat`, `X(n̄)`, `∼X(n̄)`) are recorded in their fixed form, so that no later
proof has to strip an `ev` from them. -/

/-- **The evaluated class**: the shapes that can occur in a sequent of a
cut-free ω-derivation of `ev (TI C.prec)` in the *evaluating* calculus. -/
inductive InCe {O : Type} [LinearOrder O] (C : CodedOrder O) : Proposition LX → Prop
  /-- every closed `X`-free formula -/
  | xfree {φ : Proposition LX} : IsXFreeClosed φ → InCe C φ
  /-- `ev (TI(≺))` -/
  | ti : InCe C (ev (TI C.prec))
  /-- `ev (∼Prog(≺))` -/
  | negProg : InCe C (ev (∼(Prog C.prec)))
  /-- `∀ x, X x` — a fixed point of `ev` -/
  | allX : InCe C allXat
  /-- `ev (∀ y ≺ n̄, X y)` -/
  | belowNum (n : ℕ) : InCe C (ev (LowerClass.belowAt C n))
  /-- `X(n̄)` — a fixed point of `ev` -/
  | xatNum (n : ℕ) : InCe C (Xat (numLX n))
  /-- `∼X(n̄)` — a fixed point of `ev` -/
  | negXatNum (n : ℕ) : InCe C (∼(Xat (numLX n)))
  /-- `ev (P C n)` -/
  | pNum (n : ℕ) : InCe C (ev (P C n))
  /-- `ev (∼(k̄ ≺ n̄) ⋎ X(k̄))` -/
  | precOrX (k n : ℕ) : InCe C (ev (precOrXat C k n))

/-- **The decision lemma**, as in `LowerClass.InC.exhaustive`: membership
inverted once and for all into a disjunction of equations. -/
theorem InCe.exhaustive {φ : Proposition LX} (h : InCe C φ) :
    IsXFreeClosed φ ∨
    φ = ev (TI C.prec) ∨
    φ = ev (∼(Prog C.prec)) ∨
    φ = allXat ∨
    (∃ n, φ = ev (LowerClass.belowAt C n)) ∨
    (∃ n, φ = Xat (numLX n)) ∨
    (∃ n, φ = ∼(Xat (numLX n))) ∨
    (∃ n, φ = ev (P C n)) ∨
    (∃ k n, φ = ev (precOrXat C k n)) := by
  cases h with
  | xfree hx => exact Or.inl hx
  | ti => exact Or.inr (Or.inl rfl)
  | negProg => exact Or.inr (Or.inr (Or.inl rfl))
  | allX => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | belowNum n => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))
  | xatNum n => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))
  | negXatNum n =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))))
  | pNum n =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))))
  | precOrX k n =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, n, rfl⟩)))))))

/-- Every member of the evaluated class is closed: `ev` does not move free
variables. -/
theorem InCe.freeVariables_eq_empty {φ : Proposition LX} (h : InCe C φ) :
    φ.freeVariables = ∅ := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact hx.2
  · rw [he, freeVariables_ev]; exact freeVariables_TI C.freeVariables_prec
  · rw [he, freeVariables_ev]; simp
  · rw [he]; simp
  · rw [he, freeVariables_ev]; simp
  · rw [he]; simp
  · rw [he]; simp
  · rw [he, freeVariables_ev]; simp
  · rw [he, freeVariables_ev]; simp

/-! ### (d) Which member is it?

One lemma per connective shape a *head* formula can have.  Every impossible case
is a clash of `head`, which `head_ev` reduces to the clash `LowerClass.lean`
already settles; every possible case is `or_inj`/`and_inj`/`all_inj`/`exs_inj`
applied to the corresponding evaluated shape of (b). -/

/-- The members of the evaluated class with an `⋎` head. -/
theorem InCe.or_cases {φ ψ : Proposition LX} (h : InCe C (φ ⋎ ψ)) :
    IsXFreeClosed (φ ⋎ ψ) ∨
    (φ = ev (∼(Prog C.prec)) ∧ ψ = allXat) ∨
    (∃ k n, φ = ev (∼(precAt C.prec (numLX k) (numLX n))) ∧ ψ = Xat (numLX k)) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact Or.inl hx
  · rw [ev_TI_eq] at he
    obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp he
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · rw [ev_precOrXat_eq] at he
    obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp he
    exact Or.inr (Or.inr ⟨k, n, rfl, rfl⟩)

/-- The members of the evaluated class with an `⋏` head. -/
theorem InCe.and_cases {φ ψ : Proposition LX} (h : InCe C (φ ⋏ ψ)) :
    IsXFreeClosed (φ ⋏ ψ) ∨
    (∃ n, φ = ev (LowerClass.belowAt C n) ∧ ψ = ∼(Xat (numLX n))) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact Or.inl hx
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · rw [ev_P_eq] at he
    obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp he
    exact Or.inr ⟨n, rfl, rfl⟩
  · exact absurd (congrArg head he) (by simp)

/-- The members of the evaluated class with a `∀¹` head. -/
theorem InCe.all_cases {φ : Semiformula LX ℕ 1} (h : InCe C (∀¹ φ)) :
    IsXFreeClosed (∀¹ φ) ∨ φ = Xat (#0 : Semiterm LX ℕ 1) ∨
      (∃ n, φ = ev (belowBody C n)) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact Or.inl hx
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · rw [allXat_eq] at he
    obtain rfl := (Semiformula.all_inj _ _).mp he
    exact Or.inr (Or.inl rfl)
  · rw [ev_belowAt_eq] at he
    obtain rfl := (Semiformula.all_inj _ _).mp he
    exact Or.inr (Or.inr ⟨n, rfl⟩)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)

/-- The members of the evaluated class with an `∃¹` head. -/
theorem InCe.exs_cases {φ : Semiformula LX ℕ 1} (h : InCe C (∃¹ φ)) :
    IsXFreeClosed (∃¹ φ) ∨
      φ = ev ((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LX ℕ 1))) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨k, n, he⟩
  · exact Or.inl hx
  · exact absurd (congrArg head he) (by simp)
  · rw [ev_negProg_eq] at he
    obtain rfl := (Semiformula.exs_inj _ _).mp he
    exact Or.inr rfl
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)

/-- The members of the evaluated class that are atoms. -/
theorem InCe.rel_cases {k : ℕ} (rl : LX.Rel k) (v : Fin k → SyntacticTerm LX)
    (h : InCe C (Semiformula.rel rl v)) :
    IsXFreeClosed (Semiformula.rel rl v) ∨
      (∃ n, Semiformula.rel rl v = Xat (numLX n)) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨m, n, he⟩
  · exact Or.inl hx
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact Or.inr ⟨n, he⟩
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)

/-- The members of the evaluated class that are negated atoms. -/
theorem InCe.nrel_cases {k : ℕ} (rl : LX.Rel k) (v : Fin k → SyntacticTerm LX)
    (h : InCe C (Semiformula.nrel rl v)) :
    IsXFreeClosed (Semiformula.nrel rl v) ∨
      (∃ n, Semiformula.nrel rl v = ∼(Xat (numLX n))) := by
  rcases h.exhaustive with
    hx | he | he | he | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨n, he⟩ | ⟨m, n, he⟩
  · exact Or.inl hx
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)
  · exact Or.inr ⟨n, he⟩
  · exact absurd (congrArg head he) (by simp)
  · exact absurd (congrArg head he) (by simp)

/-! ### Closure under premise-formation

One lemma per rule of `Omega/Calculus.lean` that can have a member of the
evaluated class as its principal formula, in the form the boundedness induction
consumes. -/

/-- **`or`.** -/
theorem InCe.of_or {φ ψ : Proposition LX} (h : InCe C (φ ⋎ ψ)) : InCe C φ ∧ InCe C ψ := by
  rcases h.or_cases with hx | ⟨rfl, rfl⟩ | ⟨k, n, rfl, rfl⟩
  · exact ⟨.xfree (isXFreeClosed_or.mp hx).1, .xfree (isXFreeClosed_or.mp hx).2⟩
  · exact ⟨.negProg, .allX⟩
  · exact ⟨.xfree (isXFreeClosed_ev_neg_precAt k n), .xatNum k⟩

/-- **`and`.** -/
theorem InCe.of_and {φ ψ : Proposition LX} (h : InCe C (φ ⋏ ψ)) : InCe C φ ∧ InCe C ψ := by
  rcases h.and_cases with hx | ⟨n, rfl, rfl⟩
  · exact ⟨.xfree (isXFreeClosed_and.mp hx).1, .xfree (isXFreeClosed_and.mp hx).2⟩
  · exact ⟨.belowNum n, .negXatNum n⟩

/-- **`omegaRule`.**  Every *evaluated* numeral instance of a universally
quantified member of the class is a member of the class. -/
theorem InCe.of_all {φ : Semiformula LX ℕ 1} (h : InCe C (∀¹ φ)) (n : ℕ) :
    InCe C (evInst.inst φ n) := by
  rcases h.all_cases with hx | rfl | ⟨m, rfl⟩
  · exact .xfree (isXFreeClosed_inst hx n)
  · rw [inst_allXat_body]
    exact .xatNum n
  · rw [inst_belowBody]
    exact .precOrX n m

/-- **`exs`.** -/
theorem InCe.of_exs {φ : Semiformula LX ℕ 1} (h : InCe C (∃¹ φ)) (n : ℕ) :
    InCe C (evInst.inst φ n) := by
  rcases h.exs_cases with hx | rfl
  · exact .xfree (isXFreeClosed_inst_exs hx n)
  · rw [inst_negProg_body]
    exact .pNum n

/-! ### Sequents -/

/-- A sequent all of whose formulas are in the evaluated class. -/
def InCeSeq (C : CodedOrder O) (Γ : Sequent LX) : Prop := ∀ φ ∈ Γ, InCe C φ

@[simp] theorem inCeSeq_nil : InCeSeq C [] := by
  intro φ hφ
  simp at hφ

@[simp] theorem inCeSeq_cons {φ : Proposition LX} {Γ : Sequent LX} :
    InCeSeq C (φ :: Γ) ↔ InCe C φ ∧ InCeSeq C Γ := by
  constructor
  · intro h
    exact ⟨h φ List.mem_cons_self, fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)⟩
  · rintro ⟨hφ, hΓ⟩ ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact hφ
    · exact hΓ ψ hψ

@[simp] theorem inCeSeq_append {Γ Δ : Sequent LX} :
    InCeSeq C (Γ ++ Δ) ↔ InCeSeq C Γ ∧ InCeSeq C Δ := by
  constructor
  · intro h
    exact ⟨fun φ hφ => h φ (List.mem_append_left _ hφ),
      fun φ hφ => h φ (List.mem_append_right _ hφ)⟩
  · rintro ⟨hΓ, hΔ⟩ φ hφ
    rcases List.mem_append.mp hφ with hφ | hφ
    · exact hΓ φ hφ
    · exact hΔ φ hφ

/-- **`contraction`.** -/
theorem InCeSeq.of_subset {Γ Δ : Sequent LX} (h : InCeSeq C Γ) (hs : Δ ⊆ Γ) : InCeSeq C Δ :=
  fun φ hφ => h φ (hs hφ)

/-- **`or`, at the level of sequents.** -/
theorem InCeSeq.of_or {φ ψ : Proposition LX} {Γ : Sequent LX}
    (h : InCeSeq C (φ ⋎ ψ :: Γ)) : InCeSeq C (φ :: ψ :: Γ) := by
  rw [inCeSeq_cons] at h
  obtain ⟨hor, hΓ⟩ := h
  obtain ⟨h₁, h₂⟩ := hor.of_or
  simp [h₁, h₂, hΓ]

/-- **`and`, at the level of sequents**: both premises at once. -/
theorem InCeSeq.of_and {φ ψ : Proposition LX} {Γ : Sequent LX}
    (h : InCeSeq C (φ ⋏ ψ :: Γ)) : InCeSeq C (φ :: Γ) ∧ InCeSeq C (ψ :: Γ) := by
  rw [inCeSeq_cons] at h
  obtain ⟨hand, hΓ⟩ := h
  obtain ⟨h₁, h₂⟩ := hand.of_and
  exact ⟨by simp [h₁, hΓ], by simp [h₂, hΓ]⟩

/-- **`omegaRule`, at the level of sequents**: every premise, one per numeral. -/
theorem InCeSeq.of_all {φ : Semiformula LX ℕ 1} {Γ : Sequent LX}
    (h : InCeSeq C ((∀¹ φ) :: Γ)) (n : ℕ) : InCeSeq C (evInst.inst φ n :: Γ) := by
  rw [inCeSeq_cons] at h
  obtain ⟨hall, hΓ⟩ := h
  simp [hall.of_all n, hΓ]

/-- **`exs`, at the level of sequents.** -/
theorem InCeSeq.of_exs {φ : Semiformula LX ℕ 1} {Γ : Sequent LX}
    (h : InCeSeq C ((∃¹ φ) :: Γ)) (n : ℕ) : InCeSeq C (evInst.inst φ n :: Γ) := by
  rw [inCeSeq_cons] at h
  obtain ⟨hexs, hΓ⟩ := h
  simp [hexs.of_exs n, hΓ]

/-- Every formula of a sequent in the evaluated class is closed. -/
theorem InCeSeq.freeVariables_eq_empty {Γ : Sequent LX} (h : InCeSeq C Γ)
    {φ : Proposition LX} (hφ : φ ∈ Γ) : φ.freeVariables = ∅ :=
  (h φ hφ).freeVariables_eq_empty

/-! ### No evaluated named shape other than `ev (∼(k̄ ≺ n̄))` is `X`-free

The hypothesis-separation the boundedness lemma needs, transported by
`isXFreeClosed_ev`. -/

theorem not_isXFreeClosed_ev_TI : ¬ IsXFreeClosed (ev (TI C.prec)) := by
  rw [isXFreeClosed_ev]
  exact not_isXFreeClosed_TI

theorem not_isXFreeClosed_ev_negProg :
    ¬ IsXFreeClosed (ev (∼(Prog C.prec))) := by
  rw [isXFreeClosed_ev]
  exact not_isXFreeClosed_negProg

theorem not_isXFreeClosed_ev_belowAt (n : ℕ) :
    ¬ IsXFreeClosed (ev (LowerClass.belowAt C n)) := by
  rw [isXFreeClosed_ev]
  exact not_isXFreeClosed_belowAt n

theorem not_isXFreeClosed_ev_P (n : ℕ) : ¬ IsXFreeClosed (ev (P C n)) := by
  rw [isXFreeClosed_ev]
  exact not_isXFreeClosed_P n

theorem not_isXFreeClosed_ev_precOrXat (k n : ℕ) :
    ¬ IsXFreeClosed (ev (precOrXat C k n)) := by
  rw [isXFreeClosed_ev]
  exact not_isXFreeClosed_precOrXat k n

end OrdinalAnalysis.Gentzen.LowerClassEv
