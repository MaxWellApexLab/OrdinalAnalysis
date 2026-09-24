/-
  The boundedness lemma for the ramified calculus `RA_∞`.

  This is `Gentzen/Boundedness.lean` transposed from the finitary cut rank
  `r : ℕ` and the language `LX` to the ordinal cut rank `ρ : Gamma0Note` and
  `LRA`, with the two new rule cases (Pr)/(Pr⁻) added and disposed of by
  `Ramified/LowerClass.lean`'s `not_inCe_memAt`/`not_inCe_nmemAt`.  The
  two-parameter reading is unchanged:

  * `X(n̄)` reads as "the ordinal coded by `n` is below `δ`";
  * `∼X(n̄)` reads as "the ordinal coded by `n` is **not** below `γ`";
  * `∼Prog(≺)` has **no** reading at all;
  * the remaining named members of the class read as their positive content
    bounded by `δ`.

  The lemma says: for every `γ`, a cut-free derivation of height `α` of a
  class sequent has a member true under the reading `(γ, γ ⊕ ω^α)`.  Every
  propositional and quantifier case is exactly Gentzen's; the ordinal
  arithmetic (`bump_le`, `nadd_omegaPow_le`, `le_of_forall_lt_lt`) is generic
  in `[OrdinalNotation O]` and is reused verbatim from `Gentzen.Boundedness`
  and `Gentzen`, not reproved.

  Three cases are new relative to the first-order proof.

  * **`identity` stays atomic**, unlike the second-order port: D2's calculus
    (`Ramified/Calculus.lean`) keeps atomic identity — there is no
    formula-for-variable substitution anywhere in it — so this case is
    `Gentzen`'s `InCe.rel_cases`/`nrel_cases` argument unchanged, not the
    second-order file's general `good₂_or_good₂_neg`.

  * **`pr`/`npr` are vacuous.**  A (Pr) inference's conclusion is the bare
    atom `n̄ ∈̇_ν ā`, and `not_inCe_memAt` (`not_inCe_nmemAt` for (Pr⁻)) says
    no such atom is ever a member of the class — so the hypothesis
    `InCeSeq C (memAt … :: Γ)` is already contradictory, and the case is
    discharged without touching the rule's premise at all.  This is the
    entire cash value of `SetFree`/`Ramified/Rank.lean`'s design: a cut-free
    derivation of a class sequent never uses a predicator rule.

  * **`cut` is impossible at rank `0`.**  `Gamma0Note` has no `OrderBot`
    instance in scope, so `rank φ < (0 : Gamma0Note)` is refuted directly
    from `Gamma0Note.repr` landing in `Ordinal`, where `0` already is `⊥`.
-/
import OrdinalAnalysis.Ramified.LowerClass
import OrdinalAnalysis.Gentzen.Boundedness

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/- See `Ramified/LowerClass.lean`: `numAtR` is a plain `def`, and
`numAtR_zero` is a `simp` lemma that fights every other fact about `numAtR`
used below. -/
attribute [-simp] numAtR_zero

variable {O : Type} [LinearOrder O] {C : CodedOrderR O}

/-! ### `Gamma0Note` has no element below `0`

Needed for the `cut` case: `rank φ < (0 : Gamma0Note)` must be false.
`Gamma0Note.repr` embeds into `Ordinal`, order-reflectingly, and `0`
there already is `⊥`. -/

private theorem not_lt_zero_gamma0 (x : Gamma0Note) : ¬ x < (0 : Gamma0Note) := by
  rw [Gamma0Note.lt_def, Gamma0Note.repr_zero]
  exact not_lt_bot

/-! ### Ordinal facts

Reused verbatim from `Gentzen.Boundedness`: both are generic in
`[OrdinalNotation O]` and know nothing about the syntax. -/

theorem bump_le [WellFoundedLT O] [OrdinalNotation O] {γ β α : O} (h : β < α) :
    OrdinalNotation.nadd
        (OrdinalNotation.succ (OrdinalNotation.nadd γ (OrdinalNotation.omegaPow β)))
        (OrdinalNotation.omegaPow β)
      ≤ OrdinalNotation.nadd γ (OrdinalNotation.omegaPow α) :=
  Gentzen.Boundedness.bump_le h

theorem nadd_omegaPow_le [WellFoundedLT O] [OrdinalNotation O] {γ β α : O} (h : β < α) :
    OrdinalNotation.nadd γ (OrdinalNotation.omegaPow β) ≤
      OrdinalNotation.nadd γ (OrdinalNotation.omegaPow α) :=
  Gentzen.Boundedness.nadd_omegaPow_le h

/-! ### The reading of a code -/

/-- The ordinal coded by `n`, if any, is below `δ`. -/
def Small (C : CodedOrderR O) (δ : O) (n : ℕ) : Prop := ∀ o : O, C.code o = n → o < δ

/-- Every `≺`-predecessor of `n` is small. -/
def PredsSmall (C : CodedOrderR O) (δ : O) (n : ℕ) : Prop := ∀ k : ℕ, C.precN k n → Small C δ k

theorem Small.mono {δ δ' : O} {n : ℕ} (h : δ ≤ δ') (hs : Small C δ n) : Small C δ' n :=
  fun o ho => lt_of_lt_of_le (hs o ho) h

theorem PredsSmall.mono {δ δ' : O} {n : ℕ} (h : δ ≤ δ') (hs : PredsSmall C δ n) :
    PredsSmall C δ' n :=
  fun k hk => (hs k hk).mono h

theorem PredsSmall.congr {δ : O} {n n' : ℕ} (hiff : ∀ k, C.precN k n ↔ C.precN k n')
    (hs : PredsSmall C δ n') : PredsSmall C δ n :=
  fun k hk => hs k ((hiff k).mp hk)

/-- A number all of whose predecessors are below `δ` is at most `δ`:
linearity. -/
theorem le_of_predsSmall {δ : O} {n : ℕ} (h : PredsSmall C δ n) {o : O}
    (ho : C.code o = n) : o ≤ δ := by
  refine Gentzen.le_of_forall_lt_lt (fun o' ho' => ?_)
  refine h (C.code o') ?_ o' rfl
  rw [← ho]
  exact C.precN_code_of_lt ho'

theorem Small.of_predsSmall [WellFoundedLT O] [OrdinalNotation O] {δ : O} {n : ℕ}
    (h : PredsSmall C δ n) : Small C (OrdinalNotation.succ δ) n :=
  fun _ ho => OrdinalNotation.lt_succ_of_le (le_of_predsSmall h ho)

theorem Small.of_predsSmall_lt {δ δ' : O} {n : ℕ} (h : PredsSmall C δ n) (hδ : δ < δ') :
    Small C δ' n :=
  fun _ ho => lt_of_le_of_lt (le_of_predsSmall h ho) hδ

/-! ### The reading of the class -/

/-- The reading of a class member under the bounds `(γ, δ)`; `∼Prog(≺)` has
none. -/
def GoodR (C : CodedOrderR O) (γ δ : O) (φ : Proposition LRA) : Prop :=
  (IsXFreeClosed φ ∧ TrueNR φ) ∨
  (∃ n, φ = Xat (numAtR n : Semiterm LRA ℕ 0) ∧ Small C δ n) ∨
  (∃ n, φ = ∼(Xat (numAtR n : Semiterm LRA ℕ 0)) ∧ ¬ Small C γ n) ∨
  (∃ n, φ = evR (belowAt C n) ∧ PredsSmall C δ n) ∨
  (∃ n, φ = evR (P C n) ∧ ¬ Small C γ n ∧ PredsSmall C δ n) ∨
  (∃ k n, φ = evR (precOrXat C k n) ∧ (¬ C.precN k n ∨ Small C δ k)) ∨
  (φ = allXat ∧ ∀ o : O, o < δ) ∨
  (φ = evR (TIR C.prec) ∧ ∀ o : O, o < δ)

/-- Some member of the sequent is good. -/
def Bound (C : CodedOrderR O) (γ δ : O) (Γ : Sequent LRA) : Prop := ∃ φ ∈ Γ, GoodR C γ δ φ

variable {γ δ : O} {φ : Proposition LRA}

theorem GoodR.xfree (hx : IsXFreeClosed φ) (ht : TrueNR φ) : GoodR C γ δ φ := Or.inl ⟨hx, ht⟩

theorem GoodR.xat {n : ℕ} (h : φ = Xat (numAtR n : Semiterm LRA ℕ 0)) (hs : Small C δ n) :
    GoodR C γ δ φ := Or.inr (Or.inl ⟨n, h, hs⟩)

theorem GoodR.negXat {n : ℕ} (h : φ = ∼(Xat (numAtR n : Semiterm LRA ℕ 0))) (hs : ¬ Small C γ n) :
    GoodR C γ δ φ := Or.inr (Or.inr (Or.inl ⟨n, h, hs⟩))

theorem GoodR.belowAt {n : ℕ} (h : φ = evR (belowAt C n)) (hp : PredsSmall C δ n) :
    GoodR C γ δ φ := Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h, hp⟩)))

theorem GoodR.pn {n : ℕ} (h : φ = evR (P C n)) (hs : ¬ Small C γ n) (hp : PredsSmall C δ n) :
    GoodR C γ δ φ := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h, hs, hp⟩))))

theorem GoodR.precOrXat {k n : ℕ} (h : φ = evR (precOrXat C k n))
    (hd : ¬ C.precN k n ∨ Small C δ k) : GoodR C γ δ φ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, n, h, hd⟩)))))

theorem GoodR.allXat (h : φ = allXat) (hall : ∀ o : O, o < δ) : GoodR C γ δ φ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hall⟩))))))

theorem GoodR.ti (h : φ = evR (TIR C.prec)) (hall : ∀ o : O, o < δ) : GoodR C γ δ φ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hall⟩))))))

/-- Lowering `γ` and raising `δ` keeps a reading good. -/
theorem GoodR.mono {γ' δ' : O} (hγ : γ ≤ γ') (hδ : δ ≤ δ') (hg : GoodR C γ' δ φ) :
    GoodR C γ δ' φ := by
  rcases hg with h | ⟨n, h, hs⟩ | ⟨n, h, hs⟩ | ⟨n, h, hp⟩ | ⟨n, h, hs, hp⟩ | ⟨k, n, h, hd⟩ |
    ⟨h, hall⟩ | ⟨h, hall⟩
  · exact Or.inl h
  · exact GoodR.xat h (hs.mono hδ)
  · exact GoodR.negXat h (fun hs' => hs (hs'.mono hγ))
  · exact GoodR.belowAt h (hp.mono hδ)
  · exact GoodR.pn h (fun hs' => hs (hs'.mono hγ)) (hp.mono hδ)
  · exact GoodR.precOrXat h (hd.imp id (fun hs => hs.mono hδ))
  · exact GoodR.allXat h (fun o => lt_of_lt_of_le (hall o) hδ)
  · exact GoodR.ti h (fun o => lt_of_lt_of_le (hall o) hδ)

theorem Bound.mono {γ' δ' : O} {Γ : Sequent LRA} (hγ : γ ≤ γ') (hδ : δ ≤ δ')
    (hb : Bound C γ' δ Γ) : Bound C γ δ' Γ :=
  let ⟨ψ, hψ, hg⟩ := hb
  ⟨ψ, hψ, hg.mono hγ hδ⟩

theorem Bound.subset {Γ Γ' : Sequent LRA} (h : Γ ⊆ Γ') (hb : Bound C γ δ Γ) : Bound C γ δ Γ' :=
  let ⟨ψ, hψ, hg⟩ := hb
  ⟨ψ, h hψ, hg⟩

theorem Bound_cons {Γ : Sequent LRA} :
    Bound C γ δ (φ :: Γ) ↔ GoodR C γ δ φ ∨ Bound C γ δ Γ := by
  simp only [Bound, List.exists_mem_cons_iff]

theorem Bound.head (hg : GoodR C γ δ φ) (Γ : Sequent LRA) : Bound C γ δ (φ :: Γ) :=
  Bound_cons.mpr (Or.inl hg)

theorem Bound.tail {Γ : Sequent LRA} (hb : Bound C γ δ Γ) : Bound C γ δ (φ :: Γ) :=
  Bound_cons.mpr (Or.inr hb)

/-! ### `IsXFreeClosed` of the raw named shapes, and their negations -/

theorem isXFreeClosed_verum : IsXFreeClosed (⊤ : Proposition LRA) := ⟨trivial, by simp⟩

theorem not_isXFreeClosed_negProg : ¬ IsXFreeClosed (∼(Prog C.prec)) := by
  intro h
  rw [negProg_eq] at h
  exact not_XFree_Xat (#0 : Semiterm LRA ℕ 1)
    ((XFree_and _ _).mp ((XFree_exs _).mp h.1)).2

theorem not_isXFreeClosed_allXat : ¬ IsXFreeClosed allXat := by
  intro h
  rw [allXat_eq] at h
  exact not_XFree_Xat (#0 : Semiterm LRA ℕ 1) ((XFree_all _).mp h.1)

theorem not_isXFreeClosed_TIR : ¬ IsXFreeClosed (TIR C.prec) := by
  intro h
  rw [TIR_eq] at h
  exact not_isXFreeClosed_allXat (isXFreeClosed_or.mp h).2

theorem not_isXFreeClosed_belowAt (n : ℕ) : ¬ IsXFreeClosed (belowAt C n) := by
  intro h
  rw [belowAt_eq] at h
  exact not_XFree_Xat (#0 : Semiterm LRA ℕ 1)
    ((XFree_or _ _).mp ((XFree_all _).mp h.1)).2

theorem not_isXFreeClosed_P (n : ℕ) : ¬ IsXFreeClosed (P C n) := by
  intro h
  rw [P_eq] at h
  exact not_isXFreeClosed_belowAt n (isXFreeClosed_and.mp h).1

theorem not_isXFreeClosed_precOrXat (m n : ℕ) : ¬ IsXFreeClosed (precOrXat C m n) := by
  intro h
  rw [precOrXat_eq] at h
  exact not_isXFreeClosed_Xat (isXFreeClosed_or.mp h).2

/-! ### Missing "which shape" facts for `evR`-images

`Ramified/LowerClass.lean` proves `isXFreeClosed_evR` (a general `iff`); the
five `not_isXFreeClosed_ev*` corollaries `Gentzen/LowerClassEv.lean` states
explicitly are reproved here in the same one-line shape. -/

theorem not_isXFreeClosed_evR_TIR : ¬ IsXFreeClosed (evR (TIR C.prec)) := by
  rw [isXFreeClosed_evR]; exact not_isXFreeClosed_TIR

theorem not_isXFreeClosed_evR_negProg : ¬ IsXFreeClosed (evR (∼(Prog C.prec))) := by
  rw [isXFreeClosed_evR]; exact not_isXFreeClosed_negProg

theorem not_isXFreeClosed_evR_belowAt (n : ℕ) : ¬ IsXFreeClosed (evR (belowAt C n)) := by
  rw [isXFreeClosed_evR]; exact not_isXFreeClosed_belowAt n

theorem not_isXFreeClosed_evR_P (n : ℕ) : ¬ IsXFreeClosed (evR (P C n)) := by
  rw [isXFreeClosed_evR]; exact not_isXFreeClosed_P n

theorem not_isXFreeClosed_evR_precOrXat (k n : ℕ) :
    ¬ IsXFreeClosed (evR (precOrXat C k n)) := by
  rw [isXFreeClosed_evR]; exact not_isXFreeClosed_precOrXat k n

/-! ### Truth in `ℕ`, in the shape the rules produce

`TrueNR` has no `OmegaTruth`-style companion file for `LRA`; the four laws
are proved directly from `Semiformula.Eval` and the fact that a numeral's
value is itself. -/

theorem trueNR_or (φ ψ : Proposition LRA) : TrueNR (φ ⋎ ψ) ↔ TrueNR φ ∨ TrueNR ψ := by
  simp [TrueNR]

theorem trueNR_and (φ ψ : Proposition LRA) : TrueNR (φ ⋏ ψ) ↔ TrueNR φ ∧ TrueNR ψ := by
  simp [TrueNR]

theorem trueNR_verum : TrueNR (⊤ : Proposition LRA) := by simp [TrueNR]

/-- Substituting a numeral into a one-variable formula and reading it in `ℕ`
is evaluating the formula at that number. -/
theorem trueNR_subst_numeral (φ : Semiproposition LRA 1) (n : ℕ) :
    TrueNR (φ/[(numAtR n : Semiterm LRA ℕ 0)]) ↔
      Semiformula.Eval (s := stdLRA) ![n] (fun _ => 0) φ := by
  unfold TrueNR
  rw [Semiformula.eval_substs]
  refine iff_of_eq
    (congrArg (fun w => Semiformula.Eval (s := stdLRA) w (fun _ => 0) φ) (funext fun i => ?_))
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp only [Function.comp_def, Matrix.cons_val_zero]
  rw [stdLRA_eq_raStd]
  exact val_numAtR raStruc n ![] (fun _ => 0)

theorem trueNR_all (φ : Semiproposition LRA 1) :
    TrueNR (∀¹ φ) ↔ ∀ n : ℕ, TrueNR (φ/[(numAtR n : Semiterm LRA ℕ 0)]) := by
  unfold TrueNR
  rw [Semiformula.eval_all]
  exact forall_congr' fun n => (trueNR_subst_numeral φ n).symm

theorem trueNR_exs (φ : Semiproposition LRA 1) :
    TrueNR (∃¹ φ) ↔ ∃ n : ℕ, TrueNR (φ/[(numAtR n : Semiterm LRA ℕ 0)]) := by
  unfold TrueNR
  rw [Semiformula.eval_ex]
  exact exists_congr fun n => (trueNR_subst_numeral φ n).symm

theorem trueNR_inst (φ : Semiproposition LRA 1) (n : ℕ) :
    TrueNR (evInstR.inst φ n) ↔ TrueNR (φ/[(numAtR n : Semiterm LRA ℕ 0)]) := by
  rw [evInstR_inst]
  exact trueNR_evR _

/-! ### Which reading applies to which shape -/

theorem isXFreeClosed_of_isArithLitR (h : IsArithLitR φ) : IsXFreeClosed φ := by
  refine ⟨?_, freeVariables_of_isArithLitR h⟩
  obtain ⟨k, r, v, hφ | hφ, -⟩ := h
  · subst hφ; exact (XFree_rel _ _).mpr ⟨r, rfl⟩
  · subst hφ; exact (XFree_nrel _ _).mpr ⟨r, rfl⟩

theorem evR_belowAt_ne_allXat (n : ℕ) : evR (belowAt C n) ≠ allXat := by
  intro h
  rw [evR_belowAt_eq, allXat_eq] at h
  have h' := (Semiformula.all_inj _ _).mp h
  have h'' := congrArg (fun χ : Semiformula LRA ℕ 1 => evInstR.inst χ 0) h'
  simp only [inst_belowBody, inst_allXat_body] at h''
  have := congrArg head h''
  simp at this

theorem evR_precOrXat_ne_evR_TIR (k n : ℕ) : evR (precOrXat C k n) ≠ evR (TIR C.prec) := by
  intro h
  rw [evR_precOrXat_eq, evR_TIR_eq] at h
  have := congrArg head ((Semiformula.or_inj _ _ _ _).mp h).2
  simp at this

theorem evR_precOrXat_inj {k n k' n' : ℕ}
    (h : evR (precOrXat C k n) = evR (precOrXat C k' n')) : k = k' ∧ (C.precN k n ↔ C.precN k' n') := by
  rw [evR_precOrXat_eq, evR_precOrXat_eq] at h
  obtain ⟨h₁, h₂⟩ := (Semiformula.or_inj _ _ _ _).mp h
  refine ⟨Xat_numAtR_inj.mp h₂, ?_⟩
  have := congrArg TrueNR h₁
  simp only [trueNR_evR_neg_precAt] at this
  exact not_iff_not.mp (iff_of_eq this)

theorem evR_P_inj {n n' : ℕ} (h : evR (P C n) = evR (P C n')) : n = n' := by
  rw [evR_P_eq, evR_P_eq] at h
  exact neg_Xat_numAtR_inj.mp ((Semiformula.and_inj _ _ _ _).mp h).2

/-- Two `belowAt` formulas with the same evaluation have the same
predecessors. -/
theorem evR_belowAt_precN_iff {n n' : ℕ}
    (h : evR (belowAt C n) = evR (belowAt C n')) (k : ℕ) : C.precN k n ↔ C.precN k n' := by
  rw [evR_belowAt_eq, evR_belowAt_eq] at h
  have h' := (Semiformula.all_inj _ _).mp h
  have h'' := congrArg (fun χ : Semiformula LRA ℕ 1 => evInstR.inst χ k) h'
  simp only [inst_belowBody] at h''
  exact (evR_precOrXat_inj h'').2

theorem GoodR_xfree_iff (hx : IsXFreeClosed φ) : GoodR C γ δ φ ↔ TrueNR φ := by
  constructor
  · rintro (h | ⟨n, h, -⟩ | ⟨n, h, -⟩ | ⟨n, h, -⟩ | ⟨n, h, -⟩ | ⟨k, n, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact h.2
    · subst h; exact absurd hx not_isXFreeClosed_Xat
    · subst h; exact absurd hx not_isXFreeClosed_neg_Xat
    · subst h; exact absurd ((isXFreeClosed_evR _).mp hx) (not_isXFreeClosed_belowAt n)
    · subst h; exact absurd ((isXFreeClosed_evR _).mp hx) (not_isXFreeClosed_P n)
    · subst h; exact absurd ((isXFreeClosed_evR _).mp hx) (not_isXFreeClosed_precOrXat k n)
    · subst h; exact absurd hx not_isXFreeClosed_allXat
    · subst h; exact absurd ((isXFreeClosed_evR _).mp hx) not_isXFreeClosed_TIR
  · exact fun ht => GoodR.xfree hx ht

theorem GoodR_xat_iff (n : ℕ) :
    GoodR C γ δ (Xat (numAtR n : Semiterm LRA ℕ 0)) ↔ Small C δ n := by
  constructor
  · rintro (h | ⟨m, h, hs⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd h.1 not_isXFreeClosed_Xat
    · rw [Xat_numAtR_inj.mp h]; exact hs
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact absurd h (ne_of_head (by simp))
  · exact fun hs => GoodR.xat rfl hs

theorem GoodR_negXat_iff (n : ℕ) :
    GoodR C γ δ (∼(Xat (numAtR n : Semiterm LRA ℕ 0))) ↔ ¬ Small C γ n := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, hs⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd h.1 not_isXFreeClosed_neg_Xat
    · exact absurd h (ne_of_head (by simp))
    · rw [neg_Xat_numAtR_inj.mp h]; exact hs
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact absurd h (ne_of_head (by simp))
  · exact fun hs => GoodR.negXat rfl hs

theorem GoodR_belowAt_iff (n : ℕ) : GoodR C γ δ (evR (belowAt C n)) ↔ PredsSmall C δ n := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, hp⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd ((isXFreeClosed_evR _).mp h.1) (not_isXFreeClosed_belowAt n)
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact hp.congr (evR_belowAt_precN_iff h)
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (evR_belowAt_ne_allXat n)
    · exact absurd h (ne_of_head (by simp))
  · exact fun hp => GoodR.belowAt rfl hp

theorem GoodR_P_iff (n : ℕ) :
    GoodR C γ δ (evR (P C n)) ↔ ¬ Small C γ n ∧ PredsSmall C δ n := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, hs, hp⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd ((isXFreeClosed_evR _).mp h.1) (not_isXFreeClosed_P n)
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · rw [evR_P_inj h]; exact ⟨hs, hp⟩
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact absurd h (ne_of_head (by simp))
  · exact fun ⟨hs, hp⟩ => GoodR.pn rfl hs hp

theorem GoodR_precOrXat_iff (k n : ℕ) :
    GoodR C γ δ (evR (precOrXat C k n)) ↔ (¬ C.precN k n ∨ Small C δ k) := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k', m, h, hd⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd ((isXFreeClosed_evR _).mp h.1) (not_isXFreeClosed_precOrXat k n)
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · obtain ⟨rfl, hiff⟩ := evR_precOrXat_inj h
      exact hd.imp (fun hn hk => hn (hiff.mp hk)) id
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact absurd h (evR_precOrXat_ne_evR_TIR k n)
  · exact fun hd => GoodR.precOrXat rfl hd

theorem GoodR_allXat_iff : GoodR C γ δ allXat ↔ ∀ o : O, o < δ := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨-, hall⟩ | ⟨h, -⟩)
    · exact absurd h.1 not_isXFreeClosed_allXat
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact absurd h.symm (evR_belowAt_ne_allXat m)
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact hall
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
  · exact fun hall => GoodR.allXat rfl hall

theorem GoodR_TIR_iff : GoodR C γ δ (evR (TIR C.prec)) ↔ ∀ o : O, o < δ := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨-, hall⟩)
    · exact absurd ((isXFreeClosed_evR _).mp h.1) not_isXFreeClosed_TIR
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h.symm (evR_precOrXat_ne_evR_TIR k m)
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact hall
  · exact fun hall => GoodR.ti rfl hall

theorem not_goodR_negProg : ¬ GoodR C γ δ (evR (∼(Prog C.prec))) := by
  rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
  · exact absurd ((isXFreeClosed_evR _).mp h.1) not_isXFreeClosed_negProg
  · exact absurd h (ne_of_head (by simp))
  · exact absurd h (ne_of_head (by simp))
  · exact absurd h (ne_of_head (by simp))
  · exact absurd h (ne_of_head (by simp))
  · exact absurd h (ne_of_head (by simp))
  · exact absurd h (ne_of_head (by simp [allXat_eq]))
  · exact absurd h (ne_of_head (by simp))

/-! ### The lemma -/

set_option maxHeartbeats 2000000 in
/-- **Boundedness.**  A cut-free derivation of height `α` of a sequent in the
class has, for every lower bound `γ`, a good member under `(γ, γ ⊕ ω^α)`.  The
atomic axioms may include the junk literals: a negated set atom is never in the
class. -/
theorem boundedness_junk [WellFoundedLT O] [OrdinalNotation O] {α : O} {Γ : Sequent LRA}
    (h : OmegaDerivableR junkLitsR evInstR 0 α Γ) :
    InCeSeq C Γ → ∀ γ : O, Bound C γ (OrdinalNotation.nadd γ (OrdinalNotation.omegaPow α)) Γ := by
  induction h with
  | @atom α φ hφ =>
      intro hC γ
      rcases hφ with hφ | ⟨ν, n, a, rfl, -⟩
      · exact Bound.head (GoodR.xfree (isXFreeClosed_of_isArithLitR hφ.1) hφ.2) _
      · exact absurd (hC _ List.mem_cons_self) not_inCe_nmemAt
  | @identity α k rl v =>
      intro hC γ
      have hle : γ ≤ OrdinalNotation.nadd γ (OrdinalNotation.omegaPow α) :=
        OrdinalNotation.le_nadd_left _ _
      rcases InCe.rel_cases rl v (hC _ List.mem_cons_self) with hx | ⟨n, hn⟩
      · by_cases ht : TrueNR (Semiformula.rel rl v)
        · exact Bound.head (GoodR.xfree hx ht) _
        · refine Bound.tail (Bound.head (GoodR.xfree ?_ ?_) _)
          · exact isXFreeClosed_neg.mpr hx
          · exact (trueNR_neg (Semiformula.rel rl v)).mpr ht
      · have hn' : Semiformula.nrel rl v = ∼(Xat (numAtR n : Semiterm LRA ℕ 0)) := by
          rw [← hn]; rfl
        by_cases hs : Small C γ n
        · exact Bound.head (GoodR.xat hn (hs.mono hle)) _
        · exact Bound.tail (Bound.head (GoodR.negXat hn' hs) _)
  | verum =>
      intro _ γ
      exact Bound.head (GoodR.xfree isXFreeClosed_verum trueNR_verum) _
  | @or α β φ ψ Γ' hlt _ ih =>
      intro hC γ
      have hle := nadd_omegaPow_le (γ := γ) hlt
      have hB := ih (InCeSeq.of_or hC) γ
      rw [Bound_cons, Bound_cons] at hB
      rcases InCe.or_cases (hC _ List.mem_cons_self) with hx | ⟨hφ, hψ⟩ | ⟨k, n, hφ, hψ⟩
      · have hxφ : IsXFreeClosed φ := (isXFreeClosed_or.mp hx).1
        have hxψ : IsXFreeClosed ψ := (isXFreeClosed_or.mp hx).2
        rcases hB with hg | hg | hB
        · exact Bound.head (GoodR.xfree hx ((trueNR_or φ ψ).mpr
            (Or.inl ((GoodR_xfree_iff hxφ).mp hg)))) _
        · exact Bound.head (GoodR.xfree hx ((trueNR_or φ ψ).mpr
            (Or.inr ((GoodR_xfree_iff hxψ).mp hg)))) _
        · exact Bound.tail (hB.mono le_rfl hle)
      · subst hφ; subst hψ
        rcases hB with hg | hg | hB
        · exact absurd hg not_goodR_negProg
        · exact Bound.head (GoodR.ti evR_TIR_eq.symm
            (fun o => lt_of_lt_of_le (GoodR_allXat_iff.mp hg o) hle)) _
        · exact Bound.tail (hB.mono le_rfl hle)
      · subst hφ; subst hψ
        rcases hB with hg | hg | hB
        · have ht := (GoodR_xfree_iff (isXFreeClosed_evR_neg_precAt k n)).mp hg
          exact Bound.head (GoodR.precOrXat (evR_precOrXat_eq k n).symm
            (Or.inl ((trueNR_evR_neg_precAt k n).mp ht))) _
        · exact Bound.head (GoodR.precOrXat (evR_precOrXat_eq k n).symm
            (Or.inr (((GoodR_xat_iff k).mp hg).mono hle))) _
        · exact Bound.tail (hB.mono le_rfl hle)
  | @and α β₁ β₂ φ ψ Γ' hb hc _ _ ihp ihq =>
      intro hC γ
      have hle₁ := nadd_omegaPow_le (γ := γ) hb
      have hle₂ := nadd_omegaPow_le (γ := γ) hc
      obtain ⟨hCφ, hCψ⟩ := InCeSeq.of_and hC
      have hBp := ihp hCφ γ
      have hBq := ihq hCψ γ
      rw [Bound_cons] at hBp hBq
      rcases InCe.and_cases (hC _ List.mem_cons_self) with hx | ⟨n, hφ, hψ⟩
      · have hxφ : IsXFreeClosed φ := (isXFreeClosed_and.mp hx).1
        have hxψ : IsXFreeClosed ψ := (isXFreeClosed_and.mp hx).2
        rcases hBp with hg | hB
        · rcases hBq with hg' | hB'
          · exact Bound.head (GoodR.xfree hx ((trueNR_and φ ψ).mpr
              ⟨(GoodR_xfree_iff hxφ).mp hg, (GoodR_xfree_iff hxψ).mp hg'⟩)) _
          · exact Bound.tail (hB'.mono le_rfl hle₂)
        · exact Bound.tail (hB.mono le_rfl hle₁)
      · subst hφ; subst hψ
        rcases hBp with hg | hB
        · rcases hBq with hg' | hB'
          · exact Bound.head (GoodR.pn (evR_P_eq n).symm ((GoodR_negXat_iff n).mp hg')
              (((GoodR_belowAt_iff n).mp hg).mono hle₁)) _
          · exact Bound.tail (hB'.mono le_rfl hle₂)
        · exact Bound.tail (hB.mono le_rfl hle₁)
  | @omegaRule α φ Γ' f hf _ ih =>
      intro hC γ
      have hle : ∀ m, OrdinalNotation.nadd γ (OrdinalNotation.omegaPow (f m))
          ≤ OrdinalNotation.nadd γ (OrdinalNotation.omegaPow α) := fun m => nadd_omegaPow_le (hf m)
      by_cases hctx : ∃ m, Bound C γ (OrdinalNotation.nadd γ (OrdinalNotation.omegaPow (f m))) Γ'
      · obtain ⟨m, hB⟩ := hctx
        exact Bound.tail (hB.mono le_rfl (hle m))
      · have hno : ∀ m, ¬ Bound C γ (OrdinalNotation.nadd γ (OrdinalNotation.omegaPow (f m))) Γ' :=
          fun m hB => hctx ⟨m, hB⟩
        have hprem : ∀ m, GoodR C γ (OrdinalNotation.nadd γ (OrdinalNotation.omegaPow (f m)))
            (evInstR.inst φ m) := by
          intro m
          have hB := ih m (InCeSeq.of_all hC m) γ
          rw [Bound_cons] at hB
          exact hB.resolve_right (hno m)
        rcases InCe.all_cases (hC _ List.mem_cons_self) with hx | hφ | ⟨n, hφ⟩
        · refine Bound.head (GoodR.xfree hx ((trueNR_all φ).mpr (fun m => ?_))) _
          exact (trueNR_inst φ m).mp
            ((GoodR_xfree_iff (isXFreeClosed_inst hx m)).mp (hprem m))
        · subst hφ
          refine Bound.head (GoodR.allXat allXat_eq.symm (fun o => ?_)) _
          have hg := hprem (C.code o)
          rw [inst_allXat_body] at hg
          exact lt_of_lt_of_le ((GoodR_xat_iff _).mp hg o rfl) (hle _)
        · subst hφ
          refine Bound.head (GoodR.belowAt (evR_belowAt_eq n).symm (fun k hk => ?_)) _
          have hg := hprem k
          rw [inst_belowBody] at hg
          exact (((GoodR_precOrXat_iff k n).mp hg).resolve_left (not_not.mpr hk)).mono (hle k)
  | @exs α β φ Γ' m hlt _ ih =>
      intro hC γ
      have hle := nadd_omegaPow_le (γ := γ) hlt
      have hC' := InCeSeq.of_exs hC m
      rcases InCe.exs_cases (hC _ List.mem_cons_self) with hx | hφ
      · have hB := ih hC' γ
        rw [Bound_cons] at hB
        rcases hB with hg | hB
        · refine Bound.head (GoodR.xfree hx ((trueNR_exs φ).mpr ⟨m, ?_⟩)) _
          exact (trueNR_inst φ m).mp
            ((GoodR_xfree_iff (isXFreeClosed_inst_exs hx m)).mp hg)
        · exact Bound.tail (hB.mono le_rfl hle)
      · subst hφ
        have hB := ih hC' γ
        rw [inst_negProg_body, Bound_cons] at hB
        rcases hB with hg | hB
        · obtain ⟨-, hp⟩ := (GoodR_P_iff m).mp hg
          -- invoke the hypothesis again, above the counterexample
          have hB' := ih hC' (OrdinalNotation.succ (OrdinalNotation.nadd γ (OrdinalNotation.omegaPow β)))
          rw [inst_negProg_body, Bound_cons] at hB'
          rcases hB' with hg' | hB'
          · exact absurd (Small.of_predsSmall hp) ((GoodR_P_iff m).mp hg').1
          · refine Bound.tail (hB'.mono ?_ (bump_le hlt))
            exact le_trans (OrdinalNotation.le_nadd_left _ _) (OrdinalNotation.le_succ _)
        · exact Bound.tail (hB.mono le_rfl hle)
  | contraction ss _ ih =>
      intro hC γ
      exact (ih (InCeSeq.of_subset hC ss) γ).subset ss
  | cut hc _ _ _ _ _ _ =>
      exact absurd hc (not_lt_zero_gamma0 _)
  | pr _ _ _ _ =>
      intro hC _
      exact absurd (hC _ List.mem_cons_self) not_inCe_memAt
  | npr _ _ _ _ =>
      intro hC _
      exact absurd (hC _ List.mem_cons_self) not_inCe_nmemAt

/-- **Boundedness**, for the true arithmetic literals alone. -/
theorem boundedness [WellFoundedLT O] [OrdinalNotation O] {α : O} {Γ : Sequent LRA}
    (h : OmegaDerivableR trueArithLitsR evInstR 0 α Γ) :
    InCeSeq C Γ → ∀ γ : O, Bound C γ (OrdinalNotation.nadd γ (OrdinalNotation.omegaPow α)) Γ :=
  boundedness_junk (h.mono_lits trueArithLitsR_le_junkLitsR)

/-- **`TI(≺)` has no cut-free `RA_∞`-derivation at any height**, even with the
junk literals among the axioms. -/
theorem not_derivable_TI_R_junk [WellFoundedLT O] [OrdinalNotation O] (C : CodedOrderR O)
    (α : O) : ¬ OmegaDerivableR junkLitsR evInstR 0 α [evR (TIR C.prec)] := by
  intro h
  have hB := boundedness_junk h (fun ψ hψ => by
    simp only [List.mem_singleton] at hψ
    subst hψ
    exact InCe.ti) α
  rw [Bound_cons] at hB
  rcases hB with hg | ⟨ψ, hψ, -⟩
  · exact lt_irrefl _ (GoodR_TIR_iff.mp hg _)
  · simp at hψ

/-- **`TI(≺)` has no cut-free `RA_∞`-derivation at any height.** -/
theorem not_derivable_TI_R [WellFoundedLT O] [OrdinalNotation O] (C : CodedOrderR O) (α : O) :
    ¬ OmegaDerivableR trueArithLitsR evInstR 0 α [evR (TIR C.prec)] := fun h =>
  not_derivable_TI_R_junk C α (h.mono_lits trueArithLitsR_le_junkLitsR)

/-- **The `Γ₀` instance**, with the junk literals. -/
theorem not_derivable_TI_R_gamma0_junk (α : Gamma0Note) :
    ¬ OmegaDerivableR junkLitsR evInstR 0 α [evR (TIR gamma0OrderR.prec)] :=
  not_derivable_TI_R_junk gamma0OrderR α

/-- **The `Γ₀` instance.**  Transfinite induction along the coded Veblen
ordering of `gamma0OrderR` has no cut-free `RA_∞`-derivation at any height. -/
theorem not_derivable_TI_R_gamma0 (α : Gamma0Note) :
    ¬ OmegaDerivableR trueArithLitsR evInstR 0 α [evR (TIR gamma0OrderR.prec)] :=
  not_derivable_TI_R gamma0OrderR α

end Ramified

end OrdinalAnalysis
