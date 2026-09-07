/-
  The boundedness lemma.

  A cut-free derivation of height `α` in the evaluating ω-calculus, all of
  whose formulas lie in the class `Ce`, cannot prove `TI(≺)`.  The reason is not
  semantic — `TI(≺)` is true in `ℕ` for every reading of `X`, and the calculus
  is sound for all of them — but a matter of height: a derivation of
  `¬Prog(X), X(n̄)` has to climb the ordinal coded by `n`, so its height bounds
  that ordinal, and the heights available are the notations below `ε₀`.

  The invariant that carries this is a reading of the class members with two
  parameters, a lower bound `γ` and an upper bound `δ`:

  * `X(n̄)` reads as "the ordinal coded by `n` is below `δ`";
  * `∼X(n̄)` reads as "the ordinal coded by `n` is not below `γ`";
  * `¬Prog(X)` has **no** reading at all — it is never the witness;
  * the remaining members read as their positive content bounded by `δ`.

  The lemma says: for every `γ`, a derivation of height `α` has a member true
  under the reading `(γ, γ ⊕ ω^α)`.  Every rule is checked directly.  The one
  case with content is `∃` on `¬Prog(X)`: the premise carries the counterexample
  `P(n̄)`, whose reading pins the ordinal of `n` between `γ` and `γ ⊕ ω^α'`; the
  induction hypothesis is then invoked a second time at the lower bound
  `succ (γ ⊕ ω^α')`, where `P(n̄)` can no longer be the witness, and the witness
  it produces instead is transported back down to `γ` — the upper bound grows
  from `γ ⊕ ω^α'` to `succ (γ ⊕ ω^α') ⊕ ω^α'`, which is still below `γ ⊕ ω^α`
  because `ω^α` is additively indecomposable.  That is the only ordinal
  arithmetic in the file.

  Predecessors are spoken of through the coded ordering `≺` on numbers, never
  through a rank function: "every predecessor of `n` is small" is
  `∀ k, k ≺ n → Small k`.  This is what makes the reading of `∀ y ≺ n̄, X y`
  transfer between two numbers with the same instances, which is all the
  syntax can tell apart.

  At the end `γ := 0` and the reading of `TI(≺)` is "every notation is below
  `ω^α`", refuted by `ω^α` itself.
-/
import OrdinalAnalysis.Gentzen.LowerClassEv

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.Boundedness

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen OrdinalAnalysis.Gentzen.StandardLX
open OrdinalAnalysis.Gentzen.LowerSyntax OrdinalAnalysis.Gentzen.LowerClass
open OrdinalAnalysis.Gentzen.Evaluate OrdinalAnalysis.Gentzen.EvInst
open OrdinalAnalysis.Gentzen.PrecStandard OrdinalAnalysis.Gentzen.LowerClassEv
open OrdinalAnalysis.Gentzen.NotationBridge OrdinalAnalysis.Gentzen.CodedNotation
open OrdinalAnalysis.OrdinalNotation

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O] {C : CodedOrder O}

/-! ### Ordinal facts -/

/-- **The bump.**  Raising the lower bound to `succ (γ ⊕ ω^β)` raises the upper
bound to `succ (γ ⊕ ω^β) ⊕ ω^β`, which is still below `γ ⊕ ω^α` for `β < α`. -/
theorem bump_le {γ β α : O} (h : β < α) :
    OrdinalNotation.nadd (OrdinalNotation.succ (OrdinalNotation.nadd γ (OrdinalNotation.omegaPow β))) (OrdinalNotation.omegaPow β) ≤ OrdinalNotation.nadd γ (OrdinalNotation.omegaPow α) := by
  have hw : OrdinalNotation.omegaPow β < OrdinalNotation.omegaPow α := OrdinalNotation.omegaPow_lt_omegaPow h
  have h1 : OrdinalNotation.one < OrdinalNotation.omegaPow α := lt_of_le_of_lt (OrdinalNotation.one_le_omegaPow β) hw
  have hlt : OrdinalNotation.nadd (OrdinalNotation.omegaPow β) (OrdinalNotation.nadd OrdinalNotation.one (OrdinalNotation.omegaPow β)) < OrdinalNotation.omegaPow α :=
    OrdinalNotation.nadd_lt_omegaPow hw (OrdinalNotation.nadd_lt_omegaPow h1 hw)
  have e : OrdinalNotation.nadd (OrdinalNotation.succ (OrdinalNotation.nadd γ (OrdinalNotation.omegaPow β))) (OrdinalNotation.omegaPow β)
      = OrdinalNotation.nadd γ (OrdinalNotation.nadd (OrdinalNotation.omegaPow β) (OrdinalNotation.nadd OrdinalNotation.one (OrdinalNotation.omegaPow β))) := by
    simp only [OrdinalNotation.succ]
    rw [OrdinalNotation.nadd_assoc, OrdinalNotation.nadd_assoc]
  rw [e]
  exact OrdinalNotation.nadd_le_nadd_right γ (le_of_lt hlt)

theorem nadd_omegaPow_le {γ β α : O} (h : β < α) :
    OrdinalNotation.nadd γ (OrdinalNotation.omegaPow β) ≤ OrdinalNotation.nadd γ (OrdinalNotation.omegaPow α) :=
  OrdinalNotation.nadd_le_nadd_right γ (le_of_lt (OrdinalNotation.omegaPow_lt_omegaPow h))

/-! ### The reading of a code -/

/-- The ordinal coded by `n`, if any, is below `δ`. -/
def Small (C : CodedOrder O) (δ : O) (n : ℕ) : Prop := ∀ o : O, C.code o = n → o < δ

/-- Every `≺`-predecessor of `n` is small. -/
def PredsSmall (C : CodedOrder O) (δ : O) (n : ℕ) : Prop := ∀ k : ℕ, C.precN k n → Small C δ k

theorem Small.mono {δ δ' : O} {n : ℕ} (h : δ ≤ δ') (hs : Small C δ n) : Small C δ' n :=
  fun o ho => lt_of_lt_of_le (hs o ho) h

theorem PredsSmall.mono {δ δ' : O} {n : ℕ} (h : δ ≤ δ') (hs : PredsSmall C δ n) :
    PredsSmall C δ' n :=
  fun k hk => (hs k hk).mono h

theorem PredsSmall.congr {δ : O} {n n' : ℕ} (hiff : ∀ k, C.precN k n ↔ C.precN k n')
    (hs : PredsSmall C δ n') : PredsSmall C δ n :=
  fun k hk => hs k ((hiff k).mp hk)

/-- A number all of whose predecessors are below `δ` is at most `δ`: linearity. -/
theorem le_of_predsSmall {δ : O} {n : ℕ} (h : PredsSmall C δ n) {o : O}
    (ho : C.code o = n) : o ≤ δ := by
  refine le_of_forall_lt_lt (fun o' ho' => ?_)
  refine h (C.code o') ?_ o' rfl
  rw [← ho]
  exact C.precN_code_of_lt ho'

theorem Small.of_predsSmall {δ : O} {n : ℕ} (h : PredsSmall C δ n) :
    Small C (OrdinalNotation.succ δ) n :=
  fun _ ho => OrdinalNotation.lt_succ_of_le (le_of_predsSmall h ho)

theorem Small.of_predsSmall_lt {δ δ' : O} {n : ℕ} (h : PredsSmall C δ n) (hδ : δ < δ') :
    Small C δ' n :=
  fun _ ho => lt_of_le_of_lt (le_of_predsSmall h ho) hδ

/-! ### The reading of the class -/

/-- The reading of a class member under the bounds `(γ, δ)`; `¬Prog(X)` has none. -/
def Good (C : CodedOrder O) (γ δ : O) (φ : Proposition LX) : Prop :=
  (IsXFreeClosed φ ∧ TrueN φ) ∨
  (∃ n, φ = Xat (LowerSyntax.numLX n) ∧ Small C δ n) ∨
  (∃ n, φ = ∼(Xat (LowerSyntax.numLX n)) ∧ ¬ Small C γ n) ∨
  (∃ n, φ = ev (LowerClass.belowAt C n) ∧ PredsSmall C δ n) ∨
  (∃ n, φ = ev (LowerClass.P C n) ∧ ¬ Small C γ n ∧ PredsSmall C δ n) ∨
  (∃ k n, φ = ev (precOrXat C k n) ∧ (¬ C.precN k n ∨ Small C δ k)) ∨
  (φ = allXat ∧ ∀ o : O, o < δ) ∨
  (φ = ev (TI C.prec) ∧ ∀ o : O, o < δ)

/-- Some member of the sequent is good. -/
def Bound (C : CodedOrder O) (γ δ : O) (Γ : Sequent LX) : Prop := ∃ φ ∈ Γ, Good C γ δ φ

variable {γ δ : O} {φ : Proposition LX}

theorem Good.xfree (hx : IsXFreeClosed φ) (ht : TrueN φ) : Good C γ δ φ := Or.inl ⟨hx, ht⟩

theorem Good.xat {n : ℕ} (h : φ = Xat (LowerSyntax.numLX n)) (hs : Small C δ n) : Good C γ δ φ :=
  Or.inr (Or.inl ⟨n, h, hs⟩)

theorem Good.negXat {n : ℕ} (h : φ = ∼(Xat (LowerSyntax.numLX n))) (hs : ¬ Small C γ n) : Good C γ δ φ :=
  Or.inr (Or.inr (Or.inl ⟨n, h, hs⟩))

theorem Good.belowAt {n : ℕ} (h : φ = ev (LowerClass.belowAt C n)) (hp : PredsSmall C δ n) : Good C γ δ φ :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h, hp⟩)))

theorem Good.pn {n : ℕ} (h : φ = ev (LowerClass.P C n)) (hs : ¬ Small C γ n) (hp : PredsSmall C δ n) :
    Good C γ δ φ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h, hs, hp⟩))))

theorem Good.precOrXat {k n : ℕ} (h : φ = ev (precOrXat C k n))
    (hd : ¬ C.precN k n ∨ Small C δ k) : Good C γ δ φ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, n, h, hd⟩)))))

theorem Good.allXat (h : φ = allXat) (hall : ∀ o : O, o < δ) : Good C γ δ φ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hall⟩))))))

theorem Good.ti (h : φ = ev (TI C.prec)) (hall : ∀ o : O, o < δ) : Good C γ δ φ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hall⟩))))))

/-- Lowering `γ` and raising `δ` keeps a reading good. -/
theorem Good.mono {γ' δ' : O} (hγ : γ ≤ γ') (hδ : δ ≤ δ') (hg : Good C γ' δ φ) :
    Good C γ δ' φ := by
  rcases hg with h | ⟨n, h, hs⟩ | ⟨n, h, hs⟩ | ⟨n, h, hp⟩ | ⟨n, h, hs, hp⟩ | ⟨k, n, h, hd⟩ |
    ⟨h, hall⟩ | ⟨h, hall⟩
  · exact Or.inl h
  · exact Good.xat h (hs.mono hδ)
  · exact Good.negXat h (fun hs' => hs (hs'.mono hγ))
  · exact Good.belowAt h (hp.mono hδ)
  · exact Good.pn h (fun hs' => hs (hs'.mono hγ)) (hp.mono hδ)
  · exact Good.precOrXat h (hd.imp id (fun hs => hs.mono hδ))
  · exact Good.allXat h (fun o => lt_of_lt_of_le (hall o) hδ)
  · exact Good.ti h (fun o => lt_of_lt_of_le (hall o) hδ)

theorem Bound.mono {γ' δ' : O} {Γ : Sequent LX} (hγ : γ ≤ γ') (hδ : δ ≤ δ')
    (hb : Bound C γ' δ Γ) : Bound C γ δ' Γ :=
  let ⟨ψ, hψ, hg⟩ := hb
  ⟨ψ, hψ, hg.mono hγ hδ⟩

theorem Bound.subset {Γ Γ' : Sequent LX} (h : Γ ⊆ Γ') (hb : Bound C γ δ Γ) : Bound C γ δ Γ' :=
  let ⟨ψ, hψ, hg⟩ := hb
  ⟨ψ, h hψ, hg⟩

theorem Bound_cons {Γ : Sequent LX} :
    Bound C γ δ (φ :: Γ) ↔ Good C γ δ φ ∨ Bound C γ δ Γ := by
  simp only [Bound, List.exists_mem_cons_iff]

theorem Bound.head (hg : Good C γ δ φ) (Γ : Sequent LX) : Bound C γ δ (φ :: Γ) :=
  Bound_cons.mpr (Or.inl hg)

theorem Bound.tail {Γ : Sequent LX} (hb : Bound C γ δ Γ) : Bound C γ δ (φ :: Γ) :=
  Bound_cons.mpr (Or.inr hb)

/-! ### Truth in `ℕ`, in the shape the rules produce -/

theorem trueN_or (φ ψ : Proposition LX) : TrueN (φ ⋎ ψ) ↔ TrueN φ ∨ TrueN ψ :=
  OmegaTruth.eval_or_iff _ _ φ ψ

theorem trueN_and (φ ψ : Proposition LX) : TrueN (φ ⋏ ψ) ↔ TrueN φ ∧ TrueN ψ :=
  OmegaTruth.eval_and_iff _ _ φ ψ

theorem trueN_all (φ : Semiproposition LX 1) : TrueN (∀¹ φ) ↔ ∀ n, TrueN (φ/[LowerSyntax.numLX n]) :=
  OmegaTruth.eval_all_numLX _ _ φ

theorem trueN_exs (φ : Semiproposition LX 1) : TrueN (∃¹ φ) ↔ ∃ n, TrueN (φ/[LowerSyntax.numLX n]) :=
  OmegaTruth.eval_exs_numLX _ _ φ

theorem trueN_inst (φ : Semiproposition LX 1) (n : ℕ) :
    TrueN (evInst.inst φ n) ↔ TrueN (φ/[LowerSyntax.numLX n]) := by
  rw [evInst_inst]
  exact trueN_ev _

theorem trueN_verum : TrueN (⊤ : Proposition LX) := by simp [TrueN]

theorem isXFreeClosed_verum : IsXFreeClosed (⊤ : Proposition LX) := ⟨trivial, by simp⟩

/-! ### Which reading applies to which shape -/

theorem isXFreeClosed_of_isArithLit (h : IsArithLit φ) : IsXFreeClosed φ := by
  refine ⟨?_, freeVariables_of_isArithLit h⟩
  obtain ⟨k, r, v, hφ | hφ, -⟩ := h
  · subst hφ; exact (XFree_rel _ _).mpr ⟨r, rfl⟩
  · subst hφ; exact (XFree_nrel _ _).mpr ⟨r, rfl⟩

@[simp] theorem head_belowAt (n : ℕ) : head (LowerClass.belowAt C n) = 6 := by
  rw [belowAt_eq_all]; rfl

@[simp] theorem head_P (n : ℕ) : head (LowerClass.P C n) = 4 := rfl

@[simp] theorem head_precOrXat (k n : ℕ) : head (precOrXat C k n) = 5 := rfl

theorem ev_belowAt_ne_allXat (n : ℕ) : ev (LowerClass.belowAt C n) ≠ allXat := by
  intro h
  rw [ev_belowAt_eq, allXat_eq] at h
  have h' := (Semiformula.all_inj _ _).mp h
  have h'' := congrArg (fun χ : Semiformula LX ℕ 1 => evInst.inst χ 0) h'
  simp only [inst_belowBody, inst_allXat_body] at h''
  have := congrArg head h''
  simp at this

theorem ev_precOrXat_ne_ev_TI (k n : ℕ) : ev (precOrXat C k n) ≠ ev (TI C.prec) := by
  intro h
  rw [ev_precOrXat_eq, ev_TI_eq] at h
  have := congrArg head ((Semiformula.or_inj _ _ _ _).mp h).2
  simp at this

theorem ev_precOrXat_inj {k n k' n' : ℕ} (h : ev (precOrXat C k n) = ev (precOrXat C k' n')) :
    k = k' ∧ (C.precN k n ↔ C.precN k' n') := by
  rw [ev_precOrXat_eq, ev_precOrXat_eq] at h
  obtain ⟨h₁, h₂⟩ := (Semiformula.or_inj _ _ _ _).mp h
  refine ⟨Xat_numLX_inj.mp h₂, ?_⟩
  have := congrArg TrueN h₁
  simp only [trueN_ev_neg_precAt] at this
  exact not_iff_not.mp (iff_of_eq this)

theorem ev_P_inj {n n' : ℕ} (h : ev (LowerClass.P C n) = ev (LowerClass.P C n')) : n = n' := by
  rw [ev_P_eq, ev_P_eq] at h
  exact neg_Xat_numLX_inj.mp ((Semiformula.and_inj _ _ _ _).mp h).2

/-- Two `below` formulas with the same evaluation have the same predecessors. -/
theorem ev_belowAt_precN_iff {n n' : ℕ} (h : ev (LowerClass.belowAt C n) = ev (LowerClass.belowAt C n')) (k : ℕ) :
    C.precN k n ↔ C.precN k n' := by
  rw [ev_belowAt_eq, ev_belowAt_eq] at h
  have h' := (Semiformula.all_inj _ _).mp h
  have h'' := congrArg (fun χ : Semiformula LX ℕ 1 => evInst.inst χ k) h'
  simp only [inst_belowBody] at h''
  exact (ev_precOrXat_inj h'').2

/-- The tactic for "this shape is not that shape": compare heads. -/
theorem ne_of_head {ψ χ : Proposition LX} (h : head ψ ≠ head χ) : ψ ≠ χ :=
  fun e => h (congrArg head e)

theorem Good_xfree_iff (hx : IsXFreeClosed φ) : Good C γ δ φ ↔ TrueN φ := by
  constructor
  · rintro (h | ⟨n, h, -⟩ | ⟨n, h, -⟩ | ⟨n, h, -⟩ | ⟨n, h, -⟩ | ⟨k, n, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact h.2
    · subst h; exact absurd hx not_isXFreeClosed_Xat
    · subst h; exact absurd hx not_isXFreeClosed_neg_Xat
    · subst h; exact absurd ((isXFreeClosed_ev _).mp hx) (not_isXFreeClosed_belowAt n)
    · subst h; exact absurd ((isXFreeClosed_ev _).mp hx) (not_isXFreeClosed_P n)
    · subst h; exact absurd ((isXFreeClosed_ev _).mp hx) (not_isXFreeClosed_precOrXat k n)
    · subst h; exact absurd hx not_isXFreeClosed_allXat
    · subst h; exact absurd ((isXFreeClosed_ev _).mp hx) not_isXFreeClosed_TI
  · exact fun ht => Good.xfree hx ht

theorem Good_xat_iff (n : ℕ) : Good C γ δ (Xat (LowerSyntax.numLX n)) ↔ Small C δ n := by
  constructor
  · rintro (h | ⟨m, h, hs⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd h.1 not_isXFreeClosed_Xat
    · rw [Xat_numLX_inj.mp h]; exact hs
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact absurd h (ne_of_head (by simp))
  · exact fun hs => Good.xat rfl hs

theorem Good_negXat_iff (n : ℕ) : Good C γ δ (∼(Xat (LowerSyntax.numLX n))) ↔ ¬ Small C γ n := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, hs⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd h.1 not_isXFreeClosed_neg_Xat
    · exact absurd h (ne_of_head (by simp))
    · rw [neg_Xat_numLX_inj.mp h]; exact hs
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact absurd h (ne_of_head (by simp))
  · exact fun hs => Good.negXat rfl hs

theorem Good_belowAt_iff (n : ℕ) : Good C γ δ (ev (LowerClass.belowAt C n)) ↔ PredsSmall C δ n := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, hp⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd ((isXFreeClosed_ev _).mp h.1) (not_isXFreeClosed_belowAt n)
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact hp.congr (ev_belowAt_precN_iff h)
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ev_belowAt_ne_allXat n)
    · exact absurd h (ne_of_head (by simp))
  · exact fun hp => Good.belowAt rfl hp

theorem Good_P_iff (n : ℕ) : Good C γ δ (ev (LowerClass.P C n)) ↔ ¬ Small C γ n ∧ PredsSmall C δ n := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, hs, hp⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd ((isXFreeClosed_ev _).mp h.1) (not_isXFreeClosed_P n)
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · rw [ev_P_inj h]; exact ⟨hs, hp⟩
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact absurd h (ne_of_head (by simp))
  · exact fun ⟨hs, hp⟩ => Good.pn rfl hs hp

theorem Good_precOrXat_iff (k n : ℕ) :
    Good C γ δ (ev (precOrXat C k n)) ↔ (¬ C.precN k n ∨ Small C δ k) := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k', m, h, hd⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd ((isXFreeClosed_ev _).mp h.1) (not_isXFreeClosed_precOrXat k n)
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · obtain ⟨rfl, hiff⟩ := ev_precOrXat_inj h
      exact hd.imp (fun hn hk => hn (hiff.mp hk)) id
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact absurd h (ev_precOrXat_ne_ev_TI k n)
  · exact fun hd => Good.precOrXat rfl hd

theorem Good_allXat_iff : Good C γ δ allXat ↔ ∀ o : O, o < δ := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨-, hall⟩ | ⟨h, -⟩)
    · exact absurd h.1 not_isXFreeClosed_allXat
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact absurd h.symm (ev_belowAt_ne_allXat m)
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact hall
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
  · exact fun hall => Good.allXat rfl hall

theorem Good_TI_iff : Good C γ δ (ev (TI C.prec)) ↔ ∀ o : O, o < δ := by
  constructor
  · rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨-, hall⟩)
    · exact absurd ((isXFreeClosed_ev _).mp h.1) not_isXFreeClosed_TI
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h (ne_of_head (by simp))
    · exact absurd h.symm (ev_precOrXat_ne_ev_TI k m)
    · exact absurd h (ne_of_head (by simp [allXat_eq]))
    · exact hall
  · exact fun hall => Good.ti rfl hall

theorem not_good_negProg : ¬ Good C γ δ (ev (∼(Prog C.prec))) := by
  rintro (h | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨m, h, -⟩ | ⟨k, m, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
  · exact absurd ((isXFreeClosed_ev _).mp h.1) not_isXFreeClosed_negProg
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
class has, for every lower bound `γ`, a good member under `(γ, γ ⊕ ω^α)`. -/
theorem boundedness {α : O} {Γ : Sequent LX}
    (h : OmegaDerivable trueArithLits evInst 0 α Γ) :
    InCeSeq C Γ → ∀ γ : O, Bound C γ (OrdinalNotation.nadd γ (OrdinalNotation.omegaPow α)) Γ := by
  induction h with
  | @atom α φ hφ =>
      intro _ γ
      exact Bound.head (Good.xfree (isXFreeClosed_of_isArithLit hφ.1) hφ.2) _
  | @identity α k rl v =>
      intro hC γ
      have hle : γ ≤ OrdinalNotation.nadd γ (OrdinalNotation.omegaPow α) := OrdinalNotation.le_nadd_left _ _
      rcases InCe.rel_cases rl v (hC _ List.mem_cons_self) with hx | ⟨n, hn⟩
      · by_cases ht : TrueN (Semiformula.rel rl v)
        · exact Bound.head (Good.xfree hx ht) _
        · refine Bound.tail (Bound.head (Good.xfree ?_ ?_) _)
          · exact isXFreeClosed_neg.mpr hx
          · exact (trueN_neg (Semiformula.rel rl v)).mpr ht
      · have hn' : Semiformula.nrel rl v = ∼(Xat (LowerSyntax.numLX n)) := by
          rw [← hn]; rfl
        by_cases hs : Small C γ n
        · exact Bound.head (Good.xat hn (hs.mono hle)) _
        · exact Bound.tail (Bound.head (Good.negXat hn' hs) _)
  | verum =>
      intro _ γ
      exact Bound.head (Good.xfree isXFreeClosed_verum trueN_verum) _
  | @or α β φ ψ Γ' hlt _ ih =>
      intro hC γ
      have hle := nadd_omegaPow_le (γ := γ) hlt
      have hB := ih (InCeSeq.of_or hC) γ
      rw [Bound_cons, Bound_cons] at hB
      rcases InCe.or_cases (hC _ List.mem_cons_self) with hx | ⟨hφ, hψ⟩ | ⟨k, n, hφ, hψ⟩
      · have hxφ : IsXFreeClosed φ := (isXFreeClosed_or.mp hx).1
        have hxψ : IsXFreeClosed ψ := (isXFreeClosed_or.mp hx).2
        rcases hB with hg | hg | hB
        · exact Bound.head (Good.xfree hx ((trueN_or φ ψ).mpr
            (Or.inl ((Good_xfree_iff hxφ).mp hg)))) _
        · exact Bound.head (Good.xfree hx ((trueN_or φ ψ).mpr
            (Or.inr ((Good_xfree_iff hxψ).mp hg)))) _
        · exact Bound.tail (hB.mono le_rfl hle)
      · subst hφ; subst hψ
        rcases hB with hg | hg | hB
        · exact absurd hg not_good_negProg
        · exact Bound.head (Good.ti ev_TI_eq.symm
            (fun o => lt_of_lt_of_le (Good_allXat_iff.mp hg o) hle)) _
        · exact Bound.tail (hB.mono le_rfl hle)
      · subst hφ; subst hψ
        rcases hB with hg | hg | hB
        · have ht := (Good_xfree_iff (isXFreeClosed_ev_neg_precAt k n)).mp hg
          exact Bound.head (Good.precOrXat (ev_precOrXat_eq k n).symm
            (Or.inl ((trueN_ev_neg_precAt k n).mp ht))) _
        · exact Bound.head (Good.precOrXat (ev_precOrXat_eq k n).symm
            (Or.inr (((Good_xat_iff k).mp hg).mono hle))) _
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
          · exact Bound.head (Good.xfree hx ((trueN_and φ ψ).mpr
              ⟨(Good_xfree_iff hxφ).mp hg, (Good_xfree_iff hxψ).mp hg'⟩)) _
          · exact Bound.tail (hB'.mono le_rfl hle₂)
        · exact Bound.tail (hB.mono le_rfl hle₁)
      · subst hφ; subst hψ
        rcases hBp with hg | hB
        · rcases hBq with hg' | hB'
          · exact Bound.head (Good.pn (ev_P_eq n).symm ((Good_negXat_iff n).mp hg')
              (((Good_belowAt_iff n).mp hg).mono hle₁)) _
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
        have hprem : ∀ m, Good C γ (OrdinalNotation.nadd γ (OrdinalNotation.omegaPow (f m))) (evInst.inst φ m) := by
          intro m
          have hB := ih m (InCeSeq.of_all hC m) γ
          rw [Bound_cons] at hB
          exact hB.resolve_right (hno m)
        rcases InCe.all_cases (hC _ List.mem_cons_self) with hx | hφ | ⟨n, hφ⟩
        · refine Bound.head (Good.xfree hx ((trueN_all φ).mpr (fun m => ?_))) _
          exact (trueN_inst φ m).mp
            ((Good_xfree_iff (isXFreeClosed_inst hx m)).mp (hprem m))
        · subst hφ
          refine Bound.head (Good.allXat allXat_eq.symm (fun o => ?_)) _
          have hg := hprem (C.code o)
          rw [inst_allXat_body] at hg
          exact lt_of_lt_of_le ((Good_xat_iff _).mp hg o rfl) (hle _)
        · subst hφ
          refine Bound.head (Good.belowAt (ev_belowAt_eq n).symm (fun k hk => ?_)) _
          have hg := hprem k
          rw [inst_belowBody] at hg
          exact (((Good_precOrXat_iff k n).mp hg).resolve_left (not_not.mpr hk)).mono (hle k)
  | @exs α β φ Γ' m hlt _ ih =>
      intro hC γ
      have hle := nadd_omegaPow_le (γ := γ) hlt
      have hC' := InCeSeq.of_exs hC m
      rcases InCe.exs_cases (hC _ List.mem_cons_self) with hx | hφ
      · have hB := ih hC' γ
        rw [Bound_cons] at hB
        rcases hB with hg | hB
        · refine Bound.head (Good.xfree hx ((trueN_exs φ).mpr ⟨m, ?_⟩)) _
          exact (trueN_inst φ m).mp
            ((Good_xfree_iff (isXFreeClosed_inst_exs hx m)).mp hg)
        · exact Bound.tail (hB.mono le_rfl hle)
      · subst hφ
        have hB := ih hC' γ
        rw [inst_negProg_body, Bound_cons] at hB
        rcases hB with hg | hB
        · obtain ⟨-, hp⟩ := (Good_P_iff m).mp hg
          -- invoke the hypothesis again, above the counterexample
          have hB' := ih hC' (OrdinalNotation.succ (OrdinalNotation.nadd γ (OrdinalNotation.omegaPow β)))
          rw [inst_negProg_body, Bound_cons] at hB'
          rcases hB' with hg' | hB'
          · exact absurd (Small.of_predsSmall hp) ((Good_P_iff m).mp hg').1
          · refine Bound.tail (hB'.mono ?_ (bump_le hlt))
            exact le_trans (OrdinalNotation.le_nadd_left _ _) (OrdinalNotation.le_succ _)
        · exact Bound.tail (hB.mono le_rfl hle)
  | contraction ss _ ih =>
      intro hC γ
      exact (ih (InCeSeq.of_subset hC ss) γ).subset ss
  | cut hc _ _ _ _ _ _ =>
      exact absurd hc (Nat.not_lt_zero _)

/-- **`TI(≺)` has no cut-free derivation at any height.** -/
theorem not_derivable_TI (C : CodedOrder O) (α : O) :
    ¬ OmegaDerivable trueArithLits evInst 0 α [ev (TI C.prec)] := by
  intro h
  have hB := boundedness h (fun ψ hψ => by
    simp only [List.mem_singleton] at hψ
    subst hψ
    exact InCe.ti) α
  rw [Bound_cons] at hB
  rcases hB with hg | ⟨ψ, hψ, -⟩
  · exact lt_irrefl _ (Good_TI_iff.mp hg _)
  · simp at hψ

end OrdinalAnalysis.Gentzen.Boundedness
