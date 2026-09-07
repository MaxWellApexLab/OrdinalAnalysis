/-
  The climb: transfinite induction along a coded ordering is derivable.

  The boundedness lemma says a cut-free derivation of `¬Prog(X), X(n̄)` needs
  height at least the ordinal coded by `n`.  This file is its converse: such a
  derivation exists, at height about `ω^(o+1)` where `o` is that ordinal.  The
  derivation climbs — to prove `X(n̄)` it opens `¬Prog(X)` at `n`, which asks
  for `X(k̄)` for every `k ≺ n` (each obtained recursively) and for `¬X(n̄)`
  (closed by identity), and the ω-rule collects the `k`.

  Everything is generic in the coded ordering `C` and the notation system `O`
  that carries the heights, like the boundedness lemma.  Three facts about
  the ordering are consumed as hypotheses, because they are where the two
  instances differ:

  * every false instance `¬(k̄ ≺ n̄)` is derivable at one fixed height `K`
    (ω-completeness of true `X`-free sentences, whose height lives in
    `NONote` and is carried into `O` by a height map);
  * `K` and `1` lie below every `ω^(a+1)`;
  * both sides of a true `k ≺ n` are codes of notations (`precN_dom`).

  Without the last a number that is "internally normal" but codes nothing
  would have predecessors the climb cannot reach.
-/
import OrdinalAnalysis.Gentzen.Boundedness
import OrdinalAnalysis.Omega.Identity

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.Climb

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.StandardLX (trueArithLits)
open OrdinalAnalysis.Gentzen.LowerSyntax OrdinalAnalysis.Gentzen.LowerClass
open OrdinalAnalysis.Gentzen.Evaluate OrdinalAnalysis.Gentzen.EvInst
open OrdinalAnalysis.Gentzen.LowerClassEv

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- Cut-free derivability in the evaluating calculus. -/
abbrev D (α : O) (Γ : Sequent LX) : Prop := OmegaDerivable trueArithLits evInst 0 α Γ

/-- **The data of a climb** along the coded ordering `C`: a height `K` at
which every false instance of `≺` is derivable, below every `ω^(a+1)`
together with `1`; and the domain property of `≺`. -/
structure ClimbData (C : CodedOrder O) where
  K : O
  neg_precAt : ∀ {k n : ℕ}, ¬ C.precN k n →
    D K [ev (∼(precAt C.prec (numLX k) (numLX n)))]
  K_lt : ∀ a : O, K < OrdinalNotation.omegaPow (OrdinalNotation.nadd a OrdinalNotation.one)
  one_lt : ∀ a : O,
    OrdinalNotation.one < OrdinalNotation.omegaPow (OrdinalNotation.nadd a OrdinalNotation.one)
  dom : ∀ {k n : ℕ}, C.precN k n → (∃ o : O, C.code o = k) ∧ (∃ o : O, C.code o = n)

variable {C : CodedOrder O} (M : ClimbData C)

namespace ClimbData

/-- The height of the climb at `o`. -/
def height (o : O) : O :=
  OrdinalNotation.succ (OrdinalNotation.succ (OrdinalNotation.succ (OrdinalNotation.succ
    (OrdinalNotation.nadd
      (OrdinalNotation.omegaPow (OrdinalNotation.nadd o OrdinalNotation.one)) M.K))))

/-! ### One step of the climb -/

set_option maxHeartbeats 2000000 in
/-- **One step.**  If `X(k̄)` is derivable for every `k ≺ n` at height `δ`, and
`δ` is at least `K`, then `X(n̄)` is derivable at height `δ + 4`. -/
theorem core (n : ℕ) (δ : O) (hδ : M.K ≤ δ)
    (H : ∀ k, C.precN k n → D δ [ev (∼(Prog C.prec)), Xat (numLX k)]) :
    D (OrdinalNotation.succ (OrdinalNotation.succ (OrdinalNotation.succ
        (OrdinalNotation.succ δ))))
      [ev (∼(Prog C.prec)), Xat (numLX n)] := by
  -- the instances of `∀ y ≺ n̄, X y`
  have hprem : ∀ k, D (OrdinalNotation.succ δ)
      (evInst.inst (ev (belowBody C n)) k :: [ev (∼(Prog C.prec)), Xat (numLX n)]) := by
    intro k
    rw [inst_belowBody, ev_precOrXat_eq]
    refine OmegaDerivable.or (OrdinalNotation.lt_succ δ) ?_
    by_cases hk : C.precN k n
    · refine OmegaDerivable.contraction ?_ (H k hk)
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl rfl)
    · refine OmegaDerivable.contraction ?_ ((M.neg_precAt hk).mono_ord hδ)
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl
      exact Or.inl rfl
  have hbelow : D (OrdinalNotation.succ (OrdinalNotation.succ δ))
      (ev (LowerClass.belowAt C n) :: [ev (∼(Prog C.prec)), Xat (numLX n)]) := by
    rw [ev_belowAt_eq]
    exact OmegaDerivable.omegaRule (fun _ => OrdinalNotation.succ δ)
      (fun _ => OrdinalNotation.lt_succ _) hprem
  have hneg : D δ ((∼(Xat (numLX n))) :: [ev (∼(Prog C.prec)), Xat (numLX n)]) :=
    OmegaDerivable.of_mem_identity (Sum.inr XRel.X) ![numLX n]
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      List.mem_cons_self
  have hP : D (OrdinalNotation.succ (OrdinalNotation.succ (OrdinalNotation.succ δ)))
      (ev (LowerClass.P C n) :: [ev (∼(Prog C.prec)), Xat (numLX n)]) := by
    rw [ev_P_eq]
    exact OmegaDerivable.and (OrdinalNotation.lt_succ _)
      (OrdinalNotation.lt_succ_of_le
        ((OrdinalNotation.le_succ _).trans (OrdinalNotation.le_succ _))) hbelow hneg
  have hexs : D (OrdinalNotation.succ (OrdinalNotation.succ (OrdinalNotation.succ
      (OrdinalNotation.succ δ))))
      ((∃¹ (ev ((below C.prec) ⋏ ∼(Xat (#0 : Semiterm LX ℕ 1)))))
        :: [ev (∼(Prog C.prec)), Xat (numLX n)]) := by
    refine OmegaDerivable.exs n (OrdinalNotation.lt_succ _) ?_
    rw [inst_negProg_body]
    exact hP
  refine OmegaDerivable.drop_head hexs ?_
  rw [← ev_negProg_eq]
  exact List.mem_cons_self

/-! ### The heights -/

/-- The step of the heights: `height o' < ω^(o+1)` for `o' < o`. -/
theorem height_lt {o o' : O} (hlt : o' < o) :
    M.height o' < OrdinalNotation.omegaPow (OrdinalNotation.nadd o OrdinalNotation.one) := by
  have hw : OrdinalNotation.omegaPow (OrdinalNotation.nadd o' OrdinalNotation.one)
      < OrdinalNotation.omegaPow (OrdinalNotation.nadd o OrdinalNotation.one) :=
    OrdinalNotation.omegaPow_lt_omegaPow (OrdinalNotation.nadd_lt_nadd_left _ hlt)
  have hK := M.K_lt o
  have h1 := M.one_lt o
  simp only [height, OrdinalNotation.succ]
  exact OrdinalNotation.nadd_lt_omegaPow (OrdinalNotation.nadd_lt_omegaPow
    (OrdinalNotation.nadd_lt_omegaPow (OrdinalNotation.nadd_lt_omegaPow
      (OrdinalNotation.nadd_lt_omegaPow hw hK) h1) h1) h1) h1

theorem K_le_base (o : O) :
    M.K ≤ OrdinalNotation.nadd
      (OrdinalNotation.omegaPow (OrdinalNotation.nadd o OrdinalNotation.one)) M.K :=
  OrdinalNotation.le_nadd_right _ _

/-! ### The climb -/

/-- **The climb along the codes.**  For the code of `o`, height `height o`. -/
theorem code : ∀ o : O, D (M.height o) [ev (∼(Prog C.prec)), Xat (numLX (C.code o))] := by
  intro o
  refine WellFoundedLT.induction (motive := fun o =>
    D (M.height o) [ev (∼(Prog C.prec)), Xat (numLX (C.code o))]) o ?_
  intro o ih
  refine core M (C.code o) _ (M.K_le_base o) (fun k hk => ?_)
  obtain ⟨o', rfl⟩ := (M.dom hk).1
  have hlt : o' < o := C.lt_of_precN_code hk
  refine (ih o' hlt).mono_ord (le_of_lt ?_)
  exact lt_of_lt_of_le (M.height_lt hlt) (OrdinalNotation.le_nadd_left _ _)

/-- A number that codes nothing has no predecessors, so its climb is one step. -/
theorem nonimage (n : ℕ) (hn : ¬ ∃ o : O, C.code o = n) :
    D (OrdinalNotation.succ (OrdinalNotation.succ (OrdinalNotation.succ
        (OrdinalNotation.succ M.K))))
      [ev (∼(Prog C.prec)), Xat (numLX n)] :=
  core M n M.K le_rfl (fun _ hk => absurd (M.dom hk).2 hn)

include M in
/-- **The climb.**  `¬Prog(X), X(n̄)` is derivable for every `n`. -/
theorem climb (n : ℕ) : ∃ α : O, D α [ev (∼(Prog C.prec)), Xat (numLX n)] := by
  by_cases h : ∃ o : O, C.code o = n
  · obtain ⟨o, rfl⟩ := h
    exact ⟨_, M.code o⟩
  · exact ⟨_, M.nonimage n h⟩

end ClimbData

end OrdinalAnalysis.Gentzen.Climb
