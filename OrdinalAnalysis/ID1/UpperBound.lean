/-
  The upper bound of the Bachmann–Howard analysis of `ID₁`: transfinite induction along the
  ϑ-order up to every notation below `Ω` is provable.

  Source: T. Arai, *Lectures on ordinal analysis*, arXiv:2304.00246, §1.6 (the well-ordering
  proof in `ID₁` through the accessible part and Buchholz's distinguished classes), for the
  ϑ-notation of A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Definition 3.1.

  **The sentence.**  For a notation `a`, in the shape of `LowerBound.tiFieldSentence` (the same
  `Prog(≺, X)`, the same `≺ = precC`, the same free predicate `X`):

      TI_a(≺, X)  :≡  Prog(≺, X) → ∀x (x ≺ ⌜a⌝ → X x)          (`tiUptoSentence a`),

  so that `TI_Ω(≺, X)` is `tiUptoSentence Ω` (`tiUptoSentence_Omega`).

  **The proof** (`id1_upper_bound`), in an arbitrary arithmetically standard model `N` of
  `ID1Acc precC` (completeness, `provable_of_models`): by the cofinality lemma, `a ≺ ϑ(τ_n)`
  for a standard `n`, where `τ_n` codes `ω_n(Ω + 1)`; `ϑ(τ_n)` lies in the extension `W` of
  `I` (`WellOrdering.W_theta_tau`); `W` is downward closed, so every `x ≺ ⌜a⌝` is in `W`; and
  the induction scheme of `I` at the formula `X x` turns `Prog(≺, X)` into `W ⊆ X`.
-/
import OrdinalAnalysis.ID1.Bridge
import OrdinalAnalysis.ID1.LowerBound

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

namespace UpperBound

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.ID1.Internal
open Lift (ArithStd precM Imem Xmem provable_of_models models_iSigma₁ ind_definable definable_xmem)
open LowerBound (precLXI progX tiFieldSentence)

/-! ### The sentences -/

/-- `x ≺ ⌜a⌝` in arithmetic. -/
def belowC (a : ThetaNote) : Semisentence ℒₒᵣ 1 :=
  precC ⇜ ![#0, ((codeNote a : ℕ) : Semiterm ℒₒᵣ Empty 1)]

/-- `x ≺ ⌜a⌝` in `LXI`. -/
def below (a : ThetaNote) : Semisentence LXI 1 := Semiformula.lMap toLXI (belowC a)

/-- **`TI_a(≺, X) :≡ Prog(≺, X) → ∀x (x ≺ ⌜a⌝ → X x)`**: transfinite induction for the free
predicate `X` along the ϑ-order up to `a`. -/
def tiUptoSentence (a : ThetaNote) : Sentence LXI :=
  progX 🡒 ∀¹ (below a 🡒 Xat #0)

/-- The sentence of the lower bound is the instance `a = Ω`. -/
theorem tiUptoSentence_Omega : tiUptoSentence ThetaNote.Omega = tiFieldSentence := rfl

/-! ### The sentences in an arithmetically standard model -/

section Model

variable {N : Type*} [ORingStructure N] [Structure LXI N] [ArithStd N] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

omit [Structure LXI N] [ArithStd N] in
theorem eval_belowC (a : ThetaNote) (x : N) :
    Semiformula.Evalb (M := N) ![x] (belowC a) ↔ precM precC x (mc (V := N) a.1) := by
  unfold belowC precM
  rw [Semiformula.eval_substs]
  have e : (Semiterm.val (M := N) ![x] Empty.elim ∘
      ![(#0 : Semiterm ℒₒᵣ Empty 1), ((codeNote a : ℕ) : Semiterm ℒₒᵣ Empty 1)])
        = ![x, mc (V := N) a.1] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => k.elim0) j
      simp [numeral_eq_natCast, codeNote, mc]
  rw [e]

omit [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem eval_precLXI (y x : N) :
    Semiformula.Eval (M := N) ![y, x] Empty.elim precLXI ↔ precM precC y x := by
  rw [precLXI, Lift.eval_lMap_toLXI]
  rfl

omit [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- **`Prog(≺, X)` in `N`.** -/
theorem eval_progX :
    Semiformula.Eval (M := N) ![] Empty.elim progX ↔
      ∀ x : N, (∀ y, precM precC y x → Xmem y) → Xmem x := by
  unfold progX
  rw [Semiformula.eval_all]
  refine forall_congr' fun x => ?_
  rw [LogicalConnective.HomClass.map_imply, Semiformula.eval_all, Lift.eval_Xat]
  refine imp_congr (forall_congr' fun y => ?_) Iff.rfl
  rw [LogicalConnective.HomClass.map_imply, Lift.eval_Xat]
  have e : (y :> x :> ![] : Fin 2 → N) = ![y, x] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    rfl
  rw [e, eval_precLXI]
  rfl

/-- **`TI_a(≺, X)` in `N`.** -/
theorem eval_tiUpto (a : ThetaNote) :
    Semiformula.Eval (M := N) ![] Empty.elim (tiUptoSentence a) ↔
      ((∀ x : N, (∀ y, precM precC y x → Xmem y) → Xmem x) →
        ∀ x : N, precM precC x (mc (V := N) a.1) → Xmem x) := by
  unfold tiUptoSentence
  rw [LogicalConnective.HomClass.map_imply, eval_progX, Semiformula.eval_all]
  refine imp_congr Iff.rfl (forall_congr' fun x => ?_)
  rw [LogicalConnective.HomClass.map_imply, Lift.eval_Xat, below, Lift.eval_lMap_toLXI]
  exact imp_congr (eval_belowC a x) Iff.rfl

end Model

/-! ### The upper bound -/

/-- **The upper bound of the Bachmann–Howard analysis of `ID₁`**: for every notation `a ≺ Ω`,
`ID₁` for the accessibility operator of the coded ϑ-order proves transfinite induction for the
free predicate `X` up to `a`,

    ID1Acc precC ⊢ Prog(≺, X) → ∀x (x ≺ ⌜a⌝ → X x). -/
theorem id1_upper_bound {a : ThetaNote} (ha : a < ThetaNote.Omega) :
    ID1Acc precC ⊢ tiUptoSentence a := by
  apply provable_of_models precC
  intro N _ _ _ hN
  have : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_iSigma₁ precC
  rw [models_iff]
  refine (eval_tiUpto a).mpr fun hprog x hx => ?_
  obtain ⟨n, -, hlt⟩ := WellOrdering.exists_lt_theta_tau (V := N) ha
  rw [WellOrdering.precM_iff] at hx
  have hnf : isNF (tcTheta (WellOrdering.tau n : N)) :=
    (isNF_tcTheta_iff _).mpr (WellOrdering.tau_facts n).1
  have hWx : Imem x :=
    WellOrdering.W_down (WellOrdering.W_theta_tau n) hnf hx.1 (iltb_trans hx.2.2 hlt)
  exact ind_definable precC definable_xmem hprog x hWx

end UpperBound

end InductiveDef

end OrdinalAnalysis
