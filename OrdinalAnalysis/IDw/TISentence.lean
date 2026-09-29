/- Source: OrdinalAnalysis/IDn/UpperBound.lean (the sentences) and IDn/UpperAuxForms.lean (`precW`); levels `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega. -/

/-
  **The transfinite-induction sentence of `ID_ω`**, shared by the lower bound
  (`IDw/LowerBound.lean`) and the upper bound.

  For a countable notation `a : ThetaVNoteD`, with `≺ = precW F` the internal order on normal domain
  codes (`F = Upper.orderFormulas`, `IDw/InternalFacts.lean`) and the free predicate `X` of `LXJ`,

      TI_a(≺, X)  :≡  Prog(≺, X) → ∀x (x ≺ ⌜a⌝ → X x)          (`tiUptoSentence F a`),
      Prog(≺, X)  :≡  ∀x ((∀y (y ≺ x → X y)) → X x)             (`progX F`),

  the shape of `IDn.Upper.tiUptoSentence`, in the language `LXJ` (one binary `J`, and `X`).

  **The ordinals.**  The analysis of `IDw WFormWc` reads

      (∀ a : ThetaVNoteD, a.1 < ThetaVTerm.Omega 0 → IDw WFormWc ⊢ tiUptoSentence F a) ∧
        ¬ IDw WFormWc ⊢ tiUptoSentence F (ThetaVNoteD.Omega 0),

  the unprovable bound being `Ω₁ = ThetaVNoteD.Omega 0`.  The ordinal `ψ₀(ε_{Ω_ω+1})` is *not* a
  single notation: it is the supremum of the countable notations, cofinally the terms
  `ϑ₀(ω_m(Ω_ω + 1))` (`Upper.exists_lt_tower`, `IDw/UpperAuxCof.lean`), so "TI up to every
  notation below `Ω₁`" says exactly that `ID_ω` proves TI up to `ψ₀(ε_{Ω_ω+1})`, while TI up to `Ω₁`
  itself is not provable.

  Contents.

    `OrderFormulas.fldWDef`, `precWDef`, `precW`, `eval_precWDef`   the order on the field
    `lm`                                                            arithmetic formulas in `LXJ`
    `precL`, `belowC`, `progX`, `tiUptoSentence`                    the sentences
    `eval_belowC`, `eval_progX`, `eval_tiUpto`                      the sentences in an arithmetically
                                                                    standard structure
-/
import OrdinalAnalysis.IDw.InternalFacts
import OrdinalAnalysis.IDw.Lift

set_option autoImplicit false

namespace OrdinalAnalysis.IDw.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.IDw.Internal
open OrdinalAnalysis.IDw.Lift (ArithStd Xmem eval_XatN)

/-! ### The order on the field -/

namespace OrderFormulas

variable (F : OrderFormulas)

/-- `fld(x)`: a normal domain code. -/
def fldWDef : 𝚺₁.Semisentence 1 := .mkSigma “x. !F.nfDef x ∧ !F.domDef x”

/-- `fld(y) ∧ fld(x) ∧ y ≺ x` (slot `0` the smaller element). -/
def precWDef : 𝚺₁.Semisentence 2 :=
  .mkSigma “y x. !F.nfDef y ∧ !F.domDef y ∧ !F.nfDef x ∧ !F.domDef x ∧ !F.ltDef y x”

/-- **The order of the upper bound**: `y ≺ x` on the field (normal domain codes). -/
def precW : Semisentence ℒₒᵣ 2 := F.precWDef.val

section Eval

variable {V : Type} [ORingStructure V]

@[simp] theorem eval_fldWDef (x : V) : F.fldWDef.val.Evalb ![x] ↔ F.fld x := by
  simp [fldWDef, fld]

@[simp] theorem eval_precWDef (y x : V) :
    F.precWDef.val.Evalb ![y, x] ↔ F.fld y ∧ F.fld x ∧ F.lt y x := by
  simp [precWDef, fld]
  tauto

end Eval

end OrderFormulas

/-! ### The sentences -/

section Sentences

variable (F : OrderFormulas)

/-- An arithmetic formula in `LXJ`. -/
abbrev lm {ξ : Type*} {m : ℕ} (φ : Semiformula ℒₒᵣ ξ m) : Semiformula LXJ ξ m :=
  Semiformula.lMap toLXJ φ

/-- `y ≺ x` (on the field) in `LXJ`, slot `0` the smaller element. -/
def precL : Semisentence LXJ 2 := lm (OrderFormulas.precW F)

/-- `x ≺ ⌜a⌝` in arithmetic. -/
def belowC (a : ThetaVNoteD) : Semisentence ℒₒᵣ 1 :=
  OrderFormulas.precW F ⇜ ![#0, ((code a.1 : ℕ) : Semiterm ℒₒᵣ Empty 1)]

/-- `Prog(≺, X) :≡ ∀x ((∀y ≺ x, X y) → X x)`. -/
def progX : Sentence LXJ :=
  ∀¹ ((∀¹ (precL F 🡒 Xat #0)) 🡒 Xat #0)

/-- **`TI_a(≺, X) :≡ Prog(≺, X) → ∀x (x ≺ ⌜a⌝ → X x)`**: transfinite induction for the free
predicate `X` along the ϑ-order up to `a`. -/
def tiUptoSentence (a : ThetaVNoteD) : Sentence LXJ :=
  progX F 🡒 ∀¹ (lm (belowC F a) 🡒 Xat #0)

end Sentences

/-! ### The sentences in an arithmetically standard structure -/

section Eval

variable {F : OrderFormulas}
variable {N : Type} [ORingStructure N] [s : Structure LXJ N] [ArithStd N]
  [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

omit s [ArithStd N] in
theorem eval_belowC (a : ThetaVNoteD) (x : N) :
    Semiformula.Evalb (M := N) ![x] (belowC F a) ↔
      F.fld x ∧ F.fld (mc (V := N) a.1) ∧ F.lt x (mc (V := N) a.1) := by
  unfold belowC
  rw [Semiformula.eval_substs]
  have e : (Semiterm.val (M := N) ![x] Empty.elim ∘
      ![(#0 : Semiterm ℒₒᵣ Empty 1), ((code a.1 : ℕ) : Semiterm ℒₒᵣ Empty 1)])
        = ![x, mc (V := N) a.1] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => k.elim0) j
      simp [numeral_eq_natCast, mc]
  rw [e]
  exact OrderFormulas.eval_precWDef F x _

omit [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- **`Prog(≺, X)` in `N`.** -/
theorem eval_progX :
    Semiformula.Eval (s := s) ![] Empty.elim (progX F) ↔
      ∀ x : N, (∀ y, F.fld y → F.fld x → F.lt y x → Xmem (s := s) y) → Xmem (s := s) x := by
  unfold progX
  rw [Semiformula.eval_all]
  refine forall_congr' fun x => ?_
  rw [LogicalConnective.HomClass.map_imply, Semiformula.eval_all, eval_XatN]
  refine imp_congr (forall_congr' fun y => ?_) Iff.rfl
  rw [LogicalConnective.HomClass.map_imply, eval_XatN, precL, lm, Lift.eval_lMap]
  have e : (y :> x :> ![] : Fin 2 → N) = ![y, x] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    rfl
  rw [e]
  show (F.precWDef.val.Evalb ![y, x] → _) ↔ _
  rw [OrderFormulas.eval_precWDef]
  constructor
  · intro h hy hx hlt; exact h ⟨hy, hx, hlt⟩
  · rintro h ⟨hy, hx, hlt⟩; exact h hy hx hlt

/-- **`TI_a(≺, X)` in `N`.** -/
theorem eval_tiUpto (a : ThetaVNoteD) :
    Semiformula.Eval (s := s) ![] Empty.elim (tiUptoSentence F a) ↔
      ((∀ x : N, (∀ y, F.fld y → F.fld x → F.lt y x → Xmem (s := s) y) → Xmem (s := s) x) →
        ∀ x : N, F.fld x ∧ F.fld (mc (V := N) a.1) ∧ F.lt x (mc (V := N) a.1) →
          Xmem (s := s) x) := by
  unfold tiUptoSentence
  rw [LogicalConnective.HomClass.map_imply, eval_progX, Semiformula.eval_all]
  refine imp_congr Iff.rfl (forall_congr' fun x => ?_)
  rw [LogicalConnective.HomClass.map_imply, eval_XatN, lm, Lift.eval_lMap]
  exact imp_congr (eval_belowC a x) Iff.rfl

end Eval

end OrdinalAnalysis.IDw.Upper
