/-
  The lower bound for `ID₁(Acc)`: transfinite induction along the ϑ-order up to `Ω` is
  not provable, given the embedding theorem.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Corollary 7.2 and Proposition 5.8, with Theorem 5.9
  (boundedness).  The reduction of `TI(≺, X)` to the accessible part is the usual one for
  `ID₁`: read `X` as `I`.

  **The sentence.**  `≺` is `precC`, the coded order of the normal forms of the ϑ-notation,
  and `⌜Ω⌝` the numeral of the code of `Ω`.  In the shape of `Gentzen.TIupto`,

      Prog(≺, X)    :≡  ∀x (∀y (y ≺ x → X y) → X x),
      TI_Ω(≺, X)    :≡  Prog(≺, X) → ∀x (x ≺ ⌜Ω⌝ → X x)       (`tiFieldSentence`).

  The notations `≺ Ω` are the field of the accessibility order (`Internal.ThetaField`), so
  `TI_Ω` is transfinite induction for the free predicate `X` along the ϑ-order on its field.
  `Prog(≺, X)` is the closure axiom of `ID1Acc precC` with `I` replaced by `X`
  (`lMap_swap_progX`).

  **Why `X` is read as `I` first.**  The embedding of `TI_Ω(≺, X)` is `Σ(Ω)` and has no
  parameters (`sigmaOmega_embed_ti`, `params_embed_ti`), but no stage model refutes it:
  the order is well founded, so `TI_Ω(≺, P)` holds in `ℕ` for every reading `P` of `X`.  The
  argument therefore reads `X` as `I` inside `ID₁` (`provable_fieldInI_of_ti`): in a model
  of `ID1Acc precC`, reinterpreting `X` by the extension of `I` gives again a model of
  `ID1Acc precC` (every axiom stays true), in which `Prog(≺, X)` is the closure
  axiom; hence `ID1Acc precC ⊢ TI_Ω(≺, X)` gives

      ID1Acc precC ⊢ ∀x (x ≺ ⌜Ω⌝ → I x)                        (`fieldInI`),

  an `X`-free positive sentence, whose embedding is `Σ(Ω)`.

  **The refutation** (`not_derivable_fieldInI`).  Suppose
  `H_0 ⊢^β_{Ω+m} ∀x (x ≺ ⌜Ω⌝ → I^{≺Ω} x)`.  Corollary 7.2 gives
  `H_η ⊢^{ϑη}_{ϑη} ∀x (x ≺ ⌜Ω⌝ → I^{≺Ω} x)` with `η = ω_{m+1}(β)` and `ϑη ≺ Ω`; boundedness
  (Theorem 5.9) at the stage `ϑη` gives `H_η ⊢^{ϑη}_{ϑη} ∀x (x ≺ ⌜Ω⌝ → I^{≺ϑη} x)`; the
  height is below `Ω`, so by soundness (Proposition 5.8) the sentence is true in the stage
  model.  **The interpretation**: `X` is read by any predicate `P` (it does not occur), and
  `I^{≺γ}` by the stage `S_γ` of the accessible part, whose codes are exactly those of the
  notations `≺ γ` (`StageSem.codeNote_mem_stageSet_acc`).  **The stage bound**: `γ = ϑη`,
  the height of the collapsed derivation.  At `x = code(ϑη)`, which is `≺ ⌜Ω⌝`, truth would
  put `code(ϑη)` into `S_{ϑη}`, i.e. `ϑη ≺ ϑη`.

  **The embedding as a hypothesis.**  The embedding theorem (Freund, Theorem 6.5:
  `ID₁ ⊢ σ ⇒ H_0 ⊢^{Ω·2+m}_{Ω+n} σ`) enters as a hypothesis.  It is only applied to the
  `X`-free sentence `fieldInI` (`id1_lower_bound_of_embedding_xfree`), so it may be assumed
  for `X`-free sentences only; the form with all sentences
  (`id1_lower_bound_of_embedding`) is a corollary.

  Contents.

    `precLXI`, `belowOmegaC`, `belowOmega`, `progX`, `tiFieldSentence`, `fieldInI`
    `NoX`, `swapXI`                        `X`-free formulas; the reinterpretation `X ↦ I`
    `lMap_swap_of_noX`, `lMap_swap_substI`, `lMap_swap_succInd`, `lMap_swap_progX`
    `eval_swap_of_mem_ID1Acc`              the reinterpretation maps models to models
    `provable_fieldInI_of_ti`              `TI_Ω(≺, X) ⊢ ∀x (x ≺ ⌜Ω⌝ → I x)` over `ID1Acc`
    `eval_progX_stdI`, `eval_ti_stdI`, `eval_fieldInI_stdI`   the sentences in the standard
                                           structures
    `NoI`, `sigmaOmega_embed_ti`, `params_embed_ti`, `sigmaOmega_embed_fieldInI`
    `trueS_capped_fieldInI`                the bounded sentence in the stage model
    `not_derivable_fieldInI`               **no derivation of the embedded sentence**
    `id1_lower_bound_of_embedding_xfree`, `id1_lower_bound_of_embedding`,
    `not_provable_fieldInI_of_embedding`   the lower bound, given the embedding
-/
import OrdinalAnalysis.ID1.StageSemantics
import OrdinalAnalysis.ID1.Elimination
import Foundation.FirstOrder.Completeness

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

namespace LowerBound

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.ID1.Internal

/-! ### The sentences -/

/-- `y ≺ x` in `LXI`, slot `#0` the smaller element (as in `accForm`). -/
def precLXI : Semisentence LXI 2 := Semiformula.lMap toLXI precC

/-- `x ≺ ⌜Ω⌝` in arithmetic: the field of the accessibility order. -/
def belowOmegaC : Semisentence ℒₒᵣ 1 :=
  precC ⇜ ![#0, ((codeNote ThetaNote.Omega : ℕ) : Semiterm ℒₒᵣ Empty 1)]

/-- `x ≺ ⌜Ω⌝` in `LXI`. -/
def belowOmega : Semisentence LXI 1 := Semiformula.lMap toLXI belowOmegaC

/-- `Prog(≺, X) :≡ ∀x (∀y (y ≺ x → X y) → X x)`. -/
def progX : Sentence LXI :=
  ∀¹ ((∀¹ (precLXI 🡒 Xat #0)) 🡒 Xat #0)

/-- **`TI_Ω(≺, X) :≡ Prog(≺, X) → ∀x (x ≺ ⌜Ω⌝ → X x)`**: transfinite induction for the free
predicate `X` along the ϑ-order on its field `{x | x ≺ ⌜Ω⌝}`. -/
def tiFieldSentence : Sentence LXI :=
  progX 🡒 ∀¹ (belowOmega 🡒 Xat #0)

/-- `∀x (x ≺ ⌜Ω⌝ → I x)`: the field lies in the accessible part. -/
def fieldInI : Sentence LXI :=
  ∀¹ (belowOmega 🡒 Iat #0)

/-! ### `X`-free formulas -/

/-- `X` does not occur. -/
def NoX {ξ : Type*} : {n : ℕ} → Semiformula LXI ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel (Sum.inl _) _ => True
  | _, .rel (Sum.inr IXRel.X) _ => False
  | _, .rel (Sum.inr IXRel.I) _ => True
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr IXRel.X) _ => False
  | _, .nrel (Sum.inr IXRel.I) _ => True
  | _, .and φ ψ => NoX φ ∧ NoX ψ
  | _, .or φ ψ => NoX φ ∧ NoX ψ
  | _, .all φ => NoX φ
  | _, .exs φ => NoX φ

section NoX

variable {ξ : Type*}

theorem noX_neg : ∀ {n : ℕ} (φ : Semiformula LXI ξ n), NoX (∼φ) ↔ NoX φ
  | _, .verum => Iff.rfl
  | _, .falsum => Iff.rfl
  | _, .rel (Sum.inl _) _ => Iff.rfl
  | _, .rel (Sum.inr IXRel.X) _ => Iff.rfl
  | _, .rel (Sum.inr IXRel.I) _ => Iff.rfl
  | _, .nrel (Sum.inl _) _ => Iff.rfl
  | _, .nrel (Sum.inr IXRel.X) _ => Iff.rfl
  | _, .nrel (Sum.inr IXRel.I) _ => Iff.rfl
  | _, .and φ ψ => and_congr (noX_neg φ) (noX_neg ψ)
  | _, .or φ ψ => and_congr (noX_neg φ) (noX_neg ψ)
  | _, .all φ => noX_neg φ
  | _, .exs φ => noX_neg φ

/-- `X`-freeness does not see terms. -/
theorem noX_rew {ξ₂ : Type*} : ∀ {n₁ n₂ : ℕ} (ω : Rew LXI ξ n₁ ξ₂ n₂)
    (φ : Semiformula LXI ξ n₁), NoX (ω ▹ φ) ↔ NoX φ
  | _, _, _, .verum => Iff.rfl
  | _, _, _, .falsum => Iff.rfl
  | _, _, _, .rel (Sum.inl _) _ => Iff.rfl
  | _, _, _, .rel (Sum.inr IXRel.X) _ => Iff.rfl
  | _, _, _, .rel (Sum.inr IXRel.I) _ => Iff.rfl
  | _, _, _, .nrel (Sum.inl _) _ => Iff.rfl
  | _, _, _, .nrel (Sum.inr IXRel.X) _ => Iff.rfl
  | _, _, _, .nrel (Sum.inr IXRel.I) _ => Iff.rfl
  | _, _, ω, .and φ ψ => by
    rw [show (Semiformula.and φ ψ) = φ ⋏ ψ from rfl, LogicalConnective.HomClass.map_and]
    exact and_congr (noX_rew ω φ) (noX_rew ω ψ)
  | _, _, ω, .or φ ψ => by
    rw [show (Semiformula.or φ ψ) = φ ⋎ ψ from rfl, LogicalConnective.HomClass.map_or]
    exact and_congr (noX_rew ω φ) (noX_rew ω ψ)
  | _, _, ω, .all φ => by
    rw [show (Semiformula.all φ) = ∀¹ φ from rfl, Rewriting.app_all]
    exact noX_rew ω.q φ
  | _, _, ω, .exs φ => by
    rw [show (Semiformula.exs φ) = ∃¹ φ from rfl, Rewriting.app_exs]
    exact noX_rew ω.q φ

/-- Arithmetic formulas are `X`-free. -/
theorem noX_lMap_toLXI : ∀ {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n), NoX (Semiformula.lMap toLXI φ)
  | _, .verum => trivial
  | _, .falsum => trivial
  | _, .rel _ _ => trivial
  | _, .nrel _ _ => trivial
  | _, .and φ ψ => ⟨noX_lMap_toLXI φ, noX_lMap_toLXI ψ⟩
  | _, .or φ ψ => ⟨noX_lMap_toLXI φ, noX_lMap_toLXI ψ⟩
  | _, .all φ => noX_lMap_toLXI φ
  | _, .exs φ => noX_lMap_toLXI φ

theorem noX_Iat {n : ℕ} (t : Semiterm LXI ξ n) : NoX (Iat t) := trivial

end NoX

/-! ### The reinterpretation `X ↦ I` -/

/-- `X ↦ I`; arithmetic and `I` are fixed. -/
def swapRel : {k : ℕ} → LXI.Rel k → LXI.Rel k
  | _, Sum.inl r => Sum.inl r
  | _, Sum.inr IXRel.X => Sum.inr IXRel.I
  | _, Sum.inr IXRel.I => Sum.inr IXRel.I

/-- **The reinterpretation of `X` by `I`**, as an endomorphism of `LXI`. -/
def swapXI : LXI →ᵥ LXI := ⟨fun f => f, swapRel⟩

section Swap

variable {ξ : Type*}

/-- Terms are fixed. -/
@[simp] theorem lMap_swap_term {n : ℕ} (t : Semiterm LXI ξ n) :
    Semiterm.lMap swapXI t = t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih =>
    rw [Semiterm.lMap_func]
    congr 1
    funext i
    exact ih i

theorem lMap_swap_rel {k n : ℕ} (r : LXI.Rel k) (v : Fin k → Semiterm LXI ξ n) :
    Semiformula.lMap swapXI (Semiformula.rel r v) = Semiformula.rel (swapRel r) v := by
  rw [Semiformula.lMap_rel]
  congr 1
  funext i
  simp

theorem lMap_swap_nrel {k n : ℕ} (r : LXI.Rel k) (v : Fin k → Semiterm LXI ξ n) :
    Semiformula.lMap swapXI (Semiformula.nrel r v) = Semiformula.nrel (swapRel r) v := by
  rw [Semiformula.lMap_nrel]
  congr 1
  funext i
  simp

/-- `X t ↦ I t`. -/
theorem lMap_swap_Xat {n : ℕ} (t : Semiterm LXI ξ n) :
    Semiformula.lMap swapXI (Xat t) = Iat t :=
  lMap_swap_rel _ _

/-- `X`-free formulas are fixed. -/
theorem lMap_swap_of_noX : ∀ {n : ℕ} (φ : Semiformula LXI ξ n), NoX φ →
    Semiformula.lMap swapXI φ = φ
  | _, .verum, _ => rfl
  | _, .falsum, _ => rfl
  | _, .rel (Sum.inl _) v, _ => lMap_swap_rel _ v
  | _, .rel (Sum.inr IXRel.I) v, _ => lMap_swap_rel _ v
  | _, .nrel (Sum.inl _) v, _ => lMap_swap_nrel _ v
  | _, .nrel (Sum.inr IXRel.I) v, _ => lMap_swap_nrel _ v
  | _, .and φ ψ, h => by
    rw [show (Semiformula.and φ ψ) = φ ⋏ ψ from rfl, LogicalConnective.HomClass.map_and,
      lMap_swap_of_noX φ h.1, lMap_swap_of_noX ψ h.2]
  | _, .or φ ψ, h => by
    rw [show (Semiformula.or φ ψ) = φ ⋎ ψ from rfl, LogicalConnective.HomClass.map_or,
      lMap_swap_of_noX φ h.1, lMap_swap_of_noX ψ h.2]
  | _, .all φ, h => by
    rw [show (Semiformula.all φ) = ∀¹ φ from rfl, Semiformula.lMap_all, lMap_swap_of_noX φ h]
  | _, .exs φ, h => by
    rw [show (Semiformula.exs φ) = ∃¹ φ from rfl, Semiformula.lMap_exs, lMap_swap_of_noX φ h]

/-- On an `X`-free formula, `X ↦ I` commutes with `I ↦ F`. -/
theorem lMap_swap_substI (F : Semiformula LXI ξ 1) : ∀ {n : ℕ} (φ : Semiformula LXI ξ n),
    NoX φ → Semiformula.lMap swapXI (substI F φ) = substI (Semiformula.lMap swapXI F) φ
  | _, .verum, _ => rfl
  | _, .falsum, _ => rfl
  | _, .rel (Sum.inl r) v, h => lMap_swap_of_noX (.rel (Sum.inl r) v) h
  | _, .rel (Sum.inr IXRel.I) v, _ => by
    show Semiformula.lMap swapXI (F/[v 0]) = (Semiformula.lMap swapXI F)/[v 0]
    rw [Semiformula.lMap_subst]
    congr 1
    funext i
    simp
  | _, .nrel (Sum.inl r) v, h => lMap_swap_of_noX (.nrel (Sum.inl r) v) h
  | _, .nrel (Sum.inr IXRel.I) v, _ => by
    show Semiformula.lMap swapXI (∼(F/[v 0])) = ∼((Semiformula.lMap swapXI F)/[v 0])
    rw [LogicalConnective.HomClass.map_neg, Semiformula.lMap_subst]
    congr 2
    funext i
    simp
  | _, .and φ ψ, h => by
    show Semiformula.lMap swapXI (substI F φ ⋏ substI F ψ) = _
    rw [LogicalConnective.HomClass.map_and, lMap_swap_substI F φ h.1,
      lMap_swap_substI F ψ h.2]
    rfl
  | _, .or φ ψ, h => by
    show Semiformula.lMap swapXI (substI F φ ⋎ substI F ψ) = _
    rw [LogicalConnective.HomClass.map_or, lMap_swap_substI F φ h.1,
      lMap_swap_substI F ψ h.2]
    rfl
  | _, .all φ, h => by
    show Semiformula.lMap swapXI (∀¹ substI F φ) = _
    rw [Semiformula.lMap_all, lMap_swap_substI F φ h]
    rfl
  | _, .exs φ, h => by
    show Semiformula.lMap swapXI (∃¹ substI F φ) = _
    rw [Semiformula.lMap_exs, lMap_swap_substI F φ h]
    rfl

/-- The induction axiom is mapped to the induction axiom. -/
theorem lMap_swap_succInd (φ : Semiformula LXI ξ 1) :
    Semiformula.lMap swapXI (succInd φ) = succInd (Semiformula.lMap swapXI φ) := by
  simp [succInd, Semiformula.lMap_subst, Matrix.comp₁]

end Swap

/-! ### The reinterpretation maps models of `ID1Acc precC` to models -/

section Models

theorem noX_precLXI : NoX precLXI := noX_lMap_toLXI precC

theorem noX_belowOmega : NoX belowOmega := noX_lMap_toLXI belowOmegaC

theorem noX_accForm : NoX (accForm precC) :=
  ⟨(noX_neg _).mpr (noX_lMap_toLXI precC), trivial⟩

theorem noX_closureAx : NoX (closureAx (accForm precC)) :=
  ⟨(noX_neg _).mpr noX_accForm, trivial⟩

/-- `Prog(≺, X)` becomes the closure axiom. -/
theorem lMap_swap_progX : Semiformula.lMap swapXI progX = closureAx (accForm precC) := by
  unfold progX closureAx accForm
  simp only [Semiformula.lMap_all, LogicalConnective.HomClass.map_imply, lMap_swap_Xat]
  rw [lMap_swap_of_noX _ noX_precLXI]
  rfl

/-- `TI_Ω(≺, X)` becomes `closure → ∀x (x ≺ ⌜Ω⌝ → I x)`. -/
theorem lMap_swap_ti :
    Semiformula.lMap swapXI tiFieldSentence = (closureAx (accForm precC) 🡒 fieldInI) := by
  unfold tiFieldSentence fieldInI
  rw [LogicalConnective.HomClass.map_imply, lMap_swap_progX, Semiformula.lMap_all,
    LogicalConnective.HomClass.map_imply, lMap_swap_Xat, lMap_swap_of_noX _ noX_belowOmega]

/-- `A(F, x)` for the accessibility form commutes with the reinterpretation. -/
theorem lMap_swap_opAt (F : Semiformula LXI ℕ 1) :
    Semiformula.lMap swapXI (opAt (accForm precC) F) =
      opAt (accForm precC) (Semiformula.lMap swapXI F) := by
  unfold opAt
  exact lMap_swap_substI F _ ((noX_rew _ _).mpr noX_accForm)

/-- The induction scheme for `I` at `F` is mapped to the scheme at `F` reinterpreted
(before the universal closure). -/
theorem lMap_swap_indBody (F : Semiformula LXI ℕ 1) :
    Semiformula.lMap swapXI ((∀¹ (opAt (accForm precC) F 🡒 F)) 🡒 ∀¹ (Iat #0 🡒 F)) =
      ((∀¹ (opAt (accForm precC) (Semiformula.lMap swapXI F) 🡒 Semiformula.lMap swapXI F)) 🡒
        ∀¹ (Iat #0 🡒 Semiformula.lMap swapXI F)) := by
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.lMap_all]
  rw [lMap_swap_opAt, lMap_swap_of_noX (Iat #0) (noX_Iat _)]

variable {M : Type} [Nonempty M] (s : Structure LXI M)

/-- Truth of a universal closure after the reinterpretation. -/
theorem eval_swap_univCl (φ : Proposition LXI) :
    Semiformula.Eval (s := s.lMap swapXI) ![] Empty.elim (Semiformula.univCl φ) ↔
      Semiformula.Eval (s := s) ![] Empty.elim
        (Semiformula.univCl (Semiformula.lMap swapXI φ)) := by
  have h1 := Semiformula.eval_univCl (s := s.lMap swapXI) (M := M) φ
  have h2 := Semiformula.eval_univCl (s := s) (M := M) (Semiformula.lMap swapXI φ)
  refine h1.trans (Iff.trans ?_ h2.symm)
  refine forall_congr' fun f => ?_
  exact Semiformula.eval_lMap.symm

/-- **Every axiom of `ID1Acc precC` stays true when `X` is read as `I`.**  Equality is read
as equality in `M`. -/
theorem eval_swap_of_mem_ID1Acc (hEq : ∀ a b : M,
      s.rel (Language.Eq.eq : LXI.Rel 2) ![a, b] ↔ a = b)
    (hM : ∀ σ ∈ ID1Acc precC, Semiformula.Eval (s := s) ![] Empty.elim σ)
    {σ : Sentence LXI} (hσ : σ ∈ ID1Acc precC) :
    Semiformula.Eval (s := s.lMap swapXI) ![] Empty.elim σ := by
  rcases (mem_ID1 (accForm precC)).mp hσ with h | h | h | rfl | ⟨F, rfl⟩
  · let _ : Structure LXI M := s.lMap swapXI
    have _ : Structure.Eq LXI M := ⟨fun a b => hEq a b⟩
    have := Structure.Eq.models_eq LXI M
    exact Theory.models M (𝗘𝗤 LXI) h
  · obtain ⟨τ, hτ, rfl⟩ := h
    rw [Semiformula.eval_lMap]
    have h' := hM _ (mem_ID1_of_paMinus (accForm precC) hτ)
    rw [Semiformula.eval_lMap] at h'
    exact h'
  · obtain ⟨φ, -, rfl⟩ := h
    rw [eval_swap_univCl, lMap_swap_succInd]
    exact hM _ (succInd_mem_ID1 (accForm precC) _)
  · rw [← Semiformula.eval_lMap, lMap_swap_of_noX _ noX_closureAx]
    exact hM _ (closureAx_mem_ID1 (accForm precC))
  · unfold indAx
    rw [eval_swap_univCl, lMap_swap_indBody]
    exact hM _ (indAx_mem_ID1 (accForm precC) _)

end Models

/-! ### From `TI_Ω(≺, X)` to `∀x (x ≺ ⌜Ω⌝ → I x)` -/

section Provable

/-- A sentence provable in `ID1Acc precC` is true in every structure satisfying its
axioms (soundness, in the form used below). -/
theorem eval_of_provable_of_axioms {M : Type} [Nonempty M] (s : Structure LXI M)
    (hM : ∀ σ ∈ ID1Acc precC, Semiformula.Eval (s := s) ![] Empty.elim σ) {σ : Sentence LXI}
    (h : ID1Acc precC ⊢ σ) : Semiformula.Eval (s := s) ![] Empty.elim σ := by
  let _ : Structure LXI M := s
  have hT : M↓[LXI] ⊧* ID1Acc precC :=
    Semantics.modelsSet_iff.mpr fun τ hτ => models_iff.mpr (hM τ hτ)
  exact models_iff.mp (models_of_provable hT h)

/-- **Reading `X` as `I`**: if `ID1Acc precC` proves `TI_Ω(≺, X)`, it proves that the field
lies in the accessible part.  In a model of `ID1Acc precC`, the structure with `X` read as
the extension of `I` is again a model (`eval_swap_of_mem_ID1Acc`); there `TI_Ω(≺, X)` holds,
and it says `closure → ∀x (x ≺ ⌜Ω⌝ → I x)` of the original model (`lMap_swap_ti`). -/
theorem provable_fieldInI_of_ti (h : ID1Acc precC ⊢ tiFieldSentence) :
    ID1Acc precC ⊢ fieldInI := by
  have _ : 𝗘𝗤 LXI ⪯ ID1Acc precC := eq_weakerThan_ID1 (accForm precC)
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq]
  intro M _ s hEq hM
  have hAx : ∀ σ ∈ ID1Acc precC, Semiformula.Eval (s := s) ![] Empty.elim σ :=
    fun σ hσ => models_iff.mp ((Semantics.modelsSet_iff.mp hM) hσ)
  have hEq' : ∀ a b : M, s.rel (Language.Eq.eq : LXI.Rel 2) ![a, b] ↔ a = b :=
    fun a b => hEq.eq a b
  have hswap := eval_of_provable_of_axioms (s.lMap swapXI)
    (fun σ hσ => eval_swap_of_mem_ID1Acc s hEq' hAx hσ) h
  rw [← Semiformula.eval_lMap, lMap_swap_ti, LogicalConnective.HomClass.map_imply] at hswap
  exact models_iff.mpr (hswap (hAx _ (closureAx_mem_ID1 (accForm precC))))

end Provable

/-! ### The sentences in the standard structures -/

section Standard

theorem eval_belowOmegaC (x : ℕ) :
    Semiformula.Eval (M := ℕ) ![x] Empty.elim belowOmegaC ↔
      precN x (codeNote ThetaNote.Omega) := by
  unfold belowOmegaC precN
  rw [Semiformula.eval_substs]
  have e : (Semiterm.val (M := ℕ) ![x] Empty.elim ∘
      ![(#0 : Semiterm ℒₒᵣ Empty 1), ((codeNote ThetaNote.Omega : ℕ) : Semiterm ℒₒᵣ Empty 1)])
        = ![x, codeNote ThetaNote.Omega] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => k.elim0) j
      simp
  rw [e]
  rfl

variable (P : ℕ → Prop) (S : Set ℕ)

/-- `x ≺ ⌜Ω⌝` in the standard structures. -/
theorem eval_belowOmega (x : ℕ) :
    Semiformula.Eval (s := stdI P S) ![x] Empty.elim belowOmega ↔
      precN x (codeNote ThetaNote.Omega) := by
  rw [belowOmega, eval_lMap_toLXI, eval_belowOmegaC]

/-- `y ≺ x` in the standard structures (slot `#0` the smaller element). -/
theorem eval_precLXI (y x : ℕ) :
    Semiformula.Eval (s := stdI P S) ![y, x] Empty.elim precLXI ↔ precN y x := by
  rw [precLXI, eval_lMap_toLXI]
  rfl

/-- **`Prog(≺, X)` in the standard structures**: `P` is progressive along `≺`. -/
theorem eval_progX_stdI :
    Semiformula.Eval (s := stdI P S) ![] Empty.elim progX ↔
      ∀ x, (∀ y, precN y x → P y) → P x := by
  unfold progX
  rw [Semiformula.eval_all]
  refine forall_congr' fun x => ?_
  rw [LogicalConnective.HomClass.map_imply, Semiformula.eval_all, eval_Xat]
  refine imp_congr (forall_congr' fun y => ?_) Iff.rfl
  rw [LogicalConnective.HomClass.map_imply, eval_Xat]
  have e : (y :> x :> ![] : Fin 2 → ℕ) = ![y, x] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    rfl
  rw [e, eval_precLXI]
  rfl

/-- **`TI_Ω(≺, X)` in the standard structures**: if `P` is progressive along `≺`, it holds
on the field `{x | x ≺ ⌜Ω⌝}`. -/
theorem eval_ti_stdI :
    Semiformula.Eval (s := stdI P S) ![] Empty.elim tiFieldSentence ↔
      ((∀ x, (∀ y, precN y x → P y) → P x) →
        ∀ x, precN x (codeNote ThetaNote.Omega) → P x) := by
  unfold tiFieldSentence
  rw [LogicalConnective.HomClass.map_imply, eval_progX_stdI, Semiformula.eval_all]
  refine imp_congr Iff.rfl (forall_congr' fun x => ?_)
  rw [LogicalConnective.HomClass.map_imply, eval_Xat, eval_belowOmega]
  rfl

/-- **`∀x (x ≺ ⌜Ω⌝ → I x)` in the standard structures**: the field is contained in `S`. -/
theorem eval_fieldInI_stdI :
    Semiformula.Eval (s := stdI P S) ![] Empty.elim fieldInI ↔
      ∀ x, precN x (codeNote ThetaNote.Omega) → x ∈ S := by
  unfold fieldInI
  rw [Semiformula.eval_all]
  refine forall_congr' fun x => ?_
  rw [LogicalConnective.HomClass.map_imply, eval_Iat, eval_belowOmega]
  rfl

end Standard

/-! ### The embedded sentences are `Σ(Ω)` -/

/-- `I` does not occur. -/
def NoI {ξ : Type*} : {n : ℕ} → Semiformula LXI ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel (Sum.inl _) _ => True
  | _, .rel (Sum.inr IXRel.X) _ => True
  | _, .rel (Sum.inr IXRel.I) _ => False
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr IXRel.X) _ => True
  | _, .nrel (Sum.inr IXRel.I) _ => False
  | _, .and φ ψ => NoI φ ∧ NoI ψ
  | _, .or φ ψ => NoI φ ∧ NoI ψ
  | _, .all φ => NoI φ
  | _, .exs φ => NoI φ

section Embed

variable {ξ : Type*}

theorem noI_neg : ∀ {n : ℕ} (φ : Semiformula LXI ξ n), NoI (∼φ) ↔ NoI φ
  | _, .verum => Iff.rfl
  | _, .falsum => Iff.rfl
  | _, .rel (Sum.inl _) _ => Iff.rfl
  | _, .rel (Sum.inr IXRel.X) _ => Iff.rfl
  | _, .rel (Sum.inr IXRel.I) _ => Iff.rfl
  | _, .nrel (Sum.inl _) _ => Iff.rfl
  | _, .nrel (Sum.inr IXRel.X) _ => Iff.rfl
  | _, .nrel (Sum.inr IXRel.I) _ => Iff.rfl
  | _, .and φ ψ => and_congr (noI_neg φ) (noI_neg ψ)
  | _, .or φ ψ => and_congr (noI_neg φ) (noI_neg ψ)
  | _, .all φ => noI_neg φ
  | _, .exs φ => noI_neg φ

theorem noI_lMap_toLXI : ∀ {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n), NoI (Semiformula.lMap toLXI φ)
  | _, .verum => trivial
  | _, .falsum => trivial
  | _, .rel _ _ => trivial
  | _, .nrel _ _ => trivial
  | _, .and φ ψ => ⟨noI_lMap_toLXI φ, noI_lMap_toLXI ψ⟩
  | _, .or φ ψ => ⟨noI_lMap_toLXI φ, noI_lMap_toLXI ψ⟩
  | _, .all φ => noI_lMap_toLXI φ
  | _, .exs φ => noI_lMap_toLXI φ

/-- **An `I`-free formula embeds into a `Σ(Ω)` formula without parameters.** -/
theorem embed_of_noI : ∀ {n : ℕ} (φ : Semiformula LXI ξ n), NoI φ →
    params (embed φ) = ∅ ∧ SigmaOmega (embed φ)
  | _, .verum, _ => ⟨rfl, trivial⟩
  | _, .falsum, _ => ⟨rfl, trivial⟩
  | _, .rel (Sum.inl _) _, _ => ⟨rfl, trivial⟩
  | _, .rel (Sum.inr IXRel.X) _, _ => ⟨rfl, trivial⟩
  | _, .nrel (Sum.inl _) _, _ => ⟨rfl, trivial⟩
  | _, .nrel (Sum.inr IXRel.X) _, _ => ⟨rfl, trivial⟩
  | _, .and φ ψ, h => by
    have h1 := embed_of_noI φ h.1
    have h2 := embed_of_noI ψ h.2
    rw [show (Semiformula.and φ ψ) = φ ⋏ ψ from rfl, embed, LogicalConnective.HomClass.map_and,
      params_and, sigmaOmega_and, ← embed, ← embed, h1.1, h2.1, Set.union_empty]
    exact ⟨rfl, h1.2, h2.2⟩
  | _, .or φ ψ, h => by
    have h1 := embed_of_noI φ h.1
    have h2 := embed_of_noI ψ h.2
    rw [show (Semiformula.or φ ψ) = φ ⋎ ψ from rfl, embed, LogicalConnective.HomClass.map_or,
      params_or, sigmaOmega_or, ← embed, ← embed, h1.1, h2.1, Set.union_empty]
    exact ⟨rfl, h1.2, h2.2⟩
  | _, .all φ, h => by
    rw [show (Semiformula.all φ) = ∀¹ φ from rfl, embed, Semiformula.lMap_all, params_all,
      sigmaOmega_all]
    exact embed_of_noI φ h
  | _, .exs φ, h => by
    rw [show (Semiformula.exs φ) = ∃¹ φ from rfl, embed, Semiformula.lMap_exs, params_exs,
      sigmaOmega_exs]
    exact embed_of_noI φ h

/-- The embedding of a sentence, read as a formula with free variables. -/
theorem embed_coe (σ : Sentence LXI) :
    embed (↑σ : Proposition LXI) = Rewriting.emb (embed σ) :=
  Semiformula.lMap_emb σ

end Embed

theorem noI_imp {ξ : Type*} {n : ℕ} (φ ψ : Semiformula LXI ξ n) :
    NoI (φ 🡒 ψ) ↔ NoI φ ∧ NoI ψ := by
  show NoI (∼φ) ∧ NoI ψ ↔ _
  rw [noI_neg]

theorem noI_ti : NoI tiFieldSentence :=
  (noI_imp _ _).mpr ⟨(noI_imp _ _).mpr ⟨(noI_imp _ _).mpr ⟨noI_lMap_toLXI precC, trivial⟩,
    trivial⟩, (noI_imp _ _).mpr ⟨noI_lMap_toLXI belowOmegaC, trivial⟩⟩

/-- **The embedding of `TI_Ω(≺, X)` is `Σ(Ω)`** (it does not mention `I`). -/
theorem sigmaOmega_embed_ti : SigmaOmega (embed (↑tiFieldSentence : Proposition LXI)) := by
  rw [embed_coe]
  exact (sigmaOmega_rew _ _).mpr (embed_of_noI _ noI_ti).2

/-- **The embedding of `TI_Ω(≺, X)` has no parameters.** -/
theorem params_embed_ti : params (embed (↑tiFieldSentence : Proposition LXI)) = ∅ := by
  rw [embed_coe]
  exact (params_rew _ _).trans (embed_of_noI _ noI_ti).1

theorem positive_fieldInI : Positive fieldInI :=
  ⟨(positive_lMap_toLXI belowOmegaC).2, positive_Iat _⟩

theorem noX_fieldInI : NoX fieldInI :=
  ⟨(noX_neg _).mpr noX_belowOmega, trivial⟩

/-- **The embedding of `∀x (x ≺ ⌜Ω⌝ → I x)` is `Σ(Ω)`.** -/
theorem sigmaOmega_embed_fieldInI : SigmaOmega (embed (↑fieldInI : Proposition LXI)) := by
  rw [embed_coe]
  exact (sigmaOmega_rew _ _).mpr ((sigmaOmega_embed_iff fieldInI).mpr positive_fieldInI)

/-! ### The refutation -/

section Refutation

open StageSem

/-- `(∀x (x ≺ ⌜Ω⌝ → I x))^γ = ∀x (x ≺ ⌜Ω⌝ → I^{≺γ} x)` is true in the stage model exactly
when the field is contained in the stage `S_γ`. -/
theorem trueS_capped_fieldInI (P : ℕ → Prop) (b : Stage) :
    TrueS P (accForm precC) (cap b (embed (↑fieldInI : Proposition LXI))) ↔
      ∀ x, precN x (codeNote ThetaNote.Omega) → x ∈ stageSet P (accForm precC) b.1 := by
  rw [cap_embed]
  unfold TrueS stageModel
  rw [Semiformula.eval_lMap, lMap_stageHom_stageStruc, Semiformula.eval_emb, eval_fieldInI_stdI]

/-- **No derivation of the embedded sentence.**  For every `m` and `β`,
`H_0 ⊬^β_{Ω+m} ∀x (x ≺ ⌜Ω⌝ → I x)`: collapsing (Corollary 7.2) brings a derivation below
`Ω`, boundedness (Theorem 5.9) bounds `I` by the stage `ϑη` given by the height, and
soundness (Proposition 5.8) in the stage model would put `code(ϑη)` into `S_{ϑη}`, i.e.
`ϑη ≺ ϑη`. -/
theorem not_derivable_fieldInI (m : ℕ) (β : ThetaNote) :
    ¬ IDerivable (accForm precC) (ThetaNote.Omega + ThetaNote.ofNat m)
        (ThetaNote.Hop ThetaNote.zero) β [embed (↑fieldInI : Proposition LXI)] := by
  intro d
  have hΓ : ∀ φ ∈ [embed (↑fieldInI : Proposition LXI)], SigmaOmega φ := by
    intro φ hφ
    rw [List.mem_singleton.mp hφ]
    exact sigmaOmega_embed_fieldInI
  obtain ⟨-, -, -, hlt, d'⟩ := corollary_7_2 (accForm_positive precC) hΓ m d
  let b : Stage := ⟨ThetaNote.theta (ThetaNote.omegaTower (m + 1) β), le_of_lt hlt⟩
  have d'' := boundedness (ThetaNote.Hop_isOperator _) (b := b) d'.height_mem le_rfl hlt d'
  obtain ⟨φ, hφ, htrue⟩ := sound (fun _ => True) (accForm precC) d'' hlt
  rw [List.mem_singleton.mp hφ, trueS_capped_fieldInI] at htrue
  have hx := htrue (codeNote b.1) ((precN_codeNote_iff _ _).mpr hlt)
  exact lt_irrefl b.1 ((codeNote_mem_stageSet_acc _ b.1 b.1).mp hx)

end Refutation

/-! ### The lower bound, given the embedding -/

/-- **`ID1Acc precC ⊬ TI_Ω(≺, X)`, given the embedding theorem for `X`-free sentences**
(Freund, Theorem 6.5, in the form: an `X`-free theorem `σ` of `ID1Acc precC` has a derivation
`H_0 ⊢^β_{Ω+m} σ`). -/
theorem id1_lower_bound_of_embedding_xfree
    (hemb : ∀ σ : Sentence LXI, NoX σ → ID1Acc precC ⊢ σ →
      ∃ (m : ℕ) (β : ThetaNote), IDerivable (accForm precC)
        (ThetaNote.Omega + ThetaNote.ofNat m) (ThetaNote.Hop ThetaNote.zero) β
        [embed (↑σ : Proposition LXI)]) :
    ¬ ID1Acc precC ⊢ tiFieldSentence := by
  intro h
  obtain ⟨m, β, d⟩ := hemb fieldInI noX_fieldInI (provable_fieldInI_of_ti h)
  exact not_derivable_fieldInI m β d

/-- **`ID1Acc precC ⊬ TI_Ω(≺, X)`, given the embedding theorem** (Freund, Theorem 6.5). -/
theorem id1_lower_bound_of_embedding
    (hemb : ∀ σ : Sentence LXI, ID1Acc precC ⊢ σ →
      ∃ (m : ℕ) (β : ThetaNote), IDerivable (accForm precC)
        (ThetaNote.Omega + ThetaNote.ofNat m) (ThetaNote.Hop ThetaNote.zero) β
        [embed (↑σ : Proposition LXI)]) :
    ¬ ID1Acc precC ⊢ tiFieldSentence :=
  id1_lower_bound_of_embedding_xfree fun σ _ h => hemb σ h

/-- The same argument without the reinterpretation: `ID1Acc precC ⊬ ∀x (x ≺ ⌜Ω⌝ → I x)`,
given the embedding theorem for this one sentence. -/
theorem not_provable_fieldInI_of_embedding
    (hemb : ID1Acc precC ⊢ fieldInI →
      ∃ (m : ℕ) (β : ThetaNote), IDerivable (accForm precC)
        (ThetaNote.Omega + ThetaNote.ofNat m) (ThetaNote.Hop ThetaNote.zero) β
        [embed (↑fieldInI : Proposition LXI)]) :
    ¬ ID1Acc precC ⊢ fieldInI := fun h =>
  let ⟨m, β, d⟩ := hemb h
  not_derivable_fieldInI m β d

end LowerBound

end InductiveDef

end OrdinalAnalysis
