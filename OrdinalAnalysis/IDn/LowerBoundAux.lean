/-
  Helpers for the multi-level lower bound (`IDn/LowerBound.lean`), generalising the `X ↦ I_0`
  reinterpretation and the accessible-part stage characterisation of
  `OrdinalAnalysis.ID1.LowerBound` / `OrdinalAnalysis.ID1.StageSemantics` from one inductively
  defined predicate to `n` simultaneous ones, reading `X` as the *level-0* predicate `I_0`.

  Source: A. Freund, arXiv:2204.09321, as ported by `ID1/LowerBound.lean`.

  **Step 1 (`X := I_0`).**  `NoXN` is `X`-freeness for `LXIn n`-formulas (any occurrence of the
  index-`j` predicate `I_j`, `j : Fin n`, is allowed).  `swapXIN k0` reinterprets `X` as `I_{k0}`,
  fixing arithmetic and every `I_j`.  Because none of the `n` well-ordering operator forms
  (`Upper.WForms`) mentions `X` at all, every closure axiom is already fixed by the swap; the
  induction scheme survives because `indAxAt k A F` is closed under `F ↦ swap F`
  (`lMap_swap_substIAt`, the per-level generalisation of `ID1.LowerBound.lMap_swap_substI`).  So
  every axiom of `IDn n A` stays true when the structure is read along `swapXIN k0`
  (`eval_swap_of_mem_IDn`), and `IDn n A ⊢ TI_a(≺,X)` gives `IDn n A ⊢ ∀x (x ≺ ⌜a⌝ → I_{k0} x)`
  (`provable_fieldInI0_of_ti`), exactly as `ID1.LowerBound.provable_fieldInI_of_ti`.

  **Step 6 (the accessible part at level `0`).**  `codeAt0_mem_stageSetN_iff` computes the
  level-`0` stages of `Upper.WForms F n` in terms of the internal order `F.lt`/`F.fld`: the
  code of `β : ThetaWNoteD` enters the stage `b : StageAt 0` exactly when `β < b.1` — the direct
  analogue of `ID1.StageSem.codeNote_mem_stageSet_acc`, using `eval_wForm_zero` in place of
  `ID1`'s `opA_accForm`.  Two order facts not yet available from `IDn/Internal/*.lean` (its own
  docstring: the order/domain bridging "is not built in `Codes.lean`") are carried as explicit
  hypotheses of this lemma rather than of a bespoke structure, so that this file states exactly
  what it uses and no more; `IDn/LowerBound.lean`'s `LowerBoundHyps` packages them for the
  assembly.

  Contents.

    `NoXN`, `swapRelN`, `swapXIN`                    `X ↦ I_{k0}`; the fresh part of `LXIn n`
    `lMap_swap_of_noXN`, `lMap_swap_substIAt`, `lMap_swap_indBodyAt`
    `eval_swap_of_mem_IDn`                            axioms of `IDn n A` stay true under the swap
    `provable_fieldInI0_of_ti`                        **`TI_a(≺,X) ⊢ ∀x (x ≺ ⌜a⌝ → I_{k0} x)`**
    `codeAt0_mem_stageSetN_iff`                        **the accessible part at level `0`**
-/
import OrdinalAnalysis.IDn.StageSemantics
import OrdinalAnalysis.IDn.Theorem
import Foundation.FirstOrder.Completeness

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.IDn.Upper

variable {n : ℕ}

/-! ### `X`-freeness of `LXIn n`-formulas -/

/-- `X` does not occur (every `I_j`, `j : Fin n`, is unrestricted). -/
def NoXN {ξ : Type*} : {m : ℕ} → Semiformula (LXIn n) ξ m → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel (Sum.inl _) _ => True
  | _, .rel (Sum.inr IXRelN.X) _ => False
  | _, .rel (Sum.inr (IXRelN.I _)) _ => True
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr IXRelN.X) _ => False
  | _, .nrel (Sum.inr (IXRelN.I _)) _ => True
  | _, .and φ ψ => NoXN φ ∧ NoXN ψ
  | _, .or φ ψ => NoXN φ ∧ NoXN ψ
  | _, .all φ => NoXN φ
  | _, .exs φ => NoXN φ

section NoXN

variable {ξ : Type*}

theorem noXN_neg : ∀ {m : ℕ} (φ : Semiformula (LXIn n) ξ m), NoXN (∼φ) ↔ NoXN φ
  | _, .verum => Iff.rfl
  | _, .falsum => Iff.rfl
  | _, .rel (Sum.inl _) _ => Iff.rfl
  | _, .rel (Sum.inr IXRelN.X) _ => Iff.rfl
  | _, .rel (Sum.inr (IXRelN.I _)) _ => Iff.rfl
  | _, .nrel (Sum.inl _) _ => Iff.rfl
  | _, .nrel (Sum.inr IXRelN.X) _ => Iff.rfl
  | _, .nrel (Sum.inr (IXRelN.I _)) _ => Iff.rfl
  | _, .and φ ψ => and_congr (noXN_neg φ) (noXN_neg ψ)
  | _, .or φ ψ => and_congr (noXN_neg φ) (noXN_neg ψ)
  | _, .all φ => noXN_neg φ
  | _, .exs φ => noXN_neg φ

theorem noXN_imp {m : ℕ} (φ ψ : Semiformula (LXIn n) ξ m) : NoXN (φ 🡒 ψ) ↔ NoXN φ ∧ NoXN ψ := by
  show NoXN (∼φ) ∧ NoXN ψ ↔ _; rw [noXN_neg]

theorem noXN_lMap_toLXIN : ∀ {m : ℕ} (φ : Semiformula ℒₒᵣ ξ m), NoXN (Semiformula.lMap (toLXIN (Fin n)) φ)
  | _, .verum => trivial
  | _, .falsum => trivial
  | _, .rel _ _ => trivial
  | _, .nrel _ _ => trivial
  | _, .and φ ψ => ⟨noXN_lMap_toLXIN φ, noXN_lMap_toLXIN ψ⟩
  | _, .or φ ψ => ⟨noXN_lMap_toLXIN φ, noXN_lMap_toLXIN ψ⟩
  | _, .all φ => noXN_lMap_toLXIN φ
  | _, .exs φ => noXN_lMap_toLXIN φ

theorem noXN_Iat {m : ℕ} (k : Fin n) (t : Semiterm (LXIn n) ξ m) : NoXN (Iat k t) := trivial

theorem noXN_rew {ξ₂ : Type*} : ∀ {m₁ m₂ : ℕ} (ω : Rew (LXIn n) ξ m₁ ξ₂ m₂)
    (φ : Semiformula (LXIn n) ξ m₁), NoXN (ω ▹ φ) ↔ NoXN φ
  | _, _, _, .verum => Iff.rfl
  | _, _, _, .falsum => Iff.rfl
  | _, _, _, .rel (Sum.inl _) _ => Iff.rfl
  | _, _, _, .rel (Sum.inr IXRelN.X) _ => Iff.rfl
  | _, _, _, .rel (Sum.inr (IXRelN.I _)) _ => Iff.rfl
  | _, _, _, .nrel (Sum.inl _) _ => Iff.rfl
  | _, _, _, .nrel (Sum.inr IXRelN.X) _ => Iff.rfl
  | _, _, _, .nrel (Sum.inr (IXRelN.I _)) _ => Iff.rfl
  | _, _, ω, .and φ ψ => by
    rw [show (Semiformula.and φ ψ) = φ ⋏ ψ from rfl, LogicalConnective.HomClass.map_and]
    exact and_congr (noXN_rew ω φ) (noXN_rew ω ψ)
  | _, _, ω, .or φ ψ => by
    rw [show (Semiformula.or φ ψ) = φ ⋎ ψ from rfl, LogicalConnective.HomClass.map_or]
    exact and_congr (noXN_rew ω φ) (noXN_rew ω ψ)
  | _, _, ω, .all φ => by
    rw [show (Semiformula.all φ) = ∀¹ φ from rfl, Rewriting.app_all]
    exact noXN_rew ω.q φ
  | _, _, ω, .exs φ => by
    rw [show (Semiformula.exs φ) = ∃¹ φ from rfl, Rewriting.app_exs]
    exact noXN_rew ω.q φ

end NoXN

/-! ### The reinterpretation `X ↦ I_{k0}` -/

/-- `X ↦ I_{k0}`; arithmetic and every `I_j` are fixed. -/
def swapRelN (k0 : Fin n) : {m : ℕ} → (LXIn n).Rel m → (LXIn n).Rel m
  | _, Sum.inl r => Sum.inl r
  | _, Sum.inr IXRelN.X => Sum.inr (IXRelN.I k0)
  | _, Sum.inr (IXRelN.I j) => Sum.inr (IXRelN.I j)

/-- **The reinterpretation of `X` by `I_{k0}`**, as an endomorphism of `LXIn n`. -/
def swapXIN (k0 : Fin n) : LXIn n →ᵥ LXIn n := ⟨fun f => f, swapRelN k0⟩

section Swap

variable {ξ : Type*} (k0 : Fin n)

@[simp] theorem lMap_swapN_term {m : ℕ} (t : Semiterm (LXIn n) ξ m) :
    Semiterm.lMap (swapXIN k0) t = t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih =>
    rw [Semiterm.lMap_func]; congr 1; funext i; exact ih i

theorem lMap_swapN_rel {j m : ℕ} (r : (LXIn n).Rel j) (v : Fin j → Semiterm (LXIn n) ξ m) :
    Semiformula.lMap (swapXIN k0) (Semiformula.rel r v) = Semiformula.rel (swapRelN k0 r) v := by
  rw [Semiformula.lMap_rel]; congr 1; funext i; simp

theorem lMap_swapN_nrel {j m : ℕ} (r : (LXIn n).Rel j) (v : Fin j → Semiterm (LXIn n) ξ m) :
    Semiformula.lMap (swapXIN k0) (Semiformula.nrel r v) = Semiformula.nrel (swapRelN k0 r) v := by
  rw [Semiformula.lMap_nrel]; congr 1; funext i; simp

theorem lMap_swapN_Xat {m : ℕ} (t : Semiterm (LXIn n) ξ m) :
    Semiformula.lMap (swapXIN k0) (Xat t) = Iat k0 t :=
  lMap_swapN_rel k0 _ _

theorem lMap_swapN_Iat {m : ℕ} (j : Fin n) (t : Semiterm (LXIn n) ξ m) :
    Semiformula.lMap (swapXIN k0) (Iat j t) = Iat j t :=
  lMap_swapN_rel k0 _ _

/-- `X`-free formulas are fixed by the swap. -/
theorem lMap_swap_of_noXN : ∀ {m : ℕ} (φ : Semiformula (LXIn n) ξ m), NoXN φ →
    Semiformula.lMap (swapXIN k0) φ = φ
  | _, .verum, _ => rfl
  | _, .falsum, _ => rfl
  | _, .rel (Sum.inl _) v, _ => lMap_swapN_rel k0 _ v
  | _, .rel (Sum.inr (IXRelN.I _)) v, _ => lMap_swapN_rel k0 _ v
  | _, .nrel (Sum.inl _) v, _ => lMap_swapN_nrel k0 _ v
  | _, .nrel (Sum.inr (IXRelN.I _)) v, _ => lMap_swapN_nrel k0 _ v
  | _, .and φ ψ, h => by
    rw [show (Semiformula.and φ ψ) = φ ⋏ ψ from rfl, LogicalConnective.HomClass.map_and,
      lMap_swap_of_noXN φ h.1, lMap_swap_of_noXN ψ h.2]
  | _, .or φ ψ, h => by
    rw [show (Semiformula.or φ ψ) = φ ⋎ ψ from rfl, LogicalConnective.HomClass.map_or,
      lMap_swap_of_noXN φ h.1, lMap_swap_of_noXN ψ h.2]
  | _, .all φ, h => by
    rw [show (Semiformula.all φ) = ∀¹ φ from rfl, Semiformula.lMap_all, lMap_swap_of_noXN φ h]
  | _, .exs φ, h => by
    rw [show (Semiformula.exs φ) = ∃¹ φ from rfl, Semiformula.lMap_exs, lMap_swap_of_noXN φ h]

/-- **On an `X`-free formula, `X ↦ I_{k0}` commutes with substituting for `I_k`** (the
per-level generalisation of `ID1.LowerBound.lMap_swap_substI`: `substIAt` only touches the
atoms of the one level `k`, so a mismatched level `j ≠ k` is an `I_j`-atom, fixed by the swap
regardless of `NoXN`). -/
theorem lMap_swap_substIAt (k0 : Fin n) [DecidableEq (Fin n)] (k : Fin n)
    (F : Semiformula (LXIn n) ξ 1) :
    ∀ {m : ℕ} (φ : Semiformula (LXIn n) ξ m), NoXN φ →
      Semiformula.lMap (swapXIN k0) (substIAt k F φ) =
        substIAt k (Semiformula.lMap (swapXIN k0) F) φ
  | _, .verum, _ => rfl
  | _, .falsum, _ => rfl
  | _, .rel (Sum.inl r) v, h => lMap_swap_of_noXN k0 (.rel (Sum.inl r) v) h
  | _, .rel (Sum.inr (IXRelN.I j)) v, _ => by
    show Semiformula.lMap (swapXIN k0) (substIAt k F (Semiformula.rel (Sum.inr (IXRelN.I j)) v))
      = substIAt k (Semiformula.lMap (swapXIN k0) F) (Semiformula.rel (Sum.inr (IXRelN.I j)) v)
    by_cases hjk : j = k
    · rw [substIAt, dif_pos hjk, substIAt, dif_pos hjk, Semiformula.lMap_subst]
      congr 1; funext i; simp
    · rw [substIAt, dif_neg hjk, substIAt, dif_neg hjk]
      exact lMap_swapN_rel k0 _ v
  | _, .nrel (Sum.inl r) v, h => lMap_swap_of_noXN k0 (.nrel (Sum.inl r) v) h
  | _, .nrel (Sum.inr (IXRelN.I j)) v, _ => by
    show Semiformula.lMap (swapXIN k0) (substIAt k F (Semiformula.nrel (Sum.inr (IXRelN.I j)) v))
      = substIAt k (Semiformula.lMap (swapXIN k0) F) (Semiformula.nrel (Sum.inr (IXRelN.I j)) v)
    by_cases hjk : j = k
    · rw [substIAt, dif_pos hjk, substIAt, dif_pos hjk, LogicalConnective.HomClass.map_neg,
        Semiformula.lMap_subst]
      congr 2; funext i; simp
    · rw [substIAt, dif_neg hjk, substIAt, dif_neg hjk]
      exact lMap_swapN_nrel k0 _ v
  | _, .and φ ψ, h => by
    show Semiformula.lMap (swapXIN k0) (substIAt k F φ ⋏ substIAt k F ψ) = _
    rw [LogicalConnective.HomClass.map_and,
      lMap_swap_substIAt (k0 := k0) (k := k) (F := F) φ h.1,
      lMap_swap_substIAt (k0 := k0) (k := k) (F := F) ψ h.2]
    rfl
  | _, .or φ ψ, h => by
    show Semiformula.lMap (swapXIN k0) (substIAt k F φ ⋎ substIAt k F ψ) = _
    rw [LogicalConnective.HomClass.map_or,
      lMap_swap_substIAt (k0 := k0) (k := k) (F := F) φ h.1,
      lMap_swap_substIAt (k0 := k0) (k := k) (F := F) ψ h.2]
    rfl
  | _, .all φ, h => by
    show Semiformula.lMap (swapXIN k0) (∀¹ substIAt k F φ) = _
    rw [Semiformula.lMap_all, lMap_swap_substIAt (k0 := k0) (k := k) (F := F) φ h]; rfl
  | _, .exs φ, h => by
    show Semiformula.lMap (swapXIN k0) (∃¹ substIAt k F φ) = _
    rw [Semiformula.lMap_exs, lMap_swap_substIAt (k0 := k0) (k := k) (F := F) φ h]; rfl

/-- The successor-induction axiom is mapped to the successor-induction axiom (arithmetic is
untouched by the swap). -/
theorem lMap_swap_succIndN (k0 : Fin n) (φ : Semiformula (LXIn n) ℕ 1) :
    Semiformula.lMap (swapXIN k0) (succInd φ) = succInd (Semiformula.lMap (swapXIN k0) φ) := by
  simp [succInd, Semiformula.lMap_subst, Matrix.comp₁]

/-- The induction axiom's body at level `k` is mapped to the body at `F` reinterpreted. -/
theorem lMap_swap_indBodyAt [DecidableEq (Fin n)] (k : Fin n) {A : Semisentence (LXIn n) 1}
    (hA : NoXN (Rewriting.emb A : Semiformula (LXIn n) ℕ 1)) (F : Semiformula (LXIn n) ℕ 1) :
    Semiformula.lMap (swapXIN k0) ((∀¹ (opAt k A F 🡒 F)) 🡒 ∀¹ (Iat k #0 🡒 F)) =
      ((∀¹ (opAt k A (Semiformula.lMap (swapXIN k0) F) 🡒 Semiformula.lMap (swapXIN k0) F)) 🡒
        ∀¹ (Iat k #0 🡒 Semiformula.lMap (swapXIN k0) F)) := by
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.lMap_all]
  rw [show opAt k A F = substIAt k F (Rewriting.emb A) from rfl,
    lMap_swap_substIAt (k0 := k0) (k := k) (F := F) _ hA, lMap_swapN_Iat k0 k #0]
  rfl

end Swap

/-! ### Every axiom of `IDn n A` stays true under the swap, when `A` is `X`-free at every
level -/

section Models

variable {A : Fin n → Semisentence (LXIn n) 1} (k0 : Fin n)
  (hAX : ∀ k : Fin n, NoXN (Rewriting.emb (A k) : Semiformula (LXIn n) ℕ 1))
  {M : Type} [Nonempty M] (s : Structure (LXIn n) M)

include hAX in
theorem noXN_closureAxAt (k : Fin n) : NoXN (closureAxAt k (A k)) :=
  (noXN_imp _ _).mpr ⟨(noXN_rew Rew.emb (A k)).mp (hAX k), noXN_Iat k _⟩

theorem eval_swap_univClN (φ : Proposition (LXIn n)) :
    Semiformula.Eval (s := s.lMap (swapXIN k0)) ![] Empty.elim (Semiformula.univCl φ) ↔
      Semiformula.Eval (s := s) ![] Empty.elim
        (Semiformula.univCl (Semiformula.lMap (swapXIN k0) φ)) := by
  have h1 := Semiformula.eval_univCl (s := s.lMap (swapXIN k0)) (M := M) φ
  have h2 := Semiformula.eval_univCl (s := s) (M := M) (Semiformula.lMap (swapXIN k0) φ)
  refine h1.trans (Iff.trans ?_ h2.symm)
  exact forall_congr' fun f => Semiformula.eval_lMap.symm

include hAX in
/-- **Every axiom of `IDn n A` stays true when `X` is read as `I_{k0}`** (`A` mentions no `X`
at any level; this holds for `Upper.WForms`). -/
theorem eval_swap_of_mem_IDn (hEq : ∀ a b : M,
      s.rel (Language.Eq.eq : (LXIn n).Rel 2) ![a, b] ↔ a = b)
    (hM : ∀ σ ∈ IDn n A, Semiformula.Eval (s := s) ![] Empty.elim σ)
    {σ : Sentence (LXIn n)} (hσ : σ ∈ IDn n A) :
    Semiformula.Eval (s := s.lMap (swapXIN k0)) ![] Empty.elim σ := by
  rcases mem_ID A |>.mp hσ with h | h | h | ⟨k, rfl | ⟨F, rfl⟩⟩
  · let _ : Structure (LXIn n) M := s.lMap (swapXIN k0)
    have _ : Structure.Eq (LXIn n) M := ⟨fun a b => hEq a b⟩
    have := Structure.Eq.models_eq (LXIn n) M
    exact Theory.models M (𝗘𝗤 (LXIn n)) h
  · obtain ⟨τ, hτ, rfl⟩ := h
    rw [Semiformula.eval_lMap]
    have h' := hM _ (mem_ID_of_paMinus A hτ)
    rw [Semiformula.eval_lMap] at h'
    exact h'
  · obtain ⟨φ, -, rfl⟩ := h
    rw [eval_swap_univClN k0, lMap_swap_succIndN k0 φ]
    exact hM _ (succInd_mem_ID A (Semiformula.lMap (swapXIN k0) φ))
  · rw [← Semiformula.eval_lMap, lMap_swap_of_noXN k0 _ (noXN_closureAxAt hAX k)]
    exact hM _ (closureAxAt_mem_ID A k)
  · unfold indAxAt
    rw [eval_swap_univClN k0, lMap_swap_indBodyAt k0 k (hAX k) F]
    exact hM _ (indAxAt_mem_ID A k (Semiformula.lMap (swapXIN k0) F))

end Models

end IDn

end OrdinalAnalysis
