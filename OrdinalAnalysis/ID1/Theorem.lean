/-
  The lower bound of the Bachmann–Howard analysis of `ID₁`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Theorem 6.5 (embedding), Theorem 6.7 (collapsing),
  Corollary 7.2, and the stage semantics of the accessible part.

  `ID1Acc precC` is `ID₁` for the accessibility operator `A(Y, x) :≡ ∀y (y ≺ x → Y y)` of the
  coded ϑ-order `≺ = precC`.  The reduction of the unprovability of transfinite induction for
  the free predicate `X` along `≺` below `⌜Ω⌝` to the embedding theorem for `X`-free sentences
  is `LowerBound.id1_lower_bound_of_embedding_xfree`; the embedding theorem is
  `embedding_theorem_xfree` with the operator `H_0` and the operator form `accForm precC`,
  which is positive and `X`-free.  The rank bound `Ω ⊕ m` of the embedding is the ordinal sum
  `Ω + m` (`add_ofNat_eq_nadd`).

  Contents.

    `xFreeL_of_noX`                     the two `X`-freeness predicates agree
    `xFreeL_accForm`                    the accessibility form is `X`-free
    `embedding_accForm`                 Theorem 6.5 in the form the lower bound consumes
    `id1_lower_bound`                   **`ID1Acc precC ⊬ TI_Ω(≺, X)`**
-/
import OrdinalAnalysis.ID1.Embed
import OrdinalAnalysis.ID1.LowerBound

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

open LO LO.FirstOrder
open OrdinalAnalysis.ID1.Internal

/-- A formula in which `X` does not occur is `X`-free (the two predicates have the same
clauses). -/
theorem xFreeL_of_noX {ξ : Type*} :
    ∀ {n : ℕ} (φ : Semiformula LXI ξ n), LowerBound.NoX φ → XFreeL φ
  | _, .verum, _ => trivial
  | _, .falsum, _ => trivial
  | _, .rel (Sum.inl _) _, _ => trivial
  | _, .rel (Sum.inr IXRel.X) _, h => h.elim
  | _, .rel (Sum.inr IXRel.I) _, _ => trivial
  | _, .nrel (Sum.inl _) _, _ => trivial
  | _, .nrel (Sum.inr IXRel.X) _, h => h.elim
  | _, .nrel (Sum.inr IXRel.I) _, _ => trivial
  | _, .and φ ψ, h => ⟨xFreeL_of_noX φ h.1, xFreeL_of_noX ψ h.2⟩
  | _, .or φ ψ, h => ⟨xFreeL_of_noX φ h.1, xFreeL_of_noX ψ h.2⟩
  | _, .all φ, h => xFreeL_of_noX φ h
  | _, .exs φ, h => xFreeL_of_noX φ h

/-- The accessibility form of the coded ϑ-order is `X`-free. -/
theorem xFreeL_accForm : XFreeL (accForm precC) :=
  xFreeL_of_noX _ LowerBound.noX_accForm

/-- **Freund, Theorem 6.5, for `ID1Acc precC`**: every `X`-free theorem `σ` has a derivation
`H_0 ⊢^β_{Ω+m} σ⁺`. -/
theorem embedding_accForm {σ : Sentence LXI} (hσ : LowerBound.NoX σ)
    (h : ID1Acc precC ⊢ σ) :
    ∃ (m : ℕ) (β : ThetaNote), IDerivable (accForm precC)
      (ThetaNote.Omega + ThetaNote.ofNat m) (ThetaNote.Hop ThetaNote.zero) β
      [embed (↑σ : Proposition LXI)] := by
  obtain ⟨m, n, d⟩ := embedding_theorem_xfree (ID1Acc_positive precC) xFreeL_accForm
    (xFreeL_of_noX _ hσ) h
  refine ⟨m, ThetaNote.nadd (ThetaNote.nadd ThetaNote.Omega ThetaNote.Omega)
    (ThetaNote.ofNat n), ?_⟩
  rw [ThetaNote.add_ofNat_eq_nadd]
  exact d _ (ThetaNote.Hop_nice ThetaNote.zero)

/-- **The lower bound of the Bachmann–Howard analysis of `ID₁`** (Freund, Corollary 7.2, with
the stage semantics of the accessible part): `ID₁` for the accessibility operator
`A(Y, x) :≡ ∀y (y ≺ x → Y y)` of the coded ϑ-order `≺ = precC` does not prove transfinite
induction for the free predicate `X` along `≺` below `⌜Ω⌝`,

    ID1Acc precC ⊬ Prog(≺, X) → ∀x (x ≺ ⌜Ω⌝ → X x). -/
theorem id1_lower_bound : ¬ ID1Acc precC ⊢ LowerBound.tiFieldSentence :=
  LowerBound.id1_lower_bound_of_embedding_xfree fun _ hσ h => embedding_accForm hσ h

end InductiveDef

end OrdinalAnalysis
