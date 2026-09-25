/-
  Theorem 4.8 for `ID_n` (`Statement.lean`), the case of the clause for the identity axiom of
  the free predicate `X` — proved (no `sorry`).

  Source: A. Freund, arXiv:2204.09321, Theorem 6.7, case `idX` (`ID1/Collapsing.lean`, case
  `idX`); W. Buchholz, *A simplified version of local predicativity* (1992), author preprint
  p. 27, proof of Theorem 4.8, case 1 (empty index set).

  **Across levels.**  As with `literal` and `verum`, this clause carries no premise and no side
  condition on a level `j`; only the height and the parameter hull are re-certified at
  `α̂ = γ + ω^{μ+μ+α}` in place of `γ`, via `psi_hat_mem` and `gamma_le_hat` of `Basic.lean`.

  The statement is `Cases.lean`'s `collapse_case_idX`, verbatim.
-/
import OrdinalAnalysis.IDn.Collapsing.Statement

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

namespace Collapsing

open LO LO.FirstOrder

variable {n : ℕ} {A : Fin n → Semisentence (LXIn n) 1}

/-- **Case `idX`**: the identity axiom of `X`. -/
theorem collapse_case_idX (hyp : CollapseHyps A) {m : ℕ} (hm : m ≤ n) {α : ThetaWNoteD}
    (mih : ∀ m' < m, ∀ α' : ThetaWNoteD, Claim A m' α')
    (sih : ∀ α₀ < α, Claim A m α₀)
    {k : Fin n} {γ : ThetaWNoteD} {X : Set ThetaWNoteD} {Γ : Sequent (LIinfN n)}
    (hΓ : ∀ φ ∈ Γ, SigmaW k φ) (hγ : γ ∈ ThetaWNoteD.HopS γ X)
    (hX : ThetaWNoteD.HullHypGe k.val γ X)
    (t : SyntacticTerm (LIinfN n))
    (hα : α ∈ Hg γ X ∅) (hΓH : paramsVal Γ ⊆ Hg γ X ∅) (h1 : XinfAt t ∈ Γ)
    (h2 : ∼(XinfAt t) ∈ Γ) :
    Concl A k γ X m α Γ := by
  have hα' : α ∈ ThetaWNoteD.HopS γ X := mem_Hg_empty.mp hα
  exact .idX t (mem_Hg_empty.mpr (psi_hat_mem hX hγ hα'))
    (hΓH.trans (Hg_mono (gamma_le_hat γ _ α) X ∅)) h1 h2

end Collapsing

end IDn

end OrdinalAnalysis
