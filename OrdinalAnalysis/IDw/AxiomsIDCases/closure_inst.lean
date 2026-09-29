/- Source: OrdinalAnalysis\IDn\AxiomsIDCases\closure_inst.lean (level `k : Fin n` generalised to `k : ℕ`,
   ID_n -> ID_omega; the level-`k` instance is now the *embedded* closure body, see below). -/

import OrdinalAnalysis.IDw.AxiomsIDCases.Defs
import OrdinalAnalysis.IDw.Transfer
import OrdinalAnalysis.IDw.TransferCong
import OrdinalAnalysis.IDw.NumSubst
import OrdinalAnalysis.IDw.AxiomsLogic
import OrdinalAnalysis.IDw.Embed

set_option autoImplicit false
namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting

open LO.FirstOrder.LawfulSyntacticRewriting

/-! ### Proposition 6.2: the closure axiom -/

section Closure

/-- **The embedded body of the closure axiom**: `A` compiled at the level `y = #1` with own place
`J(y, ·)` (`AAt (Jat #1 #0) #1 A`), embedded into `LIinfW` (`X` is absent). Slots: `#0 = x`,
`#1 = y`. -/
def closureBody2 (A : FormJ) : Semiformula LIinfW ℕ 2 :=
  Rewriting.emb (embK (AAt (ξ := Empty) (Jat #1 #0) #1 A))

/-- **The embedded closure axiom is `∀y ∀x (¬closureBody2 ∨ Jlev ⊤ (y, x))`.** -/
theorem emb_embK_closureAx (A : FormJ) :
    (Rewriting.emb (embK (closureAxJ A)) : Proposition LIinfW) =
      ∀¹ ∀¹ (∼(closureBody2 A) ⋎ jlevAt ⊤ (#1) (#0)) := by
  simp only [closureAxJ, closureBody2, Semiformula.imp_eq, embK_all, embK_or, embK_neg, embK_Jat,
    Rewriting.app_all, Rew.q_emb, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, rew_jlevAt_al, embT, Semiterm.lMap_bvar, Rew.emb_bvar]

theorem params_closureBody2 (A : FormJ) : params (closureBody2 A) = ∅ := by
  unfold closureBody2
  show params (Rew.emb ▹ embK (AAt (ξ := Empty) (Jat #1 #0) #1 A)) = ∅
  rw [params_rew, params_embK]

/-- The ω-rule's outer instance of `∀y ψ(y, ·)`: substituting the numeral of `k` for the outer
variable. -/
theorem subst_all_numeral (ψ : Semiformula LIinfW ℕ 2) (k : ℕ) :
    (∀¹ ψ)/[numI k] =
      ∀¹ (ψ/[(#0 : Semiterm LIinfW ℕ 1), (Semiterm.numeral k : Semiterm LIinfW ℕ 1)]) := by
  rw [show (∀¹ ψ)/[numI k] = Rew.subst ![numI k] ▹ (∀¹ ψ) from rfl, Rewriting.app_all]
  congr 1
  have : (Rew.subst ![(numI k : SyntacticTerm LIinfW)]).q =
      (Rew.subst ![(#0 : Semiterm LIinfW ℕ 1), (Semiterm.numeral k : Semiterm LIinfW ℕ 1)] :
        Rew LIinfW ℕ 2 ℕ 1) := by
    refine Rew.ext _ _ ?_ ?_
    · intro x; fin_cases x
      · simp
      · show (Rew.subst ![(numI k : SyntacticTerm LIinfW)]).q #(Fin.succ 0) = _
        rw [Rew.q_bvar_succ]; simp
    · intro x; simp
  rw [this]

/-- The ω-rule's inner instance. -/
theorem subst_numeral_comp (ψ : Semiformula LIinfW ℕ 2) (k m : ℕ) :
    (ψ/[(#0 : Semiterm LIinfW ℕ 1), (Semiterm.numeral k : Semiterm LIinfW ℕ 1)])/[numI m] =
      ψ/[numI m, (Semiterm.numeral k : Semiterm LIinfW ℕ 0)] := by
  have hc : (Rew.subst ![(numI m : SyntacticTerm LIinfW)] : Rew LIinfW ℕ 1 ℕ 0).comp
      (Rew.subst ![(#0 : Semiterm LIinfW ℕ 1), (Semiterm.numeral k : Semiterm LIinfW ℕ 1)]) =
      Rew.subst ![numI m, (Semiterm.numeral k : Semiterm LIinfW ℕ 0)] := by
    refine Rew.ext _ _ ?_ ?_
    · intro x; fin_cases x <;> simp [Rew.comp_app]
    · intro x; simp [Rew.comp_app]
  show Rew.subst ![numI m] ▹ (Rew.subst _ ▹ ψ) = _
  rw [← TransitiveRewriting.comp_app, hc]

/-- The instance of the embedded closure matrix at `(x, y) = (t, k̄)`. -/
theorem closure_inst (A : FormJ) (k : ℕ) (t : SyntacticTerm LIinfW) :
    (∼(closureBody2 A) ⋎ jlevAt ⊤ (#1) (#0))/[t, (Semiterm.numeral k : Semiterm LIinfW ℕ 0)] =
      ∼((closureBody2 A)/[t, (Semiterm.numeral k : Semiterm LIinfW ℕ 0)]) ⋎
        jlevAt ⊤ (numI k) t := by
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    rew_jlevAt_al]
  simp

/-- The instance of `(ψ/[#0, k̄])` at any term. -/
theorem subst_zero_comp (ψ : Semiformula LIinfW ℕ 2) (k : ℕ) (t : SyntacticTerm LIinfW) :
    (ψ/[(#0 : Semiterm LIinfW ℕ 1), (Semiterm.numeral k : Semiterm LIinfW ℕ 1)])/[t] =
      ψ/[t, (Semiterm.numeral k : Semiterm LIinfW ℕ 0)] := by
  have hc : (Rew.subst ![t] : Rew LIinfW ℕ 1 ℕ 0).comp
      (Rew.subst ![(#0 : Semiterm LIinfW ℕ 1), (Semiterm.numeral k : Semiterm LIinfW ℕ 1)]) =
      Rew.subst ![t, (Semiterm.numeral k : Semiterm LIinfW ℕ 0)] := by
    refine Rew.ext _ _ ?_ ?_
    · intro x; fin_cases x <;> simp [Rew.comp_app]
    · intro x; simp [Rew.comp_app]
  show Rew.subst ![t] ▹ (Rew.subst _ ▹ ψ) = _
  rw [← TransitiveRewriting.comp_app, hc]

/-- **The congruence for the closure axiom** (from the `Cong` producer `IDw.TransferCong`): for the
positive form `A`, every closed `t` and every level `k`, the embedded closure body at `(t, k̄)` is
`OkBwd k`-congruent, with the depth `cdepth A` independent of `k` and `t`, to the level-`k` top
unfolding `unfoldW A k Ω_{k+1} t` (`P ↦ I_k`, `Q ↦ Jlev k`). -/
theorem closureCong {A : FormJ} (hA : PositiveP A) (k : ℕ) {t : SyntacticTerm LIinfW}
    (ht : t.freeVariables = ∅) :
    Transfer.Cong (Transfer.OkBwd k) (Transfer.cdepth A)
      ((closureBody2 A)/[t, (Semiterm.numeral k : Semiterm LIinfW ℕ 0)])
      (unfoldW A k (StageAt.top k) t) := by
  have h := Transfer.cong_unfold_bwd k hA ht
  rwa [Transfer.embInst_closure] at h

end Closure
end IDw
end OrdinalAnalysis
