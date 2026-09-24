/-
  The descent from one level of ramified analysis to any level below:

      RAlt ν ⊢ ∀b (TI_μ(b) → ∀u (Eps(u, b) → TI_κ(u)))        (0 < κ < μ < ν)

  that is, transfinite induction below `b` for every level-`μ` set gives
  transfinite induction below `ε_b` for every level-`κ` set.

  The formula `ψ_κ(g) :≡ ∀u (Eps(u, g) → TI_κ(u))` of `Ramified/EpsProgR.lean`
  is closed and has level `κ < μ`, so it has shape `μ`, and comprehension at
  level `μ` (`Ramified/Comprehension.lean`) names the set `S = {g | ψ_κ(g)}` by
  a level-`μ` set `w`.  Instantiating `TI_μ(b)` at `w`: `S` is progressive by
  (EP_κ), so every `g ≺₁ b` lies in `S`; one more application of (EP_κ) at `b`
  gives `ψ_κ(b)`.

  This is the only way the levels interact: each passage to a lower level
  applies `ε` once.  The levels are notations, so `κ` need not be the
  predecessor of `μ`.
-/
import OrdinalAnalysis.Ramified.EpsProgR

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- The matrix of the descent: `TI_μ(b) → ψ_κ(b)`, with `b` the bound
variable. -/
def descentR (μ κ : Lv) : Semiformula LRA ℕ 1 := ∼(tiMuR μ) ⋎ psiR κ

theorem lvlOf_descentR_le {μ κ : Lv} (hκ : κ < μ) : lvlOf (descentR μ κ) ≤ μ := by
  rw [descentR, lvlOf_or, lvlOf_neg]
  exact max_le (lvlOf_tiMuR_le μ) (le_trans (lvlOf_psiR_le κ) hκ.le)

section Model

variable {M : Type} [Nonempty M] [s : Structure LRA M] [Structure.Eq LRA M] {ν μ κ : Lv}

/-- **(D_{μ,κ}) in a model**: `TI_μ(b) → ψ_κ(b)`, for `0 < κ < μ < ν`. -/
theorem descent_M (hM : M↓[LRA] ⊧* RAlt ν) (h0 : 0 < κ) (hκ : κ < μ) (hμ : μ < ν) {b : M}
    (hb : TImu μ b) : PsiM κ b := by
  have hμ0 : 0 < μ := lt_trans h0 hκ
  have hκν : κ < ν := lt_trans hκ hμ
  have hshape : Shape μ (psiR κ) :=
    shape_of_lvlOf_lt (lt_of_le_of_lt (lvlOf_psiR_le κ) hκ)
  obtain ⟨w, hw⟩ := comprM hM hμ0 hμ hshape (Classical.arbitrary M)
  have hwS : ∀ x, memM μ x w ↔ PsiM κ x := fun x => (hw x).trans (eval_psiR _ x _)
  have hprog := epsProg_M hM h0 hκν
  have hbelow : ∀ y, precM y b → PsiM κ y :=
    (TIupM_congr hwS b).mp (hb w) hprog
  exact hprog b hbelow

end Model

/-- **(D_{μ,κ})**: `RAlt ν ⊢ ∀b (TI_μ(b) → ψ_κ(b))`, for `0 < κ < μ < ν`. -/
theorem descent_provable {ν μ κ : Lv} (h0 : 0 < κ) (hκ : κ < μ) (hμ : μ < ν) :
    RAlt ν ⊢ Semiformula.univCl (∀¹ descentR μ κ) := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos (lt_trans (lt_trans h0 hκ) hμ)
  refine provable_of_eqModels hν ?_ ?_
  · rw [lvlOf_emb_univCl, lvlOf_all]
    exact lt_of_le_of_lt (lvlOf_descentR_le hκ) hμ
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f (∀¹ descentR μ κ)
    rw [Semiformula.eval_all]
    intro b
    have hb : (b :> (![] : Fin 0 → N)) = ![b] := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rfl
    rw [hb, descentR, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
      eval_tiMuR, eval_psiR]
    by_cases h : TImu μ b
    · exact Or.inr (descent_M hN h0 hκ hμ h)
    · exact Or.inl h

end Ramified

end OrdinalAnalysis
