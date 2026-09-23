/-
  The descent from one level of ramified analysis to the one below:

      RAlt ν ⊢ ∀b (TI_μ(b) → ∀u (Eps(u, b) → TI_{μ−1}(u)))        (2 ≤ μ < ν)

  that is, transfinite induction below `b` for every level-`μ` set gives
  transfinite induction below `ε_b` for every level-`(μ−1)` set.

  The formula `ψ_{μ−1}(g) :≡ ∀u (Eps(u, g) → TI_{μ−1}(u))` of
  `Ramified/EpsProgR.lean` is closed and has level `μ − 1 < μ`, so it has shape
  `μ`, and comprehension at level `μ` (`Ramified/Comprehension.lean`) names the
  set `S = {g | ψ_{μ−1}(g)}` by a level-`μ` set `w`.  Instantiating `TI_μ(b)` at
  `w`: `S` is progressive by (EP_{μ−1}), so every `g ≺₁ b` lies in `S`; one more
  application of (EP_{μ−1}) at `b` gives `ψ_{μ−1}(b)`.

  This is the only way the levels interact: each level applies `ε` once.
-/
import OrdinalAnalysis.Ramified.EpsProgR

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- The matrix of the descent: `TI_μ(b) → ψ_{μ−1}(b)`, with `b` the bound
variable. -/
def descentR (μ : Lv) : Semiformula LRA ℕ 1 := ∼(tiMuR μ) ⋎ psiR (μ - 1)

theorem lvlOf_descentR_le (μ : Lv) : lvlOf (descentR μ) ≤ μ := by
  rw [descentR, lvlOf_or, lvlOf_neg]
  exact max_le (lvlOf_tiMuR_le μ) (le_trans (lvlOf_psiR_le (μ - 1)) (Nat.sub_le μ 1))

section Model

variable {M : Type} [Nonempty M] [s : Structure LRA M] [Structure.Eq LRA M] {ν μ : Lv}

/-- **(D_μ) in a model**: `TI_μ(b) → ψ_{μ−1}(b)`, for `2 ≤ μ < ν`. -/
theorem descent_M (hM : M↓[LRA] ⊧* RAlt ν) (h2 : 2 ≤ μ) (hμ : μ < ν) {b : M}
    (hb : TImu μ b) : PsiM (μ - 1) b := by
  have h0 : 0 < μ := lt_of_lt_of_le Nat.two_pos h2
  have h0' : 0 < μ - 1 := Nat.sub_pos_of_lt (lt_of_lt_of_le Nat.one_lt_two h2)
  have hμ' : μ - 1 < ν := lt_of_le_of_lt (Nat.sub_le μ 1) hμ
  have hshape : Shape μ (psiR (μ - 1)) :=
    shape_of_lvlOf_lt (lt_of_le_of_lt (lvlOf_psiR_le (μ - 1)) (Nat.sub_lt h0 Nat.one_pos))
  obtain ⟨w, hw⟩ := comprM hM h0 hμ hshape (Classical.arbitrary M)
  have hwS : ∀ x, memM μ x w ↔ PsiM (μ - 1) x := fun x => (hw x).trans (eval_psiR _ x _)
  have hprog := epsProg_M hM h0' hμ'
  have hbelow : ∀ y, precM y b → PsiM (μ - 1) y :=
    (TIupM_congr hwS b).mp (hb w) hprog
  exact hprog b hbelow

end Model

/-- **(D_μ)**: `RAlt ν ⊢ ∀b (TI_μ(b) → ψ_{μ−1}(b))`, for `2 ≤ μ < ν`. -/
theorem descent_provable {ν μ : Lv} (h2 : 2 ≤ μ) (hμ : μ < ν) :
    RAlt ν ⊢ Semiformula.univCl (∀¹ descentR μ) := by
  have hν : 1 ≤ ν := le_trans (le_trans (Nat.le_succ 1) h2) hμ.le
  refine provable_of_eqModels hν ?_ ?_
  · rw [lvlOf_emb_univCl, lvlOf_all]
    exact lt_of_le_of_lt (lvlOf_descentR_le μ) hμ
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f (∀¹ descentR μ)
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
    · exact Or.inr (descent_M hN h2 hμ h)
    · exact Or.inl h

end Ramified

end OrdinalAnalysis
