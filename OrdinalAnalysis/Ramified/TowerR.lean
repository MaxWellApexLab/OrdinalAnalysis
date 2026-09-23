/-
  The internal ω-tower induction at a level `μ` of ramified analysis:

      RAlt ν ⊢ ∀n ∀c ∀u (Tower(u, n, c) → TI_μ(c) → TI_μ(u))      (0 < μ < ν)

  where `TI_μ(a) :≡ ∀z TI(≺₁, a, λx. x ∈̇_μ z)` is transfinite induction below
  `a` for every set of level `μ`, and `Tower(u, n, c)` is the graph of the
  internal tower `u = ω^ω^…^c` (`n` exponentials, `Gentzen/VeblenTower.lean`).

  The induction formula

      θ_μ(n) :≡ ∀c ∀u (Tower(u, n, c) → TI_μ(c) → TI_μ(u))

  mentions the membership symbol of level `μ` only, so it is a formula of level
  `μ < ν` and its induction axiom belongs to `RAlt ν`.  The zero step is the
  first tower law (`Tower(u, 0, c) → u = c`).  In the successor step,
  `Tower(u, n+1, c)` gives `v` with `Tower(v, n, c)` and `u = ω^v`; for a level-`μ`
  set `z`, comprehension with a same-level parameter
  (`Ramified/Comprehension.lean`'s jump code) gives a level-`μ` set `w` whose
  members are exactly those of the jump of `z`; the induction hypothesis at `w`
  gives `TI(≺₁, v, Jump z)`, and Gentzen's Lemma B, lifted at the level-`μ`
  predicate `λx. x ∈̇_μ z`, gives `TI(≺₁, ω^v, z)`.

  The argument is carried out in an arbitrary model of `RAlt ν` with true
  equality (`tower_TImu`) and turned into provability by
  `Ramified/LiftR.lean`'s `provable_of_eqModels` (`tower_provable`).
-/
import OrdinalAnalysis.Ramified.LiftRAux

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen (LX paLX)
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁)
open OrdinalAnalysis.Gentzen.VeblenTower (towerDef₁)

/-! ### Arithmetical formulas of `LRA` -/

/-- An arithmetical semisentence, read in `LRA`. -/
def arR {k : ℕ} (σ : ArithmeticSemisentence k) : Semiformula LRA ℕ k :=
  Semiformula.lMap toLRA (Rewriting.emb σ)

/-- An arithmetical semisentence at the terms `v`. -/
def arAt {k n : ℕ} (σ : ArithmeticSemisentence k) (v : Fin k → Semiterm LRA ℕ n) :
    Semiformula LRA ℕ n :=
  Rew.subst v ▹ arR σ

@[simp] theorem lvlOf_arAt {k n : ℕ} (σ : ArithmeticSemisentence k) (v : Fin k → Semiterm LRA ℕ n) :
    lvlOf (arAt σ v) = 0 := by
  rw [arAt, lvlOf_rew, arR, lvlOf_lMap_toLRA]

section Eval

variable {M : Type} [s : Structure LRA M]

theorem eval_arAt {k n : ℕ} (σ : ArithmeticSemisentence k) (v : Fin k → Semiterm LRA ℕ n)
    (e : Fin n → M) (f : ℕ → M) :
    Semiformula.Eval (s := s) e f (arAt σ v) ↔
      arEval σ (fun i => Semiterm.val (s := s) e f (v i)) := by
  rw [arAt, Semiformula.eval_rew, arR, Semiformula.eval_lMap]
  exact Semiformula.eval_emb (s := s.lMap toLRA) σ

end Eval

/-! ### Transfinite induction for every set of level `μ` -/

/-- `TI(≺₁, a, X)`, with `a` the bound variable. -/
def tiXF : Semiformula LX ℕ 1 :=
  Gentzen.tiUptoAt precCode₁ (Gentzen.Xat (#0 : Semiterm LX ℕ 1)) (#0 : Semiterm LX ℕ 1)

/-- **`TI_μ(a) :≡ ∀z TI(≺₁, a, λx. x ∈̇_μ z)`**, with `a` the bound variable. -/
def tiMuR (μ : Lv) : Semiformula LRA ℕ 1 :=
  ∀¹ (Rew.bind ![(#1 : Semiterm LRA ℕ 2)] (fun _ => #0) ▹ xMem μ tiXF)

theorem lvlOf_tiMuR_le (μ : Lv) : lvlOf (tiMuR μ) ≤ μ := by
  rw [tiMuR, lvlOf_all, lvlOf_rew]
  exact lvlOf_xMem_le μ tiXF

section Model

variable {M : Type} [s : Structure LRA M]

/-- `TI_μ(a)` in `M`: transfinite induction below `a` for every level-`μ` set. -/
def TImu (μ : Lv) (a : M) : Prop := ∀ z : M, TIupM (fun x => memM μ x z) a

theorem eval_tiMuR (μ : Lv) (a : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![a] f (tiMuR μ) ↔ TImu μ a := by
  rw [tiMuR, Semiformula.eval_all]
  refine forall_congr' fun z => ?_
  rw [Semiformula.eval_rew]
  have hb : (Semiterm.val (s := s) (z :> ![a]) f ∘
      ⇑(Rew.bind (ξ₁ := ℕ) ![(#1 : Semiterm LRA ℕ 2)] (fun _ => (#0 : Semiterm LRA ℕ 2))) ∘
        Semiterm.bvar) = ![a] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  have hf : (Semiterm.val (s := s) (z :> ![a]) f ∘
      ⇑(Rew.bind (ξ₁ := ℕ) ![(#1 : Semiterm LRA ℕ 2)] (fun _ => (#0 : Semiterm LRA ℕ 2))) ∘
        Semiterm.fvar) = fun _ => z := rfl
  rw [hb, hf, eval_xMem, tiXF, eval_tiUptoAt_Xat_lxStr]
  rfl

theorem eval_tiMuR_subst (μ : Lv) {n : ℕ} (t : Semiterm LRA ℕ n) (e : Fin n → M) (f : ℕ → M) :
    Semiformula.Eval (s := s) e f ((tiMuR μ)/[t]) ↔ TImu μ (Semiterm.val (s := s) e f t) := by
  rw [Semiformula.eval_substs]
  have h : (Semiterm.val (s := s) e f ∘ ![t]) = ![Semiterm.val (s := s) e f t] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  rw [h, eval_tiMuR]

theorem TIupM_congr {P Q : M → Prop} (h : ∀ x, P x ↔ Q x) (a : M) : TIupM P a ↔ TIupM Q a := by
  have hPQ : P = Q := funext fun x => propext (h x)
  rw [hPQ]

end Model

/-! ### The induction formula -/

/-- **`θ_μ(n) :≡ ∀c ∀u (Tower(u, n, c) → TI_μ(c) → TI_μ(u))`.** -/
def thetaR (μ : Lv) : Semiformula LRA ℕ 1 :=
  ∀¹ ∀¹ (∼(arAt towerDef₁.val ![(#0 : Semiterm LRA ℕ 3), #2, #1]) ⋎
    (∼((tiMuR μ)/[(#1 : Semiterm LRA ℕ 3)]) ⋎ (tiMuR μ)/[(#0 : Semiterm LRA ℕ 3)]))

theorem lvlOf_thetaR_le (μ : Lv) : lvlOf (thetaR μ) ≤ μ := by
  simp only [thetaR, lvlOf_all, lvlOf_or, lvlOf_neg, lvlOf_arAt, lvlOf_subst₁]
  exact max_le (Nat.zero_le μ) (max_le (lvlOf_tiMuR_le μ) (lvlOf_tiMuR_le μ))

section Model

variable {M : Type} [s : Structure LRA M]

theorem eval_thetaR (μ : Lv) (n : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![n] f (thetaR μ) ↔
      ∀ c u : M, towerM u n c → TImu μ c → TImu μ u := by
  simp only [thetaR, Semiformula.eval_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq, eval_arAt, eval_tiMuR_subst, Semiterm.val_bvar,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine forall_congr' fun c => forall_congr' fun u => ?_
  have ht : arEval towerDef₁.val
      (fun i => Semiterm.val (s := s) (u :> c :> ![n]) f
        (![(#0 : Semiterm LRA ℕ 3), #2, #1] i)) ↔ towerM u n c := by
    have hv : (fun i => Semiterm.val (s := s) (u :> c :> ![n]) f
        (![(#0 : Semiterm LRA ℕ 3), #2, #1] i)) = ![u, n, c] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    rfl
  rw [ht]
  tauto

end Model

/-! ### The tower induction in a model -/

section Tower

variable {M : Type} [Nonempty M] [s : Structure LRA M] [Structure.Eq LRA M] {ν μ : Lv}

omit [Structure.Eq LRA M] in
/-- **The jump of a level-`μ` set is a level-`μ` set**, in `M`. -/
theorem jump_code_M (hM : M↓[LRA] ⊧* RAlt ν) (h0 : 0 < μ) (hμ : μ < ν) (z : M) :
    ∃ w : M, ∀ x : M, memM μ x w ↔ JumpM (fun y => memM μ y z) x := by
  obtain ⟨w, hw⟩ := comprM hM h0 hμ (shape_jumpR μ) z
  refine ⟨w, fun x => (hw x).trans ?_⟩
  rw [jumpR, eval_xMem]
  exact eval_jump_lxStr _ x _

/-- **(Tw_μ) in a model**: `Tower(u, n, c) → TI_μ(c) → TI_μ(u)`. -/
theorem tower_TImu (hM : M↓[LRA] ⊧* RAlt ν) (h0 : 0 < μ) (hμ : μ < ν) :
    ∀ n c u : M, towerM u n c → TImu μ c → TImu μ u := by
  have hν : 1 ≤ ν := Nat.succ_le_of_lt (lt_trans h0 hμ)
  let f : ℕ → M := fun _ => Classical.arbitrary M
  have H := indM hM (thetaR μ) (lt_of_le_of_lt (lvlOf_thetaR_le μ) hμ) f ?_ ?_
  · intro n
    exact (eval_thetaR μ n f).mp (H n)
  · rw [eval_thetaR]
    intro c u htw hc
    rw [towerM_zero hM hν htw]
    exact hc
  · intro k hk
    rw [eval_thetaR] at hk ⊢
    intro c u htw hc z
    obtain ⟨v, hv, hω⟩ := towerM_succ hM hν htw
    have hTv : TImu μ v := hk c v hv hc
    obtain ⟨w, hw⟩ := jump_code_M hM h0 hμ z
    have hJ : TIupM (JumpM (fun y => memM μ y z)) v := (TIupM_congr hw v).mp (hTv w)
    exact jumpB_M hM (definableLt_mem hμ z) hω hJ

end Tower

/-! ### The provable form -/

/-- **(Tw_μ)**: `RAlt ν ⊢ ∀n ∀c ∀u (Tower(u, n, c) → TI_μ(c) → TI_μ(u))`, for
`0 < μ < ν`. -/
theorem tower_provable {ν μ : Lv} (h0 : 0 < μ) (hμ : μ < ν) :
    RAlt ν ⊢ Semiformula.univCl (∀¹ thetaR μ) := by
  have hν : 1 ≤ ν := Nat.succ_le_of_lt (lt_trans h0 hμ)
  refine provable_of_eqModels hν ?_ ?_
  · rw [lvlOf_emb_univCl, lvlOf_all]
    exact lt_of_le_of_lt (lvlOf_thetaR_le μ) hμ
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f (∀¹ thetaR μ)
    rw [Semiformula.eval_all]
    intro n
    have hn : (n :> (![] : Fin 0 → N)) = ![n] := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rfl
    rw [hn, eval_thetaR]
    exact tower_TImu hN h0 hμ n

end Ramified

end OrdinalAnalysis
