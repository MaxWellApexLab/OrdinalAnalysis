/-
  The provability half of the ordinal analysis of `RA_{<ν+1}`, and the
  two-sided theorem.

  **Upper bound** (`ramified_upper_bound`).  For `ν ≥ 1` and every Veblen
  notation `a < φ_1^ν(ε₀)`, `RAlt (ν+1)` proves transfinite induction along the
  coded Veblen ordering restricted to the segment below `φ_1^ν(ε₀)`, up to `a`,
  for the free predicate `X`:

      RAlt (ν+1) ⊢ Prog(≺_b, X) → ∀y ≺_b ā, X(y)        (b = φ_1^ν(ε₀))

  (`tiUptoSegR b a`), where `y ≺_b x :≡ y ≺₁ x ∧ x ≺₁ b̄`.

  The proof, in a model of `RAlt (ν+1)` with true equality:

  1. Since `φ_1^ν` is a normal function and `ε₀` a limit, `φ_1^ν(ε₀)` is the
     supremum of `φ_1^ν(c)` for `c < ε₀`; so `a < φ_1^ν(c)` for some `c < ε₀`,
     which may be taken of the form `ω^ω^…^0` (`exists_lt_veblenIter`).
  2. At the top level `ν`, (A_ν) gives `TI_ν(ε_c)` (`Ramified/EpsProgR.lean`).
  3. The descents (D_ν), …, (D_2) (`Ramified/DescentR.lean`) give
     `TI_{ν−j}(φ_1^{j+1}(c))` for `j = 0, …, ν − 1`; at `j = ν − 1`, transfinite
     induction below `φ_1^ν(c)` for every level-`1` set (`levels_M`).
  4. Level `1` names the set `G = {y | y ≺₁ b̄ → X(y)}` (its defining formula
     has no set atoms).  If `X` is `≺_b`-progressive then `G` is
     `≺₁`-progressive, so `G` holds below `φ_1^ν(c)`, hence below `ā`, and on
     `{y ≺_b ā}` this is `X(y)`.

  **The two-sided theorem** (`ramified_theorem`).  The non-provability half,
  `Ramified/LowerBound.lean`'s `ramified_lower_bound`, refutes
  `TI(≺_b, X) :≡ Prog(≺_b, X) → ∀y X(y)` for the same segment ordering: its
  ordering `(vebSegOrderR 1 (φ_1^{ν−1}(ε₀)) _).prec` is `precBelowR b` by
  `φ_1(φ_1^{ν−1}(ε₀)) = φ_1^ν(ε₀)` (`vebSegOrderR_prec_eq`).  So `RAlt (ν+1)`
  proves transfinite induction along `≺_b` up to every `a < b`, and not along
  the whole of `≺_b`.
-/
import OrdinalAnalysis.Ramified.DescentR
import OrdinalAnalysis.Ramified.LowerBound

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalVNote (precDef₁)
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)
open OrdinalAnalysis.Gentzen.VeblenEpsilon0UpperBound (vtower repr_vtower)
open OrdinalAnalysis.Gamma0Note (epsilonNote veblenNote)
open OrdinalAnalysis.Ramified.OmegaDerivableR (veblenIter veblenIter_zero)

/-! ### Cofinality of `φ_1^ν(c)`, `c < ε₀`, below `φ_1^ν(ε₀)` -/

open Ordinal in
theorem repr_veblenIter_one : ∀ (m : ℕ) (x : Gamma0Note),
    Gamma0Note.repr (veblenIter 1 m x) = (Ordinal.veblen 1)^[m] (Gamma0Note.repr x)
  | 0, _ => rfl
  | m + 1, x => by
      rw [veblenIter_succ', Gamma0Note.repr_veblenNote, repr_veblenIter_one m x,
        Gamma0Note.repr_one, Function.iterate_succ_apply']

open Ordinal in
theorem isNormal_iterate_veblen_one : ∀ m : ℕ, Order.IsNormal ((Ordinal.veblen 1)^[m])
  | 0 => Order.IsNormal.id
  | m + 1 => by
      rw [Function.iterate_succ]
      exact (isNormal_iterate_veblen_one m).comp (Ordinal.isNormal_veblen 1)

open Ordinal in
theorem isSuccLimit_epsilon_zero : Order.IsSuccLimit (Ordinal.epsilon 0) := by
  rw [← Ordinal.omega0_opow_epsilon 0]
  exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (Ordinal.epsilon_pos 0).ne'

theorem vtower_lt_epsilon_zero (n : ℕ) : vtower n < epsilonNote 0 := by
  rw [Gamma0Note.lt_def, Gamma0Note.epsilonNote_zero_repr, repr_vtower]
  exact Ordinal.iterate_omega0_opow_lt_epsilon_zero n

/-- **Every `a < φ_1^ν(ε₀)` lies below `φ_1^ν(c)` for some `c < ε₀`.** -/
theorem exists_lt_veblenIter (m : ℕ) (a : Gamma0Note)
    (ha : a < veblenIter 1 m (epsilonNote 0)) :
    ∃ c : Gamma0Note, c < epsilonNote 0 ∧ a < veblenIter 1 m c := by
  rw [Gamma0Note.lt_def, repr_veblenIter_one, Gamma0Note.epsilonNote_zero_repr] at ha
  obtain ⟨γ, hγ, haγ⟩ :=
    ((isNormal_iterate_veblen_one m).lt_iff_exists_lt isSuccLimit_epsilon_zero).mp ha
  rw [Ordinal.lt_epsilon_zero] at hγ
  obtain ⟨n, hn⟩ := hγ
  refine ⟨vtower n, vtower_lt_epsilon_zero n, ?_⟩
  rw [Gamma0Note.lt_def, repr_veblenIter_one, repr_vtower]
  exact lt_trans haγ ((isNormal_iterate_veblen_one m).strictMono hn)

/-! ### The descent through all the levels, in a model -/

section Levels

variable {M : Type} [Nonempty M] [s : Structure LRA M] [Structure.Eq LRA M] {ν : ℕ}

/-- **`TI_{ν−j}(φ_1^{j+1}(c̄))`** in a model of `RAlt (ν+1)`, for `j < ν` and an
external `c < ε₀`. -/
theorem levels_M (hM : M↓[LRA] ⊧* RAlt (ν + 1)) {c : Gamma0Note} (hc : c < epsilonNote 0) :
    ∀ j : ℕ, j + 1 ≤ ν →
      TImu (ν - j) (numVal M (gamma0Code (veblenIter 1 (j + 1) c)))
  | 0, h => by
      have h0 : 0 < ν := h
      rw [Nat.sub_zero, veblenIter_succ', veblenIter_zero]
      exact ti_epsilon_M hM h0 (Nat.lt_succ_self ν) hc
  | j + 1, h => by
      have hν1 : 1 ≤ ν + 1 := Nat.succ_le_succ (Nat.zero_le ν)
      have hprev := levels_M hM hc j (by omega)
      have h2 : 2 ≤ ν - j := by omega
      have hlt : ν - j < ν + 1 := by omega
      have hpsi := descent_M hM h2 hlt hprev
      have hsub : ν - (j + 1) = ν - j - 1 := by omega
      rw [hsub, veblenIter_succ' 1 (j + 1) c]
      exact hpsi _ (epsM_code hM hν1 (veblenIter 1 (j + 1) c))

/-- **`TI_1(φ_1^ν(c̄))`**: transfinite induction below `φ_1^ν(c)` for every
level-`1` set. -/
theorem level_one_M (hM : M↓[LRA] ⊧* RAlt (ν + 1)) (hν : 1 ≤ ν) {c : Gamma0Note}
    (hc : c < epsilonNote 0) : TImu 1 (numVal M (gamma0Code (veblenIter 1 ν c))) := by
  have h := levels_M hM hc (ν - 1) (by omega)
  have e1 : ν - (ν - 1) = 1 := by omega
  have e2 : ν - 1 + 1 = ν := by omega
  rw [e1, e2] at h
  exact h

end Levels

/-! ### The segment ordering and the upper-bound sentence -/

/-- **`y ≺_b x :≡ y ≺₁ x ∧ x ≺₁ b̄`**, the coded Veblen ordering restricted to the
segment below `b`. -/
def precBelowR (b : Gamma0Note) : Semiformula LRA ℕ 2 :=
  precCode₁R ⋏ precAt precCode₁R (#1 : Semiterm LRA ℕ 2) (numAtR (gamma0Code b) : Semiterm LRA ℕ 2)

/-- The segment ordering of `Ramified/SegOrder.lean` is `precBelowR` at its bound. -/
theorem precSegVebR_eq (a b : Gamma0Note) : precSegVebR a b = precBelowR (veblenNote a b) := rfl

/-- **`TI(≺_b, ā, X) :≡ Prog(≺_b, X) → ∀y ≺_b ā, X(y)`**, universally closed. -/
noncomputable def tiUptoSegR (b a : Gamma0Note) : Sentence LRA :=
  Semiformula.univCl (∼(Prog (precBelowR b)) ⋎
    (∀¹ (∼(precAt (precBelowR b) (#0 : Semiterm LRA ℕ 1) (numAtR (gamma0Code a))) ⋎
      Xat (#0 : Semiterm LRA ℕ 1))))

/-- The guard `y ≺₁ b̄ → X(y)`, a formula without set atoms. -/
def segGuardR (b : Gamma0Note) : Semiformula LRA ℕ 1 :=
  ∼(precAt precCode₁R (#0 : Semiterm LRA ℕ 1) (numAtR (gamma0Code b))) ⋎ Xat (#0 : Semiterm LRA ℕ 1)

theorem lvlOf_segGuardR (b : Gamma0Note) : lvlOf (segGuardR b) = 0 := by
  simp [segGuardR, precAt, precCode₁R, lvlOf_lMap_toLRA]

/-! ### Reading the segment sentences in a model -/

section Eval

variable {M : Type} [s : Structure LRA M]

/-- `X(x)` in `M`. -/
def XM (x : M) : Prop := s.rel (Sum.inr RARel.X : LRA.Rel 1) ![x]

theorem eval_Xat_model {n : ℕ} (t : Semiterm LRA ℕ n) (e : Fin n → M) (f : ℕ → M) :
    Semiformula.Eval (s := s) e f (Xat t) ↔ XM (Semiterm.val (s := s) e f t) := by
  have h : (fun i => Semiterm.val (s := s) e f ((![t] : Fin 1 → Semiterm LRA ℕ n) i)) =
      ![Semiterm.val (s := s) e f t] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  show s.rel (Sum.inr RARel.X : LRA.Rel 1)
      (fun i => Semiterm.val (s := s) e f ((![t] : Fin 1 → Semiterm LRA ℕ n) i)) ↔ _
  rw [h]
  rfl

theorem eval_precCode₁R_model (y x : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![y, x] f precCode₁R ↔ precM y x := by
  rw [precCode₁R, Semiformula.eval_lMap]
  exact Semiformula.eval_emb (s := s.lMap toLRA) _

theorem eval_precAt_model (prec : Semiformula LRA ℕ 2) {n : ℕ} (y x : Semiterm LRA ℕ n)
    (e : Fin n → M) (f : ℕ → M) :
    Semiformula.Eval (s := s) e f (precAt prec y x) ↔
      Semiformula.Eval (s := s) ![Semiterm.val (s := s) e f y, Semiterm.val (s := s) e f x] f
        prec := by
  rw [precAt, Semiformula.eval_rew]
  have hb : (Semiterm.val (s := s) e f ∘ ⇑(Rew.subst ![y, x]) ∘ Semiterm.bvar) =
      ![Semiterm.val (s := s) e f y, Semiterm.val (s := s) e f x] := by
    funext i
    fin_cases i <;> simp
  have hf : (Semiterm.val (s := s) e f ∘ ⇑(Rew.subst ![y, x]) ∘ Semiterm.fvar) = f := by
    funext i
    simp
  rw [hb, hf]

theorem eval_precBelowR (b : Gamma0Note) (y x : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![y, x] f (precBelowR b) ↔
      precM y x ∧ precM x (numVal M (gamma0Code b)) := by
  rw [precBelowR, LogicalConnective.HomClass.map_and, eval_precAt_model, eval_precCode₁R_model,
    Semiterm.val_bvar, val_numAtR_model]
  simp only [Matrix.cons_val_one, Matrix.head_cons]
  rw [eval_precCode₁R_model]
  rfl

theorem eval_segGuardR (b : Gamma0Note) (y : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![y] f (segGuardR b) ↔
      (precM y (numVal M (gamma0Code b)) → XM y) := by
  rw [segGuardR, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    eval_precAt_model, eval_Xat_model, Semiterm.val_bvar, val_numAtR_model,
    eval_precCode₁R_model]
  simp only [Matrix.cons_val_zero, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq]
  exact imp_iff_not_or.symm

theorem eval_tiUptoSegR_body (b a : Gamma0Note) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (∼(Prog (precBelowR b)) ⋎
      (∀¹ (∼(precAt (precBelowR b) (#0 : Semiterm LRA ℕ 1) (numAtR (gamma0Code a))) ⋎
        Xat (#0 : Semiterm LRA ℕ 1)))) ↔
      ((∀ x : M, (∀ y : M, precM y x ∧ precM x (numVal M (gamma0Code b)) → XM y) → XM x) →
        ∀ y : M, precM y (numVal M (gamma0Code a)) ∧
          precM (numVal M (gamma0Code a)) (numVal M (gamma0Code b)) → XM y) := by
  simp only [Prog, below, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    Semiformula.eval_all, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq,
    eval_precAt_model, eval_Xat_model, Semiterm.val_bvar, val_numAtR_model, eval_precBelowR,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  constructor
  · rintro (h | h) hprog y hy
    · refine absurd (fun x => ?_) h
      by_cases hx : XM x
      · exact Or.inr hx
      · exact Or.inl fun hall => hx (hprog x fun y hy => (hall y).resolve_left (not_not_intro hy))
    · exact (h y).resolve_left (not_not_intro hy)
  · intro h
    by_cases hprog : ∀ x : M, (∀ y : M, precM y x ∧ precM x (numVal M (gamma0Code b)) → XM y) →
        XM x
    · exact Or.inr fun y => imp_iff_not_or.mp (h hprog y)
    · refine Or.inl fun hall => hprog fun x hx => ?_
      rcases hall x with h1 | h1
      · exact absurd (fun y => imp_iff_not_or.mp (hx y)) h1
      · exact h1

end Eval

/-! ### The upper bound -/

section Model

variable {M : Type} [Nonempty M] [s : Structure LRA M] [Structure.Eq LRA M] {ν : ℕ}

/-- **The upper bound in a model**: in every model of `RAlt (ν+1)` with true
equality, `X` satisfies transfinite induction along `≺_b` up to `ā`, for
`b = φ_1^ν(ε₀)` and every `a < b`. -/
theorem upper_M (hM : M↓[LRA] ⊧* RAlt (ν + 1)) (hν : 1 ≤ ν) {a : Gamma0Note}
    (ha : a < veblenIter 1 ν (epsilonNote 0)) :
    (∀ x : M, (∀ y : M, precM y x ∧
        precM x (numVal M (gamma0Code (veblenIter 1 ν (epsilonNote 0)))) → XM y) → XM x) →
      ∀ y : M, precM y (numVal M (gamma0Code a)) ∧
        precM (numVal M (gamma0Code a))
          (numVal M (gamma0Code (veblenIter 1 ν (epsilonNote 0)))) → XM y := by
  have hν1 : 1 ≤ ν + 1 := Nat.succ_le_succ (Nat.zero_le ν)
  set B : M := numVal M (gamma0Code (veblenIter 1 ν (epsilonNote 0)))
  obtain ⟨c, hc, hac⟩ := exists_lt_veblenIter ν a ha
  have h1 := level_one_M hM hν hc
  have hshape : Shape 1 (segGuardR (veblenIter 1 ν (epsilonNote 0))) :=
    shape_of_lvlOf_lt (by rw [lvlOf_segGuardR]; exact Nat.one_pos)
  obtain ⟨w, hw⟩ := comprM hM Nat.one_pos (Nat.succ_lt_succ (lt_of_lt_of_le Nat.zero_lt_one hν))
    hshape (Classical.arbitrary M)
  have hG : ∀ x, memM 1 x w ↔ (precM x B → XM x) := fun x =>
    (hw x).trans (eval_segGuardR _ x _)
  have hTI := (TIupM_congr hG _).mp (h1 w)
  intro hprog y hy
  have hprogG : ProgM (fun x : M => precM x B → XM x) := fun x hx hxB =>
    hprog x fun y hy' => hx y hy'.1 (precM_trans hM hν1 hy'.1 hxB)
  have hAc := precM_code (M := M) hM hν1 hac
  exact hTI hprogG y (precM_trans hM hν1 hy.1 hAc) (precM_trans hM hν1 hy.1 hy.2)

end Model

/-- **The provability half of the ordinal analysis of `RA_{<ν+1}`.**  For `ν ≥ 1`
and every Veblen notation `a < φ_1^ν(ε₀)`, `RA_{<ν+1}` proves transfinite
induction for `X` along the coded Veblen ordering restricted to the segment
below `φ_1^ν(ε₀)`, up to `a`. -/
theorem ramified_upper_bound (ν : ℕ) (hν : 1 ≤ ν) (a : Gamma0Note)
    (ha : a < veblenIter 1 ν (epsilonNote 0)) :
    RAlt (ν + 1) ⊢ tiUptoSegR (veblenIter 1 ν (epsilonNote 0)) a := by
  have hν1 : 1 ≤ ν + 1 := Nat.succ_le_succ (Nat.zero_le ν)
  refine provable_of_eqModels hν1 ?_ ?_
  · rw [tiUptoSegR, lvlOf_emb_univCl]
    have h0 : lvlOf (∼(Prog (precBelowR (veblenIter 1 ν (epsilonNote 0)))) ⋎
        (∀¹ (∼(precAt (precBelowR (veblenIter 1 ν (epsilonNote 0))) (#0 : Semiterm LRA ℕ 1)
          (numAtR (gamma0Code a))) ⋎ Xat (#0 : Semiterm LRA ℕ 1)))) = 0 := by
      simp [Prog, below, precAt, precBelowR, precCode₁R, lvlOf_lMap_toLRA]
    rw [h0]
    exact Nat.succ_pos ν
  · intro N _ sN _ hN
    rw [tiUptoSegR, models_iff_proposition]
    intro f
    exact (eval_tiUptoSegR_body _ a f).mpr (upper_M hN hν ha)

/-- The ordering refuted by `Ramified/LowerBound.lean`'s `ramified_lower_bound` is
the segment ordering `≺_b` for `b = φ_1^ν(ε₀)`. -/
theorem vebSegOrderR_prec_eq (ν : ℕ) (hν : 1 ≤ ν) :
    (vebSegOrderR 1 (veblenIter 1 (ν - 1) (epsilonNote 0)) Gamma0Note.zero_lt_one).prec =
      precBelowR (veblenIter 1 ν (epsilonNote 0)) := by
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, (Nat.sub_add_cancel hν).symm⟩
  rw [Nat.add_sub_cancel, veblenIter_succ']
  rfl

/-- **The ordinal analysis of `RA_{<ν+1}`, both halves**, for `ν ≥ 1` and
`b = φ_1^ν(ε₀)`: `RAlt (ν+1)` proves transfinite induction for `X` along the
segment ordering `≺_b` up to every `a < b`, and does not prove transfinite
induction for `X` along the whole of `≺_b`. -/
theorem ramified_theorem (ν : ℕ) (hν : 1 ≤ ν) :
    (∀ a : Gamma0Note, a < veblenIter 1 ν (epsilonNote 0) →
        RAlt (ν + 1) ⊢ tiUptoSegR (veblenIter 1 ν (epsilonNote 0)) a) ∧
      RAlt (ν + 1) ⊬ (Semiformula.univCl
        (TIR (precBelowR (veblenIter 1 ν (epsilonNote 0)))) : Sentence LRA) := by
  refine ⟨fun a ha => ramified_upper_bound ν hν a ha, ?_⟩
  have h := ramified_lower_bound ν hν
  rwa [vebSegOrderR_prec_eq ν hν] at h

end Ramified

end OrdinalAnalysis
