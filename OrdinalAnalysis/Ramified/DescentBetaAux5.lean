/-
  The induction formula of Step 1 and two small facts about `Acc`.

  For a Veblen index `a` and a level `L`, the induction formula is

      F_{a,L}(g) :≡ ∀u (Veb(u, a, g) → Acc_L(u))                  (`vebF a L`)

  of level at most `L`, together with `∀y (y ≺₁ h → F(y))` (`hypF`) and the matrix
  of `Prog(≺₁, φ)` (`progBody`), and their meaning in an arbitrary structure.
  The instance of `F_{a,L}(h̄)` at `ū` is evaluated in `eval_vebF_inst`.

  The two small facts about `Acc` used in the instances of Step 1: `Acc_μ(0)`
  (`accZeroD`, vacuously: nothing lies below `0`) and `Acc_μ(e) → Acc_μ(e ⊕ 1)`
  (`succD`: below `e ⊕ 1` lie `e` and what lies below `e`), both by `accIntro`.
-/
import OrdinalAnalysis.Ramified.DescentBetaAux4

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalVNote (precDef₁)
open OrdinalAnalysis.Gentzen.InternalVeblenCode (vebDef₁)
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)

/-! ### The induction formula and its companions -/

/-- The matrix of `F_{a,L}`: `Veb(u, a, g) → Acc_L(u)`, with `u = #0`, `g = #1`. -/
def vebBody (a : Gamma0Note) (L : Lv) : Semiformula LRA ℕ 2 :=
  ∼(arAt vebDef₁.val ![(#0 : Semiterm LRA ℕ 2), numAtR (gamma0Code a), #1]) ⋎
    (tiMuR L)/[(#0 : Semiterm LRA ℕ 2)]

/-- **`F_{a,L}(g) :≡ ∀u (Veb(u, a, g) → Acc_L(u))`.** -/
def vebF (a : Gamma0Note) (L : Lv) : Semiformula LRA ℕ 1 := ∀¹ vebBody a L

/-- `∀y (y ≺₁ h → F(y))`. -/
def hypF (F : Semiformula LRA ℕ 1) (h : ℕ) : Proposition LRA :=
  ∀¹ (∼(arAt precDef₁.val ![(#0 : Semiterm LRA ℕ 1), numAtR h]) ⋎ F)

/-- The matrix of `Prog(≺₁, φ)`. -/
def progBody (φ : Semiformula LRA ℕ 1) : Semiformula LRA ℕ 1 :=
  ∼(∀¹ (∼(arAt precDef₁.val ![(#0 : Semiterm LRA ℕ 2), #1]) ⋎ φ/[(#0 : Semiterm LRA ℕ 2)])) ⋎
    φ/[(#0 : Semiterm LRA ℕ 1)]

theorem progR_eq (φ : Semiformula LRA ℕ 1) : progR φ = ∀¹ progBody φ := rfl

section Eval

variable {M : Type} [s : Structure LRA M]

theorem eval_subst_bvar_zero {n : ℕ} (φ : Semiformula LRA ℕ 1) (x : M) (e : Fin n → M)
    (f : ℕ → M) :
    Semiformula.Eval (s := s) (x :> e) f (φ/[(#0 : Semiterm LRA ℕ (n + 1))]) ↔
      Semiformula.Eval (s := s) ![x] f φ := by
  rw [Semiformula.eval_substs]
  have h : (Semiterm.val (s := s) (x :> e) f ∘ ![(#0 : Semiterm LRA ℕ (n + 1))]) = ![x] := by
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  rw [h]

theorem eval_vebBody (a : Gamma0Note) (L : Lv) (u g : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![u, g] f (vebBody a L) ↔
      (arEval vebDef₁.val ![u, numVal M (gamma0Code a), g] → TImu L u) := by
  simp only [vebBody, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, eval_arAt,
    eval_tiMuR_subst, Semiterm.val_bvar]
  have hv : (fun i => Semiterm.val (s := s) ![u, g] f
      (![(#0 : Semiterm LRA ℕ 2), numAtR (gamma0Code a), #1] i)) =
        ![u, numVal M (gamma0Code a), g] := by
    funext i
    fin_cases i
    · rfl
    · exact val_numAtR_model _ _ _
    · rfl
  rw [hv, imp_iff_not_or]
  rfl

theorem eval_vebF (a : Gamma0Note) (L : Lv) (g : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![g] f (vebF a L) ↔
      ∀ u : M, arEval vebDef₁.val ![u, numVal M (gamma0Code a), g] → TImu L u := by
  rw [vebF, Semiformula.eval_all]
  refine forall_congr' fun u => ?_
  exact eval_vebBody a L u g f

theorem eval_hypF (F : Semiformula LRA ℕ 1) (h : ℕ) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (hypF F h) ↔
      ∀ y : M, precM y (numVal M h) → Semiformula.Eval (s := s) ![y] f F := by
  rw [hypF, Semiformula.eval_all]
  refine forall_congr' fun y => ?_
  have e : (y :> (![] : Fin 0 → M)) = ![y] := by
    funext i; fin_cases i; rfl
  rw [e]
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, eval_arAt]
  have hv : (fun i => Semiterm.val (s := s) ![y] f
      (![(#0 : Semiterm LRA ℕ 1), numAtR h] i)) = ![y, numVal M h] := by
    funext i
    fin_cases i
    · rfl
    · exact val_numAtR_model _ _ _
  rw [hv, imp_iff_not_or]
  rfl

theorem eval_progBody (φ : Semiformula LRA ℕ 1) (x : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![x] f (progBody φ) ↔
      ((∀ y : M, precM y x → Semiformula.Eval (s := s) ![y] f φ) →
        Semiformula.Eval (s := s) ![x] f φ) := by
  simp only [progBody, Semiformula.eval_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq, eval_arAt, eval_subst_bvar_zero]
  have hp : ∀ y : M, arEval precDef₁.val (fun i => Semiterm.val (s := s) (y :> ![x]) f
      (![(#0 : Semiterm LRA ℕ 2), #1] i)) ↔ precM y x := by
    intro y
    have hv : (fun i => Semiterm.val (s := s) (y :> ![x]) f
        (![(#0 : Semiterm LRA ℕ 2), #1] i)) = ![y, x] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    rfl
  simp only [hp]
  constructor
  · rintro (h | h) hb
    · exact absurd (fun y => imp_iff_not_or.mp (hb y)) h
    · exact h
  · intro h
    by_cases hb : ∀ y, precM y x → Semiformula.Eval (s := s) ![y] f φ
    · exact Or.inr (h hb)
    · exact Or.inl fun hall => hb fun y hy => (hall y).resolve_left (not_not_intro hy)

/-- The instance of `F_{a,L}(h̄)` at `ū`. -/
theorem eval_vebF_inst (a : Gamma0Note) (L : Lv) (h u : ℕ) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f
        (((Rew.subst ![(num h : SyntacticTerm LRA)]).q ▹ vebBody a L)/[(num u : SyntacticTerm LRA)])
      ↔ (arEval vebDef₁.val ![numVal M u, numVal M (gamma0Code a), numVal M h] →
          TImu L (numVal M u)) := by
  rw [subst_num_eval, Semiformula.eval_rew]
  have key : ∀ (e : Fin 2 → M) (g : ℕ → M), e = ![numVal M u, numVal M h] →
      (Semiformula.Eval (s := s) e g (vebBody a L) ↔
        (arEval vebDef₁.val ![numVal M u, numVal M (gamma0Code a), numVal M h] →
          TImu L (numVal M u))) := by
    rintro e g rfl
    exact eval_vebBody a L _ _ g
  apply key
  funext i
  fin_cases i
  · rfl
  · simp only [Function.comp_apply, Fin.mk_one, Fin.isValue]
    rw [show (#1 : Semiterm LRA ℕ 2) = #(Fin.succ (0 : Fin 1)) from rfl, Rew.q_bvar_succ,
      Rew.subst_bvar, Matrix.cons_val_zero]
    show Semiterm.val (s := s) ![numVal M u] f (Rew.bShift (numAtR h)) = numVal M h
    rw [rew_numAtR, val_numAtR_model]

theorem vebF_subst (a : Gamma0Note) (L : Lv) (h : ℕ) :
    (vebF a L)/[(num h : SyntacticTerm LRA)] =
      ∀¹ ((Rew.subst ![(num h : SyntacticTerm LRA)]).q ▹ vebBody a L) := by
  simp [vebF]

end Eval

/-! ### Free variables and levels -/

theorem freeVariables_vebBody (a : Gamma0Note) (L : Lv) : (vebBody a L).freeVariables = ∅ := by
  have h1 : (arAt vebDef₁.val ![(#0 : Semiterm LRA ℕ 2), numAtR (gamma0Code a), #1]).freeVariables
      = ∅ := freeVariables_arAt' _ _ (fun i => by fin_cases i <;> simp)
  have h2 : ((tiMuR L)/[(#0 : Semiterm LRA ℕ 2)]).freeVariables = ∅ :=
    freeVariables_rewR_eq_empty _ (freeVariables_tiMuR L)
      (fun i => by rw [Subsingleton.elim i 0]; simp)
  simp [vebBody, h1, h2]

theorem freeVariables_vebF (a : Gamma0Note) (L : Lv) : (vebF a L).freeVariables = ∅ := by
  rw [vebF, Semiformula.freeVariables_all, freeVariables_vebBody]

theorem freeVariables_vebF_inst (a : Gamma0Note) (L : Lv) (h u : ℕ) :
    (((Rew.subst ![(num h : SyntacticTerm LRA)]).q ▹ vebBody a L)/[(num u : SyntacticTerm LRA)]).freeVariables
      = ∅ := by
  have h1 : (((Rew.subst ![(num h : SyntacticTerm LRA)]).q ▹ vebBody a L)).freeVariables = ∅ := by
    have := freeVariables_subst_num (freeVariables_vebF a L) h
    rwa [vebF_subst, Semiformula.freeVariables_all] at this
  exact freeVariables_subst_num h1 u

theorem freeVariables_hypF {F : Semiformula LRA ℕ 1} (hF : F.freeVariables = ∅) (h : ℕ) :
    (hypF F h).freeVariables = ∅ := by
  have h1 : (arAt precDef₁.val ![(#0 : Semiterm LRA ℕ 1), numAtR h]).freeVariables = ∅ :=
    freeVariables_arAt' _ _ (fun i => by fin_cases i <;> simp)
  simp [hypF, h1, hF]

theorem freeVariables_progBody_inst {φ : Semiformula LRA ℕ 1} (hφ : φ.freeVariables = ∅)
    (h : ℕ) : ((progBody φ)/[(num h : SyntacticTerm LRA)]).freeVariables = ∅ := by
  have h0 := freeVariables_progR hφ
  rw [progR_eq, Semiformula.freeVariables_all] at h0
  exact freeVariables_subst_num h0 h

theorem lvlOf_vebF_le (a : Gamma0Note) (L : Lv) : lvlOf (vebF a L) ≤ L := by
  simp only [vebF, vebBody, lvlOf_all, lvlOf_or, lvlOf_neg, lvlOf_arAt, lvlOf_subst₁]
  exact max_le (Gamma0Note.zero_le_note L) (lvlOf_tiMuR_le L)

theorem lvlOf_hypF_le {F : Semiformula LRA ℕ 1} {L : Lv} (hF : lvlOf F ≤ L) (h : ℕ) :
    lvlOf (hypF F h) ≤ L := by
  simp only [hypF, lvlOf_all, lvlOf_or, lvlOf_neg, lvlOf_arAt]
  exact max_le (Gamma0Note.zero_le_note L) hF

/-! ### The two small facts about `Acc` -/

variable {ρ : Gamma0Note}

theorem not_trueN_precA_zero (x : ℕ) : ¬TrueN (precA x (gamma0Code 0)) := by
  rw [precA_true_iff]
  rintro ⟨ξ, η, -, hη, hlt⟩
  rw [Gentzen.VNoteBridge.gamma0Code_inj] at hη
  subst hη
  exact absurd hlt (not_lt.mpr (Gamma0Note.zero_le_note ξ))

/-- **`Acc_μ(0)`**, vacuously. -/
theorem accZeroD {μ : Lv} (hρ1 : Gamma0Note.omegaPow 1 ≤ ρ)
    (hρ : Gamma0Note.blkTop (Gamma0Note.nadd μ 1) ≤ ρ) {Γ : Sequent LRA} {H : Gamma0Note}
    (hH : Gamma0Note.epsilonNote 0 ≤ H) :
    DerLt ρ (evR (accA μ (gamma0Code 0)) :: Γ) (Gamma0Note.nadd H (Gamma0Note.ofNat 6)) :=
  accIntro (gamma0Code 0) hρ1 hρ hH (fun _ x hx => absurd hx (not_trueN_precA_zero x))

/-- **`Acc_μ(e) → Acc_μ(e ⊕ 1)`.** -/
theorem succD {μ : Lv} (hρ1 : Gamma0Note.omegaPow 1 ≤ ρ)
    (hρ : Gamma0Note.blkTop (Gamma0Note.nadd μ 1) ≤ ρ) (e : Gamma0Note) :
    DerLt ρ [evR (∼accA μ (gamma0Code e)), evR (accA μ (gamma0Code (Gamma0Note.nadd e 1)))]
      (Gamma0Note.nadd (Gamma0Note.nadd (Gamma0Note.epsilonNote 0) (Gamma0Note.ofNat 4))
        (Gamma0Note.ofNat 6)) := by
  set E := Gamma0Note.epsilonNote 0
  have hE : E ≤ E := le_rfl
  have hrkA : rank (accA μ (gamma0Code e)) < ρ :=
    lt_of_lt_of_le (rank_lt_of_lvlOf_le (lvlOf_accA_le μ _)) hρ
  have hrkP : ∀ z, rank (progA μ z) < ρ := fun z =>
    lt_of_lt_of_le (rank_lt_of_lvlOf_le (le_of_eq (lvlOf_progA μ z))) hρ
  have h := accIntro (ρ := ρ) (μ := μ) (gamma0Code (Gamma0Note.nadd e 1))
    (Γ := [evR (∼accA μ (gamma0Code e))]) (H := Gamma0Note.nadd E (Gamma0Note.ofNat 4))
    hρ1 hρ (epsilon_le_nadd hE 4) ?_
  · exact h.weak (by subset_tac)
  intro z x hx
  obtain ⟨ξ, η, rfl, hη, hlt⟩ := (precA_true_iff _ _).mp hx
  rw [Gentzen.VNoteBridge.gamma0Code_inj] at hη
  subst hη
  have hle : ξ ≤ e := Gamma0Note.lt_nadd_one_iff.mp hlt
  have hidA : DerLt ρ (evR (accA μ (gamma0Code e)) ::
      [evR (∼progA μ z), evR (∼accA μ (gamma0Code e))]) E :=
    (DerLt.identity (evR (accA μ (gamma0Code e))) hE).weak (by simp only [evR_neg]; subset_tac)
  have hidP : DerLt ρ (evR (progA μ z) ::
      [evR (∼progA μ z), evR (∼accA μ (gamma0Code e))]) E :=
    (DerLt.identity (evR (progA μ z)) hE).weak (by simp only [evR_neg]; subset_tac)
  rcases lt_or_eq_of_le hle with hξ | rfl
  · have hpr : DerLt ρ (evR (precA (gamma0Code ξ) (gamma0Code e)) ::
        [evR (∼progA μ z), evR (∼accA μ (gamma0Code e))]) E :=
      (DerLt.of_true (rFree_arAt _ _) (freeVariables_precA _ _) (precA_true_code hξ) hE).weak
        (by subset_tac)
    have hd := DerLt.discharge (ρ := ρ) (C := memA μ (gamma0Code ξ) z)
      [accA μ (gamma0Code e), progA μ z, precA (gamma0Code ξ) (gamma0Code e)]
      (freeVariables_memA _ _ _)
      (by
        intro A hA
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl | rfl
        · exact freeVariables_accA _ _
        · exact freeVariables_progA _ _
        · exact freeVariables_precA _ _)
      (by
        intro M _ _ f hAs
        have h1 : Semiformula.Eval ![] f (accA μ (gamma0Code e)) := hAs _ List.mem_cons_self
        have h2 : Semiformula.Eval ![] f (progA μ z) :=
          hAs _ (List.mem_cons_of_mem _ List.mem_cons_self)
        have h3 : Semiformula.Eval ![] f (precA (gamma0Code ξ) (gamma0Code e)) :=
          hAs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        rw [eval_accA] at h1
        rw [eval_progA] at h2
        rw [eval_precA] at h3
        show Semiformula.Eval ![] f (memA μ (gamma0Code ξ) z)
        rw [eval_memA]
        exact h1 (numVal M z) h2 _ h3)
      (by
        intro A hA
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl | rfl
        · exact hrkA
        · exact hrkP z
        · exact lt_of_lt_of_le (rank_lt_of_lvlOf_le (L := μ)
            (by rw [lvlOf_precA]; exact gamma0_zero_le μ)) hρ)
      (by
        intro A hA
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl | rfl
        · exact hidA
        · exact hidP
        · exact hpr)
      hρ1 hE
    exact (hd.weak (by subset_tac)).mono (nadd_ofNat_le_nadd_ofNat E (by norm_num))
  · have hd := DerLt.discharge (ρ := ρ) (C := memA μ (gamma0Code ξ) z)
      [accA μ (gamma0Code ξ), progA μ z]
      (freeVariables_memA _ _ _)
      (by
        intro A hA
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl
        · exact freeVariables_accA _ _
        · exact freeVariables_progA _ _)
      (by
        intro M _ _ f hAs
        have h1 : Semiformula.Eval ![] f (accA μ (gamma0Code ξ)) := hAs _ List.mem_cons_self
        have h2 : Semiformula.Eval ![] f (progA μ z) :=
          hAs _ (List.mem_cons_of_mem _ List.mem_cons_self)
        rw [eval_accA] at h1
        rw [eval_progA] at h2
        show Semiformula.Eval ![] f (memA μ (gamma0Code ξ) z)
        rw [eval_memA]
        exact h2 _ (h1 (numVal M z) h2))
      (by
        intro A hA
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl
        · exact hrkA
        · exact hrkP z)
      (by
        intro A hA
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl
        · exact hidA
        · exact hidP)
      hρ1 hE
    exact (hd.weak (by subset_tac)).mono (nadd_ofNat_le_nadd_ofNat E (by norm_num))

end Ramified

end OrdinalAnalysis
