/-
  The last step of an instance, and the assembly of Steps 1 and 2.

  * `effEquiv_derivable`: `∀y (y ∈̇_L z̄ ↔ y ∈̇_κ w̄)` for the parameter-free code
    `w` at level `κ` of the effective body of `z` at level `L`, from
    `effBodyAt_code_derivable`; cut-free below `ε₀`.
  * `lastStep`: from `Acc_κ(b̄)` and `ξ < b`, derive `ξ̄ ∈̇_L z̄` under
    `Prog(λy. y ∈̇_L z̄)`.  The set `z` at level `L` is copied down to the level
    `κ` of the code `w`, where `Acc_κ(b̄)` applies.
  * `assemble`: `(D)` at `(a, L)`,

        ¬Acc_{L+1}(c̄), Acc_L(φ_a(c)‾)          for every notation `c`,

    at cut rank `blkTop (L+1)`, from the **instances**

        ¬Prog(λy. y ∈̇_L z), ξ̄ ∈̇_L z, ¬(∀y ≺₁ γ̄. F_{a,L}(y))          (`KeyInst`)

    for all notations `γ`, `ξ < φ_a(γ)` and all names `z`, derivable below a
    common bound `B`.  The proof of `Prog(F_{a,L})`: an ω-rule over `h`, and for
    each `h` an ω-rule over `u`; when `Veb(u, a, h)` is false the premise is true
    arithmetic, and when it is true, `h` and `u` are the codes of `γ` and
    `φ_a(γ)`, and `Acc_L(u)` is introduced by `accIntro`, whose premises are the
    instances.  Then Step 2 (`step2`) and `Veb(φ_a(c), a, c)`.
-/
import OrdinalAnalysis.Ramified.DescentBetaAux5

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalVNote (precDef₁)
open OrdinalAnalysis.Gentzen.InternalVeblenCode (vebDef₁)
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)

variable {ρ : Gamma0Note}

/-! ### A name and the code of its effective body -/

/-- `∀y (y ∈̇_L z̄ ↔ y ∈̇_κ w̄)`. -/
def effEquiv (L κ : Lv) (z w : ℕ) : Proposition LRA :=
  ∀¹ ((∼memAt L (#0 : Semiterm LRA ℕ 1) (numAtR z) ⋎ memAt κ #0 (numAtR w)) ⋏
      (∼memAt κ (#0 : Semiterm LRA ℕ 1) (numAtR w) ⋎ memAt L #0 (numAtR z)))

theorem effEquiv_inst (L κ : Lv) (z w y : ℕ) :
    ((∼memAt L (#0 : Semiterm LRA ℕ 1) (numAtR z) ⋎ memAt κ #0 (numAtR w)) ⋏
      (∼memAt κ (#0 : Semiterm LRA ℕ 1) (numAtR w) ⋎ memAt L #0 (numAtR z)))/[(num y : SyntacticTerm LRA)]
      = (∼memA L y z ⋎ memA κ y w) ⋏ (∼memA κ y w ⋎ memA L y z) := by
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, rew_memAt, Rew.subst_bvar, rew_numAtR, memA]
  rfl

theorem freeVariables_effEquiv (L κ : Lv) (z w : ℕ) : (effEquiv L κ z w).freeVariables = ∅ := by
  simp [effEquiv, freeVariables_memAt, freeVariables_nmemAt]

theorem lvlOf_effEquiv_le {L κ : Lv} (h : κ ≤ L) (z w : ℕ) : lvlOf (effEquiv L κ z w) ≤ L := by
  simp only [effEquiv, lvlOf_all, lvlOf_and, lvlOf_or, lvlOf_neg, lvlOf_memAt]
  exact max_le (max_le le_rfl h) (max_le h le_rfl)

theorem eval_effEquiv {M : Type} [s : Structure LRA M] (L κ : Lv) (z w : ℕ) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (effEquiv L κ z w) ↔
      ∀ y : M, (memM L y (numVal M z) ↔ memM κ y (numVal M w)) := by
  simp only [effEquiv, Semiformula.eval_all, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.and_eq, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq]
  refine forall_congr' fun y => ?_
  have e : (y :> (![] : Fin 0 → M)) = ![y] := by
    funext i; fin_cases i; rfl
  rw [e, eval_memAt_bvar, eval_memAt_bvar]
  tauto

/-- **A name at level `L` and the parameter-free code of its effective body at level
`κ` have the same members**, cut-free, below `ε₀ ⊕ 3`. -/
theorem effEquiv_derivable (L : Lv) (z : ℕ) {κ : Lv} (hκ : lvlOf (effBodyAt L z) < κ)
    {H : Gamma0Note} (hH : Gamma0Note.epsilonNote 0 ≤ H) :
    DerLt ρ [evR (effEquiv L κ z (code κ (effBodyAt L z)))]
      (Gamma0Note.nadd H (Gamma0Note.ofNat 3)) := by
  set w := code κ (effBodyAt L z)
  rw [effEquiv, evR_all]
  refine DerLt.all (H := Gamma0Note.nadd H (Gamma0Note.ofNat 2)) (fun y => ?_)
    (nadd_ofNat_lt_nadd_ofNat H (by norm_num))
  rw [evInstR_inst_ev, effEquiv_inst, evR_and, evR_or, evR_or, evR_neg, evR_neg]
  obtain ⟨D1, D2⟩ := effBodyAt_code_derivable (O := Gamma0Note) (A := junkLitsR) (ρ := ρ)
    (fun _ h => Or.inr h) L z hκ y
  have hlt : (OrdinalNotation.ofNat (2 * stage z + 1) : Gamma0Note) < H :=
    lt_of_lt_of_le (ofNat_lt_epsilonNote_zero _) hH
  have e1 : ∀ μ x, evR (memA μ y x) = memAt μ (num y) (num x) := fun μ x => by
    rw [memA, evR_memAt_num]; rfl
  have E1 : DerLt ρ [∼evR (memA L y z), evR (memA κ y w)] H := by
    rw [e1, e1]; exact ⟨_, hlt, D1⟩
  have E2 : DerLt ρ [∼evR (memA κ y w), evR (memA L y z)] H := by
    rw [e1, e1]; exact ⟨_, hlt, D2⟩
  refine DerLt.and (H := Gamma0Note.nadd H (Gamma0Note.ofNat 1)) ?_ ?_
    (nadd_ofNat_lt_nadd_ofNat H (by norm_num))
  · exact DerLt.or E1 (lt_of_le_of_lt (le_of_eq (Gamma0Note.nadd_zero H).symm)
      (nadd_ofNat_lt_nadd_ofNat H (by norm_num : 0 < 1)))
  · exact DerLt.or E2 (lt_of_le_of_lt (le_of_eq (Gamma0Note.nadd_zero H).symm)
      (nadd_ofNat_lt_nadd_ofNat H (by norm_num : 0 < 1)))

/-- **The last step of an instance.** -/
theorem lastStep {L κ : Lv} (hκL : κ ≤ L) (z : ℕ) (hκ : lvlOf (effBodyAt L z) < κ)
    {b ξ : Gamma0Note} (hξ : ξ < b) {Γ : Sequent LRA} {H : Gamma0Note}
    (hH : Gamma0Note.epsilonNote 0 ≤ H) (hρ1 : Gamma0Note.omegaPow 1 ≤ ρ)
    (hρ : Gamma0Note.blkTop (Gamma0Note.nadd L 1) ≤ ρ)
    (hacc : DerLt ρ (evR (accA κ (gamma0Code b)) :: Γ) H) :
    DerLt ρ (evR (memA L (gamma0Code ξ) z) :: evR (∼progA L z) :: Γ)
      (Gamma0Note.nadd H (Gamma0Note.ofNat 8)) := by
  set w := code κ (effBodyAt L z)
  set H3 := Gamma0Note.nadd H (Gamma0Note.ofNat 3)
  have hH3 : Gamma0Note.epsilonNote 0 ≤ H3 := epsilon_le_nadd hH 3
  have hE := effEquiv_derivable (ρ := ρ) L z hκ hH
  have hd := DerLt.discharge (ρ := ρ) (C := memA L (gamma0Code ξ) z)
    (Γ := evR (∼progA L z) :: Γ) (H := H3)
    [accA κ (gamma0Code b), effEquiv L κ z w, progA L z, precA (gamma0Code ξ) (gamma0Code b)]
    (freeVariables_memA _ _ _)
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl
      · exact freeVariables_accA _ _
      · exact freeVariables_effEquiv _ _ _ _
      · exact freeVariables_progA _ _
      · exact freeVariables_precA _ _)
    (by
      intro M _ _ f hAs
      have h1 : Semiformula.Eval ![] f (accA κ (gamma0Code b)) := hAs _ List.mem_cons_self
      have h2 : Semiformula.Eval ![] f (effEquiv L κ z w) :=
        hAs _ (List.mem_cons_of_mem _ List.mem_cons_self)
      have h3 : Semiformula.Eval ![] f (progA L z) :=
        hAs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have h4 : Semiformula.Eval ![] f (precA (gamma0Code ξ) (gamma0Code b)) :=
        hAs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self)))
      rw [eval_accA] at h1
      rw [eval_effEquiv] at h2
      rw [eval_progA] at h3
      rw [eval_precA] at h4
      show Semiformula.Eval ![] f (memA L (gamma0Code ξ) z)
      rw [eval_memA]
      have hprog : ProgM (fun y => memM κ y (numVal M w)) := fun y hy =>
        (h2 y).mp (h3 y fun x hx => (h2 x).mpr (hy x hx))
      exact (h2 _).mpr (h1 (numVal M w) hprog _ h4))
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl
      · exact lt_of_lt_of_le (rank_lt_of_lvlOf_le (le_trans (lvlOf_accA_le κ _) hκL)) hρ
      · exact lt_of_lt_of_le (rank_lt_of_lvlOf_le (lvlOf_effEquiv_le hκL z w)) hρ
      · exact lt_of_lt_of_le (rank_lt_of_lvlOf_le (le_of_eq (lvlOf_progA L z))) hρ
      · exact lt_of_lt_of_le (rank_lt_of_lvlOf_le (L := L)
          (by rw [lvlOf_precA]; exact gamma0_zero_le L)) hρ)
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl
      · exact (hacc.weak (by subset_tac)).mono (le_nadd_ofNat H 3)
      · exact hE.weak (by subset_tac)
      · exact ((DerLt.identity (evR (progA L z)) hH3).weak
          (by simp only [evR_neg]; subset_tac)).mono le_rfl
      · exact (DerLt.of_true (rFree_arAt _ _) (freeVariables_precA _ _)
          (precA_true_code hξ) hH3).weak (by subset_tac))
    hρ1 hH3
  simp only [List.length_cons, List.length_nil] at hd
  rw [nadd_ofNat_add] at hd
  exact hd

/-! ### The assembly -/

/-- **The instances of Step 1** at `(a, L)`, below `B`. -/
def KeyInst (ρ : Gamma0Note) (a : Gamma0Note) (L : Lv) (B : Gamma0Note) : Prop :=
  ∀ (γ ξ : Gamma0Note) (z : ℕ), ξ < Gamma0Note.veblenNote a γ →
    DerLt ρ [evR (∼progA L z), evR (memA L (gamma0Code ξ) z),
      evR (∼hypF (vebF a L) (gamma0Code γ))] B

/-- **Steps 1 and 2.**  From the instances, `(D)` at `(a, L)`: for every notation `c`,
`¬Acc_{L+1}(c̄), Acc_L(φ_a(c)‾)` at cut rank `blkTop (L+1)`, below `B ⊕ 24`. -/
theorem assemble {a : Gamma0Note} {L : Lv} {B : Gamma0Note}
    (hB : Gamma0Note.epsilonNote 0 ≤ B)
    (hkey : KeyInst (Gamma0Note.blkTop (Gamma0Note.nadd L 1)) a L B) (c : Gamma0Note) :
    DerLt (Gamma0Note.blkTop (Gamma0Note.nadd L 1))
      [evR (∼accA (Gamma0Note.nadd L 1) (gamma0Code c)),
        evR (accA L (gamma0Code (Gamma0Note.veblenNote a c)))]
      (Gamma0Note.nadd B (Gamma0Note.ofNat 24)) := by
  set ρ := Gamma0Note.blkTop (Gamma0Note.nadd L 1) with hρdef
  set F := vebF a L with hFdef
  have hρ1 : Gamma0Note.omegaPow 1 ≤ ρ := omegaPow_one_le_blkTop (nadd_one_ne_zero L)
  have hlt : ∀ m n : ℕ, m < n →
      Gamma0Note.nadd B (Gamma0Note.ofNat m) < Gamma0Note.nadd B (Gamma0Note.ofNat n) :=
    fun m n h => nadd_ofNat_lt_nadd_ofNat B h
  have hrkL : ∀ φ : Proposition LRA, lvlOf φ ≤ L → rank φ < ρ := fun φ h => rank_lt_of_lvlOf_le h
  have hFc : F.freeVariables = ∅ := freeVariables_vebF a L
  have hFl : lvlOf F ≤ L := lvlOf_vebF_le a L
  -- the premises of the ω-rule over `u`
  have hU : ∀ h u : ℕ, DerLt ρ [evR (∼vebA u (gamma0Code a) h), evR (accA L u),
      evR (∼hypF F h)] (Gamma0Note.nadd B (Gamma0Note.ofNat 6)) := by
    intro h u
    by_cases hv : TrueN (vebA u (gamma0Code a) h)
    · obtain ⟨α, γ, hα, rfl, rfl⟩ := (vebA_true_iff _ _ _).mp hv
      rw [Gentzen.VNoteBridge.gamma0Code_inj] at hα
      subst hα
      have hA := accIntro (ρ := ρ) (μ := L) (gamma0Code (Gamma0Note.veblenNote α γ))
        (Γ := [evR (∼vebA (gamma0Code (Gamma0Note.veblenNote α γ)) (gamma0Code α)
          (gamma0Code γ)), evR (∼hypF F (gamma0Code γ))]) hρ1 le_rfl hB (fun z x hx => by
            obtain ⟨ξ, η, rfl, hη, hξη⟩ := (precA_true_iff _ _).mp hx
            rw [Gentzen.VNoteBridge.gamma0Code_inj] at hη
            subst hη
            exact (hkey γ ξ z hξη).weak (by subset_tac))
      exact hA.weak (by subset_tac)
    · have ht : DerLt ρ [evR (∼vebA u (gamma0Code a) h)] B :=
        DerLt.of_true ((rFree_neg _).mpr (rFree_arAt _ _))
          (by rw [Semiformula.freeVariables_not]; exact freeVariables_vebA _ _ _)
          ((trueN_neg _).mpr hv) hB
      exact (ht.weak (by subset_tac)).mono (le_nadd_ofNat B 6)
  -- `F(h̄)`, by the ω-rule over `u`
  have hFh : ∀ h : ℕ, DerLt ρ [evR (F/[(num h : SyntacticTerm LRA)]), evR (∼hypF F h)]
      (Gamma0Note.nadd B (Gamma0Note.ofNat 10)) := by
    intro h
    rw [hFdef, vebF_subst, evR_all]
    refine DerLt.all (H := Gamma0Note.nadd B (Gamma0Note.ofNat 9)) (fun u => ?_) (hlt 9 10 (by norm_num))
    rw [evInstR_inst_ev]
    have h1 : DerLt ρ [evR (∼vebA u (gamma0Code a) h ⋎ accA L u), evR (∼hypF F h)]
        (Gamma0Note.nadd B (Gamma0Note.ofNat 7)) := by
      rw [evR_or]; exact DerLt.or (hU h u) (hlt 6 7 (by norm_num))
    have hlv1 : lvlOf (∼vebA u (gamma0Code a) h ⋎ accA L u) ≤ L := by
      rw [lvlOf_or, lvlOf_neg]
      exact max_le (by rw [lvlOf_vebA]; exact gamma0_zero_le L) (lvlOf_accA_le L u)
    have h2 := DerLt.conv (ρ := ρ) (A := ∼vebA u (gamma0Code a) h ⋎ accA L u)
      (C := ((Rew.subst ![(num h : SyntacticTerm LRA)]).q ▹ vebBody a L)/[(num u : SyntacticTerm LRA)])
      (by simp only [Semiformula.freeVariables_or, Semiformula.freeVariables_not,
        freeVariables_vebA, freeVariables_accA, Finset.union_empty])
      (freeVariables_vebF_inst a L h u)
      (fun M _ _ f hE => by
        have hE' : Semiformula.Eval ![] f (∼vebA u (gamma0Code a) h ⋎ accA L u) := hE
        show Semiformula.Eval ![] f _
        rw [eval_vebF_inst]
        simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
          LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq, eval_vebA,
          eval_accA] at hE'
        intro hv
        exact hE'.resolve_left (not_not_intro hv))
      (hrkL _ hlv1)
      hρ1 (epsilon_le_nadd hB 7) h1
    rw [nadd_ofNat_add] at h2
    exact h2
  -- `Prog(F)`, by the ω-rule over `h`
  have hP : DerLt ρ [evR (progR F)] (Gamma0Note.nadd B (Gamma0Note.ofNat 14)) := by
    rw [progR_eq, evR_all]
    refine DerLt.all (H := Gamma0Note.nadd B (Gamma0Note.ofNat 13)) (fun h => ?_)
      (hlt 13 14 (by norm_num))
    rw [evInstR_inst_ev]
    have h1 : DerLt ρ [evR (∼hypF F h ⋎ F/[(num h : SyntacticTerm LRA)])]
        (Gamma0Note.nadd B (Gamma0Note.ofNat 11)) := by
      rw [evR_or]; exact DerLt.or ((hFh h).weak (by subset_tac)) (hlt 10 11 (by norm_num))
    have h2 := DerLt.conv (ρ := ρ) (Γ := []) (A := ∼hypF F h ⋎ F/[(num h : SyntacticTerm LRA)])
      (C := (progBody F)/[(num h : SyntacticTerm LRA)])
      (by simp only [Semiformula.freeVariables_or, Semiformula.freeVariables_not,
        freeVariables_hypF hFc, freeVariables_subst_num hFc, Finset.union_empty])
      (freeVariables_progBody_inst hFc h)
      (fun M _ _ f hE => by
        have hE' : Semiformula.Eval ![] f (∼hypF F h ⋎ F/[(num h : SyntacticTerm LRA)]) := hE
        show Semiformula.Eval ![] f _
        rw [subst_num_eval, eval_progBody]
        simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
          LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq, eval_hypF,
          subst_num_eval] at hE'
        intro hb
        exact hE'.resolve_left (not_not_intro hb))
      (hrkL _ (by rw [lvlOf_or, lvlOf_neg, lvlOf_subst₁]; exact max_le (lvlOf_hypF_le hFl h) hFl))
      hρ1 (epsilon_le_nadd hB 11) h1
    rw [nadd_ofNat_add] at h2
    exact h2.weak (by subset_tac)
  -- Step 2
  have h2 := step2 hFc hFl (epsilon_le_nadd hB 14) hP (gamma0Code c)
  rw [nadd_ofNat_add] at h2
  -- the value `φ_a(c)`
  have hV : DerLt ρ [evR (vebA (gamma0Code (Gamma0Note.veblenNote a c)) (gamma0Code a)
      (gamma0Code c))] (Gamma0Note.nadd B (Gamma0Note.ofNat 21)) :=
    DerLt.of_true (rFree_arAt _ _) (freeVariables_vebA _ _ _)
      ((vebA_true_iff _ _ _).mpr ⟨a, c, rfl, rfl, rfl⟩) (epsilon_le_nadd hB 21)
  have hd := DerLt.discharge (ρ := ρ)
    (Γ := [evR (∼accA (Gamma0Note.nadd L 1) (gamma0Code c))])
    (H := Gamma0Note.nadd B (Gamma0Note.ofNat 21))
    [F/[(num (gamma0Code c) : SyntacticTerm LRA)],
      vebA (gamma0Code (Gamma0Note.veblenNote a c)) (gamma0Code a) (gamma0Code c)]
    (C := accA L (gamma0Code (Gamma0Note.veblenNote a c)))
    (freeVariables_accA _ _)
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact freeVariables_subst_num hFc _
      · exact freeVariables_vebA _ _ _)
    (by
      intro M _ _ f hAs
      have h1 : Semiformula.Eval ![] f (F/[(num (gamma0Code c) : SyntacticTerm LRA)]) :=
        hAs _ List.mem_cons_self
      have h3 : Semiformula.Eval ![] f
          (vebA (gamma0Code (Gamma0Note.veblenNote a c)) (gamma0Code a) (gamma0Code c)) :=
        hAs _ (List.mem_cons_of_mem _ List.mem_cons_self)
      rw [subst_num_eval, hFdef, eval_vebF] at h1
      rw [eval_vebA] at h3
      show Semiformula.Eval ![] f (accA L (gamma0Code (Gamma0Note.veblenNote a c)))
      rw [eval_accA]
      exact h1 _ h3)
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact hrkL _ (by rw [lvlOf_subst₁]; exact hFl)
      · exact hrkL _ (by rw [lvlOf_vebA]; exact gamma0_zero_le L))
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact h2.weak (by subset_tac)
      · exact hV.weak (by subset_tac))
    hρ1 (epsilon_le_nadd hB 21)
  simp only [List.length_cons, List.length_nil] at hd
  rw [nadd_ofNat_add] at hd
  exact hd.weak (by subset_tac)

end Ramified

end OrdinalAnalysis
