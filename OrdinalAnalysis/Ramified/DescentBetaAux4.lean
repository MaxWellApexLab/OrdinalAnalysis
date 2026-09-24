/-
  The building blocks of the generalised descent in `RA_∞`.

  * `DerLt.conv`: replace a formula by a logical consequence of it.
  * `accIntro`: **introduction of `Acc_μ(v)`**.  If for every level-`μ` name `z`
    and every `x ≺₁ v` (true in `ℕ`) the sequent `¬Prog(λy. y ∈̇_μ z), x ∈̇_μ z, Γ`
    is derivable, then so is `Acc_μ(v), Γ`: two ω-rules, over `z` and over `x`,
    the premises for `x ⊀₁ v` being true arithmetic.  The premises may be
    derived at levels and heights that depend on `z` and `x`; this is where the
    ω-rule does what no finitary proof can.
  * `copyD`: the copy lemma `Acc_μ(y) → Acc_κ(y)`, `κ ≤ μ`, at a numeral
    (finitary, from `TImu_copy`).
  * `nameIff_derivable`: for a closed `B` of level below `μ` and its
    parameter-free code `w` at level `μ`, the sentence `∀y (y ∈̇_μ w̄ ↔ B(y))`,
    by one (Pr) and one (Pr⁻) inference at each numeral; its rank is below
    `blkTop μ` (`rank_nameIff_lt`), since its level-`μ` atoms have the ground set
    argument `w̄`.
  * `step2`: **Step 2 of the generalised descent.**  If `Prog(≺₁, F)` is
    derivable for a closed `F` of level at most `L`, then
    `¬Acc_{L+1}(c̄), F(c̄)` is derivable at cut rank `blkTop (L+1)`, for every
    numeral `c`: `Acc_{L+1}(c)` is instantiated at the parameter-free level-`(L+1)`
    code of `F`, whose members are the `y` with `F(y)`.
  * `descentOne`: `(D^0)` at the value `φ_1 = ε`, at cut rank `blkTop (L+1)`:
    Step 2 applied to `ψ_L(g) :≡ ∀u (Eps(u, g) → Acc_L(u))`, whose progressiveness
    is the finitary (EP_L), `epsProg_provable`.
-/
import OrdinalAnalysis.Ramified.DescentBetaAux3

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalVNote (precDef₁)
open OrdinalAnalysis.Gentzen.InternalEpsMonoCode (epsDef₁)
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)

/-! ### Substitution and free variables -/

theorem subst_arAt {k : ℕ} (σ : ArithmeticSemisentence k) (w : Fin k → Semiterm LRA ℕ 1) (x : ℕ) :
    (arAt σ w)/[(num x : SyntacticTerm LRA)] =
      arAt σ (fun i => Rew.subst ![(num x : SyntacticTerm LRA)] (w i)) := by
  show Rew.subst ![(num x : SyntacticTerm LRA)] ▹ (Rew.subst w ▹ arR σ) = Rew.subst _ ▹ arR σ
  rw [← TransitiveRewriting.comp_app]
  have e : ((Rew.subst ![(num x : SyntacticTerm LRA)]).comp (Rew.subst w) : Rew LRA ℕ k ℕ 0) =
      Rew.subst (fun i => Rew.subst ![(num x : SyntacticTerm LRA)] (w i)) := by
    ext i
    · simp [Rew.comp_app]
    · simp [Rew.comp_app]
  rw [e]

theorem freeVariables_arAt' {n k : ℕ} (σ : ArithmeticSemisentence k)
    (v : Fin k → Semiterm LRA ℕ n) (hv : ∀ i, (v i).freeVariables = ∅) :
    (arAt σ v).freeVariables = ∅ :=
  freeVariables_rewR_eq_empty (Rew.subst v) (freeVariables_arR σ)
    (fun i => by rw [Rew.subst_bvar]; exact hv i)

theorem freeVariables_subst_num {φ : Semiformula LRA ℕ 1} (h : φ.freeVariables = ∅) (x : ℕ) :
    (φ/[(num x : SyntacticTerm LRA)]).freeVariables = ∅ :=
  freeVariables_rewR_eq_empty _ h
    (fun i => by rw [Subsingleton.elim i 0, Rew.subst_bvar]; exact freeVariables_numAtR)

theorem freeVariables_progR {φ : Semiformula LRA ℕ 1} (h : φ.freeVariables = ∅) :
    (progR φ).freeVariables = ∅ := by
  have h1 : (φ/[(#0 : Semiterm LRA ℕ 2)]).freeVariables = ∅ :=
    freeVariables_rewR_eq_empty _ h (fun i => by rw [Subsingleton.elim i 0]; simp)
  have h3 : (arAt precDef₁.val ![(#0 : Semiterm LRA ℕ 2), #1]).freeVariables = ∅ :=
    freeVariables_arAt' _ _ (fun i => by fin_cases i <;> rfl)
  simp [progR, h1, h, h3]

theorem freeVariables_accBody_inst (μ : Lv) (v z : ℕ) :
    ((accBody μ v)/[(num z : SyntacticTerm LRA)]).freeVariables = ∅ := by
  have h := freeVariables_accA μ v
  rw [accA_eq, Semiformula.freeVariables_all] at h
  exact freeVariables_subst_num h z

theorem freeVariables_psiR (μ : Lv) : (psiR μ).freeVariables = ∅ := by
  have h1 : (arAt epsDef₁.val ![(#0 : Semiterm LRA ℕ 2), #1]).freeVariables = ∅ :=
    freeVariables_arAt' _ _ (fun i => by fin_cases i <;> rfl)
  have h2 : ((tiMuR μ)/[(#0 : Semiterm LRA ℕ 2)]).freeVariables = ∅ :=
    freeVariables_rewR_eq_empty _ (freeVariables_tiMuR μ)
      (fun i => by rw [Subsingleton.elim i 0]; simp)
  simp [psiR, h1, h2]

theorem subst_num_eval {M : Type} [s : Structure LRA M] (φ : Semiformula LRA ℕ 1) (x : ℕ)
    (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (φ/[(num x : SyntacticTerm LRA)]) ↔
      Semiformula.Eval (s := s) ![numVal M x] f φ := by
  rw [Semiformula.eval_substs]
  have h : (Semiterm.val (s := s) ![] f ∘ ![(num x : SyntacticTerm LRA)]) =
      ![numVal M x] := by
    funext i
    rw [Subsingleton.elim i 0]
    exact val_numAtR_model _ _ x
  rw [h]

/-! ### Heights and ranks -/

theorem omegaPow_one_le_blkTop {ℓ : Lv} (h : ℓ ≠ 0) :
    Gamma0Note.omegaPow 1 ≤ Gamma0Note.blkTop ℓ := by
  rw [Gamma0Note.blkTop_of_ne_zero h]
  exact Gamma0Note.le_nadd_right _ _

theorem nadd_one_ne_zero (L : Lv) : Gamma0Note.nadd L 1 ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le Gamma0Note.zero_lt_one (Gamma0Note.one_le_nadd_one L))

theorem epsilon_le_nadd {H : Gamma0Note} (hH : Gamma0Note.epsilonNote 0 ≤ H) (n : ℕ) :
    Gamma0Note.epsilonNote 0 ≤ Gamma0Note.nadd H (Gamma0Note.ofNat n) :=
  le_trans hH (le_nadd_ofNat H n)

namespace DerLt

variable {ρ : Gamma0Note}

/-- **Conversion along a validity**: a formula may be replaced by any logical
consequence of it, two inferences higher. -/
theorem conv {A C : Proposition LRA} {Γ : Sequent LRA} {H : Gamma0Note}
    (hA : A.freeVariables = ∅) (hC : C.freeVariables = ∅)
    (hv : ∀ (M : Type) [Nonempty M] [Structure LRA M] (f : ℕ → M),
      Semiformula.Evalf f A → Semiformula.Evalf f C)
    (hrk : rank A < ρ) (hρ : Gamma0Note.omegaPow 1 ≤ ρ) (hH : Gamma0Note.epsilonNote 0 ≤ H)
    (h : DerLt ρ (evR A :: Γ) H) :
    DerLt ρ (evR C :: Γ) (Gamma0Note.nadd H (Gamma0Note.ofNat 2)) :=
  discharge [A] hC (fun B hB => by rw [List.mem_singleton.mp hB]; exact hA)
    (fun M _ _ f hAs => hv M f (hAs A List.mem_cons_self))
    (fun B hB => by rw [List.mem_singleton.mp hB]; exact hrk)
    (fun B hB => by rw [List.mem_singleton.mp hB]; exact h) hρ hH

end DerLt

/-! ### Introduction of `Acc_μ(v)` -/

/-- `x ≺₁ v → x ∈̇_μ z`, in `x`. -/
def belowB (μ : Lv) (v z : ℕ) : Semiformula LRA ℕ 1 :=
  ∼arAt precDef₁.val ![(#0 : Semiterm LRA ℕ 1), numAtR v] ⋎ memAt μ #0 (numAtR z)

theorem belowB_inst (μ : Lv) (v z x : ℕ) :
    (belowB μ v z)/[(num x : SyntacticTerm LRA)] = ∼precA x v ⋎ memA μ x z := by
  simp only [belowB, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    rew_memAt, subst_arAt, precA, memA]
  have h : (fun i => Rew.subst ![(num x : SyntacticTerm LRA)]
      (![(#0 : Semiterm LRA ℕ 1), numAtR v] i)) = ![numAtR x, numAtR v] := by
    funext i; fin_cases i <;> simp [num]
  rw [h, Rew.subst_bvar, rew_numAtR]
  rfl

theorem eval_belowB {M : Type} [s : Structure LRA M] (μ : Lv) (v z : ℕ) (y : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![y] f (belowB μ v z) ↔
      (precM y (numVal M v) → memM μ y (numVal M z)) := by
  simp only [belowB, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq, eval_arAt, eval_memAt_bvar]
  have h : (fun i => Semiterm.val (s := s) ![y] f
      (![(#0 : Semiterm LRA ℕ 1), numAtR v] i)) = ![y, numVal M v] := by
    funext i; fin_cases i
    · rfl
    · exact val_numAtR_model _ _ v
  rw [h]
  exact imp_iff_not_or.symm

theorem freeVariables_belowB (μ : Lv) (v z : ℕ) : (belowB μ v z).freeVariables = ∅ := by
  have h1 : (arAt precDef₁.val ![(#0 : Semiterm LRA ℕ 1), numAtR v]).freeVariables = ∅ :=
    freeVariables_arAt' _ _ (fun i => by fin_cases i <;> simp)
  simp [belowB, h1, freeVariables_memAt]

theorem lvlOf_belowB (μ : Lv) (v z : ℕ) : lvlOf (belowB μ v z) = μ := by
  simp [belowB, lvlOf_memAt]

variable {ρ : Gamma0Note}

/-- **Introduction of `Acc_μ(v)`.** -/
theorem accIntro {μ : Lv} (v : ℕ) {Γ : Sequent LRA} {H : Gamma0Note}
    (hρ1 : Gamma0Note.omegaPow 1 ≤ ρ) (hρ : Gamma0Note.blkTop (Gamma0Note.nadd μ 1) ≤ ρ)
    (hH : Gamma0Note.epsilonNote 0 ≤ H)
    (h : ∀ z x : ℕ, TrueN (precA x v) →
      DerLt ρ (evR (∼progA μ z) :: evR (memA μ x z) :: Γ) H) :
    DerLt ρ (evR (accA μ v) :: Γ) (Gamma0Note.nadd H (Gamma0Note.ofNat 6)) := by
  rw [evR_accA]
  refine DerLt.all (H := Gamma0Note.nadd H (Gamma0Note.ofNat 5)) (fun z => ?_)
    (nadd_ofNat_lt_nadd_ofNat H (by norm_num))
  rw [evInstR_inst_ev]
  have hx : ∀ x : ℕ, DerLt ρ (evR (∼precA x v) :: evR (memA μ x z) :: evR (∼progA μ z) :: Γ) H := by
    intro x
    by_cases hpx : TrueN (precA x v)
    · exact (h z x hpx).weak (by subset_tac)
    · have ht : DerLt ρ [evR (∼precA x v)] H :=
        DerLt.of_true ((rFree_neg _).mpr (rFree_arAt _ _))
          (by rw [Semiformula.freeVariables_not]; exact freeVariables_precA x v)
          ((trueN_neg _).mpr hpx) hH
      exact ht.weak (by subset_tac)
  have h3 : DerLt ρ (evR (∀¹ belowB μ v z) :: evR (∼progA μ z) :: Γ)
      (Gamma0Note.nadd H (Gamma0Note.ofNat 2)) := by
    rw [evR_all]
    refine DerLt.all (H := Gamma0Note.nadd H (Gamma0Note.ofNat 1)) (fun x => ?_)
      (nadd_ofNat_lt_nadd_ofNat H (by norm_num))
    rw [evInstR_inst_ev, belowB_inst, evR_or]
    exact DerLt.or (hx x) (lt_of_le_of_lt (le_of_eq (Gamma0Note.nadd_zero H).symm)
      (nadd_ofNat_lt_nadd_ofNat H (by norm_num : 0 < 1)))
  have h4 : DerLt ρ (evR (∼progA μ z ⋎ (∀¹ belowB μ v z)) :: Γ)
      (Gamma0Note.nadd H (Gamma0Note.ofNat 3)) := by
    rw [evR_or]
    exact DerLt.or (h3.weak (by subset_tac)) (nadd_ofNat_lt_nadd_ofNat H (by norm_num))
  have hA : (∼progA μ z ⋎ (∀¹ belowB μ v z)).freeVariables = ∅ := by
    rw [Semiformula.freeVariables_or, Semiformula.freeVariables_not, freeVariables_progA,
      Semiformula.freeVariables_all, freeVariables_belowB, Finset.union_empty]
  have hrk : rank (∼progA μ z ⋎ (∀¹ belowB μ v z)) < ρ := by
    refine lt_of_lt_of_le (rank_lt_of_lvlOf_le (L := μ) ?_) hρ
    rw [lvlOf_or, lvlOf_neg, lvlOf_progA, lvlOf_all, lvlOf_belowB, max_self]
  have h5 := DerLt.conv (C := (accBody μ v)/[(num z : SyntacticTerm LRA)]) hA
    (freeVariables_accBody_inst μ v z) (fun M _ _ f hE => by
      show Semiformula.Eval ![] f _
      rw [eval_accBody_inst]
      have hE' : Semiformula.Eval ![] f (∼progA μ z ⋎ (∀¹ belowB μ v z)) := hE
      simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
        LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq, eval_progA,
        Semiformula.eval_all] at hE'
      intro hprog y hy
      rcases hE' with hn | hall
      · exact absurd hprog hn
      · have hb := hall y
        have e : (y :> (![] : Fin 0 → M)) = ![y] := by
          funext i; fin_cases i; rfl
        rw [e, eval_belowB] at hb
        exact hb hy)
    hrk hρ1 (epsilon_le_nadd hH 3) h4
  rw [nadd_ofNat_add] at h5
  exact h5

/-! ### The copy lemma at numerals -/

theorem copy_num_provable {ν μ κ : Lv} (hκ : κ < μ) (hμ : μ < ν) (y : ℕ) :
    RAlt ν ⊢ Semiformula.univCl (∼accA μ y ⋎ accA κ y) := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos (lt_of_le_of_lt (gamma0_zero_le κ) (lt_trans hκ hμ))
  have hc : (∼accA μ y ⋎ accA κ y).freeVariables = ∅ := by
    rw [Semiformula.freeVariables_or, Semiformula.freeVariables_not, freeVariables_accA,
      freeVariables_accA, Finset.union_empty]
  refine provable_of_eqModels hν ?_ ?_
  · rw [emb_univCl_of_freeVariables_eq_empty hc, lvlOf_or, lvlOf_neg]
    exact max_lt (lt_of_le_of_lt (lvlOf_accA_le μ y) hμ)
      (lt_of_le_of_lt (lvlOf_accA_le κ y) (lt_trans hκ hμ))
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f (∼accA μ y ⋎ accA κ y)
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, eval_accA,
      eval_accA]
    by_cases h : TImu μ (numVal N y)
    · exact Or.inr (TImu_copy hN hκ hμ h)
    · exact Or.inl h

/-- **The copy lemma**, `Acc_μ(y) → Acc_κ(y)` for `κ ≤ μ`, below `ε₀`. -/
theorem copyD {μ κ : Lv} (hκ : κ ≤ μ) (y : ℕ)
    (hρ : Gamma0Note.blkTop (Gamma0Note.nadd μ 1) ≤ ρ) {H : Gamma0Note}
    (hH : Gamma0Note.epsilonNote 0 ≤ H) :
    DerLt ρ [evR (∼accA μ y), evR (accA κ y)] H := by
  rcases lt_or_eq_of_le hκ with hlt | rfl
  · have h := DerLt.of_RAlt (Gamma0Note.one_le_nadd_one μ)
      (by rw [Semiformula.freeVariables_or, Semiformula.freeVariables_not, freeVariables_accA,
        freeVariables_accA, Finset.union_empty])
      (copy_num_provable hlt (Gamma0Note.lt_nadd_one μ) y) hρ hH
    rw [evR_or] at h
    exact h.invOr
  · rw [evR_neg]
    exact (DerLt.identity (evR (accA κ y)) hH).weak (by subset_tac)

/-! ### The equivalence of a parameter-free name with its body -/

/-- `∀y (y ∈̇_μ w̄ ↔ B(y))`. -/
def nameIff (μ : Lv) (B : Semiformula LRA ℕ 1) (w : ℕ) : Proposition LRA :=
  ∀¹ ((∼memAt μ (#0 : Semiterm LRA ℕ 1) (numAtR w) ⋎ B) ⋏ (∼B ⋎ memAt μ #0 (numAtR w)))

theorem nameIff_inst (μ : Lv) (B : Semiformula LRA ℕ 1) (w y : ℕ) :
    ((∼memAt μ (#0 : Semiterm LRA ℕ 1) (numAtR w) ⋎ B) ⋏
        (∼B ⋎ memAt μ #0 (numAtR w)))/[(num y : SyntacticTerm LRA)] =
      (∼memA μ y w ⋎ B/[(num y : SyntacticTerm LRA)]) ⋏
        (∼(B/[(num y : SyntacticTerm LRA)]) ⋎ memA μ y w) := by
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, rew_memAt, Rew.subst_bvar, rew_numAtR, memA]
  rfl

theorem freeVariables_nameIff (μ : Lv) {B : Semiformula LRA ℕ 1} (hB : B.freeVariables = ∅)
    (w : ℕ) : (nameIff μ B w).freeVariables = ∅ := by
  simp [nameIff, hB, freeVariables_memAt, freeVariables_nmemAt]

theorem eval_nameIff {M : Type} [s : Structure LRA M] (μ : Lv) (B : Semiformula LRA ℕ 1) (w : ℕ)
    (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (nameIff μ B w) ↔
      ∀ y : M, (memM μ y (numVal M w) ↔ Semiformula.Eval (s := s) ![y] f B) := by
  simp only [nameIff, Semiformula.eval_all, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.and_eq, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq]
  refine forall_congr' fun y => ?_
  have e : (y :> (![] : Fin 0 → M)) = ![y] := by
    funext i; fin_cases i; rfl
  rw [e, eval_memAt_bvar]
  tauto

/-- **The rank of `∀y (y ∈̇_μ w̄ ↔ B(y))` is below `blkTop μ`.** -/
theorem rank_nameIff_lt {μ : Lv} (hμ : μ ≠ 0) {B : Semiformula LRA ℕ 1} (hB : lvlOf B < μ)
    (w : ℕ) : rank (nameIff μ B w) < Gamma0Note.blkTop μ := by
  have hm : rank (memAt μ (#0 : Semiterm LRA ℕ 1) (numAtR w)) < Gamma0Note.blkTop μ := by
    rw [rank_memAt, memRank_of_groundR hμ (groundR_numAtR w), evTermR_numAtR]
    exact Gamma0Note.blk_nadd_ofNat_lt_blkTop hμ _
  have hb : rank B < Gamma0Note.blkTop μ := rank_lt_blkTop_of_level hB
  have hs : ∀ x, x < Gamma0Note.blkTop μ → OrdinalNotation.succ x < Gamma0Note.blkTop μ :=
    fun x hx => Gamma0Note.succ_lt_blkTop hx
  simp only [nameIff, rank_all, rank_and, rank_or, rank_neg]
  exact hs _ (hs _ (max_lt (hs _ (max_lt hm hb)) (hs _ (max_lt hb hm))))

/-- **A parameter-free name has exactly the members its body says**, derived by
one (Pr) and one (Pr⁻) inference at every numeral. -/
theorem nameIff_derivable {μ : Lv} {B : Semiformula LRA ℕ 1} (hB : B.freeVariables = ∅)
    (hl : lvlOf B < μ) {H : Gamma0Note} (hH : Gamma0Note.epsilonNote 0 ≤ H) :
    DerLt ρ [evR (nameIff μ B (code μ B))] (Gamma0Note.nadd H (Gamma0Note.ofNat 4)) := by
  have hg : Good (code μ B) := good_code hl
  have hlv : lvl (code μ B) = μ := lvl_code μ B
  have hbd : body (code μ B) = B := body_code hB
  rw [nameIff, evR_all]
  refine DerLt.all (H := Gamma0Note.nadd H (Gamma0Note.ofNat 3)) (fun y => ?_)
    (nadd_ofNat_lt_nadd_ofNat H (by norm_num))
  rw [evInstR_inst_ev, nameIff_inst, evR_and, evR_or, evR_or, evR_neg, evR_neg]
  have hinst : evInstR.inst (body (code μ B)) y = evR (B/[(num y : SyntacticTerm LRA)]) := by
    rw [hbd, evInstR_inst]
  have hmem : evR (memA μ y (code μ B)) = memAt (lvl (code μ B)) (num y) (num (code μ B)) := by
    rw [memA, evR_memAt_num, hlv]; rfl
  have hid : DerLt ρ [evR (B/[(num y : SyntacticTerm LRA)]),
      ∼evR (B/[(num y : SyntacticTerm LRA)])] H := DerLt.identity _ hH
  have hn : DerLt ρ [∼evR (memA μ y (code μ B)), evR (B/[(num y : SyntacticTerm LRA)])]
      (Gamma0Note.nadd H (Gamma0Note.ofNat 1)) := by
    rw [hmem]
    refine DerLt.npr hg ?_ (lt_of_le_of_lt (le_of_eq (Gamma0Note.nadd_zero H).symm)
      (nadd_ofNat_lt_nadd_ofNat H (by norm_num : 0 < 1)))
    rw [hinst]
    exact hid.weak (by subset_tac)
  have hp : DerLt ρ [evR (memA μ y (code μ B)), ∼evR (B/[(num y : SyntacticTerm LRA)])]
      (Gamma0Note.nadd H (Gamma0Note.ofNat 1)) := by
    rw [hmem]
    refine DerLt.pr hg ?_ (lt_of_le_of_lt (le_of_eq (Gamma0Note.nadd_zero H).symm)
      (nadd_ofNat_lt_nadd_ofNat H (by norm_num : 0 < 1)))
    rw [hinst]
    exact hid
  refine DerLt.and (H := Gamma0Note.nadd H (Gamma0Note.ofNat 2)) ?_ ?_
    (nadd_ofNat_lt_nadd_ofNat H (by norm_num))
  · exact DerLt.or hn (nadd_ofNat_lt_nadd_ofNat H (by norm_num))
  · exact DerLt.or (hp.weak (by subset_tac)) (nadd_ofNat_lt_nadd_ofNat H (by norm_num))

/-! ### Step 2 -/

/-- **Step 2 of the generalised descent.** -/
theorem step2 {L : Lv} {F : Semiformula LRA ℕ 1} (hFc : F.freeVariables = ∅)
    (hFl : lvlOf F ≤ L) {H : Gamma0Note} (hH : Gamma0Note.epsilonNote 0 ≤ H)
    (hP : DerLt (Gamma0Note.blkTop (Gamma0Note.nadd L 1)) [evR (progR F)] H) (c : ℕ) :
    DerLt (Gamma0Note.blkTop (Gamma0Note.nadd L 1))
      [evR (∼accA (Gamma0Note.nadd L 1) c), evR (F/[(num c : SyntacticTerm LRA)])]
      (Gamma0Note.nadd H (Gamma0Note.ofNat 7)) := by
  set μ : Lv := Gamma0Note.nadd L 1 with hμdef
  have hμ0 : μ ≠ 0 := nadd_one_ne_zero L
  have hFμ : lvlOf F < μ := lt_of_le_of_lt hFl (Gamma0Note.lt_nadd_one L)
  set w : ℕ := code μ F with hw
  have hname := nameIff_derivable (ρ := Gamma0Note.blkTop μ) hFc hFμ hH
  have hC : (∼accA μ c ⋎ F/[(num c : SyntacticTerm LRA)]).freeVariables = ∅ := by
    rw [Semiformula.freeVariables_or, Semiformula.freeVariables_not, freeVariables_accA,
      freeVariables_subst_num hFc, Finset.union_empty]
  have h := DerLt.discharge (ρ := Gamma0Note.blkTop μ) (Γ := [])
    (H := Gamma0Note.nadd H (Gamma0Note.ofNat 4))
    [nameIff μ F w, progR F] hC
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact freeVariables_nameIff μ hFc w
      · exact freeVariables_progR hFc)
    (by
      intro M _ _ f hAs
      have h1 : Semiformula.Eval ![] f (nameIff μ F w) := hAs _ List.mem_cons_self
      have h2 : Semiformula.Eval ![] f (progR F) :=
        hAs _ (List.mem_cons_of_mem _ List.mem_cons_self)
      rw [eval_nameIff] at h1
      rw [eval_progR] at h2
      show Semiformula.Eval ![] f (∼accA μ c ⋎ F/[(num c : SyntacticTerm LRA)])
      rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, eval_accA,
        subst_num_eval]
      by_cases hacc : TImu μ (numVal M c)
      · right
        have hti := hacc (numVal M w)
        have hprogZ : ProgM (fun y => memM μ y (numVal M w)) := fun y hy =>
          (h1 y).mpr (h2 y fun x hx => (h1 x).mp (hy x hx))
        exact h2 _ fun x hx => (h1 x).mp (hti hprogZ x hx)
      · exact Or.inl hacc)
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact rank_nameIff_lt hμ0 hFμ w
      · exact rank_lt_of_lvlOf_le (by rw [lvlOf_progR]; exact hFl))
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact hname
      · exact hP.mono (le_nadd_ofNat H 4))
    (omegaPow_one_le_blkTop hμ0) (epsilon_le_nadd hH 4)
  simp only [List.length_cons, List.length_nil] at h
  rw [evR_or, nadd_ofNat_add] at h
  exact h.invOr

/-! ### `(D^0)`, the value `ε` -/

/-- **`(D^0)` in `RA_∞` at cut rank `blkTop (L+1)`**: `¬Acc_{L+1}(c̄), Acc_L(ε̄_c)`,
below `ε₀ ⊕ 10`, for every level `L > 0` and every notation `c`. -/
theorem descentOne {L : Lv} (hL : 0 < L) (c : Gamma0Note) :
    DerLt (Gamma0Note.blkTop (Gamma0Note.nadd L 1))
      [evR (∼accA (Gamma0Note.nadd L 1) (gamma0Code c)),
        evR (accA L (gamma0Code (Gamma0Note.veblenNote 1 c)))]
      (Gamma0Note.nadd (Gamma0Note.epsilonNote 0) (Gamma0Note.ofNat 10)) := by
  set ρ : Gamma0Note := Gamma0Note.blkTop (Gamma0Note.nadd L 1) with hρdef
  have hρ1 : Gamma0Note.omegaPow 1 ≤ ρ := omegaPow_one_le_blkTop (nadd_one_ne_zero L)
  have hε : Gamma0Note.epsilonNote 0 ≤ Gamma0Note.epsilonNote 0 := le_rfl
  have hP : DerLt ρ [evR (progR (psiR L))] (Gamma0Note.epsilonNote 0) :=
    DerLt.of_RAlt (Gamma0Note.one_le_nadd_one L) (freeVariables_progR (freeVariables_psiR L))
      (epsProg_provable hL (Gamma0Note.lt_nadd_one L)) le_rfl hε
  have h2 := step2 (freeVariables_psiR L) (lvlOf_psiR_le L) hε hP (gamma0Code c)
  have hE : DerLt ρ [evR (epsA (gamma0Code (Gamma0Note.epsilonNote c)) (gamma0Code c))]
      (Gamma0Note.nadd (Gamma0Note.epsilonNote 0) (Gamma0Note.ofNat 7)) :=
    DerLt.of_true (rFree_arAt _ _) (freeVariables_epsA _ _) (epsA_true_code c)
      (epsilon_le_nadd hε 7)
  have h := DerLt.discharge (ρ := ρ)
    (Γ := [evR (∼accA (Gamma0Note.nadd L 1) (gamma0Code c))])
    (H := Gamma0Note.nadd (Gamma0Note.epsilonNote 0) (Gamma0Note.ofNat 7))
    [(psiR L)/[(num (gamma0Code c) : SyntacticTerm LRA)],
      epsA (gamma0Code (Gamma0Note.epsilonNote c)) (gamma0Code c)]
    (C := accA L (gamma0Code (Gamma0Note.epsilonNote c)))
    (freeVariables_accA _ _)
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact freeVariables_subst_num (freeVariables_psiR L) _
      · exact freeVariables_epsA _ _)
    (by
      intro M _ _ f hAs
      have h1 : Semiformula.Eval ![] f ((psiR L)/[(num (gamma0Code c) : SyntacticTerm LRA)]) :=
        hAs _ List.mem_cons_self
      have h3 : Semiformula.Eval ![] f
          (epsA (gamma0Code (Gamma0Note.epsilonNote c)) (gamma0Code c)) :=
        hAs _ (List.mem_cons_of_mem _ List.mem_cons_self)
      rw [subst_num_eval, eval_psiR] at h1
      rw [eval_epsA] at h3
      show Semiformula.Eval ![] f (accA L (gamma0Code (Gamma0Note.epsilonNote c)))
      rw [eval_accA]
      exact h1 _ h3)
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact rank_lt_of_lvlOf_le (by rw [lvlOf_subst₁]; exact lvlOf_psiR_le L)
      · exact rank_lt_of_lvlOf_le (by rw [lvlOf_epsA]; exact gamma0_zero_le L))
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact h2.weak (by subset_tac)
      · exact hE.weak (by subset_tac))
    hρ1 (epsilon_le_nadd hε 7)
  rw [nadd_ofNat_add] at h
  exact h.weak (by subset_tac)

end Ramified

end OrdinalAnalysis
