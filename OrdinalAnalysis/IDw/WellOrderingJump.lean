/-
  Gentzen's jump inside models of `IDw WFormWc`, and BP78 Lemma 1 (sums).

  Sources: W. Buchholz and W. Pohlers, *Provable wellorderings of formal theories for
  transfinitely iterated inductive definitions*, J. Symbolic Logic 43 (1978), pp. 121–123
  (Lemma 1); T. Arai, *Lectures on ordinal analysis*, arXiv:2304.00246, Lemma 1.31 (the jump).
  The `ID_n` version is the jump section of `IDn/WellOrdering.lean` (`HL`, `JF`, `hl_app`,
  `jump_prog`, `holds_of_jump`, `W_cons`); here the class `Dc k` is replaced by
  `ClsW B := fld ∧ CoefW B` (the coefficient condition for the levels satisfying `B`;
  `D_k = ClsW (· < k)` is definitionally `DkW k`), the exponent list `itoL` by `expList`, and the
  `hJ.*` facts by the lemmas of `IDw/Internal/JumpList.lean`.

  * `ClsW`, `HLW`, `JFW`: the class, `HL(η)` ("`F` holds on every member of the class whose
    exponent list is below `η`") and the jump `J(y)` ("appending `y` to a descending list keeps
    `HL`");
  * `dfn_JFW` (J1a): `JFW` is definable in `LXJ`;
  * `hl_app`: iterating the jump along a list, by order induction on the appended list;
  * `jump_prog` (J1b): the jump is progressive on the class (Gentzen's Lemma B);
  * `holds_of_jump` (J1c): `F ξ` from the jump at every class member `≼` the head of `expList ξ`;
  * `W_cons` (L1, BP78 Lemma 1): a normal sum of `D_k` below `Ω_{k+1}` is in `J(k, ·)` once its
    first entry is (the jump with `B := (· < k)`, `F := (· ≺ Ω_{k+1} → J(k, ·))`);
  * `W_of_E'`, `W_Omega'`, `W_theta'`, `W_theta_of_TI'`: the theorems of `IDw/WellOrderingW.lean`
    with the hypotheses `ConsStmt`, `MonoStmt`, `OmegaStmt` discharged.
-/
import OrdinalAnalysis.IDw.WellOrderingW

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OrdinalAnalysis.IDw.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.IDw.Internal

section Jump

variable {N : Type} [ORingStructure N] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [s : Structure LXJ N]

/-! ### Order-free facts about exponent lists -/

omit [s : Structure LXJ N] in
/-- The coefficients of the exponent list of a code are those of the code. -/
theorem iinE_expList (k g x : N) : iinE k g (expList x) = 1 ↔ iinE k g x = 1 := by
  by_cases h : kind x = 1 ∨ kind x = 2 ∨ kind x = 4
  · rw [expList_of_prin h, iinE_cons_iff]
    simp
  · simp [expList, h]

omit [s : Structure LXJ N] in
theorem expList_ne_zero {x : N} (hx : x ≠ 0) : expList x ≠ 0 := by
  by_cases h : kind x = 1 ∨ kind x = 2 ∨ kind x = 4
  · rw [expList_of_prin h]; exact tcCons_ne_zero _ _
  · simpa [expList, h] using hx

omit [s : Structure LXJ N] in
/-- The head of a nonempty descending list is in the field. -/
theorem fldW_tcHd {r : N} (hr : isSL r) (hr0 : r ≠ 0) : fldW (tcHd r) := by
  obtain ⟨z, w, rfl⟩ := isSL_eq_cons hr hr0
  rw [tcHd_tcCons]
  exact ((isSL_cons_iff z w).mp hr).1

/-! ### The class, `HL`, and the jump -/

/-- The class of normal domain codes whose coefficients of the levels satisfying `B` are
distinguished: `D_k = ClsW (· < k)`, `M = ClsW (fun _ => True)`. -/
def ClsW (B : N → Prop) (x : N) : Prop := fldW x ∧ CoefW B x

/-- `HL(η)`: `F` holds on every member of the class whose exponent list is below `η`. -/
def HLW (B F : N → Prop) (η : N) : Prop :=
  ∀ ξ, ClsW B ξ → iltb (expList ξ) η = 1 → F ξ

/-- **The jump** `J(y)`: appending the exponent `y` to a list keeps `HL`. -/
def JFW (B F : N → Prop) (y : N) : Prop :=
  ∀ η, isSL η → isSL (isnocL η y) → HLW B F η → HLW B F (isnocL η y)

theorem hlW_zero {B F : N → Prop} : HLW B F (0 : N) := fun _ _ h => absurd h (not_iltb_zero_right _)

/-- `F` holds at `ξ` once `HL` holds at its exponent list, given progressiveness. -/
theorem holds_of_hl {B F : N → Prop} (hP : ProgW (ClsW B) F) {ξ : N} (hξ : ClsW B ξ)
    (h : HLW B F (expList ξ)) : F ξ :=
  hP ξ hξ fun ξ' hξ' hlt => h ξ' hξ' ((iltb_expList_iff hξ'.1.1 hξ.1.1).mpr hlt)

variable (M : WModel N)
include M

/-! ### J1a. Definability -/

theorem dfn_ClsW {B : N → Prop} (hB : 𝚺₁.DefinablePred B) : LXJ.DefinablePred (ClsW B) := by
  have h1 : LXJ.DefinablePred fun x : N => fldW x :=
    M.dfn_arith (ℌ := 𝚺₁) (by unfold fldW; definability)
  exact Language.Definable.of_iff (Language.Definable.and h1 (dfn_coef M hB)) fun v => Iff.rfl

theorem dfn_compW {m : ℕ} {Q : N → Prop} (hQ : LXJ.DefinablePred Q)
    {f : (Fin m → N) → N} (hf : 𝚺₁.DefinableFunction f) :
    LXJ.Definable fun v : Fin m → N => Q (f v) :=
  @Language.DefinablePred.comp LXJ N _ Q m f hQ (M.dfn_arith hf)

theorem dfn_HLW {B F : N → Prop} (hB : 𝚺₁.DefinablePred B) (hF : LXJ.DefinablePred F) :
    LXJ.DefinablePred (HLW B F) := by
  have h : LXJ.Definable fun w : Fin 2 → N =>
      ClsW B (w 0) → iltb (expList (w 0)) (w 1) = 1 → F (w 0) :=
    Language.Definable.imp (dfn_pred (dfn_ClsW M hB) 0)
      (Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by definability)) (dfn_pred hF 0))
  exact Language.Definable.of_iff (dfn_forall h) fun v => Iff.rfl

/-- J1a. -/
theorem dfn_JFW {B F : N → Prop} (hB : 𝚺₁.DefinablePred B) (hF : LXJ.DefinablePred F) :
    LXJ.DefinablePred (JFW (s := s) B F) := by
  have hi : 𝚺₁.DefinableFunction fun w : Fin 2 → N => isnocL (w 0) (w 1) := by definability
  have h := dfn_forall (m := 1)
    (R := fun w : Fin 2 → N => isSL (w 0) → isSL (isnocL (w 0) (w 1)) →
      HLW B F (w 0) → HLW B F (isnocL (w 0) (w 1)))
    (Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by definability))
      (Language.Definable.imp
        (dfn_compW M (Q := isSL) (M.dfn_arith (ℌ := 𝚺₁) (by definability)) hi)
        (Language.Definable.imp (dfn_pred (dfn_HLW M hB hF) 0)
          (dfn_compW M (dfn_HLW M hB hF) hi))))
  exact Language.Definable.of_iff h fun v => Iff.rfl

theorem dfn_hl_app {B F : N → Prop} (hB : 𝚺₁.DefinablePred B) (hF : LXJ.DefinablePred F) :
    LXJ.DefinablePred fun r : N => r ≠ 0 → isSL r → CoefW B r →
      (∀ y, ClsW B y → (iltb y (tcHd r) = 1 ∨ y = tcHd r) → JFW B F y) →
      ∀ η, isSL η → isSL (iapp η r) → HLW B F η → HLW B F (iapp η r) := by
  have h2 := dfn_forall (m := 1)
    (R := fun w : Fin 2 → N => ClsW B (w 0) → (iltb (w 0) (tcHd (w 1)) = 1 ∨ w 0 = tcHd (w 1)) →
      JFW B F (w 0))
    (Language.Definable.imp (dfn_pred (dfn_ClsW M hB) 0)
      (Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by definability))
        (dfn_pred (dfn_JFW M hB hF) 0)))
  have hf : 𝚺₁.DefinableFunction fun w : Fin 2 → N => iapp (w 0) (w 1) := by definability
  have h3 := dfn_forall (m := 1)
    (R := fun w : Fin 2 → N => isSL (w 0) → isSL (iapp (w 0) (w 1)) → HLW B F (w 0) →
      HLW B F (iapp (w 0) (w 1)))
    (Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by definability))
      (Language.Definable.imp
        (dfn_compW M (Q := isSL) (M.dfn_arith (ℌ := 𝚺₁) (by definability)) hf)
        (Language.Definable.imp (dfn_pred (dfn_HLW M hB hF) 0)
          (dfn_compW M (dfn_HLW M hB hF) hf))))
  refine Language.Definable.imp ?_ (Language.Definable.imp ?_
    (Language.Definable.imp (dfn_pred (dfn_coef M hB) 0) (Language.Definable.imp ?_ ?_)))
  · exact M.dfn_arith (ℌ := 𝚺₁) (by definability)
  · exact M.dfn_arith (ℌ := 𝚺₁) (by definability)
  · exact Language.Definable.of_iff h2 fun v => by simp
  · exact Language.Definable.of_iff h3 fun v => by simp

/-! ### J1b. The jump is progressive -/

/-- **Iterating the jump along a list** (the finite iteration in Gentzen's Lemma B). -/
theorem hl_app {B F : N → Prop} (hB : 𝚺₁.DefinablePred B) (hF : LXJ.DefinablePred F) :
    ∀ r : N, r ≠ 0 → isSL r → CoefW B r →
      (∀ y, ClsW B y → (iltb y (tcHd r) = 1 ∨ y = tcHd r) → JFW B F y) →
      ∀ η, isSL η → isSL (iapp η r) → HLW B F η → HLW B F (iapp η r) := by
  refine M.oind (dfn_hl_app M hB hF) ?_
  intro r ih hr0 hr hEr hJy η hη hηr hHL
  obtain ⟨z, r', rfl⟩ := isSL_eq_cons hr hr0
  obtain ⟨hz, hr', hdesc⟩ := (isSL_cons_iff z r').mp hr
  have hzD : ClsW B z := ⟨hz, fun j hj δ hδ =>
    hEr j hj δ ((iinE_cons_iff _ _ _ _).mpr (Or.inl hδ))⟩
  have hJz : JFW B F z := hJy z hzD (Or.inr (tcHd_tcCons z r').symm)
  have hsn : isSL (isnocL η z) := isSL_isnocL_of_isSL_iapp z r' η hηr
  have h1 : HLW B F (isnocL η z) := hJz η hη hsn hHL
  rcases eq_or_ne r' 0 with rfl | hr'0
  · exact h1
  · have e : iapp η (tcCons z r') = iapp (isnocL η z) r' := (iapp_isnocL z r' η).symm
    rw [e]
    refine ih r' (tl_lt_tcCons z r') hr'0 hr' (fun j hj δ hδ =>
      hEr j hj δ ((iinE_cons_iff _ _ _ _).mpr (Or.inr hδ)))
      (fun y hy hle => hJy y hy ?_) (isnocL η z) hsn (by rw [← e]; exact hηr) h1
    simp only [tcHd_tcCons]
    exact ile_trans (isTerm_of_fldW hy.1) (isTerm_of_fldW (fldW_tcHd hr' hr'0))
      (isTerm_of_fldW hz) hle (hdesc.resolve_left hr'0)

/-- J1b. **The jump is progressive** (Gentzen's Lemma B; IDn `jump_prog`, with `hl_app`). -/
theorem jump_prog {B F : N → Prop} (hB : 𝚺₁.DefinablePred B) (hF : LXJ.DefinablePred F)
    (hP : ProgW (ClsW B) F) : ProgW (ClsW B) (JFW B F) := by
  intro y hy ih η hη _ hHL ξ hξ hlt
  have hSLξ : isSL (expList ξ) := isSL_expList hξ.1.1 hξ.1.2
  rcases iltb_isnocL_cases hη hSLξ hlt with h | h | ⟨r, hr, hr0, hry⟩
  · exact hHL ξ hξ h
  · exact holds_of_hl hP hξ (by rw [h]; exact hHL)
  · refine holds_of_hl hP hξ ?_
    have hSL : isSL (iapp η r) := by rw [← hr]; exact hSLξ
    have hr' : isSL r := isSL_of_isSL_iapp_right r η hSL
    rw [hr]
    refine hl_app M hB hF r hr0 hr' (fun j hj δ hδ => ?_)
      (fun y' hy' hle => ih y' hy' ?_) η hη hSL hHL
    · have := iinE_iapp_right j δ r η hδ
      rw [← hr, iinE_expList] at this
      exact hξ.2 j hj δ this
    · exact iltb_of_le_of_lt (isTerm_of_fldW hy'.1) (isTerm_of_fldW (fldW_tcHd hr' hr0))
        (isTerm_of_fldW hy.1) hle hry

/-! ### J1c. Using the jump -/

/-- J1c. **Using the jump** (IDn `holds_of_jump`). -/
theorem holds_of_jump {B F : N → Prop} (hB : 𝚺₁.DefinablePred B) (hF : LXJ.DefinablePred F)
    (hP : ProgW (ClsW B) F) {ξ : N} (hξ : ClsW B ξ)
    (hJ : ∀ y, ClsW B y → (iltb y (tcHd (expList ξ)) = 1 ∨ y = tcHd (expList ξ)) → JFW B F y) :
    F ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ0
  · exact hP 0 hξ fun _ _ h => absurd h (not_iltb_zero_right _)
  · refine holds_of_hl hP hξ ?_
    have hSL := isSL_expList hξ.1.1 hξ.1.2
    have := hl_app M hB hF (expList ξ) (expList_ne_zero hξ0) hSL
      (fun j hj δ hδ => hξ.2 j hj δ ((iinE_expList _ _ _).mp hδ)) hJ 0 isSL_zero
      (by rw [iapp_zero_left]; exact hSL) hlW_zero
    rwa [iapp_zero_left] at this

/-! ### L1. BP78 Lemma 1 (sums) -/

/-- L1. **A normal sum of `D_k` below `Ω_{k+1}` is in `J(k, ·)` once its first entry is**
(IDn `W_cons`: the jump with `B := (· < k)`, `F := (· ≺ Ω_{k+1} → J(k, ·))`, the jump
progressive by the induction scheme of level `k`). -/
theorem W_cons : ConsStmt N := by
  intro k z w hD hz hB
  have hBd : 𝚺₁.DefinablePred fun j : N => j < k := by definability
  have hF : LXJ.DefinablePred fun ξ : N => iltb ξ (tcOmega k) = 1 → Jm k ξ :=
    Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by definability))
      (dfn_Jm M (a := fun _ => k) (b := fun u => u 0) (by definability) (by definability))
  have hP : ProgW (ClsW fun j : N => j < k) fun ξ : N => iltb ξ (tcOmega k) = 1 → Jm k ξ := by
    intro ξ hξ ih hBξ
    refine M.closure k ξ ⟨hξ, hBξ, fun y hy hyξ => ih y hy hyξ ?_⟩
    exact iltb_trans (isTerm_of_fldW hy.1) (isTerm_of_fldW hξ.1) (isTerm_tcOmega k) hyξ hBξ
  have hJy : ∀ y, Jm k y → DkW k y → JFW (fun j : N => j < k)
      (fun ξ : N => iltb ξ (tcOmega k) = 1 → Jm k ξ) y := by
    have hQ : LXJ.DefinablePred fun y : N => DkW k y → JFW (fun j : N => j < k)
        (fun ξ : N => iltb ξ (tcOmega k) = 1 → Jm k ξ) y :=
      Language.Definable.imp (dfn_pred (dfn_DkW M k) 0) (dfn_pred (dfn_JFW M hBd hF) 0)
    intro y hy
    refine M.ind k hQ (fun y hA hyD => ?_) y hy
    obtain ⟨-, -, IH⟩ := hA
    exact jump_prog M hBd hF hP y hyD fun y' hy' hlt => IH y' hy' hlt hy'
  refine holds_of_jump M hBd hF hP hD (fun y hy hle => ?_) hB
  rw [expList_tcCons, tcHd_tcCons] at hle
  exact hJy y (W_down_le M hz hy hle) hy

/-! ### The main lemmas with the jump hypothesis discharged -/

/-- **BP78 Lemma 3** (with the lower levels), `ConsStmt` discharged. -/
theorem W_of_E' : ∀ k y : N, DkW k y → iltb y (tcOmega k) = 1 →
    (∀ g, iinE k g y = 1 → Jm k g) → Jm k y :=
  W_of_E M (W_cons M)

/-- **BP78 Lemma 3**: `Ω_{j+1} ∈ J(k, ·)` for `j < k`. -/
theorem W_Omega' : OmegaStmt N := W_Omega M (W_cons M)

/-- **The main lemma (BP78 (11)), simultaneously in the internal level `k`**, with
`ConsStmt`, `MonoStmt`, `OmegaStmt` discharged. -/
theorem W_theta' {x : N} (hx : fldW x) (hM : MallW x) (H : HypW x) (k : N)
    (hk : fldW (tcTheta k x)) : Jm k (tcTheta k x) :=
  W_theta M (W_mono M) (W_cons M) (W_Omega' M) hx hM H k hk

/-- **BP78 (11)** as `Prog[M, ThetaIn]`, `ConsStmt` discharged. -/
theorem prog_thetaIn' : ProgW MMW (ThetaIn (s := s)) := prog_thetaIn M (W_cons M)

/-- **BP78 Theorem 2** (collapsing), at every level, `ConsStmt` discharged. -/
theorem W_theta_of_TI' {c : N} (hTI : TIW MMW c) (hc : MMW c) (k : N)
    (hf : fldW (tcTheta k c)) : Jm k (tcTheta k c) :=
  W_theta_of_TI M (W_cons M) hTI hc k hf

end Jump

end OrdinalAnalysis.IDw.Upper
