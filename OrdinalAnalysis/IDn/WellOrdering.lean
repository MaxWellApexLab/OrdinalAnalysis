/-
  The well-ordering proof for the multi-level ϑ-notation inside models of `ID_n`: the level
  tower, with the ranges repaired.

  Sources: T. Arai, *Lectures on ordinal analysis*, arXiv:2304.00246, §1.6 (Definition 1.27,
  Lemmas 1.29, 1.31–1.33: distinguished classes, Gentzen's jump, the main lemma), one level at a
  time as in the metatheoretic proof `Ordinal/ThetaW/WellFoundedD.lean` (`HLow`, `acc_of_lt_Omega`,
  `acc_of_lt_theta`, `cls_succ_of_cls`), with Gentzen's jump at the top level in place of the
  length induction of `result_top`; the one-level version is `ID1/WellOrdering.lean`.

  **Setting.**  `N` is an arithmetically standard model of `ID A` over `LXIN ι`, where the
  levels `0, …, n` are read through an index map `ix : ℕ → ι` injective on them, and
  `A (ix k) = wForm hJ.toOrderFormulas ix k` for `k ≤ n` (`Good`).  `W k` is the extension of `I_(ix k)`; `Dc k`
  is the distinguished class `D_k` of `UpperAuxForms` (`fld x ∧ E_j(x) ⊆ W j` for `j < k`), so
  that `W 0` is the accessible part of `≺` on the field and `W (k+1)` the accessible part of `≺`
  restricted to `Dc (k+1)` below `Ω_{k+2}` (`W_closure`, `W_induction`).

  * **Gentzen's jump** on the class `Dc k` (`jump_prog`, `holds_of_jump`, `hl_app`: the ID₁
    jump over exponent lists, the class read through its coefficient condition).
  * **Sums** (`W_cons`): a normal sum of `Dc k` is in `W k` once its first exponent is.
  * **Below `Ω_k`** (`HLow`, bottom-up, Arai 1.29 per level): `Dc k ∩ Ω_k ⊆ W k`
    (`acc_of_lt_Omega`: `Dc (k+1) ∩ Ω_{k+1} ⊆ W k`; `W_mono`: `W k ∩ Dc (k+1) ⊆ W (k+1)`).
  * **The main lemma** (`W_theta`, Arai 1.33 for `ϑ_k`), relative to a bound `τ`.
  * **The tower at the top level `n`** (`ti_tau`): transfinite induction on `Dc (n+1)` up to
    every `τ_m = ω_m(Ω_{n+1} + 1)`, for every definable predicate.
  * **The ranges** (the repair of design §3.1 (E_k)): `C k ξ :≡ ξ ∈ Dc (k+1) ∧ G_k(ξ) ≺* τ`.
    Design §3.1's "`D_{k−1} = D_k` below `ω_m(Ω_n+1)`" fails on `ϑ_1(Ω_7) ≺ Ω_2` (level-1
    coefficient needs induction up to `Ω_7`); on the ranges it holds (`cls_succ`): the level-`k`
    coefficients `ϑ_k d` of `ξ ∈ C (k−1)` have `d ∈ G_{k−1}(ξ)`, hence `d ≺ τ`, and
    `G_{k−1}(d) ⊆ G_{k−1}(ξ)`.  Transfinite induction on `C k` below `τ` passes from level
    `k+1` to level `k` (`tiC_of_succ`), and gives `ϑ_k(ξ) ∈ W k` on `C k` below `τ`
    (`W_theta_C`).
  * At level `0` and `α = τ`: **`ϑ₀(τ_m) ∈ W 0`** for every standard `m` (`W_theta_tau`).
-/
import OrdinalAnalysis.IDn.UpperAuxForms

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OrdinalAnalysis.IDn.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.IDn.Internal OrdinalAnalysis.IDn.Lift InternalOrderFacts

/-! ### Definability in `LXIN ι` -/

section Definability

variable {ι : Type} {N : Type} [ORingStructure N] [Structure (LXIN ι) N] [ArithStd ι N]

theorem dfn_all {k : ℕ} {R : (Fin (k + 1) → N) → Prop} (h : (LXIN ι).Definable R) :
    (LXIN ι).Definable fun v : Fin k → N => ∀ x, R (x :> v) := by
  refine Language.Definable.all ?_
  refine Language.Definable.of_iff h fun w => ?_
  rw [show (w 0 :> fun x => w x.succ) = w from Matrix.cons_head_tail w]

theorem dfn_pred {k : ℕ} {Q : N → Prop} (hQ : (LXIN ι).DefinablePred Q) (i : Fin k) :
    (LXIN ι).Definable fun v : Fin k → N => Q (v i) :=
  Language.Definable.of_iff (hQ.retraction ![i]) fun v => by simp

theorem dfn_comp {k : ℕ} {Q : N → Prop} (hQ : (LXIN ι).DefinablePred Q)
    {f : (Fin k → N) → N} (hf : 𝚺₁.DefinableFunction f) :
    (LXIN ι).Definable fun v : Fin k → N => Q (f v) :=
  @Language.DefinablePred.comp (LXIN ι) N _ Q k f hQ (definable_of_arith hf)

theorem dfn_sigma {k : ℕ} {R : (Fin k → N) → Prop} (h : 𝚺₁.Definable R) :
    (LXIN ι).Definable R :=
  definable_of_arith h

end Definability

/-! ### The setting -/

/-- The levels `0, …, n` are read through `ix`, injectively, with the well-ordering forms. -/
structure Good (hJ : InternalOrderFacts) {ι : Type} (ix : ℕ → ι) (n : ℕ)
    (A : ι → Semisentence (LXIN ι) 1) : Prop where
  inj : ∀ i j, i ≤ n → j ≤ n → ix i = ix j → i = j
  form : ∀ k, k ≤ n → A (ix k) = wForm hJ.toOrderFormulas ix k

section Model

variable {hJ : InternalOrderFacts} {ι : Type} [DecidableEq ι] {ix : ℕ → ι} {n : ℕ}
  {A : ι → Semisentence (LXIN ι) 1}
  {N : Type} [ORingStructure N] [s : Structure (LXIN ι) N] [ArithStd ι N]
  [hM : N↓[LXIN ι] ⊧* ID A] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable (ix) in
/-- `W k`: the extension of the predicate of level `k`. -/
def W (k : ℕ) (x : N) : Prop := Imem (s := s) (ix k) x

variable (hJ ix) in
/-- The distinguished class `D_k` in `N`. -/
def Dc (k : ℕ) (x : N) : Prop := DcS hJ.toOrderFormulas ix s k x

variable (hJ) in
/-- The bound of level `k`: none at level `0`, `x ≺ Ω_{k+1}` at level `k ≥ 1`. -/
def Bd : ℕ → N → Prop
  | 0, _ => True
  | k + 1, x => hJ.lt x (tcOmega ((k + 1 : ℕ) : N))

theorem dc_zero_iff {x : N} : Dc hJ ix 0 x ↔ hJ.fld x := Iff.rfl

theorem dc_succ_iff {k : ℕ} {x : N} :
    Dc hJ ix (k + 1) x ↔ Dc hJ ix k x ∧ ∀ δ, iinE (k : N) δ x = 1 → W ix k δ := Iff.rfl

theorem Dc.fld : ∀ {k : ℕ} {x : N}, Dc hJ ix k x → hJ.fld x
  | 0, _, h => h
  | _ + 1, _, h => Dc.fld (dc_succ_iff.mp h).1

theorem Dc.mono : ∀ {j k : ℕ} {x : N}, j ≤ k → Dc hJ ix k x → Dc hJ ix j x
  | j, 0, x, hjk, h => by obtain rfl : j = 0 := by omega
                          exact h
  | j, k + 1, x, hjk, h => by
    rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · exact Dc.mono (by omega) (dc_succ_iff.mp h).1
    · obtain rfl : j = k + 1 := by omega
      exact h

/-- `Dc k` through its coefficients. -/
theorem dc_iff : ∀ {k : ℕ} {x : N},
    Dc hJ ix k x ↔ hJ.fld x ∧ ∀ i < k, ∀ δ, iinE (i : N) δ x = 1 → W ix i δ
  | 0, x => by simp [dc_zero_iff]
  | k + 1, x => by
    rw [dc_succ_iff, dc_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun i hi δ hδ => ?_⟩
      rcases Nat.lt_or_ge i k with h | h
      · exact h2 i h δ hδ
      · obtain rfl : i = k := by omega
        exact h3 δ hδ
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun i hi => h2 i (by omega)⟩, h2 k (by omega)⟩

/-- A code with the coefficients of `x` (of every level below `k`) and in the field is in
`Dc k` when `x` is. -/
theorem Dc.of_sub {k : ℕ} {x y : N} (hx : Dc hJ ix k x) (hy : hJ.fld y)
    (hsub : ∀ i < k, ∀ δ, iinE (i : N) δ y = 1 → iinE (i : N) δ x = 1) : Dc hJ ix k y := by
  rw [dc_iff] at hx ⊢
  exact ⟨hy, fun i hi δ hδ => hx.2 i hi δ (hsub i hi δ hδ)⟩

/-- The coefficients of every level `j` of a coefficient `g ∈ E_i(x)` (`j ≤ i`) are
coefficients of `x`. -/
theorem Dc.of_iinE {k : ℕ} {x g : N} {i : ℕ} (hx : Dc hJ ix k x) (hki : k ≤ i + 1)
    (hg : iinE (i : N) g x = 1) : Dc hJ ix k g :=
  Dc.of_sub hx (fld_of_iinE hx.fld hg) fun j hj δ hδ =>
    iinE_trans (by exact_mod_cast (show j ≤ i by omega)) x g δ hg hδ

/-- An entry of a normal sum in `Dc k` is in `Dc k`. -/
theorem Dc.hd {k : ℕ} {x w : N} (h : Dc hJ ix k (tcCons x w)) : Dc hJ ix k x :=
  Dc.of_sub h (fld_hd h.fld) fun _ _ δ hδ => (iinE_tcCons_iff _ δ x w).mpr (Or.inl hδ)

/-- The argument of a collapse of level `≥ k` in `Dc k` is in `Dc k`. -/
theorem Dc.theta_arg {k j : ℕ} {x : N} (hj : k ≤ j) (h : Dc hJ ix k (tcTheta (j : N) x)) :
    Dc hJ ix k x :=
  Dc.of_sub h ((fld_theta_iff _ x).mp h.fld).1 fun i hi δ hδ => by
    rw [iinE_tcTheta_of_lt (by exact_mod_cast (show i < j by omega))]
    exact hδ

/-! ### The axioms of the levels -/

/-- The coefficient condition of `Dc k`, for any code (in particular a list). -/
def Ecl (k : ℕ) (x : N) : Prop := ∀ i < k, ∀ δ, iinE (i : N) δ x = 1 → W ix i δ

theorem dc_iff_ecl {k : ℕ} {x : N} : Dc hJ ix k x ↔ hJ.fld x ∧ Ecl (ix := ix) k x := dc_iff

theorem definable_W (k : ℕ) : (LXIN ι).DefinablePred (W (s := s) ix k) := definable_imem (ix k)

theorem definable_Dc : ∀ k : ℕ, (LXIN ι).DefinablePred (Dc (s := s) hJ ix k)
  | 0 => by
    have : 𝚺₁.Definable fun v : Fin 1 → N => hJ.fld (v 0) := by definability
    exact Language.Definable.of_iff (dfn_sigma this) fun v => Iff.rfl
  | k + 1 => by
    have h1 := dfn_all (k := 1)
      (R := fun w : Fin 2 → N => iinE (k : N) (w 0) (w 1) = 1 → W ix k (w 0))
      (Language.Definable.imp (dfn_sigma (by definability)) (dfn_pred (definable_W k) 0))
    exact Language.Definable.of_iff (Language.Definable.and (definable_Dc k) h1)
      fun v => Iff.rfl

theorem definable_Ecl (k : ℕ) : (LXIN ι).DefinablePred (Ecl (s := s) (ix := ix) k) := by
  have : ∀ k : ℕ, (LXIN ι).DefinablePred fun x : N =>
      ∀ i < k, ∀ δ, iinE (i : N) δ x = 1 → W ix i δ := by
    intro k
    induction k with
    | zero => exact Language.Definable.of_iff (Language.Definable.const True) fun v => by simp
    | succ k ih =>
      have h1 := dfn_all (k := 1)
        (R := fun w : Fin 2 → N => iinE (k : N) (w 0) (w 1) = 1 → W ix k (w 0))
        (Language.Definable.imp (dfn_sigma (by definability)) (dfn_pred (definable_W k) 0))
      refine Language.Definable.of_iff (Language.Definable.and ih h1) fun v => ?_
      constructor
      · intro h
        refine ⟨fun i hi => h i (by omega), h k (by omega)⟩
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_or_ge i k with h | h
        · exact h1 i h
        · obtain rfl : i = k := by omega
          exact h2
  exact this k

/-- `D_j` read with `I_(ix k)` replaced by `T` is `D_j`, for `j ≤ k` (the levels `< j` are not
`k`). -/
theorem dcS_withIAt {k : ℕ} (hne : ∀ i < k, ix i ≠ ix k) (T : N → Prop) :
    ∀ j, j ≤ k → ∀ x, (DcS hJ.toOrderFormulas ix (withIAt (ix k) T) j x ↔ Dc hJ ix j x)
  | 0, _, x => Iff.rfl
  | j + 1, hj, x => by
    show (DcS hJ.toOrderFormulas ix (withIAt (ix k) T) j x ∧ ∀ δ, iinE (j : N) δ x = 1 →
        relI (withIAt (ix k) T) (ix j) δ) ↔ Dc hJ ix (j + 1) x
    rw [dc_succ_iff, dcS_withIAt hne T j (by omega) x]
    refine and_congr Iff.rfl (forall_congr' fun δ => imp_congr Iff.rfl ?_)
    exact withIAt_rel_I_ne (hne j (by omega)) T δ

theorem dc_zero_code (k : ℕ) : Dc hJ ix k (0 : N) :=
  dc_iff.mpr ⟨fld_zero, fun _ _ δ h => by rw [iinE_zero] at h; simp at h⟩

theorem bd_zero (k : ℕ) : Bd hJ k (0 : N) := by
  cases k with
  | zero => trivial
  | succ k => exact zero_lt_Omega (k + 1)

section Axioms

variable (hG : Good hJ ix n A)
include hG

/-- **Closure** of level `k`. -/
theorem W_closure {k : ℕ} (hk : k ≤ n) {x : N} (hD : Dc hJ ix k x) (hB : Bd hJ k x)
    (h : ∀ y, Dc hJ ix k y → hJ.lt y x → W ix k y) : W ix k x := by
  apply imem_of_form A (ix k) x
  rw [hG.form k hk]
  cases k with
  | zero =>
    rw [eval_wForm_zero hJ.toOrderFormulas ix s (ArithStd.lMap_eq (ι := ι) (N := N))]
    intro y hy _ hlt
    exact h y hy hlt
  | succ k =>
    rw [eval_wForm_succ hJ.toOrderFormulas ix s (ArithStd.lMap_eq (ι := ι) (N := N))]
    exact ⟨hD, hB, fun y hy hlt => h y hy hlt⟩

/-- **The induction scheme** of level `k`, for definable predicates. -/
theorem W_induction {k : ℕ} (hk : k ≤ n) {Q : N → Prop} (hQ : (LXIN ι).DefinablePred Q)
    (h : ∀ x, Dc hJ ix k x → Bd hJ k x → (∀ y, Dc hJ ix k y → hJ.lt y x → Q y) → Q x) :
    ∀ x, W ix k x → Dc hJ ix k x → Q x := by
  have hQ' : (LXIN ι).DefinablePred fun x : N => Dc hJ ix k x → Q x :=
    Language.Definable.imp (dfn_pred (definable_Dc k) 0) (dfn_pred hQ 0)
  intro x hx
  refine ind_definable A (ix k) hQ' (fun x hA' => ?_) x hx
  rw [hG.form k hk] at hA'
  have hS : (withIAt (ix k) fun x : N => Dc hJ ix k x → Q x).lMap (toLXIN ι) =
      Arithmetic.standardModel N :=
    (lMap_withIAt _ _).trans (ArithStd.lMap_eq (ι := ι) (N := N))
  cases k with
  | zero =>
    rw [eval_wForm_zero hJ.toOrderFormulas ix _ hS] at hA'
    intro hD
    refine h x hD trivial fun y hy hlt => ?_
    exact (withIAt_rel_I_self (ix 0) _ y).mp (hA' y hy hD hlt) hy
  | succ k =>
    rw [eval_wForm_succ hJ.toOrderFormulas ix _ hS] at hA'
    obtain ⟨-, hB, hIH⟩ := hA'
    intro hD
    have hne : ∀ i < k + 1, ix i ≠ ix (k + 1) := fun i hi e => by
      have := hG.inj i (k + 1) (by omega) hk e; omega
    refine h x hD hB fun y hy hlt => ?_
    exact (withIAt_rel_I_self (ix (k + 1)) _ y).mp
      (hIH y ((dcS_withIAt hne _ (k + 1) le_rfl y).mpr hy) hlt) hy

theorem bd_of_lt {k : ℕ} {x y : N} (hx : hJ.fld x) (hy : hJ.fld y) (hB : Bd hJ k x)
    (hlt : hJ.lt y x) : Bd hJ k y := by
  cases k with
  | zero => trivial
  | succ k => exact lt_trans hy hx (fld_Omega (k + 1)) hlt hB

/-- **`W k` is downward closed** in `Dc k`. -/
theorem W_down {k : ℕ} (hk : k ≤ n) {x y : N} (hx : W ix k x) (hxD : Dc hJ ix k x)
    (hyD : Dc hJ ix k y) (hlt : hJ.lt y x) : W ix k y := by
  have hQ : (LXIN ι).DefinablePred fun x : N => ∀ y, Dc hJ ix k y → hJ.lt y x → W ix k y :=
    dfn_all (k := 1) (R := fun w : Fin 2 → N => Dc hJ ix k (w 0) → hJ.lt (w 0) (w 1) → W ix k (w 0))
      (Language.Definable.imp (dfn_pred (definable_Dc k) 0)
        (Language.Definable.imp (dfn_sigma (by definability)) (dfn_pred (definable_W k) 0)))
  refine W_induction hG hk hQ (fun x hD hB IH y hy hlt => ?_) x hx hxD y hyD hlt
  exact W_closure hG hk hy (bd_of_lt hG hD.fld hy.fld hB hlt)
    fun z hz hzy => IH y hy hlt z hz hzy

theorem W_down_le {k : ℕ} (hk : k ≤ n) {x y : N} (hx : W ix k x) (hxD : Dc hJ ix k x)
    (hyD : Dc hJ ix k y) (hle : hJ.le y x) : W ix k y := by
  rcases hle with h | rfl
  · exact W_down hG hk hx hxD hyD h
  · exact hx

theorem W_zero {k : ℕ} (hk : k ≤ n) : W ix k (0 : N) :=
  W_closure hG hk (dc_zero_code (ix := ix) k) (bd_zero k) fun y _ h => absurd h (hJ.ax.not_lt_zero y)

end Axioms

/-! ### Gentzen's jump on the class `Dc k` -/

section Jump

variable (hJ) in
/-- `η ++ ⟨y⟩`. -/
noncomputable def isnoc (η y : N) : N := hJ.app η (tcCons y 0)

theorem fld_tcHd {r : N} (hr : hJ.sl r) (hr0 : r ≠ 0) : hJ.fld (tcHd r) := by
  obtain ⟨z, w, rfl⟩ := sl_eq_cons hr hr0
  rw [tcHd_tcCons]
  exact ((sl_cons_iff z w).mp hr).1

variable (k : ℕ) (F : N → Prop)

variable (hJ ix) in
/-- `HL(η)`: `F` holds on every element of `Dc k` whose exponent list is below `η`. -/
def HL (η : N) : Prop := ∀ ξ, Dc hJ ix k ξ → hJ.lt (itoL ξ) η → F ξ

variable (hJ ix) in
/-- **The jump** `J(y)`: appending the exponent `y` to a list keeps `HL`. -/
def JF (y : N) : Prop :=
  ∀ η, hJ.sl η → hJ.sl (isnoc hJ η y) → HL hJ ix k F η → HL hJ ix k F (isnoc hJ η y)

variable (hJ ix) in
/-- `F` is progressive on `Dc k`. -/
def ProgD : Prop := ∀ ξ, Dc hJ ix k ξ → (∀ ξ', Dc hJ ix k ξ' → hJ.lt ξ' ξ → F ξ') → F ξ

variable {k F}

theorem holds_of_hl (hP : ProgD hJ ix k F) {ξ : N} (hξ : Dc hJ ix k ξ)
    (h : HL hJ ix k F (itoL ξ)) : F ξ :=
  hP ξ hξ fun ξ' hξ' hlt => h ξ' hξ'
    ((hJ.ax.lt_itoL_iff ξ' ξ hξ'.fld.1 hξ'.fld.2 hξ.fld.1 hξ.fld.2).mpr hlt)

theorem hl_zero : HL hJ ix k F (0 : N) := fun _ _ h => absurd h (hJ.ax.not_lt_zero _)

theorem dfn_HL (hF : (LXIN ι).DefinablePred F) :
    (LXIN ι).DefinablePred (HL (s := s) hJ ix k F) := by
  have h := dfn_all (k := 1)
    (R := fun w : Fin 2 → N => Dc hJ ix k (w 0) → hJ.lt (itoL (w 0)) (w 1) → F (w 0))
    (Language.Definable.imp (dfn_pred (definable_Dc k) 0)
      (Language.Definable.imp (dfn_sigma (by definability)) (dfn_pred hF 0)))
  exact Language.Definable.of_iff h fun v => Iff.rfl

theorem dfn_JF (hF : (LXIN ι).DefinablePred F) :
    (LXIN ι).DefinablePred (JF (s := s) hJ ix k F) := by
  have hi : 𝚺₁.DefinableFunction fun w : Fin 2 → N => isnoc hJ (w 0) (w 1) := by
    unfold isnoc; definability
  have h := dfn_all (k := 1)
    (R := fun w : Fin 2 → N => hJ.sl (w 0) → hJ.sl (isnoc hJ (w 0) (w 1)) →
      HL hJ ix k F (w 0) → HL hJ ix k F (isnoc hJ (w 0) (w 1)))
    (Language.Definable.imp (dfn_sigma (by definability))
      (Language.Definable.imp (dfn_comp (Q := hJ.sl) (dfn_sigma (by definability)) hi)
        (Language.Definable.imp (dfn_pred (dfn_HL hF) 0) (dfn_comp (dfn_HL hF) hi))))
  exact Language.Definable.of_iff h fun v => Iff.rfl

theorem dfn_hl_app (hF : (LXIN ι).DefinablePred F) :
    (LXIN ι).DefinablePred fun r : N => r ≠ 0 → hJ.sl r → Ecl (ix := ix) k r →
      (∀ y, Dc hJ ix k y → hJ.le y (tcHd r) → JF hJ ix k F y) →
      ∀ η, hJ.sl η → hJ.sl (hJ.app η r) → HL hJ ix k F η → HL hJ ix k F (hJ.app η r) := by
  have h2 := dfn_all (k := 1)
    (R := fun w : Fin 2 → N => Dc hJ ix k (w 0) → hJ.le (w 0) (tcHd (w 1)) → JF hJ ix k F (w 0))
    (Language.Definable.imp (dfn_pred (definable_Dc k) 0)
      (Language.Definable.imp (dfn_sigma (by definability)) (dfn_pred (dfn_JF hF) 0)))
  have hf : 𝚺₁.DefinableFunction fun w : Fin 2 → N => hJ.app (w 0) (w 1) := by definability
  have h3 := dfn_all (k := 1)
    (R := fun w : Fin 2 → N => hJ.sl (w 0) → hJ.sl (hJ.app (w 0) (w 1)) → HL hJ ix k F (w 0) →
      HL hJ ix k F (hJ.app (w 0) (w 1)))
    (Language.Definable.imp (dfn_sigma (by definability))
      (Language.Definable.imp (dfn_comp (Q := hJ.sl) (dfn_sigma (by definability)) hf)
        (Language.Definable.imp (dfn_pred (dfn_HL hF) 0) (dfn_comp (dfn_HL hF) hf))))
  refine Language.Definable.imp ?_ (Language.Definable.imp ?_
    (Language.Definable.imp (dfn_pred (definable_Ecl k) 0) (Language.Definable.imp ?_ ?_)))
  · exact dfn_sigma (by definability)
  · exact dfn_sigma (by definability)
  · exact Language.Definable.of_iff h2 fun v => by simp
  · exact Language.Definable.of_iff h3 fun v => by simp

include hM in
/-- **Iterating the jump along a list** (the finite iteration in Gentzen's Lemma B). -/
theorem hl_app (hF : (LXIN ι).DefinablePred F) :
    ∀ r : N, r ≠ 0 → hJ.sl r → Ecl (ix := ix) k r →
      (∀ y, Dc hJ ix k y → hJ.le y (tcHd r) → JF hJ ix k F y) →
      ∀ η, hJ.sl η → hJ.sl (hJ.app η r) → HL hJ ix k F η → HL hJ ix k F (hJ.app η r) := by
  refine order_induction_definable A (dfn_hl_app hF) ?_
  intro r ih hr0 hr hEr hJy η hη hηr hHL
  obtain ⟨z, r', rfl⟩ := sl_eq_cons hr hr0
  obtain ⟨hz, hr', hdesc⟩ := (sl_cons_iff z r').mp hr
  have hzD : Dc hJ ix k z := dc_iff.mpr ⟨hz, fun i hi δ hδ =>
    hEr i hi δ ((iinE_tcCons_iff _ _ _ _).mpr (Or.inl hδ))⟩
  have hJz : JF hJ ix k F z := hJy z hzD (Or.inr (tcHd_tcCons z r').symm)
  have hsn : hJ.sl (isnoc hJ η z) := hJ.ax.sl_isnoc_of_app η z r' hηr
  have h1 : HL hJ ix k F (isnoc hJ η z) := hJz η hη hsn hHL
  rcases eq_or_ne r' 0 with rfl | hr'0
  · exact h1
  · have e : hJ.app η (tcCons z r') = hJ.app (isnoc hJ η z) r' := (hJ.ax.app_isnoc η z r' hη).symm
    rw [e]
    refine ih r' (tl_lt_tcCons z r') hr'0 hr'
      (fun i hi δ hδ => hEr i hi δ ((iinE_tcCons_iff _ _ _ _).mpr (Or.inr hδ)))
      (fun y hy hle => hJy y hy ?_) (isnoc hJ η z) hsn (by rw [← e]; exact hηr) h1
    rw [tcHd_tcCons]
    exact le_trans hy.fld (fld_tcHd hr' hr'0) hz hle (hdesc.resolve_left hr'0)

include hM in
/-- **The jump is progressive** (Gentzen's Lemma B; Arai, Lemma 1.31). -/
theorem jump_prog (hF : (LXIN ι).DefinablePred F) (hP : ProgD hJ ix k F) :
    ∀ y, Dc hJ ix k y → (∀ y', Dc hJ ix k y' → hJ.lt y' y → JF hJ ix k F y') →
      JF hJ ix k F y := by
  intro y hy ih η hη _ hHL ξ hξ hlt
  rcases hJ.ax.lt_isnoc_cases η y (itoL ξ) hη (sl_itoL hξ.fld) hlt with h | h | ⟨r, hr, hr0, hry⟩
  · exact hHL ξ hξ h
  · exact holds_of_hl hP hξ (by rw [h]; exact hHL)
  · refine holds_of_hl hP hξ ?_
    have hSL : hJ.sl (hJ.app η r) := hr ▸ sl_itoL hξ.fld
    have hr' : hJ.sl r := hJ.ax.sl_app_right η r hSL
    rw [hr]
    refine hl_app (A := A) hF r hr0 hr' (fun i hi δ hδ => ?_)
      (fun y' hy' hle => ih y' hy' (lt_of_le_of_lt hy'.fld (fld_tcHd hr' hr0) hy.fld hle hry))
      η hη hSL hHL
    have := hJ.ax.iinE_app_right (i : N) δ η r hη hδ
    rw [← hr, iinE_itoL] at this
    exact (dc_iff.mp hξ).2 i hi δ this

include hM in
/-- **Using the jump**: `F ξ` holds as soon as `J` holds at every element of `Dc k` below or
equal to the first exponent of `ξ`. -/
theorem holds_of_jump (hF : (LXIN ι).DefinablePred F) (hP : ProgD hJ ix k F) {ξ : N}
    (hξ : Dc hJ ix k ξ)
    (hJy : ∀ y, Dc hJ ix k y → hJ.le y (tcHd (itoL ξ)) → JF hJ ix k F y) : F ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ0
  · exact hP 0 hξ fun _ _ h => absurd h (hJ.ax.not_lt_zero _)
  · refine holds_of_hl hP hξ ?_
    have hSL := sl_itoL hξ.fld
    have := hl_app (A := A) hF (itoL ξ) (itoL_ne_zero hξ0) hSL
      (fun i hi δ hδ => (dc_iff.mp hξ).2 i hi δ ((iinE_itoL _ _ _).mp hδ)) hJy 0 hJ.ax.sl_zero
      (by rw [hJ.ax.app_zero]; exact hSL) hl_zero
    rwa [hJ.ax.app_zero] at this

end Jump

/-! ### Sums, and the classes below `Ω_k` (Arai, Lemma 1.29, level by level) -/

theorem definable_Bd (k : ℕ) : (LXIN ι).DefinablePred (Bd (N := N) hJ k) := by
  cases k with
  | zero => exact Language.Definable.of_iff (Language.Definable.const True) fun v => Iff.rfl
  | succ k =>
    exact Language.Definable.of_iff (dfn_sigma (k := 1)
      (R := fun v => hJ.lt (v 0) (tcOmega ((k + 1 : ℕ) : N))) (by definability)) fun v => Iff.rfl

theorem lt_Omega_nat {i j : ℕ} (h : i < j) : hJ.lt (tcOmega (i : N)) (tcOmega (j : N)) :=
  (hJ.ax.lt_Omega_Omega _ _).mpr (by exact_mod_cast h)

theorem le_Omega_nat {i j : ℕ} (h : i ≤ j) : hJ.le (tcOmega (i : N)) (tcOmega (j : N)) := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact Or.inl (lt_Omega_nat h)
  · exact Or.inr rfl

theorem dc_Omega (k j : ℕ) : Dc hJ ix k (tcOmega (j : N)) :=
  dc_iff.mpr ⟨fld_Omega j, fun _ _ δ h => by rw [iinE_tcOmega] at h; simp at h⟩

variable (hJ ix) in
/-- `x ≺ Ω_k` (nothing is below `Ω_0 = 0`). -/
def Below : ℕ → N → Prop
  | 0, _ => False
  | k + 1, x => hJ.lt x (tcOmega (k : N))

variable (hJ ix) in
/-- `HLow k`: every element of `Dc k` below `Ω_k` is in `W k`. -/
def HLow (k : ℕ) : Prop := ∀ x : N, Dc hJ ix k x → Below hJ k x → W ix k x

section Levels

variable (hG : Good hJ ix n A)
include hG

/-- **A normal sum in `Dc k` is in `W k` once its first exponent is** (Arai, Lemma 1.29, the
step for sums; Gentzen's jump with `F = W k`). -/
theorem W_cons {k : ℕ} (hk : k ≤ n) {x w : N} (hD : Dc hJ ix k (tcCons x w)) (hx : W ix k x)
    (hB : Bd hJ k (tcCons x w)) : W ix k (tcCons x w) := by
  have hF : (LXIN ι).DefinablePred fun ξ : N => Bd hJ k ξ → W ix k ξ :=
    Language.Definable.imp (dfn_pred (definable_Bd k) 0) (dfn_pred (definable_W k) 0)
  have hP : ProgD hJ ix k fun ξ : N => Bd hJ k ξ → W ix k ξ := fun ξ hξ ih hBξ =>
    W_closure hG hk hξ hBξ fun y hy hlt => ih y hy hlt (bd_of_lt hG hξ.fld hy.fld hBξ hlt)
  have hJy : ∀ y, W ix k y → Dc hJ ix k y → JF hJ ix k (fun ξ : N => Bd hJ k ξ → W ix k ξ) y :=
    W_induction hG hk (dfn_JF hF) fun y hy _ ih => jump_prog (A := A) hF hP y hy ih
  have hxD : Dc hJ ix k x := hD.hd
  refine holds_of_jump (A := A) hF hP hD (fun y hy hle => ?_) hB
  rw [itoL_tcCons, tcHd_tcCons] at hle
  exact hJy y (W_down_le hG hk hx hxD hy hle) hy

/-- `Ω_{j+1} ∈ W k` for `j < k`. -/
theorem W_Omega {k : ℕ} (hk : k ≤ n) (hL : HLow (s := s) hJ ix k) {j : N} (hj : j < (k : N)) :
    W ix k (tcOmega j) := by
  obtain ⟨j, rfl⟩ := eq_nat_of_lt_nat hj
  have hj' : j < k := by exact_mod_cast hj
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine W_closure hG hk (dc_Omega _ j) (lt_Omega_nat hj') fun y hy hlt => hL y hy ?_
  show hJ.lt y (tcOmega (k : N))
  exact lt_of_lt_of_le hy.fld (fld_Omega j) (fld_Omega k) hlt (le_Omega_nat (by omega))

/-- **Arai, Lemma 1.29 at level `k`**: `Dc (k+1) ∩ Ω_{k+1} ⊆ W k`. -/
theorem acc_of_lt_Omega {k : ℕ} (hk : k ≤ n) (hL : HLow (s := s) hJ ix k) :
    ∀ x : N, Dc hJ ix (k + 1) x → hJ.lt x (tcOmega (k : N)) → W ix k x := by
  have hQ : (LXIN ι).DefinablePred fun x : N =>
      Dc hJ ix (k + 1) x → hJ.lt x (tcOmega (k : N)) → W ix k x :=
    Language.Definable.imp (dfn_pred (definable_Dc (k + 1)) 0)
      (Language.Definable.imp (dfn_sigma (k := 1)
        (R := fun v => hJ.lt (v 0) (tcOmega (k : N))) (by definability))
        (dfn_pred (definable_W k) 0))
  refine order_induction_definable A hQ ?_
  intro x ih hD hlt
  rcases nf_cases hD.fld.1 with rfl | h1 | h2 | h3
  · exact W_zero hG hk
  · rw [eq_tcOmega_of_kind h1] at hlt ⊢
    exact W_Omega hG hk hL ((hJ.ax.lt_Omega_Omega _ _).mp hlt)
  · obtain ⟨j, a, rfl⟩ : ∃ j a, x = tcTheta j a := ⟨_, _, eq_tcTheta_of_kind h2⟩
    have hjk := (hJ.ax.lt_theta_Omega _ _ _).mp hlt
    exact (dc_succ_iff.mp hD).2 _ (iinE_tcTheta_self hjk)
  · obtain ⟨z, w, rfl⟩ : ∃ z w, x = tcCons z w := ⟨_, _, eq_tcCons_of_kind h3⟩
    have hz := ih z (hd_lt_tcCons z w) hD.hd ((hJ.ax.lt_cons_Omega _ _ _).mp hlt)
    refine W_cons hG hk (hD.mono (by omega)) hz ?_
    cases k with
    | zero => trivial
    | succ k => exact hlt

/-- `W k ∩ Dc (k+1) ∩ Ω_{k+1} ⊆ W (k+1)`. -/
theorem W_mono {k : ℕ} (hk : k + 1 ≤ n) :
    ∀ x : N, W ix k x → Dc hJ ix k x → Dc hJ ix (k + 1) x → hJ.lt x (tcOmega (k : N)) →
      W ix (k + 1) x := by
  have hQ : (LXIN ι).DefinablePred fun x : N =>
      Dc hJ ix (k + 1) x → hJ.lt x (tcOmega (k : N)) → W ix (k + 1) x :=
    Language.Definable.imp (dfn_pred (definable_Dc (k + 1)) 0)
      (Language.Definable.imp (dfn_sigma (k := 1)
        (R := fun v => hJ.lt (v 0) (tcOmega (k : N))) (by definability))
        (dfn_pred (definable_W (k + 1)) 0))
  refine W_induction hG (by omega) hQ fun x _ _ IH hD1 hlt => ?_
  have hΩ : hJ.lt (tcOmega (k : N)) (tcOmega ((k + 1 : ℕ) : N)) := lt_Omega_nat (by omega)
  refine W_closure hG hk hD1 (lt_trans hD1.fld (fld_Omega k) (fld_Omega (k + 1)) hlt hΩ)
    fun y hy hyx => IH y (hy.mono (by omega)) hyx hy ?_
  exact lt_trans hy.fld hD1.fld (fld_Omega k) hyx hlt

theorem hLow_succ {k : ℕ} (hk : k + 1 ≤ n) (hL : HLow (s := s) hJ ix k) : HLow (s := s) hJ ix (k + 1) :=
  fun x hD hB => W_mono hG hk x (acc_of_lt_Omega hG (by omega) hL x hD hB) (hD.mono (by omega)) hD hB

theorem hLow_all : ∀ k, k ≤ n → HLow (s := s) hJ ix k
  | 0, _ => fun _ _ h => h.elim
  | k + 1, hk => hLow_succ hG hk (hLow_all k (by omega))

end Levels

/-! ### The ranges and the main lemma (Arai, Lemma 1.33, for `ϑ_k`) -/

variable (hJ ix) in
/-- **The range class** of level `k` for the bound `τ`: `Dc (k+1)` with `G_k(ξ) ≺* τ`. -/
def CC (τ : N) (k : ℕ) (ξ : N) : Prop :=
  Dc hJ ix (k + 1) ξ ∧ ∀ y, iinG (k : N) y ξ = 1 → hJ.lt y τ

theorem definable_CC (τ : N) (k : ℕ) : (LXIN ι).DefinablePred (CC (s := s) hJ ix τ k) := by
  have h := dfn_all (ι := ι) (k := 1)
    (R := fun w : Fin 2 → N => iinG (k : N) (w 0) (w 1) = 1 → hJ.lt (w 0) τ)
    (Language.Definable.imp (dfn_sigma (by definability)) (dfn_sigma (by definability)))
  exact Language.Definable.of_iff (Language.Definable.and (definable_Dc (k + 1)) h)
    fun v => Iff.rfl

section Main

variable (hG : Good hJ ix n A)
include hG

/-- **The main lemma** (Arai, Lemma 1.33, for `ϑ_k`): if `α ∈ Dc (k+1)`, `ϑ_k α` is in the
field, `α ≼ τ`, and `ϑ_k ξ ∈ W k` for every `ξ` of the range class below `α` with `ϑ_k ξ` in
the field, then `ϑ_k α ∈ W k`.  Every `γ ∈ Dc k` below `ϑ_k α` is in `W k`, by induction on
its code. -/
theorem W_theta {k : ℕ} (hk : k ≤ n) (hL : HLow (s := s) hJ ix k) {τ : N} (hτ : hJ.fld τ)
    {α : N} (hα : Dc hJ ix (k + 1) α) (hfα : hJ.fld (tcTheta (k : N) α)) (hατ : hJ.le α τ)
    (hyp : ∀ ξ, CC hJ ix τ k ξ → hJ.lt ξ α → hJ.fld (tcTheta (k : N) ξ) →
      W ix k (tcTheta (k : N) ξ)) :
    W ix k (tcTheta (k : N) α) := by
  have hQ : (LXIN ι).DefinablePred fun γ : N =>
      Dc hJ ix k γ → hJ.lt γ (tcTheta (k : N) α) → W ix k γ :=
    Language.Definable.imp (dfn_pred (definable_Dc k) 0)
      (Language.Definable.imp (dfn_sigma (k := 1)
        (R := fun v => hJ.lt (v 0) (tcTheta (k : N) α)) (by definability))
        (dfn_pred (definable_W k) 0))
  have key : ∀ γ : N, Dc hJ ix k γ → hJ.lt γ (tcTheta (k : N) α) → W ix k γ := by
    refine order_induction_definable A hQ ?_
    intro γ ih hγ hlt
    rcases nf_cases hγ.fld.1 with rfl | h1 | h2 | h3
    · exact W_zero hG hk
    · rw [eq_tcOmega_of_kind h1] at hlt ⊢
      exact W_Omega hG hk hL ((hJ.ax.lt_Omega_theta _ _ _).mp hlt)
    · obtain ⟨j, ξ, rfl⟩ : ∃ j ξ, γ = tcTheta j ξ := ⟨_, _, eq_tcTheta_of_kind h2⟩
      rcases lt_trichotomy j (k : N) with hj | rfl | hj
      · obtain ⟨j, rfl⟩ := eq_nat_of_lt_nat hj
        have hj' : j < k := by exact_mod_cast hj
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        exact hL _ hγ ((hJ.ax.lt_theta_Omega _ _ _).mpr (by exact_mod_cast (show j ≤ k' by omega)))
      · rcases (hJ.ax.lt_theta_theta _ _ _ _ ((fld_theta_iff _ ξ).mp hγ.fld).1.1
          hα.fld.1).mp hlt with h | ⟨-, ⟨h1, h2⟩ | ⟨g, hg, hle⟩⟩
        · exact absurd h (_root_.lt_irrefl _)
        · have hξk : Dc hJ ix k ξ := hγ.theta_arg le_rfl
          have hξD : Dc hJ ix (k + 1) ξ := dc_succ_iff.mpr ⟨hξk, fun g hg =>
            ih g (lt_of_le_of_lt (le_of_iinE hg) (arg_lt_tcTheta _ ξ)) (hξk.of_iinE (by omega) hg)
              (h2 g hg)⟩
          have hξτ : hJ.lt ξ τ := lt_of_lt_of_le hξD.fld hα.fld hτ h1 hατ
          refine hyp ξ ⟨hξD, fun y hy => ?_⟩ h1 hγ.fld
          exact lt_trans (fld_of_iinG hξD.fld hy) hξD.fld hτ
            (((fld_theta_iff _ ξ).mp hγ.fld).2 y hy) hξτ
        · have hgD : Dc hJ ix k g := (hα.mono (by omega)).of_iinE (by omega) hg
          exact W_down_le hG hk ((dc_succ_iff.mp hα).2 g hg) hgD hγ hle
      · rcases (hJ.ax.lt_theta_theta _ _ _ _ ((fld_theta_iff _ ξ).mp hγ.fld).1.1
          hα.fld.1).mp hlt with h | ⟨h, -⟩
        · exact absurd (_root_.lt_trans h hj) (_root_.lt_irrefl _)
        · exact absurd h (ne_of_gt hj)
    · obtain ⟨z, w, rfl⟩ : ∃ z w, γ = tcCons z w := ⟨_, _, eq_tcCons_of_kind h3⟩
      have hz := ih z (hd_lt_tcCons z w) hγ.hd ((hJ.ax.lt_cons_theta _ _ _ _).mp hlt)
      refine W_cons hG hk hγ hz ?_
      cases k with
      | zero => trivial
      | succ k =>
        exact lt_trans hγ.fld hfα (fld_Omega (k + 1)) hlt
          ((hJ.ax.lt_theta_Omega _ _ _).mpr le_rfl)
  refine W_closure hG hk ?_ ?_ key
  · exact Dc.of_sub (hα.mono (by omega)) hfα fun i hi δ hδ => by
      rwa [iinE_tcTheta_of_lt (by exact_mod_cast hi)] at hδ
  · cases k with
    | zero => trivial
    | succ k => exact (hJ.ax.lt_theta_Omega _ _ _).mpr le_rfl

end Main

/-! ### The tower at the top level (Arai, Lemmas 1.31, 1.32) -/

variable (hJ ix) in
/-- `TI_{Dc k}(β, F)`: if `F` is progressive on `Dc k`, it holds on `Dc k` below `β`. -/
def TIup (k : ℕ) (β : N) (F : N → Prop) : Prop :=
  ProgD hJ ix k F → ∀ ξ, Dc hJ ix k ξ → hJ.lt ξ β → F ξ

/-- The code of `Ω_{n+1} + 1 = ⟨Ω_{n+1}, 0⟩`. -/
noncomputable def omegaSucc (n : ℕ) : N := tcCons (tcOmega (n : N)) (tcCons 0 0)

/-- The tower `τ_0 = Ω_{n+1} + 1`, `τ_{m+1} = ω^{τ_m}` (codes of `ω_m(Ω_{n+1} + 1)`). -/
noncomputable def tau (n : ℕ) : ℕ → N
  | 0 => omegaSucc n
  | m + 1 => tcCons (tau n m) 0

theorem fld_omegaSucc (n : ℕ) : hJ.fld (omegaSucc n : N) := by
  refine (fld_cons_iff _ _).mpr ⟨(sl_cons_iff _ _).mpr ⟨fld_Omega n, ?_, Or.inr ?_⟩, ?_⟩
  · exact (sl_cons_iff 0 0).mpr ⟨fld_zero, hJ.ax.sl_zero, Or.inl rfl⟩
  · rw [tcHd_tcCons]; exact Or.inl (zero_lt_Omega n)
  · rintro ⟨h, -⟩; exact tcCons_ne_zero 0 0 h

/-- `τ_m` is a normal sum without coefficients and without collapse arguments. -/
theorem tau_facts (n : ℕ) : ∀ m : ℕ, hJ.fld (tau (N := N) n m) ∧ kind (tau (N := N) n m) = 3 ∧
    (∀ j g : N, iinE j g (tau n m) ≠ 1) ∧ (∀ j y : N, iinG j y (tau n m) ≠ 1)
  | 0 => by
    refine ⟨fld_omegaSucc n, kind_tcCons _ _, fun j g hg => ?_, fun j y hy => ?_⟩
    · simp only [tau, omegaSucc, iinE_tcCons_iff, iinE_tcOmega, iinE_zero] at hg; simp at hg
    · simp only [tau, omegaSucc, iinG_tcCons_iff, iinG_tcOmega, iinG_zero] at hy; simp at hy
  | m + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := tau_facts n m
    refine ⟨?_, kind_tcCons _ _, fun j g hg => ?_, fun j y hy => ?_⟩
    · refine (fld_cons_iff _ 0).mpr ⟨(sl_cons_iff _ 0).mpr ⟨h1, hJ.ax.sl_zero, Or.inl rfl⟩, ?_⟩
      rintro ⟨-, hk | hk⟩ <;> rw [h2] at hk <;> simp at hk
    · simp only [tau, iinE_tcCons_iff, iinE_zero] at hg
      exact h3 j g (by simpa using hg)
    · simp only [tau, iinG_tcCons_iff, iinG_zero] at hy
      exact h4 j y (by simpa using hy)

section Tower

variable (hG : Good hJ ix n A)
include hG

/-- **TI on `Dc (n+1)` up to `Ω_{n+1} + 1`**, from the induction scheme of the top level:
below `Ω_{n+1}` the class `Dc (n+1)` lies in `W n` (`acc_of_lt_Omega`). -/
theorem ti_base {F : N → Prop} (hF : (LXIN ι).DefinablePred F) :
    TIup hJ ix (n + 1) (omegaSucc n) F := by
  intro hP ξ hξ hlt
  have below : ∀ ζ, W ix n ζ → Dc hJ ix n ζ → Dc hJ ix (n + 1) ζ → F ζ :=
    W_induction hG le_rfl (Language.Definable.imp (dfn_pred (definable_Dc (n + 1)) 0)
      (dfn_pred hF 0))
      fun ζ _ _ ih hζ1 => hP ζ hζ1 fun ξ' hξ' hlt => ih ξ' (hξ'.mono (by omega)) hlt hξ'
  have lt1 : ∀ ζ, Dc hJ ix (n + 1) ζ → hJ.lt ζ (tcOmega (n : N)) → F ζ := fun ζ hζ h =>
    below ζ (acc_of_lt_Omega hG le_rfl (hLow_all hG n le_rfl) ζ hζ h) (hζ.mono (by omega)) hζ
  rcases lt_Omega_succ_cases hξ.fld hlt with h | rfl
  · exact lt1 ξ hξ h
  · exact hP _ hξ fun ξ' hξ' h => lt1 ξ' hξ' h

/-- **Gentzen's jump on `Dc (n+1)`** (Arai, Lemma 1.31): TI up to a normal sum `β` for every
definable predicate gives TI up to `ω^β = ⟨β⟩` for every definable predicate. -/
theorem ti_jump {β : N} (hβ : hJ.fld β) (hβk : kind β = 3)
    (h : ∀ F : N → Prop, (LXIN ι).DefinablePred F → TIup hJ ix (n + 1) β F) :
    ∀ F : N → Prop, (LXIN ι).DefinablePred F → TIup hJ ix (n + 1) (tcCons β 0) F := by
  intro F hF hP ξ hξ hlt
  have hJ' : ∀ y, Dc hJ ix (n + 1) y → hJ.lt y β → JF hJ ix (n + 1) F y :=
    h (JF hJ ix (n + 1) F) (dfn_JF hF) fun y hy ih => jump_prog (A := A) hF hP y hy ih
  have hβ1 : hJ.fld (tcCons β 0) := by
    refine (fld_cons_iff β 0).mpr ⟨(sl_cons_iff β 0).mpr ⟨hβ, hJ.ax.sl_zero, Or.inl rfl⟩, ?_⟩
    rintro ⟨-, hk | hk⟩ <;> rw [hβk] at hk <;> simp at hk
  have hl : hJ.lt (itoL ξ) (tcCons β 0) := by
    have := (hJ.ax.lt_itoL_iff ξ (tcCons β 0) hξ.fld.1 hξ.fld.2 hβ1.1 hβ1.2).mpr hlt
    rwa [itoL_tcCons] at this
  have hsl := sl_itoL hξ.fld
  rcases lt_single_cases hsl hl with h0 | ⟨z, w, hzw, hz⟩
  · have hξ0 : ξ = 0 := by
      by_contra hne
      exact itoL_ne_zero hne h0
    subst hξ0
    exact hP 0 hξ fun _ _ h => absurd h (hJ.ax.not_lt_zero _)
  · refine holds_of_jump (A := A) hF hP hξ fun y hy hle => hJ' y hy ?_
    rw [hzw, tcHd_tcCons] at hle
    rw [hzw] at hsl
    exact lt_of_le_of_lt hy.fld ((sl_cons_iff z w).mp hsl).1 hβ hle hz

/-- **TI on `Dc (n+1)` up to every `τ_m`** (Arai, Lemma 1.32), for every definable
predicate. -/
theorem ti_tau : ∀ m : ℕ, ∀ F : N → Prop, (LXIN ι).DefinablePred F →
    TIup hJ ix (n + 1) (tau n m) F
  | 0 => fun _ hF => ti_base hG hF
  | m + 1 => ti_jump hG (tau_facts (hJ := hJ) n m).1 (tau_facts (hJ := hJ) n m).2.1 (ti_tau m)

end Tower

/-! ### Down the levels: the ranges -/

variable (hJ ix) in
/-- `F` is progressive on the range class `CC τ k`. -/
def ProgC (τ : N) (k : ℕ) (F : N → Prop) : Prop :=
  ∀ ξ, CC hJ ix τ k ξ → (∀ ξ', CC hJ ix τ k ξ' → hJ.lt ξ' ξ → F ξ') → F ξ

variable (hJ ix) in
/-- Transfinite induction on the range class of level `k` below `τ`. -/
def TIC (τ : N) (k : ℕ) : Prop :=
  ∀ F : N → Prop, (LXIN ι).DefinablePred F → ProgC hJ ix τ k F →
    ∀ ξ, CC hJ ix τ k ξ → hJ.lt ξ τ → F ξ

section Descent

variable (hG : Good hJ ix n A)
include hG

/-- At the top level: TI on `CC τ_m n` below `τ_m`, from the tower. -/
theorem tiC_top (m : ℕ) : TIC (s := s) hJ ix (tau n m) n := by
  intro F hF hP ξ hξ hlt
  have hF' : (LXIN ι).DefinablePred fun ξ : N => CC hJ ix (tau n m) n ξ → F ξ :=
    Language.Definable.imp (dfn_pred (definable_CC _ n) 0) (dfn_pred hF 0)
  have hP' : ProgD hJ ix (n + 1) fun ξ : N => CC hJ ix (tau n m) n ξ → F ξ :=
    fun ξ _ ih hC => hP ξ hC fun ξ' hξ' hlt => ih ξ' hξ'.1 hlt hξ'
  exact ti_tau hG m _ hF' hP' ξ hξ.1 hlt hξ

/-- `ϑ_k` maps the range class below `τ` into `W k`, given TI on it. -/
theorem W_theta_C {k : ℕ} (hk : k ≤ n) {τ : N} (hτ : hJ.fld τ) (hT : TIC (s := s) hJ ix τ k) :
    ∀ ξ, CC hJ ix τ k ξ → hJ.lt ξ τ → hJ.fld (tcTheta (k : N) ξ) →
      W ix k (tcTheta (k : N) ξ) := by
  have hF : (LXIN ι).DefinablePred fun ξ : N =>
      hJ.lt ξ τ → hJ.fld (tcTheta (k : N) ξ) → W ix k (tcTheta (k : N) ξ) :=
    Language.Definable.imp (dfn_sigma (k := 1) (R := fun v => hJ.lt (v 0) τ) (by definability))
      (Language.Definable.imp (dfn_sigma (k := 1)
        (R := fun v => hJ.fld (tcTheta (k : N) (v 0))) (by definability))
        (dfn_comp (definable_W k) (f := fun v : Fin 1 → N => tcTheta (k : N) (v 0))
          (by definability)))
  have hP : ProgC hJ ix τ k fun ξ : N =>
      hJ.lt ξ τ → hJ.fld (tcTheta (k : N) ξ) → W ix k (tcTheta (k : N) ξ) :=
    fun ξ hC ih hlt hf => W_theta hG hk (hLow_all hG k hk) hτ hC.1 hf (Or.inl hlt)
      fun ξ' hC' hlt' hf' => ih ξ' hC' hlt' (lt_trans hC'.1.fld hC.1.fld hτ hlt' hlt) hf'
  intro ξ hC hlt hf
  exact hT _ hF hP ξ hC hlt hlt hf

/-- **Collapse of the class on the ranges**: `CC τ k ⊆ CC τ (k+1)`, given that `ϑ_{k+1}` maps
`CC τ (k+1)` below `τ` into `W (k+1)`. -/
theorem cls_succ {k : ℕ} (hk : k + 1 ≤ n) {τ : N}
    (hE : ∀ ξ, CC hJ ix τ (k + 1) ξ → hJ.lt ξ τ → hJ.fld (tcTheta ((k + 1 : ℕ) : N) ξ) →
      W ix (k + 1) (tcTheta ((k + 1 : ℕ) : N) ξ)) :
    ∀ ξ, CC hJ ix τ k ξ → CC hJ ix τ (k + 1) ξ := by
  have hkk : ((k : ℕ) : N) < ((k + 1 : ℕ) : N) := by exact_mod_cast Nat.lt_succ_self k
  have hQ : (LXIN ι).DefinablePred fun ξ : N =>
      CC hJ ix τ k ξ → ∀ g, iinE ((k + 1 : ℕ) : N) g ξ = 1 → W ix (k + 1) g := by
    refine Language.Definable.imp (dfn_pred (definable_CC τ k) 0) ?_
    have := dfn_all (k := 1)
      (R := fun w : Fin 2 → N => iinE ((k + 1 : ℕ) : N) (w 0) (w 1) = 1 → W ix (k + 1) (w 0))
      (Language.Definable.imp (dfn_sigma (by definability)) (dfn_pred (definable_W (k + 1)) 0))
    exact Language.Definable.of_iff this fun v => Iff.rfl
  have key : ∀ ξ : N, CC hJ ix τ k ξ → ∀ g, iinE ((k + 1 : ℕ) : N) g ξ = 1 → W ix (k + 1) g := by
    refine order_induction_definable A hQ ?_
    intro ξ ih hC g hg
    have hgD : Dc hJ ix (k + 1) g := hC.1.of_iinE (by omega) hg
    obtain ⟨e, hlev⟩ := eq_tcTheta_of_iinE hg
    rcases lt_or_eq_of_le hlev with hj | hj
    · obtain ⟨j, hj'⟩ := eq_nat_of_lt_nat hj
      have hjk : j ≤ k := by
        have h1 : (j : N) < ((k + 1 : ℕ) : N) := hj' ▸ hj
        have h2 : j < k + 1 := by exact_mod_cast h1
        omega
      refine hLow_all hG (k + 1) hk g hgD ?_
      show hJ.lt g (tcOmega (k : N))
      rw [e, hj']
      exact (hJ.ax.lt_theta_Omega _ _ _).mpr (by exact_mod_cast hjk)
    · have hgd : g = tcTheta ((k + 1 : ℕ) : N) (tcThetaArg g) := by rw [← hj]; exact e
      set d := tcThetaArg g
      have hgf : hJ.fld (tcTheta ((k + 1 : ℕ) : N) d) := hgd ▸ hgD.fld
      have hdG : iinG (k : N) d ξ = 1 :=
        iinG_of_iinE hkk ξ d (by rw [← hgd]; exact hg)
      have hdτ : hJ.lt d τ := hC.2 d hdG
      have hdD1 : Dc hJ ix (k + 1) d := Dc.theta_arg le_rfl (hgd ▸ hgD)
      have hdC : CC hJ ix τ k d := ⟨hdD1, fun y hy => hC.2 y (iinG_trans (k : N) ξ d y hdG hy)⟩
      have hdlt : d < ξ := by
        have h1 : d < g := by rw [hgd]; exact arg_lt_tcTheta _ d
        exact lt_of_lt_of_le h1 (le_of_iinE hg)
      have hdE := ih d hdlt hdC
      have hdC' : CC hJ ix τ (k + 1) d :=
        ⟨dc_succ_iff.mpr ⟨hdD1, hdE⟩, fun y hy =>
          hC.2 y (iinG_trans (k : N) ξ d y hdG (iinG_mono (le_of_lt hkk) d y hy))⟩
      rw [hgd]
      exact hE d hdC' hdτ hgf
  intro ξ hC
  exact ⟨dc_succ_iff.mpr ⟨hC.1, key ξ hC⟩,
    fun y hy => hC.2 y (iinG_mono (le_of_lt hkk) ξ y hy)⟩

theorem tiC_of_succ {k : ℕ} {τ : N} (hcls : ∀ ξ, CC hJ ix τ k ξ → CC hJ ix τ (k + 1) ξ)
    (hT : TIC (s := s) hJ ix τ (k + 1)) : TIC (s := s) hJ ix τ k := by
  intro F hF hP ξ hξ hlt
  have hF' : (LXIN ι).DefinablePred fun ξ : N => CC hJ ix τ k ξ → F ξ :=
    Language.Definable.imp (dfn_pred (definable_CC τ k) 0) (dfn_pred hF 0)
  have hP' : ProgC hJ ix τ (k + 1) fun ξ : N => CC hJ ix τ k ξ → F ξ :=
    fun ξ _ ih hξ0 => hP ξ hξ0 fun ξ' hξ' hlt => ih ξ' (hcls ξ' hξ') hlt hξ'
  exact hT _ hF' hP' ξ (hcls ξ hξ) hlt hξ

/-- **The descent**: TI on the range class below `τ_m` at every level `n - d`. -/
theorem tiC_all (m : ℕ) : ∀ d, d ≤ n → TIC (s := s) hJ ix (tau n m) (n - d)
  | 0, _ => tiC_top hG m
  | d + 1, hd => by
    have hT := tiC_all m d (by omega)
    have e : n - d = (n - (d + 1)) + 1 := by omega
    rw [e] at hT
    have hτ := (tau_facts (hJ := hJ) (N := N) n m).1
    refine tiC_of_succ hG (cls_succ hG (by omega) ?_) hT
    exact W_theta_C hG (by omega) hτ hT

/-- **`ϑ₀(τ_m) ∈ W 0`** for every standard `m`. -/
theorem W_theta_tau (m : ℕ) : W ix 0 (tcTheta (0 : N) (tau (N := N) n m)) := by
  have hT0 : TIC (s := s) hJ ix (tau n m) 0 := by
    have := tiC_all (s := s) hG m n le_rfl
    rwa [Nat.sub_self] at this
  obtain ⟨hτ, -, hE, hGτ⟩ := tau_facts (hJ := hJ) (N := N) n m
  have hα : Dc hJ ix 1 (tau (N := N) n m) :=
    dc_succ_iff.mpr ⟨hτ, fun δ h => absurd h (hE _ δ)⟩
  have hfα : hJ.fld (tcTheta ((0 : ℕ) : N) (tau (N := N) n m)) :=
    (fld_theta_iff _ _).mpr ⟨hτ, fun y h => absurd h (hGτ _ y)⟩
  have := W_theta hG (Nat.zero_le n) (hLow_all hG 0 (Nat.zero_le n)) hτ hα hfα (Or.inr rfl)
    fun ξ hC hlt hf => W_theta_C hG (Nat.zero_le n) hτ hT0 ξ hC hlt hf
  simpa using this

end Descent

end Model

end OrdinalAnalysis.IDn.Upper
