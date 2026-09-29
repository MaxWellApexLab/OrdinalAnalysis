/-
  The tower `τ_m = ω_m(Ω_ω + 1)` inside models of `IDw WFormWc`: BP78 Theorem 3, and the
  collapse `ϑ₀(τ_m) ∈ J(0, ·)` for every standard `m`.

  Sources: W. Buchholz and W. Pohlers, *Provable wellorderings of formal theories for
  transfinitely iterated inductive definitions*, J. Symbolic Logic 43 (1978), pp. 121–123
  (Theorems 2, 3); T. Arai, *Lectures on ordinal analysis*, arXiv:2304.00246, Lemmas 1.31,
  1.32.  The `ID_n` version is the tower section of `IDn/WellOrdering.lean`
  (`tau_facts`, `ti_base`, `ti_jump`, `ti_tau`, `W_theta_tau`).

  * `omegaSuccW`, `tauW`: the codes of `Ω_ω + 1 = ⟨Ω_ω, 0⟩` and `τ_{m+1} = ω^{τ_m} = ⟨τ_m⟩`;
  * `lt_OmegaW_succ_cases` (T3a): a normal domain code below `Ω_ω + 1` is below `Ω_ω` or is `Ω_ω`;
  * `tauW_facts` (T3a'): `τ_m ∈ M` is a sum and `ϑ₀ τ_m` is in the field (no coefficients, no
    collapse arguments);
  * `ti_base` (T3b): `TI[M, Ω_ω + 1]`, from `TI[M, Ω_ω]` (`ti_M_OmegaW`);
  * `ti_jump` (T3c): Gentzen's jump over `M = ClsW (fun _ => True)`;
  * `ti_tau`, `W_theta_tau`: `TI[M, τ_m]`, and `ϑ₀(τ_m) ∈ J(0, ·)` (`W_theta_of_TI'`).
-/
import OrdinalAnalysis.IDw.WellOrderingJump
import OrdinalAnalysis.IDw.WellOrderingTI

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OrdinalAnalysis.IDw.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.IDw.Internal
open OrdinalAnalysis.ID1.Internal (bor band beq bor_eq_one band_eq_one beq_eq_one)

section Tower

variable {N : Type} [ORingStructure N] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [s : Structure LXJ N]

/-- The code of `Ω_ω + 1 = ⟨Ω_ω, 0⟩`. -/
noncomputable def omegaSuccW : N := tcCons tcOmegaW (tcCons 0 0)

/-- `τ_0 = Ω_ω + 1`, `τ_{m+1} = ω^{τ_m} = ⟨τ_m⟩`. -/
noncomputable def tauW : ℕ → N
  | 0 => omegaSuccW
  | m + 1 => tcCons (tauW m) 0

/-! ### T3a. Below `Ω_ω + 1`, and the shape of `τ_m` -/

omit [s : Structure LXJ N] in
theorem fldW_tcOmegaW : fldW (tcOmegaW : N) :=
  ⟨by simp [isNF, isNFb], by simp [isDom]⟩

omit [s : Structure LXJ N] in
/-- The one-entry list `⟨0⟩` is a descending list (of normal domain codes). -/
theorem isSL_single_zero : isSL (tcCons 0 0 : N) :=
  (isSL_cons_iff 0 0).mpr ⟨⟨isNF_zero', by simp⟩, isSL_zero, Or.inl rfl⟩

omit [s : Structure LXJ N] in
/-- T3a. Below `Ω_ω + 1`: a normal code below `⟨Ω_ω, 0⟩` is below `Ω_ω` or is `Ω_ω` (IDn
`lt_Omega_succ_cases`). -/
theorem lt_OmegaW_succ_cases {ξ : N} (hξ : fldW ξ) (h : iltb ξ omegaSuccW = 1) :
    iltb ξ tcOmegaW = 1 ∨ ξ = tcOmegaW := by
  rcases nfA_cases (nfA_of_isNF hξ.1) with
    rfl | ⟨j, rfl⟩ | ⟨j, a, rfl, -⟩ | ⟨z, w, rfl, hzN, -, -, -⟩ | rfl
  · exact Or.inl (iltb_zero_pos tcOmegaW_ne_zero)
  · exact Or.inl (iltb_tcOmega_tcOmegaW j)
  · exact Or.inl (iltb_tcTheta_tcOmegaW j a)
  · unfold omegaSuccW at h
    rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at h
    rcases h with h | ⟨hz, h⟩
    · left
      rw [iltb_cons_prin z w (Or.inr (Or.inr kind_tcOmegaW))]
      exact h
    · exfalso
      subst hz
      obtain ⟨hsl, hne⟩ := (isNF_isDom_tcCons_iff _ _).mp hξ
      have hw : isSL w := ((isSL_cons_iff _ _).mp hsl).2.1
      rcases eq_or_ne w 0 with rfl | hw0
      · exact hne ⟨rfl, Or.inr (Or.inr kind_tcOmegaW)⟩
      · obtain ⟨z', w', rfl⟩ := isSL_eq_cons hw hw0
        rw [iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at h
        rcases h with h | ⟨-, h⟩
        · exact not_iltb_zero_right _ h
        · exact not_iltb_zero_right _ h
  · exact Or.inr rfl

omit [s : Structure LXJ N] in
/-- `τ_m` is a normal domain sum, without coefficients and without collapse arguments. -/
theorem tauW_props : ∀ m : ℕ, fldW (tauW (N := N) m) ∧ kind (tauW (N := N) m) = 3 ∧
    (∀ j g : N, iinE j g (tauW m) ≠ 1) ∧ (∀ j y : N, iinG j y (tauW m) ≠ 1)
  | 0 => by
    refine ⟨?_, kind_tcCons _ _, fun j g hg => ?_, fun j y hy => ?_⟩
    · refine (isNF_isDom_tcCons_iff _ _).mpr ⟨(isSL_cons_iff _ _).mpr ⟨fldW_tcOmegaW,
        isSL_single_zero, Or.inr (Or.inl ?_)⟩, ?_⟩
      · rw [tcHd_tcCons]; exact iltb_zero_pos tcOmegaW_ne_zero
      · rintro ⟨h, -⟩; exact tcCons_ne_zero 0 0 h
    · simp only [tauW, omegaSuccW, iinE_cons_iff, iinE_at_tcOmegaW, iinE_at_zero] at hg
      simp at hg
    · simp only [tauW, omegaSuccW, iinG_cons_iff, iinG_at_tcOmegaW, iinG_at_zero] at hy
      simp at hy
  | m + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := tauW_props m
    refine ⟨?_, kind_tcCons _ _, fun j g hg => ?_, fun j y hy => ?_⟩
    · refine (isNF_isDom_tcCons_iff _ _).mpr ⟨(isSL_cons_iff _ _).mpr ⟨h1, isSL_zero, Or.inl rfl⟩, ?_⟩
      rintro ⟨-, hk | hk | hk⟩ <;> rw [h2] at hk <;> simp at hk
    · simp only [tauW, iinE_cons_iff, iinE_at_zero] at hg
      exact h3 j g (by simpa using hg)
    · simp only [tauW, iinG_cons_iff, iinG_at_zero] at hy
      exact h4 j y (by simpa using hy)

/-- T3a'. `τ_m ∈ M`, `τ_m` is a sum, and `ϑ₀ τ_m` is in the field (IDn `tau_facts`). -/
theorem tauW_facts (m : ℕ) :
    MMW (s := s) (tauW (N := N) m) ∧ kind (tauW (N := N) m) = 3 ∧
      fldW (tcTheta 0 (tauW (N := N) m)) := by
  obtain ⟨h1, h2, h3, h4⟩ := tauW_props (N := N) m
  refine ⟨⟨h1, fun j g hg => absurd hg (h3 j g)⟩, h2, ?_, ?_⟩
  · rw [isNF_tcTheta_iff]; exact h1.1
  · exact (isDom_tcTheta_iff _ _).mpr ⟨h1.2, fun y hy => absurd hy (h4 _ y)⟩

end Tower

/-! ### T3b, T3c. Transfinite induction on `M` up to the tower -/

section TI

variable {N : Type} [ORingStructure N] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [s : Structure LXJ N]
variable (M : WModel N)
include M

/-- T3b. **TI on `M` up to `Ω_ω + 1`** (from (12); IDn `ti_base`). -/
theorem ti_base : TIW MMW (omegaSuccW : N) := by
  intro X hX hP ξ hξ hlt
  have hB := ti_M_OmegaW M (W_cons M) X hX hP
  rcases lt_OmegaW_succ_cases hξ.1 hlt with h | rfl
  · exact hB ξ hξ h
  · exact hP _ hξ fun ξ' hξ' h => hB ξ' hξ' h

omit M in
/-- `M` is the class `ClsW (fun _ => True)`. -/
theorem mmW_iff_cls (x : N) : MMW (s := s) x ↔ ClsW (fun _ : N => True) x :=
  ⟨fun h => ⟨h.1, fun j _ g hg => h.2 j g hg⟩, fun h => ⟨h.1, fun j g hg => h.2 j trivial g hg⟩⟩

/-- T3c. **Gentzen's jump on `M`** (BP78 Lemma 4 / Theorem 3; IDn `ti_jump`, the jump over
`ClsW (fun _ => True)`): TI on `M` up to a normal sum `β` for every definable predicate gives
TI up to `ω^β = ⟨β⟩`. -/
theorem ti_jump {β : N} (hβ : MMW β) (hβk : kind β = 3) (h : TIW MMW β) :
    TIW MMW (tcCons β 0) := by
  intro F hF hP ξ hξ hlt
  have hB : 𝚺₁.DefinablePred fun _ : N => True := by definability
  have hPc : ProgW (ClsW fun _ : N => True) F := fun x hx ih =>
    hP x ((mmW_iff_cls x).mpr hx) fun y hy hlt => ih y ((mmW_iff_cls y).mp hy) hlt
  have hPj : ProgW MMW (JFW (fun _ : N => True) F) := fun y hy ih =>
    jump_prog M hB hF hPc y ((mmW_iff_cls y).mp hy)
      fun y' hy' hlt => ih y' ((mmW_iff_cls y').mpr hy') hlt
  have hJ' : ∀ y, MMW y → iltb y β = 1 → JFW (fun _ : N => True) F y :=
    fun y hy hlt => h _ (dfn_JFW M hB hF) hPj y hy hlt
  have hβ1 : fldW (tcCons β 0) := by
    refine (isNF_isDom_tcCons_iff β 0).mpr ⟨(isSL_cons_iff β 0).mpr ⟨hβ.1, isSL_zero, Or.inl rfl⟩,
      ?_⟩
    rintro ⟨-, hk | hk | hk⟩ <;> rw [hβk] at hk <;> simp at hk
  have hl : iltb (expList ξ) (tcCons β 0) = 1 := by
    have := (iltb_expList_iff hξ.1.1 hβ1.1).mpr hlt
    rwa [expList_tcCons] at this
  have hsl := isSL_expList hξ.1.1 hξ.1.2
  rcases eq_or_ne (expList ξ) 0 with h0 | hne
  · have hξ0 : ξ = 0 := by
      by_contra hne
      exact expList_ne_zero hne h0
    subst hξ0
    exact hP 0 hξ fun _ _ h => absurd h (not_iltb_zero_right _)
  · obtain ⟨z, w, hzw⟩ := isSL_eq_cons hsl hne
    have hz : iltb z β = 1 := by
      rw [hzw, iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one] at hl
      rcases hl with hl | ⟨-, hl⟩
      · exact hl
      · exact absurd hl (not_iltb_zero_right _)
    have hzF : fldW z := by
      rw [hzw] at hsl
      exact ((isSL_cons_iff z w).mp hsl).1
    refine holds_of_jump M hB hF hPc ((mmW_iff_cls ξ).mp hξ) fun y hy hle => hJ' y
      ((mmW_iff_cls y).mpr hy) ?_
    rw [hzw, tcHd_tcCons] at hle
    exact iltb_of_le_of_lt (isTerm_of_fldW hy.1) (isTerm_of_fldW hzF) (isTerm_of_fldW hβ.1)
      hle hz

/-- **BP78 Theorem 3**: `TI[M, τ_m]` for every standard `m`. -/
theorem ti_tau : ∀ m : ℕ, TIW MMW (tauW (N := N) m)
  | 0 => ti_base M
  | m + 1 => ti_jump M (tauW_facts m).1 (tauW_facts m).2.1 (ti_tau m)

/-- **BP78 Theorem 2 at level 0, the tower**: `ϑ₀(ω_m(Ω_ω + 1)) ∈ J(0, ·)` for every `m`. -/
theorem W_theta_tau (m : ℕ) : Jm 0 (tcTheta 0 (tauW (N := N) m)) :=
  W_theta_of_TI' M (ti_tau M m) (tauW_facts m).1 0 (tauW_facts m).2.2

end TI

end OrdinalAnalysis.IDw.Upper
