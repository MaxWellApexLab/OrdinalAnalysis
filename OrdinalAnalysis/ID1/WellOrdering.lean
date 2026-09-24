/-
  The well-ordering proof for the ϑ-notation inside models of `ID₁`.

  Source: T. Arai, *Lectures on ordinal analysis*, arXiv:2304.00246, §1.6 (Definition 1.27,
  Lemmas 1.29, 1.31, 1.32, 1.33), after Buchholz's distinguished classes, carried out for the
  ϑ-notation of A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Definition 3.1, with Gentzen's jump for the part above
  `Ω`.  The metatheoretic version of the argument is `ThetaTerm.isAcc_theta_of_dist_of_forall`.

  Throughout, `N` is an arithmetically standard model of `ID1Acc precC` (so a model of `IΣ₁`,
  and the facts about the internal coding hold in `N`).  `W` is the extension of `I`: the
  accessible part of the coded order `≺` on codes of normal forms, closed (`W_of_forall`) and
  with the induction scheme for every predicate definable in `LXI` with parameters
  (`W_induction`).
  A normal form is compared with others through its exponent list `itoL α`.

  * `W` is downward closed (`W_down`).
  * **Gentzen's jump**, for an arbitrary class `D_G = {α normal | E(α) ⊆ G}` and a definable
    `F` progressive on `D_G`: with `HL(η)` = "`F` holds on every `ξ ∈ D_G` whose exponent
    list is below the list `η`" and

        J(y)  :≡  ∀η (η, η ++ ⟨y⟩ descending → HL(η) → HL(η ++ ⟨y⟩)),

    `J` is progressive on `D_G` (`jump_prog`), and `F ξ` holds as soon as `J` holds at every
    element of `D_G` below or equal to the first exponent of `ξ` (`holds_of_jump`); the latter
    is an induction on the list of exponents (`hl_iapp`).
  * **Sums** (Arai, Lemma 1.29, the step for sums): with `G` trivial and `F = W`, `J` holds on
    `W` by the induction scheme, hence a normal sum is in `W` once its first exponent is
    (`W_cons`).
  * **The distinguished class below `Ω`** (Arai, Lemma 1.29): a normal form `≺ Ω` whose
    coefficients are in `W` is in `W` (`W_of_dist_lt_one`).
  * **The tower** (Arai, Lemmas 1.31, 1.32): with `G = W`, transfinite induction along `≺` on
    `M = D_W` holds up to `Ω + 1` (from the induction scheme of `I`) and passes from `β` to
    `ω^β` (Gentzen's jump), for every definable predicate; hence up to every
    `τ_n = ω_n(Ω + 1)` (`ti_tau`).
  * **The main lemma** (Arai, Lemma 1.33, for ϑ): if `α ∈ M` and `ϑξ ∈ W` for every
    `ξ ∈ M` with `ξ ≺ α`, then `ϑα ∈ W` (`W_theta`), by induction on the codes below `ϑα`.
  * Hence `ϑ(τ_n) ∈ W` for every standard `n` (`W_theta_tau`).
-/
import OrdinalAnalysis.ID1.Lift
import OrdinalAnalysis.ID1.Internal.JumpList
import OrdinalAnalysis.ID1.Internal.ArithE

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

namespace WellOrdering

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.ID1.Internal OrdinalAnalysis.InductiveDef.Lift

/-! ### Definability in `LXI` -/

section Definability

variable {N : Type*} [ORingStructure N] [Structure LXI N] [ArithStd N]

omit [ORingStructure N] [ArithStd N] in
theorem dfn_all {k : ℕ} {R : (Fin (k + 1) → N) → Prop} (h : LXI.Definable R) :
    LXI.Definable fun v : Fin k → N => ∀ x, R (x :> v) := by
  refine Language.Definable.all ?_
  refine Language.Definable.of_iff h fun w => ?_
  rw [show (w 0 :> fun x => w x.succ) = w from Matrix.cons_head_tail w]

omit [ORingStructure N] [ArithStd N] in
theorem dfn_ex {k : ℕ} {R : (Fin (k + 1) → N) → Prop} (h : LXI.Definable R) :
    LXI.Definable fun v : Fin k → N => ∃ x, R (x :> v) := by
  refine Language.Definable.exs ?_
  refine Language.Definable.of_iff h fun w => ?_
  rw [show (w 0 :> fun x => w x.succ) = w from Matrix.cons_head_tail w]

omit [ORingStructure N] [ArithStd N] in
theorem dfn_pred {k : ℕ} {Q : N → Prop} (hQ : LXI.DefinablePred Q) (i : Fin k) :
    LXI.Definable fun v : Fin k → N => Q (v i) :=
  Language.Definable.of_iff (hQ.retraction ![i]) fun v => by simp

theorem dfn_comp {k : ℕ} {Q : N → Prop} (hQ : LXI.DefinablePred Q) {f : (Fin k → N) → N}
    (hf : 𝚺₁.DefinableFunction f) : LXI.Definable fun v : Fin k → N => Q (f v) :=
  @Language.DefinablePred.comp LXI N _ Q k f hQ (definable_of_arith hf)

theorem dfn_sigma {k : ℕ} {R : (Fin k → N) → Prop} (h : 𝚺₁.Definable R) : LXI.Definable R :=
  definable_of_arith h

end Definability

/-! ### The accessible part in a model of `ID1Acc precC` -/

section Model

variable {N : Type*} [ORingStructure N] [Structure LXI N] [ArithStd N]
  [N↓[LXI] ⊧* ID1Acc precC] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `W`: the extension of `I`, the accessible part of `≺`. -/
abbrev W (x : N) : Prop := Imem x

omit [Structure LXI N] [ArithStd N] [N↓[LXI] ⊧* ID1Acc precC] in
theorem precM_iff (y x : N) : precM precC y x ↔ isNF y ∧ isNF x ∧ iltb y x = 1 :=
  eval_thPrecDef y x

/-- `W` is closed: `(∀y ≺ x, y ∈ W) → x ∈ W`. -/
theorem W_of_forall (x : N) (h : ∀ y, isNF y → isNF x → iltb y x = 1 → W y) : W x :=
  imem_of_forall precC x fun y hy => by
    rw [precM_iff] at hy; exact h y hy.1 hy.2.1 hy.2.2

theorem W_zero : W (0 : N) := W_of_forall 0 fun _ _ _ h => absurd h (not_iltb_zero _)

omit [N↓[LXI] ⊧* ID1Acc precC] in
theorem dfn_below {Q : N → Prop} (hQ : LXI.DefinablePred Q) :
    LXI.DefinablePred fun x : N => ∀ y, isNF y → isNF x → iltb y x = 1 → Q y := by
  have h := dfn_all (k := 1)
    (R := fun w : Fin 2 → N => isNF (w 0) → isNF (w 1) → iltb (w 0) (w 1) = 1 → Q (w 0))
    (Language.Definable.imp (dfn_sigma (by definability))
      (Language.Definable.imp (dfn_sigma (by definability))
        (Language.Definable.imp (dfn_sigma (by definability)) (dfn_pred hQ 0))))
  exact Language.Definable.of_iff h fun v => by simp

/-- The induction scheme of `I`, in the form without `I` in the step. -/
theorem W_induction' {Q : N → Prop} (hQ : LXI.DefinablePred Q)
    (h : ∀ x, (∀ y, isNF y → isNF x → iltb y x = 1 → Q y) → Q x) : ∀ x, W x → Q x :=
  ind_definable precC hQ fun x hx =>
    h x fun y hy1 hy2 hy3 => hx y ((precM_iff y x).mpr ⟨hy1, hy2, hy3⟩)

/-- **`W` is downward closed.** -/
theorem W_down {x y : N} (hx : W x) (hxn : isNF x) (hy : isNF y) (h : iltb y x = 1) : W y :=
  W_induction' (Q := fun x : N => ∀ y, isNF y → isNF x → iltb y x = 1 → W y)
    (dfn_below definable_imem)
    (fun _ ih y hy hxn hyx => W_of_forall y fun z hz hyn hzy => ih y hy hxn hyx z hz hyn hzy)
    x hx y hy hxn h

theorem W_down_le {x y : N} (hx : W x) (hxn : isNF x) (hy : isNF y)
    (h : iltb y x = 1 ∨ y = x) : W y := by
  rcases h with h | rfl
  · exact W_down hx hxn hy h
  · exact hx

/-- **The induction scheme of `I`** for definable predicates. -/
theorem W_induction {Q : N → Prop} (hQ : LXI.DefinablePred Q)
    (h : ∀ x, W x → (∀ y, isNF y → isNF x → iltb y x = 1 → Q y) → Q x) : ∀ x, W x → Q x := by
  have hQ' : LXI.DefinablePred fun x : N => W x → Q x :=
    Language.Definable.imp (dfn_pred definable_imem 0) (dfn_pred hQ 0)
  intro x hx
  exact W_induction' (Q := fun x : N => W x → Q x) hQ'
    (fun x ih hx => h x hx fun y hy hxn hyx => ih y hy hxn hyx (W_down hx hxn hy hyx)) x hx hx

/-! ### Gentzen's jump on exponent lists -/

section Jump

variable (G F : N → Prop)

/-- The class `D_G`: normal forms all of whose coefficients (elements of `E`) are in `G`. -/
def Dom (ξ : N) : Prop := isNF ξ ∧ ∀ g, iinE g ξ = 1 → G g

/-- `HL(η)`: `F` holds on every element of `D_G` whose exponent list is below the list `η`. -/
def HL (s : N) : Prop := ∀ ξ, Dom G ξ → iltb (itoL ξ) s = 1 → F ξ

/-- **The jump** `J(y)`: appending the exponent `y` to a list keeps `HL`. -/
def JF (y : N) : Prop :=
  ∀ η, IsSL η → IsSL (isnoc η y) → HL G F η → HL G F (isnoc η y)

/-- `F` is progressive along `≺` on `D_G`. -/
def ProgD : Prop := ∀ ξ, Dom G ξ → (∀ ξ', Dom G ξ' → iltb ξ' ξ = 1 → F ξ') → F ξ

variable {G F}

omit [Structure LXI N] [ArithStd N] [N↓[LXI] ⊧* ID1Acc precC] in
theorem holds_of_hl (hP : ProgD G F) {ξ : N} (hξ : Dom G ξ) (h : HL G F (itoL ξ)) : F ξ :=
  hP ξ hξ fun ξ' hξ' hlt => h ξ' hξ' ((iltb_itoL_iff hξ'.1 hξ.1).mpr hlt)

omit [Structure LXI N] [ArithStd N] [N↓[LXI] ⊧* ID1Acc precC] in
theorem hl_zero : HL G F (0 : N) := fun _ _ h => absurd h (not_iltb_zero _)

omit [N↓[LXI] ⊧* ID1Acc precC] in
theorem dfn_dom (hG : LXI.DefinablePred G) : LXI.DefinablePred (Dom G) := by
  have h := dfn_all (k := 1) (R := fun w : Fin 2 → N => iinE (w 0) (w 1) = 1 → G (w 0))
    (Language.Definable.imp (dfn_sigma (by definability)) (dfn_pred hG 0))
  exact Language.Definable.of_iff
    (Language.Definable.and (dfn_sigma (k := 1) (R := fun v => isNF (v 0)) (by definability)) h)
    fun v => by simp [Dom]

omit [N↓[LXI] ⊧* ID1Acc precC] in
theorem dfn_hl (hG : LXI.DefinablePred G) (hF : LXI.DefinablePred F) :
    LXI.DefinablePred (HL G F) := by
  have h := dfn_all (k := 1)
    (R := fun w : Fin 2 → N => Dom G (w 0) → iltb (itoL (w 0)) (w 1) = 1 → F (w 0))
    (Language.Definable.imp (dfn_pred (dfn_dom hG) 0)
      (Language.Definable.imp (dfn_sigma (by definability)) (dfn_pred hF 0)))
  exact Language.Definable.of_iff h fun v => by simp [HL]

omit [N↓[LXI] ⊧* ID1Acc precC] in
theorem dfn_jf (hG : LXI.DefinablePred G) (hF : LXI.DefinablePred F) :
    LXI.DefinablePred (JF G F) := by
  have h := dfn_all (k := 1)
    (R := fun w : Fin 2 → N => IsSL (w 0) → IsSL (isnoc (w 0) (w 1)) → HL G F (w 0) →
      HL G F (isnoc (w 0) (w 1)))
    (Language.Definable.imp (dfn_sigma (by definability))
      (Language.Definable.imp (dfn_sigma (by definability))
        (Language.Definable.imp (dfn_pred (dfn_hl hG hF) 0)
          (dfn_comp (dfn_hl hG hF) (f := fun w : Fin 2 → N => isnoc (w 0) (w 1))
            (by definability)))))
  exact Language.Definable.of_iff h fun v => by simp [JF]

omit [N↓[LXI] ⊧* ID1Acc precC] in
theorem dfn_hl_iapp (hG : LXI.DefinablePred G) (hF : LXI.DefinablePred F) :
    LXI.DefinablePred fun r : N => r ≠ 0 → IsSL r → (∀ g, iinE g r = 1 → G g) →
      (∀ y, Dom G y → (iltb y (tcHd r) = 1 ∨ y = tcHd r) → JF G F y) →
      ∀ η, IsSL η → IsSL (iapp η r) → HL G F η → HL G F (iapp η r) := by
  have h1 := dfn_all (k := 1) (R := fun w : Fin 2 → N => iinE (w 0) (w 1) = 1 → G (w 0))
    (Language.Definable.imp (dfn_sigma (by definability)) (dfn_pred hG 0))
  have h2 := dfn_all (k := 1)
    (R := fun w : Fin 2 → N => Dom G (w 0) → (iltb (w 0) (tcHd (w 1)) = 1 ∨ w 0 = tcHd (w 1)) →
      JF G F (w 0))
    (Language.Definable.imp (dfn_pred (dfn_dom hG) 0)
      (Language.Definable.imp (dfn_sigma (by definability)) (dfn_pred (dfn_jf hG hF) 0)))
  have h3 := dfn_all (k := 1)
    (R := fun w : Fin 2 → N => IsSL (w 0) → IsSL (iapp (w 0) (w 1)) → HL G F (w 0) →
      HL G F (iapp (w 0) (w 1)))
    (Language.Definable.imp (dfn_sigma (by definability))
      (Language.Definable.imp (dfn_sigma (by definability))
        (Language.Definable.imp (dfn_pred (dfn_hl hG hF) 0)
          (dfn_comp (dfn_hl hG hF) (f := fun w : Fin 2 → N => iapp (w 0) (w 1))
            (by definability)))))
  have h := Language.Definable.imp (dfn_sigma (k := 1) (R := fun v => v 0 ≠ 0) (by definability))
    (Language.Definable.imp (dfn_sigma (k := 1) (R := fun v => IsSL (v 0)) (by definability))
      (Language.Definable.imp h1 (Language.Definable.imp h2 h3)))
  exact Language.Definable.of_iff h fun v => by simp

/-- **Iterating the jump along a list** (the finite iteration in Gentzen's Lemma B): if `J`
holds at every element of `D_G` below or equal to the first entry of the nonempty descending
list `ρ` with coefficients in `G`, then `HL(η) → HL(η ++ ρ)`.  Induction on the code of `ρ`. -/
theorem hl_iapp (hG : LXI.DefinablePred G) (hF : LXI.DefinablePred F) :
    ∀ r : N, r ≠ 0 → IsSL r → (∀ g, iinE g r = 1 → G g) →
      (∀ y, Dom G y → (iltb y (tcHd r) = 1 ∨ y = tcHd r) → JF G F y) →
      ∀ η, IsSL η → IsSL (iapp η r) → HL G F η → HL G F (iapp η r) := by
  refine order_induction_definable precC (dfn_hl_iapp hG hF) ?_
  intro r ih hr0 hr hGr hJ η hη hηr hHL
  obtain ⟨z, r', rfl⟩ := eq_cons_of_sumK hr.2 hr0
  obtain ⟨hz, hr', hdesc⟩ := (isSL_cons_iff z r').mp hr
  have hJz : JF G F z :=
    hJ z ⟨hz, fun g hg => hGr g ((iinE_tcCons_iff g z r').mpr (Or.inl hg))⟩
      (Or.inr (tcHd_tcCons z r').symm)
  have hsn : IsSL (isnoc η z) := isSL_isnoc_of_isSL_iapp z r' η hηr
  have h1 : HL G F (isnoc η z) := hJz η hη hsn hHL
  rcases eq_or_ne r' 0 with rfl | hr'0
  · exact h1
  · rw [← iapp_isnoc]
    refine ih r' (tl_lt_tcCons z r') hr'0 hr'
      (fun g hg => hGr g ((iinE_tcCons_iff g z r').mpr (Or.inr hg)))
      (fun y hy hle => hJ y hy ?_) (isnoc η z) hsn (by rw [iapp_isnoc]; exact hηr) h1
    rw [tcHd_tcCons]
    exact ile_trans hle (ige_eq_one.mp (hdesc.resolve_left hr'0))

/-- **The jump is progressive** (Gentzen's Lemma B; Arai, Lemma 1.31): if `F` is progressive
on `D_G`, so is `J`. -/
theorem jump_prog (hG : LXI.DefinablePred G) (hF : LXI.DefinablePred F) (hP : ProgD G F) :
    ∀ y, Dom G y → (∀ y', Dom G y' → iltb y' y = 1 → JF G F y') → JF G F y := by
  intro y _ ih η hη _ hHL ξ hξ hlt
  rcases iltb_isnoc_cases y η hη (itoL ξ) (isSL_itoL hξ.1) hlt with h | h | ⟨r, -, hr, hr0, hry⟩
  · exact hHL ξ hξ h
  · exact holds_of_hl hP hξ (by rw [h]; exact hHL)
  · refine holds_of_hl hP hξ ?_
    have hSL : IsSL (iapp η r) := hr ▸ isSL_itoL hξ.1
    rw [hr]
    refine hl_iapp hG hF r hr0 (isSL_of_isSL_iapp_right r η hSL) (fun g hg => hξ.2 g ?_)
      (fun y' hy' hle => ih y' hy' (iltb_of_le_of_lt hle hry)) η hη hSL hHL
    rw [← iinE_itoL, hr]
    exact iinE_iapp_right g r η hg

/-- **Using the jump**: `F ξ` holds as soon as `J` holds at every element of `D_G` below or
equal to the first exponent of `ξ`. -/
theorem holds_of_jump (hG : LXI.DefinablePred G) (hF : LXI.DefinablePred F) (hP : ProgD G F)
    {ξ : N} (hξ : Dom G ξ)
    (hJ : ∀ y, Dom G y → (iltb y (tcHd (itoL ξ)) = 1 ∨ y = tcHd (itoL ξ)) → JF G F y) :
    F ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ0
  · exact hP 0 hξ fun _ _ h => absurd h (not_iltb_zero _)
  · refine holds_of_hl hP hξ ?_
    have hSL := isSL_itoL hξ.1
    have := hl_iapp hG hF (itoL ξ) (itoL_ne_zero (isTerm_of_isNF hξ.1) hξ0) hSL
      (fun g hg => hξ.2 g ((iinE_itoL g ξ).mp hg)) hJ 0 isSL_zero
      (by rw [iapp_zero_left]; exact hSL) hl_zero
    rwa [iapp_zero_left] at this

end Jump

/-! ### Sums (Arai, Lemma 1.29, the step for sums) -/

/-- **A normal sum is in `W` once its first exponent is.** -/
theorem W_cons {x w : N} (hc : isNF (tcCons x w)) (hx : W x) : W (tcCons x w) := by
  have hG : LXI.DefinablePred fun _ : N => True := Language.Definable.const True
  have hP : ProgD (fun _ : N => True) W := fun ξ _ h =>
    W_of_forall ξ fun y hy _ hyx => h y ⟨hy, fun _ _ => trivial⟩ hyx
  have hJ : ∀ y, W y → isNF y → JF (fun _ : N => True) W y :=
    W_induction (Q := fun y => isNF y → JF (fun _ : N => True) W y)
      (Language.Definable.imp (dfn_sigma (k := 1) (R := fun v => isNF (v 0)) (by definability))
        (dfn_pred (dfn_jf hG definable_imem) 0))
      (fun y _ ih hy => jump_prog hG definable_imem hP y ⟨hy, fun _ _ => trivial⟩
        fun y' hy' hlt => ih y' hy'.1 hy hlt hy'.1)
  have hxn : isNF x := ((isSL_cons_iff x w).mp ((isNF_tcCons_iff x w).mp hc).1).1
  refine holds_of_jump hG definable_imem hP ⟨hc, fun _ _ => trivial⟩ fun y hy hle => ?_
  rw [itoL_tcCons, tcHd_tcCons] at hle
  exact hJ y (W_down_le hx hxn hy.1 hle) hy.1

/-! ### The distinguished class below `Ω` (Arai, Lemma 1.29) -/

/-- **A normal form below `Ω` whose coefficients are in `W` is in `W`.** -/
theorem W_of_dist_lt_one :
    ∀ γ : N, isNF γ → (∀ g, iinE g γ = 1 → W g) → iltb γ 1 = 1 → W γ := by
  have h1 := dfn_all (k := 1) (R := fun w : Fin 2 → N => iinE (w 0) (w 1) = 1 → W (w 0))
    (Language.Definable.imp (dfn_sigma (by definability)) (dfn_pred definable_imem 0))
  have hQ : LXI.DefinablePred fun γ : N =>
      isNF γ → (∀ g, iinE g γ = 1 → W g) → iltb γ 1 = 1 → W γ :=
    Language.Definable.of_iff
      (Language.Definable.imp (dfn_sigma (k := 1) (R := fun v => isNF (v 0)) (by definability))
        (Language.Definable.imp h1
          (Language.Definable.imp (dfn_sigma (k := 1) (R := fun v => iltb (v 0) 1 = 1)
            (by definability)) (dfn_pred definable_imem 0))))
      fun v => by simp
  refine order_induction_definable precC hQ ?_
  intro γ ih hγ hd hlt
  rcases nf_cases hγ with rfl | hp | ⟨z, w, rfl, -⟩
  · exact W_zero
  · rcases hp with hk | hk
    · rw [iltb_top_prin (Or.inl hk) (by simp) (by simp)] at hlt
      simp at hlt
    · obtain ⟨a, rfl⟩ : ∃ a, γ = tcTheta a := ⟨_, eq_tcTheta_of_kind hk⟩
      exact hd _ ((iinE_tcTheta_iff _ _).mpr rfl)
  · have hzw := (isSL_cons_iff z w).mp ((isNF_tcCons_iff z w).mp hγ).1
    rw [iltb_cons_one] at hlt
    exact W_cons hγ (ih z (hd_lt_tcCons z w) hzw.1
      (fun g hg => hd g ((iinE_tcCons_iff g z w).mpr (Or.inl hg))) hlt)

/-! ### The tower of jumps above `Ω` (Arai, Lemmas 1.31, 1.32) -/

/-- `TI_M(β, F)`: if `F` is progressive on the distinguished class `M = D_W` (Arai,
Definition 1.27), it holds on every element of `M` below `β`. -/
def TIup (β : N) (F : N → Prop) : Prop := ProgD W F → ∀ ξ, Dom W ξ → iltb ξ β = 1 → F ξ

/-- The code of `Ω + 1 = ⟨Ω, 0⟩`. -/
noncomputable def omegaSucc : N := tcCons 1 (tcCons 0 0)

omit [Structure LXI N] [ArithStd N] [N↓[LXI] ⊧* ID1Acc precC] in
theorem isNF_omegaSucc : isNF (omegaSucc : N) := by
  refine (isNF_tcCons_iff 1 (tcCons 0 0)).mpr ⟨(isSL_cons_iff _ _).mpr ⟨?_, ?_, ?_⟩,
    fun h => tcCons_ne_zero 0 0 h.1⟩
  · simp [isNF, isNFb]
  · exact (isSL_cons_iff 0 0).mpr ⟨by simp [isNF, isNFb], isSL_zero, Or.inl rfl⟩
  · exact Or.inr (by rw [tcHd_tcCons]; exact ige_zero_right 1)

/-- **TI on `M` up to `Ω + 1`**, from the induction scheme of `I`: below `Ω` the class `M`
lies in `W` (`W_of_dist_lt_one`). -/
theorem ti_base {F : N → Prop} (hF : LXI.DefinablePred F) : TIup omegaSucc F := by
  intro hP ξ hξ hlt
  have below : ∀ ζ, W ζ → Dom W ζ → F ζ :=
    W_induction (Q := fun ζ => Dom W ζ → F ζ)
      (Language.Definable.imp (dfn_pred (dfn_dom definable_imem) 0) (dfn_pred hF 0))
      (fun ζ _ ih hζ => hP ζ hζ fun ξ' hξ' hlt => ih ξ' hξ'.1 hζ.1 hlt hξ')
  have lt1 : ∀ ζ, Dom W ζ → iltb ζ 1 = 1 → F ζ := fun ζ hζ h =>
    below ζ (W_of_dist_lt_one ζ hζ.1 hζ.2 h) hζ
  rcases iltb_omega_succ_cases hξ.1 hlt with h | rfl
  · exact lt1 ξ hξ h
  · exact hP 1 hξ fun ξ' hξ' h => lt1 ξ' hξ' h

/-- **Gentzen's jump on `M`** (Arai, Lemma 1.31): TI on `M` up to a normal sum `β` for every
definable predicate gives TI on `M` up to `ω^β = ⟨β⟩` for every definable predicate. -/
theorem ti_jump {β : N} (hβ : isNF β) (hβk : kind β = 3)
    (h : ∀ F : N → Prop, LXI.DefinablePred F → TIup β F) :
    ∀ F : N → Prop, LXI.DefinablePred F → TIup (tcCons β 0) F := by
  intro F hF hP ξ hξ hlt
  have hJ : ∀ y, Dom W y → iltb y β = 1 → JF W F y :=
    h (JF W F) (dfn_jf definable_imem hF) fun y hy ih => jump_prog definable_imem hF hP y hy ih
  have hβ1 : isNF (tcCons β 0) := by
    refine (isNF_tcCons_iff β 0).mpr ⟨(isSL_cons_iff β 0).mpr ⟨hβ, isSL_zero, Or.inl rfl⟩, ?_⟩
    rintro ⟨-, hk | hk⟩ <;> rw [hβk] at hk <;> simp at hk
  have hl : iltb (itoL ξ) (tcCons β 0) = 1 := by
    have := iltb_itoL hξ.1 hβ1 hlt
    rwa [itoL_tcCons] at this
  rcases iltb_single_cases (sumK_itoL (isTerm_of_isNF hξ.1)) hl with h0 | ⟨z, w, hzw, hz⟩
  · have hξ0 : ξ = 0 := by
      by_contra hne
      exact itoL_ne_zero (isTerm_of_isNF hξ.1) hne h0
    subst hξ0
    exact hP 0 hξ fun _ _ h => absurd h (not_iltb_zero _)
  · refine holds_of_jump definable_imem hF hP hξ fun y hy hle => hJ y hy ?_
    rw [hzw, tcHd_tcCons] at hle
    exact iltb_of_le_of_lt hle hz

/-- The tower `τ_0 = Ω + 1`, `τ_{n+1} = ω^{τ_n}` (codes of `ω_n(Ω + 1)`). -/
noncomputable def tau : ℕ → N
  | 0 => omegaSucc
  | n + 1 => tcCons (tau n) 0

omit [Structure LXI N] [ArithStd N] [N↓[LXI] ⊧* ID1Acc precC] in
/-- `τ_n` is a normal sum without coefficients. -/
theorem tau_facts : ∀ n : ℕ, isNF (tau n : N) ∧ kind (tau n : N) = 3 ∧
    ∀ g : N, iinE g (tau n) ≠ 1
  | 0 => by
    refine ⟨isNF_omegaSucc, kind_tcCons _ _, fun g hg => ?_⟩
    simp only [tau, omegaSucc, iinE_tcCons_iff, iinE_zero, zero_ne_one, or_self, or_false] at hg
    rw [iinE_top g (Or.inl kind_one)] at hg
    simp at hg
  | n + 1 => by
    obtain ⟨h1, h2, h3⟩ := tau_facts n
    refine ⟨?_, kind_tcCons _ _, fun g hg => ?_⟩
    · refine (isNF_tcCons_iff _ 0).mpr ⟨(isSL_cons_iff _ 0).mpr ⟨h1, isSL_zero, Or.inl rfl⟩, ?_⟩
      rintro ⟨-, hk | hk⟩ <;> rw [h2] at hk <;> simp at hk
    · simp only [tau, iinE_tcCons_iff, iinE_zero, zero_ne_one, or_false] at hg
      exact h3 g hg

/-- **TI on `M` up to every `τ_n`** (Arai, Lemma 1.32), for every definable predicate. -/
theorem ti_tau : ∀ n : ℕ, ∀ F : N → Prop, LXI.DefinablePred F → TIup (tau n) F
  | 0 => fun _ hF => ti_base hF
  | n + 1 => ti_jump (tau_facts n).1 (tau_facts n).2.1 (ti_tau n)

/-! ### The main lemma (Arai, Lemma 1.33, for ϑ) -/

/-- **The main lemma**: if `α` is in the distinguished class and `ϑξ ∈ W` for every `ξ` of
the distinguished class below `α`, then `ϑα ∈ W`.  Every normal `γ ≺ ϑα` is shown to be in
`W` by induction on its code: for a sum, its first exponent is `≺ ϑα` (`W_cons`); for
`γ = ϑξ`, Freund's clause (ii') gives either `ξ ≺ α` with `E(ξ) ≺ ϑα` (the elements of `E(ξ)`
are smaller codes, so in `W`, and `ξ` is in the distinguished class), or `ϑξ ≼ δ` for some
`δ ∈ E(α) ⊆ W`. -/
theorem W_theta {α : N} (hα : Dom W α)
    (hyp : ∀ ξ, Dom W ξ → iltb ξ α = 1 → W (tcTheta ξ)) : W (tcTheta α) := by
  have hQ : LXI.DefinablePred fun γ : N => isNF γ → iltb γ (tcTheta α) = 1 → W γ :=
    Language.Definable.imp (dfn_sigma (k := 1) (R := fun v => isNF (v 0)) (by definability))
      (Language.Definable.imp
        (dfn_sigma (k := 1) (R := fun v => iltb (v 0) (tcTheta α) = 1) (by definability))
        (dfn_pred definable_imem 0))
  have key : ∀ γ : N, isNF γ → iltb γ (tcTheta α) = 1 → W γ := by
    refine order_induction_definable precC hQ ?_
    intro γ ih hγ hlt
    rcases nf_cases hγ with rfl | hp | ⟨z, w, rfl, -⟩
    · exact W_zero
    · rcases hp with hk | hk
      · rw [iltb_top_theta (Or.inl hk)] at hlt
        simp at hlt
      · obtain ⟨ξ, rfl⟩ : ∃ ξ, γ = tcTheta ξ := ⟨_, eq_tcTheta_of_kind hk⟩
        have hξ : isNF ξ := (isNF_tcTheta_iff ξ).mp hγ
        rcases (iltb_theta_theta_iff ξ α).mp hlt with ⟨h1, h2⟩ | ⟨g, hg, hle⟩
        · refine hyp ξ ⟨hξ, fun g hg => ?_⟩ h1
          exact ih g (lt_of_le_of_lt (le_of_iinE hg) (lt_tcTheta ξ))
            (isNF_of_iinE g ξ (nfA_of_isNF hξ) hg) (h2 g hg)
        · exact W_down_le (hα.2 g hg) (isNF_of_iinE g α (nfA_of_isNF hα.1) hg) hγ hle
    · have hzw := (isSL_cons_iff z w).mp ((isNF_tcCons_iff z w).mp hγ).1
      rw [iltb_cons_theta] at hlt
      exact W_cons hγ (ih z (hd_lt_tcCons z w) hzw.1 hlt)
  exact W_of_forall _ fun γ hγ _ hlt => key γ hγ hlt

/-- **`ϑ(τ_n) ∈ W`** for every standard `n`: the predicate `ξ ↦ ϑξ ∈ W` is progressive on the
distinguished class by the main lemma, so it holds below `τ_n` (`ti_tau`), and the main lemma
applies at `τ_n`, which has no coefficients. -/
theorem W_theta_tau (n : ℕ) : W (tcTheta (tau n : N)) := by
  have hQ : LXI.DefinablePred fun ξ : N => W (tcTheta ξ) :=
    dfn_comp definable_imem (f := fun v : Fin 1 → N => tcTheta (v 0)) (by definability)
  have hP : ProgD W (fun ξ : N => W (tcTheta ξ)) := fun ξ hξ ih => W_theta hξ ih
  have hτ := tau_facts (N := N) n
  exact W_theta ⟨hτ.1, fun g hg => absurd hg (hτ.2.2 g)⟩ (ti_tau n _ hQ hP)

end Model

end WellOrdering

end InductiveDef

end OrdinalAnalysis
