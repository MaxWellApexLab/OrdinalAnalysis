/-
  The well-ordering proof inside models of `IDw WFormWc`: the distinguished classes of all
  internal levels at once, and the simultaneous main lemma.

  Sources: W. Buchholz and W. Pohlers, *Provable wellorderings of formal theories for
  transfinitely iterated inductive definitions*, J. Symbolic Logic 43 (1978), pp. 121–123
  (Lemmas 1–3, the classes `Q`, `M`, (9)–(12), Theorems 1–3), with `σ = ω`.  The metatheoretic
  version of the same argument is `Ordinal/ThetaV/WellFoundedV.lean` (`Mall`, `Hyp`,
  `mall_of_parts`, `acc_of_lt_theta`, `W_theta`); the `ID_n` version is `IDn/WellOrdering.lean`.

  **Why a new proof.**  In a model `N` of `IDw WFormWc` the level `k` of `J(k, x)` is an element
  of `N`, and nonstandard levels occur (`ϑ₀(ϑ_k 0) ≺ ϑ₀(Ω_ω)` for every internal `k`).  `ID_n`'s
  per-level Lean recursion (`hLow_all`, `tiC_all`) is therefore unavailable.  What replaces it
  is that the level is an argument of a single binary predicate: the distinguished class
  `D_k(x) :≡ fld x ∧ ∀ j < k, E_j(x) ⊆ J(j, ·)` (`DkW`) and BP78's class
  `M(x) :≡ fld x ∧ ∀ j, E_j(x) ⊆ J(j, ·)` (`MallW`) are definable in `LXJ` with `k` a parameter,
  so induction along the codes applies to statements about all levels at once.

  **The interface** `WModel`: the arithmetic reduct of `N` is standard, and `N` satisfies the
  closure axiom, the induction scheme of `J(k, ·)` for every internal `k` and every predicate
  definable with parameters (`UpperAuxForms.closure_c_of_eval`, `ind_c_of_eval` read them off
  `N ⊧ IDw WFormWc`, `WModel.of_eval`), and order induction for definable predicates (the
  induction scheme of `paLXJ`, read by the `IDw/Lift` port as in `IDn.Lift`).

  Contents (proved here):

  * order-free facts about coefficient and argument sets (`cw_iinE_trans`, `cw_iinE_lower`,
    `cw_iinE_of_iinG`, `cw_iinG_trans`, `cw_iinG_of_iinE`);
  * definability in `LXJ` (`WModel.dfn_arith`, `dfn_Jm`, `dfn_coef`, `dfn_DkW`, `dfn_MallW`);
  * (BP78 (6)) `W_sub`, `W_down`; `W_zero`; `W_of_mem_E`;
  * **(BP78 (11), the main lemma, simultaneously in the internal level)** `W_theta`: if
    `x ∈ M` and `ϑ_i ξ ∈ J(i, ·)` for every `ξ ∈ M` below `x` and every level `i` with `ϑ_i ξ` in
    the field, then `ϑ_k x ∈ J(k, ·)` for every level `k` with `ϑ_k x` in the field.  Order
    induction on the code of `γ ≺ ϑ_k x`, `γ ∈ D_k`; the one new case `γ = ϑ_k ξ`, `ξ ≺ x`,
    needs `ξ ∈ M`, which is `mall_of_parts` (order induction along `G_k(ξ)`);
  * (BP78 Theorem 2) `W_theta_zero_of_TI`: transfinite induction on `M` up to `c ∈ M` gives
    `ϑ₀ c ∈ J(0, ·)`.

  The three lemmas the main lemma uses and that are proved elsewhere (the skeleton
  `IDw/_draft/WellOrderingW_skel.lean`) are explicit hypotheses, stated once as `Prop`s:
  `ConsStmt` (BP78 Lemma 1, sums; Gentzen's jump on `D_k`), `MonoStmt` (BP78 Lemma 2,
  `J(j, ·) ⊆ J(k, ·)` for `j ≤ k`), `OmegaStmt` (BP78 Lemma 3, `Ω_{j+1} ∈ J(k, ·)` for `j < k`).
-/
import OrdinalAnalysis.IDw.UpperAuxCodes
import OrdinalAnalysis.IDw.UpperAuxForms
import OrdinalAnalysis.IDw.Internal.JumpList

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OrdinalAnalysis.IDw.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.IDw.Internal
open OrdinalAnalysis.ID1.Internal (bor band beq bor_eq_one band_eq_one beq_eq_one)

/-! ### Coefficient and argument sets (inside models of `IΣ₁`) -/

section Codes

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **`E_j(g) ⊆ E_j(c)` for `g ∈ E_k(c)`, `j ≤ k`** (`ThetaVTerm.mem_E_of_mem_E`). -/
lemma cw_iinE_trans {j k : V} (hjk : j ≤ k) :
    ∀ c : V, ∀ g h, iinE k g c = 1 → iinE j h g = 1 → iinE j h c = 1 := iinE_trans hjk

/-- **A coefficient of level `j` whose own level is `≤ k ≤ j` is a coefficient of level `k`**
(`ThetaVTerm.mem_E_of_mem_E_of_le`). -/
lemma cw_iinE_lower {k j : V} (hkj : k ≤ j) :
    ∀ c : V, ∀ g, iinE j g c = 1 → tcLev g ≤ k → iinE k g c = 1 := by
  intro c
  induction c using ISigma1.pi1_order_induction
  · definability
  case ind c ih =>
    intro g hg hl
    rcases code_cases c with rfl | ⟨i, rfl⟩ | ⟨i, a, rfl⟩ | ⟨x, t, rfl⟩ | hc
    · simp at hg
    · simp at hg
    · by_cases hi : i ≤ j
      · rw [iinE_theta_le_iff hi] at hg
        subst hg
        simp only [tcLev_tcTheta] at hl
        exact (iinE_theta_le_iff hl).mpr rfl
      · have hji : j < i := not_le.mp hi
        rw [iinE_tcTheta_of_lt hji] at hg
        rw [iinE_tcTheta_of_lt (lt_of_le_of_lt hkj hji)]
        exact ih a (arg_lt_tcTheta i a) g hg hl
    · rw [iinE_cons_iff] at hg ⊢
      rcases hg with hg | hg
      · exact Or.inl (ih x (hd_lt_tcCons x t) g hg hl)
      · exact Or.inr (ih t (tl_lt_tcCons x t) g hg hl)
    · rw [iinE_kind_four j g hc] at hg; simp at hg

/-- **The coefficients of level `j ≤ k` of a member of `G_k(c)` are coefficients of `c`**
(`ThetaVTerm.mem_E_of_mem_G`). -/
lemma cw_iinE_of_iinG {j k : V} (hjk : j ≤ k) :
    ∀ c : V, ∀ z g, iinG k z c = 1 → iinE j g z = 1 → iinE j g c = 1 := by
  intro c
  induction c using ISigma1.pi1_order_induction
  · definability
  case ind c ih =>
    intro z g hz hg
    rcases code_cases c with rfl | ⟨i, rfl⟩ | ⟨i, a, rfl⟩ | ⟨x, t, rfl⟩ | hc
    · simp at hz
    · simp at hz
    · by_cases hi : k < i
      · rw [iinG_theta_lt_iff hi] at hz
        rw [iinE_tcTheta_of_lt (lt_of_le_of_lt hjk hi)]
        rcases hz with rfl | hz
        · exact hg
        · exact ih a (arg_lt_tcTheta i a) z g hz hg
      · rw [iinG_tcTheta_of_le (not_lt.mp hi)] at hz; simp at hz
    · rw [iinG_cons_iff] at hz
      rw [iinE_cons_iff]
      rcases hz with hz | hz
      · exact Or.inl (ih x (hd_lt_tcCons x t) z g hz hg)
      · exact Or.inr (ih t (tl_lt_tcCons x t) z g hz hg)
    · rw [iinG_kind_four k z hc] at hz; simp at hz

/-- **`G_k` is transitive** (`ThetaVTerm.mem_G_of_mem_G`). -/
lemma cw_iinG_trans (k : V) :
    ∀ c : V, ∀ d y, iinG k d c = 1 → iinG k y d = 1 → iinG k y c = 1 := iinG_trans k

/-- **The argument of a coefficient `ϑ_i d ∈ E_i(c)` is in `G_k(c)` for `k < i`**
(`ThetaVTerm.mem_G_of_mem_E`). -/
lemma cw_iinG_of_iinE {k i : V} (hki : k < i) :
    ∀ c : V, ∀ d, iinE i (tcTheta i d) c = 1 → iinG k d c = 1 := iinG_of_iinE hki

lemma isNF_zero' : isNF (0 : V) := by simp [isNF, isNFb]

end Codes

/-! ### The model -/

section Model

variable {N : Type} [ORingStructure N] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [s : Structure LXJ N]

variable (N) in
/-- **A model of `IDw WFormWc`, as the well-ordering proof uses it**: standard arithmetic, the
closure axiom and the induction scheme of every internal level `k` (for definable predicates),
read with the internal order (`AccW`), and order induction for definable predicates. -/
structure WModel : Prop where
  arith : s.lMap toLXJ = Arithmetic.standardModel N
  closure : ∀ k x : N, AccW k (Jm k) x → Jm k x
  ind : ∀ (k : N) {P : N → Prop}, LXJ.DefinablePred P → (∀ x, AccW k P x → P x) →
    ∀ x, Jm k x → P x
  oind : ∀ {P : N → Prop}, LXJ.DefinablePred P → (∀ x, (∀ y < x, P y) → P x) → ∀ x, P x

/-- `WModel` from the axioms of `IDw WFormWc` (`UpperAuxForms`) and order induction. -/
theorem WModel.of_eval (hS : s.lMap toLXJ = Arithmetic.standardModel N)
    (hcl : Semiformula.Eval (s := s) ![] Empty.elim (closureAxJ WFormWc))
    (hind : ∀ F, Semiformula.Eval (s := s) ![] Empty.elim (indAxJ WFormWc F))
    (hoind : ∀ {P : N → Prop}, LXJ.DefinablePred P → (∀ x, (∀ y < x, P y) → P x) → ∀ x, P x) :
    WModel N :=
  ⟨hS, closure_c_of_eval hS hcl, fun k _ hP h => ind_c_of_eval hS hind k hP h, hoind⟩

/-- BP78's `M`: every coefficient of every level is distinguished. -/
def MallW (x : N) : Prop := ∀ j g, iinE j g x = 1 → Jm j g

/-- **The hypothesis of the main lemma at `x`**: the collapses, of every level, of the smaller
members of `M` are distinguished. -/
def HypW (x : N) : Prop :=
  ∀ ξ, fldW ξ → MallW ξ → iltb ξ x = 1 → ∀ i, fldW (tcTheta i ξ) → Jm i (tcTheta i ξ)

/-- The coefficient condition for the levels satisfying `B`. -/
def CoefW (B : N → Prop) (x : N) : Prop := ∀ j, B j → ∀ g, iinE j g x = 1 → Jm j g

/-! #### Definability -/

variable (M : WModel N)
include M

theorem WModel.dfn_arith {k : ℕ} {R : (Fin k → N) → Prop} {ℌ : HierarchySymbol}
    (h : ℌ.Definable R) : LXJ.Definable R := by
  obtain ⟨φ, hφ⟩ := h.definable
  refine ⟨Semiformula.lMap toLXJ φ.val, fun v => ?_⟩
  rw [Semiformula.eval_lMap, M.arith]
  exact HierarchySymbol.IsDefinedByWithParam.df hφ v

omit M in
theorem dfn_forall {m : ℕ} {R : (Fin (m + 1) → N) → Prop} (h : LXJ.Definable R) :
    LXJ.Definable fun v : Fin m → N => ∀ x, R (x :> v) := by
  refine Language.Definable.all ?_
  refine Language.Definable.of_iff h fun w => ?_
  rw [show (w 0 :> fun x => w x.succ) = w from Matrix.cons_head_tail w]

omit M in
theorem dfn_pred {m : ℕ} {Q : N → Prop} (hQ : LXJ.DefinablePred Q) (i : Fin m) :
    LXJ.Definable fun v : Fin m → N => Q (v i) :=
  Language.Definable.of_iff (hQ.retraction ![i]) fun v => by simp

omit M in
theorem dfn_Jm_rel : LXJ.DefinableRel (Jm (s := s)) :=
  ⟨Jat #0 #1, fun v => by rw [eval_Jat_Jm]; rfl⟩

theorem dfn_Jm {m : ℕ} {a b : (Fin m → N) → N} (ha : 𝚺₁.DefinableFunction a)
    (hb : 𝚺₁.DefinableFunction b) : LXJ.Definable fun v => Jm (a v) (b v) :=
  Language.DefinableRel.comp (hP := dfn_Jm_rel) (M.dfn_arith ha) (M.dfn_arith hb)

theorem dfn_coef {B : N → Prop} (hB : 𝚺₁.DefinablePred B) :
    LXJ.DefinablePred (CoefW B) := by
  have h3 : LXJ.Definable fun u : Fin 3 → N => iinE (u 1) (u 0) (u 2) = 1 → Jm (u 1) (u 0) :=
    Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by definability))
      (dfn_Jm M (a := fun u => u 1) (b := fun u => u 0) (by definability) (by definability))
  have h2 := dfn_forall h3
  have h2' : LXJ.Definable fun w : Fin 2 → N => B (w 0) → ∀ g, iinE (w 0) g (w 1) = 1 → Jm (w 0) g :=
    Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by definability))
      (Language.Definable.of_iff h2 fun w => by simp)
  exact Language.Definable.of_iff (dfn_forall h2') fun v => by simp [CoefW]

theorem dfn_DkW (k : N) : LXJ.DefinablePred (DkW (s := s) k) := by
  have h1 : LXJ.DefinablePred fun x : N => fldW x :=
    M.dfn_arith (ℌ := 𝚺₁) (by unfold fldW; definability)
  exact Language.Definable.of_iff
    (Language.Definable.and h1 (dfn_coef M (B := fun j => j < k) (by definability)))
    fun v => Iff.rfl

theorem dfn_MallW : LXJ.DefinablePred (MallW (s := s)) :=
  Language.Definable.of_iff (dfn_coef M (B := fun _ => True) (by definability))
    fun v => by simp [MallW, CoefW]

/-! #### The axioms at work (BP78 (6)) -/

/-- `J(k, ·) ⊆ D_k ∩ Ω_{k+1}`. -/
theorem W_sub {k x : N} (hx : Jm k x) : DkW k x ∧ iltb x (tcOmega k) = 1 := by
  have hP : LXJ.DefinablePred fun x : N => DkW k x ∧ iltb x (tcOmega k) = 1 :=
    Language.Definable.and (dfn_DkW M k) (M.dfn_arith (ℌ := 𝚺₁) (by definability))
  exact M.ind k hP (fun x h => ⟨h.1, h.2.1⟩) x hx

omit M in
theorem isTerm_of_fldW {x : N} (h : fldW x) : isTerm x := isTerm_of_isNF h.1

/-- **`J(k, ·)` is downward closed in `D_k`.** -/
theorem W_down {k x y : N} (hx : Jm k x) (hy : DkW k y) (hlt : iltb y x = 1) : Jm k y := by
  have hP : LXJ.DefinablePred fun x : N => ∀ y, DkW k y → iltb y x = 1 → Jm k y := by
    have h : LXJ.Definable fun u : Fin 2 → N => DkW k (u 0) → iltb (u 0) (u 1) = 1 → Jm k (u 0) :=
      Language.Definable.imp (dfn_pred (dfn_DkW M k) 0)
        (Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by definability))
          (dfn_Jm M (a := fun _ => k) (b := fun u => u 0) (by definability) (by definability)))
    exact Language.Definable.of_iff (dfn_forall h) fun v => by simp
  refine M.ind k hP (fun x hA y hy hlt => ?_) x hx y hy hlt
  obtain ⟨hxD, hxΩ, IH⟩ := hA
  refine M.closure k y ⟨hy, ?_, fun z hz hzy => IH y hy hlt z hz hzy⟩
  exact iltb_trans (isTerm_of_fldW hy.1) (isTerm_of_fldW hxD.1) (isTerm_tcOmega k) hlt hxΩ

theorem W_down_le {k x y : N} (hx : Jm k x) (hy : DkW k y) (hle : iltb y x = 1 ∨ y = x) :
    Jm k y := by
  rcases hle with h | rfl
  · exact W_down M hx hy h
  · exact hx

omit M in
theorem dkW_zero (k : N) : DkW k (0 : N) :=
  ⟨⟨isNF_zero', isDom_at_zero⟩, fun _ _ δ h => by simp at h⟩

/-- `0 ∈ J(k, ·)`. -/
theorem W_zero (k : N) : Jm k (0 : N) :=
  M.closure k 0 ⟨dkW_zero k, iltb_zero_pos (tcOmega_ne_zero k),
    fun z _ h => absurd h (not_iltb_zero_right z)⟩

/-- The level-`k` coefficients of a member of `J(k, ·)` are in `J(k, ·)`. -/
theorem W_of_mem_E {k y g : N} (hy : Jm k y) (hg : iinE k g y = 1) : Jm k g := by
  obtain ⟨hyD, -⟩ := W_sub M hy
  have hgD : DkW k g :=
    ⟨⟨isNF_of_iinE k g y (nfA_of_isNF hyD.1.1) hg, isDom_of_iinE k g y hyD.1.2 hg⟩,
      fun i hi h hh => hyD.2 i hi h (cw_iinE_trans (le_of_lt hi) y g h hg hh)⟩
  exact W_down_le M hy hgD (ile_of_iinE hyD.1.1 hg)

end Model

/-! ### The main lemma (BP78 (11)), simultaneously in the internal level -/

section Main

variable {N : Type} [ORingStructure N] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [s : Structure LXJ N]

variable (N) in
/-- **BP78 Lemma 1** (sums): a normal sum of `D_k` below `Ω_{k+1}` is in `J(k, ·)` once its
first entry is.  (Gentzen's jump on `D_k`; the skeleton's `W_cons`.) -/
def ConsStmt : Prop :=
  ∀ k z w : N, DkW k (tcCons z w) → Jm k z → iltb (tcCons z w) (tcOmega k) = 1 →
    Jm k (tcCons z w)

variable (N) in
/-- **BP78 Lemma 2**: `J(j, ·) ⊆ J(k, ·)` for `j ≤ k`. -/
def MonoStmt : Prop := ∀ j k y : N, j ≤ k → Jm j y → Jm k y

variable (N) in
/-- **BP78 Lemma 3**: `Ω_{j+1} ∈ J(k, ·)` for `j < k`. -/
def OmegaStmt : Prop := ∀ j k : N, j < k → Jm k (tcOmega j)

variable (M : WModel N) (hMono : MonoStmt N)
include M

theorem dfn_mallParts (k x : N) : LXJ.DefinablePred fun ξ : N =>
    fldW ξ → CoefW (fun j => j ≤ k) ξ → (∀ ζ, iinG k ζ ξ = 1 → iltb ζ x = 1) → MallW ξ := by
  have hG : LXJ.DefinablePred fun ξ : N => ∀ ζ, iinG k ζ ξ = 1 → iltb ζ x = 1 :=
    M.dfn_arith (ℌ := 𝚷₁) (by definability)
  exact Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by unfold fldW; definability))
    (Language.Definable.imp (dfn_coef M (B := fun j => j ≤ k) (by definability))
      (Language.Definable.imp hG (dfn_MallW M)))

include hMono in
/-- **`M` from its lower part** (the only use of the domain condition): a member of the field
whose coefficients of level `≤ k` are distinguished, and whose higher-collapse arguments `G_k`
lie below `x`, is in `M`, given the hypothesis of the main lemma at `x`.  Order induction on the
code of `ξ`: a coefficient `ϑ_i d` of level `i > k` has `d ∈ G_k(ξ)`, a smaller code. -/
theorem mall_of_parts {x : N} (H : HypW x) (k : N) :
    ∀ ξ, fldW ξ → CoefW (fun j => j ≤ k) ξ → (∀ ζ, iinG k ζ ξ = 1 → iltb ζ x = 1) →
      MallW ξ := by
  refine M.oind (dfn_mallParts M k x) ?_
  intro ξ ih hξ hlow hG j g hg
  rcases le_or_gt j k with hjk | hkj
  · exact hlow j hjk g hg
  obtain ⟨i, d, rfl, hij⟩ := iinE_shape hg
  rcases le_or_gt i k with hik | hki
  · exact hMono k j _ (le_of_lt hkj)
      (hlow k le_rfl _ (cw_iinE_lower (le_of_lt hkj) ξ _ hg (by simpa using hik)))
  · have hgi : iinE i (tcTheta i d) ξ = 1 := cw_iinE_lower hij ξ _ hg (by simp)
    have hd : iinG k d ξ = 1 := cw_iinG_of_iinE hki ξ d hgi
    have hdN : isNF d := isNF_of_iinG k d ξ (nfA_of_isNF hξ.1) hd
    have hdD : isDom d := isDom_of_iinG k d ξ hξ.2 hd
    have hdM : MallW d := ih d (iinG_lt k d ξ hd) ⟨hdN, hdD⟩
      (fun j' hj' g' hg' => hlow j' hj' g' (cw_iinE_of_iinG hj' ξ d g' hd hg'))
      (fun ζ hζ => hG ζ (cw_iinG_trans k ξ d ζ hd hζ))
    have hgf : fldW (tcTheta i d) :=
      ⟨isNF_of_iinE j _ ξ (nfA_of_isNF hξ.1) hg, isDom_of_iinE j _ ξ hξ.2 hg⟩
    exact hMono i j _ hij (H d ⟨hdN, hdD⟩ hdM (hG d hd) i hgf)

theorem dfn_below (k x : N) : LXJ.DefinablePred fun γ : N =>
    DkW k γ → iltb γ (tcTheta k x) = 1 → Jm k γ :=
  Language.Definable.imp (dfn_pred (dfn_DkW M k) 0)
    (Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by definability))
      (dfn_Jm M (a := fun _ => k) (b := fun u => u 0) (by definability) (by definability)))

include hMono in
/-- **The main lemma (BP78 (11)), simultaneously in the internal level `k`**: if `x ∈ M` and
the collapses of the smaller members of `M` are distinguished, then `ϑ_k x ∈ J(k, ·)` for every
`k` with `ϑ_k x` in the field.  Every `γ ∈ D_k` below `ϑ_k x` is in `J(k, ·)`, by order induction
on the code of `γ`. -/
theorem W_theta (hCons : ConsStmt N) (hOm : OmegaStmt N) {x : N} (hx : fldW x)
    (hM : MallW x) (H : HypW x) (k : N) (hk : fldW (tcTheta k x)) : Jm k (tcTheta k x) := by
  have hxT : isTerm x := isTerm_of_fldW hx
  have key : ∀ γ, DkW k γ → iltb γ (tcTheta k x) = 1 → Jm k γ := by
    refine M.oind (dfn_below M k x) ?_
    intro γ ih hγ hlt
    have hγN : isNF γ := hγ.1.1
    rcases nfA_cases (nfA_of_isNF hγN) with
      rfl | ⟨j, rfl⟩ | ⟨j, ξ, rfl, hξN⟩ | ⟨z, w, rfl, hzN, -, -, -⟩ | rfl
    · exact W_zero M k
    · exact hOm j k ((iltb_Omega_theta_iff j k x).mp hlt)
    · have hξT : isTerm ξ := isTerm_of_isNF hξN
      rcases (iltb_theta_theta_iff' x hξT).mp hlt with hjk | ⟨hjk, ⟨h1, h2⟩ | ⟨g, hg, hle⟩⟩
      · -- a collapse of lower level: it is its own coefficient of level `j < k`
        have hself : iinE j (tcTheta j ξ) (tcTheta j ξ) = 1 := (iinE_theta_le_iff le_rfl).mpr rfl
        exact hMono j k _ (le_of_lt hjk) (hγ.2 j hjk _ hself)
      · -- the new case: `ξ ≺ x` and `E_k(ξ) ≺ ϑ_k x`
        subst hjk
        obtain ⟨hξD, hξG⟩ := (isDom_tcTheta_iff j ξ).mp hγ.1.2
        have hlow : CoefW (fun j' => j' ≤ j) ξ := by
          intro j' hj' g hg
          rcases lt_or_eq_of_le hj' with hj' | rfl
          · exact hγ.2 j' hj' g (by rw [iinE_tcTheta_of_lt hj']; exact hg)
          · have hgN : isNF g := isNF_of_iinE j' g ξ (nfA_of_isNF hξN) hg
            have hgD : isDom g := isDom_of_iinE j' g ξ hξD hg
            refine ih g (lt_of_le_of_lt (iinE_le hg) (arg_lt_tcTheta j' ξ))
              ⟨⟨hgN, hgD⟩, fun i hi h hh => hγ.2 i hi h ?_⟩ (h2 g hg)
            rw [iinE_tcTheta_of_lt hi]
            exact cw_iinE_trans (le_of_lt hi) ξ g h hg hh
        have hG : ∀ ζ, iinG j ζ ξ = 1 → iltb ζ x = 1 := fun ζ hζ =>
          iltb_trans (isTerm_of_isNF (isNF_of_iinG j ζ ξ (nfA_of_isNF hξN) hζ)) hξT hxT
            (hξG ζ hζ) h1
        have hξM : MallW ξ := mall_of_parts M hMono H j ξ ⟨hξN, hξD⟩ hlow hG
        exact H ξ ⟨hξN, hξD⟩ hξM h1 j hγ.1
      · -- below a level-`k` coefficient of `x`
        subst hjk
        exact W_down_le M (hM j g hg) hγ hle
    · have hlt' : iltb z (tcTheta k x) = 1 := by
        rw [← iltb_cons_prin z w (Or.inr (Or.inl (kind_tcTheta k x)))]; exact hlt
      have hzD : DkW k z :=
        ⟨⟨hzN, ((isDom_tcCons_iff z w).mp hγ.1.2).1⟩,
          fun j hj δ hδ => hγ.2 j hj δ ((iinE_cons_iff j δ z w).mpr (Or.inl hδ))⟩
      have hz := ih z (hd_lt_tcCons z w) hzD hlt'
      refine hCons k z w hγ hz ?_
      exact iltb_trans (isTerm_of_isNF hγN) ((isTerm_tcTheta_iff k x).mpr hxT)
        (isTerm_tcOmega k) hlt ((iltb_theta_Omega_iff k x k).mpr le_rfl)
    · rw [iltb_tcOmegaW_tcTheta] at hlt; simp at hlt
  refine M.closure k _ ⟨⟨hk, fun j hj δ hδ => hM j δ ?_⟩,
    (iltb_theta_Omega_iff k x k).mpr le_rfl, key⟩
  rwa [iinE_tcTheta_of_lt hj] at hδ

end Main

/-! ### BP78 Lemmas 2 and 3 -/

section Levels

variable {N : Type} [ORingStructure N] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [s : Structure LXJ N]
variable (M : WModel N)
include M

omit M in
theorem DkW.succ_down {k y : N} (h : DkW (k + 1) y) : DkW k y :=
  ⟨h.1, fun j hj δ hδ => h.2 j (lt_trans hj (lt_add_one k)) δ hδ⟩

/-- `J(k, ·) ∩ D_{k+1} ⊆ J(k+1, ·)` (induction of level `k`, closure of level `k+1`). -/
theorem W_step {k y : N} (hy : Jm k y) (hD : DkW (k + 1) y) : Jm (k + 1) y := by
  have hP : LXJ.DefinablePred fun y : N => DkW (k + 1) y → Jm (k + 1) y :=
    Language.Definable.imp (dfn_DkW M (k + 1))
      (dfn_Jm M (a := fun _ => k + 1) (b := fun u => u 0) (by definability) (by definability))
  refine M.ind k hP (fun y hA hD => ?_) y hy hD
  obtain ⟨hyD, hyΩ, IH⟩ := hA
  refine M.closure (k + 1) y ⟨hD, ?_, fun z hz hzy => IH z hz.succ_down hzy hz⟩
  exact iltb_trans (isTerm_of_fldW hyD.1) (isTerm_tcOmega k) (isTerm_tcOmega (k + 1)) hyΩ
    ((iltb_Omega_Omega_iff k (k + 1)).mpr (lt_add_one k))

omit M in
/-- Below `Ω_{j+1}` a normal code has coefficients of level `≤ j` only: `E_i(y) ⊆ E_j(y)` for
`j ≤ i` (`ThetaVTerm.mem_E_of_lt_Omega`). -/
theorem iinE_of_lt_Omega {j i y g : N} (hji : j ≤ i) (hy : isNF y)
    (hlt : iltb y (tcOmega j) = 1) (hg : iinE i g y = 1) : iinE j g y = 1 := by
  obtain ⟨l, d, rfl, -⟩ := iinE_shape hg
  have hgT : isTerm (tcTheta l d) := isTerm_of_isNF (isNF_of_iinE i _ y (nfA_of_isNF hy) hg)
  have hglt : iltb (tcTheta l d) (tcOmega j) = 1 :=
    iltb_of_le_of_lt hgT (isTerm_of_isNF hy) (isTerm_tcOmega j) (ile_of_iinE hy hg) hlt
  exact cw_iinE_lower hji y _ hg (by simpa using (iltb_theta_Omega_iff l d j).mp hglt)

/-- **BP78 Lemma 2**: `J(j, ·) ⊆ J(k, ·)` for `j ≤ k`, for all internal levels. -/
theorem W_mono : MonoStmt N := by
  intro j
  suffices H : ∀ k, j ≤ k → ∀ y, Jm j y → Jm k y from fun k y hjk hy => H k hjk y hy
  have hP : LXJ.DefinablePred fun k : N => j ≤ k → ∀ y, Jm j y → Jm k y := by
    have h : LXJ.Definable fun u : Fin 2 → N => Jm j (u 0) → Jm (u 1) (u 0) :=
      Language.Definable.imp
        (dfn_Jm M (a := fun _ => j) (b := fun u => u 0) (by definability) (by definability))
        (dfn_Jm M (a := fun u => u 1) (b := fun u => u 0) (by definability) (by definability))
    exact Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₀) (by definability))
      (Language.Definable.of_iff (dfn_forall h) fun v => by simp)
  refine M.oind hP ?_
  intro k ih hjk y hy
  rcases eq_or_lt_of_le hjk with rfl | hjk'
  · exact hy
  obtain ⟨k', rfl⟩ := eq_succ_of_pos (lt_of_le_of_lt zero_le hjk')
  have hjk'' : j ≤ k' := lt_succ_iff_le.mp hjk'
  have IH := ih k' (lt_add_one k') hjk''
  obtain ⟨hyD, hyΩ⟩ := W_sub M hy
  have hyk := IH y hy
  obtain ⟨hykD, -⟩ := W_sub M hyk
  refine W_step M hyk ⟨hyD.1, fun i hi δ hδ => ?_⟩
  rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with hi | rfl
  · exact hykD.2 i hi δ hδ
  · exact IH δ (W_of_mem_E M hy (iinE_of_lt_Omega hjk'' hyD.1.1 hyΩ hδ))

variable (hCons : ConsStmt N)
include hCons

/-- **BP78 Lemma 3** (with the lower levels): a normal code of `D_k` below `Ω_{k+1}` whose
level-`k` coefficients are in `J(k, ·)` is in `J(k, ·)`.  Order induction on the level, and
inside on the code. -/
theorem W_of_E : ∀ k y : N, DkW k y → iltb y (tcOmega k) = 1 →
    (∀ g, iinE k g y = 1 → Jm k g) → Jm k y := by
  have hPy : ∀ k : N, LXJ.DefinablePred fun y : N => DkW k y → iltb y (tcOmega k) = 1 →
      (∀ g, iinE k g y = 1 → Jm k g) → Jm k y := fun k => by
    have hE : LXJ.DefinablePred fun y : N => ∀ g, iinE k g y = 1 → Jm k g := by
      have h : LXJ.Definable fun u : Fin 2 → N => iinE k (u 0) (u 1) = 1 → Jm k (u 0) :=
        Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by definability))
          (dfn_Jm M (a := fun _ => k) (b := fun u => u 0) (by definability) (by definability))
      exact Language.Definable.of_iff (dfn_forall h) fun v => by simp
    exact Language.Definable.imp (dfn_DkW M k)
      (Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by definability))
        (Language.Definable.imp hE
          (dfn_Jm M (a := fun _ => k) (b := fun u => u 0) (by definability) (by definability))))
  have hPk : LXJ.DefinablePred fun k : N => ∀ y, DkW k y → iltb y (tcOmega k) = 1 →
      (∀ g, iinE k g y = 1 → Jm k g) → Jm k y := by
    have hE : LXJ.Definable fun u : Fin 3 → N => iinE (u 2) (u 0) (u 1) = 1 → Jm (u 2) (u 0) :=
      Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by definability))
        (dfn_Jm M (a := fun u => u 2) (b := fun u => u 0) (by definability) (by definability))
    have hE' : LXJ.Definable fun u : Fin 2 → N => ∀ g, iinE (u 1) g (u 0) = 1 → Jm (u 1) g :=
      Language.Definable.of_iff (dfn_forall hE) fun v => by simp
    have hD : LXJ.Definable fun u : Fin 2 → N => DkW (u 1) (u 0) := by
      have h1 : LXJ.Definable fun u : Fin 2 → N => fldW (u 0) :=
        M.dfn_arith (ℌ := 𝚺₁) (by unfold fldW; definability)
      have h3 : LXJ.Definable fun u : Fin 4 → N =>
          u 1 < u 3 → iinE (u 1) (u 0) (u 2) = 1 → Jm (u 1) (u 0) :=
        Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₀) (by definability))
          (Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by definability))
            (dfn_Jm M (a := fun u => u 1) (b := fun u => u 0) (by definability)
              (by definability)))
      have h2 := dfn_forall (dfn_forall h3)
      exact Language.Definable.of_iff (Language.Definable.and h1 h2) fun v => by
        simp [DkW]
        intro _
        exact ⟨fun h j δ hj => h j hj δ, fun h j hj δ => h j δ hj⟩
    have h : LXJ.Definable fun u : Fin 2 → N => DkW (u 1) (u 0) →
        iltb (u 0) (tcOmega (u 1)) = 1 → (∀ g, iinE (u 1) g (u 0) = 1 → Jm (u 1) g) →
          Jm (u 1) (u 0) :=
      Language.Definable.imp hD (Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by definability))
        (Language.Definable.imp hE'
          (dfn_Jm M (a := fun u => u 1) (b := fun u => u 0) (by definability) (by definability))))
    exact Language.Definable.of_iff (dfn_forall h) fun v => by simp
  refine M.oind hPk ?_
  intro k ihk
  refine M.oind (hPy k) ?_
  intro y ih hD hlt hE
  rcases nfA_cases (nfA_of_isNF hD.1.1) with
    rfl | ⟨i, rfl⟩ | ⟨i, a, rfl, -⟩ | ⟨z, w, rfl, hzN, -, -, -⟩ | rfl
  · exact W_zero M k
  · have hik : i < k := (iltb_Omega_Omega_iff i k).mp hlt
    refine M.closure k _ ⟨hD, hlt, fun z hz hzi => ?_⟩
    have hzi' : Jm i z := ihk i hik z ⟨hz.1, fun j hj δ hδ => hz.2 j (lt_trans hj hik) δ hδ⟩
      hzi (fun g hg => hz.2 i hik g hg)
    exact W_mono M i k z (le_of_lt hik) hzi'
  · have hik : i ≤ k := (iltb_theta_Omega_iff i a k).mp hlt
    exact hE _ ((iinE_theta_le_iff hik).mpr rfl)
  · have hzlt : iltb z (tcOmega k) = 1 := by
      rw [← iltb_cons_prin z w (Or.inl (kind_tcOmega k))]; exact hlt
    have hzD : DkW k z :=
      ⟨⟨hzN, ((isDom_tcCons_iff z w).mp hD.1.2).1⟩,
        fun j hj δ hδ => hD.2 j hj δ ((iinE_cons_iff j δ z w).mpr (Or.inl hδ))⟩
    exact hCons k z w hD (ih z (hd_lt_tcCons z w) hzD hzlt
      fun g hg => hE g ((iinE_cons_iff k g z w).mpr (Or.inl hg))) hlt
  · rw [iltb_tcOmegaW_tcOmega] at hlt; simp at hlt

omit M hCons in
theorem dkW_Omega (k j : N) : DkW k (tcOmega j) :=
  ⟨⟨by simp [isNF, isNFb], isDom_tcOmega j⟩, fun _ _ δ h => by simp at h⟩

/-- **BP78 Lemma 3**: `Ω_{j+1} ∈ J(k, ·)` for `j < k`. -/
theorem W_Omega : OmegaStmt N := fun j k hjk =>
  W_of_E M hCons k _ (dkW_Omega k j) ((iltb_Omega_Omega_iff j k).mpr hjk)
    fun g hg => by simp at hg

end Levels

/-! ### BP78 Theorem 2: collapsing transfinite induction on `M` -/

section Collapse

variable {N : Type} [ORingStructure N] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [s : Structure LXJ N]

/-- BP78's `M` as a class: normal domain codes all of whose coefficients are distinguished. -/
def MMW (x : N) : Prop := fldW x ∧ MallW x

/-- The collapses of `ξ`, of every level, are distinguished. -/
def ThetaIn (ξ : N) : Prop := ∀ i, fldW (tcTheta i ξ) → Jm i (tcTheta i ξ)

/-- `Prog[C, X]`. -/
def ProgW (C X : N → Prop) : Prop := ∀ x, C x → (∀ y, C y → iltb y x = 1 → X y) → X x

/-- `TI[C, c]` for every predicate definable in `LXJ` with parameters. -/
def TIW (C : N → Prop) (c : N) : Prop :=
  ∀ X : N → Prop, LXJ.DefinablePred X → ProgW C X → ∀ x, C x → iltb x c = 1 → X x

variable (M : WModel N) (hCons : ConsStmt N)
include M hCons

/-- **BP78 (11)**: `Prog[M, {x : ∀ i, ϑ_i x ∈ T → ϑ_i x ∈ J(i, ·)}]`. -/
theorem prog_thetaIn : ProgW MMW (ThetaIn (s := s)) := fun _ hx ih i hi =>
  W_theta M (W_mono M) hCons (W_Omega M hCons) hx.1 hx.2
    (fun ξ hξ hMξ hlt => ih ξ ⟨hξ, hMξ⟩ hlt) i hi

omit hCons in
theorem dfn_thetaIn : LXJ.DefinablePred (ThetaIn (s := s)) := by
  have h : LXJ.Definable fun u : Fin 2 → N =>
      fldW (tcTheta (u 0) (u 1)) → Jm (u 0) (tcTheta (u 0) (u 1)) :=
    Language.Definable.imp (M.dfn_arith (ℌ := 𝚺₁) (by unfold fldW; definability))
      (dfn_Jm M (a := fun u => u 0) (b := fun u => tcTheta (u 0) (u 1)) (by definability)
        (by definability))
  exact Language.Definable.of_iff (dfn_forall h) fun v => by simp [ThetaIn]

/-- **BP78 Theorem 2** (collapsing), at every level: transfinite induction on `M` up to `c ∈ M`
gives `ϑ_k c ∈ J(k, ·)` whenever `ϑ_k c` is in the field. -/
theorem W_theta_of_TI {c : N} (hTI : TIW MMW c) (hc : MMW c) (k : N)
    (hf : fldW (tcTheta k c)) : Jm k (tcTheta k c) :=
  prog_thetaIn M hCons c hc
    (fun ξ hξ hlt => hTI ThetaIn (dfn_thetaIn M) (prog_thetaIn M hCons) ξ hξ hlt) k hf

end Collapse

end OrdinalAnalysis.IDw.Upper
