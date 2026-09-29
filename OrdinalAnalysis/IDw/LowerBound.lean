/- Source: OrdinalAnalysis/IDn/LowerBound.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega; hand port: the embedded sentence contains `Jlev ⊤`, which is not `Σ(Ω₁)`, so it is first transferred to `I_0` by `Transfer.transfer5_bwd`). -/

/-
  The lower bound for `IDw WFormWc`: transfinite induction along the ϑ-order up to `Ω₁`, read for the
  free predicate `X`, is not provable, given `EmbedHyps WFormWc` (Freund's Theorem 6.5, uniformly)
  and the collapsing corollary `CollapseCorollary` (proved in `IDw/CollapseCorollaryW.lean`).

  Source: A. Freund, arXiv:2204.09321, Corollary 7.2 / Proposition 5.8 / Theorem 5.9;
  `OrdinalAnalysis.IDn.LowerBound` is the multi-level template.

  **The chain.**  `IDw WFormWc ⊢ TI_{Ω₁}(≺, X)` gives `IDw WFormWc ⊢ fieldInJ0` (the field below `Ω₁`
  lies in the level-`0` accessible part, `IDw/LowerBoundAux2.lean`), so by the embedding theorem
  `H ⊢^{Ω_ω·2+r}_{Ω_ω+m} embed(fieldInJ0)` for every nice `H`.

  **The one step `ID_ω` adds** (`IDn` has no analogue).  The embedded sentence mentions `Jlev ⊤ (0̄, x)`
  (`embedW : J ↦ Jlev ⊤`), and `Jlev ⊤` is never in `Σ(Ω₁)` (`not_relSigmaW_jlev_top`), so the collapsing
  theorem cannot be applied to it.  It is transferred to the level-`0` stage predicate first:
  `⊢ ¬embed(fieldInJ0), fieldI` with `fieldI = ∀x (embB(x) → I_0 x)`, by the monotone congruence lemma
  `Transfer.transfer5_bwd` for `OkBwd 0` (`Jlev ⊤ (0̄, s) ↦ I_0 s`, arithmetic literals fixed), at height
  `Ω₁ ⊕ (4 + 2c)` and cut rank `0`; a cut on `embed(fieldInJ0)` (rank `≤ Ω_ω + complexity`) then gives
  `fieldI` at cut rank `Ω_ω + m'` (`transfer_field`).  `fieldI` is `Σ(Ω₁)` (`sigmaW_fieldI`).

  Contents.

    `xFreeL_fieldInJ0`                       `fieldInJ0` mentions no `X`
    `AtomsArith`, `cdepth`, `cong_arith`     the congruence relation along an arithmetic formula
    `embB`, `fieldJ`, `fieldI`, `cong_field` **`Cong (OkBwd 0) c (embed fieldInJ0) fieldI`**
    `transfer_field`                         the transfer and the cut
    `sigmaW_fieldI`, `capAt_fieldI`          `fieldI` is `Σ(Ω₁)`; its bound at `b`
    `embed_lm`, `eval_embB_stage`            `embB` in the stage structure
    `CollapseCorollary`                      the collapsing corollary, as a proposition
    `not_derivable_fieldInJ0`                no derivation of the embedded sentence, given the corollary
    `idw_lower_bound_of`                     **the lower bound at `Ω₁`**, given `EmbedHyps` and the corollary
                                            (`idw_lower_bound`, `IDw/CollapseCorollaryW.lean`: no hypothesis)
-/
import OrdinalAnalysis.IDw.LowerBoundAux2
import OrdinalAnalysis.IDw.Embed
import OrdinalAnalysis.IDw.Transfer
import OrdinalAnalysis.IDw.Collapsing.Basic

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.IDw.Upper
open OrdinalAnalysis.IDw.Transfer (Cong OkBwd transfer5_bwd freeVariables_subst_numI
  freeVariables_rel_arg freeVariables_nrel_arg)

/-! ### `fieldInJ0` mentions no `X` -/

section XFree

variable {ξ : Type*}

theorem xFreeL_neg : ∀ {n : ℕ} (φ : Semiformula LXJ ξ n), XFreeL (∼φ) ↔ XFreeL φ
  | _, .verum => Iff.rfl
  | _, .falsum => Iff.rfl
  | _, .rel (Sum.inl _) _ => Iff.rfl
  | _, .rel (Sum.inr XJRel.X) _ => Iff.rfl
  | _, .rel (Sum.inr XJRel.J) _ => Iff.rfl
  | _, .nrel (Sum.inl _) _ => Iff.rfl
  | _, .nrel (Sum.inr XJRel.X) _ => Iff.rfl
  | _, .nrel (Sum.inr XJRel.J) _ => Iff.rfl
  | _, .and φ ψ => and_congr (xFreeL_neg φ) (xFreeL_neg ψ)
  | _, .or φ ψ => and_congr (xFreeL_neg φ) (xFreeL_neg ψ)
  | _, .all φ => xFreeL_neg φ
  | _, .exs φ => xFreeL_neg φ

theorem xFreeL_lm : ∀ {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n), XFreeL (lm φ)
  | _, .verum => trivial
  | _, .falsum => trivial
  | _, .rel _ _ => trivial
  | _, .nrel _ _ => trivial
  | _, .and φ ψ => ⟨xFreeL_lm φ, xFreeL_lm ψ⟩
  | _, .or φ ψ => ⟨xFreeL_lm φ, xFreeL_lm ψ⟩
  | _, .all φ => xFreeL_lm φ
  | _, .exs φ => xFreeL_lm φ

end XFree

theorem xFreeL_fieldInJ0 : XFreeL fieldInJ0 :=
  ⟨(xFreeL_neg _).mpr (xFreeL_lm _), trivial⟩

/-! ### The congruence relation along an arithmetic formula -/

section Cong0
variable {ξ : Type*}

/-- atoms arithmetic -/
def AtomsArith : {n : ℕ} → Semiformula LIinfW ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel (Sum.inl _) _ => True
  | _, .rel (Sum.inr _) _ => False
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr _) _ => False
  | _, .and φ ψ => AtomsArith φ ∧ AtomsArith ψ
  | _, .or φ ψ => AtomsArith φ ∧ AtomsArith ψ
  | _, .all φ => AtomsArith φ
  | _, .exs φ => AtomsArith φ

/-- depth -/
def cdepth : {n : ℕ} → Semiformula LIinfW ξ n → ℕ
  | _, .verum => 0
  | _, .falsum => 0
  | _, .rel _ _ => 0
  | _, .nrel _ _ => 0
  | _, .and φ ψ => max (cdepth φ) (cdepth ψ) + 1
  | _, .or φ ψ => max (cdepth φ) (cdepth ψ) + 1
  | _, .all φ => cdepth φ + 1
  | _, .exs φ => cdepth φ + 1

@[simp] theorem cdepth_and {n : ℕ} (φ ψ : Semiformula LIinfW ξ n) : cdepth (φ ⋏ ψ) = max (cdepth φ) (cdepth ψ) + 1 := rfl
@[simp] theorem cdepth_or {n : ℕ} (φ ψ : Semiformula LIinfW ξ n) : cdepth (φ ⋎ ψ) = max (cdepth φ) (cdepth ψ) + 1 := rfl
@[simp] theorem cdepth_all {n : ℕ} (φ : Semiformula LIinfW ξ (n + 1)) : cdepth (∀¹ φ) = cdepth φ + 1 := rfl
@[simp] theorem cdepth_exs {n : ℕ} (φ : Semiformula LIinfW ξ (n + 1)) : cdepth (∃¹ φ) = cdepth φ + 1 := rfl
@[simp] theorem atomsArith_and {n : ℕ} (φ ψ : Semiformula LIinfW ξ n) : AtomsArith (φ ⋏ ψ) ↔ AtomsArith φ ∧ AtomsArith ψ := Iff.rfl
@[simp] theorem atomsArith_or {n : ℕ} (φ ψ : Semiformula LIinfW ξ n) : AtomsArith (φ ⋎ ψ) ↔ AtomsArith φ ∧ AtomsArith ψ := Iff.rfl
@[simp] theorem atomsArith_all {n : ℕ} (φ : Semiformula LIinfW ξ (n + 1)) : AtomsArith (∀¹ φ) ↔ AtomsArith φ := Iff.rfl
@[simp] theorem atomsArith_exs {n : ℕ} (φ : Semiformula LIinfW ξ (n + 1)) : AtomsArith (∃¹ φ) ↔ AtomsArith φ := Iff.rfl

theorem atomsArith_rew {ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LIinfW ξ n₁ ξ₂ n₂) (φ : Semiformula LIinfW ξ n₁) :
    AtomsArith (ω ▹ φ) ↔ AtomsArith φ := by
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => simp only [LogicalConnective.HomClass.map_top]; exact Iff.rfl
  | hfalsum => simp only [LogicalConnective.HomClass.map_bot]; exact Iff.rfl
  | hrel r v =>
    rw [Semiformula.rew_rel]
    rcases r with r | r <;> exact Iff.rfl
  | hnrel r v =>
    rw [Semiformula.rew_nrel]
    rcases r with r | r <;> exact Iff.rfl
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

theorem cdepth_rew {ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LIinfW ξ n₁ ξ₂ n₂) (φ : Semiformula LIinfW ξ n₁) :
    cdepth (ω ▹ φ) = cdepth φ := by
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => simp [cdepth]
  | hfalsum => simp [cdepth]
  | hrel r v => rw [Semiformula.rew_rel]; rfl
  | hnrel r v => rw [Semiformula.rew_nrel]; rfl
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

theorem atomsArith_neg {n : ℕ} (φ : Semiformula LIinfW ξ n) (h : AtomsArith φ) : AtomsArith (∼φ) := by
  induction φ using Semiformula.rec' with
  | hverum => trivial
  | hfalsum => trivial
  | hrel r v => 
    rcases r with r | r
    · trivial
    · exact h.elim
  | hnrel r v =>
    rcases r with r | r
    · trivial
    · exact h.elim
  | hand φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | hor φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | hall φ ih => exact ih h
  | hexs φ ih => exact ih h

theorem cdepth_neg {n : ℕ} (φ : Semiformula LIinfW ξ n) : cdepth (∼φ) = cdepth φ := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => rfl
  | hnrel r v => rfl
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

end Cong0

section Cong1
variable {ξ : Type*}

theorem atomsArith_embed_lm : ∀ {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n), AtomsArith (embed (lm φ))
  | _, .verum => trivial
  | _, .falsum => trivial
  | _, .rel _ _ => trivial
  | _, .nrel _ _ => trivial
  | _, .and φ ψ => ⟨atomsArith_embed_lm φ, atomsArith_embed_lm ψ⟩
  | _, .or φ ψ => ⟨atomsArith_embed_lm φ, atomsArith_embed_lm ψ⟩
  | _, .all φ => atomsArith_embed_lm φ
  | _, .exs φ => atomsArith_embed_lm φ

end Cong1


/-- **`embed` of the arithmetic body of `fieldInJ0`** (one free slot). -/
def embB : Semiformula LIinfW ℕ 1 :=
  embed (Rewriting.emb (lm (belowC orderFormulas (ThetaVNoteD.Omega 0))) : Semiformula LXJ ℕ 1)

theorem atomsArith_embB : AtomsArith embB := by
  unfold embB embed
  rw [Semiformula.lMap_emb]
  exact (atomsArith_rew _ _).mpr (atomsArith_embed_lm _)



theorem cong_arith_aux (k : ℕ) : ∀ (n : ℕ) (ψ : Proposition LIinfW), cdepth ψ < n → AtomsArith ψ →
    ψ.freeVariables = ∅ → Cong (OkBwd k) (cdepth ψ) ψ ψ
  | 0, _, hn, _, _ => absurd hn (Nat.not_lt_zero _)
  | _ + 1, .verum, _, _, _ => Cong.verum
  | _ + 1, .falsum, _, _, _ => Cong.falsum
  | _ + 1, .rel (Sum.inl r) v, _, _, hc =>
      Cong.atom (Or.inl ⟨⟨_, r, v, Or.inl rfl, freeVariables_rel_arg hc⟩, rfl⟩)
  | _ + 1, .rel (Sum.inr r) v, _, h, _ => h.elim
  | _ + 1, .nrel (Sum.inl r) v, _, _, hc =>
      Cong.atom (Or.inl ⟨⟨_, r, v, Or.inr rfl, freeVariables_nrel_arg hc⟩, rfl⟩)
  | _ + 1, .nrel (Sum.inr r) v, _, h, _ => h.elim
  | n + 1, .and φ ψ, hn, h, hc => by
      have hc' : φ.freeVariables ∪ ψ.freeVariables = ∅ := hc
      rw [Finset.union_eq_empty] at hc'
      have hn' : max (cdepth φ) (cdepth ψ) < n := by
        have : max (cdepth φ) (cdepth ψ) + 1 < n + 1 := hn
        omega
      exact Cong.and (cong_arith_aux k n φ (lt_of_le_of_lt (le_max_left _ _) hn') h.1 hc'.1)
        (cong_arith_aux k n ψ (lt_of_le_of_lt (le_max_right _ _) hn') h.2 hc'.2)
  | n + 1, .or φ ψ, hn, h, hc => by
      have hc' : φ.freeVariables ∪ ψ.freeVariables = ∅ := hc
      rw [Finset.union_eq_empty] at hc'
      have hn' : max (cdepth φ) (cdepth ψ) < n := by
        have : max (cdepth φ) (cdepth ψ) + 1 < n + 1 := hn
        omega
      exact Cong.or (cong_arith_aux k n φ (lt_of_le_of_lt (le_max_left _ _) hn') h.1 hc'.1)
        (cong_arith_aux k n ψ (lt_of_le_of_lt (le_max_right _ _) hn') h.2 hc'.2)
  | n + 1, .all φ, hn, h, hc => by
      have hc' : φ.freeVariables = ∅ := hc
      refine Cong.all (fun m => ?_)
      have := cong_arith_aux k n (φ/[numI m])
        (by rw [cdepth_rew]; have : cdepth φ + 1 < n + 1 := hn; omega)
        ((atomsArith_rew _ _).mpr h) (freeVariables_subst_numI φ hc' m)
      rwa [cdepth_rew] at this
  | n + 1, .exs φ, hn, h, hc => by
      have hc' : φ.freeVariables = ∅ := hc
      refine Cong.exs (fun m => ?_)
      have := cong_arith_aux k n (φ/[numI m])
        (by rw [cdepth_rew]; have : cdepth φ + 1 < n + 1 := hn; omega)
        ((atomsArith_rew _ _).mpr h) (freeVariables_subst_numI φ hc' m)
      rwa [cdepth_rew] at this

theorem cong_arith (k : ℕ) (ψ : Proposition LIinfW) (h : AtomsArith ψ) (hc : ψ.freeVariables = ∅) :
    Cong (OkBwd k) (cdepth ψ) ψ ψ :=
  cong_arith_aux k (cdepth ψ + 1) ψ (Nat.lt_succ_self _) h hc

theorem embB_closed : embB.freeVariables = ∅ := by simp [embB, embed]

def fieldJ : Proposition LIinfW := ∀¹ (embB 🡒 jlevAt ⊤ ((0 : ℕ) : Semiterm LIinfW ℕ 1) #0)
def fieldI : Proposition LIinfW := ∀¹ (embB 🡒 IOmegaAt 0 #0)

theorem subst_jlev (m : ℕ) :
    (jlevAt ⊤ ((0 : ℕ) : Semiterm LIinfW ℕ 1) #0)/[numI m] = jlevAt ⊤ (numI 0) (numI m) := by
  unfold jlevAt
  refine congrArg (Semiformula.rel (L := LIinfW) (ξ := ℕ) (n := 0) (Sum.inr (IInfRelW.jlev ⊤))) ?_
  funext i
  fin_cases i
  · simp
  · simp

theorem subst_I0 (m : ℕ) : (IOmegaAt 0 (#0 : Semiterm LIinfW ℕ 1))/[numI m] = IOmegaAt 0 (numI m) := by
  unfold IOmegaAt stageAt
  refine congrArg (Semiformula.rel (L := LIinfW) (ξ := ℕ) (n := 0) (Sum.inr (IInfRelW.stage (Stage.top 0)))) ?_
  funext i
  fin_cases i
  simp

theorem cong_field : ∃ c, Cong (OkBwd 0) c fieldJ fieldI := by
  refine ⟨max (cdepth embB) 0 + 1 + 1, Cong.all fun m => ?_⟩
  have e1 : (embB 🡒 jlevAt ⊤ ((0 : ℕ) : Semiterm LIinfW ℕ 1) #0)/[numI m] =
      ∼(embB/[numI m]) ⋎ jlevAt ⊤ (numI 0) (numI m) := by
    simp only [LogicalConnective.HomClass.map_imply, subst_jlev]
    rfl
  have e2 : (embB 🡒 IOmegaAt 0 (#0 : Semiterm LIinfW ℕ 1))/[numI m] =
      ∼(embB/[numI m]) ⋎ IOmegaAt 0 (numI m) := by
    simp only [LogicalConnective.HomClass.map_imply, subst_I0]
    rfl
  rw [e1, e2]
  refine Cong.or (c₀ := cdepth embB) (c₁ := 0) ?_
    (Cong.atom (Or.inr (Or.inl ⟨numI m, numI_freeVariables m, rfl, rfl⟩)))
  have := cong_arith 0 (∼(embB/[numI m])) (atomsArith_neg _ ((atomsArith_rew _ _).mpr atomsArith_embB))
    (by rw [Semiformula.freeVariables_not]; exact freeVariables_subst_numI embB embB_closed m)
  rwa [cdepth_neg, cdepth_rew] at this


theorem embed_fieldInJ0 : embed (fieldInJ0 : Proposition LXJ) = fieldJ := by
  simp [fieldInJ0, thetaX, fieldJ, embB, embed]
  unfold Jat jlevAt
  refine congrArg (Semiformula.rel (L := LIinfW) (ξ := ℕ) (n := 1) (Sum.inr (IInfRelW.jlev ⊤))) ?_
  funext i
  fin_cases i
  · simp [Semiterm.Operator.operator, Semiterm.Operator.numeral, Semiterm.Operator.Zero.term_eq]
    rfl
  · simp

/-! ### The transfer to level `0` and the cut -/

section TransferCut

variable {A : FormJ} {H : Set ThetaVNoteD → Set ThetaVNoteD}

theorem rk_lt_OmegaPlus (ψ : Proposition LIinfW) : rk ψ < OmegaPlus (ψ.complexity + 1) :=
  lt_of_le_of_lt (rk_le_OmegaW_add_ofNat ψ) (OmegaPlus_lt (Nat.lt_succ_self _))

theorem params_fieldI_sub (hH : ThetaVNoteD.NiceS H) : Stage.val '' params fieldI ⊆ H ∅ := by
  have h : params fieldI = {Stage.top 0} := by
    unfold fieldI
    rw [params_all]
    show params (∼embB ⋎ IOmegaAt 0 (#0 : Semiterm LIinfW ℕ 1)) = _
    rw [params_or, params_neg, show params embB = ∅ from params_embed _, params_IOmegaAt]
    simp
  rw [h, Set.image_singleton]
  exact Set.singleton_subset_iff.mpr (hH.Omega_mem 0)

theorem params_fieldJ : params fieldJ = ∅ := by
  rw [← embed_fieldInJ0]; exact params_embed _

/-- **The transfer and the cut** (the step `ID_ω` adds): a derivation of `embed fieldInJ0` at cut
rank `Ω_ω + m` gives one of the `Σ(Ω₁)` sentence `fieldI` at a cut rank `Ω_ω + m'`. -/
theorem transfer_field (hH : ThetaVNoteD.NiceS H) {m r : ℕ}
    (d : IDwDerivable A (OmegaPlus m) H (OmegaTwo + ThetaVNoteD.ofNat r)
      [embed (fieldInJ0 : Proposition LXJ)]) :
    ∃ (m' : ℕ) (α : ThetaVNoteD), IDwDerivable A (OmegaPlus m') H α [fieldI] := by
  rw [embed_fieldInJ0] at d
  obtain ⟨c, hc⟩ := cong_field
  have hpJ : Stage.val '' params fieldJ ⊆ H ∅ := by
    rw [params_fieldJ, Set.image_empty]; exact Set.empty_subset _
  have hpI := params_fieldI_sub hH
  have hpΓ : paramsVal [fieldI] ⊆ H ∅ := paramsVal_cons_sub hpI (by simp)
  have t := transfer5_bwd (A := A) hH 0 (Γ := []) (by simp) hc hpJ hpI
  have hn : ThetaVNoteD.nadd (ThetaVNoteD.Omega 0) (ThetaVNoteD.ofNat (4 + 2 * c)) ∈ H ∅ :=
    Transfer.nadd_Omega_mem hH 0 _
  have hα₀ : ThetaVNoteD.nadd (OmegaTwo + ThetaVNoteD.ofNat r)
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega 0) (ThetaVNoteD.ofNat (4 + 2 * c))) ∈ H ∅ :=
    hH.nadd_mem (OmegaTwo_mem hH _ _) hn
  have hα : ThetaVNoteD.nadd (ThetaVNoteD.nadd (OmegaTwo + ThetaVNoteD.ofNat r)
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega 0) (ThetaVNoteD.ofNat (4 + 2 * c))))
      (ThetaVNoteD.ofNat (0 + 1)) ∈ H ∅ := hH.nadd_mem hα₀ (hH.ofNat_mem _)
  have hm : m ≤ max m (fieldJ.complexity + 1) := le_max_left _ _
  have hrk : rk fieldJ < OmegaPlus (max m (fieldJ.complexity + 1)) :=
    lt_of_lt_of_le (rk_lt_OmegaPlus fieldJ) (OmegaPlus_le (le_max_right m (fieldJ.complexity + 1)))
  generalize max m (fieldJ.complexity + 1) = m' at hm hrk
  have hsub : ∀ Δ : Sequent LIinfW, Δ ⊆ [fieldJ, fieldI] → paramsVal Δ ⊆ H ∅ := fun Δ hΔ =>
    Transfer.paramsVal_subset fun χ hχ => by
      have := hΔ hχ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl
      · exact hpJ
      · exact hpI
  refine ⟨m', _, .cut (α₀ := ThetaVNoteD.nadd (OmegaTwo +
    ThetaVNoteD.ofNat r) (ThetaVNoteD.nadd (ThetaVNoteD.Omega 0) (ThetaVNoteD.ofNat (4 + 2 * c))))
    hα hpΓ hrk (Transfer.lt_nadd_ofNat_succ _ 0) ?_ ?_⟩
  · refine ((d.mono_rank (OmegaPlus_le hm)).mono_height
      (ThetaVNoteD.le_nadd_left _ _) hα₀).weaken_seq hH.1 ?_
      (paramsVal_cons_sub hpJ hpΓ)
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto
  · refine ((t.mono_rank (ThetaVNoteD.zero_le' _)).mono_height
      (ThetaVNoteD.le_nadd_right _ _) hα₀).weaken_seq hH.1 ?_
      (paramsVal_cons_sub (by rw [params_neg]; exact hpJ) hpΓ)
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto

end TransferCut

/-! ### `fieldI` is `Σ(Ω₁)`, and its bound at a stage `b` -/

section SigmaCap

variable {ξ : Type*}

theorem sigmaW_of_atomsArith (k : ℕ) :
    ∀ {n : ℕ} (φ : Semiformula LIinfW ξ n), AtomsArith φ → SigmaW k φ
  | _, .verum, _ => trivial
  | _, .falsum, _ => trivial
  | _, .rel (Sum.inl _) _, _ => trivial
  | _, .rel (Sum.inr _) _, h => h.elim
  | _, .nrel (Sum.inl _) _, _ => trivial
  | _, .nrel (Sum.inr _) _, h => h.elim
  | _, .and φ ψ, h => ⟨sigmaW_of_atomsArith k φ h.1, sigmaW_of_atomsArith k ψ h.2⟩
  | _, .or φ ψ, h => ⟨sigmaW_of_atomsArith k φ h.1, sigmaW_of_atomsArith k ψ h.2⟩
  | _, .all φ, h => sigmaW_of_atomsArith k φ h
  | _, .exs φ, h => sigmaW_of_atomsArith k φ h

/-- Bounding at a stage does not touch a formula whose atoms are arithmetic. -/
theorem capAt_atomsArith (k : ℕ) (b : StageAt k) :
    ∀ {n : ℕ} (φ : Semiformula LIinfW ξ n), AtomsArith φ → capAt k b φ = φ
  | _, .verum, _ => rfl
  | _, .falsum, _ => rfl
  | _, .rel (Sum.inl _) _, _ => rfl
  | _, .rel (Sum.inr _) _, h => h.elim
  | _, .nrel (Sum.inl _) _, _ => rfl
  | _, .nrel (Sum.inr _) _, h => h.elim
  | _, .and φ ψ, h => by
      show capAt k b φ ⋏ capAt k b ψ = φ ⋏ ψ
      rw [capAt_atomsArith k b φ h.1, capAt_atomsArith k b ψ h.2]
  | _, .or φ ψ, h => by
      show capAt k b φ ⋎ capAt k b ψ = φ ⋎ ψ
      rw [capAt_atomsArith k b φ h.1, capAt_atomsArith k b ψ h.2]
  | _, .all φ, h => by
      show ∀¹ capAt k b φ = ∀¹ φ
      rw [capAt_atomsArith k b φ h]
  | _, .exs φ, h => by
      show ∃¹ capAt k b φ = ∃¹ φ
      rw [capAt_atomsArith k b φ h]

end SigmaCap

theorem sigmaW_fieldI : SigmaW 0 fieldI := by
  unfold fieldI
  rw [sigmaW_all]
  exact ⟨sigmaW_of_atomsArith 0 _ (atomsArith_neg _ atomsArith_embB), le_refl _⟩

theorem capAt_fieldI (b : StageAt 0) :
    capAt 0 b fieldI = ∀¹ (embB 🡒 stageAt (⟨0, b⟩ : Stage) (#0 : Semiterm LIinfW ℕ 1)) := by
  unfold fieldI
  rw [capAt_all]
  congr 1
  show capAt 0 b (∼embB ⋎ IOmegaAt 0 (#0 : Semiterm LIinfW ℕ 1)) = ∼embB ⋎ _
  rw [capAt_or, capAt_neg, capAt_atomsArith 0 b embB atomsArith_embB, capAt_IOmegaAt]

/-! ### `embB` in the stage structure -/

section EvalEmbB

variable {ξ : Type*}

theorem embed_term_lm {n : ℕ} (t : Semiterm ℒₒᵣ ξ n) :
    Semiterm.lMap embedW (Semiterm.lMap toLXJ t) = Semiterm.lMap toLIinfW t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih =>
    simp only [Semiterm.lMap_func]
    rw [show Semiterm.lMap embedW ∘ Semiterm.lMap toLXJ ∘ v = Semiterm.lMap toLIinfW ∘ v from
      funext ih]
    rfl

/-- **`embed` on an arithmetic formula is the embedding of arithmetic into `LIinfW`.** -/
theorem embed_lm {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) :
    embed (lm φ) = Semiformula.lMap toLIinfW φ := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
    simp only [embed, lm, Semiformula.lMap_rel]
    rw [show Semiterm.lMap embedW ∘ Semiterm.lMap toLXJ ∘ v = Semiterm.lMap toLIinfW ∘ v from
      funext fun i => embed_term_lm (v i)]
    rfl
  | hnrel r v =>
    simp only [embed, lm, Semiformula.lMap_nrel]
    rw [show Semiterm.lMap embedW ∘ Semiterm.lMap toLXJ ∘ v = Semiterm.lMap toLIinfW ∘ v from
      funext fun i => embed_term_lm (v i)]
    rfl
  | hand φ ψ ihφ ihψ =>
    simp only [embed, lm, LogicalConnective.HomClass.map_and] at ihφ ihψ ⊢
    rw [ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
    simp only [embed, lm, LogicalConnective.HomClass.map_or] at ihφ ihψ ⊢
    rw [ihφ, ihψ]
  | hall φ ih =>
    simp only [embed, lm, Semiformula.lMap_all] at ih ⊢
    rw [ih]
  | hexs φ ih =>
    simp only [embed, lm, Semiformula.lMap_exs] at ih ⊢
    rw [ih]

end EvalEmbB

section StageEval

open StageSem

/-- **`embB` in the stage structure**: the field below `Ω₁`, read in `ℕ`. -/
theorem eval_embB_stage (P : ℕ → Prop) (S : Stage → Set ℕ) (x : ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := stageStrucN P S) ![x] f embB ↔
      orderFormulas.fld x ∧ orderFormulas.fld (Internal.code (ThetaVTerm.Omega 0)) ∧
        orderFormulas.lt x (Internal.code (ThetaVTerm.Omega 0)) := by
  unfold embB embed
  rw [Semiformula.lMap_emb, Semiformula.eval_emb]
  have h : Semiformula.lMap embedW (lm (belowC orderFormulas (ThetaVNoteD.Omega 0))) =
      Semiformula.lMap toLIinfW (belowC orderFormulas (ThetaVNoteD.Omega 0)) :=
    embed_lm _
  rw [h]
  show Semiformula.Eval (s := Structure.add ℒₒᵣ IInfLangW ℕ (str₂ := iinfStrucN P S)) ![x]
    Empty.elim (Semiformula.lMap (Language.Hom.add₁ ℒₒᵣ IInfLangW)
      (belowC orderFormulas (ThetaVNoteD.Omega 0))) ↔ _
  rw [Structure.eval_lMap_add₁ (str₂ := iinfStrucN P S)]
  have := eval_belowC (F := orderFormulas) (N := ℕ) (ThetaVNoteD.Omega 0) x
  rw [Internal.mc_nat] at this
  exact this

end StageEval

/-! ### The collapsing corollary, as a proposition -/

/-- **The collapsing corollary for `ID_ω`**, as a proposition (proved as `IDw.collapseCorollaryW` in
`IDw/CollapseCorollaryW.lean`, for every positive form): a `Σ(Ω₁)` sentence derivable in the nice
operator `H_0` at cut rank `Ω_ω + m` has, for some stage `b ≺ Ω₁`, a derivation of its bounded form
`φ^b` at cut rank and height `b`, in a nice operator. -/
def CollapseCorollary (A : FormJ) : Prop :=
  ∀ {m : ℕ} {φ : Proposition LIinfW}, SigmaW 0 φ → ∀ {α : ThetaVNoteD},
    IDwDerivable A (OmegaPlus m) (ThetaVNoteD.HopS ThetaVNoteD.zero) α [φ] →
    ∃ b : StageAt 0, b.1 < ThetaVNoteD.Omega 0 ∧ ∃ H : Set ThetaVNoteD → Set ThetaVNoteD,
      ThetaVNoteD.NiceS H ∧ IDwDerivable A b.1 H b.1 (Collapsing.capSeq 0 b [φ])

/-! ### No derivation of the embedded sentence -/

/-- **`fieldI^b` is false in the stage model**: the code of `b` lies below `Ω₁`, hence in the
field, and enters the stage `b` of level `0` only if `b ≺ b`. -/
theorem not_trueSN_capAt_fieldI (P : ℕ → Prop) (b : StageAt 0) (hb : b.1 < ThetaVNoteD.Omega 0) :
    ¬ StageSem.TrueSN P WFormWc (capAt 0 b fieldI) := by
  intro h
  unfold StageSem.TrueSN at h
  rw [capAt_fieldI] at h
  have h1 := (Semiformula.eval_all.mp h) (Internal.code b.1.1)
  have h2 : Semiformula.Eval (s := StageSem.stageStrucN P (StageSem.stageSetN WFormWc))
      ![Internal.code b.1.1] (fun _ => 0)
      (embB 🡒 stageAt (⟨0, b⟩ : Stage) (#0 : Semiterm LIinfW ℕ 1)) := h1
  rw [LogicalConnective.HomClass.map_imply, eval_embB_stage, StageSem.eval_stageAt] at h2
  have hmem := h2 ⟨(Internal.eval_fld_iff b.1.1).mpr b.1.2,
    (Internal.eval_fld_iff (ThetaVNoteD.Omega 0).1).mpr (ThetaVNoteD.Omega 0).2,
    (Internal.eval_lt_iff_lt b.1.1 (ThetaVNoteD.Omega 0).1).mpr hb⟩
  exact lt_irrefl b.1 ((codeAt0_mem_stageSetN_iff b b.1).mp hmem)

/-- **No derivation of the embedded `fieldInJ0`**, given the collapsing corollary (the analogue of
`IDn.not_derivable_fieldInI0`): transfer to `fieldI` (`transfer_field`), collapse, stage soundness,
irreflexivity of `≺` at the code of `b`. -/
theorem not_derivable_fieldInJ0 (hcol : CollapseCorollary WFormWc) {m r : ℕ}
    (d : ∀ H : Set ThetaVNoteD → Set ThetaVNoteD, ThetaVNoteD.NiceS H →
      IDwDerivable WFormWc (OmegaPlus m) H (OmegaTwo + ThetaVNoteD.ofNat r)
        [embed (fieldInJ0 : Proposition LXJ)]) : False := by
  obtain ⟨m', α, d'⟩ := transfer_field (ThetaVNoteD.HopS_nice ThetaVNoteD.zero)
    (d _ (ThetaVNoteD.HopS_nice ThetaVNoteD.zero))
  obtain ⟨b, hb, H, -, D⟩ := hcol sigmaW_fieldI d'
  rw [Collapsing.capSeq_singleton] at D
  obtain ⟨φ, hφ, htrue⟩ := StageSem.sound (fun _ => True) WFormWc D hb
  rw [List.mem_singleton.mp hφ] at htrue
  exact not_trueSN_capAt_fieldI (fun _ => True) b hb htrue

/-! ### The lower bound, at `Ω₁` -/

/-- **`IDw WFormWc ⊬ TI_{Ω₁}(≺, X)`**, given `EmbedHyps` and `CollapseCorollary`. -/
theorem idw_lower_bound_of (hyps : EmbedHyps WFormWc) (hcol : CollapseCorollary WFormWc) :
    ¬ IDw WFormWc ⊢ tiUptoSentence orderFormulas (ThetaVNoteD.Omega 0) := by
  intro h
  have hσ := provable_fieldInJ0_of_ti h
  obtain ⟨m, r, hmr⟩ := embedding_theorem_xfree hyps positiveP_WFormWc xFreeL_fieldInJ0 hσ
  exact not_derivable_fieldInJ0 hcol hmr

end IDw

end OrdinalAnalysis
