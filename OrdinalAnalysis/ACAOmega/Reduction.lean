/-
  The reduction lemma for `ACA_∞`, the first cut-elimination theorem
  (Afshari–Rathjen 2012, Thm 3), and the substitution provider for the raw
  instantiation.

  The architecture is that of `Omega/Reduction.lean`: both sequents are related
  to the target by `⊆`; the recursion is on the symmetric measure `β ⊕ γ`; the
  ordinal delivered is the doubled natural sum `redOrd β γ`.  Two things are
  organised differently.

  * The induction over the right derivation is done **once**, generically
    (`reduction_right`), with the seven possible principal cases handed in as
    hypotheses; each principal case of the left induction then supplies one real
    handler and six refutations by head mismatch.  The first-order file has one
    such induction per left rule.

  * There are two new principal cases, (∀₂) against (∃₂).  The (∃₂) side names
    an arithmetical witness `ψ`; the (∀₂) side has an eigenvariable derivation,
    and the substitution lemma of `Calculus.lean` turns it into a derivation of
    the instance, at the same height.  From there the shape is exactly the
    ω-rule/∃ case: two applications of the measure hypothesis and one cut on the
    instance, whose rank is strictly below that of the quantified formula
    (`rank_subst₂_lt`).  The substitution needs `ω ≤ ρ` for its rank
    bookkeeping, and `ω ≤ rank (∀² χ) ≤ ρ` supplies it.

  The substitution of `ψ` for the eigenvariable is taken from a
  `SubstProvider`, because for a normalising instantiation it is a genuinely
  different map (substitute, then normalise the fresh subformulas).  For the raw
  instantiation it is Foundation's `Rew` at every depth, built here.

  Elimination of one rank level is stated with `PredBound ρ ρ'` ("every rank
  below `ρ'` is at most `ρ`") in place of `ρ' = ρ + 1`, and the tower with an
  inductive `Chain`; this keeps all ordinal arithmetic on `NONote` out of the
  file.
-/
import OrdinalAnalysis.ACAOmega.Calculus

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA

variable {L : FirstOrder.Language}
variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

namespace OmegaDerivable₂

variable {A : Literals₂ L} {I : Instantiation₂ L}

/-! ### The substitution of a witness for the eigenvariable -/

/-- What the reduction lemma needs from an instantiation: for every arithmetical
`ψ`, a substitution family that performs `X₀ ↦ ψ` at depth `0` — it turns the
eigenvariable premise `φ.free₁ :: shift₁ Γ` into `inst₂ φ ψ :: Γ` — and is safe
at every rank `≥ ω`. -/
structure SubstProvider (A : Literals₂ L) (I : Instantiation₂ L) where
  fam : ∀ ψ : Semiformula L ℕ ℕ 0 1, Arith ψ → SubstFamily A I
  ok : ∀ (ψ : Semiformula L ℕ ℕ 0 1) (hψ : Arith ψ) (ρ : NONote), omegaN ≤ ρ → (fam ψ hψ).Ok ρ
  head : ∀ (ψ : Semiformula L ℕ ℕ 0 1) (hψ : Arith ψ) (φ : Semiproposition L 1 0),
    (fam ψ hψ).S 0 (Semiproposition.free₁ φ) = I.inst₂ φ ψ
  ctx : ∀ (ψ : Semiformula L ℕ ℕ 0 1) (hψ : Arith ψ) (γ : Proposition L),
    (fam ψ hψ).S 0 (Semiproposition.shift₁ γ) = γ

/-- **Substituting the witness into the eigenvariable derivation.** -/
theorem SubstProvider.subst_eigen (P : SubstProvider A I) {ρ : NONote} (hρ : omegaN ≤ ρ)
    {ψ : Semiformula L ℕ ℕ 0 1} (hψ : Arith ψ) {α : O} {φ : Semiproposition L 1 0}
    {Γ : SecondOrder.Sequent L}
    (h : OmegaDerivable₂ A I ρ α (Semiproposition.free₁ φ :: SecondOrder.Sequent.shift₁ Γ)) :
    OmegaDerivable₂ A I ρ α (I.inst₂ φ ψ :: Γ) := by
  have := subst_family (P.fam ψ hψ) (P.ok ψ hψ ρ hρ) h 0
  rw [List.map_cons, P.head] at this
  have e : (SecondOrder.Sequent.shift₁ Γ).map ((P.fam ψ hψ).S 0) = Γ := by
    show (Γ.map Semiproposition.shift₁).map _ = Γ
    rw [List.map_map]
    conv_rhs => rw [← List.map_id Γ]
    congr 1
    funext γ
    exact P.ctx ψ hψ γ
  rwa [e] at this

/-! #### The provider for the raw instantiation -/

/-- `ψ` with its free set variables shifted `m` times. -/
def shiftN (ψ : Semiformula L ℕ ℕ 0 1) : ℕ → Semiformula L ℕ ℕ 0 1
  | 0 => ψ
  | m + 1 => SecondOrder.Rew.shift.app (shiftN ψ m)

@[simp] theorem shiftN_zero (ψ : Semiformula L ℕ ℕ 0 1) : shiftN ψ 0 = ψ := rfl

@[simp] theorem shiftN_succ (ψ : Semiformula L ℕ ℕ 0 1) (m : ℕ) :
    shiftN ψ (m + 1) = SecondOrder.Rew.shift.app (shiftN ψ m) := rfl

theorem arith_shiftN {ψ : Semiformula L ℕ ℕ 0 1} (hψ : Arith ψ) :
    ∀ m : ℕ, Arith (shiftN ψ m)
  | 0 => hψ
  | m + 1 => arith_app _ (arith_shiftN hψ m) _ (fun X => X.elim0) (fun X => by simp)

/-- The component at the free variable `X` of the substitution `X₀ ↦ ψ` pushed
under `m` set binders: the variables below `m` are the eigenvariables of those
binders and stay; `m` itself is the substituted one; the rest are shifted
down. -/
def fvAt (ψ : Semiformula L ℕ ℕ 0 1) (m X : ℕ) : Semiformula L ℕ ℕ 0 1 :=
  if X < m then #0 ∈& X else if X = m then shiftN ψ m else #0 ∈& (X - 1)

theorem arith_fvAt {ψ : Semiformula L ℕ ℕ 0 1} (hψ : Arith ψ) (m X : ℕ) :
    Arith (fvAt ψ m X) := by
  unfold fvAt
  split_ifs
  · simp
  · exact arith_shiftN hψ m
  · simp

/-- The substitution `X₀ ↦ ψ` at depth `m`. -/
def subAt (ψ : Semiformula L ℕ ℕ 0 1) (m : ℕ) : SecondOrder.Rew L ℕ 0 ℕ 0 ℕ :=
  ⟨fun X => X.elim0, fvAt ψ m⟩

@[simp] theorem subAt_fv (ψ : Semiformula L ℕ ℕ 0 1) (m X : ℕ) :
    (subAt ψ m).fv X = fvAt ψ m X := rfl

theorem fvAt_succ_succ (ψ : Semiformula L ℕ ℕ 0 1) (m X : ℕ) :
    fvAt ψ (m + 1) (X + 1) = SecondOrder.Rew.shift.app (fvAt ψ m X) := by
  unfold fvAt
  rcases lt_trichotomy X m with h | rfl | h
  · rw [if_pos (by omega), if_pos h]
    simp
  · rw [if_neg (by omega), if_pos rfl, if_neg (by omega), if_pos rfl]
    rfl
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have e : X + 1 - 1 = X - 1 + 1 := by omega
    rw [e]
    simp

/-- The rewriting family of `X₀ ↦ ψ`, safe at the ranks `≥ ω`. -/
def subAtFamily (num : ℕ → FirstOrder.SyntacticTerm L) {ψ : Semiformula L ℕ ℕ 0 1}
    (hψ : Arith ψ) : RewFamily (Instantiation₂.raw (L := L) num) where
  Ω m := subAt ψ m
  arith_fv m X := arith_fvAt hψ m X
  free_comp m := by
    have e : (SecondOrder.Rew.free (L := L) (ξ := ℕ) (N := 0)).bv 0 = #0 ∈& 0 :=
      SecondOrder.Rew.free_bvar_last 0
    ext X
    · cases X using Fin.cases with
      | zero => simp [e, fvAt]
      | succ X => exact X.elim0
    · simp only [SecondOrder.Rew.comp_fv, SecondOrder.Rew.free_fvar, SecondOrder.Rew.app_fvar,
        subAt_fv, SecondOrder.Rew.q_fv, SecondOrder.Rew.bmap_app_eq, free_bRight_succ,
        subst_bvar_self, fvAt_succ_succ]
  shift_comp m := by
    ext X
    · exact X.elim0
    · simp only [SecondOrder.Rew.comp_fv, SecondOrder.Rew.shift_fv, SecondOrder.Rew.app_fvar,
        subAt_fv, subst_bvar_self, fvAt_succ_succ]
  nf_comm _ _ := rfl
  Ok ρ := omegaN ≤ ρ
  rank_ctrl m φ ρ hok h := by
    rcases lt_or_ge (rank φ) omegaN with h' | h'
    · exact lt_of_lt_of_le (rank_app_lt_omegaN _ (fun X => X.elim0)
        (fun X => rank_lt_omega_of_arith (arith_fvAt hψ m X)) h') hok
    · rw [rank_app_eq_of_omegaN_le _ (fun X => X.elim0)
        (fun X => rank_lt_omega_of_arith (arith_fvAt hψ m X)) h']
      exact h

theorem subAt_zero_comp_free (ψ : Semiformula L ℕ ℕ 0 1) :
    (subAt ψ 0).comp SecondOrder.Rew.free = SecondOrder.Rew.subst ![ψ] := by
  have e : (SecondOrder.Rew.free (L := L) (ξ := ℕ) (N := 0)).bv 0 = #0 ∈& 0 :=
    SecondOrder.Rew.free_bvar_last 0
  ext X
  · cases X using Fin.cases with
    | zero => simp [e, fvAt]
    | succ X => exact X.elim0
  · simp [fvAt]

theorem subAt_zero_comp_shift (ψ : Semiformula L ℕ ℕ 0 1) :
    (subAt ψ 0).comp SecondOrder.Rew.shift = SecondOrder.Rew.id := by
  ext X
  · exact X.elim0
  · simp [fvAt]

/-- **The substitution provider of the raw instantiation.** -/
def rawProvider (A : Literals₂ L) (num : ℕ → FirstOrder.SyntacticTerm L) :
    SubstProvider A (Instantiation₂.raw num) where
  fam ψ hψ := (subAtFamily num hψ).toSubstFamily A
  ok _ _ _ h := h
  head ψ hψ φ := by
    show (subAt ψ 0).app (SecondOrder.Rew.free.app φ) = φ/⟦ψ⟧
    rw [← SecondOrder.Rew.app_comp, subAt_zero_comp_free]
  ctx ψ hψ γ := by
    show (subAt ψ 0).app (SecondOrder.Rew.shift.app γ) = γ
    rw [← SecondOrder.Rew.app_comp, subAt_zero_comp_shift, SecondOrder.Rew.app_id]

/-! ### The reduction lemma -/

/-- The reduction lemma's statement below a bound on the symmetric measure,
packaged so the principal cases can take it as an argument. -/
def RedIH₂ (L : FirstOrder.Language) (A : Literals₂ L) (I : Instantiation₂ L) (ρ : NONote)
    (s : O) : Prop :=
  ∀ (β γ : O), OrdinalNotation.nadd β γ < s →
    ∀ {Γ₀ : SecondOrder.Sequent L}, OmegaDerivable₂ A I ρ β Γ₀ →
      ∀ {φ : Proposition L}, rank φ ≤ ρ →
      ∀ {Θ Δ₀ : SecondOrder.Sequent L}, Γ₀ ⊆ φ :: Θ →
        OmegaDerivable₂ A I ρ γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ →
          OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd β γ) Θ

set_option maxHeartbeats 2000000 in
/-- **The right induction.**  Given the left derivation `hd` of a sequent inside
`φ :: Θ`, and a handler for each rule that could be principal for `∼φ` on the
right, reduce against any right derivation of a sequent inside `∼φ :: Θ`. -/
theorem reduction_right {ρ : NONote} {s α : O} (ih2 : RedIH₂ L A I ρ s)
    {Γ₀ Θ : SecondOrder.Sequent L} {φ : Proposition L}
    (hd : OmegaDerivable₂ A I ρ α Γ₀) (hss : Γ₀ ⊆ φ :: Θ) (hr : rank φ ≤ ρ)
    (hAtom : ∀ {δ : O} {χ : Proposition L}, A.T χ → χ = ∼φ →
      OrdinalNotation.nadd α δ ≤ s → OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α δ) Θ)
    (hOr : ∀ {δ δ₀ : O} {ψ₁ ψ₂ : Proposition L} {Δ₁ : SecondOrder.Sequent L},
      ψ₁ ⋎ ψ₂ = ∼φ → δ₀ < δ → OrdinalNotation.nadd α δ ≤ s →
      OmegaDerivable₂ A I ρ δ₀ (ψ₁ :: ψ₂ :: Δ₁) → Δ₁ ⊆ ∼φ :: Θ →
      OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α δ) Θ)
    (hAnd : ∀ {δ δ₀ δ₁ : O} {ψ₁ ψ₂ : Proposition L} {Δ₁ : SecondOrder.Sequent L},
      ψ₁ ⋏ ψ₂ = ∼φ → δ₀ < δ → δ₁ < δ → OrdinalNotation.nadd α δ ≤ s →
      OmegaDerivable₂ A I ρ δ₀ (ψ₁ :: Δ₁) → OmegaDerivable₂ A I ρ δ₁ (ψ₂ :: Δ₁) →
      Δ₁ ⊆ ∼φ :: Θ →
      OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α δ) Θ)
    (hOmega : ∀ {δ : O} {ψ : Semiproposition L 0 1} {Δ₁ : SecondOrder.Sequent L} {f : ℕ → O},
      (∀¹ ψ) = ∼φ → (∀ n, f n < δ) → OrdinalNotation.nadd α δ ≤ s →
      (∀ n, OmegaDerivable₂ A I ρ (f n) (I.inst ψ n :: Δ₁)) → Δ₁ ⊆ ∼φ :: Θ →
      OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α δ) Θ)
    (hExs : ∀ {δ δ₀ : O} {ψ : Semiproposition L 0 1} {Δ₁ : SecondOrder.Sequent L} {n : ℕ},
      (∃¹ ψ) = ∼φ → δ₀ < δ → OrdinalNotation.nadd α δ ≤ s →
      OmegaDerivable₂ A I ρ δ₀ (I.inst ψ n :: Δ₁) → Δ₁ ⊆ ∼φ :: Θ →
      OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α δ) Θ)
    (hAll₂ : ∀ {δ δ₀ : O} {ψ : Semiproposition L 1 0} {Δ₁ : SecondOrder.Sequent L},
      (∀² ψ) = ∼φ → δ₀ < δ → OrdinalNotation.nadd α δ ≤ s →
      OmegaDerivable₂ A I ρ δ₀ (Semiproposition.free₁ ψ :: SecondOrder.Sequent.shift₁ Δ₁) →
      Δ₁ ⊆ ∼φ :: Θ →
      OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α δ) Θ)
    (hExs₂ : ∀ {δ δ₀ : O} {ψ : Semiproposition L 1 0} {σ : Semiformula L ℕ ℕ 0 1}
      {Δ₁ : SecondOrder.Sequent L},
      (∃² ψ) = ∼φ → Arith σ → δ₀ < δ → OrdinalNotation.nadd α δ ≤ s →
      OmegaDerivable₂ A I ρ δ₀ (I.inst₂ ψ σ :: Δ₁) → Δ₁ ⊆ ∼φ :: Θ →
      OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α δ) Θ) :
    ∀ {δ : O} {Δ₀ : SecondOrder.Sequent L}, OmegaDerivable₂ A I ρ δ Δ₀ →
      OrdinalNotation.nadd α δ ≤ s → Δ₀ ⊆ ∼φ :: Θ →
        OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α δ) Θ := by
  have hsubL : ∀ ζ : Proposition L, Γ₀ ⊆ φ :: ζ :: Θ := by
    intro ζ x hx
    have := hss hx
    simp only [List.mem_cons] at this ⊢
    tauto
  have hle : ∀ δ : O, α ≤ OrdinalNotation.redOrd α δ := fun δ =>
    le_trans (OrdinalNotation.le_nadd_left α δ) (OrdinalNotation.le_nadd_left _ _)
  intro δ Δ₀ he
  induction he with
  | @atom δ' χ hχ =>
      intro hs hssR
      have h := hssR List.mem_cons_self
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact hAtom hχ h hs
      · refine .contraction ?_ (.atom hχ)
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rw [hx]; exact h
  | @identity δ' χ =>
      intro _ hssR
      rcases identity_cases hssR with ⟨h₁, h₂⟩ | h
      · exact of_mem_identity χ h₁ h₂
      · rw [Semiformula.neg_neg] at h
        refine (OmegaDerivable₂.contraction ?_ hd).mono_ord (hle δ')
        intro x hx
        have := hss hx
        simp only [List.mem_cons] at this
        rcases this with rfl | hm
        · exact h
        · exact hm
  | @verum δ' =>
      intro _ hssR
      have h := hssR (show (⊤ : Proposition L) ∈ [(⊤ : Proposition L)] by simp)
      simp only [List.mem_cons] at h
      rcases h with h | h
      · have hφ : φ = ⊥ := by
          have := congrArg (fun χ => ∼χ) h
          simpa using this.symm
        subst hφ
        exact (drop_falsum hd hss).mono_ord (hle δ')
      · exact of_mem_verum h
  | @contraction δ' Δ' Δ ss _ ih =>
      intro hs hssR
      exact ih hs (fun x hx => hssR (ss hx))
  | @or δ' δ₀ ψ₁ ψ₂ Δ₁ hlt heP _ =>
      intro hs hssR
      by_cases hcase : ψ₁ ⋎ ψ₂ = ∼φ
      · exact hOr hcase hlt hs heP (fun x hx => hssR (List.mem_cons_of_mem _ hx))
      · have hmem : (ψ₁ ⋎ ψ₂) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
          hd hr (Θ := ψ₁ :: ψ₂ :: Θ)
          (by
            intro x hx
            have := hss hx
            simp only [List.mem_cons] at this ⊢
            tauto)
          heP
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · rcases hx with rfl | hx
              · tauto
              · have := hssR (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
        exact drop_head (.or (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @and δ' δ₀ δ₁ ψ₁ ψ₂ Δ₁ hlt₀ hlt₁ heP heQ _ _ =>
      intro hs hssR
      by_cases hcase : ψ₁ ⋏ ψ₂ = ∼φ
      · exact hAnd hcase hlt₀ hlt₁ hs heP heQ (fun x hx => hssR (List.mem_cons_of_mem _ hx))
      · have hmem : (ψ₁ ⋏ ψ₂) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have hsubR : ∀ ζ : Proposition L, ζ :: Δ₁ ⊆ ∼φ :: ζ :: Θ := by
          intro ζ x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto
        have kp := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs)
          hd hr (Θ := ψ₁ :: Θ) (hsubL ψ₁) heP (hsubR ψ₁)
        have kq := ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs)
          hd hr (Θ := ψ₂ :: Θ) (hsubL ψ₂) heQ (hsubR ψ₂)
        exact drop_head
          (.and (OrdinalNotation.redOrd_lt_right α hlt₀)
            (OrdinalNotation.redOrd_lt_right α hlt₁) kp kq) hmem
  | @omegaRule δ' ψ Δ₁ f hf heP _ =>
      intro hs hssR
      by_cases hcase : (∀¹ ψ) = ∼φ
      · exact hOmega hcase hf hs heP (fun x hx => hssR (List.mem_cons_of_mem _ hx))
      · have hmem : (∀¹ ψ) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        refine drop_head
          (.omegaRule (fun n => OrdinalNotation.redOrd α (f n))
            (fun n => OrdinalNotation.redOrd_lt_right α (hf n)) (fun n => ?_)) hmem
        refine ih2 α (f n) (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α (hf n)) hs)
          hd hr (Θ := I.inst ψ n :: Θ) (hsubL _) (heP n) ?_
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssR (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto
  | @exs δ' δ₀ ψ Δ₁ n hlt heP _ =>
      intro hs hssR
      by_cases hcase : (∃¹ ψ) = ∼φ
      · exact hExs hcase hlt hs heP (fun x hx => hssR (List.mem_cons_of_mem _ hx))
      · have hmem : (∃¹ ψ) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
          hd hr (Θ := I.inst ψ n :: Θ) (hsubL _) heP
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hssR (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto)
        exact drop_head (.exs n (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @all₂ δ' δ₀ ψ Δ₁ hlt heP _ =>
      intro hs hssR
      by_cases hcase : (∀² ψ) = ∼φ
      · exact hAll₂ hcase hlt hs heP (fun x hx => hssR (List.mem_cons_of_mem _ hx))
      · have hmem : (∀² ψ) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have hd' := map_shift₁ hd
        have hss' : SecondOrder.Sequent.shift₁ Γ₀ ⊆
            Semiproposition.shift₁ φ :: Semiproposition.free₁ ψ ::
              SecondOrder.Sequent.shift₁ Θ := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := mem_shift₁.mp hx
          have := hss hy
          simp only [List.mem_cons] at this ⊢
          rcases this with rfl | h
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (shift₁_mem h))
        have hr' : rank (Semiproposition.shift₁ φ) ≤ ρ := by
          rw [rank_shift₁]; exact hr
        have hssR' : Semiproposition.free₁ ψ :: SecondOrder.Sequent.shift₁ Δ₁ ⊆
            ∼(Semiproposition.shift₁ φ) :: Semiproposition.free₁ ψ ::
              SecondOrder.Sequent.shift₁ Θ := by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inr (Or.inl rfl)
          · obtain ⟨y, hy, rfl⟩ := mem_shift₁.mp hx
            have := hssR (List.mem_cons_of_mem _ hy)
            simp only [List.mem_cons] at this
            rcases this with rfl | h
            · exact Or.inl (shift₁_neg φ)
            · exact Or.inr (Or.inr (shift₁_mem h))
        have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
          hd' hr' hss' heP hssR'
        exact drop_head (.all₂ (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @exs₂ δ' δ₀ ψ σ Δ₁ hσ hlt heP _ =>
      intro hs hssR
      by_cases hcase : (∃² ψ) = ∼φ
      · exact hExs₂ hcase hσ hlt hs heP (fun x hx => hssR (List.mem_cons_of_mem _ hx))
      · have hmem : (∃² ψ) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
          hd hr (Θ := I.inst₂ ψ σ :: Θ) (hsubL _) heP
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hssR (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto)
        exact drop_head (.exs₂ hσ (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @cut δ' δ₀ δ₁ ψ Δ₁ Δ₂ hc hlt₀ hlt₁ hpp hnn _ _ =>
      intro hs hssR
      have kp := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs)
        hd hr (Θ := ψ :: Θ) (hsubL ψ) hpp
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_left _ hx)
            simp only [List.mem_cons] at this
            tauto)
      have kn := ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs)
        hd hr (Θ := ∼ψ :: Θ) (hsubL (∼ψ)) hnn
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_right _ hx)
            simp only [List.mem_cons] at this
            tauto)
      refine .contraction ?_
        (.cut hc (OrdinalNotation.redOrd_lt_right α hlt₀)
          (OrdinalNotation.redOrd_lt_right α hlt₁) kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto

/-! #### The left induction -/

set_option maxHeartbeats 4000000 in
/-- The reduction lemma in the form the well-founded recursion needs. -/
theorem reduction_aux (P : SubstProvider A I) {ρ : NONote} :
    ∀ (s β γ : O), OrdinalNotation.nadd β γ ≤ s →
      ∀ {Γ₀ : SecondOrder.Sequent L}, OmegaDerivable₂ A I ρ β Γ₀ →
        ∀ {φ : Proposition L}, rank φ ≤ ρ →
        ∀ {Θ Δ₀ : SecondOrder.Sequent L}, Γ₀ ⊆ φ :: Θ →
          OmegaDerivable₂ A I ρ γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ →
            OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd β γ) Θ := by
  intro s
  induction s using WellFoundedLT.induction with
  | _ s ihs =>
    intro β γ hbg
    have ih2 : RedIH₂ L A I ρ (OrdinalNotation.nadd β γ) := fun β' γ' h =>
      ihs (OrdinalNotation.nadd β' γ') (lt_of_lt_of_le h hbg) β' γ' le_rfl
    suffices K : ∀ (α : O) {Γ₀ : SecondOrder.Sequent L}, OmegaDerivable₂ A I ρ α Γ₀ →
        OrdinalNotation.nadd α γ ≤ OrdinalNotation.nadd β γ →
        ∀ {φ : Proposition L}, rank φ ≤ ρ →
        ∀ {Θ Δ₀ : SecondOrder.Sequent L}, Γ₀ ⊆ φ :: Θ →
          OmegaDerivable₂ A I ρ γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ →
            OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α γ) Θ by
      intro Γ₀ hd φ hφ Θ Δ₀ hss he hst
      exact K β hd le_rfl hφ hss he hst
    intro α Γ₀ hd
    induction hd with
    | @atom α' ψ hψ =>
        intro hs φ hφ Θ Δ₀ hss he hst
        have h := hss List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with rfl | hΘ
        · refine reduction_right ih2 (.atom hψ) hss hφ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he hs hst
          · intro δ ξ hξ hξe _
            exact absurd (hξe ▸ hξ) (fun h => A.consistent ψ hψ h)
          · intro δ δ₀ ψ₁ ψ₂ Δ₁ h
            exact absurd h.symm (Literals₂.neg_ne_or hψ)
          · intro δ δ₀ δ₁ ψ₁ ψ₂ Δ₁ h
            exact absurd h.symm (Literals₂.neg_ne_and hψ)
          · intro δ ξ Δ₁ f h
            exact absurd h.symm (Literals₂.neg_ne_all₁ hψ)
          · intro δ δ₀ ξ Δ₁ n h
            exact absurd h.symm (Literals₂.neg_ne_exs₁ hψ)
          · intro δ δ₀ ξ Δ₁ h
            exact absurd h.symm (Literals₂.neg_ne_all₂ hψ)
          · intro δ δ₀ ξ σ Δ₁ h
            exact absurd h.symm (Literals₂.neg_ne_exs₂ hψ)
        · refine .contraction ?_ (.atom hψ)
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rw [hx]; exact hΘ
    | @contraction α' Δ' Γ' ss _ ihprem =>
        intro hs φ hφ Θ Δ₀ hss he hst
        exact ihprem hs hφ (fun x hx => hss (ss hx)) he hst
    | @identity α' χ =>
        intro _ φ _ Θ Δ₀ hss he hst
        have hle : γ ≤ OrdinalNotation.redOrd α' γ :=
          le_trans (OrdinalNotation.le_nadd_right α' γ) (OrdinalNotation.le_nadd_left _ _)
        rcases identity_cases hss with ⟨h₁, h₂⟩ | h
        · exact of_mem_identity χ h₁ h₂
        · refine (OmegaDerivable₂.contraction ?_ he).mono_ord hle
          intro x hx
          have := hst hx
          simp only [List.mem_cons] at this
          rcases this with rfl | hm
          · exact h
          · exact hm
    | @verum α' =>
        intro _ φ _ Θ Δ₀ hss he hst
        have h := hss (show (⊤ : Proposition L) ∈ [(⊤ : Proposition L)] by simp)
        simp only [List.mem_cons] at h
        rcases h with hφ | hΘ
        · have hbot : Δ₀ ⊆ (⊥ : Proposition L) :: Θ := by
            intro x hx
            have := hst hx
            simp only [List.mem_cons] at this ⊢
            rcases this with rfl | hm
            · left; rw [← hφ]; simp
            · tauto
          exact (drop_falsum he hbot).mono_ord
            (le_trans (OrdinalNotation.le_nadd_right α' γ) (OrdinalNotation.le_nadd_left _ _))
        · exact of_mem_verum hΘ
    | @or α' α₀ χ ψ Γ' hb hprem ihp =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (χ ⋎ ψ) = φ
        · subst hcase
          have hd : OmegaDerivable₂ A I ρ α' ((χ ⋎ ψ) :: Γ') := .or hb hprem
          have hsubL : ∀ ζ : Proposition L, ((χ ⋎ ψ) :: Γ') ⊆ (χ ⋎ ψ) :: ζ :: Θ := by
            intro ζ x hx
            have := hss hx
            simp only [List.mem_cons] at this ⊢
            tauto
          refine reduction_right ih2 hd hss hφ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he hs hst
          · intro δ ξ hξ hξe _
            exact absurd hξe (Literals₂.ne_and (ψ₁ := ∼χ) (ψ₂ := ∼ψ) hξ)
          · intro δ δ₀ ψ₁ ψ₂ Δ₁ h
            exact absurd h (by simp)
          · -- PRINCIPAL
            intro δ δ₀ δ₁ ψ₁ ψ₂ Δ₁ heq hlt₀ hlt₁ hs' heP heQ hssR
            have heq' : ψ₁ ⋏ ψ₂ = ((∼χ) ⋏ (∼ψ)) := heq
            obtain ⟨rfl, rfl⟩ := Semiformula.and_inj.mp heq'
            have hcχ : rank χ < ρ :=
              lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) (NONote.lt_succ _)) hφ
            have hcψ : rank ψ < ρ :=
              lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) (NONote.lt_succ _)) hφ
            have hA : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α₀ δ) (χ :: ψ :: Θ) :=
              ih2 α₀ δ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ hb) hs') hprem hφ
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · rcases hx with rfl | hx
                    · tauto
                    · have := hss (List.mem_cons_of_mem _ hx)
                      simp only [List.mem_cons] at this
                      tauto)
                (OmegaDerivable₂.and hlt₀ hlt₁ heP heQ)
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · exact Or.inl rfl
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
            have hB : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α' δ₀) ((∼χ) :: Θ) :=
              ih2 α' δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α' hlt₀) hs') hd hφ
                (hsubL (∼χ)) heP
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
            have hC : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α' δ₁) ((∼ψ) :: Θ) :=
              ih2 α' δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α' hlt₁) hs') hd hφ
                (hsubL (∼ψ)) heQ
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
            have h₀ : OrdinalNotation.nadd α₀ δ < OrdinalNotation.nadd α' δ :=
              OrdinalNotation.nadd_lt_nadd_left δ hb
            have h₁ : OrdinalNotation.nadd α' δ₁ < OrdinalNotation.nadd α' δ :=
              OrdinalNotation.nadd_lt_nadd_right α' hlt₁
            have hA' : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α₀ δ) (ψ :: χ :: Θ) := by
              refine OmegaDerivable₂.contraction ?_ hA
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              tauto
            have step : OmegaDerivable₂ A I ρ
                (OrdinalNotation.mid (OrdinalNotation.nadd α₀ δ) (OrdinalNotation.nadd α' δ₁)
                  (OrdinalNotation.nadd α' δ))
                (χ :: Θ) := by
              refine OmegaDerivable₂.contraction ?_
                (OmegaDerivable₂.cut hcψ (OrdinalNotation.sq_lt_mid_left h₀ h₁)
                  (OrdinalNotation.sq_lt_mid_right h₀ h₁) hA' hC)
              intro x hx
              simp only [List.cons_append, List.mem_cons, List.mem_append] at hx ⊢
              tauto
            refine OmegaDerivable₂.contraction ?_
              (OmegaDerivable₂.cut hcχ (OrdinalNotation.mid_lt_sq h₀ h₁)
                (OrdinalNotation.redOrd_lt_right α' hlt₀) step hB)
            intro x hx
            simp only [List.mem_append] at hx
            tauto
          · intro δ ξ Δ₁ f h
            exact absurd h (by simp)
          · intro δ δ₀ ξ Δ₁ n h
            exact absurd h (by simp)
          · intro δ δ₀ ξ Δ₁ h
            exact absurd h (by simp)
          · intro δ δ₀ ξ σ Δ₁ h
            exact absurd h (by simp)
        · have hmem : (χ ⋎ ψ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          have hs' : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb) hs)
          have key := ihp hs' hφ (Θ := χ :: ψ :: Θ)
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · rcases hx with rfl | hx
                · tauto
                · have := hss (List.mem_cons_of_mem _ hx)
                  simp only [List.mem_cons] at this
                  tauto)
            he
            (by
              intro x hx
              have := hst hx
              simp only [List.mem_cons] at this ⊢
              tauto)
          exact drop_head (.or (OrdinalNotation.redOrd_lt_left γ hb) key) hmem
    | @and α' α₀ α₁ χ ψ Γ' hb1 hb2 hp hq ihp ihq =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (χ ⋏ ψ) = φ
        · subst hcase
          have hd : OmegaDerivable₂ A I ρ α' ((χ ⋏ ψ) :: Γ') := .and hb1 hb2 hp hq
          refine reduction_right ih2 hd hss hφ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he hs hst
          · intro δ ξ hξ hξe _
            exact absurd hξe (Literals₂.ne_or (ψ₁ := ∼χ) (ψ₂ := ∼ψ) hξ)
          · -- PRINCIPAL
            intro δ δ₀ ψ₁ ψ₂ Δ₁ heq hlt hs' heP hssR
            have heq' : ψ₁ ⋎ ψ₂ = ((∼χ) ⋎ (∼ψ)) := heq
            obtain ⟨rfl, rfl⟩ := Semiformula.or_inj.mp heq'
            have hcχ : rank χ < ρ :=
              lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) (NONote.lt_succ _)) hφ
            have hcψ : rank ψ < ρ :=
              lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) (NONote.lt_succ _)) hφ
            have hsubR : ∀ ζ : Proposition L,
                (((∼χ) ⋎ (∼ψ)) :: Δ₁) ⊆ ∼(χ ⋏ ψ) :: ζ :: Θ := by
              intro ζ x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · exact Or.inl rfl
              · have := hssR hx
                simp only [List.mem_cons] at this
                tauto
            have hsL : (χ :: Γ') ⊆ (χ ⋏ ψ) :: χ :: Θ := by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hss (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto
            have hsL' : (ψ :: Γ') ⊆ (χ ⋏ ψ) :: ψ :: Θ := by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hss (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto
            have hA₀ : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α₀ δ) (χ :: Θ) :=
              ih2 α₀ δ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ hb1) hs') hp hφ
                hsL (OmegaDerivable₂.or hlt heP) (hsubR χ)
            have hA₁ : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α₁ δ) (ψ :: Θ) :=
              ih2 α₁ δ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ hb2) hs') hq hφ
                hsL' (OmegaDerivable₂.or hlt heP) (hsubR ψ)
            have hB : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α' δ₀)
                ((∼χ) :: (∼ψ) :: Θ) :=
              ih2 α' δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α' hlt) hs') hd hφ
                (by
                  intro x hx
                  have := hss hx
                  simp only [List.mem_cons] at this ⊢
                  tauto)
                heP
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · rcases hx with rfl | hx
                    · tauto
                    · have := hssR hx
                      simp only [List.mem_cons] at this
                      tauto)
            have h₀ : OrdinalNotation.nadd α₀ δ < OrdinalNotation.nadd α' δ :=
              OrdinalNotation.nadd_lt_nadd_left δ hb1
            have hBs : OrdinalNotation.nadd α' δ₀ < OrdinalNotation.nadd α' δ :=
              OrdinalNotation.nadd_lt_nadd_right α' hlt
            have step : OmegaDerivable₂ A I ρ
                (OrdinalNotation.mid (OrdinalNotation.nadd α₀ δ) (OrdinalNotation.nadd α' δ₀)
                  (OrdinalNotation.nadd α' δ))
                ((∼ψ) :: Θ) := by
              refine OmegaDerivable₂.contraction ?_
                (OmegaDerivable₂.cut hcχ (OrdinalNotation.sq_lt_mid_left h₀ hBs)
                  (OrdinalNotation.sq_lt_mid_right h₀ hBs) hA₀ hB)
              intro x hx
              simp only [List.mem_append, List.mem_cons] at hx ⊢
              tauto
            refine OmegaDerivable₂.contraction ?_
              (OmegaDerivable₂.cut hcψ (OrdinalNotation.redOrd_lt_left δ hb2)
                (OrdinalNotation.mid_lt_sq h₀ hBs) hA₁ step)
            intro x hx
            simp only [List.mem_append] at hx
            tauto
          · intro δ δ₀ δ₁ ψ₁ ψ₂ Δ₁ h
            exact absurd h (by simp)
          · intro δ ξ Δ₁ f h
            exact absurd h (by simp)
          · intro δ δ₀ ξ Δ₁ n h
            exact absurd h (by simp)
          · intro δ δ₀ ξ Δ₁ h
            exact absurd h (by simp)
          · intro δ δ₀ ξ σ Δ₁ h
            exact absurd h (by simp)
        · have hmem : (χ ⋏ ψ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          have hs1 : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb1) hs)
          have hs2 : OrdinalNotation.nadd α₁ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb2) hs)
          have hsubL : ∀ ζ : Proposition L, (ζ :: Γ') ⊆ φ :: ζ :: Θ := by
            intro ζ x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hss (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto
          have hsubR : ∀ ζ : Proposition L, Δ₀ ⊆ ∼φ :: ζ :: Θ := by
            intro ζ x hx
            have := hst hx
            simp only [List.mem_cons] at this ⊢
            tauto
          have kp := ihp hs1 hφ (Θ := χ :: Θ) (hsubL χ) he (hsubR χ)
          have kq := ihq hs2 hφ (Θ := ψ :: Θ) (hsubL ψ) he (hsubR ψ)
          exact drop_head
            (.and (OrdinalNotation.redOrd_lt_left γ hb1)
              (OrdinalNotation.redOrd_lt_left γ hb2) kp kq) hmem
    | @omegaRule α' χ Γ' f hf hprem ihp =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (∀¹ χ) = φ
        · subst hcase
          have hd : OmegaDerivable₂ A I ρ α' ((∀¹ χ) :: Γ') := .omegaRule f hf hprem
          refine reduction_right ih2 hd hss hφ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he hs hst
          · intro δ ξ hξ hξe _
            exact absurd hξe (Literals₂.ne_exs₁ (ψ := ∼χ) hξ)
          · intro δ δ₀ ψ₁ ψ₂ Δ₁ h
            exact absurd h (by simp)
          · intro δ δ₀ δ₁ ψ₁ ψ₂ Δ₁ h
            exact absurd h (by simp)
          · intro δ ξ Δ₁ g h
            exact absurd h (by simp)
          · -- PRINCIPAL: the witness is the existential side's `n`.
            intro δ δ₀ ξ Δ₁ n heq hlt hs' heP hssR
            obtain rfl : ξ = ∼χ := by simpa using heq
            have hcχ : rank (I.inst χ n) < ρ := by
              rw [I.rank_inst]
              exact lt_of_lt_of_le (NONote.lt_succ _) hφ
            have hA : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd (f n) δ)
                (I.inst χ n :: Θ) :=
              ih2 (f n) δ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ (hf n)) hs')
                (hprem n) hφ
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hss (List.mem_cons_of_mem _ hx)
                    simp only [List.mem_cons] at this
                    tauto)
                (OmegaDerivable₂.exs n hlt heP)
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · exact Or.inl rfl
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
            have hBsub : OmegaDerivable₂ A I ρ δ₀ ((∼I.inst χ n) :: Δ₁) := by
              simpa using heP
            have hswap : OrdinalNotation.nadd δ₀ α' < OrdinalNotation.nadd β γ := by
              rw [OrdinalNotation.nadd_comm]
              exact lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α' hlt) hs'
            have hrneg : rank (∼(∀¹ χ) : Proposition L) ≤ ρ := by simpa using hφ
            have hB : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd δ₀ α')
                ((∼I.inst χ n) :: Θ) :=
              ih2 δ₀ α' hswap hBsub hrneg
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
                hd
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · left; simp
                  · have := hss (List.mem_cons_of_mem _ hx)
                    simp only [List.mem_cons] at this
                    rcases this with rfl | hm
                    · left; simp
                    · tauto)
            have hBlt : OrdinalNotation.redOrd δ₀ α' < OrdinalNotation.redOrd α' δ := by
              have hlt' : OrdinalNotation.nadd δ₀ α' < OrdinalNotation.nadd α' δ := by
                rw [OrdinalNotation.nadd_comm]
                exact OrdinalNotation.nadd_lt_nadd_right α' hlt
              exact OrdinalNotation.sq_lt_sq hlt'
            refine OmegaDerivable₂.contraction ?_
              (OmegaDerivable₂.cut hcχ (OrdinalNotation.redOrd_lt_left δ (hf n)) hBlt hA hB)
            intro x hx
            simp only [List.mem_append] at hx
            tauto
          · intro δ δ₀ ξ Δ₁ h
            exact absurd h (by simp)
          · intro δ δ₀ ξ σ Δ₁ h
            exact absurd h (by simp)
        · have hmem : (∀¹ χ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          refine drop_head
            (.omegaRule (fun n => OrdinalNotation.redOrd (f n) γ)
              (fun n => OrdinalNotation.redOrd_lt_left γ (hf n)) (fun n => ?_)) hmem
          refine ihp n (le_of_lt (lt_of_lt_of_le
            (OrdinalNotation.nadd_lt_nadd_left γ (hf n)) hs)) hφ (Θ := I.inst χ n :: Θ) ?_ he ?_
          · intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hss (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto
          · intro x hx
            have := hst hx
            simp only [List.mem_cons] at this ⊢
            tauto
    | @exs α' α₀ χ Γ' n₀ hb hprem ihp =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (∃¹ χ) = φ
        · subst hcase
          have hd : OmegaDerivable₂ A I ρ α' ((∃¹ χ) :: Γ') := .exs n₀ hb hprem
          refine reduction_right ih2 hd hss hφ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he hs hst
          · intro δ ξ hξ hξe _
            exact absurd hξe (Literals₂.ne_all₁ (ψ := ∼χ) hξ)
          · intro δ δ₀ ψ₁ ψ₂ Δ₁ h
            exact absurd h (by simp)
          · intro δ δ₀ δ₁ ψ₁ ψ₂ Δ₁ h
            exact absurd h (by simp)
          · -- PRINCIPAL: the ω-rule on the right has a premise at `n₀`.
            intro δ ξ Δ₁ f heq hf hs' heP hssR
            obtain rfl : ξ = ∼χ := by simpa using heq
            have hcχ : rank (I.inst χ n₀) < ρ := by
              rw [I.rank_inst]
              exact lt_of_lt_of_le (NONote.lt_succ _) hφ
            have hA : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α₀ δ)
                (I.inst χ n₀ :: Θ) :=
              ih2 α₀ δ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ hb) hs') hprem hφ
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hss (List.mem_cons_of_mem _ hx)
                    simp only [List.mem_cons] at this
                    tauto)
                (OmegaDerivable₂.omegaRule f hf heP)
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · exact Or.inl rfl
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
            have hBsub : OmegaDerivable₂ A I ρ (f n₀) ((∼I.inst χ n₀) :: Δ₁) := by
              simpa using heP n₀
            have hswap : OrdinalNotation.nadd (f n₀) α' < OrdinalNotation.nadd β γ := by
              rw [OrdinalNotation.nadd_comm]
              exact lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α' (hf n₀)) hs'
            have hrneg : rank (∼(∃¹ χ) : Proposition L) ≤ ρ := by simpa using hφ
            have hB : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd (f n₀) α')
                ((∼I.inst χ n₀) :: Θ) :=
              ih2 (f n₀) α' hswap hBsub hrneg
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
                hd
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · left; simp
                  · have := hss (List.mem_cons_of_mem _ hx)
                    simp only [List.mem_cons] at this
                    rcases this with rfl | hm
                    · left; simp
                    · tauto)
            have hBlt : OrdinalNotation.redOrd (f n₀) α' < OrdinalNotation.redOrd α' δ := by
              have hlt' : OrdinalNotation.nadd (f n₀) α' < OrdinalNotation.nadd α' δ := by
                rw [OrdinalNotation.nadd_comm]
                exact OrdinalNotation.nadd_lt_nadd_right α' (hf n₀)
              exact OrdinalNotation.sq_lt_sq hlt'
            refine OmegaDerivable₂.contraction ?_
              (OmegaDerivable₂.cut hcχ (OrdinalNotation.redOrd_lt_left δ hb) hBlt hA hB)
            intro x hx
            simp only [List.mem_append] at hx
            tauto
          · intro δ δ₀ ξ Δ₁ n h
            exact absurd h (by simp)
          · intro δ δ₀ ξ Δ₁ h
            exact absurd h (by simp)
          · intro δ δ₀ ξ σ Δ₁ h
            exact absurd h (by simp)
        · have hmem : (∃¹ χ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          have hs' : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb) hs)
          have key := ihp hs' hφ (Θ := I.inst χ n₀ :: Θ)
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hss (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
            he
            (by
              intro x hx
              have := hst hx
              simp only [List.mem_cons] at this ⊢
              tauto)
          exact drop_head
            (.exs n₀ (OrdinalNotation.redOrd_lt_left γ hb) key) hmem
    | @all₂ α' α₀ χ Γ' hb hprem ihp =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (∀² χ) = φ
        · subst hcase
          have hd : OmegaDerivable₂ A I ρ α' ((∀² χ) :: Γ') := .all₂ hb hprem
          refine reduction_right ih2 hd hss hφ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he hs hst
          · intro δ ξ hξ hξe _
            exact absurd hξe (Literals₂.ne_exs₂ (ψ := ∼χ) hξ)
          · intro δ δ₀ ψ₁ ψ₂ Δ₁ h
            exact absurd h (by simp)
          · intro δ δ₀ δ₁ ψ₁ ψ₂ Δ₁ h
            exact absurd h (by simp)
          · intro δ ξ Δ₁ g h
            exact absurd h (by simp)
          · intro δ δ₀ ξ Δ₁ n h
            exact absurd h (by simp)
          · intro δ δ₀ ξ Δ₁ h
            exact absurd h (by simp)
          · -- PRINCIPAL: substitute the witness into the eigenvariable derivation.
            intro δ δ₀ ξ σ Δ₁ heq hσ hlt hs' heP hssR
            obtain rfl : ξ = ∼χ := by simpa using heq
            have hω : omegaN ≤ ρ := le_trans (omegaN_le_rank_all₂ χ) hφ
            have hc : rank (I.inst₂ χ σ) < ρ := lt_of_lt_of_le (I.rank_inst₂_lt_all₂ hσ) hφ
            have hsub : OmegaDerivable₂ A I ρ α₀ (I.inst₂ χ σ :: Γ') :=
              P.subst_eigen hω hσ hprem
            have hA : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α₀ δ)
                (I.inst₂ χ σ :: Θ) :=
              ih2 α₀ δ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ hb) hs') hsub hφ
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hss (List.mem_cons_of_mem _ hx)
                    simp only [List.mem_cons] at this
                    tauto)
                (OmegaDerivable₂.exs₂ hσ hlt heP)
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · exact Or.inl rfl
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
            have hBsub : OmegaDerivable₂ A I ρ δ₀ ((∼I.inst₂ χ σ) :: Δ₁) := by
              simpa using heP
            have hswap : OrdinalNotation.nadd δ₀ α' < OrdinalNotation.nadd β γ := by
              rw [OrdinalNotation.nadd_comm]
              exact lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α' hlt) hs'
            have hrneg : rank (∼(∀² χ) : Proposition L) ≤ ρ := by simpa using hφ
            have hB : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd δ₀ α')
                ((∼I.inst₂ χ σ) :: Θ) :=
              ih2 δ₀ α' hswap hBsub hrneg
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
                hd
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · left; simp
                  · have := hss (List.mem_cons_of_mem _ hx)
                    simp only [List.mem_cons] at this
                    rcases this with rfl | hm
                    · left; simp
                    · tauto)
            have hBlt : OrdinalNotation.redOrd δ₀ α' < OrdinalNotation.redOrd α' δ := by
              have hlt' : OrdinalNotation.nadd δ₀ α' < OrdinalNotation.nadd α' δ := by
                rw [OrdinalNotation.nadd_comm]
                exact OrdinalNotation.nadd_lt_nadd_right α' hlt
              exact OrdinalNotation.sq_lt_sq hlt'
            refine OmegaDerivable₂.contraction ?_
              (OmegaDerivable₂.cut hc (OrdinalNotation.redOrd_lt_left δ hb) hBlt hA hB)
            intro x hx
            simp only [List.mem_append] at hx
            tauto
        · have hmem : (∀² χ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          have hs' : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb) hs)
          have hφ' : rank (Semiproposition.shift₁ φ) ≤ ρ := by
            rw [rank_shift₁]; exact hφ
          have hss' : Γ' ⊆ φ :: Θ := fun x hx => hss (List.mem_cons_of_mem _ hx)
          have key := ihp hs' hφ'
            (Θ := Semiproposition.free₁ χ :: SecondOrder.Sequent.shift₁ Θ)
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · exact Or.inr (Or.inl rfl)
              · obtain ⟨y, hy, rfl⟩ := mem_shift₁.mp hx
                have := hss' hy
                simp only [List.mem_cons] at this
                rcases this with rfl | h
                · exact Or.inl rfl
                · exact Or.inr (Or.inr (shift₁_mem h)))
            (map_shift₁ he)
            (by
              intro x hx
              obtain ⟨y, hy, rfl⟩ := mem_shift₁.mp hx
              have := hst hy
              simp only [List.mem_cons] at this ⊢
              rcases this with rfl | h
              · exact Or.inl (shift₁_neg φ)
              · exact Or.inr (Or.inr (shift₁_mem h)))
          exact drop_head (.all₂ (OrdinalNotation.redOrd_lt_left γ hb) key) hmem
    | @exs₂ α' α₀ χ σ Γ' hσ hb hprem ihp =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (∃² χ) = φ
        · subst hcase
          have hd : OmegaDerivable₂ A I ρ α' ((∃² χ) :: Γ') := .exs₂ hσ hb hprem
          refine reduction_right ih2 hd hss hφ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he hs hst
          · intro δ ξ hξ hξe _
            exact absurd hξe (Literals₂.ne_all₂ (ψ := ∼χ) hξ)
          · intro δ δ₀ ψ₁ ψ₂ Δ₁ h
            exact absurd h (by simp)
          · intro δ δ₀ δ₁ ψ₁ ψ₂ Δ₁ h
            exact absurd h (by simp)
          · intro δ ξ Δ₁ g h
            exact absurd h (by simp)
          · intro δ δ₀ ξ Δ₁ n h
            exact absurd h (by simp)
          · -- PRINCIPAL: substitute our witness into the eigenvariable derivation on the right.
            intro δ δ₀ ξ Δ₁ heq hlt hs' heP hssR
            obtain rfl : ξ = ∼χ := by simpa using heq
            have hω : omegaN ≤ ρ := le_trans (omegaN_le_rank_exs₂ χ) hφ
            have hc : rank (I.inst₂ χ σ) < ρ := lt_of_lt_of_le (I.rank_inst₂_lt_exs₂ hσ) hφ
            have hsub : OmegaDerivable₂ A I ρ δ₀ (I.inst₂ (∼χ) σ :: Δ₁) :=
              P.subst_eigen hω hσ heP
            have hBsub : OmegaDerivable₂ A I ρ δ₀ ((∼I.inst₂ χ σ) :: Δ₁) := by
              simpa using hsub
            have hA : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd α₀ δ)
                (I.inst₂ χ σ :: Θ) :=
              ih2 α₀ δ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ hb) hs') hprem hφ
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hss (List.mem_cons_of_mem _ hx)
                    simp only [List.mem_cons] at this
                    tauto)
                (OmegaDerivable₂.all₂ hlt heP)
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · exact Or.inl rfl
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
            have hswap : OrdinalNotation.nadd δ₀ α' < OrdinalNotation.nadd β γ := by
              rw [OrdinalNotation.nadd_comm]
              exact lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α' hlt) hs'
            have hrneg : rank (∼(∃² χ) : Proposition L) ≤ ρ := by simpa using hφ
            have hB : OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd δ₀ α')
                ((∼I.inst₂ χ σ) :: Θ) :=
              ih2 δ₀ α' hswap hBsub hrneg
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
                hd
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · left; simp
                  · have := hss (List.mem_cons_of_mem _ hx)
                    simp only [List.mem_cons] at this
                    rcases this with rfl | hm
                    · left; simp
                    · tauto)
            have hBlt : OrdinalNotation.redOrd δ₀ α' < OrdinalNotation.redOrd α' δ := by
              have hlt' : OrdinalNotation.nadd δ₀ α' < OrdinalNotation.nadd α' δ := by
                rw [OrdinalNotation.nadd_comm]
                exact OrdinalNotation.nadd_lt_nadd_right α' hlt
              exact OrdinalNotation.sq_lt_sq hlt'
            refine OmegaDerivable₂.contraction ?_
              (OmegaDerivable₂.cut hc (OrdinalNotation.redOrd_lt_left δ hb) hBlt hA hB)
            intro x hx
            simp only [List.mem_append] at hx
            tauto
          · intro δ δ₀ ξ τ Δ₁ h
            exact absurd h (by simp)
        · have hmem : (∃² χ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          have hs' : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb) hs)
          have key := ihp hs' hφ (Θ := I.inst₂ χ σ :: Θ)
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hss (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
            he
            (by
              intro x hx
              have := hst hx
              simp only [List.mem_cons] at this ⊢
              tauto)
          exact drop_head (.exs₂ hσ (OrdinalNotation.redOrd_lt_left γ hb) key) hmem
    | @cut α' α₀ α₁ χ Γ₁ Γ₂ hc hb1 hb2 hpp hnn ihp ihn =>
        intro hs φ hφ Θ Δ₀ hss he hst
        have hs1 : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
          le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb1) hs)
        have hs2 : OrdinalNotation.nadd α₁ γ ≤ OrdinalNotation.nadd β γ :=
          le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb2) hs)
        have hsubR : ∀ ζ : Proposition L, Δ₀ ⊆ ∼φ :: ζ :: Θ := by
          intro ζ x hx
          have := hst hx
          simp only [List.mem_cons] at this ⊢
          tauto
        have kp := ihp hs1 hφ (Θ := χ :: Θ)
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hss (List.mem_append_left _ hx)
              simp only [List.mem_cons] at this
              tauto)
          he (hsubR χ)
        have kn := ihn hs2 hφ (Θ := ∼χ :: Θ)
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hss (List.mem_append_right _ hx)
              simp only [List.mem_cons] at this
              tauto)
          he (hsubR (∼χ))
        refine OmegaDerivable₂.contraction ?_
          (OmegaDerivable₂.cut hc (OrdinalNotation.redOrd_lt_left γ hb1)
            (OrdinalNotation.redOrd_lt_left γ hb2) kp kn)
        intro x hx
        simp only [List.mem_append] at hx
        tauto

/-- **Reduction.**  Two derivations at rank `ρ` that cut against each other on a
formula of rank at most `ρ` combine into one at rank `ρ`, at the doubled sum of
their heights. -/
theorem reduction (P : SubstProvider A I) {ρ : NONote} (β γ : O)
    {Γ₀ Δ₀ Θ : SecondOrder.Sequent L} {φ : Proposition L}
    (hφ : rank φ ≤ ρ)
    (hd : OmegaDerivable₂ A I ρ β Γ₀) (hss : Γ₀ ⊆ φ :: Θ)
    (he : OmegaDerivable₂ A I ρ γ Δ₀) (hst : Δ₀ ⊆ ∼φ :: Θ) :
    OmegaDerivable₂ A I ρ (OrdinalNotation.redOrd β γ) Θ :=
  reduction_aux P (OrdinalNotation.nadd β γ) β γ le_rfl hd hφ hss he hst

/-! ### Elimination and the first cut-elimination theorem -/

/-- `ρ` is a predecessor bound of `ρ'`: every rank below `ρ'` is at most `ρ`.
The relation `PredBound ρ (ρ + 1)` holds, and this is the only way the
elimination lemma speaks about successors. -/
def PredBound (ρ ρ' : NONote) : Prop := ∀ a : NONote, a < ρ' → a ≤ ρ

/-- One level of cut rank, at the cost of one `ω`-power. -/
theorem elimination (P : SubstProvider A I) {ρ ρ' : NONote} (hρ : PredBound ρ ρ') :
    ∀ {α : O} {Γ : SecondOrder.Sequent L}, OmegaDerivable₂ A I ρ' α Γ →
      OmegaDerivable₂ A I ρ (OrdinalNotation.omegaPow α) Γ := by
  intro α Γ h
  induction h with
  | atom h => exact .atom h
  | identity φ => exact .identity φ
  | verum => exact .verum
  | or hlt _ ih => exact .or (OrdinalNotation.omegaPow_lt_omegaPow hlt) ih
  | and hb hc _ _ ihp ihq =>
      exact .and (OrdinalNotation.omegaPow_lt_omegaPow hb)
        (OrdinalNotation.omegaPow_lt_omegaPow hc) ihp ihq
  | omegaRule f hf _ ih =>
      exact .omegaRule (fun n => OrdinalNotation.omegaPow (f n))
        (fun n => OrdinalNotation.omegaPow_lt_omegaPow (hf n)) ih
  | exs n hlt _ ih => exact .exs n (OrdinalNotation.omegaPow_lt_omegaPow hlt) ih
  | all₂ hlt _ ih => exact .all₂ (OrdinalNotation.omegaPow_lt_omegaPow hlt) ih
  | exs₂ hψ hlt _ ih => exact .exs₂ hψ (OrdinalNotation.omegaPow_lt_omegaPow hlt) ih
  | contraction ss _ ih => exact .contraction ss ih
  | @cut α' β' γ' φ Γ₁ Γ₂ hrank hb hc _ _ ihp ihn =>
      have hφ : rank φ ≤ ρ := hρ _ hrank
      have hkey := reduction P (OrdinalNotation.omegaPow β') (OrdinalNotation.omegaPow γ')
        (Θ := Γ₁ ++ Γ₂) hφ ihp
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr (List.mem_append_left _ hx))
        ihn
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr (List.mem_append_right _ hx))
      exact hkey.mono_ord
        (le_of_lt (OrdinalNotation.redOrd_lt_omegaPow
          (OrdinalNotation.omegaPow_lt_omegaPow hb) (OrdinalNotation.omegaPow_lt_omegaPow hc)))

/-- `Chain k ρ ρ'`: `ρ'` is reached from `ρ` by `k` predecessor-bound steps —
the generic form of `ρ' = ρ + k`. -/
def Chain : ℕ → NONote → NONote → Prop
  | 0, ρ, ρ' => ρ' ≤ ρ
  | k + 1, ρ, ρ' => ∃ ρ'', PredBound ρ'' ρ' ∧ Chain k ρ ρ''

/-- **The first cut-elimination theorem** (Afshari–Rathjen Thm 3).  Rank `ρ + k`
at height `α` becomes rank `ρ` at height the `k`-fold `ω`-tower over `α`. -/
theorem cutElimination_chain (P : SubstProvider A I) :
    ∀ (k : ℕ) {ρ ρ' : NONote}, Chain k ρ ρ' → ∀ {α : O} {Γ : SecondOrder.Sequent L},
      OmegaDerivable₂ A I ρ' α Γ →
        OmegaDerivable₂ A I ρ (OrdinalNotation.omegaTower k α) Γ := by
  intro k
  induction k with
  | zero =>
      intro ρ ρ' h α Γ hd
      exact hd.mono_rank h
  | succ k ih =>
      intro ρ ρ' h α Γ hd
      obtain ⟨ρ'', hpb, hch⟩ := h
      exact ih hch (elimination P hpb hd)

end OmegaDerivable₂

end OrdinalAnalysis.ACAOmega
