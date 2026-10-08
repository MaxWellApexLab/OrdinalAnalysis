import OrdinalAnalysis.KPi.RS.Truth

/-!
# The RS calculus, part 4: `RS^inf` (B92 Def 3.1) and the Truth Lemma 3.2

* `IsSigma`, `SigmaData kappa` : the classes `Sigma(kappa)` (B92 Def 1.10) in an environment presentation:
  the domain `L_kappa` sits in a distinguished variable (the last one), and `exists z in L_kappa A^{(z,kappa)}`
  is `bex (lev kappa) phi`.
* `Inf R Gamma a r`    : `|-^a_r Gamma` (rules `(/\)`, `(\/)`, `(Cut)`, `(Ref)`; sequents are sets).
* `TermReg kappa`      : `kappa` is a limit and every family `T_a -> kappa` (`a < kappa`) is bounded
  below `kappa`; the only property of `R` used in Sigma-reflection.
* `truth_lemma`        : `|-^a_r Gamma` implies that some member of `Gamma` is true (B92 Lemma 3.2).
-/

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

/-! ### `Σ₁`-shape and `Σ(κ)` -/

/-- `φ` (with domain variable `d`) is `Σ₁`: `d` occurs only as the bound of `∃`; no `∀` over `d`; no level bounds. -/
def IsSigma : {n : ℕ} → Fin n → D0 n → Prop
  | _, d, .mem i j => i ≠ d ∧ j ≠ d
  | _, d, .nmem i j => i ≠ d ∧ j ≠ d
  | _, d, .ad i => i ≠ d
  | _, d, .nad i => i ≠ d
  | _, d, .and A B => IsSigma d A ∧ IsSigma d B
  | _, d, .or A B => IsSigma d A ∧ IsSigma d B
  | _, d, .bex (.var _) A => IsSigma d.castSucc A
  | _, _, .bex (.lev _) _ => False
  | _, d, .ball (.var j) A => j ≠ d ∧ IsSigma d.castSucc A
  | _, _, .ball (.lev _) _ => False

/-- A member of `Σ(κ)`: `A ≡ φ^{L_κ}(ā)`, `φ ∈ Σ₁`, `ā ∈ 𝒯_κ`. -/
structure SigmaData (κ : Ordinal.{1}) where
  m : ℕ
  φ : D0 (m + 1)
  hφ : IsSigma (Fin.last m) φ
  ρ : Fin m → T
  hρ : ∀ i, (ρ i).level < κ

/-- `A ≡ φ^{L_κ}(ā)`. -/
def SigmaData.sentence {κ : Ordinal.{1}} (S : SigmaData κ) : RSS :=
  .base S.φ (ext S.ρ (T.L κ))

/-- `∃z∈L_κ A^{(z,κ)}`. -/
def SigmaData.refl {κ : Ordinal.{1}} (S : SigmaData κ) : RSS :=
  .base (D0.bex (Bd.lev κ) S.φ) S.ρ

/-! ### `RS^∞` -/

/-- `Inf R Γ α ρ` : `⊢^α_ρ Γ` in `RS^∞`, B92 Def 3.1: the rules `(⋀) (⋁) (Cut) (Ref)` for the
junctor `expand R`; `ρ` bounds the ranks of cut formulas. -/
inductive Inf (R : Set Ordinal.{1}) : Set RSS → Ordinal.{1} → Ordinal.{1} → Prop
  | all {Γ : Set RSS} {A : RSS} {α ρ : Ordinal.{1}} (hA : (expand R A).isOr = false)
      (α₀ : (expand R A).J → Ordinal.{1}) (h0 : ∀ j, α₀ j < α)
      (h : ∀ j : (expand R A).J, Inf R (insert ((expand R A).child j) Γ) (α₀ j) ρ) :
      Inf R (insert A Γ) α ρ
  | ex {Γ : Set RSS} {A : RSS} {α ρ α₀ : Ordinal.{1}} (j : (expand R A).J)
      (hA : (expand R A).isOr = true) (h0 : α₀ < α) (hl : (expand R A).lvl j < α)
      (h : Inf R (insert ((expand R A).child j) Γ) α₀ ρ) : Inf R (insert A Γ) α ρ
  | cut {Γ : Set RSS} {C : RSS} {α ρ α₀ : Ordinal.{1}} (hC : C.rk < ρ) (h0 : α₀ < α)
      (h1 : Inf R (insert C.neg Γ) α₀ ρ) (h2 : Inf R (insert C Γ) α₀ ρ) : Inf R Γ α ρ
  | ref {Γ : Set RSS} {α ρ α₀ κ : Ordinal.{1}} (S : SigmaData κ) (hκ : κ ∈ R)
      (h0 : α₀ + 1 < α) (h : Inf R (insert S.sentence Γ) α₀ ρ) : Inf R (insert S.refl Γ) α ρ

/-! ### regularity with respect to term sets -/

/-- `κ` is a limit and every `𝒯_α`-indexed family (`α < κ`) of ordinals `< κ` is bounded below `κ`. -/
def TermReg (κ : Ordinal.{1}) : Prop :=
  Order.IsSuccLimit κ ∧
    ∀ α < κ, ∀ f : Tlt α → Ordinal.{1}, (∀ t, f t < κ) → ∃ γ < κ, ∀ t, f t ≤ γ

/-! ### small facts -/

theorem ext_update {n : ℕ} (ρ : Fin n → T) (x z : T) (d : Fin n) :
    ext (Function.update ρ d z) x = Function.update (ext ρ x) d.castSucc z :=
  Fin.snoc_update (α := fun _ => T) x ρ d z

theorem update_last_ext {n : ℕ} (ρ : Fin n → T) (x y : T) :
    Function.update (ext ρ x) (Fin.last n) y = ext ρ y := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j =>
    rw [Function.update_of_ne (Fin.castSucc_ne_last j)]
    simp

theorem RSTrue_memInst_L (R : Set Ordinal.{1}) (t : T) (γ : Ordinal.{1}) :
    RSTrue R (memInst t (T.L γ)) := by
  show RSTrue R (RSS.base (D0.nmem 0 1) ![t, T.L 0])
  rw [RSTrue_nmem]
  intro s
  exact absurd s.2 (by simp [T.level, T.L, PT.level])

/-! ### Σ-reflection in the truth definition (the semantic content of `(Ref)`) -/

theorem TermReg.pos {κ : Ordinal.{1}} (hκ : TermReg κ) : 0 < κ := by
  simpa using hκ.1.bot_lt

theorem sigma_reflect (R : Set Ordinal.{1}) {κ : Ordinal.{1}} (hκ : TermReg κ) :
    ∀ {n : ℕ} (φ : D0 n) (d : Fin n), IsSigma d φ → ∀ (ρ : Fin n → T),
      ρ d = T.L κ → (∀ i, i ≠ d → (ρ i).level < κ) → RSTrue R (RSS.base φ ρ) →
      ∃ β < κ, ∀ γ, β ≤ γ → γ < κ →
        RSTrue R (RSS.base φ (Function.update ρ d (T.L γ))) := by
  intro n φ
  induction φ with
  | mem i j =>
    intro d hσ ρ hd hp h
    obtain ⟨hi, hj⟩ := hσ
    refine ⟨0, hκ.pos, fun γ _ _ => ?_⟩
    rw [RSTrue_mem, Function.update_of_ne hi, Function.update_of_ne hj]
    exact (RSTrue_mem R i j ρ).1 h
  | nmem i j =>
    intro d hσ ρ hd hp h
    obtain ⟨hi, hj⟩ := hσ
    refine ⟨0, hκ.pos, fun γ _ _ => ?_⟩
    rw [RSTrue_nmem, Function.update_of_ne hi, Function.update_of_ne hj]
    exact (RSTrue_nmem R i j ρ).1 h
  | ad i =>
    intro d hσ ρ hd hp h
    refine ⟨0, hκ.pos, fun γ _ _ => ?_⟩
    rw [RSTrue_ad, Function.update_of_ne hσ]
    exact (RSTrue_ad R i ρ).1 h
  | nad i =>
    intro d hσ ρ hd hp h
    refine ⟨0, hκ.pos, fun γ _ _ => ?_⟩
    rw [RSTrue_nad, Function.update_of_ne hσ]
    exact (RSTrue_nad R i ρ).1 h
  | and X Y ihX ihY =>
    intro d hσ ρ hd hp h
    obtain ⟨hX, hY⟩ := hσ
    rw [RSTrue_band] at h
    obtain ⟨β1, hb1κ, hb1⟩ := ihX d hX ρ hd hp h.1
    obtain ⟨β2, hb2κ, hb2⟩ := ihY d hY ρ hd hp h.2
    refine ⟨max β1 β2, max_lt hb1κ hb2κ, fun γ hγ hγκ => ?_⟩
    rw [RSTrue_band]
    exact ⟨hb1 γ (le_trans (le_max_left _ _) hγ) hγκ, hb2 γ (le_trans (le_max_right _ _) hγ) hγκ⟩
  | or X Y ihX ihY =>
    intro d hσ ρ hd hp h
    obtain ⟨hX, hY⟩ := hσ
    rw [RSTrue_bor] at h
    rcases h with h | h
    · obtain ⟨β, hβκ, hβ⟩ := ihX d hX ρ hd hp h
      exact ⟨β, hβκ, fun γ hγ hγκ => by rw [RSTrue_bor]; exact Or.inl (hβ γ hγ hγκ)⟩
    · obtain ⟨β, hβκ, hβ⟩ := ihY d hY ρ hd hp h
      exact ⟨β, hβκ, fun γ hγ hγκ => by rw [RSTrue_bor]; exact Or.inr (hβ γ hγ hγκ)⟩
  | bex b A ih =>
    intro d hσ ρ hd hp h
    cases b with
    | lev γ => exact False.elim hσ
    | var j =>
      have hσ' : IsSigma d.castSucc A := hσ
      rw [RSTrue_bex] at h
      obtain ⟨t, hmi, hA⟩ := h
      by_cases hjd : j = d
      · subst hjd
        have hlev : (ρ j).level = κ := by rw [hd]; rfl
        have htκ : t.1.level < κ := lt_of_lt_of_eq t.2 hlev
        have hp' : ∀ i, i ≠ j.castSucc → (ext ρ t.1 i).level < κ := by
          intro i hi
          induction i using Fin.lastCases with
          | last => simpa using htκ
          | cast i0 =>
            simp only [ext_castSucc]
            exact hp i0 (fun h => hi (by rw [h]))
        obtain ⟨β', hβ'κ, hβ'⟩ := ih j.castSucc hσ' (ext ρ t.1) (by simpa using hd) hp' hA
        have hb1 : t.1.level + 1 < κ := hκ.1.isSuccPrelimit.add_one_lt htκ
        refine ⟨max β' (t.1.level + 1), max_lt hβ'κ hb1, fun γ hγ hγκ => ?_⟩
        have hγ1 : β' ≤ γ := le_trans (le_max_left _ _) hγ
        have hγ2 : t.1.level + 1 ≤ γ := le_trans (le_max_right _ _) hγ
        rw [RSTrue_bex]
        have e : resBd (Bd.var j) (Function.update ρ j (T.L γ)) = T.L γ := by simp [resBd]
        rw [e]
        refine ⟨⟨t.1, lt_of_lt_of_le (lt_add_one _) hγ2⟩, RSTrue_memInst_L R _ _, ?_⟩
        rw [ext_update]
        exact hβ' γ hγ1 hγκ
      · have hres : ∀ γ, resBd (Bd.var j) (Function.update ρ d (T.L γ)) = ρ j := by
          intro γ; simp [resBd, Function.update_of_ne hjd]
        have hjκ : (ρ j).level < κ := hp j hjd
        have htκ : t.1.level < κ := lt_trans t.2 hjκ
        have hp' : ∀ i, i ≠ d.castSucc → (ext ρ t.1 i).level < κ := by
          intro i hi
          induction i using Fin.lastCases with
          | last => simpa using htκ
          | cast i0 =>
            simp only [ext_castSucc]
            exact hp i0 (fun h => hi (by rw [h]))
        obtain ⟨β', hβ'κ, hβ'⟩ := ih d.castSucc hσ' (ext ρ t.1) (by simpa using hd) hp' hA
        refine ⟨β', hβ'κ, fun γ hγ hγκ => ?_⟩
        rw [RSTrue_bex, hres γ]
        refine ⟨t, hmi, ?_⟩
        rw [ext_update]
        exact hβ' γ hγ hγκ
  | ball b A ih =>
    intro d hσ ρ hd hp h
    cases b with
    | lev γ => exact False.elim hσ
    | var j =>
      obtain ⟨hjd, hσ'⟩ := show j ≠ d ∧ IsSigma d.castSucc A from hσ
      have hres : ∀ γ, resBd (Bd.var j) (Function.update ρ d (T.L γ)) = ρ j := by
        intro γ; simp [resBd, Function.update_of_ne hjd]
      have hjκ : (ρ j).level < κ := hp j hjd
      rw [RSTrue_ball] at h
      have key : ∀ t : Tlt (resBd (Bd.var j) ρ).level, ∃ β < κ,
          RSTrue R (RSS.base A (ext ρ t.1)) →
            ∀ γ, β ≤ γ → γ < κ →
              RSTrue R (RSS.base A (Function.update (ext ρ t.1) d.castSucc (T.L γ))) := by
        intro t
        by_cases hA : RSTrue R (RSS.base A (ext ρ t.1))
        · have htκ : t.1.level < κ := lt_trans t.2 hjκ
          have hp' : ∀ i, i ≠ d.castSucc → (ext ρ t.1 i).level < κ := by
            intro i hi
            induction i using Fin.lastCases with
            | last => simpa using htκ
            | cast i0 =>
              simp only [ext_castSucc]
              exact hp i0 (fun h => hi (by rw [h]))
          obtain ⟨β', hβ'κ, hβ'⟩ := ih d.castSucc hσ' (ext ρ t.1) (by simpa using hd) hp' hA
          exact ⟨β', hβ'κ, fun _ => hβ'⟩
        · exact ⟨0, hκ.pos, fun h => absurd h hA⟩
      choose f hfκ hf using key
      obtain ⟨γ0, hγ0κ, hγ0⟩ := hκ.2 (ρ j).level hjκ f hfκ
      refine ⟨γ0, hγ0κ, fun γ hγ hγκ => ?_⟩
      rw [RSTrue_ball, hres γ]
      intro t
      rcases h t with hn | ha
      · exact Or.inl hn
      · right
        rw [ext_update]
        exact hf t ha γ (le_trans (hγ0 t) hγ) hγκ

theorem refl_true (R : Set Ordinal.{1}) {κ : Ordinal.{1}} (hκ : TermReg κ) (S : SigmaData κ)
    (h : RSTrue R S.sentence) : RSTrue R S.refl := by
  obtain ⟨β, hβκ, hβ⟩ := sigma_reflect R hκ S.φ (Fin.last S.m) S.hφ (ext S.ρ (T.L κ))
    (by simp)
    (by
      intro i hi
      induction i using Fin.lastCases with
      | last => exact absurd rfl hi
      | cast j => simpa using S.hρ j) h
  have h1 := hβ β le_rfl hβκ
  rw [update_last_ext] at h1
  show RSTrue R (RSS.base (D0.bex (Bd.lev κ) S.φ) S.ρ)
  rw [RSTrue_bex]
  exact ⟨⟨T.L β, hβκ⟩, RSTrue_memInst_L R _ _, h1⟩

/-! ### The Truth Lemma (B92 Lemma 3.2) -/

/-- **Truth Lemma.** If `R` consists of `TermReg` ordinals, every `RS^∞`-derivable sequent is true
(in B92: `κ = min R`, `k Γ ⊆ κ`, cut rank `≤ κ`; here no such side condition is needed). -/
theorem truth_lemma (R : Set Ordinal.{1}) (hreg : ∀ κ ∈ R, TermReg κ) {Γ : Set RSS}
    {α ρ : Ordinal.{1}} (h : Inf R Γ α ρ) : ∃ A ∈ Γ, RSTrue R A := by
  induction h with
  | @all Γ A α ρ hA α₀ h0 h ih =>
    by_cases hall : ∀ j, RSTrue R ((expand R A).child j)
    · exact ⟨A, Set.mem_insert _ _, (RSTrue_of_and R A hA).2 hall⟩
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      obtain ⟨B, hB, hBt⟩ := ih j
      rcases Set.mem_insert_iff.1 hB with e | hB
      · rw [e] at hBt; exact absurd hBt hj
      · exact ⟨B, Set.mem_insert_of_mem _ hB, hBt⟩
  | @ex Γ A α ρ α₀ j hA h0 hl h ih =>
    obtain ⟨B, hB, hBt⟩ := ih
    rcases Set.mem_insert_iff.1 hB with e | hB
    · rw [e] at hBt
      exact ⟨A, Set.mem_insert _ _, (RSTrue_of_or R A hA).2 ⟨j, hBt⟩⟩
    · exact ⟨B, Set.mem_insert_of_mem _ hB, hBt⟩
  | @cut Γ C α ρ α₀ hC h0 h1 h2 ih1 ih2 =>
    obtain ⟨B1, hB1, t1⟩ := ih1
    obtain ⟨B2, hB2, t2⟩ := ih2
    rcases Set.mem_insert_iff.1 hB1 with e1 | h1'
    · rw [e1] at t1
      rcases Set.mem_insert_iff.1 hB2 with e2 | h2'
      · rw [e2] at t2
        exact absurd t2 ((RSTrue_neg R C).1 t1)
      · exact ⟨B2, h2', t2⟩
    · exact ⟨B1, h1', t1⟩
  | @ref Γ α ρ α₀ κ S hκ h0 h ih =>
    obtain ⟨B, hB, hBt⟩ := ih
    rcases Set.mem_insert_iff.1 hB with e | hB
    · rw [e] at hBt
      exact ⟨S.refl, Set.mem_insert _ _, refl_true R (hreg κ hκ) S hBt⟩
    · exact ⟨B, Set.mem_insert_of_mem _ hB, hBt⟩

end OrdinalAnalysis.KPi.RS
