/-
  The upper bounds of the analyses of `ID_n` and `ID_{<ω}` for the well-ordering forms, with the
  internal order as the hypothesis `hJ : InternalOrderFacts`, and the consistency of the
  theories they are stated for.

  * **`idn_upper_bound hJ n hn`**: for `n ≥ 1` and every notation `a ≺ c_n = ϑ₀(ϑ_n 0)`,
    `IDn n (WForms F n) ⊢ TI_a(≺, X)`, `F = hJ.toOrderFormulas` (the formulas of `≺`, `NF`,
    `Dom` the forms and the sentence are written with).
  * **`idlt_upper_bound hJ`**: for every countable notation `a ≺ Ω₁`,
    `IDlt (WFormsOmega F) ⊢ TI_a(≺, X)`; and (`idlt_upper_bound_finite`) already one finite
    piece `IDseq (WFormsOmega F) m` proves it (`Union.provable_IDlt_iff`).
  * **Consistency** (the new theories are sound in the standard model): the forms are positive
    in their own predicate and mention only lower predicates (`wForms_positive`,
    `wForms_levelBounded`), so `IDn n (WForms F n)` and `IDlt (WFormsOmega F)` are consistent
    (`Sound.IDn_consistent`, `Union.IDlt_consistent`), for any formulas `F`.
-/
import OrdinalAnalysis.IDn.UpperBound
import OrdinalAnalysis.IDn.Union

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### The upper bounds -/

theorem ixFin_val {n : ℕ} (h : 0 < n) (j : ℕ) : (ixFin h j).val = j % n := rfl

/-- **The upper bound of `ID_n`**: for every notation `a ≺ c_n = ϑ₀(ϑ_n 0)`, `ID_n` for the
well-ordering forms proves transfinite induction for the free predicate `X` up to `a`. -/
theorem idn_upper_bound (hJ : InternalOrderFacts) (n : ℕ) (hn : 0 < n) :
    ∀ a : ThetaWNoteD, a < ThetaWNoteD.c n →
      IDn n (WForms hJ.toOrderFormulas n) ⊢ tiUptoSentence hJ.toOrderFormulas (Fin n) a := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro a ha
  refine upper_bound_ID hJ (ixFin (Nat.succ_pos n)) n (WForms hJ.toOrderFormulas (n + 1)) ?_ ?_ ha
  · intro i j hi hj h
    have := congrArg Fin.val h
    rw [ixFin_val, ixFin_val, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  · intro k hk
    show wForm hJ.toOrderFormulas (ixFin _) (k % (n + 1)) =
      wForm hJ.toOrderFormulas (ixFin (Nat.succ_pos n)) k
    rw [Nat.mod_eq_of_lt (by omega)]

/-- **The upper bound of `ID_{<ω}`**: for every countable notation `a ≺ Ω₁`, `ID_{<ω}` for the
well-ordering forms proves transfinite induction for the free predicate `X` up to `a`. -/
theorem idlt_upper_bound (hJ : InternalOrderFacts) :
    ∀ a : ThetaWNoteD, a.1 < ThetaWTerm.Omega 0 →
      IDlt (WFormsOmega hJ.toOrderFormulas) ⊢ tiUptoSentence hJ.toOrderFormulas ℕ a := by
  intro a ha
  obtain ⟨N, hN⟩ := exists_lt_c_succ ha
  exact upper_bound_ID hJ id N (WFormsOmega hJ.toOrderFormulas) (fun _ _ _ _ h => h) (fun _ _ => rfl) hN

/-- The same, from one finite piece of `ID_{<ω}`. -/
theorem idlt_upper_bound_finite (hJ : InternalOrderFacts) :
    ∀ a : ThetaWNoteD, a.1 < ThetaWTerm.Omega 0 →
      ∃ m, IDseq (WFormsOmega hJ.toOrderFormulas) m ⊢ tiUptoSentence hJ.toOrderFormulas ℕ a :=
  fun a ha =>
    (provable_IDlt_iff (WFormsOmega hJ.toOrderFormulas) _).mp (idlt_upper_bound hJ a ha)

/-! ### Positivity and level-boundedness of the forms -/

section Syntax

variable {ι : Type} {ξ₁ ξ₂ : Type*}

theorem positiveIn_rew (k : ι) : ∀ {n₁ n₂ : ℕ} (ω : Rew (LXIN ι) ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformula (LXIN ι) ξ₁ n₁), PositiveIn k φ → PositiveIn k (ω ▹ φ)
  | _, _, _, .verum, _ => trivial
  | _, _, _, .falsum, _ => trivial
  | _, _, _, .rel _ _, _ => trivial
  | _, _, _, .nrel (Sum.inl _) _, _ => trivial
  | _, _, _, .nrel (Sum.inr IXRelN.X) _, _ => trivial
  | _, _, _, .nrel (Sum.inr (IXRelN.I _)) _, h => h
  | _, _, ω, .and φ ψ, h => ⟨positiveIn_rew k ω φ h.1, positiveIn_rew k ω ψ h.2⟩
  | _, _, ω, .or φ ψ, h => ⟨positiveIn_rew k ω φ h.1, positiveIn_rew k ω ψ h.2⟩
  | _, _, ω, .all φ, h => positiveIn_rew k ω.q φ h
  | _, _, ω, .exs φ, h => positiveIn_rew k ω.q φ h

theorem levelBounded_rew [PartialOrder ι] (k : ι) : ∀ {n₁ n₂ : ℕ} (ω : Rew (LXIN ι) ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformula (LXIN ι) ξ₁ n₁), LevelBounded k φ → LevelBounded k (ω ▹ φ)
  | _, _, _, .verum, _ => trivial
  | _, _, _, .falsum, _ => trivial
  | _, _, _, .rel (Sum.inl _) _, _ => trivial
  | _, _, _, .rel (Sum.inr IXRelN.X) _, _ => trivial
  | _, _, _, .rel (Sum.inr (IXRelN.I _)) _, h => h
  | _, _, _, .nrel (Sum.inl _) _, _ => trivial
  | _, _, _, .nrel (Sum.inr IXRelN.X) _, _ => trivial
  | _, _, _, .nrel (Sum.inr (IXRelN.I _)) _, h => h
  | _, _, ω, .and φ ψ, h => ⟨levelBounded_rew k ω φ h.1, levelBounded_rew k ω ψ h.2⟩
  | _, _, ω, .or φ ψ, h => ⟨levelBounded_rew k ω φ h.1, levelBounded_rew k ω ψ h.2⟩
  | _, _, ω, .all φ, h => levelBounded_rew k ω.q φ h
  | _, _, ω, .exs φ, h => levelBounded_rew k ω.q φ h

/-! #### Inductive mirrors of `PositiveIn` and `LevelBounded`

`PositiveIn` and `LevelBounded` are structurally recursive on the formula. A proof by recursion on
the form index that a *concrete* form satisfies them puts `Semiformula.rec` "below" towers on the
concrete form into the proof term, which the second kernel (nanoda) cannot compare; so the
concrete-form facts are proved for these inductive mirrors (whose constructors leave nothing to
unfold), and transferred by one generic lemma each. -/

/-- `PositiveIn k` as an inductive predicate (the same clauses). -/
inductive PositiveInd (k : ι) : {m : ℕ} → Semiformula (LXIN ι) ξ₁ m → Prop
  | verum {m : ℕ} : PositiveInd k (Semiformula.verum : Semiformula (LXIN ι) ξ₁ m)
  | falsum {m : ℕ} : PositiveInd k (Semiformula.falsum : Semiformula (LXIN ι) ξ₁ m)
  | rel {m a : ℕ} (r : (LXIN ι).Rel a) (v : Fin a → Semiterm (LXIN ι) ξ₁ m) :
      PositiveInd k (Semiformula.rel r v)
  | nrelA {m a : ℕ} (r : Language.oRing.Rel a) (v : Fin a → Semiterm (LXIN ι) ξ₁ m) :
      PositiveInd k (Semiformula.nrel (Sum.inl r) v)
  | nrelX {m : ℕ} (v : Fin 1 → Semiterm (LXIN ι) ξ₁ m) :
      PositiveInd k (Semiformula.nrel (Sum.inr IXRelN.X) v)
  | nrelI {m : ℕ} {j : ι} (h : j ≠ k) (v : Fin 1 → Semiterm (LXIN ι) ξ₁ m) :
      PositiveInd k (Semiformula.nrel (Sum.inr (IXRelN.I j)) v)
  | and {m : ℕ} {φ ψ : Semiformula (LXIN ι) ξ₁ m} :
      PositiveInd k φ → PositiveInd k ψ → PositiveInd k (φ ⋏ ψ)
  | or {m : ℕ} {φ ψ : Semiformula (LXIN ι) ξ₁ m} :
      PositiveInd k φ → PositiveInd k ψ → PositiveInd k (φ ⋎ ψ)
  | all {m : ℕ} {φ : Semiformula (LXIN ι) ξ₁ (m + 1)} : PositiveInd k φ → PositiveInd k (∀¹ φ)
  | exs {m : ℕ} {φ : Semiformula (LXIN ι) ξ₁ (m + 1)} : PositiveInd k φ → PositiveInd k (∃¹ φ)

/-- `LevelBounded k` as an inductive predicate (the same clauses). -/
inductive LevelBoundedInd [PartialOrder ι] (k : ι) :
    {m : ℕ} → Semiformula (LXIN ι) ξ₁ m → Prop
  | verum {m : ℕ} : LevelBoundedInd k (Semiformula.verum : Semiformula (LXIN ι) ξ₁ m)
  | falsum {m : ℕ} : LevelBoundedInd k (Semiformula.falsum : Semiformula (LXIN ι) ξ₁ m)
  | relA {m a : ℕ} (r : Language.oRing.Rel a) (v : Fin a → Semiterm (LXIN ι) ξ₁ m) :
      LevelBoundedInd k (Semiformula.rel (Sum.inl r) v)
  | relX {m : ℕ} (v : Fin 1 → Semiterm (LXIN ι) ξ₁ m) :
      LevelBoundedInd k (Semiformula.rel (Sum.inr IXRelN.X) v)
  | relI {m : ℕ} {j : ι} (h : j ≤ k) (v : Fin 1 → Semiterm (LXIN ι) ξ₁ m) :
      LevelBoundedInd k (Semiformula.rel (Sum.inr (IXRelN.I j)) v)
  | nrelA {m a : ℕ} (r : Language.oRing.Rel a) (v : Fin a → Semiterm (LXIN ι) ξ₁ m) :
      LevelBoundedInd k (Semiformula.nrel (Sum.inl r) v)
  | nrelX {m : ℕ} (v : Fin 1 → Semiterm (LXIN ι) ξ₁ m) :
      LevelBoundedInd k (Semiformula.nrel (Sum.inr IXRelN.X) v)
  | nrelI {m : ℕ} {j : ι} (h : j ≤ k) (v : Fin 1 → Semiterm (LXIN ι) ξ₁ m) :
      LevelBoundedInd k (Semiformula.nrel (Sum.inr (IXRelN.I j)) v)
  | and {m : ℕ} {φ ψ : Semiformula (LXIN ι) ξ₁ m} :
      LevelBoundedInd k φ → LevelBoundedInd k ψ → LevelBoundedInd k (φ ⋏ ψ)
  | or {m : ℕ} {φ ψ : Semiformula (LXIN ι) ξ₁ m} :
      LevelBoundedInd k φ → LevelBoundedInd k ψ → LevelBoundedInd k (φ ⋎ ψ)
  | all {m : ℕ} {φ : Semiformula (LXIN ι) ξ₁ (m + 1)} :
      LevelBoundedInd k φ → LevelBoundedInd k (∀¹ φ)
  | exs {m : ℕ} {φ : Semiformula (LXIN ι) ξ₁ (m + 1)} :
      LevelBoundedInd k φ → LevelBoundedInd k (∃¹ φ)

/-- **Generic lemma**: `PositiveInd` implies `PositiveIn` (induction on the inductive, with a
variable formula). -/
theorem positiveIn_of_ind {k : ι} {m : ℕ} {φ : Semiformula (LXIN ι) ξ₁ m}
    (h : PositiveInd k φ) : PositiveIn k φ := by
  induction h with
  | verum => exact trivial
  | falsum => exact trivial
  | rel r v => exact trivial
  | nrelA r v => exact trivial
  | nrelX v => exact trivial
  | nrelI h v => exact h
  | and _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | or _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | all _ ih => exact ih
  | exs _ ih => exact ih

/-- **Generic lemma**: `LevelBoundedInd` implies `LevelBounded`. -/
theorem levelBounded_of_ind [PartialOrder ι] {k : ι} {m : ℕ} {φ : Semiformula (LXIN ι) ξ₁ m}
    (h : LevelBoundedInd k φ) : LevelBounded k φ := by
  induction h with
  | verum => exact trivial
  | falsum => exact trivial
  | relA r v => exact trivial
  | relX v => exact trivial
  | relI h v => exact h
  | nrelA r v => exact trivial
  | nrelX v => exact trivial
  | nrelI h v => exact h
  | and _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | or _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | all _ ih => exact ih
  | exs _ ih => exact ih

theorem positiveInd_lMap (k : ι) {m : ℕ} (φ : Semiformula ℒₒᵣ ξ₁ m) :
    PositiveInd k (Semiformula.lMap (toLXIN ι) φ) ∧
      PositiveInd k (∼(Semiformula.lMap (toLXIN ι) φ)) := by
  induction φ with
  | verum => exact ⟨PositiveInd.verum, PositiveInd.falsum⟩
  | falsum => exact ⟨PositiveInd.falsum, PositiveInd.verum⟩
  | rel r v => exact ⟨PositiveInd.rel _ _, PositiveInd.nrelA r _⟩
  | nrel r v => exact ⟨PositiveInd.nrelA r _, PositiveInd.rel _ _⟩
  | and _ _ ih1 ih2 => exact ⟨PositiveInd.and ih1.1 ih2.1, PositiveInd.or ih1.2 ih2.2⟩
  | or _ _ ih1 ih2 => exact ⟨PositiveInd.or ih1.1 ih2.1, PositiveInd.and ih1.2 ih2.2⟩
  | all _ ih => exact ⟨PositiveInd.all ih.1, PositiveInd.exs ih.2⟩
  | exs _ ih => exact ⟨PositiveInd.exs ih.1, PositiveInd.all ih.2⟩

theorem levelBoundedInd_lMap [PartialOrder ι] (k : ι) {m : ℕ} (φ : Semiformula ℒₒᵣ ξ₁ m) :
    LevelBoundedInd k (Semiformula.lMap (toLXIN ι) φ) ∧
      LevelBoundedInd k (∼(Semiformula.lMap (toLXIN ι) φ)) := by
  induction φ with
  | verum => exact ⟨LevelBoundedInd.verum, LevelBoundedInd.falsum⟩
  | falsum => exact ⟨LevelBoundedInd.falsum, LevelBoundedInd.verum⟩
  | rel r v => exact ⟨LevelBoundedInd.relA r _, LevelBoundedInd.nrelA r _⟩
  | nrel r v => exact ⟨LevelBoundedInd.nrelA r _, LevelBoundedInd.relA r _⟩
  | and _ _ ih1 ih2 => exact ⟨LevelBoundedInd.and ih1.1 ih2.1, LevelBoundedInd.or ih1.2 ih2.2⟩
  | or _ _ ih1 ih2 => exact ⟨LevelBoundedInd.or ih1.1 ih2.1, LevelBoundedInd.and ih1.2 ih2.2⟩
  | all _ ih => exact ⟨LevelBoundedInd.all ih.1, LevelBoundedInd.exs ih.2⟩
  | exs _ ih => exact ⟨LevelBoundedInd.exs ih.1, LevelBoundedInd.all ih.2⟩

theorem positiveInd_rew {k : ι} {ξ₂ : Type*} {m₁ : ℕ} {φ : Semiformula (LXIN ι) ξ₁ m₁}
    (h : PositiveInd k φ) : ∀ {m₂ : ℕ} (ω : Rew (LXIN ι) ξ₁ m₁ ξ₂ m₂), PositiveInd k (ω ▹ φ) := by
  induction h with
  | verum => intro m₂ ω; exact PositiveInd.verum
  | falsum => intro m₂ ω; exact PositiveInd.falsum
  | rel r v => intro m₂ ω; exact PositiveInd.rel r _
  | nrelA r v => intro m₂ ω; exact PositiveInd.nrelA r _
  | nrelX v => intro m₂ ω; exact PositiveInd.nrelX _
  | nrelI h v => intro m₂ ω; exact PositiveInd.nrelI h _
  | and _ _ ih1 ih2 =>
    intro m₂ ω
    rw [LogicalConnective.HomClass.map_and]
    exact PositiveInd.and (ih1 ω) (ih2 ω)
  | or _ _ ih1 ih2 =>
    intro m₂ ω
    rw [LogicalConnective.HomClass.map_or]
    exact PositiveInd.or (ih1 ω) (ih2 ω)
  | all _ ih =>
    intro m₂ ω
    rw [Rewriting.app_all]
    exact PositiveInd.all (ih ω.q)
  | exs _ ih =>
    intro m₂ ω
    rw [Rewriting.app_exs]
    exact PositiveInd.exs (ih ω.q)

theorem levelBoundedInd_rew [PartialOrder ι] {k : ι} {ξ₂ : Type*} {m₁ : ℕ}
    {φ : Semiformula (LXIN ι) ξ₁ m₁} (h : LevelBoundedInd k φ) :
    ∀ {m₂ : ℕ} (ω : Rew (LXIN ι) ξ₁ m₁ ξ₂ m₂), LevelBoundedInd k (ω ▹ φ) := by
  induction h with
  | verum => intro m₂ ω; exact LevelBoundedInd.verum
  | falsum => intro m₂ ω; exact LevelBoundedInd.falsum
  | relA r v => intro m₂ ω; exact LevelBoundedInd.relA r _
  | relX v => intro m₂ ω; exact LevelBoundedInd.relX _
  | relI h v => intro m₂ ω; exact LevelBoundedInd.relI h _
  | nrelA r v => intro m₂ ω; exact LevelBoundedInd.nrelA r _
  | nrelX v => intro m₂ ω; exact LevelBoundedInd.nrelX _
  | nrelI h v => intro m₂ ω; exact LevelBoundedInd.nrelI h _
  | and _ _ ih1 ih2 =>
    intro m₂ ω
    rw [LogicalConnective.HomClass.map_and]
    exact LevelBoundedInd.and (ih1 ω) (ih2 ω)
  | or _ _ ih1 ih2 =>
    intro m₂ ω
    rw [LogicalConnective.HomClass.map_or]
    exact LevelBoundedInd.or (ih1 ω) (ih2 ω)
  | all _ ih =>
    intro m₂ ω
    rw [Rewriting.app_all]
    exact LevelBoundedInd.all (ih ω.q)
  | exs _ ih =>
    intro m₂ ω
    rw [Rewriting.app_exs]
    exact LevelBoundedInd.exs (ih ω.q)

section IndForms

variable (F : OrderFormulas) (ix : ℕ → ι)

/-- One step of `DF`, over an abstract `D` and `e` (no concrete formula is involved). -/
theorem positiveInd_step_pos {m : ℕ} (k i : ι) {D : Semiformula (LXIN ι) ξ₁ m}
    {e : Semiformula (LXIN ι) ξ₁ (m + 1)} (hD : PositiveInd k D) (he : PositiveInd k (∼e)) :
    PositiveInd k (D ⋏ (∀¹ (e 🡒 Iat i #0))) :=
  PositiveInd.and hD (PositiveInd.all (PositiveInd.or he (PositiveInd.rel _ _)))

theorem positiveInd_step_neg {m : ℕ} (k i : ι) {D : Semiformula (LXIN ι) ξ₁ m}
    {e : Semiformula (LXIN ι) ξ₁ (m + 1)} (hD : PositiveInd k (∼D)) (he : PositiveInd k e)
    (hi : i ≠ k) : PositiveInd k (∼(D ⋏ (∀¹ (e 🡒 Iat i #0)))) := by
  have hee : PositiveInd k (∼∼e) := by
    rw [TildeInvolutive.tilde_involutive]; exact he
  exact PositiveInd.or hD (PositiveInd.exs (PositiveInd.and hee (PositiveInd.nrelI hi _)))

theorem levelBoundedInd_step_pos [PartialOrder ι] {m : ℕ} (k i : ι)
    {D : Semiformula (LXIN ι) ξ₁ m} {e : Semiformula (LXIN ι) ξ₁ (m + 1)}
    (hD : LevelBoundedInd k D) (he : LevelBoundedInd k (∼e)) (hi : i ≤ k) :
    LevelBoundedInd k (D ⋏ (∀¹ (e 🡒 Iat i #0))) :=
  LevelBoundedInd.and hD (LevelBoundedInd.all (LevelBoundedInd.or he (LevelBoundedInd.relI hi _)))

theorem levelBoundedInd_step_neg [PartialOrder ι] {m : ℕ} (k i : ι)
    {D : Semiformula (LXIN ι) ξ₁ m} {e : Semiformula (LXIN ι) ξ₁ (m + 1)}
    (hD : LevelBoundedInd k (∼D)) (he : LevelBoundedInd k e) (hi : i ≤ k) :
    LevelBoundedInd k (∼(D ⋏ (∀¹ (e 🡒 Iat i #0)))) := by
  have hee : LevelBoundedInd k (∼∼e) := by
    rw [TildeInvolutive.tilde_involutive]; exact he
  exact LevelBoundedInd.or hD (LevelBoundedInd.exs (LevelBoundedInd.and hee
    (LevelBoundedInd.nrelI hi _)))

theorem positiveInd_DF (k : ι) (j : ℕ) : PositiveInd k (DF F ix j) ∧
    ((∀ i < j, ix i ≠ k) → PositiveInd k (∼DF F ix j)) := by
  induction j with
  | zero => exact ⟨(positiveInd_lMap k _).1, fun _ => (positiveInd_lMap k _).2⟩
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    exact ⟨positiveInd_step_pos k (ix j) h1 (positiveInd_lMap k _).2,
      fun hne => positiveInd_step_neg k (ix j) (h2 fun i hi => hne i (by omega))
        (positiveInd_lMap k _).1 (hne j (by omega))⟩

theorem levelBoundedInd_DF [PartialOrder ι] (k : ι) (j : ℕ) (hle : ∀ i < j, ix i ≤ k) :
    LevelBoundedInd k (DF F ix j) ∧ LevelBoundedInd k (∼DF F ix j) := by
  induction j with
  | zero => exact ⟨(levelBoundedInd_lMap k _).1, (levelBoundedInd_lMap k _).2⟩
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hle i (by omega)
    have hj : ix j ≤ k := hle j (by omega)
    exact ⟨levelBoundedInd_step_pos k (ix j) h1 (levelBoundedInd_lMap k _).2 hj,
      levelBoundedInd_step_neg k (ix j) h2 (levelBoundedInd_lMap k _).1 hj⟩

theorem positiveInd_wForm (k : ℕ) (hne : ∀ i < k, ix i ≠ ix k) :
    PositiveInd (ix k) (wForm F ix k) := by
  cases k with
  | zero =>
    exact PositiveInd.all (PositiveInd.or (positiveInd_lMap _ _).2 (PositiveInd.rel _ _))
  | succ k =>
    have hD := positiveInd_DF F ix (ix (k + 1)) (k + 1)
    refine PositiveInd.and hD.1 (PositiveInd.and (positiveInd_lMap _ _).1
      (PositiveInd.all (PositiveInd.or (PositiveInd.or ?_ (positiveInd_lMap _ _).2)
        (PositiveInd.rel _ _))))
    show PositiveInd (ix (k + 1)) (∼(Rew.subst ![#0] ▹ DF F ix (k + 1)))
    rw [← LogicalConnective.HomClass.map_neg]
    exact positiveInd_rew (hD.2 hne) _

theorem levelBoundedInd_wForm [PartialOrder ι] (k : ℕ) (hle : ∀ i ≤ k, ix i ≤ ix k) :
    LevelBoundedInd (ix k) (wForm F ix k) := by
  cases k with
  | zero =>
    exact LevelBoundedInd.all (LevelBoundedInd.or (levelBoundedInd_lMap _ _).2
      (LevelBoundedInd.relI le_rfl _))
  | succ k =>
    have hD := levelBoundedInd_DF F ix (ix (k + 1)) (k + 1) fun i hi => hle i (by omega)
    refine LevelBoundedInd.and hD.1 (LevelBoundedInd.and (levelBoundedInd_lMap _ _).1
      (LevelBoundedInd.all (LevelBoundedInd.or
        (LevelBoundedInd.or ?_ (levelBoundedInd_lMap _ _).2) (LevelBoundedInd.relI le_rfl _))))
    show LevelBoundedInd (ix (k + 1)) (∼(Rew.subst ![#0] ▹ DF F ix (k + 1)))
    rw [← LogicalConnective.HomClass.map_neg]
    exact levelBoundedInd_rew hD.2 _

end IndForms

variable (F : OrderFormulas) (ix : ℕ → ι)

/-- `D_j` is positive in every predicate, and its negation in every predicate other than
those of the levels `< j`. -/
theorem positiveIn_DF (k : ι) : ∀ j : ℕ, PositiveIn k (DF F ix j) ∧
    ((∀ i < j, ix i ≠ k) → PositiveIn k (∼DF F ix j)) :=
  fun j => ⟨positiveIn_of_ind (positiveInd_DF F ix k j).1,
    fun h => positiveIn_of_ind ((positiveInd_DF F ix k j).2 h)⟩

/-- `D_j` mentions only the predicates of the levels `< j`. -/
theorem levelBounded_DF [PartialOrder ι] (k : ι) :
    ∀ j : ℕ, (∀ i < j, ix i ≤ k) → LevelBounded k (DF F ix j) ∧ LevelBounded k (∼DF F ix j) :=
  fun j hle => ⟨levelBounded_of_ind (levelBoundedInd_DF F ix k j hle).1,
    levelBounded_of_ind (levelBoundedInd_DF F ix k j hle).2⟩

/-- **The form of level `k` is positive in its own predicate** (the lower predicates are
distinct from it). -/
theorem positiveIn_wForm (k : ℕ) (hne : ∀ i < k, ix i ≠ ix k) :
    PositiveIn (ix k) (wForm F ix k) :=
  positiveIn_of_ind (positiveInd_wForm F ix k hne)

/-- **The form of level `k` mentions only the predicates of the levels `≤ k`.** -/
theorem levelBounded_wForm [PartialOrder ι] (k : ℕ) (hle : ∀ i ≤ k, ix i ≤ ix k) :
    LevelBounded (ix k) (wForm F ix k) :=
  levelBounded_of_ind (levelBoundedInd_wForm F ix k hle)

end Syntax

theorem wForms_positive (F : OrderFormulas) (n : ℕ) : FamilyPositive (WForms F n) := by
  intro k
  have hn : 0 < n := k.pos
  have e : ixFin hn k.val = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
  show PositiveIn k (wForm F (ixFin hn) k.val)
  have := positiveIn_wForm F (ixFin hn) k.val fun i hi h => by
    have := congrArg Fin.val h
    rw [ixFin_val, ixFin_val, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt k.isLt] at this
    omega
  rwa [e] at this

theorem wForms_levelBounded (F : OrderFormulas) (n : ℕ) :
    FamilyLevelBounded (WForms F n) := by
  intro k
  have hn : 0 < n := k.pos
  have e : ixFin hn k.val = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
  show LevelBounded k (wForm F (ixFin hn) k.val)
  have := levelBounded_wForm F (ixFin hn) k.val fun i hi => by
    show (ixFin hn i).val ≤ (ixFin hn k.val).val
    rw [ixFin_val, ixFin_val, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt k.isLt]
    exact hi
  rwa [e] at this

/-- **`ID_n` for the well-ordering forms is consistent** (it is true in the iterated
least-fixed-point model on `ℕ`). -/
theorem idn_wForms_consistent (F : OrderFormulas) (n : ℕ) :
    IDn n (WForms F n) ⊬ (⊥ : Sentence (LXIn n)) :=
  IDn_consistent n _ (wForms_positive F n) (wForms_levelBounded F n)

/-- **`ID_{<ω}` for the well-ordering forms is consistent.** -/
theorem idlt_wForms_consistent (F : OrderFormulas) :
    IDlt (WFormsOmega F) ⊬ (⊥ : Sentence LXIomega) :=
  IDlt_consistent _
    (fun k => positiveIn_wForm F id k fun i hi h => by simp only [id] at h; omega)
    (fun k => levelBounded_wForm F id k fun i hi => hi)

end OrdinalAnalysis.IDn.Upper
