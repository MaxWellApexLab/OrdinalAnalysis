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

variable (F : OrderFormulas) (ix : ℕ → ι)

/-- `D_j` is positive in every predicate, and its negation in every predicate other than
those of the levels `< j`. -/
theorem positiveIn_DF (k : ι) : ∀ j : ℕ, PositiveIn k (DF F ix j) ∧
    ((∀ i < j, ix i ≠ k) → PositiveIn k (∼DF F ix j))
  | 0 => ⟨(positive_lMap_toLXIN k _).1, fun _ => (positive_lMap_toLXIN k _).2⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := positiveIn_DF k j
    refine ⟨⟨h1, (positive_lMap_toLXIN k _).2, trivial⟩, fun hne => ?_⟩
    refine ⟨h2 fun i hi => hne i (by omega), ?_, hne j (by omega)⟩
    show PositiveIn k (∼∼(lm (inEAt j)))
    rw [TildeInvolutive.tilde_involutive]
    exact (positive_lMap_toLXIN k _).1

/-- `D_j` mentions only the predicates of the levels `< j`. -/
theorem levelBounded_DF [PartialOrder ι] (k : ι) :
    ∀ j : ℕ, (∀ i < j, ix i ≤ k) → LevelBounded k (DF F ix j) ∧ LevelBounded k (∼DF F ix j)
  | 0, _ => ⟨(levelBounded_lMap_toLXIN k _).1, (levelBounded_lMap_toLXIN k _).2⟩
  | j + 1, hle => by
    obtain ⟨h1, h2⟩ := levelBounded_DF k j fun i hi => hle i (by omega)
    refine ⟨⟨h1, (levelBounded_lMap_toLXIN k _).2, hle j (by omega)⟩, ⟨h2, ?_, hle j (by omega)⟩⟩
    show LevelBounded k (∼∼(lm (inEAt j)))
    rw [TildeInvolutive.tilde_involutive]
    exact (levelBounded_lMap_toLXIN k _).1

/-- **The form of level `k` is positive in its own predicate** (the lower predicates are
distinct from it). -/
theorem positiveIn_wForm (k : ℕ) (hne : ∀ i < k, ix i ≠ ix k) :
    PositiveIn (ix k) (wForm F ix k) := by
  cases k with
  | zero => exact ⟨(positive_lMap_toLXIN _ _).2, trivial⟩
  | succ k =>
    refine ⟨(positiveIn_DF F ix (ix (k + 1)) (k + 1)).1, (positive_lMap_toLXIN _ _).1, ?_, trivial⟩
    refine ⟨?_, (positive_lMap_toLXIN _ _).2⟩
    show PositiveIn (ix (k + 1)) (∼(Rew.subst ![#0] ▹ DF F ix (k + 1)))
    rw [← LogicalConnective.HomClass.map_neg]
    exact positiveIn_rew _ _ _ ((positiveIn_DF F ix (ix (k + 1)) (k + 1)).2 hne)

/-- **The form of level `k` mentions only the predicates of the levels `≤ k`.** -/
theorem levelBounded_wForm [PartialOrder ι] (k : ℕ) (hle : ∀ i ≤ k, ix i ≤ ix k) :
    LevelBounded (ix k) (wForm F ix k) := by
  cases k with
  | zero => exact ⟨(levelBounded_lMap_toLXIN _ _).2, le_rfl⟩
  | succ k =>
    have hD := levelBounded_DF F ix (ix (k + 1)) (k + 1) fun i hi => hle i (by omega)
    refine ⟨hD.1, (levelBounded_lMap_toLXIN _ _).1, ?_, le_rfl⟩
    refine ⟨?_, (levelBounded_lMap_toLXIN _ _).2⟩
    show LevelBounded (ix (k + 1)) (∼(Rew.subst ![#0] ▹ DF F ix (k + 1)))
    rw [← LogicalConnective.HomClass.map_neg]
    exact levelBounded_rew _ _ _ hD.2

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
