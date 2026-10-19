module

public import OrdinalAnalysis.KPi.RS.Card
public import OrdinalAnalysis.KPi.SoundAux0

@[expose] public section

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.Sound

open OrdinalAnalysis.KPi.RS Ordinal

section Sem

variable (R : Set Ordinal.{1})

/-- `a ∈ b` in the RS term model (B92 (⊨2)): some `t` of level `< |b|` satisfies `t ∈° b` and `t = a`. -/
def Mem (a b : T) : Prop :=
  ∃ t : Tlt b.level, RSTrue R (memInst t.1 b) ∧ RSTrue R (eqS t.1 a)

/-- `a = b` (B92's defined equality `a ⊆ b ∧ b ⊆ a`), as truth of the sentence `eqS a b`. -/
def Eqv (a b : T) : Prop := RSTrue R (eqS a b)

/-- `a ⊆ b`: every `t ∈° a` (of level `< |a|`) is a member of `b`. -/
def Sub (a b : T) : Prop :=
  ∀ t : Tlt a.level, RSTrue R (memInst t.1 a) → Mem R t.1 b

theorem RSTrue_mem_iff {n : ℕ} (i j : Fin n) (ρ : Fin n → T) :
    RSTrue R (RSS.base (D0.mem i j) ρ) ↔ Mem R (ρ i) (ρ j) := RSTrue_mem R i j ρ

theorem RSTrue_sub_iff {n : ℕ} (i j : Fin n) (ρ : Fin n → T) :
    RSTrue R (RSS.base (D0.subset i j) ρ) ↔ Sub R (ρ i) (ρ j) := by
  unfold D0.subset
  rw [RSTrue_ball]
  refine forall_congr' fun t => ?_
  rw [RSTrue_neg, RSTrue_mem_iff]
  simp only [ext_last, ext_castSucc]
  exact imp_iff_not_or.symm

theorem eqv_iff (a b : T) : Eqv R a b ↔ Sub R a b ∧ Sub R b a := by
  unfold Eqv eqS D0.eqf
  rw [RSTrue_band, RSTrue_sub_iff, RSTrue_sub_iff]
  rfl

/-! ### `=` is an equivalence relation (induction on levels, not on ranks) -/

theorem Eqv.symm {a b : T} (h : Eqv R a b) : Eqv R b a := by
  rw [eqv_iff] at h ⊢; exact ⟨h.2, h.1⟩

theorem eqv_refl_aux : ∀ (δ : Ordinal.{1}) (a : T), a.level = δ → Eqv R a a := by
  intro δ
  induction δ using WellFoundedLT.induction with
  | _ δ ih =>
  intro a ha
  have hs : Sub R a a := fun t ht => ⟨t, ht, ih t.1.level (ha ▸ t.2) t.1 rfl⟩
  exact (eqv_iff R a a).2 ⟨hs, hs⟩

theorem Eqv.refl (a : T) : Eqv R a a := eqv_refl_aux R _ a rfl

theorem sub_trans_aux (δ : Ordinal.{1})
    (ih : ∀ δ' < δ, ∀ x y z : T, x.level ≤ δ' → y.level ≤ δ' → z.level ≤ δ' →
      Eqv R x y → Eqv R y z → Eqv R x z)
    {x y z : T} (hx : x.level ≤ δ) (hy : y.level ≤ δ) (hz : z.level ≤ δ)
    (h1 : Sub R x y) (h2 : Sub R y z) : Sub R x z := by
  intro t ht
  obtain ⟨s, hs, hst⟩ := h1 t ht
  obtain ⟨u, hu, hus⟩ := h2 s hs
  refine ⟨u, hu, ?_⟩
  have hlt : max (max u.1.level s.1.level) t.1.level < δ :=
    max_lt (max_lt (lt_of_lt_of_le u.2 hz) (lt_of_lt_of_le s.2 hy)) (lt_of_lt_of_le t.2 hx)
  exact ih _ hlt u.1 s.1 t.1 (by simp) (by simp) (by simp) hus hst

theorem eqv_trans_aux : ∀ δ : Ordinal.{1}, ∀ x y z : T, x.level ≤ δ → y.level ≤ δ → z.level ≤ δ →
    Eqv R x y → Eqv R y z → Eqv R x z := by
  intro δ
  induction δ using WellFoundedLT.induction with
  | _ δ ih =>
  intro x y z hx hy hz h1 h2
  rw [eqv_iff] at h1 h2 ⊢
  exact ⟨sub_trans_aux R δ ih hx hy hz h1.1 h2.1, sub_trans_aux R δ ih hz hy hx h2.2 h1.2⟩

theorem Eqv.trans {x y z : T} (h1 : Eqv R x y) (h2 : Eqv R y z) : Eqv R x z :=
  eqv_trans_aux R (max (max x.level y.level) z.level) x y z
    (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_right _ _) h1 h2

/-- `Eqv (L κ) a` forces `κ ≤ |a|`. -/
theorem level_le_of_eqv_L : ∀ (κ : Ordinal.{1}) (a : T), Eqv R (T.L κ) a → κ ≤ a.level := by
  intro κ
  induction κ using WellFoundedLT.induction with
  | _ κ ih =>
  intro a h
  rw [eqv_iff] at h
  refine le_of_forall_lt fun δ hδ => ?_
  obtain ⟨s, hs, hst⟩ := h.1 ⟨T.L δ, hδ⟩ (RSTrue_memInst_L R _ _)
  exact lt_of_le_of_lt (ih δ hδ s.1 (Eqv.symm R hst)) s.2

/-! ### `∈` and `Ad` are congruences for `=` -/

theorem Mem.congr_left {a a' b : T} (h : Eqv R a a') : Mem R a b → Mem R a' b :=
  fun ⟨t, ht, he⟩ => ⟨t, ht, Eqv.trans R he h⟩

theorem Mem.congr_right {a b b' : T} (h : Eqv R b b') : Mem R a b → Mem R a b' := by
  rintro ⟨t, ht, he⟩
  obtain ⟨s, hs, hst⟩ := ((eqv_iff R b b').1 h).1 t ht
  exact ⟨s, hs, Eqv.trans R hst he⟩

theorem mem_L_iff (a : T) (γ : Ordinal.{1}) : Mem R a (T.L γ) ↔ ∃ s : T, s.level < γ ∧ Eqv R s a :=
  ⟨fun ⟨t, _, h⟩ => ⟨t.1, t.2, h⟩, fun ⟨s, hs, h⟩ => ⟨⟨s, hs⟩, RSTrue_memInst_L R _ _, h⟩⟩

theorem acc_congr {t y : T} (h : Acc (Mem R) t) (e : Eqv R t y) : Acc (Mem R) y :=
  ⟨y, fun _ hz => h.inv (Mem.congr_right R (Eqv.symm R e) hz)⟩

theorem acc_mem : ∀ (δ : Ordinal.{1}) (a : T), a.level = δ → Acc (Mem R) a := by
  intro δ
  induction δ using WellFoundedLT.induction with
  | _ δ ih =>
  intro a ha
  refine ⟨a, fun y hy => ?_⟩
  obtain ⟨t, -, ht⟩ := hy
  exact acc_congr R (ih t.1.level (ha ▸ t.2) t.1 rfl) ht

/-- `∈` of the RS term model is well-founded. -/
theorem wf_Mem : WellFounded (Mem R) := ⟨fun a => acc_mem R _ a rfl⟩

/-- `Ad(a)` in the RS term model (B92 (⊨3)). -/
def AdP (a : T) : Prop := RSTrue R (RSS.base (D0.ad 0) ![a])

theorem AdP_iff (a : T) : AdP R a ↔ ∃ κ : Ordinal.{1}, κ ∈ R ∧ 0 < κ ∧ Eqv R (T.L κ) a := by
  unfold AdP
  rw [RSTrue_ad]
  constructor
  · rintro ⟨⟨κ, hR, h0, _⟩, h⟩; exact ⟨κ, hR, h0, h⟩
  · rintro ⟨κ, hR, h0, h⟩
    exact ⟨⟨κ, hR, h0, level_le_of_eqv_L R κ a h⟩, h⟩

theorem AdP.congr {a a' : T} (h : Eqv R a a') (ha : AdP R a) : AdP R a' := by
  rw [AdP_iff] at ha ⊢
  obtain ⟨κ, hR, h0, he⟩ := ha
  exact ⟨κ, hR, h0, Eqv.trans R he h⟩

theorem AdP_L {κ : Ordinal.{1}} (hR : κ ∈ R) (h0 : 0 < κ) : AdP R (T.L κ) :=
  (AdP_iff R _).2 ⟨κ, hR, h0, Eqv.refl R _⟩

end Sem


/-! ### The model -/

/-- The data of the standard model: `R ⊆ RegOrd` (B92's class `R`), the level bound `lam`
(regular, with `R` cofinal below it). -/
structure Params where
  R : Set Ordinal.{1}
  lam : Ordinal.{1}
  hR : R ⊆ RegOrd
  hlam : lam ∈ RegOrd
  hcof : ∀ α < lam, ∃ κ ∈ R, α < κ ∧ κ < lam

/-- The RS term model: the terms of level `< lam`. -/
abbrev RSModel (p : Params) : Type 2 := Tlt p.lam

namespace RSModel

variable (p : Params)

theorem termReg_lam : TermReg p.lam := by
  obtain ⟨c, hc, h0, e⟩ := p.hlam
  rw [e]; exact termReg_of_regular hc h0

theorem lam_pos : 0 < p.lam := (termReg_lam p).pos

theorem termReg_of_mem {κ : Ordinal.{1}} (h : κ ∈ p.R) : TermReg κ := by
  obtain ⟨c, hc, h0, e⟩ := p.hR h
  rw [e]; exact termReg_of_regular hc h0

instance : Nonempty (RSModel p) := ⟨⟨T.L 0, by simpa [T.level, T.L, PT.level] using lam_pos p⟩⟩

/-- `∈` on the model. -/
def rel (a b : RSModel p) : Prop := Mem p.R a.1 b.1

/-- `Ad` on the model. -/
def ad (a : RSModel p) : Prop := AdP p.R a.1

theorem eqm_iff (a b : RSModel p) : Eqm (rel p) a b ↔ Eqv p.R a.1 b.1 := by
  rw [eqv_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · exact h1 ⟨t.1, lt_trans t.2 a.2⟩ ⟨t, ht, Eqv.refl _ _⟩
    · exact h2 ⟨t.1, lt_trans t.2 b.2⟩ ⟨t, ht, Eqv.refl _ _⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨t, ht, hte⟩ := hx
      obtain ⟨s, hs, hst⟩ := h1 t ht
      exact ⟨s, hs, Eqv.trans _ hst hte⟩
    · obtain ⟨t, ht, hte⟩ := hx
      obtain ⟨s, hs, hst⟩ := h2 t ht
      exact ⟨s, hs, Eqv.trans _ hst hte⟩

/-- **(Ext) holds** in the model: `=` is a congruence for `∈` and `Ad`. -/
theorem extOK : ExtOK (rel p) (ad p) := by
  intro x y z e
  rw [eqm_iff] at e
  exact ⟨Mem.congr_left _ e, AdP.congr _ e⟩

theorem wf_rel : WellFounded (rel p) :=
  InvImage.wf (fun a : RSModel p => a.1) (wf_Mem p.R)

end RSModel

end OrdinalAnalysis.KPi.Sound
