module

public import OrdinalAnalysis.KPi.SoundAux1

/-!
# KPi soundness, part 4: the guard `D_κ`, and the comprehension cores for Pair / Union / Col

In the RS term model `RSModel p` (terms of level `< lam`), the guard
`D_κ a :≡ a ∈ L_κ` (for `κ ≤ lam`, `κ` a successor limit) is the set of elements equal to a term of
level `< κ`.  For `κ = lam` it is everything; for `κ = |x|` with `Ad x` it is the set `{a | a ∈ x}`.
The "core" lemmas below are the (Pair), (Union), (Δ₀-Col) comprehension principles in *guard form*;
they serve both the model itself (`κ = lam`) and (Ad.3) (`κ ∈ R`).  The (Δ₀-Sep) core is in
`SoundAux2` (it needs the translation `tr`).
-/

@[expose] public section

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.Sound

open LO LO.FirstOrder OrdinalAnalysis.KPi.RS Ordinal

@[simp] theorem T_L_level (γ : Ordinal.{1}) : (T.L γ).level = γ := rfl

theorem add_one_lt_of_limit {κ b : Ordinal.{1}} (hlim : Order.IsSuccLimit κ) (h : b < κ) :
    b + 1 < κ := by
  have := hlim.succ_lt h
  rwa [Order.succ_eq_add_one] at this

namespace RSModel

variable (p : Params)

/-- the level constant `L_γ` as an element of the model (`γ < lam`). -/
def lvl {γ : Ordinal.{1}} (h : γ < p.lam) : RSModel p := ⟨T.L γ, by simpa using h⟩

@[simp] theorem lvl_val {γ : Ordinal.{1}} (h : γ < p.lam) : (lvl p h).1 = T.L γ := rfl

/-- the guard `D_κ = {a | a ∈ L_κ}`. -/
def Dk (κ : Ordinal.{1}) (a : RSModel p) : Prop := Mem p.R a.1 (T.L κ)

theorem Dk_iff (κ : Ordinal.{1}) (a : RSModel p) :
    Dk p κ a ↔ ∃ s : T, s.level < κ ∧ Eqv p.R s a.1 := mem_L_iff p.R a.1 κ

theorem Dk_lam (a : RSModel p) : Dk p p.lam a := (Dk_iff p _ a).2 ⟨a.1, a.2, Eqv.refl _ _⟩

theorem Dk_of_rep {κ : Ordinal.{1}} {a : RSModel p} {s : T} (hs : s.level < κ)
    (he : Eqv p.R s a.1) : Dk p κ a := (Dk_iff p κ a).2 ⟨s, hs, he⟩

theorem Dk_lvl {κ γ : Ordinal.{1}} (h : γ < p.lam) (hγ : γ < κ) : Dk p κ (lvl p h) :=
  Dk_of_rep p (s := T.L γ) hγ (Eqv.refl _ _)

/-- the guard is downward closed under `∈`. -/
theorem Dk_trans {κ : Ordinal.{1}} {a y : RSModel p} (ha : Dk p κ a) (hy : rel p y a) :
    Dk p κ y := by
  obtain ⟨s, hs, he⟩ := (Dk_iff p κ a).1 ha
  have h1 : Mem p.R y.1 s := Mem.congr_right p.R (Eqv.symm p.R he) hy
  obtain ⟨t, -, ht⟩ := h1
  exact Dk_of_rep p (lt_trans t.2 hs) ht

/-- below an element equal to `L_κ`, membership is the guard. -/
theorem rel_iff_Dk {κ : Ordinal.{1}} {a x : RSModel p} (hx : Eqv p.R (T.L κ) x.1) :
    rel p a x ↔ Dk p κ a :=
  ⟨fun h => Mem.congr_right p.R (Eqv.symm p.R hx) h, fun h => Mem.congr_right p.R hx h⟩

/-! ### Δ₀-congruence in the model, for the small arities used by the axioms -/

theorem eval_congr1 {φ : Semiformula LAd ℕ 1} (hφ : IsDelta0 φ) (f : ℕ → RSModel p)
    {x x' : RSModel p} (hx : Eqv p.R x.1 x'.1) :
    Semiformula.Eval (s := adStruc (rel p) (ad p)) ![x] f φ ↔
      Semiformula.Eval (s := adStruc (rel p) (ad p)) ![x'] f φ := by
  refine eval_congr_delta0 (extOK p) hφ _ _ f f (fun i => ?_) (fun j => Eqm.refl _)
  fin_cases i
  exact (eqm_iff p x x').2 hx

theorem eval_congr2 {φ : Semiformula LAd ℕ 2} (hφ : IsDelta0 φ) (f : ℕ → RSModel p)
    {x x' y y' : RSModel p} (hx : Eqv p.R x.1 x'.1) (hy : Eqv p.R y.1 y'.1) :
    Semiformula.Eval (s := adStruc (rel p) (ad p)) ![x, y] f φ ↔
      Semiformula.Eval (s := adStruc (rel p) (ad p)) ![x', y'] f φ := by
  refine eval_congr_delta0 (extOK p) hφ _ _ f f (fun i => ?_) (fun j => Eqm.refl _)
  fin_cases i
  · exact (eqm_iff p x x').2 hx
  · exact (eqm_iff p y y').2 hy

/-! ### Pair, Union, Col in guard form -/

theorem core_pair {κ : Ordinal.{1}} (hlim : Order.IsSuccLimit κ) (hκl : κ ≤ p.lam)
    {a b : RSModel p} (ha : Dk p κ a) (hb : Dk p κ b) :
    ∃ c : RSModel p, Dk p κ c ∧ rel p a c ∧ rel p b c := by
  obtain ⟨sa, hsa, hea⟩ := (Dk_iff p κ a).1 ha
  obtain ⟨sb, hsb, heb⟩ := (Dk_iff p κ b).1 hb
  have hγ : max sa.level sb.level + 1 < κ := add_one_lt_of_limit hlim (max_lt hsa hsb)
  have hγl : max sa.level sb.level + 1 < p.lam := lt_of_lt_of_le hγ hκl
  refine ⟨lvl p hγl, Dk_lvl p hγl hγ, ?_, ?_⟩
  · exact (mem_L_iff p.R a.1 _).2
      ⟨sa, lt_of_le_of_lt (le_max_left _ _) (lt_add_one _), hea⟩
  · exact (mem_L_iff p.R b.1 _).2
      ⟨sb, lt_of_le_of_lt (le_max_right _ _) (lt_add_one _), heb⟩

theorem core_union {κ : Ordinal.{1}} (hκl : κ ≤ p.lam) {a : RSModel p} (ha : Dk p κ a) :
    ∃ c : RSModel p, Dk p κ c ∧ ∀ y : RSModel p, rel p y a → ∀ u : RSModel p, rel p u y →
      rel p u c := by
  obtain ⟨s, hs, hes⟩ := (Dk_iff p κ a).1 ha
  have hsl : s.level < p.lam := lt_of_lt_of_le hs hκl
  refine ⟨lvl p hsl, Dk_lvl p hsl hs, ?_⟩
  intro y hy u hu
  have h1 : Mem p.R y.1 s := Mem.congr_right p.R (Eqv.symm p.R hes) hy
  obtain ⟨t, -, ht⟩ := h1
  have h2 : Mem p.R u.1 t.1 := Mem.congr_right p.R (Eqv.symm p.R ht) hu
  obtain ⟨t', -, ht'⟩ := h2
  exact (mem_L_iff p.R u.1 _).2 ⟨t'.1, lt_trans t'.2 t.2, ht'⟩

theorem core_col {κ : Ordinal.{1}} (hreg : TermReg κ) (hκl : κ ≤ p.lam)
    {φ : Semiformula LAd ℕ 2} (hφ : IsDelta0 φ) (f : ℕ → RSModel p) {w : RSModel p}
    (hw : Dk p κ w)
    (H : ∀ x : RSModel p, rel p x w → ∃ y : RSModel p, Dk p κ y ∧
      Semiformula.Eval (s := adStruc (rel p) (ad p)) ![x, y] f φ) :
    ∃ v : RSModel p, Dk p κ v ∧ ∀ x : RSModel p, rel p x w → ∃ y : RSModel p, rel p y v ∧
      Semiformula.Eval (s := adStruc (rel p) (ad p)) ![x, y] f φ := by
  obtain ⟨w', hw'κ, hww'⟩ := (Dk_iff p κ w).1 hw
  have hlim := hreg.1
  have hκ0 : 0 < κ := hreg.pos
  have hl0 : 0 < p.lam := lt_of_lt_of_le hκ0 hκl
  -- for every term `t` of level `< |w'|` choose a witness of level `< κ`
  have hex : ∀ t : Tlt w'.level, ∃ s : RSModel p, s.1.level < κ ∧
      (rel p ⟨t.1, lt_of_lt_of_le (lt_trans t.2 hw'κ) hκl⟩ w →
        Semiformula.Eval (s := adStruc (rel p) (ad p))
          ![(⟨t.1, lt_of_lt_of_le (lt_trans t.2 hw'κ) hκl⟩ : RSModel p), s] f φ) := by
    intro t
    by_cases h : rel p ⟨t.1, lt_of_lt_of_le (lt_trans t.2 hw'κ) hκl⟩ w
    · obtain ⟨y, hy, hev⟩ := H _ h
      obtain ⟨s0, hs0, hes0⟩ := (Dk_iff p κ y).1 hy
      refine ⟨⟨s0, lt_of_lt_of_le hs0 hκl⟩, hs0, fun _ => ?_⟩
      exact (eval_congr2 p hφ f (x := ⟨t.1, _⟩) (x' := ⟨t.1, _⟩) (y := ⟨s0, _⟩) (y' := y)
        (Eqv.refl _ _) hes0).2 hev
    · exact ⟨lvl p hl0, by simpa using hκ0, fun h' => absurd h' h⟩
  choose s hs1 hs2 using hex
  obtain ⟨γ, hγκ, hγ⟩ := hreg.2 w'.level hw'κ (fun t => (s t).1.level) hs1
  have hγ1 : γ + 1 < κ := add_one_lt_of_limit hlim hγκ
  have hγ1l : γ + 1 < p.lam := lt_of_lt_of_le hγ1 hκl
  refine ⟨lvl p hγ1l, Dk_lvl p hγ1l hγ1, ?_⟩
  intro x hx
  have hxw' : Mem p.R x.1 w' := by
    refine Mem.congr_right p.R (Eqv.symm p.R hww') ?_
    exact hx
  obtain ⟨t, hmt, het⟩ := hxw'
  let t' : RSModel p := ⟨t.1, lt_of_lt_of_le (lt_trans t.2 hw'κ) hκl⟩
  have htw : rel p t' w := Mem.congr_right p.R hww' ⟨t, hmt, Eqv.refl _ _⟩
  refine ⟨s t, ?_, ?_⟩
  · exact (mem_L_iff p.R (s t).1 _).2 ⟨(s t).1, lt_of_le_of_lt (hγ t) (lt_add_one _), Eqv.refl _ _⟩
  · exact (eval_congr2 p hφ f (x := t') (x' := x) (y := s t) (y' := s t) het (Eqv.refl _ _)).1
      (hs2 t htw)

/-! ### The standard facts about `Ad` -/

theorem ad_data {x : RSModel p} (hx : ad p x) :
    ∃ κ : Ordinal.{1}, κ ∈ p.R ∧ 0 < κ ∧ Eqv p.R (T.L κ) x.1 := (AdP_iff p.R x.1).1 hx

theorem kappa_lt_lam {κ : Ordinal.{1}} {x : RSModel p} (he : Eqv p.R (T.L κ) x.1) :
    κ < p.lam := lt_of_le_of_lt (level_le_of_eqv_L p.R κ x.1 he) x.2

/-- an admissible element is transitive. -/
theorem rel_trans_ad {x : RSModel p} (hx : ad p x) :
    ∀ c : RSModel p, rel p c x → ∀ y : RSModel p, rel p y c → rel p y x := by
  obtain ⟨κ, -, -, he⟩ := ad_data p hx
  intro c hc y hy
  exact (rel_iff_Dk p he).2 (Dk_trans p ((rel_iff_Dk p he).1 hc) hy)

/-- the ordinal `ω` lies below every regular uncountable `κ`. -/
theorem omega_lt_of_mem {κ : Ordinal.{1}} (hκ : κ ∈ p.R) : ω < κ := by
  obtain ⟨c, -, h0, e⟩ := p.hR hκ
  rw [e, Cardinal.lt_ord, Ordinal.card_omega0]
  exact h0

theorem holds_ad1 : Holds (rel p) (ad p) ad1Ax := by
  rw [holds_ad1Ax]
  intro x hx
  obtain ⟨κ, hκR, hκ0, he⟩ := ad_data p hx
  have hκl : κ < p.lam := kappa_lt_lam p he
  have hωκ : ω < κ := omega_lt_of_mem p hκR
  have hωl : ω < p.lam := lt_trans hωκ hκl
  refine ⟨fun y hy z hz => rel_trans_ad p hx y hy z hz, lvl p hωl, ?_, ?_, ?_⟩
  · exact (rel_iff_Dk p he).2 (Dk_lvl p hωl hωκ)
  · have h0 : (0 : Ordinal.{1}) < p.lam := lt_trans hκ0 hκl
    exact ⟨lvl p h0, (mem_L_iff p.R _ _).2 ⟨T.L 0, Ordinal.omega0_pos, Eqv.refl _ _⟩,
      fun c hc => hc⟩
  · intro a ha
    obtain ⟨s, hs, hes⟩ := (mem_L_iff p.R a.1 ω).1 ha
    have hs1 : s.level + 1 < ω := add_one_lt_of_limit Ordinal.isSuccLimit_omega0 hs
    have hs1l : s.level + 1 < p.lam := lt_trans hs1 hωl
    refine ⟨lvl p hs1l, (mem_L_iff p.R _ ω).2 ⟨T.L (s.level + 1), hs1, Eqv.refl _ _⟩, ?_⟩
    exact (mem_L_iff p.R a.1 _).2 ⟨s, lt_add_one _, hes⟩

theorem holds_ad2 : Holds (rel p) (ad p) ad2Ax := by
  rw [holds_ad2Ax]
  rintro x y ⟨hx, hy⟩
  obtain ⟨κ, -, -, hex⟩ := ad_data p hx
  obtain ⟨κ', -, -, hey⟩ := ad_data p hy
  rcases lt_trichotomy κ κ' with h | h | h
  · left
    exact Mem.congr_left p.R hex
      (Mem.congr_right p.R hey ((mem_L_iff p.R _ _).2 ⟨T.L κ, h, Eqv.refl _ _⟩))
  · right; left
    subst h
    exact (eqm_iff p x y).2 (Eqv.trans p.R (Eqv.symm p.R hex) hey)
  · right; right
    exact Mem.congr_left p.R hey
      (Mem.congr_right p.R hex ((mem_L_iff p.R _ _).2 ⟨T.L κ', h, Eqv.refl _ _⟩))

theorem holds_lim : Holds (rel p) (ad p) limAx := by
  rw [holds_limAx]
  intro x
  obtain ⟨κ, hκR, hxκ, hκl⟩ := p.hcof x.1.level x.2
  have hκ0 : 0 < κ := lt_of_le_of_lt zero_le hxκ
  refine ⟨lvl p hκl, AdP_L p.R hκR hκ0, ?_⟩
  exact (mem_L_iff p.R x.1 _).2 ⟨x.1, hxκ, Eqv.refl _ _⟩

theorem holds_ext : Holds (rel p) (ad p) extAx := (holds_extAx (rel p) (ad p)).2 (extOK p)

theorem holds_found (φ : Semiformula LAd ℕ 1) : Holds (rel p) (ad p) (foundAx φ) := by
  rw [holds_foundAx]
  intro f hstep x
  exact (wf_rel p).induction (C := fun x =>
    Semiformula.Eval (s := adStruc (rel p) (ad p)) ![x] f φ) x hstep

end RSModel

end OrdinalAnalysis.KPi.Sound
