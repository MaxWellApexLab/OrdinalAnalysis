module

public import OrdinalAnalysis.KPi.SoundAux2
public import OrdinalAnalysis.KPi.SoundAux3
public import OrdinalAnalysis.KPi.SoundAux4
public import OrdinalAnalysis.KPi.Ord.Defs

/-!
# KPi is consistent: the RS term model is a model of `KPi` (K1-R, soundness)

For every admissible parameter set `p : Params` (`R ⊆ RegOrd`, `lam` regular, `R` cofinal below
`lam`), the term model `RSModel p` (the RS-terms of level `< lam`, with `∈` and `Ad` given by the
truth predicate of `RS`) satisfies every axiom of `KPi` (B92 §2):

* (Ext) `RSModel.extOK`, (Found) from well-foundedness of `∈` (`wf_rel`), (Ad.1), (Ad.2), (Lim) from
  the structure of `R`; (Pair), (Union), (Δ₀-Sep), (Δ₀-Col) by explicit comprehension terms
  (`core_pair`, `core_union`, `core_sep`, `core_col`), in *guard form* for the guard
  `D_κ = {a | a ∈ L_κ}`;
* (Ad.3) by the relativisation lemma (`holds_ad3_iff`): `ψ^x` holds in the model iff `ψ` holds in
  the substructure `{a | a ∈ x}`, where the same cores apply with `κ ∈ R`.

`models_KPi p : (RSModel p)↓[LAd] ⊧* KPi`, and with the standard parameters (`R = Rset`, `lam = I`)
`KPi_consistent : Entailment.Consistent KPi` with no hypothesis.
-/

@[expose] public section

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.Sound

open LO LO.FirstOrder OrdinalAnalysis.KPi.RS Ordinal

/-- The `ℒ_Ad`-structure on the RS term model. -/
instance instStructureRSModel (p : Params) : Structure LAd (RSModel p) :=
  adStruc (RSModel.rel p) (RSModel.ad p)

namespace RSModel

variable (p : Params)

/-! ### The model satisfies the axioms outright (`κ = lam`) -/

theorem holds_pair : Holds (rel p) (ad p) pairAx := by
  refine (holds_pairAx (rel p) (ad p)).2 ?_
  intro x y
  obtain ⟨c, -, h1, h2⟩ := core_pair p (termReg_lam p).1 le_rfl (Dk_lam p x) (Dk_lam p y)
  exact ⟨c, h1, h2⟩

theorem holds_union : Holds (rel p) (ad p) unionAx := by
  refine (holds_unionAx (rel p) (ad p)).2 ?_
  intro x
  obtain ⟨c, -, h⟩ := core_union p le_rfl (Dk_lam p x)
  exact ⟨c, h⟩

theorem holds_sep {φ : Semiformula LAd ℕ 1} (hφ : IsDelta0 φ) :
    Holds (rel p) (ad p) (sepAx φ) := by
  refine (holds_sepAx (rel p) (ad p) φ).2 ?_
  intro f w
  obtain ⟨y, -, h⟩ := core_sep p p.lam (termReg_lam p).1 le_rfl φ hφ f w
    (fun j => ⟨(f j).1, (f j).2, Eqv.refl _ _⟩) ⟨w.1, w.2, Eqv.refl _ _⟩
  exact ⟨y, h⟩

theorem holds_col {φ : Semiformula LAd ℕ 2} (hφ : IsDelta0 φ) :
    Holds (rel p) (ad p) (colAx φ) := by
  refine (holds_colAx (rel p) (ad p) φ).2 ?_
  intro f w H
  obtain ⟨v, -, h⟩ := core_col p (termReg_lam p) le_rfl hφ f (Dk_lam p w)
    (fun x hx => by
      obtain ⟨y, hy⟩ := H x hx
      exact ⟨y, Dk_lam p y, hy⟩)
  exact ⟨v, h⟩

/-! ### (Ad.3): the substructure below an admissible element -/

section Ad3

variable {p}

/-- the elements below `x`. -/
abbrev Below (x : RSModel p) : Type 2 := {a : RSModel p // rel p a x}

theorem below_nonempty {x : RSModel p} (hx : ad p x) : Nonempty (Below x) := by
  obtain ⟨κ, -, hκ0, he⟩ := ad_data p hx
  have h0 : (0 : Ordinal.{1}) < p.lam := lt_trans hκ0 (kappa_lt_lam p he)
  exact ⟨⟨lvl p h0, (rel_iff_Dk p he).2 (Dk_lvl p h0 hκ0)⟩⟩

theorem env1_below {x : RSModel p} (a : Below x) :
    (fun i => ((![a] : Fin 1 → Below x) i).1) = ![a.1] := by
  funext i; fin_cases i; rfl

theorem env2_below {x : RSModel p} (a b : Below x) :
    (fun i => ((![a, b] : Fin 2 → Below x) i).1) = ![a.1, b.1] := by
  funext i; fin_cases i <;> rfl

end Ad3

theorem holds_ad3_pair : Holds (rel p) (ad p) (ad3Ax pairAx) := by
  refine (holds_ad3_iff (rel p) (ad p) (fun x hx => rel_trans_ad p hx) pairAx).2 ?_
  intro x hx
  obtain ⟨κ, hκR, hκ0, he⟩ := ad_data p hx
  have hreg := termReg_of_mem p hκR
  have hκl := (kappa_lt_lam p he).le
  refine (holds_pairAx _ _).2 ?_
  intro a b
  obtain ⟨c, hc, h1, h2⟩ :=
    core_pair p hreg.1 hκl ((rel_iff_Dk p he).1 a.2) ((rel_iff_Dk p he).1 b.2)
  exact ⟨⟨c, (rel_iff_Dk p he).2 hc⟩, h1, h2⟩

theorem holds_ad3_union : Holds (rel p) (ad p) (ad3Ax unionAx) := by
  refine (holds_ad3_iff (rel p) (ad p) (fun x hx => rel_trans_ad p hx) unionAx).2 ?_
  intro x hx
  obtain ⟨κ, hκR, hκ0, he⟩ := ad_data p hx
  have hκl := (kappa_lt_lam p he).le
  refine (holds_unionAx _ _).2 ?_
  intro a
  obtain ⟨c, hc, h⟩ := core_union p hκl ((rel_iff_Dk p he).1 a.2)
  exact ⟨⟨c, (rel_iff_Dk p he).2 hc⟩, fun y hy u hu => h y.1 hy u.1 hu⟩

theorem holds_ad3_sep {φ : Semiformula LAd ℕ 1} (hφ : IsDelta0 φ) :
    Holds (rel p) (ad p) (ad3Ax (sepAx φ)) := by
  refine (holds_ad3_iff (rel p) (ad p) (fun x hx => rel_trans_ad p hx) (sepAx φ)).2 ?_
  intro x hx
  obtain ⟨κ, hκR, hκ0, he⟩ := ad_data p hx
  have hreg := termReg_of_mem p hκR
  have hκl := (kappa_lt_lam p he).le
  have : Nonempty (Below x) := below_nonempty hx
  have hD : ∀ c, rel p c x → ∀ y, rel p y c → rel p y x := rel_trans_ad p hx
  refine (holds_sepAx _ _ φ).2 ?_
  intro f w
  obtain ⟨y, hylev, hy1, hy2⟩ := core_sep p κ hreg.1 hκl φ hφ (fun j => (f j).1) w.1
    (fun j => ((Dk_iff p κ (f j).1).1 ((rel_iff_Dk p he).1 (f j).2)))
    ((Dk_iff p κ w.1).1 ((rel_iff_Dk p he).1 w.2))
  have hyN : rel p y x :=
    (rel_iff_Dk p he).2 (Dk_of_rep p (s := y.1) hylev (Eqv.refl _ _))
  refine ⟨⟨y, hyN⟩, ?_, ?_⟩
  · intro x' hx'
    have h := hy1 x'.1 hx'
    refine ⟨h.1, ?_⟩
    rw [eval_sub_delta0 (rel p) (ad p) hD hφ ![x'] f, env1_below]
    exact h.2
  · intro x' hx' hev
    rw [eval_sub_delta0 (rel p) (ad p) hD hφ ![x'] f, env1_below] at hev
    exact hy2 x'.1 hx' hev

theorem holds_ad3_col {φ : Semiformula LAd ℕ 2} (hφ : IsDelta0 φ) :
    Holds (rel p) (ad p) (ad3Ax (colAx φ)) := by
  refine (holds_ad3_iff (rel p) (ad p) (fun x hx => rel_trans_ad p hx) (colAx φ)).2 ?_
  intro x hx
  obtain ⟨κ, hκR, hκ0, he⟩ := ad_data p hx
  have hreg := termReg_of_mem p hκR
  have hκl := (kappa_lt_lam p he).le
  have : Nonempty (Below x) := below_nonempty hx
  have hD : ∀ c, rel p c x → ∀ y, rel p y c → rel p y x := rel_trans_ad p hx
  refine (holds_colAx _ _ φ).2 ?_
  intro f w H
  obtain ⟨v, hv, h⟩ := core_col p hreg hκl hφ (fun j => (f j).1) ((rel_iff_Dk p he).1 w.2)
    (fun x' hx' => by
      have hxN : rel p x' x := hD w.1 w.2 x' hx'
      obtain ⟨y, hy⟩ := H ⟨x', hxN⟩ hx'
      refine ⟨y.1, (rel_iff_Dk p he).1 y.2, ?_⟩
      rw [eval_sub_delta0 (rel p) (ad p) hD hφ ![⟨x', hxN⟩, y] f, env2_below] at hy
      exact hy)
  have hvN : rel p v x := (rel_iff_Dk p he).2 hv
  refine ⟨⟨v, hvN⟩, ?_⟩
  intro x' hx'
  obtain ⟨y, hy1, hy2⟩ := h x'.1 hx'
  have hyN : rel p y x := hD v hvN y hy1
  refine ⟨⟨y, hyN⟩, hy1, ?_⟩
  rw [eval_sub_delta0 (rel p) (ad p) hD hφ ![x', ⟨y, hyN⟩] f, env2_below]
  exact hy2

end RSModel

/-! ### Soundness -/

/-- **Soundness of `KPi` for the RS term model**: for every admissible parameter set `p`,
`RSModel p` (terms of level `< lam`, `∈` and `Ad` from RS truth) is a model of `KPi`. -/
theorem models_KPi (p : Params) : (RSModel p)↓[LAd] ⊧* KPi := by
  refine models_theory_iff.mpr ?_
  intro σ hσ
  have hσ' : KPi σ := hσ
  cases hσ' with
  | ext => exact RSModel.holds_ext p
  | found φ => exact RSModel.holds_found p φ
  | pair => exact RSModel.holds_pair p
  | union => exact RSModel.holds_union p
  | sep φ h => exact RSModel.holds_sep p h
  | col φ h => exact RSModel.holds_col p h
  | ad1 => exact RSModel.holds_ad1 p
  | ad2 => exact RSModel.holds_ad2 p
  | ad3 h =>
    cases h with
    | pair => exact RSModel.holds_ad3_pair p
    | union => exact RSModel.holds_ad3_union p
    | sep φ h => exact RSModel.holds_ad3_sep p h
    | col φ h => exact RSModel.holds_ad3_col p h
  | lim => exact RSModel.holds_lim p

/-- `KPi` is consistent as soon as one admissible parameter set exists. -/
theorem KPi_consistent_of (p : Params) : Entailment.Consistent KPi := by
  have : Nonempty (RSModel p) := inferInstance
  have : (RSModel p)↓[LAd] ⊧* KPi := models_KPi p
  exact consistent_of_model KPi (RSModel p)

/-! ### The standard parameters (`R = {I} ∪ {Ω_{σ+1} | σ < I}`, `lam = I`) -/

/-- `R = Rset` and `lam = I = Iord` (B92 Def 4.1) are admissible parameters. -/
noncomputable def stdParams : Params where
  R := Ord.Rset
  lam := Ord.Iord
  hR := fun κ h =>
    let hh := Ord.Rset_isRU h
    ⟨κ.card, hh.reg, hh.unc, hh.ord.symm⟩
  hlam :=
    let hh := Ord.isRU_Iord
    ⟨Ord.Iord.card, hh.reg, hh.unc, hh.ord.symm⟩
  hcof := by
    intro α hα
    have hlim : Order.IsSuccLimit Ord.Iord := by
      have h := Cardinal.isSuccLimit_ord Ord.isRU_Iord.unc.le
      rwa [Ord.isRU_Iord.ord] at h
    have hα1 : α + 1 < Ord.Iord := add_one_lt_of_limit hlim hα
    refine ⟨ω_ (α + 1), Ord.omega_succ_mem_Rset hα, ?_, ?_⟩
    · exact lt_of_le_of_lt (Ordinal.omega_strictMono.id_le α)
        (Ordinal.omega_strictMono (lt_add_one α))
    · have h := Ordinal.omega_strictMono hα1
      rwa [Ord.Iord_spec.2] at h

/-- **`KPi` is consistent** (B92 §2: the theory has a model, namely the RS term model for
`R = Rset`, `lam = I`). -/
theorem KPi_consistent : Entailment.Consistent KPi := KPi_consistent_of stdParams

end OrdinalAnalysis.KPi.Sound
