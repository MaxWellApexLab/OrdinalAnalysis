/-
  `ThetaWNoteD` at every level `k`, as a complete `CollapsingNotation`/`CollapsingLevel` (and,
  as a bonus, `CollapsingTower`): no `sorry`, no hypotheses structure needed.

  History. The first landing
  of this file left the 19 hull-dependent fields (of 42) as hypotheses, `ThetaWNotationFacts`/
  `ThetaWHullFacts`, because the level-free Buchholz hull (Definition 4.2: one `C(α, β)` closed
  under every `ϑ_j` restricted to domain arguments below `α`) did not exist yet in
  `Ordinal/ThetaW/*` — only N1's own per-level `Hop k` (`ThetaW/Hull.lean`), which the plan's §2b
  already flagged as almost certainly the wrong shape.  The level-free operator has since landed,
  settling that adjudication in Lean:
  * `Ordinal/ThetaW/HullSingle.lean`: `CsetS`, `HopS` (the level-free `H_α`), `NiceS`, `Ahull`
    (the level-free support, replacing the per-level `Ehull k`), `theta_isLeastS`,
    `theta_mem_HopS`, `theta_lt_theta_of_mem_HopS`, `HopS_nice`.
  * `Ordinal/ThetaW/HullDom.lean`: the domain lemma `dom_add_omegaPow` for `HopS` (no bound
    `α, β ≺ Ω_{k+1}`, unlike the old per-level `Hop k` — see the file's own docstring for the
    refutation of the per-level design: `not_dom_add_omegaPow_Hop`, `hA_refutes_Hop`,
    `not_Hop_zero_subset_Hop_one`), and `HullHypGe k` (`HullHypS j` for every `j ≥ k`, Buchholz's
    `𝒜(Θ; γ, κ, μ)` quantifying over every `τ ⪰ κ`), with `HullHypGe.up/mono/lt_theta/
    union_singleton` and `dom_add_omegaPow_ge`.
  Every field of `thetaWCN`/`thetaWLevel`/`thetaWTower` below is filled from these, checked to
  compile (`remote_build.sh`, sky4) before landing, matching the adjudicated
  scratch `Iface_filled.lean`.  `DomK`/`thetaD` (total, junk `0` outside the domain — distinct
  from `ThetaW/Hull.lean`'s own dependent `thetaD k a hdom`, which lives in a different,
  untouched namespace and is never opened here) are still defined fresh, exactly as before.
-/
import OrdinalAnalysis.Ordinal.Collapsing.Interface
import OrdinalAnalysis.Ordinal.ThetaW.Instance
import OrdinalAnalysis.Ordinal.ThetaW.WellFoundedD
import OrdinalAnalysis.Ordinal.ThetaW.HullDom

set_option autoImplicit false

namespace OrdinalAnalysis
namespace Notn

namespace ThetaWNoteD

/-- The domain of `ϑ_k` on notations (Wilken Lemma 2.13 / Weiermann–Wilken 2011 Lemma 4.3). -/
def DomK (k : ℕ) (a : ThetaWNoteD) : Prop := ∀ x ∈ ThetaWTerm.G k a.1, x < a.1

instance (k : ℕ) : DecidablePred (DomK k) := fun a => by unfold DomK; infer_instance

/-- `ϑ_k` on notations, junk `0` outside the domain. -/
def thetaD (k : ℕ) (a : ThetaWNoteD) : ThetaWNoteD :=
  ⟨if DomK k a then ThetaWTerm.theta k a.1 else ThetaWTerm.zero, by
    split
    · next h => exact ⟨(ThetaWTerm.nf_theta_iff k a.1).mpr a.2.1,
        (ThetaWTerm.dom_theta_iff k a.1).mpr ⟨a.2.2, h⟩⟩
    · exact ⟨ThetaWTerm.nf_zero, ThetaWTerm.dom_zero⟩⟩

theorem thetaD_of_dom {k : ℕ} {a : ThetaWNoteD} (h : DomK k a) :
    (thetaD k a).1 = ThetaWTerm.theta k a.1 := if_pos h

theorem thetaD_of_not_dom {k : ℕ} {a : ThetaWNoteD} (h : ¬ DomK k a) :
    (thetaD k a).1 = ThetaWTerm.zero := if_neg h

theorem thetaD_lt_Omega (k : ℕ) (a : ThetaWNoteD) : thetaD k a < ThetaWNoteD.Omega k := by
  by_cases h : DomK k a
  · show (thetaD k a).1 < ThetaWTerm.Omega k
    rw [thetaD_of_dom h]; exact ThetaWTerm.theta_lt_Omega_self k a.1
  · show (thetaD k a).1 < ThetaWTerm.Omega k
    rw [thetaD_of_not_dom h]
    exact ThetaWTerm.nil_lt_Omega k

end ThetaWNoteD

/-! ## `ThetaWNoteD` as a `CollapsingNotation`

The 17 arithmetic/principal fields are the same `ThetaW/Arith` lemmas as before; `supp := Ahull`
and `Hop := HopS` are the level-free Buchholz hull of `HullSingle.lean`. -/

instance thetaWCN : CollapsingNotation ThetaWNoteD where
  zero := ThetaWNoteD.zero
  zero_le := fun _ => bot_le
  add := (· + ·)
  add_zero := ThetaWNoteD.add_zero
  add_assoc := ThetaWNoteD.add_assoc
  add_lt_add_left := ThetaWNoteD.add_lt_add_left
  le_add_left := ThetaWNoteD.le_add_left
  add_lt_omegaPow := ThetaWNoteD.add_lt_omegaPow
  zero_lt_one := ThetaWNoteD.zero_lt_one
  omegaMul := ThetaWNoteD.omegaMul
  omegaMul_lt_omegaMul := ThetaWNoteD.omegaMul_lt_omegaMul
  IsPrin := fun p => ThetaWTerm.IsPrin p.1
  omegaMul_prin := ThetaWNoteD.omegaMul_prin
  omegaMul_lt_prin := ThetaWNoteD.omegaMul_lt_prin
  nadd_lt_prin := ThetaWNoteD.nadd_lt_prin
  one_lt_prin := ThetaWNoteD.one_lt_prin
  ofNat_lt_prin := fun hp n => ThetaWNoteD.ofNat_lt_prin hp n
  supp := OrdinalAnalysis.ThetaWNoteD.Ahull
  supp_add := OrdinalAnalysis.ThetaWNoteD.Ahull_add_subset
  supp_nadd := OrdinalAnalysis.ThetaWNoteD.Ahull_nadd_subset
  supp_omegaPow := OrdinalAnalysis.ThetaWNoteD.Ahull_omegaPow
  supp_omegaMul := OrdinalAnalysis.ThetaWNoteD.Ahull_omegaMul_subset
  supp_zero := OrdinalAnalysis.ThetaWNoteD.Ahull_zero
  supp_one := OrdinalAnalysis.ThetaWNoteD.Ahull_one
  supp_ofNat := OrdinalAnalysis.ThetaWNoteD.Ahull_ofNat
  Hop := OrdinalAnalysis.ThetaWNoteD.HopS
  Hop_nice := fun a => OrdinalAnalysis.ThetaWNoteD.HopS_nice a
  Hop_subset_Hop := fun h X => OrdinalAnalysis.ThetaWNoteD.HopS_subset_HopS h X

/-! ## `ThetaWNoteD` at level `k` as a `CollapsingLevel`

`HullHyp := HullHypGe k` (the hypothesis at every level `≥ k`, not just `HullHypS k`): that is
what keeps `hullHyp_union_singleton` provable (raising the level to compare `Omega k ≤ Omega j`)
and what `CollapsingTower.hullHyp_up` below needs. -/

noncomputable def thetaWLevel (k : ℕ) : CollapsingLevel ThetaWNoteD where
  Omega := ThetaWNoteD.Omega k
  isPrin_Omega := trivial
  supp_Omega := OrdinalAnalysis.ThetaWNoteD.Ahull_Omega k
  D := ThetaWNoteD.DomK k
  theta := ThetaWNoteD.thetaD k
  isPrin_theta := fun {a} h => by
    show ThetaWTerm.IsPrin (ThetaWNoteD.thetaD k a).1
    rw [ThetaWNoteD.thetaD_of_dom h]; trivial
  theta_lt_Omega := ThetaWNoteD.thetaD_lt_Omega k
  HullHyp := OrdinalAnalysis.ThetaWNoteD.HullHypGe k
  hullHyp_mono := fun h hab => h.mono hab
  hullHyp_lt_theta := fun {a c d X} h hac hc hd hΩ => by
    have hc' : ThetaWTerm.Dom (ThetaWTerm.theta k c.1) :=
      (ThetaWTerm.dom_theta_iff k c.1).mpr ⟨c.2.2, hc⟩
    show d.1 < (ThetaWNoteD.thetaD k c).1
    rw [ThetaWNoteD.thetaD_of_dom hc]
    exact h.lt_theta hac hc' hd hΩ
  hullHyp_union_singleton := fun h hd hΩ hgd => h.union_singleton hd hΩ hgd
  theta_mem_Hop := fun {a b X} ha hab hD => by
    have hd' : ThetaWTerm.Dom (ThetaWTerm.theta k a.1) :=
      (ThetaWTerm.dom_theta_iff k a.1).mpr ⟨a.2.2, hD⟩
    have e : ThetaWNoteD.thetaD k a = OrdinalAnalysis.ThetaWNoteD.thetaD k a hd' :=
      Subtype.ext (ThetaWNoteD.thetaD_of_dom hD)
    rw [e]; exact OrdinalAnalysis.ThetaWNoteD.theta_mem_HopS k ha hab hd'
  theta_lt_theta_of_mem_Hop := fun {a b c X} hX hab hbc hb hDb hDc => by
    have hb' : ThetaWTerm.Dom (ThetaWTerm.theta k b.1) :=
      (ThetaWTerm.dom_theta_iff k b.1).mpr ⟨b.2.2, hDb⟩
    have hc' : ThetaWTerm.Dom (ThetaWTerm.theta k c.1) :=
      (ThetaWTerm.dom_theta_iff k c.1).mpr ⟨c.2.2, hDc⟩
    show (ThetaWNoteD.thetaD k b).1 < (ThetaWNoteD.thetaD k c).1
    rw [ThetaWNoteD.thetaD_of_dom hDb, ThetaWNoteD.thetaD_of_dom hDc]
    exact OrdinalAnalysis.ThetaWNoteD.theta_lt_theta_of_mem_HopS hX.hullHypS hab hbc hb hb' hc'
  dom_add_omegaPow := fun {a b X} hX ha hb =>
    ((ThetaWTerm.dom_theta_iff k _).mp (OrdinalAnalysis.ThetaWNoteD.dom_add_omegaPow_ge hX ha hb)).2

/-- The generic lemma of `Interface.lean` is available at every level with no further work — the
audit's claim, now unconditional (no `ThetaWNotationFacts`/`ThetaWHullFacts` argument). -/
example (k : ℕ) {a b : ThetaWNoteD} {X : Set ThetaWNoteD} (hX : (thetaWLevel k).HullHyp a X)
    (ha : a ∈ CollapsingNotation.Hop a X) (hb : b ∈ CollapsingNotation.Hop a X) :
    ThetaWNoteD.thetaD k (a + ThetaWNoteD.omegaPow b) ∈
      CollapsingNotation.Hop (a + ThetaWNoteD.omegaPow b) X :=
  (thetaWLevel k).theta_add_omegaPow_mem_Hop hX ha hb

/-- Level-`k` stages are the in-flight `IDn.StageAt k` (checked by type only; `IDn.Language` is
not imported here). -/
example (k : ℕ) : (thetaWLevel k).Stage = {a : ThetaWNoteD // a ≤ ThetaWNoteD.Omega k} := rfl

/-! ## Bonus: `ThetaWNoteD` as a `CollapsingTower` (Layer 3, C4)

Not asked for by this landing's brief (only `CollapsingLevel` was), but every field is now
provable from the same two files, so it costs nothing to include: `Omega_strictMono` and
`add_Omega_Omega` were already provable before this update; `Omega_lt_theta_succ` and
`hullHyp_up` needed exactly the level-free hull this update brought in
(`HullHypGe.up` for the latter). -/

noncomputable def thetaWTower : CollapsingTower ThetaWNoteD where
  lev := thetaWLevel
  Omega_strictMono := fun i j h => (ThetaWTerm.Omega_lt_Omega_iff i j).mpr h
  Omega_lt_theta_succ := fun k a h => by
    show ThetaWTerm.Omega k < (ThetaWNoteD.thetaD (k + 1) a).1
    rw [ThetaWNoteD.thetaD_of_dom h]; exact ThetaWTerm.Omega_lt_theta_succ k a.1
  hullHyp_up := fun h hkj => OrdinalAnalysis.ThetaWNoteD.HullHypGe.up h hkj
  add_Omega_Omega := fun k =>
    ThetaWNoteD.add_Omega_of_lt ((ThetaWTerm.Omega_lt_Omega_iff k (k + 1)).mpr (Nat.lt_succ_self k))

#print axioms thetaWCN
#print axioms thetaWLevel
#print axioms thetaWTower

end Notn
end OrdinalAnalysis
