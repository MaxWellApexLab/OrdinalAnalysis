/-
  `ThetaNote` as a `CollapsingNotation`/`CollapsingLevel`: complete, no `sorry`.

  Source: `idn_abstraction_plan.md` §2 ("What compiled"): every field of `thetaCN` and
  `thetaLevel` is an existing lemma of `Ordinal/Theta/*` (or `trivial`), `D := fun _ => True`,
  and `InductiveDef.Stage` (`ID1/Language.lean`) equals `thetaLevel.Stage` by `rfl`.  The
  examples below recover three ID₁ statements from `ID1/Collapsing.lean` — the types of
  `ThetaNote.theta_add_omegaPow_mem_Hop`, `ThetaNote.Hop_subset_Hop` and
  `ThetaNote.HullHyp.lt_theta` — from the generic fields of `Collapsing/Interface.lean` by
  unfolding the instance.
-/
import OrdinalAnalysis.Ordinal.Collapsing.Interface
import OrdinalAnalysis.ID1.Language
import OrdinalAnalysis.Ordinal.Theta.HullCofinal

set_option autoImplicit false

namespace OrdinalAnalysis
namespace Notn

/-! ## `ThetaNote` as a `CollapsingNotation` -/

instance thetaCN : CollapsingNotation ThetaNote where
  zero := ThetaNote.zero
  zero_le := fun _ => bot_le
  add := (· + ·)
  add_zero := ThetaNote.add_zero
  add_assoc := ThetaNote.add_assoc
  add_lt_add_left := ThetaNote.add_lt_add_left
  le_add_left := ThetaNote.le_add_left
  add_lt_omegaPow := ThetaNote.add_lt_omegaPow
  zero_lt_one := ThetaNote.zero_lt_one
  omegaMul := ThetaNote.omegaMul
  omegaMul_lt_omegaMul := ThetaNote.omegaMul_lt_omegaMul
  IsPrin := fun p => ThetaTerm.IsPrin p.1
  omegaMul_prin := ThetaNote.omegaMul_prin
  omegaMul_lt_prin := ThetaNote.omegaMul_lt_prin
  nadd_lt_prin := ThetaNote.nadd_lt_prin
  one_lt_prin := ThetaNote.one_lt_prin
  ofNat_lt_prin := fun hp n => ThetaNote.ofNat_lt_prin hp n
  supp := ThetaNote.Ehull
  supp_add := ThetaNote.Ehull_add_subset_hull
  supp_nadd := ThetaNote.Ehull_nadd_subset_hull
  supp_omegaPow := ThetaNote.Ehull_omegaPow_hull
  supp_omegaMul := ThetaNote.Ehull_omegaMul_subset_hull
  supp_zero := ThetaNote.Ehull_zero_hull
  supp_one := ThetaNote.Ehull_one_hull
  supp_ofNat := ThetaNote.Ehull_ofNat_hull
  Hop := ThetaNote.Hop
  Hop_nice := ThetaNote.Hop_nice
  Hop_subset_Hop := fun h X => ThetaNote.Hop_subset_Hop h X

/-- The single level of `ThetaNote`: `D := True` everywhere, so all four Dom-guarded fields
discharge trivially. -/
def thetaLevel : CollapsingLevel ThetaNote where
  Omega := ThetaNote.Omega
  isPrin_Omega := trivial
  supp_Omega := ThetaNote.Ehull_Omega_hull
  D := fun _ => True
  theta := ThetaNote.theta
  isPrin_theta := fun _ => trivial
  theta_lt_Omega := ThetaNote.theta_lt_Omega
  HullHyp := ThetaNote.HullHyp
  hullHyp_mono := fun h hab => h.mono hab
  hullHyp_lt_theta := fun h hac _ hd hΩ => h.lt_theta hac hd hΩ
  hullHyp_union_singleton := fun h hd hΩ hg => h.union_singleton hd hΩ hg
  theta_mem_Hop := fun ha hab _ => ThetaNote.theta_mem_Hop ha hab
  theta_lt_theta_of_mem_Hop := fun hX hab hbc hb _ _ =>
    ThetaNote.theta_lt_theta_of_mem_Hop hX hab hbc hb
  dom_add_omegaPow := fun _ _ _ => trivial

/-! ### ID₁ statements are recovered by unfolding (the "byte-identical" check)

Three statements from `ID1/Collapsing.lean`, chosen per the audit: the types of
`theta_add_omegaPow_mem_Hop`, `Hop_subset_Hop` and `HullHyp.lt_theta`.  Each `example` below has
exactly the ID₁ statement's type and is closed by a generic field/lemma of `Interface.lean`
through the `thetaCN`/`thetaLevel` instances — i.e. the ID₁ statement unfolds to the generic
one. -/

example : InductiveDef.Stage = thetaLevel.Stage := rfl

example : ∀ H : Set ThetaNote → Set ThetaNote, ThetaNote.IsOperator H ↔ IsOperator H :=
  fun _ => Iff.rfl

example : ∀ H : Set ThetaNote → Set ThetaNote, ThetaNote.Nice H ↔ Nice ThetaNote.Ehull H :=
  fun _ => Iff.rfl

/-- `ThetaNote.Hop_subset_Hop`, recovered from the generic field `CollapsingNotation.Hop_subset_Hop`
by unfolding the `thetaCN` instance. -/
example {a b : ThetaNote} (h : a < b) (X : Set ThetaNote) :
    ThetaNote.Hop a X ⊆ ThetaNote.Hop b X :=
  CollapsingNotation.Hop_subset_Hop h X

/-- `ThetaNote.HullHyp.lt_theta`, recovered from the generic field
`CollapsingLevel.hullHyp_lt_theta` at `thetaLevel`, the trivial `D c` discharged by `trivial`. -/
example {a c d : ThetaNote} {X : Set ThetaNote} (h : ThetaNote.HullHyp a X) (hac : a < c)
    (hd : d ∈ ThetaNote.Hop a X) (hΩ : d < ThetaNote.Omega) : d < ThetaNote.theta c :=
  thetaLevel.hullHyp_lt_theta h hac trivial hd hΩ

/-- ID₁'s `theta_add_omegaPow_mem_Hop`, verbatim, closed by the generic lemma. -/
theorem id1_check {a b : ThetaNote} {X : Set ThetaNote} (hX : ThetaNote.HullHyp a X)
    (ha : a ∈ ThetaNote.Hop a X) (hb : b ∈ ThetaNote.Hop a X) :
    ThetaNote.theta (a + ThetaNote.omegaPow b) ∈ ThetaNote.Hop (a + ThetaNote.omegaPow b) X :=
  thetaLevel.theta_add_omegaPow_mem_Hop hX ha hb

example (a : ThetaNote) {b b' : ThetaNote} (h : b' < b) :
    a + ThetaNote.omegaPow b' + ThetaNote.omegaPow b' < a + ThetaNote.omegaPow b :=
  CollapsingLevel.add_omegaPow_add_omegaPow_lt a h

/-- Dot notation through an abbreviation (the A-refactor of `Hull.lean`'s operator algebra):
if `ThetaNote.IsOperator` were `abbrev … := Notn.IsOperator`, `hH.mono` must still resolve. -/
abbrev IsOperatorT (H : Set ThetaNote → Set ThetaNote) : Prop := IsOperator H

example {H : Set ThetaNote → Set ThetaNote} (hH : IsOperatorT H) {X Y : Set ThetaNote}
    (h : X ⊆ Y) : H X ⊆ H Y := hH.mono h

#print axioms id1_check
#print axioms thetaLevel

end Notn
end OrdinalAnalysis
