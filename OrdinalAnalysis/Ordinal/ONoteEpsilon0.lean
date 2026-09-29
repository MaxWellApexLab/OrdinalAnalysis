/-
  Normal-form ordinal notations denote exactly the ordinals below `ε₀`.

  Mathlib's `ONote`/`NONote` (Cantor normal form notations, `ω ^ e * n + a`) come with
  arithmetic, but not with the identification of their range.  This file proves it:

  * `nf_repr_lt_epsilon0`: every normal-form notation denotes an ordinal below `ε₀`
    (structural induction; a normal form `ω ^ e * n + a` lies below `ω ^ (e + 1)`,
    and `ε₀` is closed under `e ↦ ω ^ (e + 1)`).
  * `exists_nf_repr_eq`: every ordinal below `ε₀` is denoted by a normal-form notation
    (well-founded induction, Cantor normal form via `log ω`, division and remainder).
  * `nonoteIsoIio`: the resulting order isomorphism `NONote ≃o Set.Iio ε₀`.
  * `type_lt_NONote`: the order type of `NONote` is `ε₀`.
-/
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.SetTheory.Ordinal.Veblen

set_option autoImplicit false

namespace OrdinalAnalysis.ONoteEps

open Ordinal ONote

/-- `ε₀` is closed under `x ↦ ω ^ (succ x)`. -/
theorem omega0_opow_succ_lt_epsilon0 {r : Ordinal.{0}} (h : r < ε₀) :
    ω ^ Order.succ r < ε₀ := by
  obtain ⟨k, hk⟩ := lt_epsilon_zero.1 h
  have h1 : Order.succ r ≤ (fun a : Ordinal.{0} ↦ ω ^ a)^[k] 0 := Order.succ_le_of_lt hk
  have h2 : ω ^ Order.succ r ≤ (fun a : Ordinal.{0} ↦ ω ^ a)^[k + 1] 0 := by
    rw [Function.iterate_succ_apply']
    exact Ordinal.opow_le_opow_right omega0_pos h1
  exact lt_of_le_of_lt h2 (iterate_omega0_opow_lt_epsilon_zero (k + 1))

/-- Every normal-form notation denotes an ordinal below `ε₀`. -/
theorem nf_repr_lt_epsilon0 (x : ONote) (h : x.NF) : x.repr < ε₀ := by
  induction x with
  | zero => simp
  | oadd e n a ihe iha =>
      have he : e.NF := h.fst
      have hb : NFBelow (ONote.oadd e n a) (Order.succ e.repr) :=
        NFBelow.oadd he h.snd' (Order.lt_succ _)
      exact lt_trans hb.repr_lt (omega0_opow_succ_lt_epsilon0 (ihe he))

/-- Every ordinal below `ε₀` is the value of a normal-form notation. -/
theorem exists_nf_repr_eq (o : Ordinal.{0}) (ho : o < ε₀) :
    ∃ x : ONote, x.NF ∧ x.repr = o := by
  induction o using WellFoundedLT.induction with
  | _ o ih =>
    by_cases h0 : o = 0
    · exact ⟨0, ONote.NF.zero, by simp [h0]⟩
    set e : Ordinal.{0} := Ordinal.log ω o with he
    have hle : ω ^ e ≤ o := Ordinal.opow_log_le_self ω h0
    have hlt : o < ω ^ Order.succ e := Ordinal.lt_opow_succ_log_self one_lt_omega0 o
    have hpos : 0 < ω ^ e := Ordinal.opow_pos _ omega0_pos
    have hne : ω ^ e ≠ 0 := hpos.ne'
    -- the exponent is below `ε₀`
    have he_eps : e < ε₀ := by
      have : ω ^ e < ω ^ ε₀ := by
        rw [omega0_opow_epsilon]; exact lt_of_le_of_lt hle ho
      exact (Ordinal.opow_lt_opow_iff_right one_lt_omega0).1 this
    -- and below `o`
    have he_o : e < o := by
      refine lt_of_le_of_ne ((Ordinal.right_le_opow e one_lt_omega0).trans hle) ?_
      intro hEq
      rw [hEq] at hle
      exact absurd (epsilon_zero_le_of_omega0_opow_le hle) (not_le.2 ho)
    -- Cantor decomposition `o = ω ^ e * n + a`
    set n : Ordinal.{0} := o / ω ^ e with hn
    set a : Ordinal.{0} := o % ω ^ e with ha
    have hdec : ω ^ e * n + a = o := Ordinal.div_add_mod o (ω ^ e)
    have hnpos : 0 < n := (Ordinal.div_pos hne).2 hle
    have hnomega : n < ω := by
      rw [hn, ← Ordinal.lt_mul_iff_div_lt hne, ← Ordinal.opow_succ]; exact hlt
    have ha_lt : a < ω ^ e := Ordinal.mod_lt o hne
    have ha_o : a < o := lt_of_lt_of_le ha_lt hle
    obtain ⟨k, hk⟩ := Ordinal.lt_omega0.1 hnomega
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp [hk] at hnpos
    obtain ⟨xe, hxe, hre⟩ := ih e he_o he_eps
    obtain ⟨xa, hxa, hra⟩ := ih a ha_o (lt_trans ha_o ho)
    have hbel : NFBelow xa xe.repr := by
      refine NF.below_of_lt' ?_ hxa
      rw [hra, hre]; exact ha_lt
    refine ⟨ONote.oadd xe ⟨k, Nat.pos_of_ne_zero hk0⟩ xa, NF.oadd hxe _ hbel, ?_⟩
    simp only [ONote.repr, hre, hra, PNat.mk_coe]
    rw [← hk, hdec]

/-- `NONote`, ordered by the ordinals it denotes, is order-isomorphic to `[0, ε₀)`. -/
noncomputable def nonoteIsoIio : NONote ≃o Set.Iio (ε₀ : Ordinal.{0}) :=
  StrictMono.orderIsoOfSurjective
    (fun a : NONote => (⟨a.repr, nf_repr_lt_epsilon0 a.1 a.2⟩ : Set.Iio (ε₀ : Ordinal.{0})))
    (fun _ _ hab => hab)
    (fun ⟨o, ho⟩ => by
      obtain ⟨x, hx, hxo⟩ := exists_nf_repr_eq o ho
      exact ⟨⟨x, hx⟩, Subtype.ext hxo⟩)

@[simp] theorem nonoteIsoIio_apply_val (a : NONote) : (nonoteIsoIio a).1 = a.repr := rfl

/-- The order type of the normal-form notations is `ε₀`. -/
theorem type_lt_NONote :
    Ordinal.type ((· < ·) : NONote → NONote → Prop) = ε₀ := by
  have h := nonoteIsoIio.toRelIsoLT.ordinal_lift_type_eq
  have h2 : Ordinal.type ((· < ·) : Set.Iio (ε₀ : Ordinal.{0}) → _ → Prop)
      = Ordinal.lift.{1} (ε₀ : Ordinal.{0}) := Ordinal.type_lt_Iio _
  rw [h2] at h
  rw [Ordinal.lift_lift] at h
  exact Ordinal.lift_inj.1 (h.trans (by simp))

end OrdinalAnalysis.ONoteEps
