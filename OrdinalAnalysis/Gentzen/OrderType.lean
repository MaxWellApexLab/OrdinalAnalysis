/-
  The order type of the coded ordering `≺` is exactly `ε₀`.

  `gentzen_theorem` (`Gentzen/GentzenTheorem.lean`) is stated about the coded ordering
  `≺` = `CodedNotation.precCode`, read in `ℕ` as `PrecStandard.precN`, and its reading as
  `|PA| = ε₀` rests on the fact that `≺` *is* the standard ε₀-ordering.  That fact is
  assembled here, from two pieces already in the repository:

  * `CodeSurj.isNF_iff_exists_nonote` — in `ℕ`, the codes the internal recogniser accepts
    are exactly the codes of normal-form notations, so `nonoteCode` is onto the field of `≺`;
  * `PrecStandard.precN_code_iff` — standard codes are ordered as the notations are.

  Together they give an order isomorphism `codeIso : (NONote, <) ≃r (Field, precF)`, hence
  `type precF = type (NONote, <)`.  The remaining input, that the order type of mathlib's
  `NONote` is `ε₀`, is *not* in mathlib: mathlib has `NONote.repr` strictly monotone but not
  its surjectivity onto `Set.Iio ε₀`.  The §"ε₀-completeness" block below supplies it,
  adapted (Apache 2.0) from Trevor Morris' `gotrevor/goodstein-independence`,
  `GoodsteinPA/ToMathlib/Ordinal/Epsilon0.lean` (`exists_NF_repr_eq`, `range_NONote_repr`).
-/
import Mathlib.SetTheory.Ordinal.Veblen
import OrdinalAnalysis.Gentzen.CodeSurj
import OrdinalAnalysis.Gentzen.GentzenTheorem

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.OrderType

open Ordinal
open scoped Ordinal
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.NotationBridge
open OrdinalAnalysis.Gentzen.PrecStandard
open OrdinalAnalysis.Gentzen.CodeSurj
open OrdinalAnalysis.Gentzen.CodedNotation
open OrdinalAnalysis.Gentzen.Order
open OrdinalAnalysis.Gentzen.UpperBound
open OrdinalAnalysis.Gentzen.StandardLX

open LO LO.FirstOrder

/-! ### ε₀-completeness of the CNF notations

Mathlib proves `NONote.repr` is a strictly monotone embedding into the ordinals, but not
that its range is all of `Set.Iio ε₀`.  Both halves of that are proved here. -/

/-- For `0 ≠ o < ε₀`, the leading CNF exponent `log ω o` is strictly below `o`. -/
theorem log_omega0_lt_self {o : Ordinal} (ho : o ≠ 0) (hε : o < ε₀) : log ω o < o := by
  have h1 : ω ^ log ω o ≤ o := opow_log_le_self ω ho
  have h2 : log ω o ≤ ω ^ log ω o :=
    (isNormal_opow one_lt_omega0).strictMono.le_apply
  rcases lt_or_eq_of_le (h2.trans h1) with h | h
  · exact h
  · rw [h] at h1
    exact absurd (epsilon_zero_le_of_omega0_opow_le h1) (not_le.2 hε)

/-- **ε₀-completeness of the CNF notations.**  Every ordinal `< ε₀` is `repr` of some
normal-form `ONote`. -/
theorem exists_NF_repr_eq (o : Ordinal) (hε : o < ε₀) :
    ∃ x : ONote, x.NF ∧ x.repr = o := by
  induction o using WellFoundedLT.induction with
  | _ o IH =>
    obtain rfl | ho := eq_or_ne o 0
    · exact ⟨0, ONote.NF.zero, ONote.repr_zero⟩
    · set e := log ω o with he
      have hee : e < o := log_omega0_lt_self ho hε
      obtain ⟨eN, heNF, heRepr⟩ := IH e hee (hee.trans hε)
      set r := o % ω ^ e with hr
      have hre : r < o := mod_opow_log_lt_self ω ho
      obtain ⟨rN, hrNF, hrRepr⟩ := IH r hre (hre.trans hε)
      have hcpos : 0 < o / ω ^ e := div_opow_log_pos ω ho
      have hclt : o / ω ^ e < ω := div_opow_log_lt o one_lt_omega0
      obtain ⟨m, hm⟩ := lt_omega0.1 hclt
      have hmpos : 0 < m := by rw [hm] at hcpos; exact_mod_cast hcpos
      have hωe : ω ^ e ≠ 0 := (opow_pos e omega0_pos).ne'
      refine ⟨ONote.oadd eN ⟨m, hmpos⟩ rN, ?_, ?_⟩
      · refine ONote.NF.oadd heNF _ (ONote.NF.below_of_lt' ?_ hrNF)
        rw [hrRepr, heRepr]
        exact mod_lt _ hωe
      · have hval : ONote.repr (ONote.oadd eN ⟨m, hmpos⟩ rN)
            = ω ^ ONote.repr eN * (m : Ordinal) + ONote.repr rN := by
          simp [ONote.repr]
        rw [hval, heRepr, hrRepr, hr, ← hm]
        exact div_add_mod o (ω ^ e)

/-- `ε₀` is a limit ordinal: it is `ω ^ ε₀`, a nonzero power of the limit `ω`. -/
theorem isSuccLimit_epsilon0 : Order.IsSuccLimit ε₀ := by
  have h := isSuccLimit_opow_left isSuccLimit_omega0 (epsilon_pos 0).ne'
  rwa [omega0_opow_epsilon] at h

/-- Every normal-form `ONote` represents an ordinal `< ε₀`. -/
theorem repr_lt_epsilon0 (x : ONote) (h : x.NF) : x.repr < ε₀ := by
  induction x with
  | zero => exact epsilon_pos 0
  | oadd e n a IHe IHa =>
    have hee : ONote.repr e < ε₀ := IHe h.fst
    have hbelow : ONote.repr a < ω ^ ONote.repr e := h.snd'.repr_lt
    have hsucc : Order.succ (ONote.repr e) < ε₀ := isSuccLimit_epsilon0.succ_lt hee
    have key : ONote.repr (ONote.oadd e n a) < ω ^ (Order.succ (ONote.repr e)) := by
      rw [opow_succ]
      have h1 : ONote.repr (ONote.oadd e n a)
          = ω ^ ONote.repr e * ((n : ℕ) : Ordinal) + ONote.repr a := by
        simp [ONote.repr]
      rw [h1]
      calc ω ^ ONote.repr e * ((n : ℕ) : Ordinal) + ONote.repr a
          < ω ^ ONote.repr e * ((n : ℕ) : Ordinal) + ω ^ ONote.repr e :=
            (add_lt_add_iff_left _).2 hbelow
        _ = ω ^ ONote.repr e * (((n : ℕ) : Ordinal) + 1) := by rw [mul_add, mul_one]
        _ ≤ ω ^ ONote.repr e * ω := by
            gcongr
            rw [← Nat.cast_one, ← Nat.cast_add]
            exact (natCast_lt_omega0 _).le
    exact key.trans (((opow_lt_opow_iff_right one_lt_omega0).2 hsucc).trans_eq
      (omega0_opow_epsilon 0))

/-- The range of `NONote.repr` is exactly the ordinals `< ε₀`. -/
theorem range_NONote_repr : Set.range NONote.repr = Set.Iio ε₀ := by
  ext o
  constructor
  · rintro ⟨x, rfl⟩
    exact repr_lt_epsilon0 x.1 x.2
  · intro ho
    obtain ⟨x, hx, hxo⟩ := exists_NF_repr_eq o ho
    exact ⟨⟨x, hx⟩, hxo⟩

/-- `NONote.repr`, viewed as an order isomorphism onto `Set.Iio ε₀`. -/
noncomputable def reprIso : NONote ≃o Set.Iio ε₀ where
  toEquiv :=
    Equiv.ofBijective (fun o : NONote => (⟨NONote.repr o, by
        rw [← range_NONote_repr]; exact ⟨o, rfl⟩⟩ : Set.Iio ε₀))
      ⟨fun a b h => by
        have h' : NONote.repr a = NONote.repr b := congrArg Subtype.val h
        exact le_antisymm h'.le h'.ge,
       fun x => by
        obtain ⟨o, ho⟩ : x.1 ∈ Set.range NONote.repr := by
          rw [range_NONote_repr]; exact x.2
        exact ⟨o, Subtype.ext ho⟩⟩
  map_rel_iff' := by
    intro a b
    exact Iff.rfl

/-- **The order type of the CNF notations is `ε₀`.** -/
theorem type_NONote_lt : typeLT NONote = ε₀ := by
  have h := reprIso.toRelIsoLT.ordinal_lift_type_eq
  rw [type_lt_Iio] at h
  have h2 : Ordinal.lift.{1, 0} (typeLT NONote) = Ordinal.lift.{1, 0} ε₀ := by
    simpa using h
  exact Ordinal.lift_inj.1 h2

/-! ### The field of `≺` and its order type -/

/-- The field of `≺` on `ℕ`: the codes the internal recogniser accepts. -/
abbrev Field : Type := {n : ℕ // InternalONote.isNF (V := ℕ) n}

/-- `≺` restricted to its field. -/
def precF (m n : Field) : Prop := PrecStandard.precN m.1 n.1

/-- The code of a notation, as an element of the field of `≺`. -/
def toField (o : NONote) : Field :=
  ⟨nonoteCode o, (isNF_iff_exists_nonote _).mpr ⟨o, rfl⟩⟩

theorem toField_injective : Function.Injective toField := by
  intro a b h
  have hc : nonoteCode a = nonoteCode b := congrArg Subtype.val h
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd ((precN_code_iff a a).1 (by
      have := precN_code_of_lt hlt; rwa [← hc] at this)) (lt_irrefl a)
  · exact heq
  · exact absurd ((precN_code_iff b b).1 (by
      have := precN_code_of_lt hgt; rwa [hc] at this)) (lt_irrefl b)

theorem toField_surjective : Function.Surjective toField := by
  intro n
  obtain ⟨o, ho⟩ := (isNF_iff_exists_nonote n.1).1 n.2
  exact ⟨o, Subtype.ext ho⟩

/-- **`nonoteCode` is an order isomorphism from `NONote` onto the field of `≺`.** -/
noncomputable def codeIso : @RelIso NONote Field (· < ·) precF where
  toEquiv := Equiv.ofBijective toField ⟨toField_injective, toField_surjective⟩
  map_rel_iff' := by
    intro a b
    exact precN_code_iff a b

instance precF_isWellOrder : IsWellOrder Field precF :=
  RelEmbedding.isWellOrder codeIso.symm.toRelEmbedding

/-- **`≺` has order type exactly `ε₀`.** -/
theorem precF_type_eq_epsilon0 : Ordinal.type precF = ε₀ := by
  rw [← type_NONote_lt]
  exact (Ordinal.type_eq.2 ⟨codeIso.symm⟩)

/-- **`precF` really is `≺`.**  On its field, `precF` is the standard-model reading of
`CodedNotation.precCode` in the exact spelling `gentzen_theorem` is about, namely
`precAt precCode` applied to the two numerals (`PrecStandard.eval_precAt_numeral`).
This is the audit link between the headline below and `gentzen_theorem`. -/
theorem precF_iff_eval_precCode (P : ℕ → Prop) (m n : Field) (f : ℕ → ℕ) :
    precF m n ↔ Semiformula.Eval (s := stdLX P) ![] f
      (precAt CodedNotation.precCode (LowerSyntax.numLX m.1) (LowerSyntax.numLX n.1)) :=
  (eval_precAt_numeral P m.1 n.1 f).symm

/-- Gentzen's theorem, with the order type of `≺` spelled out. -/
theorem gentzen_theorem_with_order_type :
    Ordinal.type precF = ε₀ ∧
      ((∀ (φ : Semiformula LX ℕ 1) (a : ONote) (ha : ONote.NF a),
          paLX ⊢ closedTI φ (notationTerm ⟨a, ha⟩)) ∧
        paLX ⊬ (TI CodedNotation.precCode).univCl) :=
  ⟨precF_type_eq_epsilon0, gentzen_theorem⟩

end OrdinalAnalysis.Gentzen.OrderType
