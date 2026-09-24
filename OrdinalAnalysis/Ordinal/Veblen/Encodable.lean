/-
  `Gamma0Note` is encodable.

  A Veblen notation is a finite tree, so it has a Gödel number: `0` codes `0`, and
  `vadd a b n c` is coded by `⟨⟨a, b⟩, ⟨n − 1, c⟩⟩ + 1` (nested `Nat.pair`).  Every number
  decodes to *some* notation (`decodeV`, total), and decoding inverts coding (`decodeV_encodeV`).

  The normal forms are then cut out by a computable test.  `NF` is stated through `repr`, but
  on notations whose parts are already normal both of its side conditions are syntactic:
  `b` is a fixed point of `φ_a` exactly when it passes the test of `VNote.veblenNote`
  (`veblen_repr_eq_of_test` / `repr_lt_veblen_of_test`), and the tail condition is a
  comparison, decided by `cmp` (`repr_lt_iff`).  So `NF` is decidable (`nfb_iff`), and
  `Gamma0Note`, a subtype of `VNote`, inherits an `Encodable` instance.
-/
import OrdinalAnalysis.Ordinal.Veblen.Instance
import Mathlib.Logic.Encodable.Basic

set_option autoImplicit false

namespace OrdinalAnalysis

open Ordinal

namespace VNote

/-! ### Coding and decoding notations -/

/-- The Gödel number of a notation. -/
def encodeV : VNote → ℕ
  | .zero => 0
  | .vadd a b n c => Nat.pair (Nat.pair (encodeV a) (encodeV b)) (Nat.pair n.natPred (encodeV c)) + 1

/-- The notation of a number.  Total: every number decodes to some notation. -/
def decodeV : ℕ → VNote
  | 0 => .zero
  | k + 1 =>
      .vadd (decodeV k.unpair.1.unpair.1) (decodeV k.unpair.1.unpair.2)
        k.unpair.2.unpair.1.succPNat (decodeV k.unpair.2.unpair.2)
  decreasing_by
    · exact Nat.lt_succ_of_le ((Nat.unpair_left_le _).trans (Nat.unpair_left_le _))
    · exact Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_left_le _))
    · exact Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _))

/-- **Decoding inverts coding.** -/
theorem decodeV_encodeV : ∀ x : VNote, decodeV (encodeV x) = x
  | .zero => by rw [encodeV, decodeV]
  | .vadd a b n c => by
    rw [encodeV, decodeV]
    simp only [Nat.unpair_pair, PNat.succPNat_natPred]
    rw [decodeV_encodeV a, decodeV_encodeV b, decodeV_encodeV c]

theorem encodeV_injective : Function.Injective encodeV :=
  Function.LeftInverse.injective decodeV_encodeV

instance : Encodable VNote :=
  Encodable.ofLeftInverse encodeV decodeV decodeV_encodeV

/-! ### Deciding the normal form -/

/-- The fixed-point test of `veblenNote`: `true` exactly when `b = φ_{b₁}(b₂)` with `a < b₁`,
decided syntactically. -/
def fixTest (a : VNote) : VNote → Bool
  | .zero => false
  | .vadd b₁ _ n c => decide (n = 1 ∧ c = 0 ∧ cmp a b₁ = Ordering.lt)

/-- **The normal-form test.** -/
def nfb : VNote → Bool
  | .zero => true
  | .vadd a b _ c =>
      nfb a && nfb b && nfb c && !(fixTest a b) && decide (cmp c (.vadd a b 1 0) = Ordering.lt)

/-- On normal parts, failing the fixed-point test is the side condition of `NF`. -/
theorem fixTest_false_iff {a b : VNote} (ha : NF a) (hb : NF b) :
    fixTest a b = false ↔ repr b < veblen (repr a) (repr b) := by
  cases b with
  | zero =>
    simp only [fixTest, true_iff]
    exact veblen_pos
  | vadd b₁ b₂ n c =>
    simp only [fixTest, decide_eq_false_iff_not]
    constructor
    · intro htest
      exact repr_lt_veblen_of_test ha hb htest
    · rintro hlt ⟨rfl, rfl, hcmp⟩
      exact absurd (veblen_repr_eq_of_test ha hb.fst hcmp) hlt.ne'

/-- **The test decides `NF`.** -/
theorem nfb_iff : ∀ x : VNote, nfb x = true ↔ NF x
  | .zero => by simp only [nfb, true_iff]; exact NF.zero
  | .vadd a b n c => by
    simp only [nfb, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    constructor
    · rintro ⟨⟨⟨⟨ha, hb⟩, hc⟩, hfix⟩, hcmp⟩
      have ha' := (nfb_iff a).1 ha
      have hb' := (nfb_iff b).1 hb
      have hc' := (nfb_iff c).1 hc
      have hsnd := (fixTest_false_iff ha' hb').1 hfix
      have hlead : NF (VNote.vadd a b 1 0) := NF.vadd_zero 1 ha' hb' hsnd
      have htail : repr c < repr (VNote.vadd a b 1 0) := (repr_lt_iff hc' hlead).2 hcmp
      rw [repr_vadd_one_zero] at htail
      exact NF.vadd ha' hb' hc' hsnd htail
    · intro h
      have hlead : NF (VNote.vadd a b 1 0) := NF.vadd_zero 1 h.fst h.snd h.snd_lt
      have htail : repr c < repr (VNote.vadd a b 1 0) := by
        rw [repr_vadd_one_zero]; exact h.tail_lt
      exact ⟨⟨⟨⟨(nfb_iff a).2 h.fst, (nfb_iff b).2 h.snd⟩, (nfb_iff c).2 h.tail⟩,
        (fixTest_false_iff h.fst h.snd).2 h.snd_lt⟩, (repr_lt_iff h.tail hlead).1 htail⟩

instance decidableNF : DecidablePred NF := fun x => decidable_of_iff _ (nfb_iff x)

end VNote

namespace Gamma0Note

/-- **`Gamma0Note` is encodable**, as the subtype of the normal forms. -/
instance instEncodable : Encodable Gamma0Note :=
  inferInstanceAs (Encodable { o : VNote // VNote.NF o })

end Gamma0Note

end OrdinalAnalysis
