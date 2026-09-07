/-
  Reflection of mathlib ordinal notations into the internal HFS coding.

  The external `ONote` recursion and the internal arithmetized recursion use
  the same pairing layout.  Consequently comparison and normal-form facts for
  every fixed standard notation remain valid in every model of IΣ₁.
-/
import OrdinalAnalysis.Gentzen.InternalONote
import Mathlib.SetTheory.Ordinal.Notation

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.NotationBridge

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote

/-- The primitive-recursive natural-number code of a mathlib ordinal notation. -/
def code : ONote → ℕ
  | 0 => 0
  | .oadd e n r => Nat.pair (Nat.pair (code e) (n : ℕ)) (code r) + 1

/-- The standard numeral denoting an external notation code in an arithmetic model. -/
def modelCode {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (o : ONote) : V := (code o : V)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] lemma modelCode_zero : modelCode (V := V) 0 = 0 := by
  simp [modelCode, code]

@[simp] lemma numeral_code_eq_modelCode (o : ONote) :
    ORingStructure.numeral (code o) = modelCode (V := V) o := by
  simp [modelCode, numeral_eq_natCast]

@[simp] lemma modelCode_oadd (e r : ONote) (n : ℕ+) :
    modelCode (V := V) (.oadd e n r) =
      ocOadd (modelCode (V := V) e) (n : ℕ) (modelCode (V := V) r) := by
  simp [modelCode, code, ocOadd, coe_pair_eq_pair_coe]

/-- Arithmetic code used by both `ONote.cmp` and the internal comparator. -/
def orderingCode : Ordering → ℕ
  | .lt => 0
  | .eq => 1
  | .gt => 2

@[simp] lemma thenV_orderingCode (a b : Ordering) :
    thenV (V := V) (orderingCode a : V) (orderingCode b : V) =
      (orderingCode (a.then b) : V) := by
  cases a <;> simp [thenV, orderingCode]

@[simp] lemma cmpV_natCast (m n : ℕ) :
    cmpV (V := V) (m : V) (n : V) =
      (orderingCode (_root_.cmp m n) : V) := by
  rcases lt_trichotomy m n with h | h | h
  · simp [cmpV, _root_.cmp, cmpUsing, h, orderingCode]
  · subst n
    simp [cmpV, _root_.cmp, cmpUsing, orderingCode]
  · have hnm : n < m := h
    have hmn : ¬m < n := Nat.not_lt.mpr (Nat.le_of_lt hnm)
    have hne : m ≠ n := Nat.ne_of_gt hnm
    simp [cmpV, _root_.cmp, cmpUsing, hnm, hmn, hne, orderingCode]

/-- Exact agreement of the external structural comparator with the internal one. -/
theorem icmp_modelCode : ∀ a b : ONote,
    icmp (modelCode (V := V) a) (modelCode (V := V) b) =
      (orderingCode (a.cmp b) : V) := by
  intro a
  induction a with
  | zero =>
      intro b
      cases b with
      | zero => simp [ONote.cmp, orderingCode]
      | oadd e n r => simp [ONote.cmp, orderingCode, icmp_zero_ocOadd]
  | oadd e n r ihe ihr =>
      intro b
      cases b with
      | zero => simp [ONote.cmp, orderingCode, icmp_ocOadd_zero]
      | oadd e' n' r' =>
          simp only [ONote.cmp, modelCode_oadd, icmp_ocOadd, ihe, ihr,
            cmpV_natCast, thenV_orderingCode]

/-- Every external Cantor-normal-form notation is recognized by `isNF` in
every model of IΣ₁ when inserted as its standard natural-number code. -/
theorem isNF_modelCode : ∀ o : ONote, ONote.NF o →
    isNF (modelCode (V := V) o) := by
  intro o
  induction o with
  | zero =>
      intro _
      exact isNF_zero (V := V)
  | oadd e n r ihe ihr =>
      intro hnf
      rw [modelCode_oadd, isNF_ocOadd]
      have he : ONote.NF e := hnf.fst
      have hr : ONote.NF r := hnf.snd
      refine ⟨?_, ihe he, ihr hr, ?_⟩
      · exact_mod_cast (Nat.ne_of_gt n.2)
      · cases r with
        | zero => simp
        | oadd er nr rr =>
            right
            have htop : ONote.TopBelow e (.oadd er nr rr) :=
              ((@ONote.nfBelow_iff_topBelow e he (.oadd er nr rr)).mp
                hnf.snd').2
            simp only [modelCode_oadd, ocExp_ocOadd]
            rw [icmp_modelCode]
            change er.cmp e = Ordering.lt at htop
            rw [htop]
            simp [orderingCode]

@[simp] theorem icmp_modelCode_eq_zero_iff (a b : ONote) :
    icmp (modelCode (V := V) a) (modelCode (V := V) b) = 0 ↔
      a.cmp b = Ordering.lt := by
  rw [icmp_modelCode]
  cases a.cmp b <;> simp [orderingCode]

/-- On external normal forms, external ordinal order is precisely internal
comparison code zero. -/
theorem lt_iff_icmp_modelCode_eq_zero (a b : ONote)
    [ONote.NF a] [ONote.NF b] :
    a < b ↔ icmp (modelCode (V := V) a) (modelCode (V := V) b) = 0 := by
  rw [icmp_modelCode_eq_zero_iff]
  exact (ONote.cmp_compares a b).eq_lt.symm

/-- Natural-number code specialized to normal-form notations. -/
def nonoteCode (o : NONote) : ℕ := code o.1

/-- A normal-form notation code interpreted in an arithmetic model. -/
def nonoteModelCode (o : NONote) : V := (nonoteCode o : V)

@[simp] lemma nonoteModelCode_eq (o : NONote) :
    nonoteModelCode (V := V) o = modelCode (V := V) o.1 := rfl

theorem isNF_nonoteModelCode (o : NONote) :
    isNF (nonoteModelCode (V := V) o) := by
  rw [nonoteModelCode_eq]
  exact isNF_modelCode o.1 o.2

theorem nonote_lt_iff_icmpModelCode_eq_zero (a b : NONote) :
    a < b ↔
      icmp (nonoteModelCode (V := V) a) (nonoteModelCode (V := V) b) = 0 := by
  rw [nonoteModelCode_eq, nonoteModelCode_eq]
  change a.1 < b.1 ↔ _
  exact lt_iff_icmp_modelCode_eq_zero a.1 b.1

end OrdinalAnalysis.Gentzen.NotationBridge
