/-
  Encodability and decidability for mathlib's ordinal notations, on top of
  the project's code `NotationBridge.code : ONote → ℕ`.

  Gentzen 1943 talks about notations below ε₀ *inside* arithmetic, so every
  notation needs a numeral, hence a code.  mathlib's `ONote` carries no
  `Encodable` instance (checked on db584cd6d46c: `deriving DecidableEq` is the
  only derived instance, Mathlib/SetTheory/Ordinal/Notation.lean:43).

  The coding is *not invented* here.  It is `NotationBridge.code`
  (OrdinalAnalysis/Gentzen/NotationBridge.lean:20),

    code 0            = 0
    code (oadd e n a) = ⟪⟪code e, n⟫, code a⟫ + 1

  with the coefficient `n : ℕ+` stored as the number `n` itself, and it is the
  one the verified upper bound already uses through `modelCode`.  This file
  adds what the bridge does not need but the syntactic side does:

  * `toCode`, the same recursion spelled out locally, with `toCode_eq_code`
    proving it *is* the bridge's `code` — so nothing below forks the coding;
  * a decoder `ofCode` with `ofCode (code o) = o`, hence `code_injective`
    and `toCode_injective`;
  * `Encodable ONote` and `Encodable NONote` built from `code`;
  * Boolean decision procedures `ltb`, `leb`, `nfb` for `<`, `≤` and `NF`,
    correct on normal forms, stated as explicit primitive recursions on the
    syntax so they can later be reflected into PA;
  * the closed `LX`-term `noteNumeral o` naming `code o`, and its identification
    with the `lMap`-image of the arithmetic numeral.

  Decoding treats a zero coefficient as garbage and returns `0`.
-/
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Encodable.Basic
import Mathlib.Tactic.FinCases
import OrdinalAnalysis.Gentzen.NotationBridge
import OrdinalAnalysis.Gentzen.Setup

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.NotationBridge

/-! ### Equations of the code -/

@[simp] theorem code_zero : code 0 = 0 := rfl

@[simp] theorem code_zero' : code ONote.zero = 0 := rfl

@[simp] theorem code_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    code (.oadd e n a) = Nat.pair (Nat.pair (code e) (n : ℕ)) (code a) + 1 := rfl

theorem code_oadd_pos (e : ONote) (n : ℕ+) (a : ONote) : 0 < code (.oadd e n a) :=
  Nat.succ_pos _

theorem code_eq_zero_iff {o : ONote} : code o = 0 ↔ o = 0 := by
  cases o with
  | zero => simp
  | oadd e n a => simp

/-! ### The encoder of this file

`toCode` is the same primitive recursion written out here, so that the
encodability development below is readable without opening the bridge.  It is
*not* a second coding: `toCode_eq_code` identifies it with
`NotationBridge.code` (NotationBridge.lean:20), so every fact proved for one
transfers to the other. -/

/-- The code of a notation, as a self-contained primitive recursion.  Equal to
`code` by `toCode_eq_code`; the coefficient `n : ℕ+` is stored as the number
`n` itself, matching the internal `ocOadd` (InternalONote.lean:20). -/
def toCode : ONote → ℕ
  | .zero => 0
  | .oadd e n a => Nat.pair (Nat.pair (toCode e) (n : ℕ)) (toCode a) + 1

@[simp] theorem toCode_zero : toCode 0 = 0 := rfl

@[simp] theorem toCode_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    toCode (.oadd e n a) = Nat.pair (Nat.pair (toCode e) (n : ℕ)) (toCode a) + 1 := rfl

/-- The two codes are the same function. -/
theorem toCode_eq_code : ∀ o : ONote, toCode o = code o
  | .zero => rfl
  | .oadd e n a => by
      rw [toCode_oadd, code_oadd, toCode_eq_code e, toCode_eq_code a]

theorem toCode_eq_code' : toCode = code := funext toCode_eq_code

/-! ### Decoding -/

/-- Partial decoding.  Returns `0` on numbers that are not codes, i.e. those
whose coefficient field is `0`.  Well-founded on the code: both sub-codes of
`k + 1` are `≤ k` by `Nat.unpair_left_le` / `Nat.unpair_right_le`. -/
def ofCode : ℕ → ONote
  | 0 => 0
  | k + 1 =>
    if h : (Nat.unpair (Nat.unpair k).1).2 = 0 then 0
    else
      .oadd (ofCode (Nat.unpair (Nat.unpair k).1).1)
        ⟨(Nat.unpair (Nat.unpair k).1).2, Nat.pos_of_ne_zero h⟩
        (ofCode (Nat.unpair k).2)
termination_by n => n
decreasing_by
  all_goals
    first
    | exact Nat.lt_succ_of_le (le_trans (Nat.unpair_left_le _) (Nat.unpair_left_le _))
    | exact Nat.lt_succ_of_le (Nat.unpair_right_le _)

theorem ofCode_zero : ofCode 0 = 0 := by
  rw [ofCode]

/-- `ofCode` is a left inverse of `code`. -/
theorem ofCode_code : ∀ o : ONote, ofCode (code o) = o
  | .zero => ofCode_zero
  | .oadd e n a => by
      rw [code_oadd, ofCode]
      simp only [Nat.unpair_pair]
      rw [dif_neg (PNat.ne_zero n), ofCode_code e, ofCode_code a]
      rfl

theorem leftInverse_ofCode : Function.LeftInverse ofCode code := ofCode_code

/-- The code is injective: distinct notations have distinct codes. -/
theorem code_injective : Function.Injective code :=
  leftInverse_ofCode.injective

theorem code_inj {a b : ONote} : code a = code b ↔ a = b :=
  code_injective.eq_iff

theorem ofCode_surjective : Function.Surjective ofCode :=
  leftInverse_ofCode.surjective

/-! ### The round trip for `toCode` -/

/-- `ofCode` decodes `toCode`: the round trip. -/
@[simp] theorem ofCode_toCode (o : ONote) : ofCode (toCode o) = o := by
  rw [toCode_eq_code]; exact ofCode_code o

theorem leftInverse_ofCode_toCode : Function.LeftInverse ofCode toCode := ofCode_toCode

/-- Distinct notations get distinct codes. -/
theorem toCode_injective : Function.Injective toCode :=
  leftInverse_ofCode_toCode.injective

theorem toCode_inj {a b : ONote} : toCode a = toCode b ↔ a = b :=
  toCode_injective.eq_iff

/-! ### Encodability -/

instance instEncodableONote : Encodable ONote :=
  Encodable.ofLeftInverse code ofCode ofCode_code

@[simp] theorem encode_eq (o : ONote) : Encodable.encode o = code o := rfl

@[simp] theorem decode_eq (k : ℕ) :
    (Encodable.decode k : Option ONote) = some (ofCode k) := rfl

instance instCountableONote : Countable ONote := inferInstance

/-- Normal-form notations inherit the code through the subtype. -/
instance instEncodableNONote : Encodable NONote :=
  inferInstanceAs (Encodable {o : ONote // ONote.NF o})

@[simp] theorem encode_nonote (o : NONote) : Encodable.encode o = nonoteCode o := rfl

theorem nonoteCode_injective : Function.Injective nonoteCode :=
  fun _ _ h => Subtype.ext (code_injective h)

/-! ### Boolean decision procedures

`ONote.cmp` (Notation.lean:154) decides the order, but only on normal forms
(`ONote.cmp_compares`, Notation.lean:280).  These wrap it into `Bool`-valued
functions whose recursion is explicit, so it can later be arithmetized. -/

/-- `a < b`, decided through `ONote.cmp`; correct on normal forms (`ltb_iff`). -/
def ltb (a b : ONote) : Bool := decide (a.cmp b = Ordering.lt)

/-- `a ≤ b`, decided through `ONote.cmp`; correct on normal forms (`leb_iff`). -/
def leb (a b : ONote) : Bool := decide (a.cmp b ≠ Ordering.gt)

theorem ltb_iff {a b : ONote} (ha : ONote.NF a) (hb : ONote.NF b) :
    ltb a b = true ↔ a < b := by
  unfold ltb
  rw [decide_eq_true_iff]
  exact (@ONote.cmp_compares a b ha hb).eq_lt

theorem leb_iff {a b : ONote} (ha : ONote.NF a) (hb : ONote.NF b) :
    leb a b = true ↔ a ≤ b := by
  unfold leb
  rw [decide_eq_true_iff]
  exact (@ONote.cmp_compares a b ha hb).ne_gt

theorem ltb_iff_cmp {a b : ONote} : ltb a b = true ↔ a.cmp b = Ordering.lt := by
  unfold ltb
  exact decide_eq_true_iff

open LO LO.FirstOrder LO.FirstOrder.Arithmetic in
/-- `ltb` agrees with the internal comparator of the bridge: on any model of
IΣ₁ the code of `a` compares below the code of `b` exactly when `ltb a b`. -/
theorem ltb_iff_icmp_modelCode {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a b : ONote) :
    ltb a b = true ↔
      InternalONote.icmp (modelCode (V := V) a) (modelCode (V := V) b) = 0 := by
  rw [ltb_iff_cmp, icmp_modelCode_eq_zero_iff]

/-- `TopBelow b o` (Notation.lean:340) as a Boolean: the leading exponent of
`o`, if any, compares below `b`. -/
def topBelowb (b : ONote) : ONote → Bool
  | .zero => true
  | .oadd e _ _ => decide (e.cmp b = Ordering.lt)

theorem topBelowb_iff (b o : ONote) : topBelowb b o = true ↔ ONote.TopBelow b o := by
  cases o with
  | zero => simp [topBelowb, ONote.TopBelow]
  | oadd e n a => simp [topBelowb, ONote.TopBelow]

/-- Normal form as a Boolean recursion on the syntax. -/
def nfb : ONote → Bool
  | .zero => true
  | .oadd e _ a => nfb e && nfb a && topBelowb e a

/-- The recursion behind mathlib's `decidableNF` (Notation.lean:354), stated. -/
theorem nf_oadd_iff {e : ONote} {n : ℕ+} {a : ONote} :
    ONote.NF (.oadd e n a) ↔ ONote.NF e ∧ ONote.NF a ∧ ONote.TopBelow e a :=
  ⟨fun h => ⟨h.fst, (@ONote.nfBelow_iff_topBelow e h.fst a).mp h.snd'⟩,
   fun ⟨h₁, h₂, h₃⟩ => ONote.NF.oadd h₁ n ((@ONote.nfBelow_iff_topBelow e h₁ a).mpr ⟨h₂, h₃⟩)⟩

theorem nfb_iff : ∀ o : ONote, nfb o = true ↔ ONote.NF o
  | .zero => ⟨fun _ => ONote.NF.zero, fun _ => rfl⟩
  | .oadd e n a => by
      rw [nf_oadd_iff, ← nfb_iff e, ← nfb_iff a, ← topBelowb_iff e a]
      simp [nfb, and_assoc]

end OrdinalAnalysis.Gentzen.NotationBridge

/-! ### Numerals -/

namespace OrdinalAnalysis.Gentzen

open LO LO.FirstOrder

/-- The closed term of `LX` naming the code of `o`: `S^{code o} 0`, built by
Foundation's `Semiterm.numeral` (Foundation/FirstOrder/Basic/Operator.lean:695,
generic in any language with `0`, `1`, `+`; here `LX` through `Language.ORing LX`). -/
def noteNumeral (o : ONote) : Semiterm LX ℕ 0 := Semiterm.numeral (NotationBridge.code o)

theorem noteNumeral_def (o : ONote) :
    noteNumeral o = ((NotationBridge.code o : ℕ) : Semiterm LX ℕ 0) := rfl

/-- The same term, spelled with this file's `toCode`. -/
theorem noteNumeral_toCode (o : ONote) :
    noteNumeral o = ((NotationBridge.toCode o : ℕ) : Semiterm LX ℕ 0) := by
  rw [noteNumeral_def, NotationBridge.toCode_eq_code]

/-! ### Transport from `ℒₒᵣ`

A PA theorem `σ` moves to `LX` as `Semiformula.lMap toLX σ`.  If `σ` mentions
the arithmetic numeral of a code, the moved sentence mentions
`Semiterm.lMap toLX` of it, and this is what identifies that with
`noteNumeral`. -/

section transport

variable {ξ : Type*} {n : ℕ}

lemma lMap_toLX_numeral_zero :
    Semiterm.lMap toLX ((0 : ℕ) : Semiterm ℒₒᵣ ξ n) = ((0 : ℕ) : Semiterm LX ξ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, toLX]

lemma lMap_toLX_numeral_one :
    Semiterm.lMap toLX ((1 : ℕ) : Semiterm ℒₒᵣ ξ n) = ((1 : ℕ) : Semiterm LX ξ n) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, toLX]

lemma lMap_toLX_add (v : Fin 2 → Semiterm ℒₒᵣ ξ n) :
    Semiterm.lMap toLX (Semiterm.Operator.Add.add.operator v) =
      Semiterm.Operator.Add.add.operator (Semiterm.lMap toLX ∘ v) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, toLX]
  funext i
  simp

/-- `numeral (k + 2) = numeral (k + 1) + 1`, in the shape `Add.add.operator ![_, _]`
(`Semiterm.Operator.numeral_succ`, Foundation/FirstOrder/Basic/Operator.lean:166). -/
lemma numeral_succ_succ (L : Language) [L.Zero] [L.One] [L.Add] (k : ℕ) :
    ((k + 1 + 1 : ℕ) : Semiterm L ξ n) =
      Semiterm.Operator.Add.add.operator
        ![((k + 1 : ℕ) : Semiterm L ξ n), ((1 : ℕ) : Semiterm L ξ n)] := by
  have h : k + 1 ≠ 0 := Nat.succ_ne_zero k
  simp only [Semiterm.numeral, Semiterm.Operator.const,
    Semiterm.Operator.numeral_succ h, Semiterm.Operator.operator_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem lMap_toLX_numeral (k : ℕ) :
    Semiterm.lMap toLX ((k : ℕ) : Semiterm ℒₒᵣ ξ n) = ((k : ℕ) : Semiterm LX ξ n) := by
  induction k with
  | zero => exact lMap_toLX_numeral_zero
  | succ k ih =>
    cases k with
    | zero => exact lMap_toLX_numeral_one
    | succ k =>
      rw [numeral_succ_succ ℒₒᵣ k, numeral_succ_succ LX k, lMap_toLX_add]
      congr 1
      funext i
      fin_cases i
      · exact ih
      · exact lMap_toLX_numeral_one

end transport

theorem noteNumeral_eq_lMap (o : ONote) :
    noteNumeral o =
      Semiterm.lMap toLX ((NotationBridge.code o : ℕ) : Semiterm ℒₒᵣ ℕ 0) :=
  (lMap_toLX_numeral _).symm

end OrdinalAnalysis.Gentzen

