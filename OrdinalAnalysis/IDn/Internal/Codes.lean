/-
  Arithmetic coding of the multi-level ϑ-notation (`ThetaWTerm`), generalizing
  `ID1/Internal/Codes.lean`.

  **Codes.**  A term is coded by a natural number, the level of a principal term packed
  alongside its payload:

  * `⟨⟩` (the term `0`) by `0`,
  * `Ω_{k+1}` (`Omega k`) by `⟪0, k⟫ + 1`,
  * `ϑ_k α` (`theta k α`) by `⟪1, ⟪k, ⌜α⌝⟫⟫ + 1`,
  * `⟨α₀, α₁, …⟩` by `⟪2, ⟪⌜α₀⌝, ⌜⟨α₁, …⟩⌝⟫⟫ + 1`.

  This is exactly ID1's scheme with `Omega`'s payload widened from nothing to a level, and
  `theta`'s payload widened from the argument alone to a level/argument pair; `kind` (the tag
  0/1/2/3/4) is unchanged.

  **What generalizes structurally (no order needed).**  The Gödel coding itself, the internal
  constructors/destructors, the term recogniser `isTermb`, the length `ilen`, and the level-`k`
  coefficient/argument sets `iinE`/`iinG` (Wilken's `E_k`/`K*_{k+1}`) all generalize by the same
  proof shapes as ID1, with the level `k` carried as a *spectator* parameter of the recursion
  (it never changes while the inspected code shrinks).

  **What needs a new idea.**  ID1's single comparison table packing `(lt, all, ex)` at one
  position `⟪c1,c2⟫` does not directly generalize: the ϑ_k-ϑ_k order clause needs `all_k`/`ex_k`
  for the *specific* `k` read off the two codes, so the table needs an extra level dimension for
  `all`/`ex` but not for `lt`.  `IDn/Internal/CovTable.lean`'s `tagP`/`tagL` combinators encode
  this: `lt(c1,c2)` lives at `⟪tagP c1, tagP c2⟫`, `all_k(P,Q)` at `⟪tagL k P, tagP Q⟫`,
  `ex_k(P,Q)` at `⟪tagP P, tagL k Q⟫`, all sharing one well order.  See the notes file for the
  worked correctness argument (the design is sound on paper; whether it closes cleanly in Lean
  is checked below, after the order-free part).
-/
import OrdinalAnalysis.IDn.Internal.CovTable
import OrdinalAnalysis.Ordinal.ThetaW.Dom

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.ThetaWTerm
open OrdinalAnalysis.ID1.Internal (bor band beq borDef bandDef beqDef bor_defined band_defined
  beq_defined bor_eq_one band_eq_one beq_eq_one covVal covTable covVal_unfold covVal_zero
  covVal_succ covValDef covTableDef covVal_defined covTable_defined)

/-! ## Codes of terms, in `ℕ` -/

mutual
/-- The Gödel code of a term. -/
def code : ThetaWTerm → ℕ
  | .Omega k => Nat.pair 0 k + 1
  | .theta k a => Nat.pair 1 (Nat.pair k (code a)) + 1
  | .sum xs => codeList xs
/-- The code of the sum of a list of terms. -/
def codeList : List ThetaWTerm → ℕ
  | [] => 0
  | x :: xs => Nat.pair 2 (Nat.pair (code x) (codeList xs)) + 1
end

@[simp] theorem code_Omega (k : ℕ) : code (.Omega k) = Nat.pair 0 k + 1 := by simp [code]

@[simp] theorem code_theta (k : ℕ) (a : ThetaWTerm) :
    code (.theta k a) = Nat.pair 1 (Nat.pair k (code a)) + 1 := by simp [code]

@[simp] theorem code_nil : code (.sum []) = 0 := by simp [code, codeList]

@[simp] theorem code_cons (x : ThetaWTerm) (xs : List ThetaWTerm) :
    code (.sum (x :: xs)) = Nat.pair 2 (Nat.pair (code x) (code (.sum xs))) + 1 := by
  simp [code, codeList]

/-- The entries of a term read as a sum; `[]` for `Omega k` and `theta k α`. -/
def sumArgs : ThetaWTerm → List ThetaWTerm
  | .sum xs => xs
  | _ => []

@[simp] theorem sumArgs_sum (xs : List ThetaWTerm) : sumArgs (.sum xs) = xs := rfl

/-- Decoding: the inverse of `code` on codes, and some term elsewhere. -/
def decode (n : ℕ) : ThetaWTerm :=
  match n with
  | 0 => .sum []
  | k + 1 =>
    if (Nat.unpair k).1 = 1 then
      .theta (Nat.unpair (Nat.unpair k).2).1 (decode (Nat.unpair (Nat.unpair k).2).2)
    else if (Nat.unpair k).1 = 2 then
      .sum (decode (Nat.unpair (Nat.unpair k).2).1 ::
        sumArgs (decode (Nat.unpair (Nat.unpair k).2).2))
    else .Omega (Nat.unpair k).2
termination_by n
decreasing_by
  all_goals
    have h1 := Nat.unpair_right_le k
    first
      | omega
      | (have := Nat.unpair_left_le (Nat.unpair k).2; omega)
      | (have := Nat.unpair_right_le (Nat.unpair k).2; omega)

theorem decode_zero : decode 0 = .sum [] := by rw [decode]

theorem decode_succ (k : ℕ) :
    decode (k + 1) =
      if (Nat.unpair k).1 = 1 then
        .theta (Nat.unpair (Nat.unpair k).2).1 (decode (Nat.unpair (Nat.unpair k).2).2)
      else if (Nat.unpair k).1 = 2 then
        .sum (decode (Nat.unpair (Nat.unpair k).2).1 ::
          sumArgs (decode (Nat.unpair (Nat.unpair k).2).2))
      else .Omega (Nat.unpair k).2 := by
  rw [decode]

/-- **Decoding inverts coding.** -/
theorem decode_code : ∀ t : ThetaWTerm, decode (code t) = t
  | .Omega k => by
    rw [code_Omega, show Nat.pair 0 k + 1 = Nat.pair 0 k + 1 from rfl, decode_succ]
    simp
  | .theta k a => by
    rw [code_theta, decode_succ]; simp [decode_code a]
  | .sum [] => by rw [code_nil, decode_zero]
  | .sum (x :: xs) => by
    rw [code_cons, decode_succ]; simp [decode_code x, decode_code (.sum xs)]
termination_by t => l t
decreasing_by all_goals simp; try omega

theorem code_injective : Function.Injective code :=
  Function.LeftInverse.injective decode_code

@[simp] theorem code_inj {a b : ThetaWTerm} : code a = code b ↔ a = b :=
  code_injective.eq_iff

/-! ## Codes inside a model of `IΣ₁` -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The code of `Ω_{i+1}` at level `i`. -/
noncomputable def tcOmega (i : V) : V := ⟪0, i⟫ + 1

/-- The code of `ϑ_i α` from the level `i` and the code `a` of `α`. -/
noncomputable def tcTheta (i a : V) : V := ⟪1, ⟪i, a⟫⟫ + 1

/-- The code of the sum with first entry coded by `x` and remaining sum coded by `s`. -/
noncomputable def tcCons (x s : V) : V := ⟪2, ⟪x, s⟫⟫ + 1

/-- The payload of a code (after stripping the tag and the `+1`). -/
noncomputable def tcArg (c : V) : V := sndIdx c

/-- The level of an `Ω`-code. -/
noncomputable def tcOmegaLev (c : V) : V := tcArg c

/-- The level of a `ϑ`-code. -/
noncomputable def tcLev (c : V) : V := π₁ (tcArg c)

/-- The argument of a `ϑ`-code. -/
noncomputable def tcThetaArg (c : V) : V := π₂ (tcArg c)

/-- The first entry of a cons code. -/
noncomputable def tcHd (c : V) : V := π₁ (sndIdx c)

/-- The remaining sum of a cons code. -/
noncomputable def tcTl (c : V) : V := π₂ (sndIdx c)

/-- The shape of a code: `0` empty sum, `1` tag of `Ω`, `2` tag of `ϑ`, `3` tag of a cons
cell, `4` any other tag. -/
noncomputable def kind (c : V) : V :=
  if c = 0 then 0 else if fstIdx c = 0 then 1 else if fstIdx c = 1 then 2
  else if fstIdx c = 2 then 3 else 4

/-- The standard numeral of the code of a term. -/
def mc (t : ThetaWTerm) : V := (code t : V)

def tcOmegaDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y i. ∃ p, !pairDef p 0 i ∧ y = p + 1”

def tcThetaDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y i a. ∃ q, !pairDef q i a ∧ ∃ p, !pairDef p 1 q ∧ y = p + 1”

def tcConsDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y x s. ∃ q, !pairDef q x s ∧ ∃ p, !pairDef p 2 q ∧ y = p + 1”

def tcOmegaLevDef : 𝚺₀.Semisentence 2 := sndIdxDef

def tcLevDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y c. ∃ a <⁺ c, !sndIdxDef a c ∧ !pi₁Def y a”

def tcThetaArgDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y c. ∃ a <⁺ c, !sndIdxDef a c ∧ !pi₂Def y a”

def tcHdDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y c. ∃ p <⁺ c, !sndIdxDef p c ∧ !pi₁Def y p”

def tcTlDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y c. ∃ p <⁺ c, !sndIdxDef p c ∧ !pi₂Def y p”

def kindDef : 𝚺₀.Semisentence 2 := .mkSigma
  “k c. (c = 0 ∧ k = 0) ∨
    (c ≠ 0 ∧ ∃ f <⁺ c, !fstIdxDef f c ∧
      ((f = 0 ∧ k = 1) ∨ (f = 1 ∧ k = 2) ∨ (f = 2 ∧ k = 3) ∨ (f ≠ 0 ∧ f ≠ 1 ∧ f ≠ 2 ∧ k = 4)))”

instance tcOmega_defined : 𝚺₁-Function₁ (tcOmega : V → V) via tcOmegaDef := .mk fun v ↦ by
  simp [tcOmegaDef, tcOmega, pair_defined.iff]

instance tcTheta_defined : 𝚺₁-Function₂ (tcTheta : V → V → V) via tcThetaDef := .mk fun v ↦ by
  simp [tcThetaDef, tcTheta, pair_defined.iff]

instance tcCons_defined : 𝚺₁-Function₂ (tcCons : V → V → V) via tcConsDef := .mk fun v ↦ by
  simp [tcConsDef, tcCons, pair_defined.iff]

instance tcOmegaLev_defined : 𝚺₀-Function₁ (tcOmegaLev : V → V) via tcOmegaLevDef := .mk fun v ↦ by
  simp [tcOmegaLevDef, tcOmegaLev, tcArg, sndIdx_defined.iff]

instance tcLev_defined : 𝚺₀-Function₁ (tcLev : V → V) via tcLevDef := .mk fun v ↦ by
  simp [tcLevDef, tcLev, tcArg, sndIdx_defined.iff, pi₁_defined.iff]

instance tcThetaArg_defined : 𝚺₀-Function₁ (tcThetaArg : V → V) via tcThetaArgDef := .mk fun v ↦ by
  simp [tcThetaArgDef, tcThetaArg, tcArg, sndIdx_defined.iff, pi₂_defined.iff]

instance tcHd_defined : 𝚺₀-Function₁ (tcHd : V → V) via tcHdDef := .mk fun v ↦ by
  simp [tcHdDef, tcHd, sndIdx_defined.iff, pi₁_defined.iff]

instance tcTl_defined : 𝚺₀-Function₁ (tcTl : V → V) via tcTlDef := .mk fun v ↦ by
  simp [tcTlDef, tcTl, sndIdx_defined.iff, pi₂_defined.iff]

instance kind_defined : 𝚺₀-Function₁ (kind : V → V) via kindDef := .mk fun v ↦ by
  simp only [kindDef, kind]
  have hle := fstIdx_le_self (v 1)
  by_cases h0 : v 1 = 0
  · simp [h0]
  · have h1le : 1 ≤ v 1 := pos_iff_one_le.mp (pos_iff_ne_zero.mpr h0)
    by_cases h1 : fstIdx (v 1) = 0
    · simp [h0, h1, fstIdx_defined.iff]
    · by_cases h2 : fstIdx (v 1) = 1
      · simp [h0, h2, fstIdx_defined.iff, h1le]
      · by_cases h3 : fstIdx (v 1) = 2
        · rw [h3] at hle
          simp [h0, h3, fstIdx_defined.iff, hle]
        · simp [h0, h1, h2, h3, fstIdx_defined.iff]

instance tcOmega_definable : 𝚺₁-Function₁ (tcOmega : V → V) := tcOmega_defined.to_definable
instance tcTheta_definable : 𝚺₁-Function₂ (tcTheta : V → V → V) := tcTheta_defined.to_definable
instance tcCons_definable : 𝚺₁-Function₂ (tcCons : V → V → V) := tcCons_defined.to_definable
instance tcOmegaLev_definable : 𝚺₀-Function₁ (tcOmegaLev : V → V) := tcOmegaLev_defined.to_definable
instance tcLev_definable : 𝚺₀-Function₁ (tcLev : V → V) := tcLev_defined.to_definable
instance tcThetaArg_definable : 𝚺₀-Function₁ (tcThetaArg : V → V) := tcThetaArg_defined.to_definable
instance tcHd_definable : 𝚺₀-Function₁ (tcHd : V → V) := tcHd_defined.to_definable
instance tcTl_definable : 𝚺₀-Function₁ (tcTl : V → V) := tcTl_defined.to_definable
instance kind_definable : 𝚺₀-Function₁ (kind : V → V) := kind_defined.to_definable
instance tcOmegaLev_definable' (Γ) : Γ-Function₁ (tcOmegaLev : V → V) := tcOmegaLev_definable.of_zero
instance tcLev_definable' (Γ) : Γ-Function₁ (tcLev : V → V) := tcLev_definable.of_zero
instance tcThetaArg_definable' (Γ) : Γ-Function₁ (tcThetaArg : V → V) := tcThetaArg_definable.of_zero
instance tcHd_definable' (Γ) : Γ-Function₁ (tcHd : V → V) := tcHd_definable.of_zero
instance tcTl_definable' (Γ) : Γ-Function₁ (tcTl : V → V) := tcTl_definable.of_zero
instance kind_definable' (Γ) : Γ-Function₁ (kind : V → V) := kind_definable.of_zero

/-! ### Destructors and shapes of constructor codes -/

@[simp] lemma tcOmega_ne_zero (i : V) : tcOmega i ≠ 0 := by simp [tcOmega]

@[simp] lemma tcTheta_ne_zero (i a : V) : tcTheta i a ≠ 0 := by simp [tcTheta]

@[simp] lemma tcCons_ne_zero (x s : V) : tcCons x s ≠ 0 := by simp [tcCons]

@[simp] lemma tcOmegaLev_tcOmega (i : V) : tcOmegaLev (tcOmega i) = i := by
  simp [tcOmegaLev, tcArg, tcOmega, sndIdx]

@[simp] lemma tcLev_tcTheta (i a : V) : tcLev (tcTheta i a) = i := by
  simp [tcLev, tcArg, tcTheta, sndIdx]

@[simp] lemma tcThetaArg_tcTheta (i a : V) : tcThetaArg (tcTheta i a) = a := by
  simp [tcThetaArg, tcArg, tcTheta, sndIdx]

@[simp] lemma tcHd_tcCons (x s : V) : tcHd (tcCons x s) = x := by simp [tcHd, tcCons, sndIdx]

@[simp] lemma tcTl_tcCons (x s : V) : tcTl (tcCons x s) = s := by simp [tcTl, tcCons, sndIdx]

@[simp] lemma kind_zero : kind (0 : V) = 0 := by simp [kind]

@[simp] lemma kind_tcOmega (i : V) : kind (tcOmega i) = 1 := by
  simp [kind, tcOmega, fstIdx]

@[simp] lemma kind_tcTheta (i a : V) : kind (tcTheta i a) = 2 := by
  simp [kind, tcTheta, fstIdx]

@[simp] lemma kind_tcCons (x s : V) : kind (tcCons x s) = 3 := by
  simp [kind, tcCons, fstIdx]

lemma kind_cases (c : V) :
    kind c = 0 ∨ kind c = 1 ∨ kind c = 2 ∨ kind c = 3 ∨ kind c = 4 := by
  unfold kind; split_ifs <;> simp

lemma kind_eq_zero_iff {c : V} : kind c = 0 ↔ c = 0 := by
  unfold kind; split_ifs with h <;> simp [h]

lemma tag_payload {c : V} (hc : c ≠ 0) : (⟪fstIdx c, sndIdx c⟫ : V) + 1 = c := by
  simp only [fstIdx, sndIdx, pair_unpair]
  exact sub_add_self_of_le (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hc))

lemma eq_tcOmega_of_kind {c : V} (h : kind c = 1) : c = tcOmega (tcOmegaLev c) := by
  have hc : c ≠ 0 := fun e => by simp [e] at h
  have hf : fstIdx c = 0 := by
    unfold kind at h; split_ifs at h with h0 <;> simp_all
  have e := tag_payload hc
  rw [hf] at e
  simpa [tcOmega, tcOmegaLev, tcArg] using e.symm

lemma eq_tcTheta_of_kind {c : V} (h : kind c = 2) : c = tcTheta (tcLev c) (tcThetaArg c) := by
  have hc : c ≠ 0 := fun e => by simp [e] at h
  have hf : fstIdx c = 1 := by
    unfold kind at h; split_ifs at h with h0 h1 <;> simp_all
  have e := tag_payload hc
  rw [hf] at e
  unfold tcTheta tcLev tcThetaArg tcArg
  rw [← pair_unpair (sndIdx c)] at e
  exact e.symm

lemma eq_tcCons_of_kind {c : V} (h : kind c = 3) : c = tcCons (tcHd c) (tcTl c) := by
  have hc : c ≠ 0 := fun e => by simp [e] at h
  have hf : fstIdx c = 2 := by
    unfold kind at h; split_ifs at h with h0 h1 h2 <;> simp_all
  have e := tag_payload hc
  rw [hf, ← pair_unpair (sndIdx c)] at e
  exact e.symm

/-! ### Constituents are smaller -/

lemma lt_tcOmega (i : V) : i < tcOmega i :=
  lt_of_le_of_lt (le_pair_right 0 i) (by simp [tcOmega])

lemma lev_lt_tcTheta (i a : V) : i < tcTheta i a :=
  lt_of_le_of_lt (le_trans (le_pair_left i a) (le_pair_right 1 _)) (by simp [tcTheta])

lemma arg_lt_tcTheta (i a : V) : a < tcTheta i a :=
  lt_of_le_of_lt (le_trans (le_pair_right i a) (le_pair_right 1 _)) (by simp [tcTheta])

lemma hd_lt_tcCons (x s : V) : x < tcCons x s :=
  lt_of_le_of_lt (le_trans (le_pair_left x s) (le_pair_right 2 _)) (by simp [tcCons])

lemma tl_lt_tcCons (x s : V) : s < tcCons x s :=
  lt_of_le_of_lt (le_trans (le_pair_right x s) (le_pair_right 2 _)) (by simp [tcCons])

lemma tcArg_lt {c : V} (hc : c ≠ 0) : tcArg c < c := by
  have h1 : tcArg c ≤ c - 1 := by simp [tcArg, sndIdx]
  exact lt_of_le_of_lt h1 (pred_lt_self_of_pos (pos_iff_ne_zero.mpr hc))

lemma tcLev_lt {c : V} (hc : c ≠ 0) : tcLev c < c :=
  lt_of_le_of_lt (show π₁ (tcArg c) ≤ tcArg c from pi₁_le_self _) (tcArg_lt hc)

lemma tcThetaArg_lt {c : V} (hc : c ≠ 0) : tcThetaArg c < c :=
  lt_of_le_of_lt (show π₂ (tcArg c) ≤ tcArg c from pi₂_le_self _) (tcArg_lt hc)

lemma tcHd_lt {c : V} (hc : c ≠ 0) : tcHd c < c :=
  lt_of_le_of_lt (by simp [tcHd, tcArg]) (tcArg_lt hc)

lemma tcTl_lt {c : V} (hc : c ≠ 0) : tcTl c < c :=
  lt_of_le_of_lt (by simp [tcTl, tcArg]) (tcArg_lt hc)

/-! ### Standard codes -/

@[simp] lemma mc_Omega (k : ℕ) : mc (V := V) (.Omega k) = tcOmega (k : V) := by
  simp [mc, tcOmega, coe_pair_eq_pair_coe]

@[simp] lemma mc_nil : mc (V := V) (.sum []) = 0 := by simp [mc]

@[simp] lemma mc_theta (k : ℕ) (a : ThetaWTerm) :
    mc (V := V) (.theta k a) = tcTheta (k : V) (mc a) := by
  simp [mc, tcTheta, coe_pair_eq_pair_coe]

@[simp] lemma mc_cons (x : ThetaWTerm) (xs : List ThetaWTerm) :
    mc (V := V) (.sum (x :: xs)) = tcCons (mc x) (mc (.sum xs)) := by
  simp [mc, tcCons, coe_pair_eq_pair_coe]

@[simp] lemma mc_inj {a b : ThetaWTerm} : mc (V := V) a = mc b ↔ a = b := by
  simp [mc]

@[simp] lemma mc_nat (t : ThetaWTerm) : mc (V := ℕ) t = code t := by simp [mc]

end Model

/-! ## Recognisers and length

Both generalize ID1's `isTermb`/`ilen` verbatim, with `Omega`'s clause simplified: an `Ω`-code
is *always* well-formed regardless of its level (ID1's `Omega` carries no payload, so it needed
`beq (tcArg c) 0`; here every level is a legitimate payload). -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `1` iff `c` is `0` or a cons code: the shapes of sum codes. -/
noncomputable def sumK (c : V) : V := if kind c = 0 ∨ kind c = 3 then 1 else 0

def sumKDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ k, !kindDef k c ∧ (((k = 0 ∨ k = 3) ∧ y = 1) ∨ (k ≠ 0 ∧ k ≠ 3 ∧ y = 0))”

instance sumK_defined : 𝚺₁-Function₁ (sumK : V → V) via sumKDef := .mk fun v ↦ by
  simp [sumKDef, sumK, kind_defined.iff]
  rcases kind_cases (v 1) with h | h | h | h | h <;> simp [h]

@[simp] lemma sumK_zero : sumK (0 : V) = 1 := by simp [sumK]
@[simp] lemma sumK_tcCons (x s : V) : sumK (tcCons x s) = 1 := by simp [sumK]
@[simp] lemma sumK_tcOmega (i : V) : sumK (tcOmega i) = 0 := by simp [sumK]
@[simp] lemma sumK_tcTheta (i a : V) : sumK (tcTheta i a) = 0 := by simp [sumK]

/-! ### Codes of terms -/

/-- The step of the term recogniser. -/
noncomputable def wfStep (c s : V) : V :=
  if kind c = 0 then 1
  else if kind c = 1 then 1
  else if kind c = 2 then znth s (tcThetaArg c)
  else if kind c = 3 then band (znth s (tcHd c)) (band (znth s (tcTl c)) (sumK (tcTl c)))
  else 0

def wfStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c s. ∃ k, !kindDef k c ∧
    ( (k = 0 ∧ y = 1)
    ∨ (k = 1 ∧ y = 1)
    ∨ (k = 2 ∧ ∃ a, !tcThetaArgDef a c ∧ !znthDef y s a)
    ∨ (k = 3 ∧ ∃ h, !tcHdDef h c ∧ ∃ t, !tcTlDef t c ∧ ∃ r1, !znthDef r1 s h ∧
        ∃ r2, !znthDef r2 s t ∧ ∃ q, !sumKDef q t ∧ ∃ b, !bandDef b r2 q ∧ !bandDef y r1 b)
    ∨ (k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ y = 0) )”

instance wfStep_defined : 𝚺₁-Function₂ (wfStep : V → V → V) via wfStepDef := .mk fun v ↦ by
  simp [wfStepDef, wfStep, kind_defined.iff, tcThetaArg_defined.iff, znth_defined.iff,
    tcHd_defined.iff, tcTl_defined.iff, sumK_defined.iff, band_defined.iff]
  rcases kind_cases (v 1) with h | h | h | h | h <;> simp [h]

/-- The term flag: `1` iff `c` is the code of a term. -/
noncomputable def isTermb (c : V) : V := covVal wfStep wfStepDef c

/-- `c` is the code of a term. -/
def isTerm (c : V) : Prop := isTermb c = 1

def isTermbDef : 𝚺₁.Semisentence 2 := covValDef wfStepDef

instance isTermb_defined : 𝚺₁-Function₁ (isTermb : V → V) via isTermbDef :=
  covVal_defined wfStep wfStepDef

lemma isTermb_unfold (c : V) :
    ∃ S : V, isTermb c = wfStep c S ∧ ∀ k < c, znth S k = isTermb k :=
  covVal_unfold wfStep wfStepDef c

@[simp] lemma isTermb_zero : isTermb (0 : V) = 1 := by
  obtain ⟨S, h, -⟩ := isTermb_unfold (0 : V); simp [h, wfStep]

lemma isTermb_kind_one {c : V} (h1 : kind c = 1) : isTermb c = 1 := by
  obtain ⟨S, h, -⟩ := isTermb_unfold c; simp [h, wfStep, h1]

@[simp] lemma isTermb_tcOmega (i : V) : isTermb (tcOmega i) = 1 := isTermb_kind_one (by simp)

@[simp] lemma isTermb_tcTheta (i a : V) : isTermb (tcTheta i a) = isTermb a := by
  obtain ⟨S, h, hr⟩ := isTermb_unfold (tcTheta i a)
  simp [h, wfStep, hr a (arg_lt_tcTheta i a)]

@[simp] lemma isTermb_tcCons (x s : V) :
    isTermb (tcCons x s) = band (isTermb x) (band (isTermb s) (sumK s)) := by
  obtain ⟨S, h, hr⟩ := isTermb_unfold (tcCons x s)
  simp [h, wfStep, hr x (hd_lt_tcCons x s), hr s (tl_lt_tcCons x s)]

lemma isTermb_kind_four {c : V} (h4 : kind c = 4) : isTermb c = 0 := by
  obtain ⟨S, h, -⟩ := isTermb_unfold c; simp [h, wfStep, h4]

/-- Every standard code is recognised. -/
theorem isTerm_mc : ∀ t : ThetaWTerm, isTerm (mc (V := V) t)
  | .Omega k => by simp [isTerm]
  | .theta k a => by have := isTerm_mc a; simp_all [isTerm]
  | .sum [] => by simp [isTerm]
  | .sum (x :: xs) => by
    have h1 := isTerm_mc x
    have h2 := isTerm_mc (.sum xs)
    unfold isTerm at h1 h2 ⊢
    rw [mc_cons, isTermb_tcCons, h1, h2]
    cases xs <;> simp
termination_by t => l t
decreasing_by all_goals simp; try omega

/-! ### Length -/

/-- The step of the length table. -/
noncomputable def lenStep (c s : V) : V :=
  if kind c = 2 then znth s (tcThetaArg c) + 1
  else if kind c = 3 then znth s (tcHd c) + 1 + znth s (tcTl c)
  else 0

def lenStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c s. ∃ k, !kindDef k c ∧
    ( (k = 2 ∧ ∃ a, !tcThetaArgDef a c ∧ ∃ r, !znthDef r s a ∧ y = r + 1)
    ∨ (k = 3 ∧ ∃ h, !tcHdDef h c ∧ ∃ t, !tcTlDef t c ∧ ∃ r1, !znthDef r1 s h ∧
        ∃ r2, !znthDef r2 s t ∧ y = r1 + 1 + r2)
    ∨ (k ≠ 2 ∧ k ≠ 3 ∧ y = 0) )”

instance lenStep_defined : 𝚺₁-Function₂ (lenStep : V → V → V) via lenStepDef := .mk fun v ↦ by
  simp [lenStepDef, lenStep, kind_defined.iff, tcThetaArg_defined.iff, znth_defined.iff,
    tcHd_defined.iff, tcTl_defined.iff]
  rcases kind_cases (v 1) with h | h | h | h | h <;> simp [h]

/-- **The length** `l` on codes. -/
noncomputable def ilen (c : V) : V := covVal lenStep lenStepDef c

def ilenDef : 𝚺₁.Semisentence 2 := covValDef lenStepDef

instance ilen_defined : 𝚺₁-Function₁ (ilen : V → V) via ilenDef :=
  covVal_defined lenStep lenStepDef

lemma ilen_unfold (c : V) : ∃ S : V, ilen c = lenStep c S ∧ ∀ k < c, znth S k = ilen k :=
  covVal_unfold lenStep lenStepDef c

@[simp] lemma ilen_zero : ilen (0 : V) = 0 := by
  obtain ⟨S, h, -⟩ := ilen_unfold (0 : V); simp [h, lenStep]

@[simp] lemma ilen_tcOmega (i : V) : ilen (tcOmega i) = 0 := by
  obtain ⟨S, h, -⟩ := ilen_unfold (tcOmega i); simp [h, lenStep]

@[simp] lemma ilen_tcTheta (i a : V) : ilen (tcTheta i a) = ilen a + 1 := by
  obtain ⟨S, h, hr⟩ := ilen_unfold (tcTheta i a)
  simp [h, lenStep, hr a (arg_lt_tcTheta i a)]

@[simp] lemma ilen_tcCons (x s : V) : ilen (tcCons x s) = ilen x + 1 + ilen s := by
  obtain ⟨S, h, hr⟩ := ilen_unfold (tcCons x s)
  simp [h, lenStep, hr x (hd_lt_tcCons x s), hr s (tl_lt_tcCons x s)]

/-- The length on standard codes. -/
theorem ilen_mc : ∀ t : ThetaWTerm, ilen (mc (V := V) t) = (l t : V)
  | .Omega k => by simp
  | .theta k a => by simp [ilen_mc a]
  | .sum [] => by simp
  | .sum (x :: xs) => by simp [ilen_mc x, ilen_mc (.sum xs)]
termination_by t => l t
decreasing_by all_goals simp; try omega

end Model

/-! ## Coefficient sets `E_k` and argument sets `G_k`

Both tables carry the level `k` as a *spectator* position coordinate: the recursion only ever
shrinks the inspected code `c`, at the *same* `k` throughout, so `k` (and, for `E_k`/`G_k`
membership, the candidate element `g`/`x`) rides along unchanged in the pair `⟪k, ⟪g, c⟫⟫` while
only the innermost `c` decreases — exactly ID1's `iinE` recursion, with one extra untouched
pairing layer for `k`. No order (`iltb`) is needed for either. -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The step of the `E_k`-membership table at position `⟪lev, ⟪g, c⟫⟫`. -/
noncomputable def inEStep (i s : V) : V :=
  if kind (π₂ (π₂ i)) = 2 then
    if tcLev (π₂ (π₂ i)) ≤ π₁ i then beq (π₁ (π₂ i)) (π₂ (π₂ i))
    else znth s ⟪π₁ i, ⟪π₁ (π₂ i), tcThetaArg (π₂ (π₂ i))⟫⟫
  else if kind (π₂ (π₂ i)) = 3 then
    bor (znth s ⟪π₁ i, ⟪π₁ (π₂ i), tcHd (π₂ (π₂ i))⟫⟫)
      (znth s ⟪π₁ i, ⟪π₁ (π₂ i), tcTl (π₂ (π₂ i))⟫⟫)
  else 0

def inEStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y i s. ∃ lev, !pi₁Def lev i ∧ ∃ gc, !pi₂Def gc i ∧ ∃ g, !pi₁Def g gc ∧ ∃ c, !pi₂Def c gc ∧
    ∃ kd, !kindDef kd c ∧
    ( (kd = 2 ∧ ∃ jl, !tcLevDef jl c ∧
        ( (jl ≤ lev ∧ !beqDef y g c)
        ∨ (lev < jl ∧ ∃ a, !tcThetaArgDef a c ∧ ∃ ga, !pairDef ga g a ∧
            ∃ p, !pairDef p lev ga ∧ !znthDef y s p) ) )
    ∨ (kd = 3 ∧ ∃ h, !tcHdDef h c ∧ ∃ t, !tcTlDef t c ∧
        ∃ gh, !pairDef gh g h ∧ ∃ ph, !pairDef ph lev gh ∧
        ∃ gt, !pairDef gt g t ∧ ∃ pt, !pairDef pt lev gt ∧
        ∃ r1, !znthDef r1 s ph ∧ ∃ r2, !znthDef r2 s pt ∧ !borDef y r1 r2)
    ∨ (kd ≠ 2 ∧ kd ≠ 3 ∧ y = 0) )”

instance inEStep_defined : 𝚺₁-Function₂ (inEStep : V → V → V) via inEStepDef := .mk fun v ↦ by
  simp only [inEStepDef, inEStep]
  rcases kind_cases (π₂ (π₂ (v 1))) with h | h | h | h | h
  · simp [h]
  · simp [h]
  · by_cases hle : tcLev (π₂ (π₂ (v 1))) ≤ π₁ (v 1)
    · have hnlt : ¬ π₁ (v 1) < tcLev (π₂ (π₂ (v 1))) := not_lt.mpr hle
      simp [h, hle, hnlt]
    · have hlt : π₁ (v 1) < tcLev (π₂ (π₂ (v 1))) := not_le.mp hle
      simp [h, hle, hlt]
  · simp [h]
  · simp [h]

/-- **Membership in `E_k`** on codes: `iinE k g c = 1` iff `g` is an element of `E_k(c)`. -/
noncomputable def iinE (k g c : V) : V := covVal inEStep inEStepDef ⟪k, ⟪g, c⟫⟫

def inEValDef : 𝚺₁.Semisentence 2 := covValDef inEStepDef

def iinEDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y k g c. ∃ gc, !pairDef gc g c ∧ ∃ i, !pairDef i k gc ∧ !inEValDef y i”

instance iinE_defined : 𝚺₁-Function₃ (iinE : V → V → V → V) via iinEDef := .mk fun v ↦ by
  simp [iinEDef, iinE, pair_defined.iff, (covVal_defined inEStep inEStepDef).iff, inEValDef]

lemma iinE_unfold (k g c : V) :
    ∃ S : V, iinE k g c = inEStep ⟪k, ⟪g, c⟫⟫ S ∧
      ∀ k' g' c' : V, ⟪k', ⟪g', c'⟫⟫ < ⟪k, ⟪g, c⟫⟫ →
        znth S ⟪k', ⟪g', c'⟫⟫ = iinE k' g' c' := by
  obtain ⟨S, h, hr⟩ := covVal_unfold inEStep inEStepDef (⟪k, ⟪g, c⟫⟫ : V)
  exact ⟨S, h, fun k' g' c' hlt => hr _ hlt⟩

private lemma pos_lt_of_c_lt {k g c c' : V} (h : c' < c) :
    (⟪k, ⟪g, c'⟫⟫ : V) < ⟪k, ⟪g, c⟫⟫ :=
  pair_lt_pair_right k (pair_lt_pair_right g h)

lemma iinE_of_kind (k g : V) {c : V} (hc : kind c = 0 ∨ kind c = 1) : iinE k g c = 0 := by
  obtain ⟨S, h, -⟩ := iinE_unfold k g c
  rw [h, inEStep]
  simp only [pi₁_pair, pi₂_pair]
  rcases hc with hc | hc <;> simp [hc]

lemma iinE_tcTheta_of_le {k j a g : V} (hjk : j ≤ k) :
    iinE k g (tcTheta j a) = beq g (tcTheta j a) := by
  obtain ⟨S, h, -⟩ := iinE_unfold k g (tcTheta j a)
  rw [h, inEStep]
  simp [hjk]

lemma iinE_tcTheta_of_lt {k j a g : V} (hkj : k < j) :
    iinE k g (tcTheta j a) = iinE k g a := by
  obtain ⟨S, h, hr⟩ := iinE_unfold k g (tcTheta j a)
  rw [h, inEStep]
  simp [pi₁_pair, pi₂_pair, kind_tcTheta, tcLev_tcTheta, tcThetaArg_tcTheta]
  rw [if_neg (not_le.mpr hkj)]
  have hpos : (⟪k, ⟪g, a⟫⟫ : V) < ⟪k, ⟪g, tcTheta j a⟫⟫ := pos_lt_of_c_lt (arg_lt_tcTheta j a)
  exact hr k g a hpos

lemma iinE_tcCons (k g x s : V) : iinE k g (tcCons x s) = bor (iinE k g x) (iinE k g s) := by
  obtain ⟨S, h, hr⟩ := iinE_unfold k g (tcCons x s)
  rw [h, inEStep]
  simp [pi₁_pair, pi₂_pair, kind_tcCons, tcHd_tcCons, tcTl_tcCons]
  rw [hr k g x (pos_lt_of_c_lt (hd_lt_tcCons x s)), hr k g s (pos_lt_of_c_lt (tl_lt_tcCons x s))]

/-- Membership in `E_k` on standard codes, for a standard level `kk`. -/
theorem iinE_mc (kk : ℕ) :
    ∀ (x : V) (a : ThetaWTerm), iinE (kk : V) x (mc a) = 1 ↔ ∃ g ∈ E kk a, x = mc g
  | x, .Omega j => by simp [iinE_of_kind]
  | x, .theta j a => by
    by_cases hjk : j ≤ kk
    · rw [mc_theta, iinE_tcTheta_of_le (by exact_mod_cast hjk), beq_eq_one, E_theta_of_le hjk]
      simp [mc_theta]
    · have hkj' : kk < j := not_le.mp hjk
      have hkj : (kk : V) < (j : V) := by exact_mod_cast hkj'
      rw [mc_theta, iinE_tcTheta_of_lt hkj, iinE_mc kk x a, E_theta_of_lt hkj']
  | x, .sum [] => by simp [iinE_of_kind]
  | x, .sum (y :: ys) => by
    rw [mc_cons, iinE_tcCons, bor_eq_one, iinE_mc kk x y, iinE_mc kk x (.sum ys), E_cons]
    simp only [List.mem_append]
    constructor
    · rintro (⟨g, hg, h⟩ | ⟨g, hg, h⟩)
      exacts [⟨g, Or.inl hg, h⟩, ⟨g, Or.inr hg, h⟩]
    · rintro ⟨g, hg | hg, h⟩
      exacts [Or.inl ⟨g, hg, h⟩, Or.inr ⟨g, hg, h⟩]
termination_by _ a => l a
decreasing_by all_goals simp; try omega

theorem iinE_mc_mc (kk : ℕ) (g a : ThetaWTerm) :
    iinE (kk : V) (mc (V := V) g) (mc a) = 1 ↔ g ∈ E kk a := by
  rw [iinE_mc]
  constructor
  · rintro ⟨g', hg', h⟩; rwa [mc_inj.mp h]
  · intro h; exact ⟨g, h, rfl⟩

/-! ### Wilken's argument sets `G_k` -/

/-- The step of the `G_k`-membership table at position `⟪lev, ⟪x, c⟫⟫`. -/
noncomputable def inGStep (i s : V) : V :=
  if kind (π₂ (π₂ i)) = 2 then
    if π₁ i < tcLev (π₂ (π₂ i)) then
      bor (beq (π₁ (π₂ i)) (tcThetaArg (π₂ (π₂ i))))
        (znth s ⟪π₁ i, ⟪π₁ (π₂ i), tcThetaArg (π₂ (π₂ i))⟫⟫)
    else 0
  else if kind (π₂ (π₂ i)) = 3 then
    bor (znth s ⟪π₁ i, ⟪π₁ (π₂ i), tcHd (π₂ (π₂ i))⟫⟫)
      (znth s ⟪π₁ i, ⟪π₁ (π₂ i), tcTl (π₂ (π₂ i))⟫⟫)
  else 0

def inGStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y i s. ∃ lev, !pi₁Def lev i ∧ ∃ xc, !pi₂Def xc i ∧ ∃ x, !pi₁Def x xc ∧ ∃ c, !pi₂Def c xc ∧
    ∃ kd, !kindDef kd c ∧
    ( (kd = 2 ∧ ∃ jl, !tcLevDef jl c ∧
        ( (lev < jl ∧ ∃ a, !tcThetaArgDef a c ∧ ∃ e, !beqDef e x a ∧
            ∃ xa, !pairDef xa x a ∧ ∃ p, !pairDef p lev xa ∧ ∃ r, !znthDef r s p ∧
            !borDef y e r)
        ∨ (jl ≤ lev ∧ y = 0) ) )
    ∨ (kd = 3 ∧ ∃ h, !tcHdDef h c ∧ ∃ t, !tcTlDef t c ∧
        ∃ xh, !pairDef xh x h ∧ ∃ ph, !pairDef ph lev xh ∧
        ∃ xt, !pairDef xt x t ∧ ∃ pt, !pairDef pt lev xt ∧
        ∃ r1, !znthDef r1 s ph ∧ ∃ r2, !znthDef r2 s pt ∧ !borDef y r1 r2)
    ∨ (kd ≠ 2 ∧ kd ≠ 3 ∧ y = 0) )”

instance inGStep_defined : 𝚺₁-Function₂ (inGStep : V → V → V) via inGStepDef := .mk fun v ↦ by
  simp only [inGStepDef, inGStep]
  rcases kind_cases (π₂ (π₂ (v 1))) with h | h | h | h | h
  · simp [h]
  · simp [h]
  · by_cases hlt : π₁ (v 1) < tcLev (π₂ (π₂ (v 1)))
    · have hnle : ¬ tcLev (π₂ (π₂ (v 1))) ≤ π₁ (v 1) := not_le.mpr hlt
      simp [h, hlt, hnle]
    · have hle : tcLev (π₂ (π₂ (v 1))) ≤ π₁ (v 1) := not_lt.mp hlt
      simp [h, hlt, hle]
  · simp [h]
  · simp [h]

/-- **Membership in `G_k`** (Wilken's `K*_{k+1}`) on codes. -/
noncomputable def iinG (k x c : V) : V := covVal inGStep inGStepDef ⟪k, ⟪x, c⟫⟫

def inGValDef : 𝚺₁.Semisentence 2 := covValDef inGStepDef

def iinGDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y k x c. ∃ xc, !pairDef xc x c ∧ ∃ i, !pairDef i k xc ∧ !inGValDef y i”

instance iinG_defined : 𝚺₁-Function₃ (iinG : V → V → V → V) via iinGDef := .mk fun v ↦ by
  simp [iinGDef, iinG, pair_defined.iff, (covVal_defined inGStep inGStepDef).iff, inGValDef]

lemma iinG_unfold (k x c : V) :
    ∃ S : V, iinG k x c = inGStep ⟪k, ⟪x, c⟫⟫ S ∧
      ∀ k' x' c' : V, ⟪k', ⟪x', c'⟫⟫ < ⟪k, ⟪x, c⟫⟫ →
        znth S ⟪k', ⟪x', c'⟫⟫ = iinG k' x' c' := by
  obtain ⟨S, h, hr⟩ := covVal_unfold inGStep inGStepDef (⟪k, ⟪x, c⟫⟫ : V)
  exact ⟨S, h, fun k' x' c' hlt => hr _ hlt⟩

lemma iinG_of_kind (k x : V) {c : V} (hc : kind c = 0 ∨ kind c = 1) : iinG k x c = 0 := by
  obtain ⟨S, h, -⟩ := iinG_unfold k x c
  rw [h, inGStep]
  simp only [pi₁_pair, pi₂_pair]
  rcases hc with hc | hc <;> simp [hc]

lemma iinG_tcTheta_of_lt {k j a x : V} (hkj : k < j) :
    iinG k x (tcTheta j a) = bor (beq x a) (iinG k x a) := by
  obtain ⟨S, h, hr⟩ := iinG_unfold k x (tcTheta j a)
  rw [h, inGStep]
  simp [pi₁_pair, pi₂_pair, kind_tcTheta, tcLev_tcTheta, tcThetaArg_tcTheta]
  rw [if_pos hkj]
  have hpos : (⟪k, ⟪x, a⟫⟫ : V) < ⟪k, ⟪x, tcTheta j a⟫⟫ :=
    pair_lt_pair_right k (pair_lt_pair_right x (arg_lt_tcTheta j a))
  rw [hr k x a hpos]

lemma iinG_tcTheta_of_le {k j a x : V} (hjk : j ≤ k) : iinG k x (tcTheta j a) = 0 := by
  obtain ⟨S, h, -⟩ := iinG_unfold k x (tcTheta j a)
  rw [h, inGStep]
  simp [pi₁_pair, pi₂_pair, kind_tcTheta, tcLev_tcTheta]
  exact fun hkj => absurd hjk (not_le.mpr hkj)

lemma iinG_tcCons (k x y s : V) : iinG k x (tcCons y s) = bor (iinG k x y) (iinG k x s) := by
  obtain ⟨S, h, hr⟩ := iinG_unfold k x (tcCons y s)
  rw [h, inGStep]
  simp [pi₁_pair, pi₂_pair, kind_tcCons, tcHd_tcCons, tcTl_tcCons]
  rw [hr k x y (pos_lt_of_c_lt (hd_lt_tcCons y s)), hr k x s (pos_lt_of_c_lt (tl_lt_tcCons y s))]

/-- Membership in `G_k` on standard codes, for a standard level `kk`. -/
theorem iinG_mc (kk : ℕ) :
    ∀ (x : V) (a : ThetaWTerm), iinG (kk : V) x (mc a) = 1 ↔ ∃ g ∈ G kk a, x = mc g
  | x, .Omega j => by simp [iinG_of_kind]
  | x, .theta j a => by
    by_cases hjk : j ≤ kk
    · rw [mc_theta, iinG_tcTheta_of_le (by exact_mod_cast hjk), G_theta_of_le hjk]; simp
    · have hkj' : kk < j := not_le.mp hjk
      have hkj : (kk : V) < (j : V) := by exact_mod_cast hkj'
      rw [mc_theta, iinG_tcTheta_of_lt hkj, bor_eq_one, beq_eq_one,
        G_theta_of_lt hkj', iinG_mc kk x a]
      simp only [List.mem_cons]
      constructor
      · rintro (rfl | ⟨g, hg, h⟩)
        · exact ⟨a, Or.inl rfl, rfl⟩
        · exact ⟨g, Or.inr hg, h⟩
      · rintro ⟨g, hg | hg, h⟩
        · exact Or.inl (by rw [h, hg])
        · exact Or.inr ⟨g, hg, h⟩
  | x, .sum [] => by simp [iinG_of_kind]
  | x, .sum (y :: ys) => by
    rw [mc_cons, iinG_tcCons, bor_eq_one, iinG_mc kk x y, iinG_mc kk x (.sum ys), G_cons]
    simp only [List.mem_append]
    constructor
    · rintro (⟨g, hg, h⟩ | ⟨g, hg, h⟩)
      exacts [⟨g, Or.inl hg, h⟩, ⟨g, Or.inr hg, h⟩]
    · rintro ⟨g, hg | hg, h⟩
      exacts [Or.inl ⟨g, hg, h⟩, Or.inr ⟨g, hg, h⟩]
termination_by _ a => l a
decreasing_by all_goals simp; try omega

theorem iinG_mc_mc (kk : ℕ) (x a : ThetaWTerm) :
    iinG (kk : V) (mc (V := V) x) (mc a) = 1 ↔ x ∈ G kk a := by
  rw [iinG_mc]
  constructor
  · rintro ⟨g', hg', h⟩; rwa [mc_inj.mp h]
  · intro h; exact ⟨x, h, rfl⟩

end Model

/-! ## The arithmetic formulas

Each order-free predicate of the coding as a `Σ₁` formula of `ℒₒᵣ`, mirroring ID1's `thTermDef`/
`thLenDef`/`thInEDef`. `thPrecDef`/`thNFDef`-style order-dependent formulas are not built here
(see the module docstring). -/

/-- `x` is the code of a term. -/
def thTermDef : 𝚺₁.Semisentence 1 := .mkSigma “x. !isTermbDef 1 x”

/-- `y` is the length of (the term coded by) `x`. -/
def thLenDef : 𝚺₁.Semisentence 2 := .mkSigma “y x. !ilenDef y x”

/-- `g` is an element of `E_k(a)`. -/
def thInEDef : 𝚺₁.Semisentence 3 := .mkSigma “k g a. !iinEDef 1 k g a”

/-- `x` is an element of `G_k(a)` (Wilken's `K*_{k+1}`). -/
def thGDef : 𝚺₁.Semisentence 3 := .mkSigma “k x a. !iinGDef 1 k x a”

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem eval_thTermDef (x : V) : thTermDef.val.Evalb ![x] ↔ isTerm x := by
  simp [thTermDef, isTerm, isTermb_defined.iff, eq_comm]

@[simp] theorem eval_thLenDef (y x : V) : thLenDef.val.Evalb ![y, x] ↔ y = ilen x := by
  simp [thLenDef, ilen_defined.iff]

@[simp] theorem eval_thInEDef (k g a : V) : thInEDef.val.Evalb ![k, g, a] ↔ iinE k g a = 1 := by
  simp [thInEDef, iinE_defined.iff, eq_comm]

@[simp] theorem eval_thGDef (k x a : V) : thGDef.val.Evalb ![k, x, a] ↔ iinG k x a = 1 := by
  simp [thGDef, iinG_defined.iff, eq_comm]

/-! ### The formulas on standard codes, in every model of `IΣ₁` -/

theorem eval_thTermDef_mc (t : ThetaWTerm) : thTermDef.val.Evalb ![mc (V := V) t] := by
  simpa using isTerm_mc (V := V) t

theorem eval_thLenDef_mc (t : ThetaWTerm) :
    thLenDef.val.Evalb ![(l t : V), mc (V := V) t] := by
  simp [ilen_mc]

theorem eval_thInEDef_mc (kk : ℕ) (g a : ThetaWTerm) :
    thInEDef.val.Evalb ![(kk : V), mc (V := V) g, mc a] ↔ g ∈ E kk a := by
  simpa using iinE_mc_mc (V := V) kk g a

theorem eval_thGDef_mc (kk : ℕ) (x a : ThetaWTerm) :
    thGDef.val.Evalb ![(kk : V), mc (V := V) x, mc a] ↔ x ∈ G kk a := by
  simpa using iinG_mc_mc (V := V) kk x a

end Model

/-! ## Definability at every level

A total function with a `Σ₁` graph is `Δ₁`-definable in models of `IΣ₁`; these instances make the
functions and predicates of the coding available at every level of the arithmetical hierarchy,
mirroring ID1's closing section. -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance tcOmega_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (tcOmega : V → V) :=
  tcOmega_definable.of_sigmaOne
instance tcTheta_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (tcTheta : V → V → V) :=
  tcTheta_definable.of_sigmaOne
instance tcCons_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (tcCons : V → V → V) :=
  tcCons_definable.of_sigmaOne

instance isTermb_definable : 𝚺₁-Function₁ (isTermb : V → V) := isTermb_defined.to_definable
instance isTermb_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (isTermb : V → V) :=
  isTermb_definable.of_sigmaOne
instance ilen_definable : 𝚺₁-Function₁ (ilen : V → V) := ilen_defined.to_definable
instance ilen_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (ilen : V → V) :=
  ilen_definable.of_sigmaOne
instance iinE_definable : 𝚺₁-Function₃ (iinE : V → V → V → V) := iinE_defined.to_definable
instance iinE_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₃ (iinE : V → V → V → V) :=
  iinE_definable.of_sigmaOne
instance iinG_definable : 𝚺₁-Function₃ (iinG : V → V → V → V) := iinG_defined.to_definable
instance iinG_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₃ (iinG : V → V → V → V) :=
  iinG_definable.of_sigmaOne

instance isTerm_definable (Γ) (m : ℕ) : Γ-[m + 1]-Predicate (isTerm : V → Prop) := by
  unfold isTerm; definability

end Model

end OrdinalAnalysis.IDn.Internal
