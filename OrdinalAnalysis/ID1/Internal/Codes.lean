/-
  Arithmetic coding of the ϑ-notation.

  **Codes.**  A term is coded by a natural number:

  * `⟨⟩` (the term `0`) by `0`,
  * `Ω` by `1 = ⟪0, 0⟫ + 1`,
  * `ϑ α` by `⟪1, ⌜α⌝⟫ + 1`,
  * `⟨α₀, α₁, …⟩` by `⟪2, ⟪⌜α₀⌝, ⌜⟨α₁, …⟩⌝⟫⟫ + 1`.

  So a nonempty sum is a cons cell whose tail is again the code of a sum, and every immediate
  constituent of a positive code `c` is strictly below `c`.  The first component of `c - 1` is
  the *tag* of `c`; `kind c` records the shape: `0` for the empty sum, `1`, `2`, `3` for the
  tags of `Ω`, `ϑ` and cons cells, and `4` for any other tag.

  **The coding inside a model `V` of `IΣ₁`.**  The definitions of `ThetaTerm` are the
  specification; each is a course-of-values table (`CovTable`) with a `Σ₁` graph:

  * `iltb`, the order `ltb` (together with the two `E`-quantifier flags `iall`, `iex` that its
    `ϑ`-`ϑ` clause needs), over pair positions;
  * `isTermb` and `isNFb`, the recognisers of codes of terms and of normal forms;
  * `ilen`, the length `l`; `iinE`, membership in `E`, over pair positions;
  * `icmp`, the three-way comparison.

  On standard codes `mc t = (code t : V)` each of them computes its specification, in every
  model (`iltb_mc`, `isNF_mc`, `ilen_mc`, `iinE_mc_mc`, `icmp_mc_eq_zero_iff`, …).  The
  predicates are finally collected as `Σ₁` formulas of `ℒₒᵣ` (`thTermDef`, `thNFDef`,
  `thLenDef`, `thInEDef`, `thLtDef`, `thCmpDef`, `thPrecDef`, `thFieldDef`,
  `thPrecFieldDef`), with their evaluation lemmas.  Only the recursion equations and their
  agreement with the specification on standard codes are proved here; the order-theoretic
  facts about the internal order in arbitrary models are not.
-/
import OrdinalAnalysis.ID1.Internal.CovTable
import OrdinalAnalysis.Ordinal.Theta.Order

set_option autoImplicit false

namespace OrdinalAnalysis.ID1.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.ThetaTerm

/-! ## Codes of terms, in `ℕ` -/

mutual
/-- The Gödel code of a term. -/
def code : ThetaTerm → ℕ
  | .Omega => 1
  | .theta a => Nat.pair 1 (code a) + 1
  | .sum xs => codeList xs
/-- The code of the sum of a list of terms. -/
def codeList : List ThetaTerm → ℕ
  | [] => 0
  | x :: xs => Nat.pair 2 (Nat.pair (code x) (codeList xs)) + 1
end

@[simp] theorem code_Omega : code .Omega = 1 := by simp [code]

@[simp] theorem code_theta (a : ThetaTerm) : code (.theta a) = Nat.pair 1 (code a) + 1 := by
  simp [code]

@[simp] theorem code_nil : code (.sum []) = 0 := by simp [code, codeList]

@[simp] theorem code_cons (x : ThetaTerm) (xs : List ThetaTerm) :
    code (.sum (x :: xs)) = Nat.pair 2 (Nat.pair (code x) (code (.sum xs))) + 1 := by
  simp [code, codeList]

/-- The entries of a term read as a sum; `[]` for `Ω` and `ϑ α`. -/
def sumArgs : ThetaTerm → List ThetaTerm
  | .sum xs => xs
  | _ => []

@[simp] theorem sumArgs_sum (xs : List ThetaTerm) : sumArgs (.sum xs) = xs := rfl

/-- Decoding: the inverse of `code` on codes, and some term elsewhere. -/
def decode (n : ℕ) : ThetaTerm :=
  match n with
  | 0 => .sum []
  | k + 1 =>
    if (Nat.unpair k).1 = 1 then .theta (decode (Nat.unpair k).2)
    else if (Nat.unpair k).1 = 2 then
      .sum (decode (Nat.unpair (Nat.unpair k).2).1 ::
        sumArgs (decode (Nat.unpair (Nat.unpair k).2).2))
    else .Omega
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
      if (Nat.unpair k).1 = 1 then .theta (decode (Nat.unpair k).2)
      else if (Nat.unpair k).1 = 2 then
        .sum (decode (Nat.unpair (Nat.unpair k).2).1 ::
          sumArgs (decode (Nat.unpair (Nat.unpair k).2).2))
      else .Omega := by
  rw [decode]

/-- **Decoding inverts coding.** -/
theorem decode_code : ∀ t : ThetaTerm, decode (code t) = t
  | .Omega => by
    rw [code_Omega, show (1 : ℕ) = 0 + 1 from rfl, decode_succ]; simp
  | .theta a => by
    rw [code_theta, decode_succ]; simp [decode_code a]
  | .sum [] => by rw [code_nil, decode_zero]
  | .sum (x :: xs) => by
    rw [code_cons, decode_succ]; simp [decode_code x, decode_code (.sum xs)]
termination_by t => l t
decreasing_by all_goals simp; try omega

theorem code_injective : Function.Injective code :=
  Function.LeftInverse.injective decode_code

@[simp] theorem code_inj {a b : ThetaTerm} : code a = code b ↔ a = b :=
  code_injective.eq_iff

/-- The code of a notation. -/
def codeNote (a : ThetaNote) : ℕ := code a.1

theorem codeNote_injective : Function.Injective codeNote := fun _ _ h =>
  Subtype.ext (code_injective h)


/-! ## Codes inside a model of `IΣ₁` -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The code of `ϑ α` from the code `a` of `α`. -/
noncomputable def tcTheta (a : V) : V := ⟪1, a⟫ + 1

/-- The code of the sum with first entry coded by `x` and remaining sum coded by `s`. -/
noncomputable def tcCons (x s : V) : V := ⟪2, ⟪x, s⟫⟫ + 1

/-- The argument of a `ϑ`-code. -/
noncomputable def tcArg (c : V) : V := sndIdx c

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
def mc (t : ThetaTerm) : V := (code t : V)

def tcThetaDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y a. ∃ p, !pairDef p 1 a ∧ y = p + 1”

def tcConsDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y x s. ∃ q, !pairDef q x s ∧ ∃ p, !pairDef p 2 q ∧ y = p + 1”

def tcHdDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y c. ∃ p <⁺ c, !sndIdxDef p c ∧ !pi₁Def y p”

def tcTlDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y c. ∃ p <⁺ c, !sndIdxDef p c ∧ !pi₂Def y p”

def kindDef : 𝚺₀.Semisentence 2 := .mkSigma
  “k c. (c = 0 ∧ k = 0) ∨
    (c ≠ 0 ∧ ∃ f <⁺ c, !fstIdxDef f c ∧
      ((f = 0 ∧ k = 1) ∨ (f = 1 ∧ k = 2) ∨ (f = 2 ∧ k = 3) ∨ (f ≠ 0 ∧ f ≠ 1 ∧ f ≠ 2 ∧ k = 4)))”

instance tcTheta_defined : 𝚺₁-Function₁ (tcTheta : V → V) via tcThetaDef := .mk fun v ↦ by
  simp [tcThetaDef, tcTheta, pair_defined.iff]

instance tcCons_defined : 𝚺₁-Function₂ (tcCons : V → V → V) via tcConsDef := .mk fun v ↦ by
  simp [tcConsDef, tcCons, pair_defined.iff]

instance tcArg_defined : 𝚺₀-Function₁ (tcArg : V → V) via sndIdxDef := .mk fun v ↦ by
  simp [tcArg, sndIdx_defined.iff]

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

instance tcTheta_definable : 𝚺₁-Function₁ (tcTheta : V → V) := tcTheta_defined.to_definable
instance tcCons_definable : 𝚺₁-Function₂ (tcCons : V → V → V) := tcCons_defined.to_definable
instance tcArg_definable : 𝚺₀-Function₁ (tcArg : V → V) := tcArg_defined.to_definable
instance tcHd_definable : 𝚺₀-Function₁ (tcHd : V → V) := tcHd_defined.to_definable
instance tcTl_definable : 𝚺₀-Function₁ (tcTl : V → V) := tcTl_defined.to_definable
instance kind_definable : 𝚺₀-Function₁ (kind : V → V) := kind_defined.to_definable
instance tcArg_definable' (Γ) : Γ-Function₁ (tcArg : V → V) := tcArg_definable.of_zero
instance tcHd_definable' (Γ) : Γ-Function₁ (tcHd : V → V) := tcHd_definable.of_zero
instance tcTl_definable' (Γ) : Γ-Function₁ (tcTl : V → V) := tcTl_definable.of_zero
instance kind_definable' (Γ) : Γ-Function₁ (kind : V → V) := kind_definable.of_zero

/-! ### Destructors and shapes of constructor codes -/

@[simp] lemma tcTheta_ne_zero (a : V) : tcTheta a ≠ 0 := by simp [tcTheta]

@[simp] lemma tcCons_ne_zero (x s : V) : tcCons x s ≠ 0 := by simp [tcCons]

@[simp] lemma tcArg_tcTheta (a : V) : tcArg (tcTheta a) = a := by simp [tcArg, tcTheta, sndIdx]

@[simp] lemma tcHd_tcCons (x s : V) : tcHd (tcCons x s) = x := by simp [tcHd, tcCons, sndIdx]

@[simp] lemma tcTl_tcCons (x s : V) : tcTl (tcCons x s) = s := by simp [tcTl, tcCons, sndIdx]

@[simp] lemma kind_zero : kind (0 : V) = 0 := by simp [kind]

@[simp] lemma kind_one : kind (1 : V) = 1 := by simp [kind, fstIdx, pi₁_zero]

@[simp] lemma kind_tcTheta (a : V) : kind (tcTheta a) = 2 := by
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

lemma eq_tcTheta_of_kind {c : V} (h : kind c = 2) : c = tcTheta (tcArg c) := by
  have hc : c ≠ 0 := fun e => by simp [e] at h
  have hf : fstIdx c = 1 := by
    unfold kind at h; split_ifs at h with h0 h1 h2 <;> simp_all
  have e := tag_payload hc
  rw [hf] at e
  exact e.symm

lemma eq_tcCons_of_kind {c : V} (h : kind c = 3) : c = tcCons (tcHd c) (tcTl c) := by
  have hc : c ≠ 0 := fun e => by simp [e] at h
  have hf : fstIdx c = 2 := by
    unfold kind at h; split_ifs at h with h0 h1 h2 h3 <;> simp_all
  have e := tag_payload hc
  rw [hf, ← pair_unpair (sndIdx c)] at e
  exact e.symm

lemma eq_one_of_kind {c : V} (h : kind c = 1) (h' : tcArg c = 0) : c = 1 := by
  have hc : c ≠ 0 := fun e => by simp [e] at h
  have hf : fstIdx c = 0 := by
    unfold kind at h; split_ifs at h with h0 h1 <;> simp_all
  have h'' : sndIdx c = 0 := h'
  have e := tag_payload hc
  rw [hf, h'', pair_zero_zero, zero_add] at e
  exact e.symm

/-! ### Constituents are smaller -/

lemma lt_tcTheta (a : V) : a < tcTheta a :=
  lt_of_le_of_lt (le_pair_right 1 a) (by simp [tcTheta])

lemma hd_lt_tcCons (x s : V) : x < tcCons x s :=
  lt_of_le_of_lt (le_trans (le_pair_left x s) (le_pair_right 2 _)) (by simp [tcCons])

lemma tl_lt_tcCons (x s : V) : s < tcCons x s :=
  lt_of_le_of_lt (le_trans (le_pair_right x s) (le_pair_right 2 _)) (by simp [tcCons])

lemma tcArg_lt {c : V} (hc : c ≠ 0) : tcArg c < c := by
  have h1 : tcArg c ≤ c - 1 := by simp [tcArg, sndIdx]
  exact lt_of_le_of_lt h1 (pred_lt_self_of_pos (pos_iff_ne_zero.mpr hc))

lemma tcHd_lt {c : V} (hc : c ≠ 0) : tcHd c < c :=
  lt_of_le_of_lt (by simp [tcHd, tcArg]) (tcArg_lt hc)

lemma tcTl_lt {c : V} (hc : c ≠ 0) : tcTl c < c :=
  lt_of_le_of_lt (by simp [tcTl, tcArg]) (tcArg_lt hc)

/-! ### Standard codes -/

@[simp] lemma mc_Omega : mc (V := V) .Omega = 1 := by simp [mc]

@[simp] lemma mc_nil : mc (V := V) (.sum []) = 0 := by simp [mc]

@[simp] lemma mc_theta (a : ThetaTerm) : mc (V := V) (.theta a) = tcTheta (mc a) := by
  simp [mc, tcTheta, coe_pair_eq_pair_coe]

@[simp] lemma mc_cons (x : ThetaTerm) (xs : List ThetaTerm) :
    mc (V := V) (.sum (x :: xs)) = tcCons (mc x) (mc (.sum xs)) := by
  simp [mc, tcCons, coe_pair_eq_pair_coe]

@[simp] lemma mc_inj {a b : ThetaTerm} : mc (V := V) a = mc b ↔ a = b := by
  simp [mc]

@[simp] lemma mc_nat (t : ThetaTerm) : mc (V := ℕ) t = code t := by simp [mc]

end Model

/-! ## The comparison table

One course-of-values table over pair positions `⟪c₁, c₂⟫` carries three `0/1` flags,
packed as `⟪lt, ⟪all, ex⟫⟫`:

* `lt`: the order `c₁ ≺ c₂` of `ltb`;
* `all`: every element of `E(c₁)` is `≺ c₂`;
* `ex`: `c₁ ≼ γ` for some element `γ` of `E(c₂)`.

The `ϑ`-`ϑ` clause of the order reads `lt` at `⟪a, b⟫`, `all` at `⟪a, ϑ b⟫` and `ex` at
`⟪ϑ a, b⟫`; the two quantifier flags recurse on the entries of a sum, and at a `ϑ`-code they
are the `lt` flag of the same position, which the step computes first.  Every other read is at
a strictly smaller position. -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The `lt` flag stored in a table `s` at `⟪x, y⟫`. -/
noncomputable def rdLt (s x y : V) : V := π₁ (znth s ⟪x, y⟫)

/-- The `all` flag stored in a table `s` at `⟪x, y⟫`. -/
noncomputable def rdAl (s x y : V) : V := π₁ (π₂ (znth s ⟪x, y⟫))

/-- The `ex` flag stored in a table `s` at `⟪x, y⟫`. -/
noncomputable def rdEx (s x y : V) : V := π₂ (π₂ (znth s ⟪x, y⟫))

def rdLtDef : 𝚺₁.Semisentence 4 := .mkSigma
  “r s x y. ∃ i, !pairDef i x y ∧ ∃ e, !znthDef e s i ∧ !pi₁Def r e”

def rdAlDef : 𝚺₁.Semisentence 4 := .mkSigma
  “r s x y. ∃ i, !pairDef i x y ∧ ∃ e, !znthDef e s i ∧ ∃ q, !pi₂Def q e ∧ !pi₁Def r q”

def rdExDef : 𝚺₁.Semisentence 4 := .mkSigma
  “r s x y. ∃ i, !pairDef i x y ∧ ∃ e, !znthDef e s i ∧ ∃ q, !pi₂Def q e ∧ !pi₂Def r q”

instance rdLt_defined : 𝚺₁-Function₃ (rdLt : V → V → V → V) via rdLtDef := .mk fun v ↦ by
  simp [rdLtDef, rdLt, pair_defined.iff, znth_defined.iff, pi₁_defined.iff]

instance rdAl_defined : 𝚺₁-Function₃ (rdAl : V → V → V → V) via rdAlDef := .mk fun v ↦ by
  simp [rdAlDef, rdAl, pair_defined.iff, znth_defined.iff, pi₁_defined.iff, pi₂_defined.iff]

instance rdEx_defined : 𝚺₁-Function₃ (rdEx : V → V → V → V) via rdExDef := .mk fun v ↦ by
  simp [rdExDef, rdEx, pair_defined.iff, znth_defined.iff, pi₂_defined.iff]

/-- The `lt` flag at two cons codes: lexicographic comparison. -/
noncomputable def ltCC (c1 c2 s : V) : V :=
  bor (rdLt s (tcHd c1) (tcHd c2)) (band (beq (tcHd c1) (tcHd c2)) (rdLt s (tcTl c1) (tcTl c2)))

/-- The `lt` flag at a cons code against a principal code: compare the first entry. -/
noncomputable def ltCP (c1 c2 s : V) : V := rdLt s (tcHd c1) c2

/-- The `lt` flag at a principal code against a cons code: `≼` the first entry. -/
noncomputable def ltPC (c1 c2 s : V) : V := bor (rdLt s c1 (tcHd c2)) (beq c1 (tcHd c2))

/-- The `lt` flag at two `ϑ`-codes. -/
noncomputable def ltTT (c1 c2 s : V) : V :=
  bor (band (rdLt s (tcArg c1) (tcArg c2)) (rdAl s (tcArg c1) c2)) (rdEx s c1 (tcArg c2))

def ltCCDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y c1 c2 s. ∃ h1, !tcHdDef h1 c1 ∧ ∃ h2, !tcHdDef h2 c2 ∧ ∃ t1, !tcTlDef t1 c1 ∧
    ∃ t2, !tcTlDef t2 c2 ∧ ∃ r1, !rdLtDef r1 s h1 h2 ∧ ∃ r2, !rdLtDef r2 s t1 t2 ∧
    ∃ e, !beqDef e h1 h2 ∧ ∃ a, !bandDef a e r2 ∧ !borDef y r1 a”

def ltCPDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y c1 c2 s. ∃ h1, !tcHdDef h1 c1 ∧ !rdLtDef y s h1 c2”

def ltPCDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y c1 c2 s. ∃ h2, !tcHdDef h2 c2 ∧ ∃ r, !rdLtDef r s c1 h2 ∧ ∃ e, !beqDef e c1 h2 ∧
    !borDef y r e”

def ltTTDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y c1 c2 s. ∃ a1, !sndIdxDef a1 c1 ∧ ∃ a2, !sndIdxDef a2 c2 ∧ ∃ r1, !rdLtDef r1 s a1 a2 ∧
    ∃ r2, !rdAlDef r2 s a1 c2 ∧ ∃ r3, !rdExDef r3 s c1 a2 ∧ ∃ a, !bandDef a r1 r2 ∧
    !borDef y a r3”

instance ltCC_defined : 𝚺₁-Function₃ (ltCC : V → V → V → V) via ltCCDef := .mk fun v ↦ by
  simp [ltCCDef, ltCC, tcHd_defined.iff, tcTl_defined.iff, rdLt_defined.iff,
    beq_defined.iff, band_defined.iff, bor_defined.iff]

instance ltCP_defined : 𝚺₁-Function₃ (ltCP : V → V → V → V) via ltCPDef := .mk fun v ↦ by
  simp [ltCPDef, ltCP, tcHd_defined.iff, rdLt_defined.iff]

instance ltPC_defined : 𝚺₁-Function₃ (ltPC : V → V → V → V) via ltPCDef := .mk fun v ↦ by
  simp [ltPCDef, ltPC, tcHd_defined.iff, rdLt_defined.iff, beq_defined.iff, bor_defined.iff]

instance ltTT_defined : 𝚺₁-Function₃ (ltTT : V → V → V → V) via ltTTDef := .mk fun v ↦ by
  simp [ltTTDef, ltTT, tcArg, sndIdx_defined.iff, rdLt_defined.iff, rdAl_defined.iff,
    rdEx_defined.iff, band_defined.iff, bor_defined.iff]

/-- The `lt` flag at `⟪c1, c2⟫`, by cases on the shapes of the two codes. -/
noncomputable def ltStep (c1 c2 s : V) : V :=
  if kind c1 = 0 then (if kind c2 = 0 then 0 else 1)
  else if kind c2 = 0 then 0
  else if kind c1 = 3 then (if kind c2 = 3 then ltCC c1 c2 s else ltCP c1 c2 s)
  else if kind c2 = 3 then ltPC c1 c2 s
  else if kind c1 = 2 then (if kind c2 = 2 then ltTT c1 c2 s else 1)
  else 0

def ltStepDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y c1 c2 s. ∃ k1, !kindDef k1 c1 ∧ ∃ k2, !kindDef k2 c2 ∧
    ( (k1 = 0 ∧ k2 = 0 ∧ y = 0)
    ∨ (k1 = 0 ∧ k2 ≠ 0 ∧ y = 1)
    ∨ (k1 ≠ 0 ∧ k2 = 0 ∧ y = 0)
    ∨ (k1 = 3 ∧ k2 = 3 ∧ !ltCCDef y c1 c2 s)
    ∨ (k1 = 3 ∧ k2 ≠ 0 ∧ k2 ≠ 3 ∧ !ltCPDef y c1 c2 s)
    ∨ (k1 ≠ 0 ∧ k1 ≠ 3 ∧ k2 = 3 ∧ !ltPCDef y c1 c2 s)
    ∨ (k1 = 2 ∧ k2 = 2 ∧ !ltTTDef y c1 c2 s)
    ∨ (k1 = 2 ∧ k2 ≠ 0 ∧ k2 ≠ 3 ∧ k2 ≠ 2 ∧ y = 1)
    ∨ (k1 ≠ 0 ∧ k1 ≠ 3 ∧ k1 ≠ 2 ∧ k2 ≠ 0 ∧ k2 ≠ 3 ∧ y = 0) )”

instance ltStep_defined : 𝚺₁-Function₃ (ltStep : V → V → V → V) via ltStepDef := .mk fun v ↦ by
  simp [ltStepDef, ltStep, kind_defined.iff, ltCC_defined.iff, ltCP_defined.iff,
    ltPC_defined.iff, ltTT_defined.iff]
  rcases kind_cases (v 1) with h1 | h1 | h1 | h1 | h1 <;>
    rcases kind_cases (v 2) with h2 | h2 | h2 | h2 | h2 <;> simp [h1, h2]

/-- The `all` flag at `⟪c1, c2⟫`, given the `lt` flag `l` at the same position. -/
noncomputable def alStep (c1 c2 s l : V) : V :=
  if kind c1 = 2 then l
  else if kind c1 = 3 then band (rdAl s (tcHd c1) c2) (rdAl s (tcTl c1) c2)
  else 1

/-- The `ex` flag at `⟪c1, c2⟫`, given the `lt` flag `l` at the same position. -/
noncomputable def exStep (c1 c2 s l : V) : V :=
  if kind c2 = 2 then bor l (beq c1 c2)
  else if kind c2 = 3 then bor (rdEx s c1 (tcHd c2)) (rdEx s c1 (tcTl c2))
  else 0

def alStepDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y c1 c2 s l. ∃ k1, !kindDef k1 c1 ∧
    ( (k1 = 2 ∧ y = l)
    ∨ (k1 = 3 ∧ ∃ h, !tcHdDef h c1 ∧ ∃ t, !tcTlDef t c1 ∧ ∃ r1, !rdAlDef r1 s h c2 ∧
        ∃ r2, !rdAlDef r2 s t c2 ∧ !bandDef y r1 r2)
    ∨ (k1 ≠ 2 ∧ k1 ≠ 3 ∧ y = 1) )”

def exStepDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y c1 c2 s l. ∃ k2, !kindDef k2 c2 ∧
    ( (k2 = 2 ∧ ∃ e, !beqDef e c1 c2 ∧ !borDef y l e)
    ∨ (k2 = 3 ∧ ∃ h, !tcHdDef h c2 ∧ ∃ t, !tcTlDef t c2 ∧ ∃ r1, !rdExDef r1 s c1 h ∧
        ∃ r2, !rdExDef r2 s c1 t ∧ !borDef y r1 r2)
    ∨ (k2 ≠ 2 ∧ k2 ≠ 3 ∧ y = 0) )”

instance alStep_defined : 𝚺₁-Function₄ (alStep : V → V → V → V → V) via alStepDef :=
  .mk fun v ↦ by
  simp [alStepDef, alStep, kind_defined.iff, tcHd_defined.iff, tcTl_defined.iff,
    rdAl_defined.iff, band_defined.iff]
  rcases kind_cases (v 1) with h1 | h1 | h1 | h1 | h1 <;> simp [h1]

instance exStep_defined : 𝚺₁-Function₄ (exStep : V → V → V → V → V) via exStepDef :=
  .mk fun v ↦ by
  simp [exStepDef, exStep, kind_defined.iff, tcHd_defined.iff, tcTl_defined.iff,
    rdEx_defined.iff, bor_defined.iff, beq_defined.iff]
  rcases kind_cases (v 2) with h2 | h2 | h2 | h2 | h2 <;> simp [h2]

/-- The step of the comparison table at position `i = ⟪c1, c2⟫`. -/
noncomputable def cmpStep (i s : V) : V :=
  ⟪ltStep (π₁ i) (π₂ i) s,
    ⟪alStep (π₁ i) (π₂ i) s (ltStep (π₁ i) (π₂ i) s),
      exStep (π₁ i) (π₂ i) s (ltStep (π₁ i) (π₂ i) s)⟫⟫

def cmpStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y i s. ∃ c1, !pi₁Def c1 i ∧ ∃ c2, !pi₂Def c2 i ∧ ∃ l, !ltStepDef l c1 c2 s ∧
    ∃ a, !alStepDef a c1 c2 s l ∧ ∃ x, !exStepDef x c1 c2 s l ∧ ∃ p, !pairDef p a x ∧
    !pairDef y l p”

instance cmpStep_defined : 𝚺₁-Function₂ (cmpStep : V → V → V) via cmpStepDef := .mk fun v ↦ by
  simp [cmpStepDef, cmpStep, pi₁_defined.iff, pi₂_defined.iff, ltStep_defined.iff,
    alStep_defined.iff, exStep_defined.iff, pair_defined.iff]

/-- The entry of the comparison table at position `m`. -/
noncomputable def cmpVal (m : V) : V := covVal cmpStep cmpStepDef m

/-- **The internal order** as a `0/1` flag: `iltb c1 c2 = 1` iff `c1 ≺ c2`. -/
noncomputable def iltb (c1 c2 : V) : V := π₁ (cmpVal ⟪c1, c2⟫)

/-- `iall c1 c2 = 1` iff every element of `E(c1)` is `≺ c2`. -/
noncomputable def iall (c1 c2 : V) : V := π₁ (π₂ (cmpVal ⟪c1, c2⟫))

/-- `iex c1 c2 = 1` iff `c1 ≼ γ` for some element `γ` of `E(c2)`. -/
noncomputable def iex (c1 c2 : V) : V := π₂ (π₂ (cmpVal ⟪c1, c2⟫))

def cmpValDef : 𝚺₁.Semisentence 2 := covValDef cmpStepDef

instance cmpVal_defined : 𝚺₁-Function₁ (cmpVal : V → V) via cmpValDef :=
  covVal_defined cmpStep cmpStepDef

def iltbDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c1 c2. ∃ i, !pairDef i c1 c2 ∧ ∃ e, !cmpValDef e i ∧ !pi₁Def y e”

def iallDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c1 c2. ∃ i, !pairDef i c1 c2 ∧ ∃ e, !cmpValDef e i ∧ ∃ q, !pi₂Def q e ∧ !pi₁Def y q”

def iexDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c1 c2. ∃ i, !pairDef i c1 c2 ∧ ∃ e, !cmpValDef e i ∧ ∃ q, !pi₂Def q e ∧ !pi₂Def y q”

instance iltb_defined : 𝚺₁-Function₂ (iltb : V → V → V) via iltbDef := .mk fun v ↦ by
  simp [iltbDef, iltb, pair_defined.iff, cmpVal_defined.iff, pi₁_defined.iff]

instance iall_defined : 𝚺₁-Function₂ (iall : V → V → V) via iallDef := .mk fun v ↦ by
  simp [iallDef, iall, pair_defined.iff, cmpVal_defined.iff, pi₁_defined.iff, pi₂_defined.iff]

instance iex_defined : 𝚺₁-Function₂ (iex : V → V → V) via iexDef := .mk fun v ↦ by
  simp [iexDef, iex, pair_defined.iff, cmpVal_defined.iff, pi₂_defined.iff]

instance iltb_definable : 𝚺₁-Function₂ (iltb : V → V → V) := iltb_defined.to_definable
instance iall_definable : 𝚺₁-Function₂ (iall : V → V → V) := iall_defined.to_definable
instance iex_definable : 𝚺₁-Function₂ (iex : V → V → V) := iex_defined.to_definable

/-! ### The recursion laws of the comparison -/

/-- The three flags at `⟪c1, c2⟫` are the step functions applied to a table whose entries at
smaller positions are the flags there. -/
lemma cmp_unfold (c1 c2 : V) :
    ∃ S : V, iltb c1 c2 = ltStep c1 c2 S ∧
      iall c1 c2 = alStep c1 c2 S (iltb c1 c2) ∧
      iex c1 c2 = exStep c1 c2 S (iltb c1 c2) ∧
      ∀ x y : V, ⟪x, y⟫ < ⟪c1, c2⟫ →
        rdLt S x y = iltb x y ∧ rdAl S x y = iall x y ∧ rdEx S x y = iex x y := by
  obtain ⟨S, hS, hr⟩ := covVal_unfold cmpStep cmpStepDef (⟪c1, c2⟫ : V)
  have hv : cmpVal ⟪c1, c2⟫ = cmpStep ⟪c1, c2⟫ S := hS
  refine ⟨S, ?_, ?_, ?_, fun x y hxy => ?_⟩
  · simp [iltb, hv, cmpStep]
  · simp [iall, iltb, hv, cmpStep]
  · simp [iex, iltb, hv, cmpStep]
  · have e : znth S ⟪x, y⟫ = cmpVal ⟪x, y⟫ := hr _ hxy
    simp [rdLt, rdAl, rdEx, iltb, iall, iex, e]

lemma iltb_zero_zero : iltb (0 : V) 0 = 0 := by
  obtain ⟨S, h, -⟩ := cmp_unfold (0 : V) 0
  simp [h, ltStep]

lemma iltb_zero_pos {c : V} (hc : c ≠ 0) : iltb (0 : V) c = 1 := by
  obtain ⟨S, h, -⟩ := cmp_unfold (0 : V) c
  simp [h, ltStep, kind_eq_zero_iff, hc]

lemma iltb_pos_zero {c : V} (hc : c ≠ 0) : iltb c (0 : V) = 0 := by
  obtain ⟨S, h, -⟩ := cmp_unfold c (0 : V)
  simp [h, ltStep, kind_eq_zero_iff, hc]

lemma iltb_cons_cons (x s y t : V) :
    iltb (tcCons x s) (tcCons y t) = bor (iltb x y) (band (beq x y) (iltb s t)) := by
  obtain ⟨S, h, -, -, hr⟩ := cmp_unfold (tcCons x s) (tcCons y t)
  rw [h, ltStep]
  simp only [kind_tcCons]
  simp [ltCC, (hr x y (pair_lt_pair (hd_lt_tcCons x s) (hd_lt_tcCons y t))).1,
    (hr s t (pair_lt_pair (tl_lt_tcCons x s) (tl_lt_tcCons y t))).1]

lemma iltb_cons_prin (x s : V) {c : V} (hc : kind c = 1 ∨ kind c = 2) :
    iltb (tcCons x s) c = iltb x c := by
  obtain ⟨S, h, -, -, hr⟩ := cmp_unfold (tcCons x s) c
  have hc0 : kind c ≠ 0 := by rcases hc with hc | hc <;> simp [hc]
  have hc3 : kind c ≠ 3 := by rcases hc with hc | hc <;> simp [hc]
  rw [h, ltStep]
  simp only [kind_tcCons]
  simp [hc0, hc3, ltCP, (hr x c (pair_lt_pair_left (hd_lt_tcCons x s) c)).1]

lemma iltb_prin_cons {c : V} (hc : kind c = 1 ∨ kind c = 2) (y t : V) :
    iltb c (tcCons y t) = bor (iltb c y) (beq c y) := by
  obtain ⟨S, h, -, -, hr⟩ := cmp_unfold c (tcCons y t)
  have hc0 : kind c ≠ 0 := by rcases hc with hc | hc <;> simp [hc]
  have hc3 : kind c ≠ 3 := by rcases hc with hc | hc <;> simp [hc]
  rw [h, ltStep]
  simp only [kind_tcCons]
  simp [hc0, hc3, ltPC, (hr c y (pair_lt_pair_right c (hd_lt_tcCons y t))).1]

lemma iltb_theta_theta (a b : V) :
    iltb (tcTheta a) (tcTheta b) =
      bor (band (iltb a b) (iall a (tcTheta b))) (iex (tcTheta a) b) := by
  obtain ⟨S, h, -, -, hr⟩ := cmp_unfold (tcTheta a) (tcTheta b)
  rw [h, ltStep]
  simp only [kind_tcTheta]
  simp [ltTT, (hr a b (pair_lt_pair (lt_tcTheta a) (lt_tcTheta b))).1,
    (hr a (tcTheta b) (pair_lt_pair_left (lt_tcTheta a) _)).2.1,
    (hr (tcTheta a) b (pair_lt_pair_right _ (lt_tcTheta b))).2.2]

lemma iltb_theta_one (a : V) : iltb (tcTheta a) 1 = 1 := by
  obtain ⟨S, h, -⟩ := cmp_unfold (tcTheta a) 1
  rw [h, ltStep]
  simp

lemma iltb_one_prin {c : V} (hc : kind c = 1 ∨ kind c = 2) : iltb (1 : V) c = 0 := by
  obtain ⟨S, h, -⟩ := cmp_unfold (1 : V) c
  rw [h, ltStep]
  rcases hc with hc | hc <;> simp [hc]

lemma iall_of_kind {c : V} (hc : kind c = 0 ∨ kind c = 1) (x : V) : iall c x = 1 := by
  obtain ⟨S, -, h, -⟩ := cmp_unfold c x
  rw [h, alStep]
  rcases hc with hc | hc <;> simp [hc]

lemma iall_theta (a x : V) : iall (tcTheta a) x = iltb (tcTheta a) x := by
  obtain ⟨S, -, h, -⟩ := cmp_unfold (tcTheta a) x
  rw [h, alStep]
  simp

lemma iall_cons (y t x : V) : iall (tcCons y t) x = band (iall y x) (iall t x) := by
  obtain ⟨S, -, h, -, hr⟩ := cmp_unfold (tcCons y t) x
  rw [h, alStep]
  simp [(hr y x (pair_lt_pair_left (hd_lt_tcCons y t) x)).2.1,
    (hr t x (pair_lt_pair_left (tl_lt_tcCons y t) x)).2.1]

lemma iex_of_kind (x : V) {c : V} (hc : kind c = 0 ∨ kind c = 1) : iex x c = 0 := by
  obtain ⟨S, -, -, h, -⟩ := cmp_unfold x c
  rw [h, exStep]
  rcases hc with hc | hc <;> simp [hc]

lemma iex_theta (x d : V) :
    iex x (tcTheta d) = bor (iltb x (tcTheta d)) (beq x (tcTheta d)) := by
  obtain ⟨S, -, -, h, -⟩ := cmp_unfold x (tcTheta d)
  rw [h, exStep]
  simp

lemma iex_cons (x y t : V) : iex x (tcCons y t) = bor (iex x y) (iex x t) := by
  obtain ⟨S, -, -, h, hr⟩ := cmp_unfold x (tcCons y t)
  rw [h, exStep]
  simp [(hr x y (pair_lt_pair_right x (hd_lt_tcCons y t))).2.2,
    (hr x t (pair_lt_pair_right x (tl_lt_tcCons y t))).2.2]

/-! ### Standard codes: the table computes `ltb` -/

/-- The `all` flag at a standard code, in terms of the `lt` flag. -/
theorem iall_mc : ∀ (a : ThetaTerm) (x : V),
    iall (mc a) x = 1 ↔ ∀ g ∈ E a, iltb (mc g) x = 1
  | .Omega, x => by simp [iall_of_kind]
  | .theta a, x => by simp [iall_theta]
  | .sum [], x => by simp [iall_of_kind]
  | .sum (y :: ys), x => by
    rw [mc_cons, iall_cons, band_eq_one, iall_mc y x, iall_mc (.sum ys) x, E_cons]
    simp only [List.mem_append]
    constructor
    · rintro ⟨h1, h2⟩ g (hg | hg)
      exacts [h1 g hg, h2 g hg]
    · intro h
      exact ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩
termination_by a => l a
decreasing_by all_goals simp; try omega

/-- The `ex` flag at a standard code, in terms of the `lt` flag. -/
theorem iex_mc : ∀ (x : V) (b : ThetaTerm),
    iex x (mc b) = 1 ↔ ∃ g ∈ E b, iltb x (mc g) = 1 ∨ x = mc g
  | x, .Omega => by simp [iex_of_kind]
  | x, .theta b => by simp [iex_theta]
  | x, .sum [] => by simp [iex_of_kind]
  | x, .sum (y :: ys) => by
    rw [mc_cons, iex_cons, bor_eq_one, iex_mc x y, iex_mc x (.sum ys), E_cons]
    simp only [List.mem_append]
    constructor
    · rintro (⟨g, hg, h⟩ | ⟨g, hg, h⟩)
      exacts [⟨g, Or.inl hg, h⟩, ⟨g, Or.inr hg, h⟩]
    · rintro ⟨g, hg | hg, h⟩
      exacts [Or.inl ⟨g, hg, h⟩, Or.inr ⟨g, hg, h⟩]
termination_by _ b => l b
decreasing_by all_goals simp; try omega

private lemma kind_mc_prin {p : ThetaTerm} (hp : IsPrin p) :
    kind (mc (V := V) p) = 1 ∨ kind (mc (V := V) p) = 2 := by
  cases p with
  | Omega => simp
  | theta a => simp
  | sum _ => exact absurd hp id

/-- **The internal order agrees with `ltb` on standard codes**, in every model of `IΣ₁`. -/
theorem iltb_mc : ∀ a b : ThetaTerm, iltb (mc (V := V) a) (mc b) = 1 ↔ a < b
  | .sum [], .sum [] => by simp [iltb_zero_zero]
  | .sum [], .Omega => by simp [iltb_zero_pos, nil_lt_Omega]
  | .sum [], .theta b => by simp [iltb_zero_pos, nil_lt_theta]
  | .sum [], .sum (b :: bs) => by simp [iltb_zero_pos, nil_lt_cons]
  | .Omega, .sum [] => by simp [iltb_pos_zero, not_Omega_lt_nil]
  | .theta a, .sum [] => by simp [iltb_pos_zero, not_theta_lt_nil]
  | .sum (a :: as), .sum [] => by simp [iltb_pos_zero, not_cons_lt_nil]
  | .sum (a :: as), .sum (b :: bs) => by
    rw [mc_cons, mc_cons, iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one, mc_inj,
      iltb_mc a b, iltb_mc (.sum as) (.sum bs), cons_lt_cons_iff]
  | .sum (a :: as), .Omega => by
    rw [mc_cons, iltb_cons_prin _ _ (kind_mc_prin isPrin_Omega), iltb_mc a .Omega,
      cons_lt_Omega_iff]
  | .sum (a :: as), .theta b => by
    rw [mc_cons, iltb_cons_prin _ _ (kind_mc_prin (isPrin_theta b)), iltb_mc a (.theta b),
      cons_lt_theta_iff]
  | .Omega, .sum (b :: bs) => by
    rw [mc_cons, iltb_prin_cons (kind_mc_prin isPrin_Omega), bor_eq_one, beq_eq_one, mc_inj,
      iltb_mc .Omega b, Omega_lt_cons_iff, le_def]
  | .theta a, .sum (b :: bs) => by
    rw [mc_cons, iltb_prin_cons (kind_mc_prin (isPrin_theta a)), bor_eq_one, beq_eq_one,
      mc_inj, iltb_mc (.theta a) b, theta_lt_cons_iff, le_def]
  | .Omega, .Omega => by simp [iltb_one_prin]
  | .Omega, .theta b => by simp [iltb_one_prin, not_Omega_lt_theta]
  | .theta a, .Omega => by simp [iltb_theta_one, theta_lt_Omega]
  | .theta a, .theta b => by
    rw [mc_theta, mc_theta, iltb_theta_theta, bor_eq_one, band_eq_one, iltb_mc a b,
      ← mc_theta, iall_mc a, ← mc_theta, iex_mc _ b, theta_lt_theta_iff]
    have h1 : ∀ g ∈ E a, (iltb (mc (V := V) g) (mc (.theta b)) = 1 ↔ g < .theta b) :=
      fun g hg => iltb_mc g (.theta b)
    have h2 : ∀ g ∈ E b, (iltb (mc (V := V) (.theta a)) (mc g) = 1 ↔ .theta a < g) :=
      fun g hg => iltb_mc (.theta a) g
    constructor
    · rintro (⟨hab, hE⟩ | ⟨g, hg, h⟩)
      · exact Or.inl ⟨hab, fun g hg => (h1 g hg).mp (hE g hg)⟩
      · refine Or.inr ⟨g, hg, ?_⟩
        rcases h with h | h
        · exact Or.inl ((h2 g hg).mp h)
        · exact Or.inr (mc_inj.mp h)
    · rintro (⟨hab, hE⟩ | ⟨g, hg, h⟩)
      · exact Or.inl ⟨hab, fun g hg => (h1 g hg).mpr (hE g hg)⟩
      · refine Or.inr ⟨g, hg, ?_⟩
        rcases h with h | h
        · exact Or.inl ((h2 g hg).mpr h)
        · exact Or.inr (congrArg mc h)
termination_by a b => l a + l b
decreasing_by
  all_goals simp only [l_Omega, l_theta, l_cons]
  all_goals first
    | omega
    | (have := l_le_of_mem_E hg; omega)

end Model

/-! ## Recognisers, length and coefficient sets

Four more tables, three over single codes and one over pairs.

* `isTermb c = 1` iff `c` is the code of a term.  At a cons code the tail must again be the
  code of a sum: `sumK` checks that it is `0` or a cons code.
* `nfA c`: at the code of a sum `⟨α₀, …⟩`, that every `αᵢ` is normal and the entries are
  non-increasing; at `ϑ α`, that `α` is normal; at `Ω`, `1`.  Normality itself is
  `isNFb c = band (nfA c) (sok c)`, where `sok` is the one-entry condition on sums, which is
  not hereditary and so is kept out of the table.
* `ilen c` is the length `l`.
* `iinE g c = 1` iff `g` is an element of `E(c)`, over pair positions `⟪g, c⟫`. -/

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

@[simp] lemma sumK_one : sumK (1 : V) = 0 := by simp [sumK]

@[simp] lemma sumK_tcTheta (a : V) : sumK (tcTheta a) = 0 := by simp [sumK]

/-! ### Codes of terms -/

/-- The step of the term recogniser. -/
noncomputable def wfStep (c s : V) : V :=
  if kind c = 0 then 1
  else if kind c = 1 then beq (tcArg c) 0
  else if kind c = 2 then znth s (tcArg c)
  else if kind c = 3 then band (znth s (tcHd c)) (band (znth s (tcTl c)) (sumK (tcTl c)))
  else 0

def wfStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c s. ∃ k, !kindDef k c ∧
    ( (k = 0 ∧ y = 1)
    ∨ (k = 1 ∧ ∃ a, !sndIdxDef a c ∧ !beqDef y a 0)
    ∨ (k = 2 ∧ ∃ a, !sndIdxDef a c ∧ !znthDef y s a)
    ∨ (k = 3 ∧ ∃ h, !tcHdDef h c ∧ ∃ t, !tcTlDef t c ∧ ∃ r1, !znthDef r1 s h ∧
        ∃ r2, !znthDef r2 s t ∧ ∃ q, !sumKDef q t ∧ ∃ b, !bandDef b r2 q ∧ !bandDef y r1 b)
    ∨ (k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ y = 0) )”

instance wfStep_defined : 𝚺₁-Function₂ (wfStep : V → V → V) via wfStepDef := .mk fun v ↦ by
  simp [wfStepDef, wfStep, kind_defined.iff, tcArg, sndIdx_defined.iff, beq_defined.iff,
    znth_defined.iff, tcHd_defined.iff, tcTl_defined.iff, sumK_defined.iff, band_defined.iff]
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

lemma isTermb_kind_one {c : V} (h1 : kind c = 1) : isTermb c = beq (tcArg c) 0 := by
  obtain ⟨S, h, -⟩ := isTermb_unfold c; simp [h, wfStep, h1]

@[simp] lemma isTermb_one : isTermb (1 : V) = 1 := by
  rw [isTermb_kind_one kind_one]; simp [tcArg, sndIdx, pi₂_zero]

@[simp] lemma isTermb_tcTheta (a : V) : isTermb (tcTheta a) = isTermb a := by
  obtain ⟨S, h, hr⟩ := isTermb_unfold (tcTheta a)
  simp [h, wfStep, hr a (lt_tcTheta a)]

@[simp] lemma isTermb_tcCons (x s : V) :
    isTermb (tcCons x s) = band (isTermb x) (band (isTermb s) (sumK s)) := by
  obtain ⟨S, h, hr⟩ := isTermb_unfold (tcCons x s)
  simp [h, wfStep, hr x (hd_lt_tcCons x s), hr s (tl_lt_tcCons x s)]

lemma isTermb_kind_four {c : V} (h4 : kind c = 4) : isTermb c = 0 := by
  obtain ⟨S, h, -⟩ := isTermb_unfold c; simp [h, wfStep, h4]

/-- Every standard code is recognised. -/
theorem isTerm_mc : ∀ t : ThetaTerm, isTerm (mc (V := V) t)
  | .Omega => by simp [isTerm]
  | .theta a => by have := isTerm_mc a; simp_all [isTerm]
  | .sum [] => by simp [isTerm]
  | .sum (x :: xs) => by
    have h1 := isTerm_mc x
    have h2 := isTerm_mc (.sum xs)
    unfold isTerm at h1 h2 ⊢
    rw [mc_cons, isTermb_tcCons, h1, h2]
    cases xs <;> simp
termination_by t => l t
decreasing_by all_goals simp; try omega

/-! ### Normal forms -/

/-- The one-entry condition of a sum code: `0` iff `c` is a one-entry sum whose entry has the
shape of `Ω` or of a `ϑ`-term. -/
noncomputable def sok (c : V) : V :=
  if kind c = 3 ∧ tcTl c = 0 ∧ (kind (tcHd c) = 1 ∨ kind (tcHd c) = 2) then 0 else 1

def sokDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ k, !kindDef k c ∧ ∃ t, !tcTlDef t c ∧ ∃ h, !tcHdDef h c ∧ ∃ kh, !kindDef kh h ∧
    ((k = 3 ∧ t = 0 ∧ (kh = 1 ∨ kh = 2) ∧ y = 0) ∨
      ((k ≠ 3 ∨ t ≠ 0 ∨ (kh ≠ 1 ∧ kh ≠ 2)) ∧ y = 1))”

instance sok_defined : 𝚺₁-Function₁ (sok : V → V) via sokDef := .mk fun v ↦ by
  simp [sokDef, sok, kind_defined.iff, tcTl_defined.iff, tcHd_defined.iff]
  by_cases h : kind (v 1) = 3 ∧ tcTl (v 1) = 0 ∧ (kind (tcHd (v 1)) = 1 ∨ kind (tcHd (v 1)) = 2)
  · obtain ⟨h1, h2, h3⟩ := h
    rcases h3 with h3 | h3 <;> simp [h1, h2, h3]
  · rw [if_neg h]
    simp only [not_and, not_or] at h
    by_cases h1 : kind (v 1) = 3
    · by_cases h2 : tcTl (v 1) = 0
      · obtain ⟨h3, h4⟩ := h h1 h2
        simp [h1, h2, h3, h4]
      · simp [h1, h2]
    · simp [h1]

/-- The ordering condition between the first two entries of a sum code. -/
noncomputable def descOk (c : V) : V :=
  if tcTl c = 0 then 1 else bor (iltb (tcHd (tcTl c)) (tcHd c)) (beq (tcHd (tcTl c)) (tcHd c))

def descOkDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ t, !tcTlDef t c ∧ ((t = 0 ∧ y = 1) ∨ (t ≠ 0 ∧ ∃ h, !tcHdDef h c ∧
    ∃ h2, !tcHdDef h2 t ∧ ∃ r, !iltbDef r h2 h ∧ ∃ e, !beqDef e h2 h ∧ !borDef y r e))”

instance descOk_defined : 𝚺₁-Function₁ (descOk : V → V) via descOkDef := .mk fun v ↦ by
  simp [descOkDef, descOk, tcTl_defined.iff, tcHd_defined.iff, iltb_defined.iff,
    beq_defined.iff, bor_defined.iff]
  by_cases h : tcTl (v 1) = 0 <;> simp [h]

/-- The step of the normal-form table. -/
noncomputable def nfStep (c s : V) : V :=
  if kind c = 0 then 1
  else if kind c = 1 then beq (tcArg c) 0
  else if kind c = 2 then band (znth s (tcArg c)) (sok (tcArg c))
  else if kind c = 3 then
    band (band (znth s (tcHd c)) (sok (tcHd c)))
      (band (znth s (tcTl c)) (band (sumK (tcTl c)) (descOk c)))
  else 0

def nfStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c s. ∃ k, !kindDef k c ∧
    ( (k = 0 ∧ y = 1)
    ∨ (k = 1 ∧ ∃ a, !sndIdxDef a c ∧ !beqDef y a 0)
    ∨ (k = 2 ∧ ∃ a, !sndIdxDef a c ∧ ∃ r, !znthDef r s a ∧ ∃ o, !sokDef o a ∧ !bandDef y r o)
    ∨ (k = 3 ∧ ∃ h, !tcHdDef h c ∧ ∃ t, !tcTlDef t c ∧ ∃ r1, !znthDef r1 s h ∧
        ∃ o, !sokDef o h ∧ ∃ b1, !bandDef b1 r1 o ∧ ∃ r2, !znthDef r2 s t ∧
        ∃ q, !sumKDef q t ∧ ∃ d, !descOkDef d c ∧ ∃ b2, !bandDef b2 q d ∧
        ∃ b3, !bandDef b3 r2 b2 ∧ !bandDef y b1 b3)
    ∨ (k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ y = 0) )”

instance nfStep_defined : 𝚺₁-Function₂ (nfStep : V → V → V) via nfStepDef := .mk fun v ↦ by
  simp [nfStepDef, nfStep, kind_defined.iff, tcArg, sndIdx_defined.iff, beq_defined.iff,
    znth_defined.iff, sok_defined.iff, band_defined.iff, tcHd_defined.iff, tcTl_defined.iff,
    sumK_defined.iff, descOk_defined.iff]
  rcases kind_cases (v 1) with h | h | h | h | h <;> simp [h]

/-- The hereditary part of normality (see the section header). -/
noncomputable def nfA (c : V) : V := covVal nfStep nfStepDef c

/-- The normal-form flag: `1` iff `c` is the code of a term in normal form. -/
noncomputable def isNFb (c : V) : V := band (nfA c) (sok c)

/-- `c` is the code of a term in normal form. -/
def isNF (c : V) : Prop := isNFb c = 1

def nfADef : 𝚺₁.Semisentence 2 := covValDef nfStepDef

instance nfA_defined : 𝚺₁-Function₁ (nfA : V → V) via nfADef := covVal_defined nfStep nfStepDef

def isNFbDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ a, !nfADef a c ∧ ∃ o, !sokDef o c ∧ !bandDef y a o”

instance isNFb_defined : 𝚺₁-Function₁ (isNFb : V → V) via isNFbDef := .mk fun v ↦ by
  simp [isNFbDef, isNFb, nfA_defined.iff, sok_defined.iff, band_defined.iff]

lemma nfA_unfold (c : V) : ∃ S : V, nfA c = nfStep c S ∧ ∀ k < c, znth S k = nfA k :=
  covVal_unfold nfStep nfStepDef c

@[simp] lemma nfA_zero : nfA (0 : V) = 1 := by
  obtain ⟨S, h, -⟩ := nfA_unfold (0 : V); simp [h, nfStep]

lemma nfA_kind_one {c : V} (h1 : kind c = 1) : nfA c = beq (tcArg c) 0 := by
  obtain ⟨S, h, -⟩ := nfA_unfold c; simp [h, nfStep, h1]

@[simp] lemma nfA_one : nfA (1 : V) = 1 := by
  rw [nfA_kind_one kind_one]; simp [tcArg, sndIdx, pi₂_zero]

@[simp] lemma nfA_tcTheta (a : V) : nfA (tcTheta a) = isNFb a := by
  obtain ⟨S, h, hr⟩ := nfA_unfold (tcTheta a)
  simp [h, nfStep, hr a (lt_tcTheta a), isNFb]

@[simp] lemma nfA_tcCons (x s : V) :
    nfA (tcCons x s) = band (isNFb x) (band (nfA s) (band (sumK s) (descOk (tcCons x s)))) := by
  obtain ⟨S, h, hr⟩ := nfA_unfold (tcCons x s)
  simp [h, nfStep, hr x (hd_lt_tcCons x s), hr s (tl_lt_tcCons x s), isNFb]

lemma nfA_kind_four {c : V} (h4 : kind c = 4) : nfA c = 0 := by
  obtain ⟨S, h, -⟩ := nfA_unfold c; simp [h, nfStep, h4]

@[simp] lemma sok_zero : sok (0 : V) = 1 := by simp [sok]

@[simp] lemma sok_one : sok (1 : V) = 1 := by simp [sok]

@[simp] lemma sok_tcTheta (a : V) : sok (tcTheta a) = 1 := by simp [sok]

lemma sok_tcCons (x s : V) :
    sok (tcCons x s) = if s = 0 ∧ (kind x = 1 ∨ kind x = 2) then 0 else 1 := by
  simp [sok]

@[simp] lemma descOk_tcCons_zero (x : V) : descOk (tcCons x 0) = 1 := by simp [descOk]

@[simp] lemma descOk_tcCons_tcCons (x y t : V) :
    descOk (tcCons x (tcCons y t)) = bor (iltb y x) (beq y x) := by simp [descOk]

mutual
/-- **Normal forms are recognised on standard codes**, in every model of `IΣ₁`. -/
theorem isNF_mc : ∀ t : ThetaTerm, isNF (mc (V := V) t) ↔ NF t
  | .Omega => by simp [isNF, isNFb]
  | .theta a => by
    rw [isNF, mc_theta, isNFb, nfA_tcTheta, sok_tcTheta, nf_theta_iff, band_eq_one,
      and_iff_left rfl]
    exact isNF_mc a
  | .sum xs => by
    rw [nf_sum_iff, ← nfList_iff, isNF, isNFb, band_eq_one, nfA_sum_mc xs]
    have hs : sok (mc (V := V) (.sum xs)) = 1 ↔ SingleOK xs := by
      match xs with
      | [] => simp [SingleOK]
      | [x] =>
        cases x with
        | Omega => simp [sok_tcCons, SingleOK]
        | theta a => simp [sok_tcCons, SingleOK]
        | sum ys => cases ys <;> simp [sok_tcCons, SingleOK]
      | x :: y :: ys => simp [sok_tcCons, SingleOK]
    rw [hs]; tauto
termination_by t => 2 * l t + 1
decreasing_by all_goals simp; try omega

/-- The table part of normality on the code of a sum. -/
theorem nfA_sum_mc : ∀ xs : List ThetaTerm,
    nfA (mc (V := V) (.sum xs)) = 1 ↔ NFList xs ∧ Desc xs
  | [] => by simp [NFList]
  | x :: xs => by
    rw [mc_cons, nfA_tcCons, band_eq_one, band_eq_one, band_eq_one, ← isNF, isNF_mc x,
      nfA_sum_mc xs]
    have hk : sumK (mc (V := V) (.sum xs)) = 1 := by cases xs <;> simp
    have hd : descOk (tcCons (mc (V := V) x) (mc (.sum xs))) = 1 ↔
        (∀ y ∈ xs.head?, y ≤ x) := by
      cases xs with
      | nil => simp
      | cons y ys =>
        rw [mc_cons, descOk_tcCons_tcCons, bor_eq_one, beq_eq_one, mc_inj, iltb_mc]
        simp [ThetaTerm.le_def]
    rw [hd]
    simp only [hk, true_and, NFList]
    cases xs with
    | nil => simp
    | cons y ys => simp; tauto
termination_by xs => 2 * l (.sum xs)
decreasing_by all_goals simp; try omega
end

/-! ### Length -/

/-- The step of the length table. -/
noncomputable def lenStep (c s : V) : V :=
  if kind c = 2 then znth s (tcArg c) + 1
  else if kind c = 3 then znth s (tcHd c) + 1 + znth s (tcTl c)
  else 0

def lenStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c s. ∃ k, !kindDef k c ∧
    ( (k = 2 ∧ ∃ a, !sndIdxDef a c ∧ ∃ r, !znthDef r s a ∧ y = r + 1)
    ∨ (k = 3 ∧ ∃ h, !tcHdDef h c ∧ ∃ t, !tcTlDef t c ∧ ∃ r1, !znthDef r1 s h ∧
        ∃ r2, !znthDef r2 s t ∧ y = r1 + 1 + r2)
    ∨ (k ≠ 2 ∧ k ≠ 3 ∧ y = 0) )”

instance lenStep_defined : 𝚺₁-Function₂ (lenStep : V → V → V) via lenStepDef := .mk fun v ↦ by
  simp [lenStepDef, lenStep, kind_defined.iff, tcArg, sndIdx_defined.iff, znth_defined.iff,
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

@[simp] lemma ilen_one : ilen (1 : V) = 0 := by
  obtain ⟨S, h, -⟩ := ilen_unfold (1 : V); simp [h, lenStep]

@[simp] lemma ilen_tcTheta (a : V) : ilen (tcTheta a) = ilen a + 1 := by
  obtain ⟨S, h, hr⟩ := ilen_unfold (tcTheta a)
  simp [h, lenStep, hr a (lt_tcTheta a)]

@[simp] lemma ilen_tcCons (x s : V) : ilen (tcCons x s) = ilen x + 1 + ilen s := by
  obtain ⟨S, h, hr⟩ := ilen_unfold (tcCons x s)
  simp [h, lenStep, hr x (hd_lt_tcCons x s), hr s (tl_lt_tcCons x s)]

/-- The length on standard codes. -/
theorem ilen_mc : ∀ t : ThetaTerm, ilen (mc (V := V) t) = (l t : V)
  | .Omega => by simp
  | .theta a => by simp [ilen_mc a]
  | .sum [] => by simp
  | .sum (x :: xs) => by simp [ilen_mc x, ilen_mc (.sum xs)]
termination_by t => l t
decreasing_by all_goals simp; try omega

/-! ### Coefficient sets -/

/-- The step of the membership table at position `⟪g, c⟫`. -/
noncomputable def inEStep (i s : V) : V :=
  if kind (π₂ i) = 2 then beq (π₁ i) (π₂ i)
  else if kind (π₂ i) = 3 then
    bor (znth s ⟪π₁ i, tcHd (π₂ i)⟫) (znth s ⟪π₁ i, tcTl (π₂ i)⟫)
  else 0

def inEStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y i s. ∃ g, !pi₁Def g i ∧ ∃ c, !pi₂Def c i ∧ ∃ k, !kindDef k c ∧
    ( (k = 2 ∧ !beqDef y g c)
    ∨ (k = 3 ∧ ∃ h, !tcHdDef h c ∧ ∃ t, !tcTlDef t c ∧ ∃ j1, !pairDef j1 g h ∧
        ∃ j2, !pairDef j2 g t ∧ ∃ r1, !znthDef r1 s j1 ∧ ∃ r2, !znthDef r2 s j2 ∧
        !borDef y r1 r2)
    ∨ (k ≠ 2 ∧ k ≠ 3 ∧ y = 0) )”

instance inEStep_defined : 𝚺₁-Function₂ (inEStep : V → V → V) via inEStepDef := .mk fun v ↦ by
  simp [inEStepDef, inEStep, pi₁_defined.iff, pi₂_defined.iff, kind_defined.iff,
    beq_defined.iff, tcHd_defined.iff, tcTl_defined.iff, pair_defined.iff, znth_defined.iff,
    bor_defined.iff]
  rcases kind_cases (π₂ (v 1)) with h | h | h | h | h <;> simp [h]

/-- **Membership in `E`** on codes: `iinE g c = 1` iff `g` is an element of `E(c)`. -/
noncomputable def iinE (g c : V) : V := covVal inEStep inEStepDef ⟪g, c⟫

def inEValDef : 𝚺₁.Semisentence 2 := covValDef inEStepDef

def iinEDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y g c. ∃ i, !pairDef i g c ∧ !inEValDef y i”

instance iinE_defined : 𝚺₁-Function₂ (iinE : V → V → V) via iinEDef := .mk fun v ↦ by
  simp [iinEDef, iinE, pair_defined.iff, (covVal_defined inEStep inEStepDef).iff, inEValDef]

lemma iinE_unfold (g c : V) :
    ∃ S : V, iinE g c = inEStep ⟪g, c⟫ S ∧
      ∀ x y : V, ⟪x, y⟫ < ⟪g, c⟫ → znth S ⟪x, y⟫ = iinE x y := by
  obtain ⟨S, h, hr⟩ := covVal_unfold inEStep inEStepDef (⟪g, c⟫ : V)
  exact ⟨S, h, fun x y hxy => hr _ hxy⟩

lemma iinE_of_kind (g : V) {c : V} (hc : kind c = 0 ∨ kind c = 1) : iinE g c = 0 := by
  obtain ⟨S, h, -⟩ := iinE_unfold g c
  rw [h, inEStep]
  rcases hc with hc | hc <;> simp [hc]

lemma iinE_tcTheta (g a : V) : iinE g (tcTheta a) = beq g (tcTheta a) := by
  obtain ⟨S, h, -⟩ := iinE_unfold g (tcTheta a)
  simp [h, inEStep]

lemma iinE_tcCons (g x s : V) : iinE g (tcCons x s) = bor (iinE g x) (iinE g s) := by
  obtain ⟨S, h, hr⟩ := iinE_unfold g (tcCons x s)
  simp [h, inEStep, hr g x (pair_lt_pair_right g (hd_lt_tcCons x s)),
    hr g s (pair_lt_pair_right g (tl_lt_tcCons x s))]

/-- Membership in `E` on standard codes. -/
theorem iinE_mc : ∀ (x : V) (a : ThetaTerm), iinE x (mc a) = 1 ↔ ∃ g ∈ E a, x = mc g
  | x, .Omega => by simp [iinE_of_kind]
  | x, .theta a => by simp [iinE_tcTheta]
  | x, .sum [] => by simp [iinE_of_kind]
  | x, .sum (y :: ys) => by
    rw [mc_cons, iinE_tcCons, bor_eq_one, iinE_mc x y, iinE_mc x (.sum ys), E_cons]
    simp only [List.mem_append]
    constructor
    · rintro (⟨g, hg, h⟩ | ⟨g, hg, h⟩)
      exacts [⟨g, Or.inl hg, h⟩, ⟨g, Or.inr hg, h⟩]
    · rintro ⟨g, hg | hg, h⟩
      exacts [Or.inl ⟨g, hg, h⟩, Or.inr ⟨g, hg, h⟩]
termination_by _ a => l a
decreasing_by all_goals simp; try omega

theorem iinE_mc_mc (g a : ThetaTerm) : iinE (mc (V := V) g) (mc a) = 1 ↔ g ∈ E a := by
  rw [iinE_mc]
  constructor
  · rintro ⟨g', hg', h⟩; rwa [mc_inj.mp h]
  · intro h; exact ⟨g, h, rfl⟩

end Model

/-! ## Three-way comparison -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Three-way comparison of codes with the ordering codes `0` (less), `1` (equal),
`2` (greater), as `ThetaTerm.cmp` computes it from the order and equality. -/
noncomputable def icmp (c1 c2 : V) : V := if c1 = c2 then 1 else if iltb c1 c2 = 1 then 0 else 2

def icmpDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c1 c2. (c1 = c2 ∧ y = 1) ∨
    (c1 ≠ c2 ∧ ∃ r, !iltbDef r c1 c2 ∧ ((r = 1 ∧ y = 0) ∨ (r ≠ 1 ∧ y = 2)))”

instance icmp_defined : 𝚺₁-Function₂ (icmp : V → V → V) via icmpDef := .mk fun v ↦ by
  simp [icmpDef, icmp, iltb_defined.iff]
  by_cases h : v 1 = v 2
  · simp [h]
  · by_cases h' : iltb (v 1) (v 2) = 1 <;> simp [h, h']

instance icmp_definable : 𝚺₁-Function₂ (icmp : V → V → V) := icmp_defined.to_definable

theorem icmp_mc_eq_zero_iff (a b : ThetaTerm) : icmp (mc (V := V) a) (mc b) = 0 ↔ a < b := by
  unfold icmp
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (by simpa using h)]
    by_cases h' : iltb (mc (V := V) a) (mc b) = 1
    · simp [h', (iltb_mc a b).mp h']
    · simp [h', (iltb_mc a b).not.mp h']

theorem icmp_mc_eq_one_iff (a b : ThetaTerm) : icmp (mc (V := V) a) (mc b) = 1 ↔ a = b := by
  unfold icmp
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (by simpa using h)]
    by_cases h' : iltb (mc (V := V) a) (mc b) = 1 <;> simp [h', h]

theorem icmp_mc_eq_two_iff (a b : ThetaTerm) : icmp (mc (V := V) a) (mc b) = 2 ↔ b < a := by
  unfold icmp
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (by simpa using h)]
    by_cases h' : iltb (mc (V := V) a) (mc b) = 1
    · have hab := (iltb_mc a b).mp h'
      simp [h', lt_asymm' hab]
    · have hba : b < a := by
        rcases lt_trichotomy' a b with h1 | h1 | h1
        · exact absurd ((iltb_mc a b).mpr h1) h'
        · exact absurd h1 h
        · exact h1
      simp [h', hba]

end Model

/-! ## The arithmetic formulas

Each predicate of the coding as a `Σ₁` formula of `ℒₒᵣ`.  Slot `#0` of a binary order formula
is the smaller element: `thLtDef` and `thPrecDef` evaluated at `![y, x]` say `y ≺ x`. -/

/-- `x` is the code of a term. -/
def thTermDef : 𝚺₁.Semisentence 1 := .mkSigma “x. !isTermbDef 1 x”

/-- `x` is the code of a term in normal form. -/
def thNFDef : 𝚺₁.Semisentence 1 := .mkSigma “x. !isNFbDef 1 x”

/-- `y` is the length of (the term coded by) `x`. -/
def thLenDef : 𝚺₁.Semisentence 2 := .mkSigma “y x. !ilenDef y x”

/-- `g` is an element of `E(a)`. -/
def thInEDef : 𝚺₁.Semisentence 2 := .mkSigma “g a. !iinEDef 1 g a”

/-- The order `y ≺ x` on codes of terms, normal or not. -/
def thLtDef : 𝚺₁.Semisentence 2 := .mkSigma “y x. !iltbDef 1 y x”

/-- The three-way comparison: `y` is the ordering code of `c1` against `c2`. -/
def thCmpDef : 𝚺₁.Semisentence 3 := .mkSigma “y c1 c2. !icmpDef y c1 c2”

/-- **The order of the notation system**: `y` and `x` are codes of normal forms and
`y ≺ x`. -/
def thPrecDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. !isNFbDef 1 y ∧ !isNFbDef 1 x ∧ !iltbDef 1 y x”

/-- The field of the accessibility order: codes of normal forms `≺ Ω`. -/
def thFieldDef : 𝚺₁.Semisentence 1 := .mkSigma “x. !isNFbDef 1 x ∧ !iltbDef 1 x 1”

/-- The order restricted to its field: `y ≺ x ≺ Ω`, both normal. -/
def thPrecFieldDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. !thFieldDef y ∧ !thFieldDef x ∧ !iltbDef 1 y x”

/-- The order as a formula of `ℒₒᵣ`, for `ID1.accForm`. -/
def precC : Semisentence ℒₒᵣ 2 := thPrecDef.val

/-- The order restricted to its field, as a formula of `ℒₒᵣ`. -/
def precFieldC : Semisentence ℒₒᵣ 2 := thPrecFieldDef.val

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem eval_thTermDef (x : V) : thTermDef.val.Evalb ![x] ↔ isTerm x := by
  simp [thTermDef, isTerm, isTermb_defined.iff, eq_comm]

@[simp] theorem eval_thNFDef (x : V) : thNFDef.val.Evalb ![x] ↔ isNF x := by
  simp [thNFDef, isNF, isNFb_defined.iff, eq_comm]

@[simp] theorem eval_thLenDef (y x : V) : thLenDef.val.Evalb ![y, x] ↔ y = ilen x := by
  simp [thLenDef, ilen_defined.iff]

@[simp] theorem eval_thInEDef (g a : V) : thInEDef.val.Evalb ![g, a] ↔ iinE g a = 1 := by
  simp [thInEDef, iinE_defined.iff, eq_comm]

@[simp] theorem eval_thLtDef (y x : V) : thLtDef.val.Evalb ![y, x] ↔ iltb y x = 1 := by
  simp [thLtDef, iltb_defined.iff, eq_comm]

@[simp] theorem eval_thCmpDef (y c1 c2 : V) :
    thCmpDef.val.Evalb ![y, c1, c2] ↔ y = icmp c1 c2 := by
  simp [thCmpDef, icmp_defined.iff]

@[simp] theorem eval_thPrecDef (y x : V) :
    thPrecDef.val.Evalb ![y, x] ↔ isNF y ∧ isNF x ∧ iltb y x = 1 := by
  simp [thPrecDef, isNF, isNFb_defined.iff, iltb_defined.iff, eq_comm]

@[simp] theorem eval_thFieldDef (x : V) :
    thFieldDef.val.Evalb ![x] ↔ isNF x ∧ iltb x 1 = 1 := by
  simp [thFieldDef, isNF, isNFb_defined.iff, iltb_defined.iff, eq_comm]

@[simp] theorem eval_thPrecFieldDef (y x : V) :
    thPrecFieldDef.val.Evalb ![y, x] ↔
      (isNF y ∧ iltb y 1 = 1) ∧ (isNF x ∧ iltb x 1 = 1) ∧ iltb y x = 1 := by
  simp [thPrecFieldDef, isNF, isNFb_defined.iff, iltb_defined.iff, eq_comm, thFieldDef]

/-! ### The formulas on standard codes, in every model of `IΣ₁` -/

theorem eval_thTermDef_mc (t : ThetaTerm) : thTermDef.val.Evalb ![mc (V := V) t] := by
  simpa using isTerm_mc (V := V) t

theorem eval_thNFDef_mc (t : ThetaTerm) : thNFDef.val.Evalb ![mc (V := V) t] ↔ NF t := by
  simpa using isNF_mc (V := V) t

theorem eval_thLenDef_mc (t : ThetaTerm) :
    thLenDef.val.Evalb ![(l t : V), mc (V := V) t] := by
  simp [ilen_mc]

theorem eval_thInEDef_mc (g a : ThetaTerm) :
    thInEDef.val.Evalb ![mc (V := V) g, mc a] ↔ g ∈ E a := by
  simpa using iinE_mc_mc (V := V) g a

theorem eval_thLtDef_mc (y x : ThetaTerm) :
    thLtDef.val.Evalb ![mc (V := V) y, mc x] ↔ y < x := by
  simpa using iltb_mc (V := V) y x

theorem eval_thPrecDef_mc (y x : ThetaTerm) :
    thPrecDef.val.Evalb ![mc (V := V) y, mc x] ↔ NF y ∧ NF x ∧ y < x := by
  simp [isNF_mc, iltb_mc]

theorem iltb_mc_one (x : ThetaTerm) : iltb (mc (V := V) x) 1 = 1 ↔ x < .Omega := by
  simpa using iltb_mc (V := V) x .Omega

theorem eval_thFieldDef_mc (x : ThetaTerm) :
    thFieldDef.val.Evalb ![mc (V := V) x] ↔ NF x ∧ x < .Omega := by
  rw [eval_thFieldDef, isNF_mc, iltb_mc_one]

theorem eval_thPrecFieldDef_mc (y x : ThetaTerm) :
    thPrecFieldDef.val.Evalb ![mc (V := V) y, mc x] ↔
      (NF y ∧ y < .Omega) ∧ (NF x ∧ x < .Omega) ∧ y < x := by
  rw [eval_thPrecFieldDef, isNF_mc, isNF_mc, iltb_mc_one, iltb_mc_one, iltb_mc]

end Model

/-! ## Definability at every level

A total function with a `Σ₁` graph is `Δ₁`-definable in models of `IΣ₁`; these instances make
the functions and predicates of the coding available to the order and succession inductions of
`IΣ₁` (`ISigma1.sigma1_order_induction`, `ISigma1.sigma1_succ_induction`). -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance tcTheta_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (tcTheta : V → V) :=
  tcTheta_definable.of_sigmaOne
instance tcCons_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (tcCons : V → V → V) :=
  tcCons_definable.of_sigmaOne
instance iltb_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (iltb : V → V → V) :=
  iltb_definable.of_sigmaOne
instance iall_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (iall : V → V → V) :=
  iall_definable.of_sigmaOne
instance iex_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (iex : V → V → V) :=
  iex_definable.of_sigmaOne
instance icmp_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (icmp : V → V → V) :=
  icmp_definable.of_sigmaOne

instance isTermb_definable : 𝚺₁-Function₁ (isTermb : V → V) := isTermb_defined.to_definable
instance isTermb_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (isTermb : V → V) :=
  isTermb_definable.of_sigmaOne
instance isNFb_definable : 𝚺₁-Function₁ (isNFb : V → V) := isNFb_defined.to_definable
instance isNFb_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (isNFb : V → V) :=
  isNFb_definable.of_sigmaOne
instance ilen_definable : 𝚺₁-Function₁ (ilen : V → V) := ilen_defined.to_definable
instance ilen_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₁ (ilen : V → V) :=
  ilen_definable.of_sigmaOne
instance iinE_definable : 𝚺₁-Function₂ (iinE : V → V → V) := iinE_defined.to_definable
instance iinE_definable' (Γ) (m : ℕ) : Γ-[m + 1]-Function₂ (iinE : V → V → V) :=
  iinE_definable.of_sigmaOne

instance isTerm_definable (Γ) (m : ℕ) : Γ-[m + 1]-Predicate (isTerm : V → Prop) := by
  unfold isTerm; definability

instance isNF_definable (Γ) (m : ℕ) : Γ-[m + 1]-Predicate (isNF : V → Prop) := by
  unfold isNF; definability

end Model

end OrdinalAnalysis.ID1.Internal
