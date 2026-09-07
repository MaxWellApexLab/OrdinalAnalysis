/-
  Arithmetic coding of Veblen normal forms (the notations below `Γ₀`) inside
  arbitrary models of `IΣ₁`.

  Zero is coded by zero and a nonzero term `φ_a(b) · n + c` is coded by
  `⟪⟪⟪a,b⟫,n⟫,c⟫ + 1`.  Course-of-values tables provide a uniformly definable
  comparison `icmp₁` and normal-form recogniser `isNF₁`.  This is the exact
  analogue of `OrdinalAnalysis.Gentzen.InternalONote` one notation system up:
  the only structural difference is that the leading-term comparison is the
  three-case Veblen rule of `Ordinal.cmp_veblen`, whose two unequal branches
  compare one argument against a *whole* Veblen value `φ_{a'}(b')`.  That value
  is coded by `vcVadd a' b' 1 0`, which is not a subcode of `vcVadd a' b' n' c'`
  but *is* bounded by it once the coefficient `n'` is positive — which is what
  keeps the course-of-values recursion on the pair index legitimate.

  This module is deliberately X-free; the Gentzen layer later maps its
  arithmetic formulas into the language LX.
-/
import OrdinalAnalysis.Gentzen.InternalONote

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OrdinalAnalysis.Gentzen.InternalVNote

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.Gentzen.InternalONote

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Codes -/

/-- The code of the zero notation. -/
noncomputable def vcZero : V := 0

/-- Code of `vadd a b n c` (denoting `φ_a(b) · n + c`) from the subcodes `ac`, `bc`, the
coefficient `n` and the tail code `cc`. -/
noncomputable def vcVadd (ac bc n cc : V) : V := ⟪⟪⟪ac, bc⟫, n⟫, cc⟫ + 1

/-- The `⟪a,b⟫` part of a code: `π₁ (fstIdx c)`. -/
noncomputable def vcHead (c : V) : V := π₁ (fstIdx c)

/-- The first Veblen argument of a code. -/
noncomputable def vcFst (c : V) : V := π₁ (vcHead c)

/-- The second Veblen argument of a code. -/
noncomputable def vcSnd (c : V) : V := π₂ (vcHead c)

/-- The leading coefficient of a code. -/
noncomputable def vcCoeff (c : V) : V := π₂ (fstIdx c)

/-- The tail subcode of a code. -/
noncomputable def vcTail (c : V) : V := sndIdx c

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
@[simp] lemma vcZero_eq : (vcZero : V) = 0 := rfl

@[simp] lemma vcVadd_pos (ac bc n cc : V) : 0 < vcVadd ac bc n cc := by simp [vcVadd]

@[simp] lemma vcVadd_ne_zero (ac bc n cc : V) : vcVadd ac bc n cc ≠ 0 :=
  (vcVadd_pos ac bc n cc).ne'

/-! ### `𝚺₀`-definability of the decode projections -/

def _root_.LO.FirstOrder.Arithmetic.vcHeadDef : 𝚺₀.Semisentence 2 := .mkSigma
  “n c. ∃ f <⁺ c, !fstIdxDef f c ∧ !pi₁Def n f”

instance vcHead_defined : 𝚺₀-Function₁ (vcHead : V → V) via vcHeadDef := .mk fun v ↦ by
  simp [vcHeadDef, vcHead, fstIdx_defined.iff, pi₁_defined.iff]

instance vcHead_definable : 𝚺₀-Function₁ (vcHead : V → V) := vcHead_defined.to_definable
instance vcHead_definable' (Γ) : Γ-Function₁ (vcHead : V → V) := vcHead_definable.of_zero

@[simp] lemma vcHead_le (c : V) : vcHead c ≤ c := by
  have h1 : vcHead c ≤ fstIdx c := by simp [vcHead]
  have h2 : fstIdx c ≤ c - 1 := by simp [fstIdx]
  have h3 : c - 1 ≤ c := by simp
  exact le_trans h1 (le_trans h2 h3)

def _root_.LO.FirstOrder.Arithmetic.vcFstDef : 𝚺₀.Semisentence 2 := .mkSigma
  “n c. ∃ h <⁺ c, !vcHeadDef h c ∧ !pi₁Def n h”

instance vcFst_defined : 𝚺₀-Function₁ (vcFst : V → V) via vcFstDef := .mk fun v ↦ by
  simp [vcFstDef, vcFst, vcHead_defined.iff, pi₁_defined.iff]

instance vcFst_definable : 𝚺₀-Function₁ (vcFst : V → V) := vcFst_defined.to_definable
instance vcFst_definable' (Γ) : Γ-Function₁ (vcFst : V → V) := vcFst_definable.of_zero

def _root_.LO.FirstOrder.Arithmetic.vcSndDef : 𝚺₀.Semisentence 2 := .mkSigma
  “n c. ∃ h <⁺ c, !vcHeadDef h c ∧ !pi₂Def n h”

instance vcSnd_defined : 𝚺₀-Function₁ (vcSnd : V → V) via vcSndDef := .mk fun v ↦ by
  simp [vcSndDef, vcSnd, vcHead_defined.iff, pi₂_defined.iff]

instance vcSnd_definable : 𝚺₀-Function₁ (vcSnd : V → V) := vcSnd_defined.to_definable
instance vcSnd_definable' (Γ) : Γ-Function₁ (vcSnd : V → V) := vcSnd_definable.of_zero

def _root_.LO.FirstOrder.Arithmetic.vcCoeffDef : 𝚺₀.Semisentence 2 := .mkSigma
  “n c. ∃ f <⁺ c, !fstIdxDef f c ∧ !pi₂Def n f”

instance vcCoeff_defined : 𝚺₀-Function₁ (vcCoeff : V → V) via vcCoeffDef := .mk fun v ↦ by
  simp [vcCoeffDef, vcCoeff, fstIdx_defined.iff, pi₂_defined.iff]

instance vcCoeff_definable : 𝚺₀-Function₁ (vcCoeff : V → V) := vcCoeff_defined.to_definable
instance vcCoeff_definable' (Γ) : Γ-Function₁ (vcCoeff : V → V) := vcCoeff_definable.of_zero

instance vcTail_defined : 𝚺₀-Function₁ (vcTail : V → V) via sndIdxDef := .mk fun v ↦ by
  simp [vcTail, sndIdx_defined.iff]

instance vcTail_definable : 𝚺₀-Function₁ (vcTail : V → V) := vcTail_defined.to_definable
instance vcTail_definable' (Γ) : Γ-Function₁ (vcTail : V → V) := vcTail_definable.of_zero

def _root_.LO.FirstOrder.Arithmetic.vcVaddDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y ac bc n cc. ∃ p, !pairDef p ac bc ∧ ∃ q, !pairDef q p n ∧ ∃ r, !pairDef r q cc ∧ y = r + 1”

instance vcVadd_defined : 𝚺₁-Function₄ (vcVadd : V → V → V → V → V) via vcVaddDef :=
  .mk fun v ↦ by simp [vcVaddDef, vcVadd, pair_defined.iff]

instance vcVadd_definable : 𝚺₁-Function₄ (vcVadd : V → V → V → V → V) :=
  vcVadd_defined.to_definable

/-! ### Round-trip: decoding recovers the subcodes -/

@[simp] lemma fstIdx_vcVadd (ac bc n cc : V) : fstIdx (vcVadd ac bc n cc) = ⟪⟪ac, bc⟫, n⟫ := by
  simp [fstIdx, vcVadd]

@[simp] lemma sndIdx_vcVadd (ac bc n cc : V) : sndIdx (vcVadd ac bc n cc) = cc := by
  simp [sndIdx, vcVadd]

@[simp] lemma vcHead_vcVadd (ac bc n cc : V) : vcHead (vcVadd ac bc n cc) = ⟪ac, bc⟫ := by
  simp [vcHead]

@[simp] lemma vcFst_vcVadd (ac bc n cc : V) : vcFst (vcVadd ac bc n cc) = ac := by
  simp [vcFst]

@[simp] lemma vcSnd_vcVadd (ac bc n cc : V) : vcSnd (vcVadd ac bc n cc) = bc := by
  simp [vcSnd]

@[simp] lemma vcCoeff_vcVadd (ac bc n cc : V) : vcCoeff (vcVadd ac bc n cc) = n := by
  simp [vcCoeff]

@[simp] lemma vcTail_vcVadd (ac bc n cc : V) : vcTail (vcVadd ac bc n cc) = cc := by
  simp [vcTail]

/-- **Destructor**: a positive code is the `vcVadd` of its decoded parts. -/
lemma vcVadd_destruct {c : V} (hc : c ≠ 0) :
    vcVadd (vcFst c) (vcSnd c) (vcCoeff c) (vcTail c) = c := by
  have hpos : 0 < c := pos_iff_ne_zero.mpr hc
  unfold vcVadd vcFst vcSnd vcHead vcCoeff vcTail fstIdx sndIdx
  rw [pair_unpair, pair_unpair, pair_unpair]
  exact sub_add_self_of_le (pos_iff_one_le.mp hpos)

/-! ### Subterm bounds (course-of-values decrease)

Every subcode of a `vcVadd`-code is strictly smaller than the code itself: the pairing places
the subterm `≤` the innermost pair `≤` … `≤` the outer pair `< (+1) =` the code. -/

lemma vcFst_lt (ac bc n cc : V) : vcFst (vcVadd ac bc n cc) < vcVadd ac bc n cc := by
  rw [vcFst_vcVadd]
  calc ac ≤ ⟪ac, bc⟫ := le_pair_left ac bc
    _ ≤ ⟪⟪ac, bc⟫, n⟫ := le_pair_left _ n
    _ ≤ ⟪⟪⟪ac, bc⟫, n⟫, cc⟫ := le_pair_left _ cc
    _ < ⟪⟪⟪ac, bc⟫, n⟫, cc⟫ + 1 := by simp
    _ = vcVadd ac bc n cc := rfl

lemma vcSnd_lt (ac bc n cc : V) : vcSnd (vcVadd ac bc n cc) < vcVadd ac bc n cc := by
  rw [vcSnd_vcVadd]
  calc bc ≤ ⟪ac, bc⟫ := le_pair_right ac bc
    _ ≤ ⟪⟪ac, bc⟫, n⟫ := le_pair_left _ n
    _ ≤ ⟪⟪⟪ac, bc⟫, n⟫, cc⟫ := le_pair_left _ cc
    _ < ⟪⟪⟪ac, bc⟫, n⟫, cc⟫ + 1 := by simp
    _ = vcVadd ac bc n cc := rfl

lemma vcCoeff_lt (ac bc n cc : V) : vcCoeff (vcVadd ac bc n cc) < vcVadd ac bc n cc := by
  rw [vcCoeff_vcVadd]
  calc n ≤ ⟪⟪ac, bc⟫, n⟫ := le_pair_right _ n
    _ ≤ ⟪⟪⟪ac, bc⟫, n⟫, cc⟫ := le_pair_left _ cc
    _ < ⟪⟪⟪ac, bc⟫, n⟫, cc⟫ + 1 := by simp
    _ = vcVadd ac bc n cc := rfl

lemma vcTail_lt (ac bc n cc : V) : vcTail (vcVadd ac bc n cc) < vcVadd ac bc n cc := by
  rw [vcTail_vcVadd]
  calc cc ≤ ⟪⟪⟪ac, bc⟫, n⟫, cc⟫ := le_pair_right _ cc
    _ < ⟪⟪⟪ac, bc⟫, n⟫, cc⟫ + 1 := by simp
    _ = vcVadd ac bc n cc := rfl

/-- The first Veblen argument of any positive code is `< c`. -/
lemma vcFst_lt_of_pos {c : V} (hc : 0 < c) : vcFst c < c := by
  have h1 : vcFst c ≤ vcHead c := by simp [vcFst]
  have h2 : vcHead c ≤ fstIdx c := by simp [vcHead]
  have h3 : fstIdx c ≤ c - 1 := by simp [fstIdx]
  exact lt_of_le_of_lt (le_trans h1 (le_trans h2 h3)) (pred_lt_self_of_pos hc)

lemma vcSnd_lt_of_pos {c : V} (hc : 0 < c) : vcSnd c < c := by
  have h1 : vcSnd c ≤ vcHead c := by simp [vcSnd]
  have h2 : vcHead c ≤ fstIdx c := by simp [vcHead]
  have h3 : fstIdx c ≤ c - 1 := by simp [fstIdx]
  exact lt_of_le_of_lt (le_trans h1 (le_trans h2 h3)) (pred_lt_self_of_pos hc)

lemma vcCoeff_lt_of_pos {c : V} (hc : 0 < c) : vcCoeff c < c := by
  have h1 : vcCoeff c ≤ fstIdx c := by simp [vcCoeff]
  have h2 : fstIdx c ≤ c - 1 := by simp [fstIdx]
  exact lt_of_le_of_lt (le_trans h1 h2) (pred_lt_self_of_pos hc)

lemma vcTail_lt_of_pos {c : V} (hc : 0 < c) : vcTail c < c := by
  have h1 : vcTail c ≤ c - 1 := by simp [vcTail, sndIdx]
  exact lt_of_le_of_lt h1 (pred_lt_self_of_pos hc)

/-! ### The leading single Veblen term of a code

`vcLead c` is the code of `φ_a(b)`, the leading term of `c` with coefficient `1` and empty
tail.  It is the argument the Veblen comparison rule feeds back into itself.  Crucially it is
*bounded by* `c` as soon as `c`'s coefficient is positive, which is what makes the
course-of-values recursion on the pair index `⟪c₁,c₂⟫` legitimate. -/

/-- The code of the leading Veblen term `φ_a(b)` of `c`. -/
noncomputable def vcLead (c : V) : V := vcVadd (vcFst c) (vcSnd c) 1 0

def _root_.LO.FirstOrder.Arithmetic.vcLeadDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ a, !vcFstDef a c ∧ ∃ b, !vcSndDef b c ∧ !vcVaddDef y a b 1 0”

instance vcLead_defined : 𝚺₁-Function₁ (vcLead : V → V) via vcLeadDef := .mk fun v ↦ by
  simp [vcLeadDef, vcLead, vcFst_defined.iff, vcSnd_defined.iff, vcVadd_defined.iff]

instance vcLead_definable : 𝚺₁-Function₁ (vcLead : V → V) := vcLead_defined.to_definable

@[simp] lemma vcLead_vcVadd (ac bc n cc : V) : vcLead (vcVadd ac bc n cc) = vcVadd ac bc 1 0 := by
  simp [vcLead]

@[simp] lemma vcLead_ne_zero (c : V) : vcLead c ≠ 0 := by simp [vcLead]

@[simp] lemma vcLead_pos (c : V) : 0 < vcLead c := by simp [vcLead]

/-- **The bound that makes the Veblen recursion terminate.**  For a code with a positive
coefficient the leading single term is bounded by the code itself. -/
lemma vcLead_le {c : V} (hc : c ≠ 0) (hn : vcCoeff c ≠ 0) : vcLead c ≤ c := by
  have hone : (1 : V) ≤ vcCoeff c := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hn)
  have hle : (⟪⟪⟪vcFst c, vcSnd c⟫, 1⟫, 0⟫ : V)
      ≤ ⟪⟪⟪vcFst c, vcSnd c⟫, vcCoeff c⟫, vcTail c⟫ :=
    pair_le_pair (pair_le_pair_right _ hone) (by simp)
  calc vcLead c = ⟪⟪⟪vcFst c, vcSnd c⟫, 1⟫, 0⟫ + 1 := rfl
    _ ≤ ⟪⟪⟪vcFst c, vcSnd c⟫, vcCoeff c⟫, vcTail c⟫ + 1 := by simpa using hle
    _ = c := vcVadd_destruct hc

lemma vcVadd_one_zero_le {ac bc n cc : V} (hn : n ≠ 0) :
    vcVadd ac bc 1 0 ≤ vcVadd ac bc n cc := by
  have := vcLead_le (c := vcVadd ac bc n cc) (by simp) (by simpa using hn)
  simpa using this

/-! ## The internal Veblen comparison `icmp₁`

The three ordering codes are those of `InternalONote`: `0` = less, `1` = equal, `2` = greater,
combined lexicographically by `thenV` and swapped by `oswap`.  What is new is the shape of the
leading-term comparison, which follows `Ordinal.cmp_veblen`: comparing `φ_a(b)` with
`φ_{a'}(b')` compares `a` with `a'` first and then, in the two unequal cases, one argument
against the *whole* Veblen value on the other side.  `leadV` is that three-way branch. -/

/-- Three-way branch on an ordering code: equal (`1`) selects `p`, less (`0`) selects `q`,
anything else selects `r`. -/
noncomputable def leadV (x p q r : V) : V := if x = 1 then p else if x = 0 then q else r

def _root_.LO.FirstOrder.Arithmetic.leadVDef : 𝚺₀.Semisentence 5 := .mkSigma
  “y x p q r. (x = 1 ∧ y = p) ∨ (x ≠ 1 ∧ x = 0 ∧ y = q) ∨ (x ≠ 1 ∧ x ≠ 0 ∧ y = r)”

instance leadV_defined : 𝚺₀-Function₄ (leadV : V → V → V → V → V) via leadVDef := .mk fun v ↦ by
  simp [leadVDef, leadV]
  by_cases h1 : v 1 = 1 <;> by_cases h0 : v 1 = 0 <;> simp [h1, h0]

instance leadV_definable : 𝚺₀-Function₄ (leadV : V → V → V → V → V) := leadV_defined.to_definable
instance leadV_definable' (Γ) : Γ-Function₄ (leadV : V → V → V → V → V) :=
  leadV_definable.of_zero

@[simp] lemma leadV_one (p q r : V) : leadV 1 p q r = p := by simp [leadV]

@[simp] lemma leadV_zero (p q r : V) : leadV 0 p q r = q := by
  rw [leadV, if_neg (zero_ne_one), if_pos rfl]

@[simp] lemma leadV_two (p q r : V) : leadV 2 p q r = r := by
  rw [leadV, if_neg (by simp), if_neg (by simp)]

/-- The "both-positive" branch of the Veblen comparison step at the pair index `i = ⟪c1,c2⟫`
with table `s`: the lexicographic `thenV`-combine of the leading Veblen term comparison, the
coefficient comparison, and the tail comparison.  The leading comparison is `leadV` applied to
the comparison of the two first arguments, dispatching to `b` vs `b'`, `b` vs `φ_{a'}(b')`, or
`φ_a(b)` vs `b'`. -/
noncomputable def icmp₁Main (i s : V) : V :=
  thenV
    (leadV (znth s ⟪vcFst (π₁ i), vcFst (π₂ i)⟫)
      (znth s ⟪vcSnd (π₁ i), vcSnd (π₂ i)⟫)
      (znth s ⟪vcSnd (π₁ i), vcLead (π₂ i)⟫)
      (znth s ⟪vcLead (π₁ i), vcSnd (π₂ i)⟫))
    (thenV (cmpV (vcCoeff (π₁ i)) (vcCoeff (π₂ i)))
      (znth s ⟪vcTail (π₁ i), vcTail (π₂ i)⟫))

def _root_.LO.FirstOrder.Arithmetic.icmp₁MainDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y i s.
    ∃ c1, !pi₁Def c1 i ∧ ∃ c2, !pi₂Def c2 i ∧
      ∃ a1, !vcFstDef a1 c1 ∧ ∃ a2, !vcFstDef a2 c2 ∧ ∃ ia, !pairDef ia a1 a2 ∧
        ∃ ra, !znthDef ra s ia ∧
      ∃ b1, !vcSndDef b1 c1 ∧ ∃ b2, !vcSndDef b2 c2 ∧ ∃ ib, !pairDef ib b1 b2 ∧
        ∃ rb, !znthDef rb s ib ∧
      ∃ l1, !vcLeadDef l1 c1 ∧ ∃ l2, !vcLeadDef l2 c2 ∧
      ∃ ibl, !pairDef ibl b1 l2 ∧ ∃ rbl, !znthDef rbl s ibl ∧
      ∃ ilb, !pairDef ilb l1 b2 ∧ ∃ rlb, !znthDef rlb s ilb ∧
      ∃ lead, !leadVDef lead ra rb rbl rlb ∧
      ∃ n1, !vcCoeffDef n1 c1 ∧ ∃ n2, !vcCoeffDef n2 c2 ∧ ∃ cn, !cmpVDef cn n1 n2 ∧
      ∃ t1, !sndIdxDef t1 c1 ∧ ∃ t2, !sndIdxDef t2 c2 ∧ ∃ it, !pairDef it t1 t2 ∧
        ∃ rt, !znthDef rt s it ∧
      ∃ inner, !thenVDef inner cn rt ∧ !thenVDef y lead inner”

instance icmp₁Main_defined : 𝚺₁-Function₂ (icmp₁Main : V → V → V) via icmp₁MainDef :=
  .mk fun v ↦ by
  simp [icmp₁MainDef, icmp₁Main, pi₁_defined.iff, pi₂_defined.iff, vcFst_defined.iff,
    vcSnd_defined.iff, vcLead_defined.iff, vcCoeff_defined.iff, vcTail, sndIdx_defined.iff,
    pair_defined.iff, znth_defined.iff, cmpV_defined.iff, leadV_defined.iff, thenV_defined.iff]

instance icmp₁Main_definable : 𝚺₁-Function₂ (icmp₁Main : V → V → V) :=
  icmp₁Main_defined.to_definable

/-- Table step of `icmp₁` at the pair index `i = ⟪c1,c2⟫`: the zero base cases, else the
Veblen lexicographic step `icmp₁Main`. -/
noncomputable def icmp₁Next (i s : V) : V :=
  if π₁ i = 0 then (if π₂ i = 0 then 1 else 0)
  else if π₂ i = 0 then 2
  else icmp₁Main i s

def _root_.LO.FirstOrder.Arithmetic.icmp₁NextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y i s.
    ∃ c1, !pi₁Def c1 i ∧ ∃ c2, !pi₂Def c2 i ∧
      ( (c1 = 0 ∧ c2 = 0 ∧ y = 1)
      ∨ (c1 = 0 ∧ c2 ≠ 0 ∧ y = 0)
      ∨ (c1 ≠ 0 ∧ c2 = 0 ∧ y = 2)
      ∨ (c1 ≠ 0 ∧ c2 ≠ 0 ∧ !icmp₁MainDef y i s) )”

instance icmp₁Next_defined : 𝚺₁-Function₂ (icmp₁Next : V → V → V) via icmp₁NextDef :=
  .mk fun v ↦ by
  simp [icmp₁NextDef, icmp₁Next, pi₁_defined.iff, pi₂_defined.iff, icmp₁Main_defined.iff]
  by_cases h1 : π₁ (v 1) = 0 <;> by_cases h2 : π₂ (v 1) = 0 <;> simp [h1, h2]

instance icmp₁Next_definable : 𝚺₁-Function₂ (icmp₁Next : V → V → V) :=
  icmp₁Next_defined.to_definable

/-! ### The `icmp₁` table -/

/-- Blueprint for the `icmp₁` table: position `j` holds `icmp₁Next j (table @ 0..j-1)`. -/
def icmp₁Table.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 1”
  succ := .mkSigma “y ih n. ∃ v, !icmp₁NextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def icmp₁Table.construction : PR.Construction V icmp₁Table.blueprint where
  zero := fun _ ↦ !⟦1⟧
  succ := fun _ n ih ↦ seqCons ih (icmp₁Next (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [icmp₁Table.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [icmp₁Table.blueprint, icmp₁Next_defined.iff, seqCons_defined.iff]

noncomputable def icmp₁Table (n : V) : V := icmp₁Table.construction.result ![] n

@[simp] lemma icmp₁Table_zero : icmp₁Table (0 : V) = !⟦1⟧ := by
  simp [icmp₁Table, icmp₁Table.construction]

@[simp] lemma icmp₁Table_succ (n : V) :
    icmp₁Table (n + 1) = seqCons (icmp₁Table n) (icmp₁Next (n + 1) (icmp₁Table n)) := by
  simp [icmp₁Table, icmp₁Table.construction]

/-- **Internal Veblen-normal-form comparison.** `icmp₁ c1 c2` is the ordering code
(lt = 0, eq = 1, gt = 2) of the codes `c1`, `c2`, read out of the table at `⟪c1,c2⟫`. -/
noncomputable def icmp₁ (c1 c2 : V) : V := znth (icmp₁Table ⟪c1, c2⟫) ⟪c1, c2⟫

def _root_.LO.FirstOrder.Arithmetic.icmp₁TableDef : 𝚺₁.Semisentence 2 :=
  icmp₁Table.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance icmp₁Table_defined : 𝚺₁-Function₁ (icmp₁Table : V → V) via icmp₁TableDef := .mk
  fun v ↦ by simp [icmp₁Table.construction.result_defined_iff, icmp₁TableDef]; rfl

instance icmp₁Table_definable : 𝚺₁-Function₁ (icmp₁Table : V → V) :=
  icmp₁Table_defined.to_definable
instance icmp₁Table_definable' (Γ) (m : ℕ) :
    Γ-[m + 1]-Function₁ (icmp₁Table : V → V) :=
  icmp₁Table_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.icmp₁Def : 𝚺₁.Semisentence 3 := .mkSigma
  “y c1 c2. ∃ i, !pairDef i c1 c2 ∧ ∃ t, !icmp₁TableDef t i ∧ !znthDef y t i”

instance icmp₁_defined : 𝚺₁-Function₂ (icmp₁ : V → V → V) via icmp₁Def := .mk fun v ↦ by
  simp [icmp₁Def, icmp₁, pair_defined.iff, icmp₁Table_defined.iff, znth_defined.iff]

instance icmp₁_definable : 𝚺₁-Function₂ (icmp₁ : V → V → V) := icmp₁_defined.to_definable
instance icmp₁_definable' (Γ) (m : ℕ) :
    Γ-[m + 1]-Function₂ (icmp₁ : V → V → V) :=
  icmp₁_definable.of_sigmaOne

/-! ### Structural correctness of the `icmp₁` table -/

private lemma def_icmp₁Table {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ icmp₁Table (v i)) :=
  DefinableFunction₁.comp (F := icmp₁Table) (DefinableFunction.var i)

@[simp] lemma icmp₁Table_seq (n : V) : Seq (icmp₁Table n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_icmp₁Table 0)
  case zero => simp
  case succ n ih => rw [icmp₁Table_succ]; exact ih.seqCons _

@[simp] lemma icmp₁Table_lh (n : V) : lh (icmp₁Table n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_icmp₁Table 0)) (by definability)
  case zero => simp
  case succ n ih => rw [icmp₁Table_succ, Seq.lh_seqCons _ (icmp₁Table_seq n), ih]

lemma znth_icmp₁Table_succ {n k : V} (hk : k < n + 1) :
    znth (icmp₁Table (n + 1)) k = znth (icmp₁Table n) k := by
  rw [icmp₁Table_succ]
  exact znth_seqCons_of_lt (icmp₁Table_seq n) _ (by rw [icmp₁Table_lh]; exact hk)

/-- **Table stability.** Every entry of the length-`(N+1)` table is the genuine `icmp₁` value
at that pair index. -/
lemma znth_icmp₁Table_eq_icmp₁ :
    ∀ N : V, ∀ k ≤ N, znth (icmp₁Table N) k = icmp₁ (π₁ k) (π₂ k) := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_icmp₁Table 1) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := icmp₁)
        (DefinableFunction₁.comp (F := pi₁) (DefinableFunction.var 0))
        (DefinableFunction₁.comp (F := pi₂) (DefinableFunction.var 0)))
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rw [icmp₁]; simp
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rw [icmp₁, pair_unpair]
    · rw [znth_icmp₁Table_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

/-! ### Base cases and the `icmp₁` recursion law -/

private lemma icmp₁_key {m : V} (hm : 0 < m) :
    ∃ M : V, m = M + 1 ∧ znth (icmp₁Table m) m = icmp₁Next m (icmp₁Table M) := by
  obtain ⟨M, hM⟩ : ∃ M, m = M + 1 :=
    ⟨m - 1, (sub_add_self_of_le (pos_iff_one_le.mp hm)).symm⟩
  refine ⟨M, hM, ?_⟩
  rw [hM, icmp₁Table_succ]
  have := znth_seqCons_self (icmp₁Table_seq M) (icmp₁Next (M + 1) (icmp₁Table M))
  rwa [icmp₁Table_lh] at this

@[simp] lemma icmp₁_zero_zero : icmp₁ (0 : V) 0 = 1 := by
  rw [icmp₁, pair_zero_zero, icmp₁Table_zero]
  exact (singleton_seq 1).znth_eq_of_mem ((mem_singleton_seq_iff 1 1).mpr rfl)

lemma icmp₁_zero_vcVadd (ac bc n cc : V) : icmp₁ (0 : V) (vcVadd ac bc n cc) = 0 := by
  set c2 := vcVadd ac bc n cc with hc2
  have hpos2 : 0 < c2 := vcVadd_pos ac bc n cc
  set m := (⟪(0 : V), c2⟫ : V) with hm
  have hmpos : 0 < m := lt_of_lt_of_le hpos2 (by rw [hm]; exact le_pair_right 0 c2)
  obtain ⟨M, hM, key⟩ := icmp₁_key hmpos
  have hpi1 : π₁ m = 0 := by rw [hm]; simp
  have hpi2 : π₂ m = c2 := by rw [hm]; simp
  rw [icmp₁, ← hm, key, icmp₁Next, hpi1, hpi2]
  simp [hpos2.ne']

lemma icmp₁_vcVadd_zero (ac bc n cc : V) : icmp₁ (vcVadd ac bc n cc) 0 = 2 := by
  set c1 := vcVadd ac bc n cc with hc1
  have hpos1 : 0 < c1 := vcVadd_pos ac bc n cc
  set m := (⟪c1, (0 : V)⟫ : V) with hm
  have hmpos : 0 < m := lt_of_lt_of_le hpos1 (by rw [hm]; exact le_pair_left c1 0)
  obtain ⟨M, hM, key⟩ := icmp₁_key hmpos
  have hpi1 : π₁ m = c1 := by rw [hm]; simp
  have hpi2 : π₂ m = 0 := by rw [hm]; simp
  rw [icmp₁, ← hm, key, icmp₁Next, hpi1, hpi2]
  simp [hpos1.ne']

/-- **The internal Veblen `icmp₁` recursion.**  Comparison of two positive codes with positive
coefficients is the lexicographic `thenV`-combine of the three-case Veblen leading-term
comparison, the coefficient comparison, and the tail comparison.  This mirrors
`OrdinalAnalysis.VNote.cmp_vadd_vadd`, realized on codes inside `V`.

The hypotheses `n ≠ 0`, `n' ≠ 0` are exactly what makes the two cross-recursive reads
(`b` against `φ_{a'}(b')` and `φ_a(b)` against `b'`) land at table indices below the current
one; they hold for every code of an actual notation, whose coefficients are positive. -/
lemma icmp₁_vcVadd_vcVadd {a b n c a2 b2 n2 c2 : V} (hn : n ≠ 0) (hn2 : n2 ≠ 0) :
    icmp₁ (vcVadd a b n c) (vcVadd a2 b2 n2 c2)
      = thenV
          (leadV (icmp₁ a a2) (icmp₁ b b2)
            (icmp₁ b (vcVadd a2 b2 1 0)) (icmp₁ (vcVadd a b 1 0) b2))
          (thenV (cmpV n n2) (icmp₁ c c2)) := by
  set d1 := vcVadd a b n c with hd1
  set d2 := vcVadd a2 b2 n2 c2 with hd2
  have hpos1 : 0 < d1 := vcVadd_pos a b n c
  have hpos2 : 0 < d2 := vcVadd_pos a2 b2 n2 c2
  set m := (⟪d1, d2⟫ : V) with hm
  have hmpos : 0 < m := lt_of_lt_of_le hpos1 (by rw [hm]; exact le_pair_left d1 d2)
  obtain ⟨M, hM, key⟩ := icmp₁_key hmpos
  have hpi1 : π₁ m = d1 := by rw [hm]; simp
  have hpi2 : π₂ m = d2 := by rw [hm]; simp
  have hlead1 : vcLead d1 ≤ d1 := by rw [hd1, vcLead_vcVadd]; exact vcVadd_one_zero_le hn
  have hlead2 : vcLead d2 ≤ d2 := by rw [hd2, vcLead_vcVadd]; exact vcVadd_one_zero_le hn2
  have hfst : (⟪vcFst d1, vcFst d2⟫ : V) < m := by
    rw [hm]; exact pair_lt_pair (vcFst_lt a b n c) (vcFst_lt a2 b2 n2 c2)
  have hsnd : (⟪vcSnd d1, vcSnd d2⟫ : V) < m := by
    rw [hm]; exact pair_lt_pair (vcSnd_lt a b n c) (vcSnd_lt a2 b2 n2 c2)
  have hbl : (⟪vcSnd d1, vcLead d2⟫ : V) < m := by
    rw [hm]
    exact lt_of_le_of_lt (pair_le_pair_right _ hlead2)
      (pair_lt_pair_left (vcSnd_lt a b n c) d2)
  have hlb : (⟪vcLead d1, vcSnd d2⟫ : V) < m := by
    rw [hm]
    exact lt_of_le_of_lt (pair_le_pair_left hlead1 _)
      (pair_lt_pair_right d1 (vcSnd_lt a2 b2 n2 c2))
  have htail : (⟪vcTail d1, vcTail d2⟫ : V) < m := by
    rw [hm]; exact pair_lt_pair (vcTail_lt a b n c) (vcTail_lt a2 b2 n2 c2)
  have hfstle : (⟪vcFst d1, vcFst d2⟫ : V) ≤ M := le_iff_lt_succ.mpr (hM ▸ hfst)
  have hsndle : (⟪vcSnd d1, vcSnd d2⟫ : V) ≤ M := le_iff_lt_succ.mpr (hM ▸ hsnd)
  have hblle : (⟪vcSnd d1, vcLead d2⟫ : V) ≤ M := le_iff_lt_succ.mpr (hM ▸ hbl)
  have hlble : (⟪vcLead d1, vcSnd d2⟫ : V) ≤ M := le_iff_lt_succ.mpr (hM ▸ hlb)
  have htaille : (⟪vcTail d1, vcTail d2⟫ : V) ≤ M := le_iff_lt_succ.mpr (hM ▸ htail)
  rw [icmp₁, ← hm, key, icmp₁Next, hpi1, hpi2]
  simp only [hpos1.ne', hpos2.ne', if_false]
  rw [icmp₁Main, hpi1, hpi2,
    znth_icmp₁Table_eq_icmp₁ M _ hfstle, znth_icmp₁Table_eq_icmp₁ M _ hsndle,
    znth_icmp₁Table_eq_icmp₁ M _ hblle, znth_icmp₁Table_eq_icmp₁ M _ hlble,
    znth_icmp₁Table_eq_icmp₁ M _ htaille]
  simp only [pi₁_pair, pi₂_pair, hd1, hd2, vcFst_vcVadd, vcSnd_vcVadd, vcCoeff_vcVadd,
    vcTail_vcVadd, vcLead_vcVadd]

/-! ## The internal Veblen normal-form recogniser `isNF₁`

`isNF₁ c` (`isNFb₁ c = 1`) holds iff the code `c` is a valid Veblen normal form.  The external
side conditions of `OrdinalAnalysis.VNote.NF` on `vadd a b n c` are

* `repr b < veblen (repr a) (repr b)` — the second argument is not a fixed point of `φ_a`;
* `repr c < veblen (repr a) (repr b)` — the tail is below the leading term,

and *both* compare against `repr (vadd a b 1 0) = φ_a(b)`, whose code is `vcLead`.  So on codes
both conditions read `icmp₁ · (vcVadd a b 1 0) = 0`.  Unlike the Cantor-normal-form recogniser
`InternalONote.isNF`, no `tail = 0 ∨ …` disjunct is needed: `icmp₁ 0 (vcVadd …) = 0` already
holds (`icmp₁_zero_vcVadd`), so the uniform clause covers the empty tail.

As in `InternalONote.isNFb`, the flag is built as a product of `0/1` indicators through a
course-of-values table, so the step stays `𝚺₁` with no negated existentials. -/

/-- `0/1` indicator that `icmp₁ a b = 0` (i.e. `a ≺ b` in the Veblen order). -/
noncomputable def ltIndic₁ (a b : V) : V := if icmp₁ a b = 0 then 1 else 0

def _root_.LO.FirstOrder.Arithmetic.ltIndic₁Def : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b. ∃ c, !icmp₁Def c a b ∧ ((c = 0 ∧ y = 1) ∨ (c ≠ 0 ∧ y = 0))”

instance ltIndic₁_defined : 𝚺₁-Function₂ (ltIndic₁ : V → V → V) via ltIndic₁Def :=
  .mk fun v ↦ by
  simp [ltIndic₁Def, ltIndic₁, icmp₁_defined.iff]
  by_cases h : icmp₁ (v 1) (v 2) = 0 <;> simp [h]

instance ltIndic₁_definable : 𝚺₁-Function₂ (ltIndic₁ : V → V → V) :=
  ltIndic₁_defined.to_definable

@[simp] lemma ltIndic₁_eq_one_iff (a b : V) : ltIndic₁ a b = 1 ↔ icmp₁ a b = 0 := by
  unfold ltIndic₁; by_cases h : icmp₁ a b = 0 <;> simp [h]

lemma ltIndic₁_le_one (a b : V) : ltIndic₁ a b ≤ 1 := by
  unfold ltIndic₁; by_cases h : icmp₁ a b = 0 <;> simp [h]

/-- The "second argument is not a fixed point of `φ` at the first" flag of a code:
`1` iff `b ≺ φ_a(b)`. -/
noncomputable def fixOk₁ (c : V) : V := ltIndic₁ (vcSnd c) (vcLead c)

/-- The "tail below the leading term" flag of a code: `1` iff `tail ≺ φ_a(b)`. -/
noncomputable def tailOk₁ (c : V) : V := ltIndic₁ (vcTail c) (vcLead c)

def _root_.LO.FirstOrder.Arithmetic.fixOk₁Def : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ b, !vcSndDef b c ∧ ∃ l, !vcLeadDef l c ∧ !ltIndic₁Def y b l”

instance fixOk₁_defined : 𝚺₁-Function₁ (fixOk₁ : V → V) via fixOk₁Def := .mk fun v ↦ by
  simp [fixOk₁Def, fixOk₁, vcSnd_defined.iff, vcLead_defined.iff, ltIndic₁_defined.iff]

instance fixOk₁_definable : 𝚺₁-Function₁ (fixOk₁ : V → V) := fixOk₁_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.tailOk₁Def : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ t, !sndIdxDef t c ∧ ∃ l, !vcLeadDef l c ∧ !ltIndic₁Def y t l”

instance tailOk₁_defined : 𝚺₁-Function₁ (tailOk₁ : V → V) via tailOk₁Def := .mk fun v ↦ by
  simp [tailOk₁Def, tailOk₁, vcTail, sndIdx_defined.iff, vcLead_defined.iff,
    ltIndic₁_defined.iff]

instance tailOk₁_definable : 𝚺₁-Function₁ (tailOk₁ : V → V) := tailOk₁_defined.to_definable

@[simp] lemma fixOk₁_vcVadd (ac bc n cc : V) :
    fixOk₁ (vcVadd ac bc n cc) = ltIndic₁ bc (vcVadd ac bc 1 0) := by
  simp [fixOk₁]

@[simp] lemma tailOk₁_vcVadd (ac bc n cc : V) :
    tailOk₁ (vcVadd ac bc n cc) = ltIndic₁ cc (vcVadd ac bc 1 0) := by
  simp [tailOk₁]

lemma fixOk₁_le_one (c : V) : fixOk₁ c ≤ 1 := ltIndic₁_le_one _ _

lemma tailOk₁_le_one (c : V) : tailOk₁ c ≤ 1 := ltIndic₁_le_one _ _

/-- Table step of `isNFb₁` (only ever evaluated at codes `c > 0`, since position `0` is
seeded): the product of the six Veblen well-formedness flags — coefficient positive, the three
subcodes normal (read off the table at `vcFst c`, `vcSnd c`, `vcTail c`, all `< c`), the
second argument not a fixed point, and the tail below the leading term. -/
noncomputable def isNFb₁Next (c s : V) : V :=
  nzIndic (vcCoeff c) * znth s (vcFst c) * znth s (vcSnd c) * znth s (vcTail c)
    * fixOk₁ c * tailOk₁ c

def _root_.LO.FirstOrder.Arithmetic.isNFb₁NextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c s.
    ∃ co, !vcCoeffDef co c ∧ ∃ nc, !nzIndicDef nc co ∧
    ∃ a, !vcFstDef a c ∧ ∃ sa, !znthDef sa s a ∧
    ∃ b, !vcSndDef b c ∧ ∃ sb, !znthDef sb s b ∧
    ∃ t, !sndIdxDef t c ∧ ∃ st, !znthDef st s t ∧
    ∃ fk, !fixOk₁Def fk c ∧
    ∃ tk, !tailOk₁Def tk c ∧
    y = nc * sa * sb * st * fk * tk”

instance isNFb₁Next_defined : 𝚺₁-Function₂ (isNFb₁Next : V → V → V) via isNFb₁NextDef :=
  .mk fun v ↦ by
  simp [isNFb₁NextDef, isNFb₁Next, vcCoeff_defined.iff, nzIndic_defined.iff,
    vcFst_defined.iff, vcSnd_defined.iff, vcTail, sndIdx_defined.iff, znth_defined.iff,
    fixOk₁_defined.iff, tailOk₁_defined.iff]

instance isNFb₁Next_definable : 𝚺₁-Function₂ (isNFb₁Next : V → V → V) :=
  isNFb₁Next_defined.to_definable

/-! ### The `isNFb₁` table -/

def isNFb₁Table.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 1”
  succ := .mkSigma “y ih n. ∃ v, !isNFb₁NextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def isNFb₁Table.construction : PR.Construction V isNFb₁Table.blueprint where
  zero := fun _ ↦ !⟦1⟧
  succ := fun _ n ih ↦ seqCons ih (isNFb₁Next (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [isNFb₁Table.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [isNFb₁Table.blueprint, isNFb₁Next_defined.iff, seqCons_defined.iff]

noncomputable def isNFb₁Table (n : V) : V := isNFb₁Table.construction.result ![] n

@[simp] lemma isNFb₁Table_zero : isNFb₁Table (0 : V) = !⟦1⟧ := by
  simp [isNFb₁Table, isNFb₁Table.construction]

@[simp] lemma isNFb₁Table_succ (n : V) :
    isNFb₁Table (n + 1) = seqCons (isNFb₁Table n) (isNFb₁Next (n + 1) (isNFb₁Table n)) := by
  simp [isNFb₁Table, isNFb₁Table.construction]

/-- **Internal Veblen well-formedness flag** (`0/1`): `1` iff the code `c` is a valid Veblen
normal form. -/
noncomputable def isNFb₁ (c : V) : V := znth (isNFb₁Table c) c

/-- **Internal `NF` predicate** on Veblen codes inside `V`. -/
def isNF₁ (c : V) : Prop := isNFb₁ c = 1

def _root_.LO.FirstOrder.Arithmetic.isNFb₁TableDef : 𝚺₁.Semisentence 2 :=
  isNFb₁Table.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance isNFb₁Table_defined : 𝚺₁-Function₁ (isNFb₁Table : V → V) via isNFb₁TableDef := .mk
  fun v ↦ by simp [isNFb₁Table.construction.result_defined_iff, isNFb₁TableDef]; rfl

instance isNFb₁Table_definable : 𝚺₁-Function₁ (isNFb₁Table : V → V) :=
  isNFb₁Table_defined.to_definable
instance isNFb₁Table_definable' (Γ) (m : ℕ) :
    Γ-[m + 1]-Function₁ (isNFb₁Table : V → V) :=
  isNFb₁Table_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.isNFb₁Def : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ t, !isNFb₁TableDef t c ∧ !znthDef y t c”

instance isNFb₁_defined : 𝚺₁-Function₁ (isNFb₁ : V → V) via isNFb₁Def := .mk fun v ↦ by
  simp [isNFb₁Def, isNFb₁, isNFb₁Table_defined.iff, znth_defined.iff]

instance isNFb₁_definable : 𝚺₁-Function₁ (isNFb₁ : V → V) := isNFb₁_defined.to_definable
instance isNFb₁_definable' (Γ) (m : ℕ) :
    Γ-[m + 1]-Function₁ (isNFb₁ : V → V) :=
  isNFb₁_definable.of_sigmaOne

instance isNF₁_definable (Γ) (m : ℕ) :
    Γ-[m + 1]-Predicate (isNF₁ : V → Prop) := by
  unfold isNF₁; definability

/-! ### Structural correctness of the `isNFb₁` table -/

private lemma def_isNFb₁Table {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ isNFb₁Table (v i)) :=
  DefinableFunction₁.comp (F := isNFb₁Table) (DefinableFunction.var i)

private lemma def_isNFb₁ {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ isNFb₁ (v i)) :=
  DefinableFunction₁.comp (F := isNFb₁) (DefinableFunction.var i)

@[simp] lemma isNFb₁Table_seq (n : V) : Seq (isNFb₁Table n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_isNFb₁Table 0)
  case zero => simp
  case succ n ih => rw [isNFb₁Table_succ]; exact ih.seqCons _

@[simp] lemma isNFb₁Table_lh (n : V) : lh (isNFb₁Table n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_isNFb₁Table 0))
      (by definability)
  case zero => simp
  case succ n ih => rw [isNFb₁Table_succ, Seq.lh_seqCons _ (isNFb₁Table_seq n), ih]

lemma znth_isNFb₁Table_succ {n k : V} (hk : k < n + 1) :
    znth (isNFb₁Table (n + 1)) k = znth (isNFb₁Table n) k := by
  rw [isNFb₁Table_succ]
  exact znth_seqCons_of_lt (isNFb₁Table_seq n) _ (by rw [isNFb₁Table_lh]; exact hk)

lemma znth_isNFb₁Table_eq_isNFb₁ : ∀ N : V, ∀ k ≤ N, znth (isNFb₁Table N) k = isNFb₁ k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_isNFb₁Table 1) (DefinableFunction.var 0))
      (def_isNFb₁ 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_isNFb₁Table_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

@[simp] lemma isNFb₁_zero : isNFb₁ (0 : V) = 1 := by
  simp only [isNFb₁, isNFb₁Table_zero]
  exact (singleton_seq 1).znth_eq_of_mem ((mem_singleton_seq_iff 1 1).mpr rfl)

@[simp] lemma isNF₁_zero : isNF₁ (0 : V) := by simp [isNF₁]

/-- **The internal `isNFb₁` recursion** on Veblen codes. -/
lemma isNFb₁_vcVadd (ac bc n cc : V) :
    isNFb₁ (vcVadd ac bc n cc)
      = nzIndic n * isNFb₁ ac * isNFb₁ bc * isNFb₁ cc
          * ltIndic₁ bc (vcVadd ac bc 1 0) * ltIndic₁ cc (vcVadd ac bc 1 0) := by
  set c := vcVadd ac bc n cc with hc
  have hpos : 0 < c := vcVadd_pos ac bc n cc
  obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
    ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (isNFb₁Table c) c = isNFb₁Next c (isNFb₁Table M) := by
    rw [hM, isNFb₁Table_succ]
    have := znth_seqCons_self (isNFb₁Table_seq M) (isNFb₁Next (M + 1) (isNFb₁Table M))
    rwa [isNFb₁Table_lh] at this
  have ha : vcFst c ≤ M := le_iff_lt_succ.mpr (hM ▸ vcFst_lt ac bc n cc)
  have hb : vcSnd c ≤ M := le_iff_lt_succ.mpr (hM ▸ vcSnd_lt ac bc n cc)
  have ht : vcTail c ≤ M := le_iff_lt_succ.mpr (hM ▸ vcTail_lt ac bc n cc)
  rw [isNFb₁, key, isNFb₁Next,
    znth_isNFb₁Table_eq_isNFb₁ M (vcFst c) ha, znth_isNFb₁Table_eq_isNFb₁ M (vcSnd c) hb,
    znth_isNFb₁Table_eq_isNFb₁ M (vcTail c) ht]
  simp only [hc, vcCoeff_vcVadd, vcFst_vcVadd, vcSnd_vcVadd, vcTail_vcVadd,
    fixOk₁_vcVadd, tailOk₁_vcVadd]

/-! ### `0/1` arithmetic for the six-factor product -/

private lemma mul_le_one_of {a b : V} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := by
  calc a * b ≤ 1 * 1 := by gcongr
    _ = 1 := by simp

private lemma mul_eq_one_iff_of {a b : V} (ha : a ≤ 1) (hb : b ≤ 1) :
    a * b = 1 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    have ka : a * b ≤ a := by
      calc a * b ≤ a * 1 := by gcongr
        _ = a := by simp
    have kb : a * b ≤ b := by
      calc a * b ≤ 1 * b := by gcongr
        _ = b := by simp
    exact ⟨le_antisymm ha (h ▸ ka), le_antisymm hb (h ▸ kb)⟩
  · rintro ⟨rfl, rfl⟩; simp

private lemma prod6_eq_one {a b c d e f : V}
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1) (he : e ≤ 1) (hf : f ≤ 1) :
    a * b * c * d * e * f = 1 ↔ a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 ∧ e = 1 ∧ f = 1 := by
  rw [mul_eq_one_iff_of
        (mul_le_one_of (mul_le_one_of (mul_le_one_of (mul_le_one_of ha hb) hc) hd) he) hf,
    mul_eq_one_iff_of (mul_le_one_of (mul_le_one_of (mul_le_one_of ha hb) hc) hd) he,
    mul_eq_one_iff_of (mul_le_one_of (mul_le_one_of ha hb) hc) hd,
    mul_eq_one_iff_of (mul_le_one_of ha hb) hc,
    mul_eq_one_iff_of ha hb]
  simp only [and_assoc]

/-- `isNFb₁` is a `0/1` flag. -/
lemma isNFb₁_le_one (c : V) : isNFb₁ c ≤ 1 := by
  induction c using ISigma1.sigma1_order_induction
  · exact Definable.comp₂ (def_isNFb₁ 0) (by definability)
  case ind c ih =>
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · have hpos : 0 < c := pos_iff_ne_zero.mpr hc
      obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
        ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
      have key : znth (isNFb₁Table c) c = isNFb₁Next c (isNFb₁Table M) := by
        rw [hM, isNFb₁Table_succ]
        have := znth_seqCons_self (isNFb₁Table_seq M) (isNFb₁Next (M + 1) (isNFb₁Table M))
        rwa [isNFb₁Table_lh] at this
      have ha : vcFst c ≤ M := le_iff_lt_succ.mpr (hM ▸ vcFst_lt_of_pos hpos)
      have hb : vcSnd c ≤ M := le_iff_lt_succ.mpr (hM ▸ vcSnd_lt_of_pos hpos)
      have ht : vcTail c ≤ M := le_iff_lt_succ.mpr (hM ▸ vcTail_lt_of_pos hpos)
      rw [isNFb₁, key, isNFb₁Next,
        znth_isNFb₁Table_eq_isNFb₁ M (vcFst c) ha, znth_isNFb₁Table_eq_isNFb₁ M (vcSnd c) hb,
        znth_isNFb₁Table_eq_isNFb₁ M (vcTail c) ht]
      have h1 := nzIndic_le_one (vcCoeff c)
      have h2 := ih _ (vcFst_lt_of_pos hpos)
      have h3 := ih _ (vcSnd_lt_of_pos hpos)
      have h4 := ih _ (vcTail_lt_of_pos hpos)
      have h5 := fixOk₁_le_one c
      have h6 := tailOk₁_le_one c
      calc nzIndic (vcCoeff c) * isNFb₁ (vcFst c) * isNFb₁ (vcSnd c) * isNFb₁ (vcTail c)
              * fixOk₁ c * tailOk₁ c
          ≤ 1 * 1 * 1 * 1 * 1 * 1 := by gcongr
        _ = 1 := by simp

/-- **The internal Veblen `NF` recursion** — the form the bridge and the decoding consume.
Compare `InternalONote.isNF_ocOadd`; the two side conditions are the coded readings of
`repr b < veblen (repr a) (repr b)` and `repr c < veblen (repr a) (repr b)`. -/
lemma isNF₁_vcVadd (ac bc n cc : V) :
    isNF₁ (vcVadd ac bc n cc) ↔
      n ≠ 0 ∧ isNF₁ ac ∧ isNF₁ bc ∧ isNF₁ cc ∧
        icmp₁ bc (vcVadd ac bc 1 0) = 0 ∧ icmp₁ cc (vcVadd ac bc 1 0) = 0 := by
  unfold isNF₁
  rw [isNFb₁_vcVadd,
    prod6_eq_one (nzIndic_le_one n) (isNFb₁_le_one ac) (isNFb₁_le_one bc) (isNFb₁_le_one cc)
      (ltIndic₁_le_one _ _) (ltIndic₁_le_one _ _),
    nzIndic_eq_one_iff, ltIndic₁_eq_one_iff, ltIndic₁_eq_one_iff]

/-- The subcodes of a normal code are normal, together with its two side conditions. -/
lemma isNF₁_destruct {c : V} (hc : c ≠ 0) (h : isNF₁ c) :
    vcCoeff c ≠ 0 ∧ isNF₁ (vcFst c) ∧ isNF₁ (vcSnd c) ∧ isNF₁ (vcTail c) ∧
      icmp₁ (vcSnd c) (vcLead c) = 0 ∧ icmp₁ (vcTail c) (vcLead c) = 0 := by
  have hd := vcVadd_destruct hc
  have h' : isNF₁ (vcVadd (vcFst c) (vcSnd c) (vcCoeff c) (vcTail c)) := by rw [hd]; exact h
  rw [isNF₁_vcVadd] at h'
  simp only [vcLead]
  exact h'

/-- **The leading single term of a normal code is normal.**  This is what keeps the
NF-restricted `icmp₁` inductions inside the normal codes: the Veblen comparison rule feeds
`vcLead` back into itself. -/
lemma isNF₁_vcLead {c : V} (hc : c ≠ 0) (h : isNF₁ c) : isNF₁ (vcLead c) := by
  obtain ⟨-, ha, hb, -, hfix, -⟩ := isNF₁_destruct hc h
  simp only [vcLead] at hfix ⊢
  rw [isNF₁_vcVadd]
  exact ⟨_root_.one_ne_zero, ha, hb, isNF₁_zero, hfix, icmp₁_zero_vcVadd _ _ _ _⟩

/-! ### The `icmp₁` recursion in destructor form -/

lemma icmp₁_zero_pos {c : V} (hc : c ≠ 0) : icmp₁ (0 : V) c = 0 := by
  obtain ⟨a, b, n, t, rfl⟩ : ∃ a b n t, c = vcVadd a b n t :=
    ⟨_, _, _, _, (vcVadd_destruct hc).symm⟩
  exact icmp₁_zero_vcVadd a b n t

lemma icmp₁_pos_zero {c : V} (hc : c ≠ 0) : icmp₁ c (0 : V) = 2 := by
  obtain ⟨a, b, n, t, rfl⟩ : ∃ a b n t, c = vcVadd a b n t :=
    ⟨_, _, _, _, (vcVadd_destruct hc).symm⟩
  exact icmp₁_vcVadd_zero a b n t

/-- `icmp₁_vcVadd_vcVadd` phrased on positive codes with positive coefficients — the form the
inductions below consume. -/
lemma icmp₁_pos_pos {c1 c2 : V} (h1 : c1 ≠ 0) (h2 : c2 ≠ 0)
    (hn1 : vcCoeff c1 ≠ 0) (hn2 : vcCoeff c2 ≠ 0) :
    icmp₁ c1 c2 =
      thenV
        (leadV (icmp₁ (vcFst c1) (vcFst c2)) (icmp₁ (vcSnd c1) (vcSnd c2))
          (icmp₁ (vcSnd c1) (vcLead c2)) (icmp₁ (vcLead c1) (vcSnd c2)))
        (thenV (cmpV (vcCoeff c1) (vcCoeff c2)) (icmp₁ (vcTail c1) (vcTail c2))) := by
  obtain ⟨a1, b1, k1, t1, rfl⟩ : ∃ a b n t, c1 = vcVadd a b n t :=
    ⟨_, _, _, _, (vcVadd_destruct h1).symm⟩
  obtain ⟨a2, b2, k2, t2, rfl⟩ : ∃ a b n t, c2 = vcVadd a b n t :=
    ⟨_, _, _, _, (vcVadd_destruct h2).symm⟩
  rw [icmp₁_vcVadd_vcVadd (by simpa using hn1) (by simpa using hn2)]
  simp only [vcFst_vcVadd, vcSnd_vcVadd, vcTail_vcVadd, vcCoeff_vcVadd, vcLead_vcVadd]

/-! ### The five index bounds of the Veblen recursion, on a pair index -/

private lemma pair_indices {m : V} (ha : π₁ m ≠ 0) (hb : π₂ m ≠ 0)
    (hn1 : vcCoeff (π₁ m) ≠ 0) (hn2 : vcCoeff (π₂ m) ≠ 0) :
    (⟪vcFst (π₁ m), vcFst (π₂ m)⟫ : V) < m ∧
    (⟪vcSnd (π₁ m), vcSnd (π₂ m)⟫ : V) < m ∧
    (⟪vcSnd (π₁ m), vcLead (π₂ m)⟫ : V) < m ∧
    (⟪vcLead (π₁ m), vcSnd (π₂ m)⟫ : V) < m ∧
    (⟪vcTail (π₁ m), vcTail (π₂ m)⟫ : V) < m := by
  have hm : (⟪π₁ m, π₂ m⟫ : V) = m := pair_unpair m
  have hlead1 : vcLead (π₁ m) ≤ π₁ m := vcLead_le ha hn1
  have hlead2 : vcLead (π₂ m) ≤ π₂ m := vcLead_le hb hn2
  have hf1 : vcFst (π₁ m) < π₁ m := vcFst_lt_of_pos (pos_iff_ne_zero.mpr ha)
  have hf2 : vcFst (π₂ m) < π₂ m := vcFst_lt_of_pos (pos_iff_ne_zero.mpr hb)
  have hs1 : vcSnd (π₁ m) < π₁ m := vcSnd_lt_of_pos (pos_iff_ne_zero.mpr ha)
  have hs2 : vcSnd (π₂ m) < π₂ m := vcSnd_lt_of_pos (pos_iff_ne_zero.mpr hb)
  have ht1 : vcTail (π₁ m) < π₁ m := vcTail_lt_of_pos (pos_iff_ne_zero.mpr ha)
  have ht2 : vcTail (π₂ m) < π₂ m := vcTail_lt_of_pos (pos_iff_ne_zero.mpr hb)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := pair_lt_pair hf1 hf2; rwa [hm] at h
  · have h := pair_lt_pair hs1 hs2; rwa [hm] at h
  · have h := lt_of_le_of_lt (pair_le_pair_right _ hlead2) (pair_lt_pair_left hs1 (π₂ m))
    rwa [hm] at h
  · have h := lt_of_le_of_lt (pair_le_pair_left hlead1 _) (pair_lt_pair_right (π₁ m) hs2)
    rwa [hm] at h
  · have h := pair_lt_pair ht1 ht2; rwa [hm] at h

/-! ### `icmp₁` returns an ordering code

(`InternalONote`'s `cmpV_cases` / `thenV_cases_of` are `private`, so they are re-proved
here.) -/

private lemma cmpV_cases₁ (a b : V) : cmpV a b = 0 ∨ cmpV a b = 1 ∨ cmpV a b = 2 := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact Or.inl (cmpV_eq_zero.mpr hab)
  · exact Or.inr (Or.inl (cmpV_eq_one.mpr hab))
  · refine Or.inr (Or.inr ?_)
    rw [cmpV, if_neg (not_lt.mpr hba.le), if_neg hba.ne']

private lemma thenV_cases₁ {a b : V}
    (ha : a = 0 ∨ a = 1 ∨ a = 2) (hb : b = 0 ∨ b = 1 ∨ b = 2) :
    thenV a b = 0 ∨ thenV a b = 1 ∨ thenV a b = 2 := by
  unfold thenV
  by_cases h : a = 1
  · rw [if_pos h]; exact hb
  · rw [if_neg h]; exact ha

private lemma leadV_cases₁ (x : V) {p q r : V}
    (hp : p = 0 ∨ p = 1 ∨ p = 2) (hq : q = 0 ∨ q = 1 ∨ q = 2) (hr : r = 0 ∨ r = 1 ∨ r = 2) :
    leadV x p q r = 0 ∨ leadV x p q r = 1 ∨ leadV x p q r = 2 := by
  rcases eq_or_ne x 1 with rfl | h1
  · rw [leadV_one]; exact hp
  · rcases eq_or_ne x 0 with rfl | h0
    · rw [leadV_zero]; exact hq
    · rw [leadV, if_neg h1, if_neg h0]; exact hr

private lemma icmp₁_cases_aux : ∀ m : V,
    isNF₁ (π₁ m) → isNF₁ (π₂ m) →
      icmp₁ (π₁ m) (π₂ m) = 0 ∨ icmp₁ (π₁ m) (π₂ m) = 1 ∨ icmp₁ (π₁ m) (π₂ m) = 2 := by
  intro m
  induction m using ISigma1.sigma1_order_induction
  · definability
  case ind m ih =>
    intro h1 h2
    rcases eq_or_ne (π₁ m) 0 with ha | ha
    · rcases eq_or_ne (π₂ m) 0 with hb | hb
      · rw [ha, hb, icmp₁_zero_zero]; exact Or.inr (Or.inl rfl)
      · rw [ha, icmp₁_zero_pos hb]; exact Or.inl rfl
    · rcases eq_or_ne (π₂ m) 0 with hb | hb
      · rw [hb, icmp₁_pos_zero ha]; exact Or.inr (Or.inr rfl)
      · obtain ⟨hn1, -, hB1, hC1, -, -⟩ := isNF₁_destruct ha h1
        obtain ⟨hn2, -, hB2, hC2, -, -⟩ := isNF₁_destruct hb h2
        have hL1 : isNF₁ (vcLead (π₁ m)) := isNF₁_vcLead ha h1
        have hL2 : isNF₁ (vcLead (π₂ m)) := isNF₁_vcLead hb h2
        obtain ⟨-, hB, hBL, hLB, hC⟩ := pair_indices ha hb hn1 hn2
        have eB := ih _ hB (by simpa using hB1) (by simpa using hB2)
        have eBL := ih _ hBL (by simpa using hB1) (by simpa using hL2)
        have eLB := ih _ hLB (by simpa using hL1) (by simpa using hB2)
        have eC := ih _ hC (by simpa using hC1) (by simpa using hC2)
        simp only [pi₁_pair, pi₂_pair] at eB eBL eLB eC
        rw [icmp₁_pos_pos ha hb hn1 hn2]
        exact thenV_cases₁ (leadV_cases₁ _ eB eBL eLB)
          (thenV_cases₁ (cmpV_cases₁ _ _) eC)

/-- Internal Veblen comparison of normal codes always returns one of the three ordering
codes. -/
lemma icmp₁_cases {a b : V} (ha : isNF₁ a) (hb : isNF₁ b) :
    icmp₁ a b = 0 ∨ icmp₁ a b = 1 ∨ icmp₁ a b = 2 := by
  have h := icmp₁_cases_aux ⟪a, b⟫ (by simpa using ha) (by simpa using hb)
  simpa using h

/-! ### Antisymmetry of `icmp₁` on normal codes

The swap law `icmp₁ c2 c1 = oswap (icmp₁ c1 c2)` cannot hold for *arbitrary* codes: the
recursion law `icmp₁_vcVadd_vcVadd` needs both coefficients positive (that is exactly what
puts the two cross-reads `⟪b, vcLead c2⟫`, `⟪vcLead c1, b'⟫` below the current table index),
and at a code with coefficient `0` the table reads out of range.  On normal codes both
coefficients are positive and `isNF₁_vcLead` keeps the cross-reads normal, so the usual
strong induction on the pair index goes through. -/

private lemma icmp₁_swap_aux : ∀ m : V,
    isNF₁ (π₁ m) → isNF₁ (π₂ m) → icmp₁ (π₂ m) (π₁ m) = oswap (icmp₁ (π₁ m) (π₂ m)) := by
  intro m
  induction m using ISigma1.sigma1_order_induction
  · definability
  case ind m ih =>
    intro h1 h2
    rcases eq_or_ne (π₁ m) 0 with ha | ha
    · rcases eq_or_ne (π₂ m) 0 with hb | hb
      · rw [ha, hb, icmp₁_zero_zero]; simp
      · rw [ha, icmp₁_zero_pos hb, icmp₁_pos_zero hb]; simp
    · rcases eq_or_ne (π₂ m) 0 with hb | hb
      · rw [hb, icmp₁_pos_zero ha, icmp₁_zero_pos ha]; simp
      · obtain ⟨hn1, hA1, hB1, hC1, -, -⟩ := isNF₁_destruct ha h1
        obtain ⟨hn2, hA2, hB2, hC2, -, -⟩ := isNF₁_destruct hb h2
        have hL1 : isNF₁ (vcLead (π₁ m)) := isNF₁_vcLead ha h1
        have hL2 : isNF₁ (vcLead (π₂ m)) := isNF₁_vcLead hb h2
        obtain ⟨hA, hB, hBL, hLB, hC⟩ := pair_indices ha hb hn1 hn2
        have eA := ih _ hA (by simpa using hA1) (by simpa using hA2)
        have eB := ih _ hB (by simpa using hB1) (by simpa using hB2)
        have eBL := ih _ hBL (by simpa using hB1) (by simpa using hL2)
        have eLB := ih _ hLB (by simpa using hL1) (by simpa using hB2)
        have eC := ih _ hC (by simpa using hC1) (by simpa using hC2)
        simp only [pi₁_pair, pi₂_pair] at eA eB eBL eLB eC
        have hlead :
            leadV (icmp₁ (vcFst (π₂ m)) (vcFst (π₁ m)))
                (icmp₁ (vcSnd (π₂ m)) (vcSnd (π₁ m)))
                (icmp₁ (vcSnd (π₂ m)) (vcLead (π₁ m)))
                (icmp₁ (vcLead (π₂ m)) (vcSnd (π₁ m)))
              = oswap (leadV (icmp₁ (vcFst (π₁ m)) (vcFst (π₂ m)))
                  (icmp₁ (vcSnd (π₁ m)) (vcSnd (π₂ m)))
                  (icmp₁ (vcSnd (π₁ m)) (vcLead (π₂ m)))
                  (icmp₁ (vcLead (π₁ m)) (vcSnd (π₂ m)))) := by
          rcases icmp₁_cases hA1 hA2 with h0 | he | h2'
          · rw [eA, h0, oswap_zero, leadV_two, leadV_zero]; exact eBL
          · rw [eA, he, oswap_one, leadV_one, leadV_one]; exact eB
          · rw [eA, h2', oswap_two, leadV_zero, leadV_two]; exact eLB
        rw [icmp₁_pos_pos ha hb hn1 hn2, icmp₁_pos_pos hb ha hn2 hn1,
          oswap_thenV, oswap_thenV, hlead, cmpV_swap, eC]

/-- **Swapping the arguments of the internal Veblen comparison swaps the less/greater
codes**, on normal codes. -/
lemma icmp₁_swap {c1 c2 : V} (h1 : isNF₁ c1) (h2 : isNF₁ c2) :
    icmp₁ c2 c1 = oswap (icmp₁ c1 c2) := by
  have h := icmp₁_swap_aux ⟪c1, c2⟫ (by simpa using h1) (by simpa using h2)
  simpa using h

/-! ## `𝚺₁` graph formulas for the Veblen notation layer

The exact analogues of `CodedNotation.nfDef` / `CodedNotation.precDef`, one notation system
up.  They are stated here, in the pure arithmetic language, so that `CodedVeblen` only has to
transport them into `LX`. -/

def nfDef₁ : 𝚺₁.Semisentence 1 := .mkSigma
  “x. !isNFb₁Def 1 x”

def precDef₁ : 𝚺₁.Semisentence 2 := .mkSigma
  “x y. !isNFb₁Def 1 x ∧ !isNFb₁Def 1 y ∧ !icmp₁Def 0 x y”

@[simp] theorem eval_nfDef₁ (x : V) :
    nfDef₁.val.Evalb ![x] ↔ isNF₁ x := by
  simp [nfDef₁, isNF₁, isNFb₁_defined.iff, eq_comm]

@[simp] theorem eval_precDef₁ (x y : V) :
    precDef₁.val.Evalb ![x, y] ↔ isNF₁ x ∧ isNF₁ y ∧ icmp₁ x y = 0 := by
  simp [precDef₁, isNF₁, isNFb₁_defined.iff, icmp₁_defined.iff, eq_comm]

end OrdinalAnalysis.Gentzen.InternalVNote
