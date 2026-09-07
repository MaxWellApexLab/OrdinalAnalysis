/-
  Arithmetic coding of Cantor normal forms inside arbitrary models of IΣ₁.

  Zero is coded by zero and a nonzero term ω^e · n + r is coded by
  ⟪⟪e,n⟫,r⟫ + 1.  Course-of-values tables provide uniformly definable
  comparison, normal-form recognition, and ordinary ordinal addition.  This
  module is deliberately X-free; the Gentzen layer later maps its arithmetic
  formulas into the language LX.
-/
import Foundation.FirstOrder.Arithmetic.HFS

namespace OrdinalAnalysis.Gentzen.InternalONote

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Code of `oadd e n r` from the subcodes `ec` (exponent), `n` (coefficient), `rc` (tail). -/
noncomputable def ocOadd (ec n rc : V) : V := ⟪⟪ec, n⟫, rc⟫ + 1

/-- The exponent subcode of a code: `π₁ (fstIdx c)` (`fstIdx c = π₁ (c-1) = ⟪ec,n⟫`). -/
noncomputable def ocExp (c : V) : V := π₁ (fstIdx c)

/-- The coefficient of a code: `π₂ (fstIdx c)`. -/
noncomputable def ocCoeff (c : V) : V := π₂ (fstIdx c)

/-- The tail subcode of a code: `sndIdx c = π₂ (c-1) = rc`. -/
noncomputable def ocTail (c : V) : V := sndIdx c

@[simp] lemma ocOadd_pos (ec n rc : V) : 0 < ocOadd ec n rc := by simp [ocOadd]

@[simp] lemma ocOadd_ne_zero (ec n rc : V) : ocOadd ec n rc ≠ 0 :=
  (ocOadd_pos ec n rc).ne'

/-! ### `𝚺₀`-definability of the decode projections -/

def _root_.LO.FirstOrder.Arithmetic.ocExpDef : 𝚺₀.Semisentence 2 := .mkSigma
  “n c. ∃ f <⁺ c, !fstIdxDef f c ∧ !pi₁Def n f”

instance ocExp_defined : 𝚺₀-Function₁ (ocExp : V → V) via ocExpDef := .mk fun v ↦ by
  simp [ocExpDef, ocExp, fstIdx_defined.iff, pi₁_defined.iff]

instance ocExp_definable : 𝚺₀-Function₁ (ocExp : V → V) := ocExp_defined.to_definable
instance ocExp_definable' (Γ) : Γ-Function₁ (ocExp : V → V) := ocExp_definable.of_zero

def _root_.LO.FirstOrder.Arithmetic.ocCoeffDef : 𝚺₀.Semisentence 2 := .mkSigma
  “n c. ∃ f <⁺ c, !fstIdxDef f c ∧ !pi₂Def n f”

instance ocCoeff_defined : 𝚺₀-Function₁ (ocCoeff : V → V) via ocCoeffDef := .mk fun v ↦ by
  simp [ocCoeffDef, ocCoeff, fstIdx_defined.iff, pi₂_defined.iff]

instance ocCoeff_definable : 𝚺₀-Function₁ (ocCoeff : V → V) := ocCoeff_defined.to_definable
instance ocCoeff_definable' (Γ) : Γ-Function₁ (ocCoeff : V → V) := ocCoeff_definable.of_zero

instance ocTail_defined : 𝚺₀-Function₁ (ocTail : V → V) via sndIdxDef := .mk fun v ↦ by
  simp [ocTail, sndIdx_defined.iff]

instance ocTail_definable : 𝚺₀-Function₁ (ocTail : V → V) := ocTail_defined.to_definable
instance ocTail_definable' (Γ) : Γ-Function₁ (ocTail : V → V) := ocTail_definable.of_zero

/-! ### Round-trip: decode recovers the subcodes -/

@[simp] lemma fstIdx_ocOadd (ec n rc : V) : fstIdx (ocOadd ec n rc) = ⟪ec, n⟫ := by
  simp [fstIdx, ocOadd]

@[simp] lemma sndIdx_ocOadd (ec n rc : V) : sndIdx (ocOadd ec n rc) = rc := by
  simp [sndIdx, ocOadd]

@[simp] lemma ocExp_ocOadd (ec n rc : V) : ocExp (ocOadd ec n rc) = ec := by
  simp [ocExp]

@[simp] lemma ocCoeff_ocOadd (ec n rc : V) : ocCoeff (ocOadd ec n rc) = n := by
  simp [ocCoeff]

@[simp] lemma ocTail_ocOadd (ec n rc : V) : ocTail (ocOadd ec n rc) = rc := by
  simp [ocTail]

/-! ### Subterm bounds (course-of-values decrease)

Each subcode of an `oadd`-code is strictly smaller than the code itself: the pairing places the
subterm `≤` the inner pair `≤` the outer pair `< (+1) =` the code. These are the strict-decrease
facts a course-of-values recursion on the code value relies on. -/

lemma ocExp_lt (ec n rc : V) : ocExp (ocOadd ec n rc) < ocOadd ec n rc := by
  rw [ocExp_ocOadd]
  calc ec ≤ ⟪ec, n⟫ := le_pair_left ec n
    _ ≤ ⟪⟪ec, n⟫, rc⟫ := le_pair_left _ rc
    _ < ⟪⟪ec, n⟫, rc⟫ + 1 := by simp
    _ = ocOadd ec n rc := rfl

lemma ocCoeff_lt (ec n rc : V) : ocCoeff (ocOadd ec n rc) < ocOadd ec n rc := by
  rw [ocCoeff_ocOadd]
  calc n ≤ ⟪ec, n⟫ := le_pair_right ec n
    _ ≤ ⟪⟪ec, n⟫, rc⟫ := le_pair_left _ rc
    _ < ⟪⟪ec, n⟫, rc⟫ + 1 := by simp
    _ = ocOadd ec n rc := rfl

lemma ocTail_lt (ec n rc : V) : ocTail (ocOadd ec n rc) < ocOadd ec n rc := by
  rw [ocTail_ocOadd]
  calc rc ≤ ⟪⟪ec, n⟫, rc⟫ := le_pair_right _ rc
    _ < ⟪⟪ec, n⟫, rc⟫ + 1 := by simp
    _ = ocOadd ec n rc := rfl

/-- The exponent subcode of any positive code is `< c` (via `ocExp = π₁ (fstIdx c)` and the pairing
bounds, with `fstIdx c ≤ c - 1 < c`). The form a recursion uses when it only knows `0 < c`. -/
lemma ocExp_lt_of_pos {c : V} (hc : 0 < c) : ocExp c < c := by
  have h1 : ocExp c ≤ fstIdx c := by simp [ocExp]
  have h2 : fstIdx c ≤ c - 1 := by simp [fstIdx]
  have h3 : c - 1 < c := pred_lt_self_of_pos hc
  exact lt_of_le_of_lt (le_trans h1 h2) h3

lemma ocTail_lt_of_pos {c : V} (hc : 0 < c) : ocTail c < c := by
  have h1 : ocTail c ≤ c - 1 := by simp [ocTail, sndIdx]
  exact lt_of_le_of_lt h1 (pred_lt_self_of_pos hc)

lemma znth_seqCons_of_lt {s : V} (h : Seq s) (x : V) {i} (hi : i < lh s) :
    znth (seqCons s x) i = znth s i :=
  (h.seqCons x).znth_eq_of_mem (Seq.subset_seqCons s x (h.znth hi))

lemma znth_seqCons_self {s : V} (h : Seq s) (x : V) : znth (seqCons s x) (lh s) = x :=
  (h.seqCons x).znth_eq_of_mem (lh_mem_seqCons s x)

noncomputable def thenV (a b : V) : V := if a = 1 then b else a

def _root_.LO.FirstOrder.Arithmetic.thenVDef : 𝚺₀.Semisentence 3 := .mkSigma
  “y a b. (a = 1 ∧ y = b) ∨ (a ≠ 1 ∧ y = a)”

instance thenV_defined : 𝚺₀-Function₂ (thenV : V → V → V) via thenVDef := .mk fun v ↦ by
  simp [thenVDef, thenV]
  by_cases h : v 1 = 1 <;> simp [h]

instance thenV_definable : 𝚺₀-Function₂ (thenV : V → V → V) := thenV_defined.to_definable
instance thenV_definable' (Γ) : Γ-Function₂ (thenV : V → V → V) := thenV_definable.of_zero

/-- `cmp` on ordering codes: 0 if `a<b`, 1 if `a=b`, 2 otherwise. -/
noncomputable def cmpV (a b : V) : V := if a < b then 0 else if a = b then 1 else 2

def _root_.LO.FirstOrder.Arithmetic.cmpVDef : 𝚺₀.Semisentence 3 := .mkSigma
  “y a b. (a < b ∧ y = 0) ∨ (a ≥ b ∧ a = b ∧ y = 1) ∨ (a ≥ b ∧ a ≠ b ∧ y = 2)”

instance cmpV_defined : 𝚺₀-Function₂ (cmpV : V → V → V) via cmpVDef := .mk fun v ↦ by
  simp [cmpVDef, cmpV]
  rcases lt_trichotomy (v 1) (v 2) with h | h | h
  · simp [h]
  · simp [h]
  · simp [not_lt.mpr (le_of_lt h), le_of_lt h, (ne_of_lt h).symm]

instance cmpV_definable : 𝚺₀-Function₂ (cmpV : V → V → V) := cmpV_defined.to_definable
instance cmpV_definable' (Γ) : Γ-Function₂ (cmpV : V → V → V) := cmpV_definable.of_zero

/-- Order-code involution swapping `0`↔`2` (lt↔gt), fixing `1` (eq). `icmp` is antisymmetric
through it: `icmp c2 c1 = oswap (icmp c1 c2)` (`icmp_swap`). -/
noncomputable def oswap (x : V) : V := if x = 0 then 2 else if x = 2 then 0 else x

def _root_.LO.FirstOrder.Arithmetic.oswapDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y x. (x = 0 ∧ y = 2) ∨ (x ≠ 0 ∧ x = 2 ∧ y = 0) ∨ (x ≠ 0 ∧ x ≠ 2 ∧ y = x)”

instance oswap_defined : 𝚺₀-Function₁ (oswap : V → V) via oswapDef := .mk fun v ↦ by
  simp [oswapDef, oswap]
  by_cases h0 : v 1 = 0 <;> by_cases h2 : v 1 = 2 <;> simp [h0, h2]

instance oswap_definable : 𝚺₀-Function₁ (oswap : V → V) := oswap_defined.to_definable

@[simp] lemma oswap_zero : oswap (0 : V) = 2 := by simp [oswap]
@[simp] lemma oswap_two : oswap (2 : V) = 0 := by simp [oswap]
@[simp] lemma oswap_one : oswap (1 : V) = 1 := by simp [oswap]

lemma oswap_eq_one {x : V} : oswap x = 1 ↔ x = 1 := by
  rcases eq_or_ne x 1 with rfl | h
  · simp
  · constructor
    · intro hx; simp only [oswap] at hx
      by_cases h0 : x = 0 <;> by_cases h2 : x = 2 <;> simp_all
    · intro hx; exact absurd hx h

/-- `oswap` is a `thenV`-homomorphism (lexicographic-combine commutes with the swap). -/
lemma oswap_thenV (a b : V) : oswap (thenV a b) = thenV (oswap a) (oswap b) := by
  unfold thenV
  by_cases ha : a = 1
  · simp [ha]
  · rw [if_neg ha, if_neg (by rw [oswap_eq_one]; exact ha)]

@[simp] lemma thenV_one_left (x : V) : thenV 1 x = x := by simp [thenV]
@[simp] lemma thenV_zero_left (x : V) : thenV 0 x = 0 := by
  rw [thenV, if_neg (zero_ne_one)]

/-- `thenV` is associative (lexicographic combine). -/
lemma thenV_assoc (a b c : V) : thenV (thenV a b) c = thenV a (thenV b c) := by
  unfold thenV
  by_cases ha : a = 1 <;> simp [ha]

/-- `cmpV` is antisymmetric through `oswap`. -/
lemma cmpV_swap (a b : V) : cmpV b a = oswap (cmpV a b) := by
  rcases lt_trichotomy a b with h | h | h
  · have e1 : cmpV a b = 0 := by rw [cmpV, if_pos h]
    have e2 : cmpV b a = 2 := by rw [cmpV, if_neg (not_lt.mpr h.le), if_neg h.ne']
    rw [e1, e2]; simp
  · subst h
    have e1 : cmpV a a = 1 := by rw [cmpV, if_neg (_root_.lt_irrefl a), if_pos rfl]
    rw [e1]; simp
  · have e1 : cmpV a b = 2 := by rw [cmpV, if_neg (not_lt.mpr h.le), if_neg h.ne']
    have e2 : cmpV b a = 0 := by rw [cmpV, if_pos h]
    rw [e1, e2]; simp

/-- The "both-positive" branch of the comparison step on the pair index `i = ⟪c1,c2⟫` with table `s`:
lexicographic `then`-combine of the exponent comparison (read at `⟪ocExp c1, ocExp c2⟫`), the leading
coefficient comparison (`cmpV`), and the tail comparison (read at `⟪ocTail c1, ocTail c2⟫`). -/
noncomputable def icmpMain (i s : V) : V :=
  thenV (znth s ⟪ocExp (π₁ i), ocExp (π₂ i)⟫)
    (thenV (cmpV (ocCoeff (π₁ i)) (ocCoeff (π₂ i)))
      (znth s ⟪ocTail (π₁ i), ocTail (π₂ i)⟫))

def _root_.LO.FirstOrder.Arithmetic.icmpMainDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y i s.
    ∃ c1, !pi₁Def c1 i ∧ ∃ c2, !pi₂Def c2 i ∧
      ∃ e1, !ocExpDef e1 c1 ∧ ∃ e2, !ocExpDef e2 c2 ∧ ∃ ie, !pairDef ie e1 e2 ∧
        ∃ re, !znthDef re s ie ∧
      ∃ co1, !ocCoeffDef co1 c1 ∧ ∃ co2, !ocCoeffDef co2 c2 ∧ ∃ cn, !cmpVDef cn co1 co2 ∧
      ∃ t1, !sndIdxDef t1 c1 ∧ ∃ t2, !sndIdxDef t2 c2 ∧ ∃ ia, !pairDef ia t1 t2 ∧
        ∃ ra, !znthDef ra s ia ∧
      ∃ inner, !thenVDef inner cn ra ∧ !thenVDef y re inner”

instance icmpMain_defined : 𝚺₁-Function₂ (icmpMain : V → V → V) via icmpMainDef := .mk fun v ↦ by
  simp [icmpMainDef, icmpMain, pi₁_defined.iff, pi₂_defined.iff, ocExp_defined.iff,
    ocCoeff_defined.iff, ocTail, sndIdx_defined.iff, pair_defined.iff, znth_defined.iff,
    cmpV_defined.iff, thenV_defined.iff]

instance icmpMain_definable : 𝚺₁-Function₂ (icmpMain : V → V → V) := icmpMain_defined.to_definable

/-- Table step of `icmp` on the pair index `i = ⟪c1,c2⟫`: handle the zero base cases (eq=1, lt=0,
gt=2), else the lexicographic `icmpMain`. -/
noncomputable def icmpNext (i s : V) : V :=
  if π₁ i = 0 then (if π₂ i = 0 then 1 else 0)
  else if π₂ i = 0 then 2
  else icmpMain i s

def _root_.LO.FirstOrder.Arithmetic.icmpNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y i s.
    ∃ c1, !pi₁Def c1 i ∧ ∃ c2, !pi₂Def c2 i ∧
      ( (c1 = 0 ∧ c2 = 0 ∧ y = 1)
      ∨ (c1 = 0 ∧ c2 ≠ 0 ∧ y = 0)
      ∨ (c1 ≠ 0 ∧ c2 = 0 ∧ y = 2)
      ∨ (c1 ≠ 0 ∧ c2 ≠ 0 ∧ !icmpMainDef y i s) )”

instance icmpNext_defined : 𝚺₁-Function₂ (icmpNext : V → V → V) via icmpNextDef := .mk fun v ↦ by
  simp [icmpNextDef, icmpNext, pi₁_defined.iff, pi₂_defined.iff, icmpMain_defined.iff]
  by_cases h1 : π₁ (v 1) = 0 <;> by_cases h2 : π₂ (v 1) = 0 <;> simp [h1, h2]

instance icmpNext_definable : 𝚺₁-Function₂ (icmpNext : V → V → V) := icmpNext_defined.to_definable

/-! ### The `icmp` table -/

/-- Blueprint for the `icmp` table: position `j` holds `icmpNext j (table @ 0..j-1)`. -/
def icmpTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 1”
  succ := .mkSigma “y ih n. ∃ v, !icmpNextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def icmpTable.construction : PR.Construction V icmpTable.blueprint where
  zero := fun _ ↦ !⟦1⟧
  succ := fun _ n ih ↦ seqCons ih (icmpNext (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [icmpTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [icmpTable.blueprint, icmpNext_defined.iff, seqCons_defined.iff]

noncomputable def icmpTable (n : V) : V := icmpTable.construction.result ![] n

@[simp] lemma icmpTable_zero : icmpTable (0 : V) = !⟦1⟧ := by
  simp [icmpTable, icmpTable.construction]

@[simp] lemma icmpTable_succ (n : V) :
    icmpTable (n + 1) = seqCons (icmpTable n) (icmpNext (n + 1) (icmpTable n)) := by
  simp [icmpTable, icmpTable.construction]

/-- **Internal CNF comparison.** `icmp c1 c2` = ordering code (lt=0, eq=1, gt=2) of the CNF codes
`c1`, `c2`, read out of the table at the pair index `⟪c1,c2⟫`. -/
noncomputable def icmp (c1 c2 : V) : V := znth (icmpTable ⟪c1, c2⟫) ⟪c1, c2⟫

def _root_.LO.FirstOrder.Arithmetic.icmpTableDef : 𝚺₁.Semisentence 2 :=
  icmpTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance icmpTable_defined : 𝚺₁-Function₁ (icmpTable : V → V) via icmpTableDef := .mk
  fun v ↦ by simp [icmpTable.construction.result_defined_iff, icmpTableDef]; rfl

instance icmpTable_definable : 𝚺₁-Function₁ (icmpTable : V → V) := icmpTable_defined.to_definable
instance icmpTable_definable' (Γ) (m : ℕ) :
    Γ-[m + 1]-Function₁ (icmpTable : V → V) :=
  icmpTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.icmpDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c1 c2. ∃ i, !pairDef i c1 c2 ∧ ∃ t, !icmpTableDef t i ∧ !znthDef y t i”

instance icmp_defined : 𝚺₁-Function₂ (icmp : V → V → V) via icmpDef := .mk fun v ↦ by
  simp [icmpDef, icmp, pair_defined.iff, icmpTable_defined.iff, znth_defined.iff]

instance icmp_definable : 𝚺₁-Function₂ (icmp : V → V → V) := icmp_defined.to_definable
instance icmp_definable' (Γ) (m : ℕ) :
    Γ-[m + 1]-Function₂ (icmp : V → V → V) :=
  icmp_definable.of_sigmaOne

/-! ### Structural correctness of the `icmp` table -/

private lemma def_icmpTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ icmpTable (v i)) :=
  DefinableFunction₁.comp (F := icmpTable) (DefinableFunction.var i)

@[simp] lemma icmpTable_seq (n : V) : Seq (icmpTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_icmpTable 0)
  case zero => simp
  case succ n ih => rw [icmpTable_succ]; exact ih.seqCons _

@[simp] lemma icmpTable_lh (n : V) : lh (icmpTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_icmpTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [icmpTable_succ, Seq.lh_seqCons _ (icmpTable_seq n), ih]

lemma znth_icmpTable_succ {n k : V} (hk : k < n + 1) :
    znth (icmpTable (n + 1)) k = znth (icmpTable n) k := by
  rw [icmpTable_succ]
  exact znth_seqCons_of_lt (icmpTable_seq n) _ (by rw [icmpTable_lh]; exact hk)

/-- **Table stability.** Every entry of the length-`(N+1)` table is the genuine `icmp` value at that
pair index. (`icmp` itself reads `znth (icmpTable ⟪c1,c2⟫) ⟪c1,c2⟫`; this connects the two via the
pair round-trip `⟪π₁ k, π₂ k⟫ = k`.) -/
lemma znth_icmpTable_eq_icmp : ∀ N : V, ∀ k ≤ N, znth (icmpTable N) k = icmp (π₁ k) (π₂ k) := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_icmpTable 1) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := icmp)
        (DefinableFunction₁.comp (F := pi₁) (DefinableFunction.var 0))
        (DefinableFunction₁.comp (F := pi₂) (DefinableFunction.var 0)))
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rw [icmp]; simp
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rw [icmp, pair_unpair]
    · rw [znth_icmpTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

/-! ### Base cases & the `icmp` recursion law -/

lemma pair_zero_zero : (⟪(0 : V), 0⟫ : V) = 0 := by simp [pair]

@[simp] lemma icmp_zero_zero : icmp (0 : V) 0 = 1 := by
  rw [icmp, pair_zero_zero, icmpTable_zero]
  exact (singleton_seq 1).znth_eq_of_mem ((mem_singleton_seq_iff 1 1).mpr rfl)

lemma icmp_zero_ocOadd (ec n rc : V) : icmp (0 : V) (ocOadd ec n rc) = 0 := by
  set c2 := ocOadd ec n rc with hc2
  have hpos2 : 0 < c2 := ocOadd_pos ec n rc
  set m := (⟪(0 : V), c2⟫ : V) with hm
  have hmpos : 0 < m := lt_of_lt_of_le hpos2 (by rw [hm]; exact le_pair_right 0 c2)
  obtain ⟨M, hM⟩ : ∃ M, m = M + 1 :=
    ⟨m - 1, (sub_add_self_of_le (pos_iff_one_le.mp hmpos)).symm⟩
  have key : znth (icmpTable m) m = icmpNext m (icmpTable M) := by
    rw [hM, icmpTable_succ]
    have := znth_seqCons_self (icmpTable_seq M) (icmpNext (M + 1) (icmpTable M))
    rwa [icmpTable_lh] at this
  have hpi1 : π₁ m = 0 := by rw [hm]; simp
  have hpi2 : π₂ m = c2 := by rw [hm]; simp
  rw [icmp, ← hm, key, icmpNext, hpi1, hpi2]
  simp [hpos2.ne']

lemma icmp_ocOadd_zero (ec n rc : V) : icmp (ocOadd ec n rc) 0 = 2 := by
  set c1 := ocOadd ec n rc with hc1
  have hpos1 : 0 < c1 := ocOadd_pos ec n rc
  set m := (⟪c1, (0 : V)⟫ : V) with hm
  have hmpos : 0 < m := lt_of_lt_of_le hpos1 (by rw [hm]; exact le_pair_left c1 0)
  obtain ⟨M, hM⟩ : ∃ M, m = M + 1 :=
    ⟨m - 1, (sub_add_self_of_le (pos_iff_one_le.mp hmpos)).symm⟩
  have key : znth (icmpTable m) m = icmpNext m (icmpTable M) := by
    rw [hM, icmpTable_succ]
    have := znth_seqCons_self (icmpTable_seq M) (icmpNext (M + 1) (icmpTable M))
    rwa [icmpTable_lh] at this
  have hpi1 : π₁ m = c1 := by rw [hm]; simp
  have hpi2 : π₂ m = 0 := by rw [hm]; simp
  rw [icmp, ← hm, key, icmpNext, hpi1, hpi2]
  simp [hpos1.ne']

/-- **The internal `icmp` recursion**: comparison of two positive (`oadd`) codes is the lexicographic
`then`-combine of (exponent comparison, leading-coefficient comparison, tail comparison). Mirrors
`ONoteComp.cmpStep`/`ONote.cmp`, realized on codes inside `V`. -/
lemma icmp_ocOadd (e1 n1 r1 e2 n2 r2 : V) :
    icmp (ocOadd e1 n1 r1) (ocOadd e2 n2 r2)
      = thenV (icmp e1 e2) (thenV (cmpV n1 n2) (icmp r1 r2)) := by
  set c1 := ocOadd e1 n1 r1 with hc1
  set c2 := ocOadd e2 n2 r2 with hc2
  have hpos1 : 0 < c1 := ocOadd_pos e1 n1 r1
  have hpos2 : 0 < c2 := ocOadd_pos e2 n2 r2
  set m := (⟪c1, c2⟫ : V) with hm
  have hmpos : 0 < m := lt_of_lt_of_le hpos1 (by rw [hm]; exact le_pair_left c1 c2)
  obtain ⟨M, hM⟩ : ∃ M, m = M + 1 :=
    ⟨m - 1, (sub_add_self_of_le (pos_iff_one_le.mp hmpos)).symm⟩
  have key : znth (icmpTable m) m = icmpNext m (icmpTable M) := by
    rw [hM, icmpTable_succ]
    have := znth_seqCons_self (icmpTable_seq M) (icmpNext (M + 1) (icmpTable M))
    rwa [icmpTable_lh] at this
  -- the two sub-indices are `≤ M`
  have hpi1 : π₁ m = c1 := by rw [hm]; simp
  have hpi2 : π₂ m = c2 := by rw [hm]; simp
  have hexplt : (⟪ocExp c1, ocExp c2⟫ : V) < m := by
    rw [hm]; exact pair_lt_pair (ocExp_lt e1 n1 r1) (ocExp_lt e2 n2 r2)
  have htaillt : (⟪ocTail c1, ocTail c2⟫ : V) < m := by
    rw [hm]; exact pair_lt_pair (ocTail_lt e1 n1 r1) (ocTail_lt e2 n2 r2)
  have hexple : (⟪ocExp c1, ocExp c2⟫ : V) ≤ M := le_iff_lt_succ.mpr (hM ▸ hexplt)
  have htaille : (⟪ocTail c1, ocTail c2⟫ : V) ≤ M := le_iff_lt_succ.mpr (hM ▸ htaillt)
  rw [icmp, ← hm, key, icmpNext, hpi1, hpi2]
  simp only [hpos1.ne', hpos2.ne', if_false]
  rw [icmpMain, hpi1, hpi2,
    znth_icmpTable_eq_icmp M _ hexple, znth_icmpTable_eq_icmp M _ htaille]
  simp only [pi₁_pair, pi₂_pair, ocExp_ocOadd, ocCoeff_ocOadd, ocTail_ocOadd, hc1, hc2]



/-! ## Internal `NF` predicate `isNF` (CNF well-formedness flag)

`isNF c` (`isNFb c = 1`) holds iff the code `c` is a valid Cantor-normal-form notation: positive
coefficients, NF sub-exponent and tail, and the tail's leading exponent strictly below the head's
(`icmp (ocExp r) e = 0`). Built as a `0/1` flag via a course-of-values table (product of four
definable indicator flags, so the step stays `𝚺₁` with no negated existentials). The recursion
`isNF_ocOadd` is the form the order-reflection and `βₖ`-construction consume. -/


/-- `0/1` indicator that `a ≠ 0`. -/
noncomputable def nzIndic (a : V) : V := if a = 0 then 0 else 1

def _root_.LO.FirstOrder.Arithmetic.nzIndicDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y a. (a = 0 ∧ y = 0) ∨ (a ≠ 0 ∧ y = 1)”

instance nzIndic_defined : 𝚺₀-Function₁ (nzIndic : V → V) via nzIndicDef := .mk fun v ↦ by
  simp [nzIndicDef, nzIndic]; by_cases h : v 1 = 0 <;> simp [h]

instance nzIndic_definable : 𝚺₀-Function₁ (nzIndic : V → V) := nzIndic_defined.to_definable
instance nzIndic_definable' (Γ) : Γ-Function₁ (nzIndic : V → V) := nzIndic_definable.of_zero

/-- `0/1` indicator that `icmp a b = 0` (i.e. `a ≺ b`). -/
noncomputable def ltIndic (a b : V) : V := if icmp a b = 0 then 1 else 0

def _root_.LO.FirstOrder.Arithmetic.ltIndicDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b. ∃ c, !icmpDef c a b ∧ ((c = 0 ∧ y = 1) ∨ (c ≠ 0 ∧ y = 0))”

instance ltIndic_defined : 𝚺₁-Function₂ (ltIndic : V → V → V) via ltIndicDef := .mk fun v ↦ by
  simp [ltIndicDef, ltIndic, icmp_defined.iff]
  by_cases h : icmp (v 1) (v 2) = 0 <;> simp [h]

instance ltIndic_definable : 𝚺₁-Function₂ (ltIndic : V → V → V) := ltIndic_defined.to_definable

/-- The tail-exponent condition flag for `c` (an `oadd`-code): `1` if the tail is `0` or its leading
exponent is `≺` `c`'s exponent, else `0`. -/
noncomputable def tailOk (c : V) : V :=
  if ocTail c = 0 then 1 else ltIndic (ocExp (ocTail c)) (ocExp c)

def _root_.LO.FirstOrder.Arithmetic.tailOkDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ t, !sndIdxDef t c ∧
    ((t = 0 ∧ y = 1) ∨ (t ≠ 0 ∧ ∃ et, !ocExpDef et t ∧ ∃ e, !ocExpDef e c ∧ !ltIndicDef y et e))”

instance tailOk_defined : 𝚺₁-Function₁ (tailOk : V → V) via tailOkDef := .mk fun v ↦ by
  simp [tailOkDef, tailOk, ocTail, sndIdx_defined.iff, ocExp_defined.iff, ltIndic_defined.iff]
  by_cases h : sndIdx (v 1) = 0 <;> simp [h]

instance tailOk_definable : 𝚺₁-Function₁ (tailOk : V → V) := tailOk_defined.to_definable

/-- Table step of `isNFb` (only ever evaluated at codes `c > 0`, since position `0` is seeded): the
product of the four CNF well-formedness flags — coefficient positive, exponent NF, tail NF, tail
exponent below `c`'s exponent (`znth s e`, `znth s r` read the NF flags of the subcodes). -/
noncomputable def isNFbNext (c s : V) : V :=
  nzIndic (ocCoeff c) * znth s (ocExp c) * znth s (ocTail c) * tailOk c

def _root_.LO.FirstOrder.Arithmetic.isNFbNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c s.
    ∃ co, !ocCoeffDef co c ∧ ∃ nc, !nzIndicDef nc co ∧
    ∃ e, !ocExpDef e c ∧ ∃ se, !znthDef se s e ∧
    ∃ t, !sndIdxDef t c ∧ ∃ st, !znthDef st s t ∧
    ∃ tk, !tailOkDef tk c ∧
    y = nc * se * st * tk”

instance isNFbNext_defined : 𝚺₁-Function₂ (isNFbNext : V → V → V) via isNFbNextDef := .mk fun v ↦ by
  simp [isNFbNextDef, isNFbNext, ocCoeff_defined.iff, nzIndic_defined.iff, ocExp_defined.iff,
    ocTail, sndIdx_defined.iff, znth_defined.iff, tailOk_defined.iff]

instance isNFbNext_definable : 𝚺₁-Function₂ (isNFbNext : V → V → V) := isNFbNext_defined.to_definable

/-! ### Indicator value lemmas -/

@[simp] lemma nzIndic_eq_one_iff (a : V) : nzIndic a = 1 ↔ a ≠ 0 := by
  unfold nzIndic; by_cases h : a = 0 <;> simp [h]

lemma nzIndic_le_one (a : V) : nzIndic a ≤ 1 := by
  unfold nzIndic; by_cases h : a = 0 <;> simp [h]

@[simp] lemma ltIndic_eq_one_iff (a b : V) : ltIndic a b = 1 ↔ icmp a b = 0 := by
  unfold ltIndic; by_cases h : icmp a b = 0 <;> simp [h]

lemma ltIndic_le_one (a b : V) : ltIndic a b ≤ 1 := by
  unfold ltIndic; by_cases h : icmp a b = 0 <;> simp [h]

lemma tailOk_le_one (c : V) : tailOk c ≤ 1 := by
  unfold tailOk; by_cases h : ocTail c = 0 <;> simp [h, ltIndic_le_one]

lemma tailOk_ocOadd (ec n rc : V) :
    tailOk (ocOadd ec n rc) = if rc = 0 then 1 else ltIndic (ocExp rc) ec := by
  unfold tailOk; rw [ocTail_ocOadd, ocExp_ocOadd]

/-! ### The `isNFb` table -/

def isNFbTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 1”
  succ := .mkSigma “y ih n. ∃ v, !isNFbNextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def isNFbTable.construction : PR.Construction V isNFbTable.blueprint where
  zero := fun _ ↦ !⟦1⟧
  succ := fun _ n ih ↦ seqCons ih (isNFbNext (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [isNFbTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [isNFbTable.blueprint, isNFbNext_defined.iff, seqCons_defined.iff]

noncomputable def isNFbTable (n : V) : V := isNFbTable.construction.result ![] n

@[simp] lemma isNFbTable_zero : isNFbTable (0 : V) = !⟦1⟧ := by
  simp [isNFbTable, isNFbTable.construction]

@[simp] lemma isNFbTable_succ (n : V) :
    isNFbTable (n + 1) = seqCons (isNFbTable n) (isNFbNext (n + 1) (isNFbTable n)) := by
  simp [isNFbTable, isNFbTable.construction]

/-- **Internal CNF well-formedness flag** (`0/1`): `1` iff the code `c` is a valid CNF notation. -/
noncomputable def isNFb (c : V) : V := znth (isNFbTable c) c

/-- **Internal `NF` predicate** on codes inside `V`. -/
def isNF (c : V) : Prop := isNFb c = 1

def _root_.LO.FirstOrder.Arithmetic.isNFbTableDef : 𝚺₁.Semisentence 2 :=
  isNFbTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance isNFbTable_defined : 𝚺₁-Function₁ (isNFbTable : V → V) via isNFbTableDef := .mk
  fun v ↦ by simp [isNFbTable.construction.result_defined_iff, isNFbTableDef]; rfl

instance isNFbTable_definable : 𝚺₁-Function₁ (isNFbTable : V → V) := isNFbTable_defined.to_definable
instance isNFbTable_definable' (Γ) (m : ℕ) :
    Γ-[m + 1]-Function₁ (isNFbTable : V → V) :=
  isNFbTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.isNFbDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ t, !isNFbTableDef t c ∧ !znthDef y t c”

instance isNFb_defined : 𝚺₁-Function₁ (isNFb : V → V) via isNFbDef := .mk fun v ↦ by
  simp [isNFbDef, isNFb, isNFbTable_defined.iff, znth_defined.iff]

instance isNFb_definable : 𝚺₁-Function₁ (isNFb : V → V) := isNFb_defined.to_definable
instance isNFb_definable' (Γ) (m : ℕ) :
    Γ-[m + 1]-Function₁ (isNFb : V → V) :=
  isNFb_definable.of_sigmaOne

instance isNF_definable (Γ) (m : ℕ) :
    Γ-[m + 1]-Predicate (isNF : V → Prop) := by
  unfold isNF; definability

/-! ### Structural correctness of the `isNFb` table -/

private lemma def_isNFbTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ isNFbTable (v i)) :=
  DefinableFunction₁.comp (F := isNFbTable) (DefinableFunction.var i)

private lemma def_isNFb {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ isNFb (v i)) :=
  DefinableFunction₁.comp (F := isNFb) (DefinableFunction.var i)

@[simp] lemma isNFbTable_seq (n : V) : Seq (isNFbTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_isNFbTable 0)
  case zero => simp
  case succ n ih => rw [isNFbTable_succ]; exact ih.seqCons _

@[simp] lemma isNFbTable_lh (n : V) : lh (isNFbTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_isNFbTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [isNFbTable_succ, Seq.lh_seqCons _ (isNFbTable_seq n), ih]

lemma znth_isNFbTable_succ {n k : V} (hk : k < n + 1) :
    znth (isNFbTable (n + 1)) k = znth (isNFbTable n) k := by
  rw [isNFbTable_succ]
  exact znth_seqCons_of_lt (isNFbTable_seq n) _ (by rw [isNFbTable_lh]; exact hk)

lemma znth_isNFbTable_eq_isNFb : ∀ N : V, ∀ k ≤ N, znth (isNFbTable N) k = isNFb k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_isNFbTable 1) (DefinableFunction.var 0))
      (def_isNFb 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_isNFbTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

@[simp] lemma isNFb_zero : isNFb (0 : V) = 1 := by
  simp only [isNFb, isNFbTable_zero]
  exact (singleton_seq 1).znth_eq_of_mem ((mem_singleton_seq_iff 1 1).mpr rfl)

@[simp] lemma isNF_zero : isNF (0 : V) := by simp [isNF]

/-- **The internal `isNFb` recursion** on codes. -/
lemma isNFb_ocOadd (ec n rc : V) :
    isNFb (ocOadd ec n rc)
      = nzIndic n * isNFb ec * isNFb rc * tailOk (ocOadd ec n rc) := by
  set c := ocOadd ec n rc with hc
  have hpos : 0 < c := ocOadd_pos ec n rc
  obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
    ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (isNFbTable c) c = isNFbNext c (isNFbTable M) := by
    rw [hM, isNFbTable_succ]
    have := znth_seqCons_self (isNFbTable_seq M) (isNFbNext (M + 1) (isNFbTable M))
    rwa [isNFbTable_lh] at this
  have hexp : ocExp c ≤ M := le_iff_lt_succ.mpr (hM ▸ ocExp_lt ec n rc)
  have htail : ocTail c ≤ M := le_iff_lt_succ.mpr (hM ▸ ocTail_lt ec n rc)
  rw [isNFb, key, isNFbNext,
    znth_isNFbTable_eq_isNFb M (ocExp c) hexp, znth_isNFbTable_eq_isNFb M (ocTail c) htail,
    ocCoeff_ocOadd, ocExp_ocOadd, ocTail_ocOadd]

/-- `isNFb` is a `0/1` flag. -/
lemma isNFb_le_one (c : V) : isNFb c ≤ 1 := by
  induction c using ISigma1.sigma1_order_induction
  · exact Definable.comp₂ (def_isNFb 0) (by definability)
  case ind c ih =>
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
        ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hc))).symm⟩
      have key : znth (isNFbTable c) c = isNFbNext c (isNFbTable M) := by
        rw [hM, isNFbTable_succ]
        have := znth_seqCons_self (isNFbTable_seq M) (isNFbNext (M + 1) (isNFbTable M))
        rwa [isNFbTable_lh] at this
      have hexp : ocExp c ≤ M := by
        have := ocExp_lt_of_pos (pos_iff_ne_zero.mpr hc); exact le_iff_lt_succ.mpr (hM ▸ this)
      have htail : ocTail c ≤ M := by
        have := ocTail_lt_of_pos (pos_iff_ne_zero.mpr hc); exact le_iff_lt_succ.mpr (hM ▸ this)
      have hse : isNFb (ocExp c) ≤ 1 := ih _ (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hc))
      have hst : isNFb (ocTail c) ≤ 1 := ih _ (ocTail_lt_of_pos (pos_iff_ne_zero.mpr hc))
      rw [isNFb, key, isNFbNext,
        znth_isNFbTable_eq_isNFb M (ocExp c) hexp, znth_isNFbTable_eq_isNFb M (ocTail c) htail]
      have h1 := nzIndic_le_one (ocCoeff c)
      have h4 := tailOk_le_one c
      calc nzIndic (ocCoeff c) * isNFb (ocExp c) * isNFb (ocTail c) * tailOk c
          ≤ 1 * 1 * 1 * 1 := by gcongr
        _ = 1 := by simp

private lemma prod4_eq_one {a b c d : V} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1) :
    a * b * c * d = 1 ↔ a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  constructor
  · intro h
    have ka : a * b * c * d ≤ a := by
      calc a * b * c * d ≤ a * 1 * 1 * 1 := by gcongr
        _ = a := by simp
    have kb : a * b * c * d ≤ b := by
      calc a * b * c * d ≤ 1 * b * 1 * 1 := by gcongr
        _ = b := by simp
    have kc : a * b * c * d ≤ c := by
      calc a * b * c * d ≤ 1 * 1 * c * 1 := by gcongr
        _ = c := by simp
    have kd : a * b * c * d ≤ d := by
      calc a * b * c * d ≤ 1 * 1 * 1 * d := by gcongr
        _ = d := by simp
    refine ⟨le_antisymm ha (h ▸ ka), le_antisymm hb (h ▸ kb),
      le_antisymm hc (h ▸ kc), le_antisymm hd (h ▸ kd)⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; simp

lemma tailFlag_eq_one_iff (ec rc : V) :
    (if rc = 0 then (1 : V) else ltIndic (ocExp rc) ec) = 1
      ↔ (rc = 0 ∨ icmp (ocExp rc) ec = 0) := by
  by_cases h : rc = 0 <;> simp [h]

/-- **The internal `NF` recursion** (the form the order-reflection and `βₖ`-construction consume). -/
lemma isNF_ocOadd (ec n rc : V) :
    isNF (ocOadd ec n rc) ↔
      n ≠ 0 ∧ isNF ec ∧ isNF rc ∧ (rc = 0 ∨ icmp (ocExp rc) ec = 0) := by
  unfold isNF
  rw [isNFb_ocOadd, tailOk_ocOadd,
    prod4_eq_one (nzIndic_le_one n) (isNFb_le_one ec) (isNFb_le_one rc)
      (by by_cases h : rc = 0 <;> simp [h, ltIndic_le_one]),
    nzIndic_eq_one_iff, tailFlag_eq_one_iff]


/-! ## Order-reflection: `ievalNat b` reflects the CNF (`icmp`) order (Rathjen 2.3(iii))

The descent's `ineq6_step` consumes `o ≺ p ⇒ ievalNat b o < ievalNat b p` on the `isNF`/`iCanon b`
domain. Proved digit-direct (no ordinals, so it internalizes): the value-bound `TB` and the
monotonicity `MONO` are mutually recursive (the leading term dominates iff the tail is bounded by the
leading power, which needs monotonicity at the exponents), so both are carried in one strong induction
on a single code measure. `icmp_eq_imp_eq` (a separate induction) supplies the `eq` case. -/

/-- **Destructor**: a positive code is the `ocOadd` of its decoded parts. -/
lemma ocOadd_destruct {c : V} (hc : c ≠ 0) :
    ocOadd (ocExp c) (ocCoeff c) (ocTail c) = c := by
  have hpos : 0 < c := pos_iff_ne_zero.mpr hc
  unfold ocOadd ocExp ocCoeff ocTail fstIdx sndIdx
  rw [pair_unpair, pair_unpair]
  exact sub_add_self_of_le (pos_iff_one_le.mp hpos)

/-! ### `thenV` / `cmpV` value lemmas -/

lemma thenV_eq_one {a b : V} : thenV a b = 1 ↔ a = 1 ∧ b = 1 := by
  unfold thenV; by_cases h : a = 1 <;> simp [h]

lemma thenV_eq_zero {a b : V} : thenV a b = 0 ↔ a = 0 ∨ (a = 1 ∧ b = 0) := by
  unfold thenV; by_cases h : a = 1 <;> simp [h]

lemma cmpV_eq_zero {a b : V} : cmpV a b = 0 ↔ a < b := by
  unfold cmpV
  by_cases h : a < b
  · simp [h]
  · simp only [h]; by_cases h2 : a = b <;> simp [h2]

lemma cmpV_eq_one {a b : V} : cmpV a b = 1 ↔ a = b := by
  unfold cmpV
  by_cases h : a < b
  · simp only [if_pos h]
    constructor
    · intro h0; simp at h0
    · rintro rfl; exact absurd h (_root_.lt_irrefl a)
  · by_cases h2 : a = b
    · subst h2; simp
    · simp [h, h2]
def _root_.LO.FirstOrder.Arithmetic.ocOaddDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y ec n rc. ∃ p, !pairDef p ec n ∧ ∃ q, !pairDef q p rc ∧ y = q + 1”

instance ocOadd_defined : 𝚺₁-Function₃ (ocOadd : V → V → V → V) via ocOaddDef := .mk fun v ↦ by
  simp [ocOaddDef, ocOadd, pair_defined.iff]

instance ocOadd_definable : 𝚺₁-Function₃ (ocOadd : V → V → V → V) := ocOadd_defined.to_definable

/-- Table step of `iadd` at first-argument index `c` (param `b`, table `s` of `iadd · b`). -/
noncomputable def iaddNext (b c s : V) : V :=
  if c = 0 then b
  else if b = 0 then c
  else if icmp (ocExp c) (ocExp b) = 0 then b
  else if icmp (ocExp c) (ocExp b) = 1 then
    ocOadd (ocExp c) (ocCoeff c + ocCoeff b) (ocTail b)
  else ocOadd (ocExp c) (ocCoeff c) (znth s (ocTail c))

def _root_.LO.FirstOrder.Arithmetic.iaddNextDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y b c s.
    (c = 0 ∧ y = b)
  ∨ (c ≠ 0 ∧ b = 0 ∧ y = c)
  ∨ (c ≠ 0 ∧ b ≠ 0 ∧ ∃ ec, !ocExpDef ec c ∧ ∃ eb, !ocExpDef eb b ∧
       ∃ cm, !icmpDef cm ec eb ∧
       ( (cm = 0 ∧ y = b)
       ∨ (cm = 1 ∧ ∃ cc, !ocCoeffDef cc c ∧ ∃ cb, !ocCoeffDef cb b ∧ ∃ tb, !sndIdxDef tb b ∧
            !ocOaddDef y ec (cc + cb) tb)
       ∨ (cm ≠ 0 ∧ cm ≠ 1 ∧ ∃ cc, !ocCoeffDef cc c ∧ ∃ tc, !sndIdxDef tc c ∧
            ∃ st, !znthDef st s tc ∧ !ocOaddDef y ec cc st) ) )”

instance iaddNext_defined : 𝚺₁-Function₃ (iaddNext : V → V → V → V) via iaddNextDef := .mk
  fun v ↦ by
  simp [iaddNextDef, iaddNext, ocExp_defined.iff, ocCoeff_defined.iff, ocTail,
    sndIdx_defined.iff, icmp_defined.iff, znth_defined.iff, ocOadd_defined.iff]
  by_cases hc : v 2 = 0
  · simp [hc]
  · by_cases hb : v 1 = 0
    · simp [hc, hb]
    · by_cases h0 : icmp (ocExp (v 2)) (ocExp (v 1)) = 0
      · simp [hc, hb, h0]
      · by_cases h1 : icmp (ocExp (v 2)) (ocExp (v 1)) = 1
        · simp [hc, hb, h1]
        · simp [hc, hb, h0, h1]

instance iaddNext_definable : 𝚺₁-Function₃ (iaddNext : V → V → V → V) := iaddNext_defined.to_definable

/-- Blueprint for the `iadd` table (parameter = second summand `b`). -/
def iaddTable.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. !mkSeq₁Def y x”
  succ := .mkSigma “y ih n x. ∃ v, !iaddNextDef v x (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def iaddTable.construction : PR.Construction V iaddTable.blueprint where
  zero := fun x ↦ !⟦x 0⟧
  succ := fun x n ih ↦ seqCons ih (iaddNext (x 0) (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [iaddTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [iaddTable.blueprint, iaddNext_defined.iff, seqCons_defined.iff]

/-- **The `iadd` table**: `iaddTable b n = ⟨iadd 0 b,…,iadd n b⟩`. -/
noncomputable def iaddTable (b n : V) : V := iaddTable.construction.result ![b] n

@[simp] lemma iaddTable_zero (b : V) : iaddTable b 0 = !⟦b⟧ := by
  simp [iaddTable, iaddTable.construction]

@[simp] lemma iaddTable_succ (b n : V) :
    iaddTable b (n + 1) = seqCons (iaddTable b n) (iaddNext b (n + 1) (iaddTable b n)) := by
  simp [iaddTable, iaddTable.construction]

/-- **Internal CNF ordinal addition** `a + b` inside `V`: the `a`-th entry of the table. -/
noncomputable def iadd (a b : V) : V := znth (iaddTable b a) a

def _root_.LO.FirstOrder.Arithmetic.iaddTableDef : 𝚺₁.Semisentence 3 :=
  iaddTable.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance iaddTable_defined : 𝚺₁-Function₂ (iaddTable : V → V → V) via iaddTableDef := .mk
  fun v ↦ by simp [iaddTable.construction.result_defined_iff, iaddTableDef]; rfl

instance iaddTable_definable : 𝚺₁-Function₂ (iaddTable : V → V → V) := iaddTable_defined.to_definable
instance iaddTable_definable' (Γ) (m : ℕ) :
    Γ-[m + 1]-Function₂ (iaddTable : V → V → V) :=
  iaddTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.iaddDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b. ∃ t, !iaddTableDef t b a ∧ !znthDef y t a”

instance iadd_defined : 𝚺₁-Function₂ (iadd : V → V → V) via iaddDef := .mk fun v ↦ by
  simp [iaddDef, iadd, iaddTable_defined.iff, znth_defined.iff]

instance iadd_definable : 𝚺₁-Function₂ (iadd : V → V → V) := iadd_defined.to_definable
instance iadd_definable' (Γ) (m : ℕ) :
    Γ-[m + 1]-Function₂ (iadd : V → V → V) :=
  iadd_definable.of_sigmaOne

/-! ### Structural correctness of `iadd` -/

private lemma def_iaddTable {k} (b : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iaddTable b (v i)) :=
  DefinableFunction₂.comp (F := iaddTable) (DefinableFunction.const b) (DefinableFunction.var i)

private lemma def_iadd {k} (b : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iadd (v i) b) :=
  DefinableFunction₂.comp (F := iadd) (DefinableFunction.var i) (DefinableFunction.const b)

@[simp] lemma iaddTable_seq (b n : V) : Seq (iaddTable b n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_iaddTable b 0)
  case zero => simp
  case succ n ih => rw [iaddTable_succ]; exact ih.seqCons _

@[simp] lemma iaddTable_lh (b n : V) : lh (iaddTable b n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_iaddTable b 0)) (by definability)
  case zero => simp
  case succ n ih => rw [iaddTable_succ, Seq.lh_seqCons _ (iaddTable_seq b n), ih]

lemma znth_iaddTable_succ {b n k : V} (hk : k < n + 1) :
    znth (iaddTable b (n + 1)) k = znth (iaddTable b n) k := by
  rw [iaddTable_succ]
  exact znth_seqCons_of_lt (iaddTable_seq b n) _ (by rw [iaddTable_lh]; exact hk)

lemma znth_iaddTable_eq_iadd (b : V) : ∀ N : V, ∀ k ≤ N, znth (iaddTable b N) k = iadd k b := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_iaddTable b 1) (DefinableFunction.var 0))
      (def_iadd b 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_iaddTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

@[simp] lemma iadd_zero_left (b : V) : iadd 0 b = b := by
  simp only [iadd, iaddTable_zero]
  exact (singleton_seq b).znth_eq_of_mem ((mem_singleton_seq_iff b b).mpr rfl)

/-- **The internal CNF-addition recursion**: `iadd (oadd e n r) b` evaluates the three-way leading
exponent comparison (the `gt` branch recursing into `iadd r b`). -/
lemma iadd_ocOadd (ec n rc b : V) :
    iadd (ocOadd ec n rc) b =
      (if b = 0 then ocOadd ec n rc
       else if icmp ec (ocExp b) = 0 then b
       else if icmp ec (ocExp b) = 1 then ocOadd ec (n + ocCoeff b) (ocTail b)
       else ocOadd ec n (iadd rc b)) := by
  set c := ocOadd ec n rc with hc
  have hpos : 0 < c := ocOadd_pos ec n rc
  obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
    ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (iaddTable b c) c = iaddNext b c (iaddTable b M) := by
    rw [hM, iaddTable_succ]
    have := znth_seqCons_self (iaddTable_seq b M) (iaddNext b (M + 1) (iaddTable b M))
    rwa [iaddTable_lh] at this
  have htail : ocTail c ≤ M := by
    have := ocTail_lt ec n rc; rw [← hc] at this; exact le_iff_lt_succ.mpr (hM ▸ this)
  have hcne : c ≠ 0 := hpos.ne'
  rw [iadd, key, iaddNext, if_neg hcne]
  rw [znth_iaddTable_eq_iadd b M (ocTail c) htail, ocExp_ocOadd, ocCoeff_ocOadd, ocTail_ocOadd]

/-! ### Structural laws for internal comparison -/

private lemma code_lt_of_exp {e n r w : V} (h : ocOadd e n r ≤ w) : e < w := by
  have : e < ocOadd e n r := by
    have h' := ocExp_lt e n r
    rwa [ocExp_ocOadd] at h'
  exact lt_of_lt_of_le this h

private lemma code_lt_of_tail {e n r w : V} (h : ocOadd e n r ≤ w) : r < w := by
  have : r < ocOadd e n r := by
    have h' := ocTail_lt e n r
    rwa [ocTail_ocOadd] at h'
  exact lt_of_lt_of_le this h

/-- An internal comparison returning the equality code reflects equality of codes. -/
theorem icmp_eq_imp_eq : ∀ w : V, ∀ a ≤ w, ∀ c ≤ w, icmp a c = 1 → a = c := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro a haw c hcw hcmp
    rcases eq_or_ne a 0 with rfl | ha
    · rcases eq_or_ne c 0 with rfl | hc
      · rfl
      · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, c = ocOadd e n r :=
          ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
        rw [icmp_zero_ocOadd] at hcmp
        exact absurd hcmp zero_ne_one
    · rcases eq_or_ne c 0 with rfl | hc
      · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, a = ocOadd e n r :=
          ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
        rw [icmp_ocOadd_zero] at hcmp
        exact absurd hcmp (one_lt_two).ne'
      · obtain ⟨e1, n1, r1, rfl⟩ : ∃ e n r, a = ocOadd e n r :=
          ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
        obtain ⟨e2, n2, r2, rfl⟩ : ∃ e n r, c = ocOadd e n r :=
          ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
        rw [icmp_ocOadd, thenV_eq_one, thenV_eq_one] at hcmp
        obtain ⟨he, hn, hr⟩ := hcmp
        have he1w : e1 < w := code_lt_of_exp haw
        have he2w : e2 < w := code_lt_of_exp hcw
        have hr1w : r1 < w := code_lt_of_tail haw
        have hr2w : r2 < w := code_lt_of_tail hcw
        have hee : e1 = e2 :=
          ih (max e1 e2) (max_lt he1w he2w) e1 (le_max_left _ _) e2 (le_max_right _ _) he
        have hnn : n1 = n2 := cmpV_eq_one.mp hn
        have hrr : r1 = r2 :=
          ih (max r1 r2) (max_lt hr1w hr2w) r1 (le_max_left _ _) r2 (le_max_right _ _) hr
        rw [hee, hnn, hrr]

@[simp] lemma cmpV_self (a : V) : cmpV a a = 1 := by simp [cmpV]

/-- Internal comparison is reflexive, uniformly below an induction bound. -/
lemma icmp_self : ∀ w : V, ∀ a ≤ w, icmp a a = 1 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro a haw
    rcases eq_or_ne a 0 with rfl | ha
    · exact icmp_zero_zero
    · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, a = ocOadd e n r :=
        ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
      have he_lt : e < w := lt_of_lt_of_le (by
        have h := ocExp_lt e n r
        rwa [ocExp_ocOadd] at h) haw
      have hr_lt : r < w := lt_of_lt_of_le (by
        have h := ocTail_lt e n r
        rwa [ocTail_ocOadd] at h) haw
      rw [icmp_ocOadd, ih e he_lt e le_rfl, cmpV_self, ih r hr_lt r le_rfl]
      simp [thenV]

lemma icmp_zero_pos {c : V} (hc : c ≠ 0) : icmp 0 c = 0 := by
  obtain ⟨e, n, r, rfl⟩ : ∃ e n r, c = ocOadd e n r :=
    ⟨_, _, _, (ocOadd_destruct hc).symm⟩
  exact icmp_zero_ocOadd e n r

lemma icmp_pos_zero {c : V} (hc : c ≠ 0) : icmp c 0 = 2 := by
  obtain ⟨e, n, r, rfl⟩ : ∃ e n r, c = ocOadd e n r :=
    ⟨_, _, _, (ocOadd_destruct hc).symm⟩
  exact icmp_ocOadd_zero e n r

lemma icmp_pos_pos {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) :
    icmp a b = thenV (icmp (ocExp a) (ocExp b))
      (thenV (cmpV (ocCoeff a) (ocCoeff b)) (icmp (ocTail a) (ocTail b))) := by
  obtain ⟨ea, ca, ta, rfl⟩ : ∃ x y z, a = ocOadd x y z :=
    ⟨_, _, _, (ocOadd_destruct ha).symm⟩
  obtain ⟨eb, cb, tb, rfl⟩ : ∃ x y z, b = ocOadd x y z :=
    ⟨_, _, _, (ocOadd_destruct hb).symm⟩
  rw [icmp_ocOadd]
  simp only [ocExp_ocOadd, ocCoeff_ocOadd, ocTail_ocOadd]

private lemma icmp_swap_aux : ∀ m : V,
    icmp (π₂ m) (π₁ m) = oswap (icmp (π₁ m) (π₂ m)) := by
  intro m
  induction m using ISigma1.sigma1_order_induction
  · definability
  case ind m ih =>
    have hm : (⟪π₁ m, π₂ m⟫ : V) = m := pair_unpair m
    rcases eq_or_ne (π₁ m) 0 with ha | ha
    · rcases eq_or_ne (π₂ m) 0 with hb | hb
      · rw [ha, hb, icmp_zero_zero]
        simp
      · rw [ha, icmp_zero_pos hb, icmp_pos_zero hb]
        simp
    · rcases eq_or_ne (π₂ m) 0 with hb | hb
      · rw [hb, icmp_pos_zero ha, icmp_zero_pos ha]
        simp
      · rw [icmp_pos_pos ha hb, icmp_pos_pos hb ha]
        have hexp : (⟪ocExp (π₁ m), ocExp (π₂ m)⟫ : V) < m := by
          have h := pair_lt_pair (ocExp_lt_of_pos (pos_iff_ne_zero.mpr ha))
            (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hb))
          rwa [hm] at h
        have htail : (⟪ocTail (π₁ m), ocTail (π₂ m)⟫ : V) < m := by
          have h := pair_lt_pair (ocTail_lt_of_pos (pos_iff_ne_zero.mpr ha))
            (ocTail_lt_of_pos (pos_iff_ne_zero.mpr hb))
          rwa [hm] at h
        have he := ih _ hexp
        have ht := ih _ htail
        simp only [pi₁_pair, pi₂_pair] at he ht
        rw [he, ht, cmpV_swap, oswap_thenV, oswap_thenV]

/-- Swapping comparison arguments swaps the less/greater result codes. -/
lemma icmp_swap (c1 c2 : V) : icmp c2 c1 = oswap (icmp c1 c2) := by
  have h := icmp_swap_aux ⟪c1, c2⟫
  simpa using h

private lemma cmpV_cases (a b : V) :
    cmpV a b = 0 ∨ cmpV a b = 1 ∨ cmpV a b = 2 := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact Or.inl (cmpV_eq_zero.mpr hab)
  · exact Or.inr (Or.inl (cmpV_eq_one.mpr hab))
  · refine Or.inr (Or.inr ?_)
    rw [cmpV, if_neg (not_lt.mpr hba.le), if_neg hba.ne']

private lemma thenV_cases_of {a b : V}
    (ha : a = 0 ∨ a = 1 ∨ a = 2)
    (hb : b = 0 ∨ b = 1 ∨ b = 2) :
    thenV a b = 0 ∨ thenV a b = 1 ∨ thenV a b = 2 := by
  unfold thenV
  by_cases h : a = 1
  · rw [if_pos h]
    exact hb
  · rw [if_neg h]
    exact ha

private lemma icmp_cases_aux : ∀ m : V,
    icmp (π₁ m) (π₂ m) = 0 ∨
      icmp (π₁ m) (π₂ m) = 1 ∨
      icmp (π₁ m) (π₂ m) = 2 := by
  intro m
  induction m using ISigma1.sigma1_order_induction
  · definability
  case ind m ih =>
    have hm : (⟪π₁ m, π₂ m⟫ : V) = m := pair_unpair m
    rcases eq_or_ne (π₁ m) 0 with ha | ha
    · rcases eq_or_ne (π₂ m) 0 with hb | hb
      · rw [ha, hb, icmp_zero_zero]
        exact Or.inr (Or.inl rfl)
      · rw [ha, icmp_zero_pos hb]
        exact Or.inl rfl
    · rcases eq_or_ne (π₂ m) 0 with hb | hb
      · rw [hb, icmp_pos_zero ha]
        exact Or.inr (Or.inr rfl)
      · rw [icmp_pos_pos ha hb]
        have hexp : (⟪ocExp (π₁ m), ocExp (π₂ m)⟫ : V) < m := by
          have h := pair_lt_pair (ocExp_lt_of_pos (pos_iff_ne_zero.mpr ha))
            (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hb))
          rwa [hm] at h
        have htail : (⟪ocTail (π₁ m), ocTail (π₂ m)⟫ : V) < m := by
          have h := pair_lt_pair (ocTail_lt_of_pos (pos_iff_ne_zero.mpr ha))
            (ocTail_lt_of_pos (pos_iff_ne_zero.mpr hb))
          rwa [hm] at h
        have he := ih _ hexp
        have ht := ih _ htail
        simp only [pi₁_pair, pi₂_pair] at he ht
        exact thenV_cases_of he (thenV_cases_of (cmpV_cases _ _) ht)

/-- Internal comparison always returns one of the three ordering codes. -/
lemma icmp_cases (a b : V) :
    icmp a b = 0 ∨ icmp a b = 1 ∨ icmp a b = 2 := by
  have h := icmp_cases_aux ⟪a, b⟫
  simpa using h

/-- If an internal comparison is neither equality nor greater-than, it is less-than. -/
lemma icmp_eq_zero_of_ne {a b : V} (h1 : icmp a b ≠ 1) (h2 : icmp a b ≠ 2) :
    icmp a b = 0 := by
  rcases icmp_cases a b with h | h | h
  · exact h
  · exact absurd h h1
  · exact absurd h h2

/-- The equality result is a right identity for lexicographic comparison. -/
@[simp] lemma thenV_one_right (a : V) : thenV a 1 = a := by
  unfold thenV
  by_cases h : a = 1 <;> simp [h]

/-- Internal comparison commutes with the single-term coding of `ω`-powers. -/
lemma icmp_omega_pow (α β : V) :
    icmp (ocOadd α 1 0) (ocOadd β 1 0) = icmp α β := by
  rw [icmp_ocOadd, cmpV_self, icmp_zero_zero, thenV_one_right, thenV_one_right]

/-- Strict internal comparison is transitive, uniformly below an induction bound. -/
lemma icmp_trans : ∀ w : V, ∀ a ≤ w, ∀ b ≤ w, ∀ c ≤ w,
    icmp a b = 0 → icmp b c = 0 → icmp a c = 0 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro a haw b hbw c hcw hab hbc
    rcases eq_or_ne a 0 with rfl | ha
    · have hc : c ≠ 0 := by
        rintro rfl
        rcases eq_or_ne b 0 with rfl | hb
        · rw [icmp_zero_zero] at hbc
          exact absurd hbc (by simp)
        · rw [icmp_pos_zero hb] at hbc
          exact absurd hbc (by simp)
      rw [icmp_zero_pos hc]
    · have hb : b ≠ 0 := by
        rintro rfl
        rw [icmp_pos_zero ha] at hab
        exact absurd hab (by simp)
      have hc : c ≠ 0 := by
        rintro rfl
        rw [icmp_pos_zero hb] at hbc
        exact absurd hbc (by simp)
      obtain ⟨ea, ca, ra, rfl⟩ : ∃ ea ca ra, a = ocOadd ea ca ra :=
        ⟨_, _, _, (ocOadd_destruct ha).symm⟩
      obtain ⟨eb, cb, rb, rfl⟩ : ∃ eb cb rb, b = ocOadd eb cb rb :=
        ⟨_, _, _, (ocOadd_destruct hb).symm⟩
      obtain ⟨ec, cc, rc, rfl⟩ : ∃ ec cc rc, c = ocOadd ec cc rc :=
        ⟨_, _, _, (ocOadd_destruct hc).symm⟩
      rw [icmp_ocOadd] at hab hbc ⊢
      have hea : ea < w := lt_of_lt_of_le (by simpa using ocExp_lt ea ca ra) haw
      have heb : eb < w := lt_of_lt_of_le (by simpa using ocExp_lt eb cb rb) hbw
      have hec : ec < w := lt_of_lt_of_le (by simpa using ocExp_lt ec cc rc) hcw
      have hra : ra < w := lt_of_lt_of_le (by simpa using ocTail_lt ea ca ra) haw
      have hrb : rb < w := lt_of_lt_of_le (by simpa using ocTail_lt eb cb rb) hbw
      have hrc : rc < w := lt_of_lt_of_le (by simpa using ocTail_lt ec cc rc) hcw
      have ihe : icmp ea eb = 0 → icmp eb ec = 0 → icmp ea ec = 0 := fun h1 h2 =>
        ih (max ea (max eb ec)) (max_lt hea (max_lt heb hec))
          ea (le_max_left _ _) eb (le_trans (le_max_left _ _) (le_max_right _ _))
          ec (le_trans (le_max_right _ _) (le_max_right _ _)) h1 h2
      have ihr : icmp ra rb = 0 → icmp rb rc = 0 → icmp ra rc = 0 := fun h1 h2 =>
        ih (max ra (max rb rc)) (max_lt hra (max_lt hrb hrc))
          ra (le_max_left _ _) rb (le_trans (le_max_left _ _) (le_max_right _ _))
          rc (le_trans (le_max_right _ _) (le_max_right _ _)) h1 h2
      rcases eq_or_ne (icmp ea eb) 0 with hEab | hEab
      · have hEac : icmp ea ec = 0 := by
          rcases eq_or_ne (icmp eb ec) 0 with hEbc | hEbc
          · exact ihe hEab hEbc
          · have hEbc1 : icmp eb ec = 1 := by
              rcases thenV_eq_zero.mp hbc with h | ⟨h, _⟩
              · exact absurd h hEbc
              · exact h
            have hee : eb = ec :=
              icmp_eq_imp_eq (max eb ec) eb (le_max_left _ _) ec (le_max_right _ _) hEbc1
            rw [← hee]
            exact hEab
        rw [hEac]
        simp [thenV]
      · have hEab1 : icmp ea eb = 1 := by
          rcases thenV_eq_zero.mp hab with h | ⟨h, _⟩
          · exact absurd h hEab
          · exact h
        have habCR : thenV (cmpV ca cb) (icmp ra rb) = 0 := by
          rcases thenV_eq_zero.mp hab with h | ⟨_, h⟩
          · exact absurd h hEab
          · exact h
        have heab : ea = eb :=
          icmp_eq_imp_eq (max ea eb) ea (le_max_left _ _) eb (le_max_right _ _) hEab1
        rcases eq_or_ne (icmp eb ec) 0 with hEbc | hEbc
        · have h : icmp ea ec = 0 := by
            rw [heab]
            exact hEbc
          rw [h]
          simp [thenV]
        · have hEbc1 : icmp eb ec = 1 := by
            rcases thenV_eq_zero.mp hbc with h | ⟨h, _⟩
            · exact absurd h hEbc
            · exact h
          have hbcCR : thenV (cmpV cb cc) (icmp rb rc) = 0 := by
            rcases thenV_eq_zero.mp hbc with h | ⟨_, h⟩
            · exact absurd h hEbc
            · exact h
          have hebc : eb = ec :=
            icmp_eq_imp_eq (max eb ec) eb (le_max_left _ _) ec (le_max_right _ _) hEbc1
          have hEac1 : icmp ea ec = 1 := by
            rw [heab, hebc]
            exact icmp_self ec ec le_rfl
          rw [hEac1, thenV_one_left]
          rcases eq_or_ne (cmpV ca cb) 0 with hCab | hCab
          · have hcacb : ca < cb := cmpV_eq_zero.mp hCab
            have hCac : cmpV ca cc = 0 := by
              rcases eq_or_ne (cmpV cb cc) 0 with hCbc | hCbc
              · exact cmpV_eq_zero.mpr (lt_trans hcacb (cmpV_eq_zero.mp hCbc))
              · have hCbc1 : cmpV cb cc = 1 := by
                  rcases thenV_eq_zero.mp hbcCR with h | ⟨h, _⟩
                  · exact absurd h hCbc
                  · exact h
                have hbe : cb = cc := cmpV_eq_one.mp hCbc1
                exact cmpV_eq_zero.mpr (by rw [← hbe]; exact hcacb)
            rw [hCac]
            simp [thenV]
          · have hCab1 : cmpV ca cb = 1 := by
              rcases thenV_eq_zero.mp habCR with h | ⟨h, _⟩
              · exact absurd h hCab
              · exact h
            have hRab : icmp ra rb = 0 := by
              rcases thenV_eq_zero.mp habCR with h | ⟨_, h⟩
              · exact absurd h hCab
              · exact h
            have hcacb : ca = cb := cmpV_eq_one.mp hCab1
            rcases eq_or_ne (cmpV cb cc) 0 with hCbc | hCbc
            · have hCac : cmpV ca cc = 0 :=
                cmpV_eq_zero.mpr (by rw [hcacb]; exact cmpV_eq_zero.mp hCbc)
              rw [hCac]
              simp [thenV]
            · have hCbc1 : cmpV cb cc = 1 := by
                rcases thenV_eq_zero.mp hbcCR with h | ⟨h, _⟩
                · exact absurd h hCbc
                · exact h
              have hRbc : icmp rb rc = 0 := by
                rcases thenV_eq_zero.mp hbcCR with h | ⟨_, h⟩
                · exact absurd h hCbc
                · exact h
              have hcbcc : cb = cc := cmpV_eq_one.mp hCbc1
              have hCac1 : cmpV ca cc = 1 := cmpV_eq_one.mpr (hcacb.trans hcbcc)
              rw [hCac1, thenV_one_left]
              exact ihr hRab hRbc

/-! ### Ordinary addition by a single omega block -/

@[simp] lemma iadd_zero_right (a : V) : iadd a 0 = a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, a = ocOadd e n r :=
      ⟨_, _, _, (ocOadd_destruct ha).symm⟩
    rw [iadd_ocOadd, if_pos rfl]

/-- Appending one more `omega^d` increments the coefficient of an existing
`omega^d` block.  This is the specialized associativity law needed by the
finite iteration in Gentzen's limit argument. -/
lemma iadd_omegaBlock_succ (d k : V) : ∀ b : V,
    iadd (iadd b (ocOadd d k 0)) (ocOadd d 1 0) =
      iadd b (ocOadd d (k + 1) 0) := by
  intro b
  induction b using ISigma1.sigma1_order_induction
  · definability
  case ind b ih =>
    rcases eq_or_ne b 0 with rfl | hb
    · rw [iadd_zero_left, iadd_ocOadd,
        if_neg (ocOadd_ne_zero d 1 0), ocExp_ocOadd,
        icmp_self d d le_rfl, if_neg _root_.one_ne_zero,
        if_pos rfl, ocCoeff_ocOadd, ocTail_ocOadd,
        iadd_zero_left]
    · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, b = ocOadd e n r :=
        ⟨_, _, _, (ocOadd_destruct hb).symm⟩
      have hr : r < ocOadd e n r := by
        simpa using ocTail_lt e n r
      rw [iadd_ocOadd, if_neg (ocOadd_ne_zero d k 0), ocExp_ocOadd]
      by_cases h0 : icmp e d = 0
      · rw [if_pos h0, iadd_ocOadd, if_neg (ocOadd_ne_zero d 1 0),
          ocExp_ocOadd, icmp_self d d le_rfl, if_neg _root_.one_ne_zero,
          if_pos rfl, ocCoeff_ocOadd, ocTail_ocOadd]
        rw [iadd_ocOadd, if_neg (ocOadd_ne_zero d (k + 1) 0),
          ocExp_ocOadd, if_pos h0]
      · rw [if_neg h0]
        by_cases h1 : icmp e d = 1
        · rw [if_pos h1, iadd_ocOadd, if_neg (ocOadd_ne_zero d 1 0),
            ocExp_ocOadd, h1, if_neg _root_.one_ne_zero, if_pos rfl,
            ocCoeff_ocOadd, ocTail_ocOadd]
          rw [iadd_ocOadd, if_neg (ocOadd_ne_zero d (k + 1) 0),
            ocExp_ocOadd, if_neg h0, if_pos h1]
          simp [add_assoc]
        · rw [if_neg h1, iadd_ocOadd, if_neg (ocOadd_ne_zero d 1 0),
            ocExp_ocOadd, if_neg h0, if_neg h1]
          rw [iadd_ocOadd, if_neg (ocOadd_ne_zero d (k + 1) 0),
            ocExp_ocOadd, if_neg h0, if_neg h1]
          rw [ih r hr]

lemma ocExp_iadd_omegaBlock (r d k : V) :
    ocExp (iadd r (ocOadd d k 0)) =
      if r = 0 then d else if icmp (ocExp r) d = 0 then d else ocExp r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · obtain ⟨e, n, t, rfl⟩ : ∃ e n t, r = ocOadd e n t :=
      ⟨_, _, _, (ocOadd_destruct hr).symm⟩
    rw [iadd_ocOadd, if_neg (ocOadd_ne_zero d k 0), ocExp_ocOadd]
    by_cases h0 : icmp e d = 0
    · simp [h0]
    · rw [if_neg h0]
      by_cases h1 : icmp e d = 1 <;> simp [h0, h1]

lemma isNF_omegaBlock {d k : V} (hd : isNF d) (hk : k ≠ 0) :
    isNF (ocOadd d k 0) := by
  exact (isNF_ocOadd d k 0).2 ⟨hk, hd, isNF_zero, Or.inl rfl⟩

/-- Ordinary addition of a positive single omega block preserves CNF normal
form on a normal left operand. -/
lemma isNF_iadd_omegaBlock {d k : V} (hd : isNF d) (hk : k ≠ 0) :
    ∀ b : V, isNF b → isNF (iadd b (ocOadd d k 0)) := by
  intro b
  induction b using ISigma1.sigma1_order_induction
  · definability
  case ind b ih =>
    intro hbNF
    rcases eq_or_ne b 0 with rfl | hb
    · simpa using isNF_omegaBlock hd hk
    · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, b = ocOadd e n r :=
        ⟨_, _, _, (ocOadd_destruct hb).symm⟩
      have hrlt : r < ocOadd e n r := by simpa using ocTail_lt e n r
      obtain ⟨hn, he, hrNF, hside⟩ := (isNF_ocOadd e n r).1 hbNF
      rw [iadd_ocOadd, if_neg (ocOadd_ne_zero d k 0), ocExp_ocOadd]
      by_cases h0 : icmp e d = 0
      · rw [if_pos h0]
        exact isNF_omegaBlock hd hk
      · rw [if_neg h0]
        by_cases h1 : icmp e d = 1
        · rw [if_pos h1, ocCoeff_ocOadd, ocTail_ocOadd, isNF_ocOadd]
          refine ⟨?_, he, isNF_zero, Or.inl rfl⟩
          exact (lt_of_lt_of_le (pos_iff_ne_zero.mpr hn)
            (le_add_right (le_refl n))).ne'
        · rw [if_neg h1, isNF_ocOadd]
          refine ⟨hn, he, ih r hrlt hrNF, Or.inr ?_⟩
          have h2 : icmp e d = 2 := by
            rcases icmp_cases e d with h | h | h
            · exact absurd h h0
            · exact absurd h h1
            · exact h
          have hde : icmp d e = 0 := by
            have hswap := icmp_swap e d
            rw [h2] at hswap
            simpa [oswap] using hswap
          rw [ocExp_iadd_omegaBlock]
          rcases eq_or_ne r 0 with rfl | hr
          · simp [hde]
          · rw [if_neg hr]
            by_cases hrd : icmp (ocExp r) d = 0
            · rw [if_pos hrd]
              exact hde
            · rw [if_neg hrd]
              exact hside.resolve_left hr

end OrdinalAnalysis.Gentzen.InternalONote
