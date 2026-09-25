/-
  The internal order `iltb` of the multi-level ϑ-notation, its normal-form predicate `isNFb`, and
  Wilken's domain condition `isDom`, generalizing ID1's comparison-table section of
  `ID1/Internal/Codes.lean`.

  **Why a new position encoding.** ID1 packs `(lt, all, ex)` into one value at position `⟪c1,c2⟫`:
  `all`/`ex` recurse structurally on one coordinate while the other stays fixed, fitting the same
  pair-order recursion as `lt`. Here the ϑ_k-ϑ_k clause needs `all_k`/`ex_k` for the *specific*
  `k` read off the two codes, so `all`/`ex` need an extra level dimension that `lt` does not; `lt`
  and `all_k`/`ex_k` stay mutually recursive but live over differently-shaped positions. The
  `tagP`/`tagL` combinators already in `CovTable.lean` (parity-based: `tagP c := c+c`, `tagL i c
  := ⟪i,c⟫+⟪i,c⟫+1`) have the right order properties but no cheap decode (recovering "is `X`
  even, and if so `X/2`" needs a half-extraction primitive not otherwise needed and not available
  off the shelf). So this file uses a *second*, pair-based tagging with the same order properties
  and a free decode via the already-available `fstIdx`/`sndIdx` (exactly `kind`'s own mechanism):
  `posP c := ⟪0,c⟫` ("plain code `c`"), `posL i c := ⟪1,⟪i,c⟫⟫` ("code `c` at level `i`"). This
  is a new definition in a new file, not an edit to the merged `CovTable.lean`.

  **The combined position** `⟪X,Y⟫`, decoded by `(fstIdx X, fstIdx Y)`:
  * `(0,0)`: `X = posP c1`, `Y = posP c2` — the table entry is `lt(c1,c2)`.
  * `(1,0)`: `X = posL k P`, `Y = posP Q` — the entry is `all_k(P,Q) := ∀ g ∈ E_k(P), g ≺ Q`.
  * `(0,1)`: `X = posP P`, `Y = posL k Q` — the entry is `ex_k(P,Q) := ∃ g ∈ E_k(Q), P ≼ g`.
  * `(1,1)`: unused (never read by a public accessor), `0`.

  **The step function** mirrors ID1's `ltStep`/`alStep`/`exStep` verbatim except: (i) `ltStep`'s
  "both principal" case now compares *levels* (`tcOmegaLev`/`tcLev`) with the four sub-cases
  `Omega-Omega`/`Omega-theta` (`i<j`), `theta-Omega` (`i≤j`), `theta-theta` (`i<j`, or `i=j` and
  the same-level clause reading `all_i`/`ex_i`, or `false` if `j<i`); (ii) `allStep`/`exStep` are
  indexed by the level `k` carried in the position tag (`E_k(theta j d)`: the plain slot when
  `j≤k`, recursion into `d` at the *same* level when `k<j`).

  **Well-foundedness, checked by hand once per clause** (never a case split on `Nat.pair`'s
  internal `if`, only `pair_lt_pair`/`_left`/`_right` on the outer `⟪X,Y⟫` and two crossing facts):
  * `posP`/`posL k` are each monotone in their code argument (`pair_lt_pair_right`).
  * `posP c < posL i c` (`posP_lt_posL`): `⟪0,c⟫ ≤ ⟪0,⟪i,c⟫⟫ < ⟪1,⟪i,c⟫⟫` (`le_pair_right`,
    `pair_lt_pair_left`) — used by `allStep`/`exStep`'s base case (`j ≤ k`) reading the plain slot
    from the leveled one, second coordinate unchanged.
  * `posL i c < posP (posL i c + 1)` (`posL_lt_posP_succ`), and `posL i c + 1 = tcTheta i c`
    *definitionally* (`posL i c = ⟪1,⟪i,c⟫⟫`) — used by `ltStep`'s ϑ_i-ϑ_i clause reading the
    leveled slots `posAll i a c2`/`posEx i c1 b` from the plain slot at `⟪posP c1, posP c2⟫` (with
    `c1 = tcTheta i a`, `c2 = tcTheta i b`), second/first coordinate unchanged respectively.
-/
import OrdinalAnalysis.IDn.Internal.Codes

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.ThetaWTerm
open OrdinalAnalysis.ID1.Internal (bor band beq borDef bandDef beqDef bor_defined band_defined
  beq_defined bor_eq_one band_eq_one beq_eq_one covVal covVal_unfold covVal_zero covVal_succ
  covValDef covVal_defined)

/-! ## The pair-based position tags -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The "plain code `c`" position tag. -/
noncomputable def posP (c : V) : V := ⟪0, c⟫

/-- The "code `c` at level `i`" position tag. -/
noncomputable def posL (i c : V) : V := ⟪1, ⟪i, c⟫⟫

def posPDef : 𝚺₁.Semisentence 2 := .mkSigma “y c. !pairDef y 0 c”

def posLDef : 𝚺₁.Semisentence 3 := .mkSigma “y i c. ∃ q, !pairDef q i c ∧ !pairDef y 1 q”

instance posP_defined : 𝚺₁-Function₁ (posP : V → V) via posPDef := .mk fun v ↦ by
  simp [posPDef, posP, pair_defined.iff]

instance posL_defined : 𝚺₁-Function₂ (posL : V → V → V) via posLDef := .mk fun v ↦ by
  simp [posLDef, posL, pair_defined.iff]

@[simp] lemma pi1_posP (c : V) : π₁ (posP c) = 0 := by simp [posP]

@[simp] lemma pi2_posP (c : V) : π₂ (posP c) = c := by simp [posP]

@[simp] lemma pi1_posL (i c : V) : π₁ (posL i c) = 1 := by simp [posL]

@[simp] lemma pi2_posL (i c : V) : π₂ (posL i c) = ⟪i, c⟫ := by simp [posL]

@[simp] lemma posP_lt_posP {a b : V} (h : a < b) : posP a < posP b :=
  pair_lt_pair_right 0 h

@[simp] lemma posP_inj {a b : V} : posP a = posP b ↔ a = b := by
  unfold posP
  constructor
  · intro h
    have h2 : π₂ (⟪0, a⟫ : V) = π₂ (⟪0, b⟫ : V) := by rw [h]
    simpa using h2
  · rintro rfl; rfl

@[simp] lemma posL_lt_posL_of_lt_right (i : V) {a b : V} (h : a < b) : posL i a < posL i b :=
  pair_lt_pair_right 1 (pair_lt_pair_right i h)

lemma posL_inj {i a b : V} (h : posL i a = posL i b) : a = b := by
  have h1 : (⟪i, a⟫ : V) = ⟪i, b⟫ := by
    have h2 : π₂ (posL i a) = π₂ (posL i b) := by rw [h]
    simpa using h2
  have h3 : π₂ (⟪i, a⟫ : V) = π₂ (⟪i, b⟫ : V) := by rw [h1]
  simpa using h3

/-- **The key crossing lemma, direction 1**: the plain code `c` sits below `c` tagged at any
level `i` — used to read `lt` from an `all_i`/`ex_i` base case. -/
lemma posP_lt_posL (i c : V) : posP c < posL i c := by
  have h : (⟪0, c⟫ : V) ≤ ⟪0, ⟪i, c⟫⟫ := pair_le_pair_right 0 (le_pair_right i c)
  have h2 : (⟪0, (⟪i, c⟫ : V)⟫ : V) < ⟪1, ⟪i, c⟫⟫ := pair_lt_pair_left (by norm_num) _
  exact lt_of_le_of_lt h h2

/-- **The key crossing lemma, direction 2**: `c` tagged at level `i` sits strictly below the
plain slot of `posL i c + 1` — and `posL i c + 1 = tcTheta i c` definitionally, so this is
exactly "read the leveled slot from the ϑ_i-ϑ_i clause of `lt`". -/
lemma posL_lt_posP_succ (i c : V) : posL i c < posP (posL i c + 1) := by
  have h1 : posL i c < posL i c + 1 := lt_add_one _
  have h2 : posL i c + 1 ≤ posP (posL i c + 1) := le_pair_right 0 _
  exact lt_of_lt_of_le h1 h2

lemma tcTheta_eq_posL_succ (i c : V) : tcTheta i c = posL i c + 1 := rfl

end Model

/-! ## The comparison table -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The `lt` flag stored in a table `s` at the plain position of `x`, `y`. -/
noncomputable def rdLt (s x y : V) : V := znth s ⟪posP x, posP y⟫

/-- The `all_k` flag stored in a table `s`: `∀ g ∈ E_k(x), g ≺ y`. -/
noncomputable def rdAll (s k x y : V) : V := znth s ⟪posL k x, posP y⟫

/-- The `ex_k` flag stored in a table `s`: `∃ g ∈ E_k(y), x ≼ g`. -/
noncomputable def rdEx (s k x y : V) : V := znth s ⟪posP x, posL k y⟫

def rdLtDef : 𝚺₁.Semisentence 4 := .mkSigma
  “r s x y. ∃ px, !posPDef px x ∧ ∃ py, !posPDef py y ∧ ∃ p, !pairDef p px py ∧ !znthDef r s p”

def rdAllDef : 𝚺₁.Semisentence 5 := .mkSigma
  “r s k x y. ∃ px, !posLDef px k x ∧ ∃ py, !posPDef py y ∧ ∃ p, !pairDef p px py ∧ !znthDef r s p”

def rdExDef : 𝚺₁.Semisentence 5 := .mkSigma
  “r s k x y. ∃ px, !posPDef px x ∧ ∃ py, !posLDef py k y ∧ ∃ p, !pairDef p px py ∧ !znthDef r s p”

instance rdLt_defined : 𝚺₁-Function₃ (rdLt : V → V → V → V) via rdLtDef := .mk fun v ↦ by
  simp [rdLtDef, rdLt, posP_defined.iff, pair_defined.iff, znth_defined.iff]

instance rdAll_defined : 𝚺₁-Function₄ (rdAll : V → V → V → V → V) via rdAllDef := .mk fun v ↦ by
  simp [rdAllDef, rdAll, posL_defined.iff, posP_defined.iff, pair_defined.iff, znth_defined.iff]

instance rdEx_defined : 𝚺₁-Function₄ (rdEx : V → V → V → V → V) via rdExDef := .mk fun v ↦ by
  simp [rdExDef, rdEx, posP_defined.iff, posL_defined.iff, pair_defined.iff, znth_defined.iff]

/-- The level of a principal code (`Omega` or `theta`). -/
noncomputable def princLev (c : V) : V := if kind c = 1 then tcOmegaLev c else tcLev c

def princLevDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ k, !kindDef k c ∧ ((k = 1 ∧ !tcOmegaLevDef y c) ∨ (k ≠ 1 ∧ !tcLevDef y c))”

instance princLev_defined : 𝚺₁-Function₁ (princLev : V → V) via princLevDef := .mk fun v ↦ by
  simp only [princLevDef, princLev, kind_defined.iff]
  by_cases h : kind (v 1) = 1 <;> simp [h, tcOmegaLev_defined.iff, tcLev_defined.iff]

/-- The `lt` flag at two cons codes: lexicographic comparison. -/
noncomputable def ltCC (c1 c2 s : V) : V :=
  bor (rdLt s (tcHd c1) (tcHd c2)) (band (beq (tcHd c1) (tcHd c2)) (rdLt s (tcTl c1) (tcTl c2)))

/-- The `lt` flag at a cons code against a principal code: compare the first entry. -/
noncomputable def ltCP (c1 c2 s : V) : V := rdLt s (tcHd c1) c2

/-- The `lt` flag at a principal code against a cons code: `≼` the first entry. -/
noncomputable def ltPC (c1 c2 s : V) : V := bor (rdLt s c1 (tcHd c2)) (beq c1 (tcHd c2))

def ltCCDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y c1 c2 s. ∃ h1, !tcHdDef h1 c1 ∧ ∃ h2, !tcHdDef h2 c2 ∧ ∃ t1, !tcTlDef t1 c1 ∧
    ∃ t2, !tcTlDef t2 c2 ∧ ∃ r1, !rdLtDef r1 s h1 h2 ∧ ∃ r2, !rdLtDef r2 s t1 t2 ∧
    ∃ e, !beqDef e h1 h2 ∧ ∃ a, !bandDef a e r2 ∧ !borDef y r1 a”

def ltCPDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y c1 c2 s. ∃ h1, !tcHdDef h1 c1 ∧ !rdLtDef y s h1 c2”

def ltPCDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y c1 c2 s. ∃ h2, !tcHdDef h2 c2 ∧ ∃ r, !rdLtDef r s c1 h2 ∧ ∃ e, !beqDef e c1 h2 ∧
    !borDef y r e”

instance ltCC_defined : 𝚺₁-Function₃ (ltCC : V → V → V → V) via ltCCDef := .mk fun v ↦ by
  simp [ltCCDef, ltCC, tcHd_defined.iff, tcTl_defined.iff, rdLt_defined.iff,
    beq_defined.iff, band_defined.iff, bor_defined.iff]

instance ltCP_defined : 𝚺₁-Function₃ (ltCP : V → V → V → V) via ltCPDef := .mk fun v ↦ by
  simp [ltCPDef, ltCP, tcHd_defined.iff, rdLt_defined.iff]

instance ltPC_defined : 𝚺₁-Function₃ (ltPC : V → V → V → V) via ltPCDef := .mk fun v ↦ by
  simp [ltPCDef, ltPC, tcHd_defined.iff, rdLt_defined.iff, beq_defined.iff, bor_defined.iff]

/-- The `lt` flag between two principal codes (`kind ∈ {1,2}`): position first, the ϑ_i-ϑ_i
clause when both are `theta`-codes at the same level. -/
noncomputable def ltPP (c1 c2 s : V) : V :=
  if kind c1 = 2 ∧ kind c2 = 2 then
    (if princLev c1 < princLev c2 then 1
     else if princLev c2 < princLev c1 then 0
     else
       bor (band (rdLt s (tcThetaArg c1) (tcThetaArg c2))
         (rdAll s (princLev c1) (tcThetaArg c1) c2))
         (rdEx s (princLev c1) c1 (tcThetaArg c2)))
  else if kind c1 = 2 ∧ kind c2 = 1 then
    (if princLev c1 ≤ princLev c2 then 1 else 0)
  else
    (if princLev c1 < princLev c2 then 1 else 0)

def ltPPDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y c1 c2 s. ∃ k1, !kindDef k1 c1 ∧ ∃ k2, !kindDef k2 c2 ∧ ∃ i, !princLevDef i c1 ∧
    ∃ j, !princLevDef j c2 ∧
    ( (k1 = 2 ∧ k2 = 2 ∧
        ( (i < j ∧ y = 1)
        ∨ (j < i ∧ y = 0)
        ∨ (i = j ∧ ∃ a, !tcThetaArgDef a c1 ∧ ∃ b, !tcThetaArgDef b c2 ∧
            ∃ r1, !rdLtDef r1 s a b ∧ ∃ r2, !rdAllDef r2 s i a c2 ∧ ∃ p, !bandDef p r1 r2 ∧
            ∃ r3, !rdExDef r3 s i c1 b ∧ !borDef y p r3) ) )
    ∨ ((k1 ≠ 2 ∨ k2 ≠ 2) ∧ k1 = 2 ∧ k2 = 1 ∧ ((i ≤ j ∧ y = 1) ∨ (j < i ∧ y = 0)))
    ∨ ((k1 ≠ 2 ∨ k2 ≠ 2) ∧ (k1 ≠ 2 ∨ k2 ≠ 1) ∧ ((i < j ∧ y = 1) ∨ (j ≤ i ∧ y = 0))) )”

instance ltPP_defined : 𝚺₁-Function₃ (ltPP : V → V → V → V) via ltPPDef := .mk fun v ↦ by
  simp only [ltPPDef, ltPP, kind_defined.iff, princLev_defined.iff, tcThetaArg_defined.iff,
    rdLt_defined.iff, rdAll_defined.iff, rdEx_defined.iff, band_defined.iff, bor_defined.iff]
  by_cases h1 : kind (v 1) = 2
  · by_cases h2 : kind (v 2) = 2
    · by_cases hij : princLev (v 1) < princLev (v 2)
      · simp [h1, h2, hij, lt_asymm hij, hij.ne]
      · by_cases hji : princLev (v 2) < princLev (v 1)
        · simp [h1, h2, hij, hji, hji.ne']
        · have heq : princLev (v 1) = princLev (v 2) := le_antisymm (not_lt.mp hji) (not_lt.mp hij)
          simp [h1, h2, hij, hji, heq]
    · by_cases h3 : kind (v 2) = 1
      · by_cases hle : princLev (v 1) ≤ princLev (v 2)
        · simp [h1, h2, h3, hle]
        · simp [h1, h2, h3, hle, not_le.mp hle]
      · by_cases hlt : princLev (v 1) < princLev (v 2)
        · simp [h1, h2, h3, hlt]
        · simp [h1, h2, h3, hlt, not_lt.mp hlt]
  · by_cases hlt : princLev (v 1) < princLev (v 2)
    · simp [h1, hlt]
    · simp [h1, hlt, not_lt.mp hlt]

/-- The step of the comparison table at a *plain* position `⟪posP c1, posP c2⟫`. -/
noncomputable def ltStep (c1 c2 s : V) : V :=
  if kind c1 = 0 then (if kind c2 = 0 then 0 else 1)
  else if kind c2 = 0 then 0
  else if kind c1 = 3 then (if kind c2 = 3 then ltCC c1 c2 s else ltCP c1 c2 s)
  else if kind c2 = 3 then ltPC c1 c2 s
  else ltPP c1 c2 s

def ltStepDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y c1 c2 s. ∃ k1, !kindDef k1 c1 ∧ ∃ k2, !kindDef k2 c2 ∧
    ( (k1 = 0 ∧ k2 = 0 ∧ y = 0)
    ∨ (k1 = 0 ∧ k2 ≠ 0 ∧ y = 1)
    ∨ (k1 ≠ 0 ∧ k2 = 0 ∧ y = 0)
    ∨ (k1 = 3 ∧ k2 = 3 ∧ !ltCCDef y c1 c2 s)
    ∨ (k1 = 3 ∧ k2 ≠ 0 ∧ k2 ≠ 3 ∧ !ltCPDef y c1 c2 s)
    ∨ (k1 ≠ 0 ∧ k1 ≠ 3 ∧ k2 = 3 ∧ !ltPCDef y c1 c2 s)
    ∨ (k1 ≠ 0 ∧ k1 ≠ 3 ∧ k2 ≠ 0 ∧ k2 ≠ 3 ∧ !ltPPDef y c1 c2 s) )”

instance ltStep_defined : 𝚺₁-Function₃ (ltStep : V → V → V → V) via ltStepDef := .mk fun v ↦ by
  simp [ltStepDef, ltStep, kind_defined.iff, ltCC_defined.iff, ltCP_defined.iff,
    ltPC_defined.iff, ltPP_defined.iff]
  rcases kind_cases (v 1) with h1 | h1 | h1 | h1 | h1 <;>
    rcases kind_cases (v 2) with h2 | h2 | h2 | h2 | h2 <;> simp [h1, h2]

/-- The step of the `all_k`-table at a *leveled* position `⟪posL k P, posP Q⟫`. -/
noncomputable def allStep (pos s : V) : V :=
  let X := π₁ pos
  let Y := π₂ pos
  let k := π₁ (π₂ X)
  let P := π₂ (π₂ X)
  let Q := π₂ Y
  if kind P = 0 then 1
  else if kind P = 1 then 1
  else if kind P = 2 then
    (if tcLev P ≤ k then rdLt s P Q else znth s ⟪posL k (tcThetaArg P), posP Q⟫)
  else if kind P = 3 then
    band (znth s ⟪posL k (tcHd P), posP Q⟫) (znth s ⟪posL k (tcTl P), posP Q⟫)
  else 0

def allStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y pos s. ∃ X, !pi₁Def X pos ∧ ∃ Y, !pi₂Def Y pos ∧ ∃ kX, !pi₂Def kX X ∧
    ∃ k, !pi₁Def k kX ∧ ∃ P, !pi₂Def P kX ∧ ∃ Q, !pi₂Def Q Y ∧ ∃ kd, !kindDef kd P ∧
    ( (kd = 0 ∧ y = 1)
    ∨ (kd = 1 ∧ y = 1)
    ∨ (kd = 2 ∧ ∃ jl, !tcLevDef jl P ∧
        ( (jl ≤ k ∧ !rdLtDef y s P Q)
        ∨ (k < jl ∧ ∃ a, !tcThetaArgDef a P ∧ ∃ pl, !posLDef pl k a ∧
            ∃ pq, !posPDef pq Q ∧ ∃ p, !pairDef p pl pq ∧ !znthDef y s p) ) )
    ∨ (kd = 3 ∧ ∃ h, !tcHdDef h P ∧ ∃ t, !tcTlDef t P ∧
        ∃ plh, !posLDef plh k h ∧ ∃ pq, !posPDef pq Q ∧ ∃ ph, !pairDef ph plh pq ∧
        ∃ plt, !posLDef plt k t ∧ ∃ pt, !pairDef pt plt pq ∧
        ∃ r1, !znthDef r1 s ph ∧ ∃ r2, !znthDef r2 s pt ∧ !bandDef y r1 r2)
    ∨ (kd ≠ 0 ∧ kd ≠ 1 ∧ kd ≠ 2 ∧ kd ≠ 3 ∧ y = 0) )”

instance allStep_defined : 𝚺₁-Function₂ (allStep : V → V → V) via allStepDef := .mk fun v ↦ by
  simp only [allStepDef, allStep]
  rcases kind_cases (π₂ (π₂ (π₁ (v 1)))) with h | h | h | h | h
  · simp [h]
  · simp [h]
  · by_cases hle : tcLev (π₂ (π₂ (π₁ (v 1)))) ≤ π₁ (π₂ (π₁ (v 1)))
    · have hnlt : ¬ π₁ (π₂ (π₁ (v 1))) < tcLev (π₂ (π₂ (π₁ (v 1)))) := not_lt.mpr hle
      simp [h, hle, hnlt, rdLt_defined.iff]
    · have hlt : π₁ (π₂ (π₁ (v 1))) < tcLev (π₂ (π₂ (π₁ (v 1)))) := not_le.mp hle
      simp [h, hle, hlt, tcThetaArg_defined.iff, posL_defined.iff, posP_defined.iff,
        pair_defined.iff, znth_defined.iff]
  · simp [h, tcHd_defined.iff, tcTl_defined.iff, posL_defined.iff, posP_defined.iff,
      pair_defined.iff, znth_defined.iff, band_defined.iff]
  · simp [h]

/-- The step of the `ex_k`-table at a *leveled* position `⟪posP P, posL k Q⟫`. -/
noncomputable def exStep (pos s : V) : V :=
  let X := π₁ pos
  let Y := π₂ pos
  let P := π₂ X
  let k := π₁ (π₂ Y)
  let Q := π₂ (π₂ Y)
  if kind Q = 0 then 0
  else if kind Q = 1 then 0
  else if kind Q = 2 then
    (if tcLev Q ≤ k then bor (rdLt s P Q) (beq P Q) else znth s ⟪posP P, posL k (tcThetaArg Q)⟫)
  else if kind Q = 3 then
    bor (znth s ⟪posP P, posL k (tcHd Q)⟫) (znth s ⟪posP P, posL k (tcTl Q)⟫)
  else 0

def exStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y pos s. ∃ X, !pi₁Def X pos ∧ ∃ Y, !pi₂Def Y pos ∧ ∃ P, !pi₂Def P X ∧
    ∃ kY, !pi₂Def kY Y ∧ ∃ k, !pi₁Def k kY ∧ ∃ Q, !pi₂Def Q kY ∧ ∃ kd, !kindDef kd Q ∧
    ( (kd = 0 ∧ y = 0)
    ∨ (kd = 1 ∧ y = 0)
    ∨ (kd = 2 ∧ ∃ jl, !tcLevDef jl Q ∧
        ( (jl ≤ k ∧ ∃ r, !rdLtDef r s P Q ∧ ∃ e, !beqDef e P Q ∧ !borDef y r e)
        ∨ (k < jl ∧ ∃ a, !tcThetaArgDef a Q ∧ ∃ pp, !posPDef pp P ∧
            ∃ pl, !posLDef pl k a ∧ ∃ p, !pairDef p pp pl ∧ !znthDef y s p) ) )
    ∨ (kd = 3 ∧ ∃ h, !tcHdDef h Q ∧ ∃ t, !tcTlDef t Q ∧
        ∃ pp, !posPDef pp P ∧ ∃ plh, !posLDef plh k h ∧ ∃ ph, !pairDef ph pp plh ∧
        ∃ plt, !posLDef plt k t ∧ ∃ pt, !pairDef pt pp plt ∧
        ∃ r1, !znthDef r1 s ph ∧ ∃ r2, !znthDef r2 s pt ∧ !borDef y r1 r2)
    ∨ (kd ≠ 0 ∧ kd ≠ 1 ∧ kd ≠ 2 ∧ kd ≠ 3 ∧ y = 0) )”

instance exStep_defined : 𝚺₁-Function₂ (exStep : V → V → V) via exStepDef := .mk fun v ↦ by
  simp only [exStepDef, exStep]
  rcases kind_cases (π₂ (π₂ (π₂ (v 1)))) with h | h | h | h | h
  · simp [h]
  · simp [h]
  · by_cases hle : tcLev (π₂ (π₂ (π₂ (v 1)))) ≤ π₁ (π₂ (π₂ (v 1)))
    · have hnlt : ¬ π₁ (π₂ (π₂ (v 1))) < tcLev (π₂ (π₂ (π₂ (v 1)))) := not_lt.mpr hle
      simp [h, hle, hnlt, rdLt_defined.iff, beq_defined.iff, bor_defined.iff]
    · have hlt : π₁ (π₂ (π₂ (v 1))) < tcLev (π₂ (π₂ (π₂ (v 1)))) := not_le.mp hle
      simp [h, hle, hlt, tcThetaArg_defined.iff, posL_defined.iff, posP_defined.iff,
        pair_defined.iff, znth_defined.iff]
  · simp [h, tcHd_defined.iff, tcTl_defined.iff, posL_defined.iff, posP_defined.iff,
      pair_defined.iff, znth_defined.iff, bor_defined.iff]
  · simp [h]

/-- The combined step of the comparison table at position `⟪X,Y⟫`, dispatching on whether `X`,
`Y` are plain (`posP`) or leveled (`posL`) codes. -/
noncomputable def cmpStep (pos s : V) : V :=
  if π₁ (π₁ pos) = 0 ∧ π₁ (π₂ pos) = 0 then ltStep (π₂ (π₁ pos)) (π₂ (π₂ pos)) s
  else if π₁ (π₁ pos) = 1 ∧ π₁ (π₂ pos) = 0 then allStep pos s
  else if π₁ (π₁ pos) = 0 ∧ π₁ (π₂ pos) = 1 then exStep pos s
  else 0

def cmpStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y pos s. ∃ X, !pi₁Def X pos ∧ ∃ Y, !pi₂Def Y pos ∧ ∃ kX, !pi₁Def kX X ∧ ∃ kY, !pi₁Def kY Y ∧
    ( (kX = 0 ∧ kY = 0 ∧ ∃ c1, !pi₂Def c1 X ∧ ∃ c2, !pi₂Def c2 Y ∧ !ltStepDef y c1 c2 s)
    ∨ (kX = 1 ∧ kY = 0 ∧ !allStepDef y pos s)
    ∨ (kX = 0 ∧ kY = 1 ∧ !exStepDef y pos s)
    ∨ (kX ≠ 0 ∧ kX ≠ 1 ∧ y = 0)
    ∨ (kX = 1 ∧ kY ≠ 0 ∧ y = 0)
    ∨ (kX = 0 ∧ kY ≠ 0 ∧ kY ≠ 1 ∧ y = 0) )”

instance cmpStep_defined : 𝚺₁-Function₂ (cmpStep : V → V → V) via cmpStepDef := .mk fun v ↦ by
  simp only [cmpStepDef, cmpStep]
  by_cases h1 : π₁ (π₁ (v 1)) = 0
  · by_cases h2 : π₁ (π₂ (v 1)) = 0
    · simp [h1, h2, ltStep_defined.iff]
    · by_cases h2' : π₁ (π₂ (v 1)) = 1
      · simp [h1, h2, h2', exStep_defined.iff]
      · simp [h1, h2, h2']
  · by_cases h1' : π₁ (π₁ (v 1)) = 1
    · by_cases h2 : π₁ (π₂ (v 1)) = 0
      · simp [h1, h1', h2, allStep_defined.iff]
      · simp [h1, h1', h2]
    · simp [h1, h1']

/-- The value of the comparison table at position `p`. -/
noncomputable def cmpVal (p : V) : V := covVal cmpStep cmpStepDef p

def cmpValDef : 𝚺₁.Semisentence 2 := covValDef cmpStepDef

instance cmpVal_defined : 𝚺₁-Function₁ (cmpVal : V → V) via cmpValDef :=
  covVal_defined cmpStep cmpStepDef

/-- **The internal order** as a `0/1` flag: `iltb c1 c2 = 1` iff `c1 ≺ c2`. -/
noncomputable def iltb (c1 c2 : V) : V := cmpVal ⟪posP c1, posP c2⟫

/-- `iall k c1 c2 = 1` iff every element of `E_k(c1)` is `≺ c2`. -/
noncomputable def iall (k c1 c2 : V) : V := cmpVal ⟪posL k c1, posP c2⟫

/-- `iex k c1 c2 = 1` iff `c1 ≼ γ` for some element `γ` of `E_k(c2)`. -/
noncomputable def iex (k c1 c2 : V) : V := cmpVal ⟪posP c1, posL k c2⟫

def iltbDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c1 c2. ∃ p1, !posPDef p1 c1 ∧ ∃ p2, !posPDef p2 c2 ∧ ∃ p, !pairDef p p1 p2 ∧
    !cmpValDef y p”

def iallDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y k c1 c2. ∃ p1, !posLDef p1 k c1 ∧ ∃ p2, !posPDef p2 c2 ∧ ∃ p, !pairDef p p1 p2 ∧
    !cmpValDef y p”

def iexDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y k c1 c2. ∃ p1, !posPDef p1 c1 ∧ ∃ p2, !posLDef p2 k c2 ∧ ∃ p, !pairDef p p1 p2 ∧
    !cmpValDef y p”

instance iltb_defined : 𝚺₁-Function₂ (iltb : V → V → V) via iltbDef := .mk fun v ↦ by
  simp [iltbDef, iltb, posP_defined.iff, pair_defined.iff, cmpVal_defined.iff]

instance iall_defined : 𝚺₁-Function₃ (iall : V → V → V → V) via iallDef := .mk fun v ↦ by
  simp [iallDef, iall, posL_defined.iff, posP_defined.iff, pair_defined.iff, cmpVal_defined.iff]

instance iex_defined : 𝚺₁-Function₃ (iex : V → V → V → V) via iexDef := .mk fun v ↦ by
  simp [iexDef, iex, posP_defined.iff, posL_defined.iff, pair_defined.iff, cmpVal_defined.iff]

/-! ### The recursion law of the comparison table -/

/-- **The recursion law**: the value of `iltb`/`iall`/`iex` at any position is the corresponding
step function applied to a table whose entries at strictly smaller positions already agree with
`cmpVal`. -/
lemma cmp_unfold (p : V) :
    ∃ S : V, cmpVal p = cmpStep p S ∧ ∀ q < p, znth S q = cmpVal q :=
  covVal_unfold cmpStep cmpStepDef p

lemma iltb_unfold (c1 c2 : V) :
    ∃ S : V, iltb c1 c2 = ltStep c1 c2 S ∧ ∀ q < (⟪posP c1, posP c2⟫ : V), znth S q = cmpVal q := by
  obtain ⟨S, h, hr⟩ := cmp_unfold (⟪posP c1, posP c2⟫ : V)
  refine ⟨S, ?_, hr⟩
  show cmpVal ⟪posP c1, posP c2⟫ = ltStep c1 c2 S
  rw [h, cmpStep]
  simp

lemma iall_unfold (k c1 c2 : V) :
    ∃ S : V, iall k c1 c2 = allStep ⟪posL k c1, posP c2⟫ S ∧
      ∀ q < (⟪posL k c1, posP c2⟫ : V), znth S q = cmpVal q := by
  obtain ⟨S, h, hr⟩ := cmp_unfold (⟪posL k c1, posP c2⟫ : V)
  refine ⟨S, ?_, hr⟩
  show cmpVal ⟪posL k c1, posP c2⟫ = allStep ⟪posL k c1, posP c2⟫ S
  rw [h, cmpStep]
  simp

lemma iex_unfold (k c1 c2 : V) :
    ∃ S : V, iex k c1 c2 = exStep ⟪posP c1, posL k c2⟫ S ∧
      ∀ q < (⟪posP c1, posL k c2⟫ : V), znth S q = cmpVal q := by
  obtain ⟨S, h, hr⟩ := cmp_unfold (⟪posP c1, posL k c2⟫ : V)
  refine ⟨S, ?_, hr⟩
  show cmpVal ⟪posP c1, posL k c2⟫ = exStep ⟪posP c1, posL k c2⟫ S
  rw [h, cmpStep]
  simp

/-! ### The recursion equations, one constructor pair at a time -/

lemma iltb_zero_zero : iltb (0 : V) 0 = 0 := by
  obtain ⟨S, h, -⟩ := iltb_unfold (0 : V) 0
  rw [h, ltStep]; simp

lemma iltb_zero_pos {c : V} (hc : c ≠ 0) : iltb (0 : V) c = 1 := by
  obtain ⟨S, h, -⟩ := iltb_unfold (0 : V) c
  rw [h, ltStep]
  simp [kind_eq_zero_iff, hc]

lemma iltb_pos_zero {c : V} (hc : c ≠ 0) : iltb c (0 : V) = 0 := by
  obtain ⟨S, h, -⟩ := iltb_unfold c (0 : V)
  rw [h, ltStep]
  simp [kind_eq_zero_iff, hc]

lemma iltb_cons_cons (x s y t : V) :
    iltb (tcCons x s) (tcCons y t) = bor (iltb x y) (band (beq x y) (iltb s t)) := by
  obtain ⟨S, h, hr⟩ := iltb_unfold (tcCons x s) (tcCons y t)
  rw [h, ltStep]
  simp only [kind_tcCons]
  have e1 : rdLt S x y = iltb x y := by
    unfold rdLt iltb
    exact hr _ (pair_lt_pair (posP_lt_posP (hd_lt_tcCons x s)) (posP_lt_posP (hd_lt_tcCons y t)))
  have e2 : rdLt S s t = iltb s t := by
    unfold rdLt iltb
    exact hr _ (pair_lt_pair (posP_lt_posP (tl_lt_tcCons x s)) (posP_lt_posP (tl_lt_tcCons y t)))
  simp [ltCC, tcHd_tcCons, tcTl_tcCons, e1, e2]

lemma iltb_cons_prin (x s : V) {c : V} (hc : kind c = 1 ∨ kind c = 2) :
    iltb (tcCons x s) c = iltb x c := by
  obtain ⟨S, h, hr⟩ := iltb_unfold (tcCons x s) c
  have hc0 : kind c ≠ 0 := by rcases hc with hc | hc <;> simp [hc]
  have hc3 : kind c ≠ 3 := by rcases hc with hc | hc <;> simp [hc]
  rw [h, ltStep]
  simp only [kind_tcCons]
  have e1 : rdLt S x c = iltb x c := by
    unfold rdLt iltb
    exact hr _ (pair_lt_pair_left (posP_lt_posP (hd_lt_tcCons x s)) _)
  simp [hc0, hc3, ltCP, tcHd_tcCons, e1]

lemma iltb_prin_cons {c : V} (hc : kind c = 1 ∨ kind c = 2) (y t : V) :
    iltb c (tcCons y t) = bor (iltb c y) (beq c y) := by
  obtain ⟨S, h, hr⟩ := iltb_unfold c (tcCons y t)
  have hc0 : kind c ≠ 0 := by rcases hc with hc | hc <;> simp [hc]
  have hc3 : kind c ≠ 3 := by rcases hc with hc | hc <;> simp [hc]
  rw [h, ltStep]
  simp only [kind_tcCons]
  have e1 : rdLt S c y = iltb c y := by
    unfold rdLt iltb
    exact hr _ (pair_lt_pair_right _ (posP_lt_posP (hd_lt_tcCons y t)))
  simp [hc0, hc3, ltPC, tcHd_tcCons, e1]

lemma iltb_tcOmega_tcOmega (i j : V) :
    iltb (tcOmega i) (tcOmega j) = (if i < j then 1 else 0) := by
  obtain ⟨S, h, -⟩ := iltb_unfold (tcOmega i) (tcOmega j)
  rw [h, ltStep]
  simp [ltPP, princLev]

lemma iltb_tcOmega_tcTheta (i j a : V) :
    iltb (tcOmega i) (tcTheta j a) = (if i < j then 1 else 0) := by
  obtain ⟨S, h, -⟩ := iltb_unfold (tcOmega i) (tcTheta j a)
  rw [h, ltStep]
  simp [ltPP, princLev]

lemma iltb_tcTheta_tcOmega (i a j : V) :
    iltb (tcTheta i a) (tcOmega j) = (if i ≤ j then 1 else 0) := by
  obtain ⟨S, h, -⟩ := iltb_unfold (tcTheta i a) (tcOmega j)
  rw [h, ltStep]
  simp [ltPP, princLev]

lemma iltb_tcTheta_tcTheta_of_lt {i j : V} (hij : i < j) (a b : V) :
    iltb (tcTheta i a) (tcTheta j b) = 1 := by
  obtain ⟨S, h, -⟩ := iltb_unfold (tcTheta i a) (tcTheta j b)
  rw [h, ltStep]
  simp [ltPP, princLev, hij]

lemma iltb_tcTheta_tcTheta_of_gt {i j : V} (hji : j < i) (a b : V) :
    iltb (tcTheta i a) (tcTheta j b) = 0 := by
  obtain ⟨S, h, -⟩ := iltb_unfold (tcTheta i a) (tcTheta j b)
  rw [h, ltStep]
  simp [ltPP, princLev, hji, not_lt.mpr hji.le, lt_asymm hji]

lemma iltb_tcTheta_tcTheta_eq (i a b : V) :
    iltb (tcTheta i a) (tcTheta i b) =
      bor (band (iltb a b) (iall i a (tcTheta i b))) (iex i (tcTheta i a) b) := by
  obtain ⟨S, h, hr⟩ := iltb_unfold (tcTheta i a) (tcTheta i b)
  have e1 : rdLt S a b = iltb a b := by
    unfold rdLt iltb
    exact hr _ (pair_lt_pair (posP_lt_posP (arg_lt_tcTheta i a)) (posP_lt_posP (arg_lt_tcTheta i b)))
  have e2 : rdAll S i a (tcTheta i b) = iall i a (tcTheta i b) := by
    unfold rdAll iall
    exact hr _ (pair_lt_pair_left (posL_lt_posP_succ i a) _)
  have e3 : rdEx S i (tcTheta i a) b = iex i (tcTheta i a) b := by
    unfold rdEx iex
    exact hr _ (pair_lt_pair_right _ (posL_lt_posP_succ i b))
  rw [h, ltStep]
  simp [ltPP, kind_tcTheta, princLev, tcLev_tcTheta, tcThetaArg_tcTheta, e1, e2, e3]

/-! ### The `all_k`/`ex_k` recursion equations -/

lemma iall_of_kind (k : V) {c : V} (hc : kind c = 0 ∨ kind c = 1) (x : V) : iall k c x = 1 := by
  obtain ⟨S, h, -⟩ := iall_unfold k c x
  rw [h]
  rcases hc with hc | hc <;> simp [allStep, hc]

lemma iall_tcTheta_of_le {k j : V} (hjk : j ≤ k) (a x : V) :
    iall k (tcTheta j a) x = iltb (tcTheta j a) x := by
  obtain ⟨S, h, hr⟩ := iall_unfold k (tcTheta j a) x
  rw [h]
  have e : rdLt S (tcTheta j a) x = iltb (tcTheta j a) x := by
    unfold rdLt iltb
    exact hr _ (pair_lt_pair_left (posP_lt_posL k (tcTheta j a)) _)
  simp [allStep, tcLev_tcTheta, hjk, e]

lemma iall_tcTheta_of_lt {k j : V} (hkj : k < j) (a x : V) :
    iall k (tcTheta j a) x = iall k a x := by
  obtain ⟨S, h, hr⟩ := iall_unfold k (tcTheta j a) x
  rw [h]
  have hnle : ¬ j ≤ k := not_le.mpr hkj
  have e : znth S ⟪posL k a, posP x⟫ = iall k a x := by
    unfold iall
    exact hr _ (pair_lt_pair_left (posL_lt_posL_of_lt_right k (arg_lt_tcTheta j a)) _)
  simp [allStep, tcLev_tcTheta, hnle, tcThetaArg_tcTheta, e]

lemma iall_cons (k y t x : V) : iall k (tcCons y t) x = band (iall k y x) (iall k t x) := by
  obtain ⟨S, h, hr⟩ := iall_unfold k (tcCons y t) x
  rw [h]
  have e1 : znth S ⟪posL k y, posP x⟫ = iall k y x := by
    unfold iall; exact hr _ (pair_lt_pair_left (posL_lt_posL_of_lt_right k (hd_lt_tcCons y t)) _)
  have e2 : znth S ⟪posL k t, posP x⟫ = iall k t x := by
    unfold iall; exact hr _ (pair_lt_pair_left (posL_lt_posL_of_lt_right k (tl_lt_tcCons y t)) _)
  simp [allStep, tcHd_tcCons, tcTl_tcCons, e1, e2]

lemma iex_of_kind (k x : V) {c : V} (hc : kind c = 0 ∨ kind c = 1) : iex k x c = 0 := by
  obtain ⟨S, h, -⟩ := iex_unfold k x c
  rw [h]
  rcases hc with hc | hc <;> simp [exStep, hc]

lemma iex_tcTheta_of_le {k j : V} (hjk : j ≤ k) (x a : V) :
    iex k x (tcTheta j a) = bor (iltb x (tcTheta j a)) (beq x (tcTheta j a)) := by
  obtain ⟨S, h, hr⟩ := iex_unfold k x (tcTheta j a)
  rw [h]
  have e : rdLt S x (tcTheta j a) = iltb x (tcTheta j a) := by
    unfold rdLt iltb
    exact hr _ (pair_lt_pair_right _ (posP_lt_posL k (tcTheta j a)))
  simp [exStep, tcLev_tcTheta, hjk, e]

lemma iex_tcTheta_of_lt {k j : V} (hkj : k < j) (x a : V) :
    iex k x (tcTheta j a) = iex k x a := by
  obtain ⟨S, h, hr⟩ := iex_unfold k x (tcTheta j a)
  rw [h]
  have hnle : ¬ j ≤ k := not_le.mpr hkj
  have e : znth S ⟪posP x, posL k a⟫ = iex k x a := by
    unfold iex
    exact hr _ (pair_lt_pair_right _ (posL_lt_posL_of_lt_right k (arg_lt_tcTheta j a)))
  simp [exStep, tcLev_tcTheta, hnle, tcThetaArg_tcTheta, e]

lemma iex_cons (k x y t : V) : iex k x (tcCons y t) = bor (iex k x y) (iex k x t) := by
  obtain ⟨S, h, hr⟩ := iex_unfold k x (tcCons y t)
  rw [h]
  have e1 : znth S ⟪posP x, posL k y⟫ = iex k x y := by
    unfold iex; exact hr _ (pair_lt_pair_right _ (posL_lt_posL_of_lt_right k (hd_lt_tcCons y t)))
  have e2 : znth S ⟪posP x, posL k t⟫ = iex k x t := by
    unfold iex; exact hr _ (pair_lt_pair_right _ (posL_lt_posL_of_lt_right k (tl_lt_tcCons y t)))
  simp [exStep, tcHd_tcCons, tcTl_tcCons, e1, e2]

/-! ### Standard codes: the tables compute `E_k`/`≺` -/

/-- The `all_k` flag at a standard code, in terms of `iltb`. -/
theorem iall_mc (k : ℕ) : ∀ (a : ThetaWTerm) (x : V),
    iall (k : V) (mc a) x = 1 ↔ ∀ g ∈ E k a, iltb (mc g) x = 1
  | .Omega j, x => by simp [iall_of_kind]
  | .theta j a, x => by
    by_cases hjk : j ≤ k
    · rw [mc_theta, iall_tcTheta_of_le (by exact_mod_cast hjk), E_theta_of_le hjk]
      simp [mc_theta]
    · have hkj' : k < j := not_le.mp hjk
      have hkj : (k : V) < (j : V) := by exact_mod_cast hkj'
      rw [mc_theta, iall_tcTheta_of_lt hkj, iall_mc k a x, E_theta_of_lt hkj']
  | .sum [], x => by simp [iall_of_kind]
  | .sum (y :: ys), x => by
    rw [mc_cons, iall_cons, band_eq_one, iall_mc k y x, iall_mc k (.sum ys) x, E_cons]
    simp only [List.mem_append]
    constructor
    · rintro ⟨h1, h2⟩ g (hg | hg)
      exacts [h1 g hg, h2 g hg]
    · intro h
      exact ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩
termination_by a => l a
decreasing_by all_goals simp; try omega

/-- The `ex_k` flag at a standard code, in terms of `iltb`. -/
theorem iex_mc (k : ℕ) : ∀ (x : V) (b : ThetaWTerm),
    iex (k : V) x (mc b) = 1 ↔ ∃ g ∈ E k b, iltb x (mc g) = 1 ∨ x = mc g
  | x, .Omega j => by simp [iex_of_kind]
  | x, .theta j b => by
    by_cases hjk : j ≤ k
    · rw [mc_theta, iex_tcTheta_of_le (by exact_mod_cast hjk), E_theta_of_le hjk]
      simp [bor_eq_one, beq_eq_one, mc_theta]
    · have hkj' : k < j := not_le.mp hjk
      have hkj : (k : V) < (j : V) := by exact_mod_cast hkj'
      rw [mc_theta, iex_tcTheta_of_lt hkj, iex_mc k x b, E_theta_of_lt hkj']
  | x, .sum [] => by simp [iex_of_kind]
  | x, .sum (y :: ys) => by
    rw [mc_cons, iex_cons, bor_eq_one, iex_mc k x y, iex_mc k x (.sum ys), E_cons]
    simp only [List.mem_append]
    constructor
    · rintro (⟨g, hg, h⟩ | ⟨g, hg, h⟩)
      exacts [⟨g, Or.inl hg, h⟩, ⟨g, Or.inr hg, h⟩]
    · rintro ⟨g, hg | hg, h⟩
      exacts [Or.inl ⟨g, hg, h⟩, Or.inr ⟨g, hg, h⟩]
termination_by _ b => l b
decreasing_by all_goals simp; try omega

private lemma kind_mc_prin {p : ThetaWTerm} (hp : IsPrin p) :
    kind (mc (V := V) p) = 1 ∨ kind (mc (V := V) p) = 2 := by
  cases p with
  | Omega k => simp
  | theta k a => simp
  | sum _ => exact absurd hp id

/-- **The internal order agrees with `ltb` on standard codes**, in every model of `IΣ₁`. -/
theorem iltb_mc : ∀ a b : ThetaWTerm, iltb (mc (V := V) a) (mc b) = 1 ↔ a < b
  | .sum [], .sum [] => by simp [iltb_zero_zero]
  | .sum [], .Omega j => by simp [iltb_zero_pos, nil_lt_Omega]
  | .sum [], .theta j b => by simp [iltb_zero_pos, nil_lt_theta]
  | .sum [], .sum (b :: bs) => by simp [iltb_zero_pos, nil_lt_cons]
  | .Omega i, .sum [] => by simp [iltb_pos_zero, not_Omega_lt_nil]
  | .theta i a, .sum [] => by simp [iltb_pos_zero, not_theta_lt_nil]
  | .sum (a :: as), .sum [] => by simp [iltb_pos_zero, not_cons_lt_nil]
  | .sum (a :: as), .sum (b :: bs) => by
    rw [mc_cons, mc_cons, iltb_cons_cons, bor_eq_one, band_eq_one, beq_eq_one, mc_inj,
      iltb_mc a b, iltb_mc (.sum as) (.sum bs), cons_lt_cons_iff]
  | .sum (a :: as), .Omega j => by
    rw [mc_cons, iltb_cons_prin _ _ (kind_mc_prin (isPrin_Omega j)), iltb_mc a (.Omega j),
      cons_lt_Omega_iff]
  | .sum (a :: as), .theta j b => by
    rw [mc_cons, iltb_cons_prin _ _ (kind_mc_prin (isPrin_theta j b)), iltb_mc a (.theta j b),
      cons_lt_theta_iff]
  | .Omega i, .sum (b :: bs) => by
    rw [mc_cons, iltb_prin_cons (kind_mc_prin (isPrin_Omega i)), bor_eq_one, beq_eq_one, mc_inj,
      iltb_mc (.Omega i) b, Omega_lt_cons_iff, ThetaWTerm.le_def]
  | .theta i a, .sum (b :: bs) => by
    rw [mc_cons, iltb_prin_cons (kind_mc_prin (isPrin_theta i a)), bor_eq_one, beq_eq_one,
      mc_inj, iltb_mc (.theta i a) b, theta_lt_cons_iff, ThetaWTerm.le_def]
  | .Omega i, .Omega j => by
    rw [mc_Omega, mc_Omega, iltb_tcOmega_tcOmega, Omega_lt_Omega_iff]
    by_cases h : i < j
    · simp [h, show (i : V) < (j : V) from by exact_mod_cast h]
    · simp [h, show ¬ (i : V) < (j : V) from by exact_mod_cast h]
  | .Omega i, .theta j b => by
    rw [mc_Omega, mc_theta, iltb_tcOmega_tcTheta, Omega_lt_theta_iff]
    by_cases h : i < j
    · simp [h, show (i : V) < (j : V) from by exact_mod_cast h]
    · simp [h, show ¬ (i : V) < (j : V) from by exact_mod_cast h]
  | .theta i a, .Omega j => by
    rw [mc_theta, mc_Omega, iltb_tcTheta_tcOmega, theta_lt_Omega_iff]
    by_cases h : i ≤ j
    · simp [h, show (i : V) ≤ (j : V) from by exact_mod_cast h]
    · simp [h, show ¬ (i : V) ≤ (j : V) from by exact_mod_cast h]
  | .theta i a, .theta j b => by
    rcases lt_trichotomy i j with hij | hij | hij
    · rw [mc_theta, mc_theta, iltb_tcTheta_tcTheta_of_lt (show (i : V) < (j : V) from by
        exact_mod_cast hij)]
      simp [theta_lt_theta_of_lt_level a b hij]
    · subst hij
      rw [mc_theta, mc_theta, iltb_tcTheta_tcTheta_eq, bor_eq_one, band_eq_one,
        iltb_mc a b, ← mc_theta, iall_mc i a, ← mc_theta, iex_mc i _ b, theta_lt_theta_iff]
      have h1 : ∀ g ∈ E i a, (iltb (mc (V := V) g) (mc (.theta i b)) = 1 ↔ g < .theta i b) :=
        fun g hg => iltb_mc g (.theta i b)
      have h2 : ∀ g ∈ E i b, (iltb (mc (V := V) (.theta i a)) (mc g) = 1 ↔ .theta i a < g) :=
        fun g hg => iltb_mc (.theta i a) g
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
          · exact Or.inr (congrArg (mc (V := V)) h)
    · rw [mc_theta, mc_theta, iltb_tcTheta_tcTheta_of_gt (show (j : V) < (i : V) from by
        exact_mod_cast hij)]
      simp [not_theta_lt_theta_of_lt_level a b hij]
termination_by a b => l a + l b
decreasing_by
  all_goals simp only [l_Omega, l_theta, l_cons]
  all_goals first
    | omega
    | (have := l_le_of_mem_E hg; omega)

end Model

/-! ## Normal forms

`sok`/`descOk`/`nfStep` generalize ID1's verbatim: no level threading is needed anywhere here
(`NF` has no domain-type restriction — that is `isDom`, built separately below — and `Omega`'s
clause is `1` unconditionally for the same reason as `isTermb`'s). -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The one-entry condition of a sum code. -/
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
  else if kind c = 1 then 1
  else if kind c = 2 then band (znth s (tcThetaArg c)) (sok (tcThetaArg c))
  else if kind c = 3 then
    band (band (znth s (tcHd c)) (sok (tcHd c)))
      (band (znth s (tcTl c)) (band (sumK (tcTl c)) (descOk c)))
  else 0

def nfStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c s. ∃ k, !kindDef k c ∧
    ( (k = 0 ∧ y = 1)
    ∨ (k = 1 ∧ y = 1)
    ∨ (k = 2 ∧ ∃ a, !tcThetaArgDef a c ∧ ∃ r, !znthDef r s a ∧ ∃ o, !sokDef o a ∧ !bandDef y r o)
    ∨ (k = 3 ∧ ∃ h, !tcHdDef h c ∧ ∃ t, !tcTlDef t c ∧ ∃ r1, !znthDef r1 s h ∧
        ∃ o, !sokDef o h ∧ ∃ b1, !bandDef b1 r1 o ∧ ∃ r2, !znthDef r2 s t ∧
        ∃ q, !sumKDef q t ∧ ∃ d, !descOkDef d c ∧ ∃ b2, !bandDef b2 q d ∧
        ∃ b3, !bandDef b3 r2 b2 ∧ !bandDef y b1 b3)
    ∨ (k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ y = 0) )”

instance nfStep_defined : 𝚺₁-Function₂ (nfStep : V → V → V) via nfStepDef := .mk fun v ↦ by
  simp [nfStepDef, nfStep, kind_defined.iff, tcThetaArg_defined.iff, znth_defined.iff,
    sok_defined.iff, band_defined.iff, tcHd_defined.iff, tcTl_defined.iff,
    sumK_defined.iff, descOk_defined.iff]
  rcases kind_cases (v 1) with h | h | h | h | h <;> simp [h]

/-- The hereditary part of normality. -/
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

@[simp] lemma nfA_tcOmega (i : V) : nfA (tcOmega i) = 1 := by
  obtain ⟨S, h, -⟩ := nfA_unfold (tcOmega i); simp [h, nfStep]

@[simp] lemma nfA_tcTheta (i a : V) : nfA (tcTheta i a) = isNFb a := by
  obtain ⟨S, h, hr⟩ := nfA_unfold (tcTheta i a)
  simp [h, nfStep, hr a (arg_lt_tcTheta i a), isNFb]

@[simp] lemma nfA_tcCons (x s : V) :
    nfA (tcCons x s) = band (isNFb x) (band (nfA s) (band (sumK s) (descOk (tcCons x s)))) := by
  obtain ⟨S, h, hr⟩ := nfA_unfold (tcCons x s)
  simp [h, nfStep, hr x (hd_lt_tcCons x s), hr s (tl_lt_tcCons x s), isNFb]

lemma nfA_kind_four {c : V} (h4 : kind c = 4) : nfA c = 0 := by
  obtain ⟨S, h, -⟩ := nfA_unfold c; simp [h, nfStep, h4]

@[simp] lemma sok_zero : sok (0 : V) = 1 := by simp [sok]

@[simp] lemma sok_tcOmega (i : V) : sok (tcOmega i) = 1 := by simp [sok]

@[simp] lemma sok_tcTheta (i a : V) : sok (tcTheta i a) = 1 := by simp [sok]

lemma sok_tcCons (x s : V) :
    sok (tcCons x s) = if s = 0 ∧ (kind x = 1 ∨ kind x = 2) then 0 else 1 := by
  simp [sok]

@[simp] lemma descOk_tcCons_zero (x : V) : descOk (tcCons x 0) = 1 := by simp [descOk]

@[simp] lemma descOk_tcCons_tcCons (x y t : V) :
    descOk (tcCons x (tcCons y t)) = bor (iltb y x) (beq y x) := by simp [descOk]

mutual
/-- **Normal forms are recognised on standard codes**, in every model of `IΣ₁`. -/
theorem isNF_mc : ∀ t : ThetaWTerm, isNF (mc (V := V) t) ↔ NF t
  | .Omega k => by simp [isNF, isNFb]
  | .theta k a => by
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
        | Omega k => simp [sok_tcCons, SingleOK]
        | theta k a => simp [sok_tcCons, SingleOK]
        | sum ys => cases ys <;> simp [sok_tcCons, SingleOK]
      | x :: y :: ys => simp [sok_tcCons, SingleOK]
    rw [hs]; tauto
termination_by t => 2 * l t + 1
decreasing_by all_goals simp; try omega

/-- The table part of normality on the code of a sum. -/
theorem nfA_sum_mc : ∀ xs : List ThetaWTerm,
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
        simp [ThetaWTerm.le_def]
    rw [hd]
    simp only [hk, true_and, NFList]
    cases xs with
    | nil => simp
    | cons y ys => simp; tauto
termination_by xs => 2 * l (.sum xs)
decreasing_by all_goals simp; try omega
end

end Model

/-! ## Wilken's domain condition

`Dom(theta k a) := Dom a ∧ ∀ x ∈ G_k(a), x < a`.  The universally-quantified part is built as its
own course-of-values table `domOk` over the *spectator* position `⟪bound, ⟪k, c⟫⟫` (`bound`, `k`
untouched, only `c` shrinks — the same trick as `iinE`/`iinG`), computing "every member of
`G_k(c)` is `≺ bound`" *structurally*, alongside `G_k`'s own recursion, instead of as a bounded
quantifier over the separately-computed `iinG`: `domOk bound k (theta j a) = a ≺ bound ∧
domOk bound k a` when `k < j` (the sole new member `a` and the hereditary rest), `1` when `j ≤ k`
(`G_k = ∅`, vacuous), and the union rule on sums — using the *already fully constructed* `iltb`,
exactly as `descOk` already does for `NF`'s `Desc` condition. This sidesteps the question of
whether a genuine bounded universal quantifier over a `Σ₁` matrix is itself `Σ₁` under `IΣ₁`'s
collection scheme (it is, but no combinator for it was needed anywhere else in this file, and
building one was not risked here). -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The step of the `domOk`-table at position `⟪bound, ⟪k, c⟫⟫`: "every member of `G_k(c)` is
`≺ bound`". -/
noncomputable def domOkStep (i s : V) : V :=
  if kind (π₂ (π₂ i)) = 2 then
    (if π₁ (π₂ i) < tcLev (π₂ (π₂ i)) then
      band (iltb (tcThetaArg (π₂ (π₂ i))) (π₁ i))
        (znth s ⟪π₁ i, ⟪π₁ (π₂ i), tcThetaArg (π₂ (π₂ i))⟫⟫)
     else 1)
  else if kind (π₂ (π₂ i)) = 3 then
    band (znth s ⟪π₁ i, ⟪π₁ (π₂ i), tcHd (π₂ (π₂ i))⟫⟫)
      (znth s ⟪π₁ i, ⟪π₁ (π₂ i), tcTl (π₂ (π₂ i))⟫⟫)
  else 1

def domOkStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y i s. ∃ bound, !pi₁Def bound i ∧ ∃ kc, !pi₂Def kc i ∧ ∃ k, !pi₁Def k kc ∧
    ∃ c, !pi₂Def c kc ∧ ∃ kd, !kindDef kd c ∧
    ( (kd = 2 ∧ ∃ jl, !tcLevDef jl c ∧
        ( (k < jl ∧ ∃ a, !tcThetaArgDef a c ∧ ∃ r1, !iltbDef r1 a bound ∧
            ∃ p, !pairDef p k a ∧ ∃ q, !pairDef q bound p ∧ ∃ r2, !znthDef r2 s q ∧
            !bandDef y r1 r2)
        ∨ (jl ≤ k ∧ y = 1) ) )
    ∨ (kd = 3 ∧ ∃ h, !tcHdDef h c ∧ ∃ t, !tcTlDef t c ∧
        ∃ ph, !pairDef ph k h ∧ ∃ qh, !pairDef qh bound ph ∧
        ∃ pt, !pairDef pt k t ∧ ∃ qt, !pairDef qt bound pt ∧
        ∃ r1, !znthDef r1 s qh ∧ ∃ r2, !znthDef r2 s qt ∧ !bandDef y r1 r2)
    ∨ (kd ≠ 2 ∧ kd ≠ 3 ∧ y = 1) )”

instance domOkStep_defined : 𝚺₁-Function₂ (domOkStep : V → V → V) via domOkStepDef :=
  .mk fun v ↦ by
  simp only [domOkStepDef, domOkStep]
  rcases kind_cases (π₂ (π₂ (v 1))) with h | h | h | h | h
  · simp [h]
  · simp [h]
  · by_cases hlt : π₁ (π₂ (v 1)) < tcLev (π₂ (π₂ (v 1)))
    · have hnle : ¬ tcLev (π₂ (π₂ (v 1))) ≤ π₁ (π₂ (v 1)) := not_le.mpr hlt
      simp [h, hlt, hnle, tcThetaArg_defined.iff, iltb_defined.iff, pair_defined.iff,
        znth_defined.iff, band_defined.iff]
    · have hle : tcLev (π₂ (π₂ (v 1))) ≤ π₁ (π₂ (v 1)) := not_lt.mp hlt
      simp [h, hlt, hle]
  · simp [h, tcHd_defined.iff, tcTl_defined.iff, pair_defined.iff, znth_defined.iff,
      band_defined.iff]
  · simp [h]

/-- **`domOk bound k c = 1`** iff every member of `G_k(c)` is `≺ bound`. -/
noncomputable def domOk (bound k c : V) : V := covVal domOkStep domOkStepDef ⟪bound, ⟪k, c⟫⟫

def domOkValDef : 𝚺₁.Semisentence 2 := covValDef domOkStepDef

def domOkDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y bound k c. ∃ kc, !pairDef kc k c ∧ ∃ i, !pairDef i bound kc ∧ !domOkValDef y i”

instance domOk_defined : 𝚺₁-Function₃ (domOk : V → V → V → V) via domOkDef := .mk fun v ↦ by
  simp [domOkDef, domOk, pair_defined.iff, (covVal_defined domOkStep domOkStepDef).iff,
    domOkValDef]

lemma domOk_unfold (bound k c : V) :
    ∃ S : V, domOk bound k c = domOkStep ⟪bound, ⟪k, c⟫⟫ S ∧
      ∀ bound' k' c' : V, ⟪bound', ⟪k', c'⟫⟫ < ⟪bound, ⟪k, c⟫⟫ →
        znth S ⟪bound', ⟪k', c'⟫⟫ = domOk bound' k' c' := by
  obtain ⟨S, h, hr⟩ := covVal_unfold domOkStep domOkStepDef (⟪bound, ⟪k, c⟫⟫ : V)
  exact ⟨S, h, fun bound' k' c' hlt => hr _ hlt⟩

private lemma domPos_lt_of_c_lt {bound k c c' : V} (h : c' < c) :
    (⟪bound, ⟪k, c'⟫⟫ : V) < ⟪bound, ⟪k, c⟫⟫ :=
  pair_lt_pair_right bound (pair_lt_pair_right k h)

lemma domOk_of_kind (bound k : V) {c : V} (hc : kind c = 0 ∨ kind c = 1) : domOk bound k c = 1 := by
  obtain ⟨S, h, -⟩ := domOk_unfold bound k c
  rw [h, domOkStep]
  simp only [pi₁_pair, pi₂_pair]
  rcases hc with hc | hc <;> simp [hc]

lemma domOk_tcTheta_of_le {bound k j : V} (hjk : j ≤ k) (a : V) :
    domOk bound k (tcTheta j a) = 1 := by
  obtain ⟨S, h, -⟩ := domOk_unfold bound k (tcTheta j a)
  rw [h, domOkStep]
  simp only [pi₁_pair, pi₂_pair, kind_tcTheta, tcLev_tcTheta]
  have hnlt : ¬ k < j := not_lt.mpr hjk
  simp [hnlt]

lemma domOk_tcTheta_of_lt {bound k j : V} (hkj : k < j) (a : V) :
    domOk bound k (tcTheta j a) = band (iltb a bound) (domOk bound k a) := by
  obtain ⟨S, h, hr⟩ := domOk_unfold bound k (tcTheta j a)
  rw [h, domOkStep]
  simp only [pi₁_pair, pi₂_pair, kind_tcTheta, tcLev_tcTheta, tcThetaArg_tcTheta]
  have e : znth S ⟪bound, ⟪k, a⟫⟫ = domOk bound k a := by
    exact hr _ _ _ (domPos_lt_of_c_lt (arg_lt_tcTheta j a))
  simp [hkj, e]

lemma domOk_tcCons (bound k x s : V) :
    domOk bound k (tcCons x s) = band (domOk bound k x) (domOk bound k s) := by
  obtain ⟨S, h, hr⟩ := domOk_unfold bound k (tcCons x s)
  rw [h, domOkStep]
  simp only [pi₁_pair, pi₂_pair, kind_tcCons, tcHd_tcCons, tcTl_tcCons]
  have e1 : znth S ⟪bound, ⟪k, x⟫⟫ = domOk bound k x := hr _ _ _ (domPos_lt_of_c_lt (hd_lt_tcCons x s))
  have e2 : znth S ⟪bound, ⟪k, s⟫⟫ = domOk bound k s := hr _ _ _ (domPos_lt_of_c_lt (tl_lt_tcCons x s))
  simp [e1, e2]

/-- `domOk` on standard codes, for a standard level `kk` and any bound `bt : V`. -/
theorem domOk_mc (kk : ℕ) (bt : V) :
    ∀ c : ThetaWTerm, domOk bt (kk : V) (mc c) = 1 ↔ ∀ x ∈ G kk c, iltb (mc x) bt = 1
  | .Omega j => by simp [domOk_of_kind]
  | .theta j a => by
    by_cases hjk : j ≤ kk
    · rw [mc_theta, domOk_tcTheta_of_le (by exact_mod_cast hjk), G_theta_of_le hjk]
      simp
    · have hkj' : kk < j := not_le.mp hjk
      have hkj : (kk : V) < (j : V) := by exact_mod_cast hkj'
      rw [mc_theta, domOk_tcTheta_of_lt hkj, band_eq_one, domOk_mc kk bt a, G_theta_of_lt hkj']
      simp only [List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩ x (rfl | hx)
        exacts [h1, h2 x hx]
      · intro h
        exact ⟨h a (Or.inl rfl), fun x hx => h x (Or.inr hx)⟩
  | .sum [] => by simp [domOk_of_kind]
  | .sum (y :: ys) => by
    rw [mc_cons, domOk_tcCons, band_eq_one, domOk_mc kk bt y, domOk_mc kk bt (.sum ys), G_cons]
    simp only [List.mem_append]
    constructor
    · rintro ⟨h1, h2⟩ x (hx | hx)
      exacts [h1 x hx, h2 x hx]
    · intro h
      exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
termination_by c => l c
decreasing_by all_goals simp; try omega

/-- The step of the `Dom` table. -/
noncomputable def domStep (c s : V) : V :=
  if kind c = 0 then 1
  else if kind c = 1 then 1
  else if kind c = 2 then
    band (znth s (tcThetaArg c)) (domOk (tcThetaArg c) (tcLev c) (tcThetaArg c))
  else if kind c = 3 then band (znth s (tcHd c)) (znth s (tcTl c))
  else 0

def domStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c s. ∃ k, !kindDef k c ∧
    ( (k = 0 ∧ y = 1)
    ∨ (k = 1 ∧ y = 1)
    ∨ (k = 2 ∧ ∃ a, !tcThetaArgDef a c ∧ ∃ r, !znthDef r s a ∧ ∃ lv, !tcLevDef lv c ∧
        ∃ o, !domOkDef o a lv a ∧ !bandDef y r o)
    ∨ (k = 3 ∧ ∃ h, !tcHdDef h c ∧ ∃ t, !tcTlDef t c ∧ ∃ r1, !znthDef r1 s h ∧
        ∃ r2, !znthDef r2 s t ∧ !bandDef y r1 r2)
    ∨ (k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ y = 0) )”

instance domStep_defined : 𝚺₁-Function₂ (domStep : V → V → V) via domStepDef := .mk fun v ↦ by
  simp [domStepDef, domStep, kind_defined.iff, tcThetaArg_defined.iff, znth_defined.iff,
    tcLev_defined.iff, domOk_defined.iff, band_defined.iff, tcHd_defined.iff, tcTl_defined.iff]
  rcases kind_cases (v 1) with h | h | h | h | h <;> simp [h]

/-- The domain flag: `1` iff `c` is the code of a domain term. -/
noncomputable def isDomb (c : V) : V := covVal domStep domStepDef c

/-- `c` is the code of a domain term (Wilken's `∀ subterms ϑ_k ξ, G_k(ξ) ≺ ξ`). -/
def isDom (c : V) : Prop := isDomb c = 1

def isDombDef : 𝚺₁.Semisentence 2 := covValDef domStepDef

instance isDomb_defined : 𝚺₁-Function₁ (isDomb : V → V) via isDombDef :=
  covVal_defined domStep domStepDef

lemma isDomb_unfold (c : V) :
    ∃ S : V, isDomb c = domStep c S ∧ ∀ k < c, znth S k = isDomb k :=
  covVal_unfold domStep domStepDef c

@[simp] lemma isDomb_zero : isDomb (0 : V) = 1 := by
  obtain ⟨S, h, -⟩ := isDomb_unfold (0 : V); simp [h, domStep]

@[simp] lemma isDomb_tcOmega (i : V) : isDomb (tcOmega i) = 1 := by
  obtain ⟨S, h, -⟩ := isDomb_unfold (tcOmega i); simp [h, domStep]

@[simp] lemma isDomb_tcTheta (i a : V) :
    isDomb (tcTheta i a) = band (isDomb a) (domOk a i a) := by
  obtain ⟨S, h, hr⟩ := isDomb_unfold (tcTheta i a)
  simp [h, domStep, hr a (arg_lt_tcTheta i a)]

@[simp] lemma isDomb_tcCons (x s : V) : isDomb (tcCons x s) = band (isDomb x) (isDomb s) := by
  obtain ⟨S, h, hr⟩ := isDomb_unfold (tcCons x s)
  simp [h, domStep, hr x (hd_lt_tcCons x s), hr s (tl_lt_tcCons x s)]

/-- **Domain terms are recognised on standard codes**, in every model of `IΣ₁`. -/
theorem isDom_mc : ∀ t : ThetaWTerm, isDom (mc (V := V) t) ↔ Dom t
  | .Omega k => by simp [isDom]
  | .theta k a => by
    rw [isDom, mc_theta, isDomb_tcTheta, band_eq_one, ← isDom, isDom_mc a, dom_theta_iff,
      domOk_mc k (mc a) a]
    constructor
    · rintro ⟨hDa, hG⟩
      exact ⟨hDa, fun x hx => (iltb_mc x a).mp (hG x hx)⟩
    · rintro ⟨hDa, hG⟩
      exact ⟨hDa, fun x hx => (iltb_mc x a).mpr (hG x hx)⟩
  | .sum [] => by simp [isDom, dom_sum_iff]
  | .sum (x :: xs) => by
    have h1 := isDom_mc x
    have h2 := isDom_mc (.sum xs)
    unfold isDom at h1 h2 ⊢
    rw [mc_cons, isDomb_tcCons, band_eq_one, h1, h2]
    simp [dom_sum_iff, List.mem_cons, forall_eq_or_imp]
termination_by t => l t
decreasing_by all_goals simp; try omega

end Model

/-! ## The arithmetic formulas, and the ℕ-model bridge -/

/-- `x` is the code of a term in normal form. -/
def thNFDef : 𝚺₁.Semisentence 1 := .mkSigma “x. !isNFbDef 1 x”

/-- **The order of the notation system**: `y` and `x` are codes of normal forms and `y ≺ x`. -/
def thPrecDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. !isNFbDef 1 y ∧ !isNFbDef 1 x ∧ !iltbDef 1 y x”

/-- `x` is the code of a domain term. -/
def thDomDef : 𝚺₁.Semisentence 1 := .mkSigma “x. !isDombDef 1 x”

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem eval_thNFDef (x : V) : thNFDef.val.Evalb ![x] ↔ isNF x := by
  simp [thNFDef, isNF, isNFb_defined.iff, eq_comm]

@[simp] theorem eval_thPrecDef (y x : V) :
    thPrecDef.val.Evalb ![y, x] ↔ isNF y ∧ isNF x ∧ iltb y x = 1 := by
  simp [thPrecDef, isNF, isNFb_defined.iff, iltb_defined.iff, eq_comm]

@[simp] theorem eval_thDomDef (x : V) : thDomDef.val.Evalb ![x] ↔ isDom x := by
  simp [thDomDef, isDom, isDomb_defined.iff, eq_comm]

theorem eval_thNFDef_mc (t : ThetaWTerm) : thNFDef.val.Evalb ![mc (V := V) t] ↔ NF t := by
  simpa using isNF_mc (V := V) t

theorem eval_thPrecDef_mc (y x : ThetaWTerm) :
    thPrecDef.val.Evalb ![mc (V := V) y, mc x] ↔ NF y ∧ NF x ∧ y < x := by
  simp [isNF_mc, iltb_mc]

theorem eval_thDomDef_mc (t : ThetaWTerm) : thDomDef.val.Evalb ![mc (V := V) t] ↔ Dom t := by
  simpa using isDom_mc (V := V) t

end Model

/-- **The order of the notation, read on plain ℕ-codes.** -/
theorem standard_lt_iff (a b : ThetaWTerm) : iltb (code a : ℕ) (code b : ℕ) = 1 ↔ a < b := by
  simpa [mc_nat] using iltb_mc (V := ℕ) a b

/-- **Normal forms, read on plain ℕ-codes.** -/
theorem standard_nf_iff (t : ThetaWTerm) : isNF (code t : ℕ) ↔ NF t := by
  simpa [mc_nat] using isNF_mc (V := ℕ) t

/-- **The domain condition, read on plain ℕ-codes.** -/
theorem standard_dom_iff (t : ThetaWTerm) : isDom (code t : ℕ) ↔ Dom t := by
  simpa [mc_nat] using isDom_mc (V := ℕ) t

/-! ### The slot check

Concrete small terms, per clause: `iltb` on the same-level ϑ-clause and across levels (a level
comparison swapped would flip one of these two facts), and `isDom` on a genuine positive example
and on the counterexample already recorded in `ThetaW/Dom.lean`'s docstring
(`ϑ₀(ϑ₁(Ω₃))`, later named `tower 0 2` there — reproved here directly from `dom_theta_iff` so it
does not depend on that file's `tower`/`Descent` machinery). -/

section SlotCheck

/-- **Same-level clause**: `ϑ₀(Ω₂) ≺ ϑ₀(Ω₃)` (from `Ω₂ ≺ Ω₃` via the ϑ_0-ϑ_0 clause). -/
theorem slotCheck_iltb_theta_same_level :
    iltb (code (theta 0 (Omega 1)) : ℕ) (code (theta 0 (Omega 2))) = 1 := by
  rw [standard_lt_iff, theta_lt_theta_iff]
  exact Or.inl ⟨(Omega_lt_Omega_iff 1 2).mpr (by norm_num), by simp⟩

/-- **Cross-level clause, the other direction**: `ϑ₁(Ω₁) ⊀ ϑ₀(Ω₆)` — a level comparison
flipped (`i < j` confused with `j < i`, or the same-level clause misfiring across levels) would
make this provable by luck. -/
theorem slotCheck_not_iltb_cross_level :
    iltb (code (theta 1 (Omega 0)) : ℕ) (code (theta 0 (Omega 5))) ≠ 1 := by
  intro h
  rw [standard_lt_iff] at h
  exact not_theta_lt_theta_of_lt_level (Omega 0) (Omega 5) (show (0 : ℕ) < 1 by norm_num) h

/-- **A genuine domain term**: `ϑ_0(Ω_6)` (Wilken's `ϑ̄_0` applied to `Ω_6` is always in the
domain, `dom_theta_Omega`). -/
theorem slotCheck_isDom_theta0_Omega5 : isDom (code (theta 0 (Omega 5)) : ℕ) := by
  rw [standard_dom_iff]; exact dom_theta_Omega 0 5

/-- **The domain counterexample**: `ϑ_0(ϑ_1(Ω_3))` is *not* a domain term — `G_0(ϑ_1(Ω_3)) ∋ Ω_3`
sits *above* `ϑ_1(Ω_3)` in the order (`Ω_2 ≺ ϑ_1(Ω_3)` needs level `2 < 1`, false), exactly the
defect `ThetaW/Dom.lean`'s `not_dom_tower` documents (there as `tower 0 2`). -/
theorem slotCheck_not_isDom_theta0_theta1_Omega2 :
    ¬ isDom (code (theta 0 (theta 1 (Omega 2))) : ℕ) := by
  rw [standard_dom_iff, dom_theta_iff]
  rintro ⟨-, hG⟩
  have hmem : Omega 2 ∈ G 0 (theta 1 (Omega 2)) := by
    rw [G_theta_of_lt (show (0 : ℕ) < 1 by decide)]; simp
  have hlt := hG (Omega 2) hmem
  have hno : ¬ Omega 2 < theta 1 (Omega 2) := by
    rw [Omega_lt_theta_iff]; decide
  exact hno hlt

end SlotCheck

end OrdinalAnalysis.IDn.Internal
