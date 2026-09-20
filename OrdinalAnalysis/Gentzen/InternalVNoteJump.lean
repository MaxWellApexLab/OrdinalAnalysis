/-
  The internal ordinal operations Gentzen's jump needs, over the Veblen codes.

  * `iomegaPow a` — the code of `ω ^ a`.  Below `Γ₀` the ω-power of a normal form is
    `φ_0(a) = vadd 0 a 1 0` unless `a` is a fixed point of `ω ^ ·`, i.e. unless `a` is
    itself a single Veblen term `φ_{a₁}(a₂)` with `a₁ ≠ 0`, in which case `ω ^ a = a`.
    `fixIndic` is that syntactic test on codes (it agrees with the fixed-point test of
    `OrdinalAnalysis.VNote.veblenNote` on standard codes).  The ω-power is always a
    *single term* `vcVadd (ipowFst a) (ipowSnd a) 1 0`, so `omegaBlock a k`, the code of
    `ω ^ a · k`, is the same term with coefficient `k`.
  * `iadd₁ x y` — ordinary ordinal addition on Veblen codes, by a course-of-values table on
    the first summand exactly as `InternalONote.iadd`, with the exponent comparison
    replaced by the leading-term comparison `icmp₁ (vcLead x) (vcLead y)`.
  * the ω-cover: every normal code strictly between `b` and `b + ω ^ a` lies below
    `b + ω ^ d · (k + 1)` for some normal `d < a` (`iadd₁_omegaPow_cover`).  The proof is
    the one of `OmegaCover.iadd_omegaPow_cover`, read through the lead form of
    `InternalVNoteOrder`; the only genuinely new ingredient is
    `icmp₁_iomegaPow : icmp₁ (ω ^ d) (ω ^ a) = icmp₁ d a`, which absorbs the fixed-point
    cases, together with the "logarithm" `ilog` of a code, whose ω-power is the code's
    leading term.
  * the totalised addition `safeIadd₁` and the unguarded finite iteration `safeIter₁`
    of `JumpArithmetic`, one notation system up.
-/
import OrdinalAnalysis.Gentzen.InternalVNoteOrder

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OrdinalAnalysis.Gentzen.InternalVNoteJump

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.InternalVNote
open OrdinalAnalysis.Gentzen.InternalVNoteOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The fixed-point test and the ω-power -/

/-- `0/1` flag: `c` is a single Veblen term `φ_a(b)` with `a ≠ 0`, i.e. (on normal codes) a
fixed point of `ω ^ ·`. -/
noncomputable def fixIndic (c : V) : V :=
  if c ≠ 0 ∧ vcCoeff c = 1 ∧ vcTail c = 0 ∧ vcFst c ≠ 0 then 1 else 0

def _root_.LO.FirstOrder.Arithmetic.fixIndicDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ n, !vcCoeffDef n c ∧ ∃ t, !sndIdxDef t c ∧ ∃ a, !vcFstDef a c ∧
    ((c ≠ 0 ∧ n = 1 ∧ t = 0 ∧ a ≠ 0 ∧ y = 1) ∨ ((c = 0 ∨ n ≠ 1 ∨ t ≠ 0 ∨ a = 0) ∧ y = 0))”

instance fixIndic_defined : 𝚺₁-Function₁ (fixIndic : V → V) via fixIndicDef := .mk fun v ↦ by
  simp [fixIndicDef, fixIndic, vcCoeff_defined.iff, vcTail, sndIdx_defined.iff, vcFst_defined.iff]
  by_cases h0 : v 1 = 0 <;> by_cases h1 : vcCoeff (v 1) = 1 <;>
    by_cases h2 : sndIdx (v 1) = 0 <;> by_cases h3 : vcFst (v 1) = 0 <;> simp [h0, h1, h2, h3]

instance fixIndic_definable : 𝚺₁-Function₁ (fixIndic : V → V) := fixIndic_defined.to_definable

lemma fixIndic_eq_one_iff (c : V) :
    fixIndic c = 1 ↔ (c ≠ 0 ∧ vcCoeff c = 1 ∧ vcTail c = 0 ∧ vcFst c ≠ 0) := by
  unfold fixIndic
  split_ifs with h <;> simp [h]

lemma fixIndic_vcVadd (a b n c : V) :
    fixIndic (vcVadd a b n c) = 1 ↔ (n = 1 ∧ c = 0 ∧ a ≠ 0) := by
  rw [fixIndic_eq_one_iff]
  simp

lemma fixIndic_zero_ne_one : fixIndic (0 : V) ≠ 1 := by
  rw [Ne, fixIndic_eq_one_iff]
  simp

/-- A fixed-point-shaped code is a single term with nonzero first argument. -/
lemma fix_destruct {c : V} (h : fixIndic c = 1) : ∃ p q : V, c = vcVadd p q 1 0 ∧ p ≠ 0 := by
  obtain ⟨hc0, hn, ht, hp⟩ := (fixIndic_eq_one_iff c).1 h
  refine ⟨vcFst c, vcSnd c, ?_, hp⟩
  calc c = vcVadd (vcFst c) (vcSnd c) (vcCoeff c) (vcTail c) := (vcVadd_destruct hc0).symm
    _ = vcVadd (vcFst c) (vcSnd c) 1 0 := by rw [hn, ht]

/-- First argument of the ω-power term. -/
noncomputable def ipowFst (c : V) : V := if fixIndic c = 1 then vcFst c else 0

/-- Second argument of the ω-power term. -/
noncomputable def ipowSnd (c : V) : V := if fixIndic c = 1 then vcSnd c else c

/-- **The code of `ω ^ c`**, always a single Veblen term. -/
noncomputable def iomegaPow (c : V) : V := vcVadd (ipowFst c) (ipowSnd c) 1 0

/-- **The code of `ω ^ c · k`.** -/
noncomputable def omegaBlock (c k : V) : V := vcVadd (ipowFst c) (ipowSnd c) k 0

def _root_.LO.FirstOrder.Arithmetic.ipowFstDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ f, !fixIndicDef f c ∧ ((f = 1 ∧ !vcFstDef y c) ∨ (f ≠ 1 ∧ y = 0))”

instance ipowFst_defined : 𝚺₁-Function₁ (ipowFst : V → V) via ipowFstDef := .mk fun v ↦ by
  simp [ipowFstDef, ipowFst, fixIndic_defined.iff, vcFst_defined.iff]
  by_cases h : fixIndic (v 1) = 1 <;> simp [h]

instance ipowFst_definable : 𝚺₁-Function₁ (ipowFst : V → V) := ipowFst_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.ipowSndDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ f, !fixIndicDef f c ∧ ((f = 1 ∧ !vcSndDef y c) ∨ (f ≠ 1 ∧ y = c))”

instance ipowSnd_defined : 𝚺₁-Function₁ (ipowSnd : V → V) via ipowSndDef := .mk fun v ↦ by
  simp [ipowSndDef, ipowSnd, fixIndic_defined.iff, vcSnd_defined.iff]
  by_cases h : fixIndic (v 1) = 1 <;> simp [h]

instance ipowSnd_definable : 𝚺₁-Function₁ (ipowSnd : V → V) := ipowSnd_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.iomegaPowDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ p, !ipowFstDef p c ∧ ∃ q, !ipowSndDef q c ∧ !vcVaddDef y p q 1 0”

instance iomegaPow_defined : 𝚺₁-Function₁ (iomegaPow : V → V) via iomegaPowDef := .mk fun v ↦ by
  simp [iomegaPowDef, iomegaPow, ipowFst_defined.iff, ipowSnd_defined.iff, vcVadd_defined.iff]

instance iomegaPow_definable : 𝚺₁-Function₁ (iomegaPow : V → V) := iomegaPow_defined.to_definable

lemma iomegaPow_eq (c : V) : iomegaPow c = vcVadd (ipowFst c) (ipowSnd c) 1 0 := rfl

@[simp] lemma omegaBlock_one (c : V) : omegaBlock c 1 = iomegaPow c := rfl

@[simp] lemma vcLead_iomegaPow (c : V) : vcLead (iomegaPow c) = iomegaPow c := by
  simp [iomegaPow]

@[simp] lemma vcLead_omegaBlock (c k : V) : vcLead (omegaBlock c k) = iomegaPow c := by
  simp [omegaBlock, iomegaPow]

@[simp] lemma iomegaPow_ne_zero (c : V) : iomegaPow c ≠ 0 := vcVadd_ne_zero _ _ _ _

@[simp] lemma omegaBlock_ne_zero (c k : V) : omegaBlock c k ≠ 0 := vcVadd_ne_zero _ _ _ _

lemma iomegaPow_of_fix {c : V} (h : fixIndic c = 1) : iomegaPow c = c := by
  obtain ⟨p, q, rfl, -⟩ := fix_destruct h
  simp [iomegaPow, ipowFst, ipowSnd, h]

lemma iomegaPow_of_not_fix {c : V} (h : fixIndic c ≠ 1) : iomegaPow c = vcVadd 0 c 1 0 := by
  simp [iomegaPow, ipowFst, ipowSnd, h]

/-- The coded fixed-point condition of the ω-power: a normal code that is not
fixed-point-shaped sits strictly below `φ_0` of itself. -/
lemma lt_omegaPow_of_not_fix {c : V} (hc : isNF₁ c) (h : fixIndic c ≠ 1) :
    icmp₁ c (vcVadd 0 c 1 0) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc0
  · exact icmp₁_zero_vcVadd _ _ _ _
  · obtain ⟨a₁, a₂, m, d, rfl⟩ : ∃ a b n c', c = vcVadd a b n c' :=
      ⟨_, _, _, _, (vcVadd_destruct hc0).symm⟩
    obtain ⟨hm, -, ha₂, -, hL, hfix, -⟩ := nf_parts hc
    rw [Ne, fixIndic_vcVadd] at h
    apply lt_of_lead_lt hm _root_.one_ne_zero
    rw [icmp₁_lead_lead]
    rcases eq_or_ne a₁ 0 with rfl | ha₁
    · rw [icmp₁_zero_zero, leadV_one]
      exact lt_of_lt_lead ha₂ hm hfix
    · rw [icmp₁_pos_zero ha₁, leadV_two, icmp₁_lead_form _root_.one_ne_zero hm, icmp₁_self hL,
        thenV_one_left]
      rcases eq_or_ne m 1 with rfl | hm1
      · have hd : d ≠ 0 := by
          intro hd
          exact h ⟨rfl, hd, ha₁⟩
        exact thenV_eq_zero.mpr (Or.inr ⟨cmpV_self 1, icmp₁_zero_pos hd⟩)
      · have h1m : (1 : V) < m :=
          lt_of_le_of_ne (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hm)) (Ne.symm hm1)
        exact thenV_eq_zero.mpr (Or.inl (cmpV_eq_zero.mpr h1m))

/-- **The ω-power of a normal code is normal.** -/
lemma isNF₁_iomegaPow {c : V} (hc : isNF₁ c) : isNF₁ (iomegaPow c) := by
  by_cases h : fixIndic c = 1
  · rw [iomegaPow_of_fix h]
    exact hc
  · rw [iomegaPow_of_not_fix h]
    exact isNF₁_of_parts isNF₁_zero hc (lt_omegaPow_of_not_fix hc h) _root_.one_ne_zero
      isNF₁_zero (icmp₁_zero_vcVadd _ _ _ _)

lemma isNF₁_omegaBlock {c : V} (hc : isNF₁ c) {k : V} (hk : k ≠ 0) : isNF₁ (omegaBlock c k) := by
  have h := isNF₁_iomegaPow hc
  rw [iomegaPow_eq] at h
  obtain ⟨-, hp, hq, -, -, hfix, -⟩ := nf_parts h
  exact isNF₁_of_parts hp hq hfix hk isNF₁_zero (icmp₁_zero_vcVadd _ _ _ _)

/-- **`ω ^ ·` reflects and preserves the order on normal codes**, fixed points included. -/
lemma icmp₁_iomegaPow {d a : V} (hd : isNF₁ d) (ha : isNF₁ a) :
    icmp₁ (iomegaPow d) (iomegaPow a) = icmp₁ d a := by
  by_cases fd : fixIndic d = 1 <;> by_cases fa : fixIndic a = 1
  · rw [iomegaPow_of_fix fd, iomegaPow_of_fix fa]
  · obtain ⟨d₁, d₂, rfl, hd₁⟩ := fix_destruct fd
    rw [iomegaPow_of_fix fd, iomegaPow_of_not_fix fa, icmp₁_lead_lead, icmp₁_pos_zero hd₁,
      leadV_two]
  · obtain ⟨a₁, a₂, rfl, ha₁⟩ := fix_destruct fa
    rw [iomegaPow_of_not_fix fd, iomegaPow_of_fix fa, icmp₁_lead_lead, icmp₁_zero_pos ha₁,
      leadV_zero]
  · rw [iomegaPow_of_not_fix fd, iomegaPow_of_not_fix fa, icmp₁_lead_lead, icmp₁_zero_zero,
      leadV_one]

/-! ## The logarithm of a code -/

/-- The exponent whose ω-power is the leading term of `c`: the second argument when the
leading term is `φ_0(·)`, and the leading term itself otherwise (it is then a fixed point). -/
noncomputable def ilog (c : V) : V := if vcFst c = 0 then vcSnd c else vcLead c

lemma isNF₁_ilog {c : V} (hc : isNF₁ c) (hc0 : c ≠ 0) : isNF₁ (ilog c) := by
  unfold ilog
  split_ifs
  · exact (isNF₁_destruct hc0 hc).2.2.1
  · exact isNF₁_vcLead hc0 hc

/-- **The ω-power of the logarithm is the leading term.** -/
lemma iomegaPow_ilog {c : V} (hc : isNF₁ c) (hc0 : c ≠ 0) : iomegaPow (ilog c) = vcLead c := by
  obtain ⟨a, b, n, t, rfl⟩ : ∃ a b n t, c = vcVadd a b n t :=
    ⟨_, _, _, _, (vcVadd_destruct hc0).symm⟩
  obtain ⟨-, -, hb, -, -, hfix, -⟩ := nf_parts hc
  unfold ilog
  rw [vcFst_vcVadd, vcSnd_vcVadd, vcLead_vcVadd]
  split_ifs with ha
  · subst ha
    have hnf : fixIndic b ≠ 1 := by
      intro hf
      obtain ⟨b₁, b₂, rfl, hb₁⟩ := fix_destruct hf
      rw [icmp₁_lead_lead, icmp₁_pos_zero hb₁, leadV_two, icmp₁_self hb] at hfix
      exact _root_.one_ne_zero hfix
    rw [iomegaPow_of_not_fix hnf]
  · rw [iomegaPow_of_fix ((fixIndic_vcVadd a b 1 0).2 ⟨rfl, rfl, ha⟩)]

lemma ipowFst_ilog {a b n t : V} (hc : isNF₁ (vcVadd a b n t)) :
    ipowFst (ilog (vcVadd a b n t)) = a := by
  have h := congrArg vcFst (iomegaPow_ilog hc (vcVadd_ne_zero a b n t))
  simpa [iomegaPow] using h

lemma ipowSnd_ilog {a b n t : V} (hc : isNF₁ (vcVadd a b n t)) :
    ipowSnd (ilog (vcVadd a b n t)) = b := by
  have h := congrArg vcSnd (iomegaPow_ilog hc (vcVadd_ne_zero a b n t))
  simpa [iomegaPow] using h

/-- If the leading term of `g` is below `ω ^ a`, then its logarithm is below `a`. -/
lemma ilog_lt_of_lead_lt {g a : V} (hg : isNF₁ g) (hg0 : g ≠ 0) (ha : isNF₁ a)
    (h : icmp₁ (vcLead g) (iomegaPow a) = 0) : icmp₁ (ilog g) a = 0 := by
  rw [← icmp₁_iomegaPow (isNF₁_ilog hg hg0) ha, iomegaPow_ilog hg hg0]
  exact h

/-! ## Internal ordinal addition `iadd₁` -/

/-- Table step of `iadd₁` at first-argument index `c` (parameter `b`, table `s` of `iadd₁ · b`). -/
noncomputable def iadd₁Next (b c s : V) : V :=
  if c = 0 then b
  else if b = 0 then c
  else if icmp₁ (vcLead c) (vcLead b) = 0 then b
  else if icmp₁ (vcLead c) (vcLead b) = 1 then
    vcVadd (vcFst c) (vcSnd c) (vcCoeff c + vcCoeff b) (vcTail b)
  else vcVadd (vcFst c) (vcSnd c) (vcCoeff c) (znth s (vcTail c))

def _root_.LO.FirstOrder.Arithmetic.iadd₁NextDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y b c s.
    (c = 0 ∧ y = b)
  ∨ (c ≠ 0 ∧ b = 0 ∧ y = c)
  ∨ (c ≠ 0 ∧ b ≠ 0 ∧ ∃ lc, !vcLeadDef lc c ∧ ∃ lb, !vcLeadDef lb b ∧
       ∃ cm, !icmp₁Def cm lc lb ∧
       ( (cm = 0 ∧ y = b)
       ∨ (cm = 1 ∧ ∃ p, !vcFstDef p c ∧ ∃ q, !vcSndDef q c ∧ ∃ nc, !vcCoeffDef nc c ∧
            ∃ nb, !vcCoeffDef nb b ∧ ∃ tb, !sndIdxDef tb b ∧ !vcVaddDef y p q (nc + nb) tb)
       ∨ (cm ≠ 0 ∧ cm ≠ 1 ∧ ∃ p, !vcFstDef p c ∧ ∃ q, !vcSndDef q c ∧ ∃ nc, !vcCoeffDef nc c ∧
            ∃ tc, !sndIdxDef tc c ∧ ∃ st, !znthDef st s tc ∧ !vcVaddDef y p q nc st) ) )”

instance iadd₁Next_defined : 𝚺₁-Function₃ (iadd₁Next : V → V → V → V) via iadd₁NextDef := .mk
  fun v ↦ by
  simp [iadd₁NextDef, iadd₁Next, vcLead_defined.iff, vcFst_defined.iff, vcSnd_defined.iff,
    vcCoeff_defined.iff, vcTail, sndIdx_defined.iff, icmp₁_defined.iff, znth_defined.iff,
    vcVadd_defined.iff]
  by_cases hc : v 2 = 0
  · simp [hc]
  · by_cases hb : v 1 = 0
    · simp [hc, hb]
    · by_cases h0 : icmp₁ (vcLead (v 2)) (vcLead (v 1)) = 0
      · simp [hc, hb, h0]
      · by_cases h1 : icmp₁ (vcLead (v 2)) (vcLead (v 1)) = 1
        · simp [hc, hb, h1]
        · simp [hc, hb, h0, h1]

instance iadd₁Next_definable : 𝚺₁-Function₃ (iadd₁Next : V → V → V → V) :=
  iadd₁Next_defined.to_definable

/-- Blueprint for the `iadd₁` table (parameter = second summand `b`). -/
def iadd₁Table.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. !mkSeq₁Def y x”
  succ := .mkSigma “y ih n x. ∃ v, !iadd₁NextDef v x (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def iadd₁Table.construction : PR.Construction V iadd₁Table.blueprint where
  zero := fun x ↦ !⟦x 0⟧
  succ := fun x n ih ↦ seqCons ih (iadd₁Next (x 0) (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [iadd₁Table.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [iadd₁Table.blueprint, iadd₁Next_defined.iff, seqCons_defined.iff]

/-- **The `iadd₁` table**: `iadd₁Table b n = ⟨iadd₁ 0 b,…,iadd₁ n b⟩`. -/
noncomputable def iadd₁Table (b n : V) : V := iadd₁Table.construction.result ![b] n

@[simp] lemma iadd₁Table_zero (b : V) : iadd₁Table b 0 = !⟦b⟧ := by
  simp [iadd₁Table, iadd₁Table.construction]

@[simp] lemma iadd₁Table_succ (b n : V) :
    iadd₁Table b (n + 1) = seqCons (iadd₁Table b n) (iadd₁Next b (n + 1) (iadd₁Table b n)) := by
  simp [iadd₁Table, iadd₁Table.construction]

/-- **Internal Veblen-normal-form ordinal addition** `a + b` inside `V`. -/
noncomputable def iadd₁ (a b : V) : V := znth (iadd₁Table b a) a

def _root_.LO.FirstOrder.Arithmetic.iadd₁TableDef : 𝚺₁.Semisentence 3 :=
  iadd₁Table.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance iadd₁Table_defined : 𝚺₁-Function₂ (iadd₁Table : V → V → V) via iadd₁TableDef := .mk
  fun v ↦ by simp [iadd₁Table.construction.result_defined_iff, iadd₁TableDef]; rfl

instance iadd₁Table_definable : 𝚺₁-Function₂ (iadd₁Table : V → V → V) :=
  iadd₁Table_defined.to_definable
instance iadd₁Table_definable' (Γ) (m : ℕ) :
    Γ-[m + 1]-Function₂ (iadd₁Table : V → V → V) :=
  iadd₁Table_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.iadd₁Def : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b. ∃ t, !iadd₁TableDef t b a ∧ !znthDef y t a”

instance iadd₁_defined : 𝚺₁-Function₂ (iadd₁ : V → V → V) via iadd₁Def := .mk fun v ↦ by
  simp [iadd₁Def, iadd₁, iadd₁Table_defined.iff, znth_defined.iff]

instance iadd₁_definable : 𝚺₁-Function₂ (iadd₁ : V → V → V) := iadd₁_defined.to_definable
instance iadd₁_definable' (Γ) (m : ℕ) :
    Γ-[m + 1]-Function₂ (iadd₁ : V → V → V) :=
  iadd₁_definable.of_sigmaOne

/-! ### Structural correctness of `iadd₁` -/

private lemma def_iadd₁Table {k} (b : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iadd₁Table b (v i)) :=
  DefinableFunction₂.comp (F := iadd₁Table) (DefinableFunction.const b) (DefinableFunction.var i)

private lemma def_iadd₁ {k} (b : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iadd₁ (v i) b) :=
  DefinableFunction₂.comp (F := iadd₁) (DefinableFunction.var i) (DefinableFunction.const b)

@[simp] lemma iadd₁Table_seq (b n : V) : Seq (iadd₁Table b n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_iadd₁Table b 0)
  case zero => simp
  case succ n ih => rw [iadd₁Table_succ]; exact ih.seqCons _

@[simp] lemma iadd₁Table_lh (b n : V) : lh (iadd₁Table b n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_iadd₁Table b 0))
      (by definability)
  case zero => simp
  case succ n ih => rw [iadd₁Table_succ, Seq.lh_seqCons _ (iadd₁Table_seq b n), ih]

lemma znth_iadd₁Table_succ {b n k : V} (hk : k < n + 1) :
    znth (iadd₁Table b (n + 1)) k = znth (iadd₁Table b n) k := by
  rw [iadd₁Table_succ]
  exact znth_seqCons_of_lt (iadd₁Table_seq b n) _ (by rw [iadd₁Table_lh]; exact hk)

lemma znth_iadd₁Table_eq_iadd₁ (b : V) : ∀ N : V, ∀ k ≤ N, znth (iadd₁Table b N) k = iadd₁ k b := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_iadd₁Table b 1) (DefinableFunction.var 0))
      (def_iadd₁ b 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_iadd₁Table_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

@[simp] lemma iadd₁_zero_left (b : V) : iadd₁ 0 b = b := by
  simp only [iadd₁, iadd₁Table_zero]
  exact (singleton_seq b).znth_eq_of_mem ((mem_singleton_seq_iff b b).mpr rfl)

/-- **The internal Veblen-addition recursion**: the three-way leading-term comparison, the
last branch recursing into the tail. -/
lemma iadd₁_vcVadd (a b n c y : V) :
    iadd₁ (vcVadd a b n c) y =
      (if y = 0 then vcVadd a b n c
       else if icmp₁ (vcVadd a b 1 0) (vcLead y) = 0 then y
       else if icmp₁ (vcVadd a b 1 0) (vcLead y) = 1 then
         vcVadd a b (n + vcCoeff y) (vcTail y)
       else vcVadd a b n (iadd₁ c y)) := by
  set x := vcVadd a b n c with hx
  have hpos : 0 < x := vcVadd_pos a b n c
  obtain ⟨M, hM⟩ : ∃ M, x = M + 1 :=
    ⟨x - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (iadd₁Table y x) x = iadd₁Next y x (iadd₁Table y M) := by
    rw [hM, iadd₁Table_succ]
    have := znth_seqCons_self (iadd₁Table_seq y M) (iadd₁Next y (M + 1) (iadd₁Table y M))
    rwa [iadd₁Table_lh] at this
  have htail : vcTail x ≤ M := by
    have := vcTail_lt a b n c
    rw [← hx] at this
    exact le_iff_lt_succ.mpr (hM ▸ this)
  have hxne : x ≠ 0 := hpos.ne'
  rw [iadd₁, key, iadd₁Next, if_neg hxne]
  rw [znth_iadd₁Table_eq_iadd₁ y M (vcTail x) htail, hx, vcLead_vcVadd, vcFst_vcVadd,
    vcSnd_vcVadd, vcCoeff_vcVadd, vcTail_vcVadd]

@[simp] lemma iadd₁_zero_right (a : V) : iadd₁ a 0 = a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · obtain ⟨p, q, n, r, rfl⟩ : ∃ p q n r, a = vcVadd p q n r :=
      ⟨_, _, _, _, (vcVadd_destruct ha).symm⟩
    rw [iadd₁_vcVadd, if_pos rfl]

/-! ### Adding single-term blocks -/

/-- Appending one more `ω ^ d`-term (any normal single term `T = φ_p(q)`) increments the
coefficient of an existing `T`-block: `(b + T·k) + T = b + T·(k+1)`. -/
lemma iadd₁_block_succ {p q : V} (hT : isNF₁ (vcVadd p q 1 0)) (k : V) : ∀ b : V,
    iadd₁ (iadd₁ b (vcVadd p q k 0)) (vcVadd p q 1 0) = iadd₁ b (vcVadd p q (k + 1) 0) := by
  intro b
  induction b using ISigma1.sigma1_order_induction
  · definability
  case ind b ih =>
    rcases eq_or_ne b 0 with rfl | hb
    · rw [iadd₁_zero_left, iadd₁_vcVadd, if_neg (vcVadd_ne_zero p q 1 0), vcLead_vcVadd,
        icmp₁_self hT, if_neg _root_.one_ne_zero, if_pos rfl, vcCoeff_vcVadd, vcTail_vcVadd,
        iadd₁_zero_left]
    · obtain ⟨e, f, n, r, rfl⟩ : ∃ e f n r, b = vcVadd e f n r :=
        ⟨_, _, _, _, (vcVadd_destruct hb).symm⟩
      have hr : r < vcVadd e f n r := tail_lt_code e f n r
      rw [iadd₁_vcVadd, if_neg (vcVadd_ne_zero p q k 0), vcLead_vcVadd]
      by_cases h0 : icmp₁ (vcVadd e f 1 0) (vcVadd p q 1 0) = 0
      · rw [if_pos h0, iadd₁_vcVadd, if_neg (vcVadd_ne_zero p q 1 0), vcLead_vcVadd,
          icmp₁_self hT, if_neg _root_.one_ne_zero, if_pos rfl, vcCoeff_vcVadd, vcTail_vcVadd]
        rw [iadd₁_vcVadd, if_neg (vcVadd_ne_zero p q (k + 1) 0), vcLead_vcVadd, if_pos h0]
      · rw [if_neg h0]
        by_cases h1 : icmp₁ (vcVadd e f 1 0) (vcVadd p q 1 0) = 1
        · rw [if_pos h1, vcCoeff_vcVadd, vcTail_vcVadd, iadd₁_vcVadd,
            if_neg (vcVadd_ne_zero p q 1 0), vcLead_vcVadd, h1, if_neg _root_.one_ne_zero,
            if_pos rfl, vcCoeff_vcVadd, vcTail_vcVadd]
          rw [iadd₁_vcVadd, if_neg (vcVadd_ne_zero p q (k + 1) 0), vcLead_vcVadd, if_neg h0,
            if_pos h1, vcCoeff_vcVadd, vcTail_vcVadd, add_assoc]
        · rw [if_neg h1, iadd₁_vcVadd, if_neg (vcVadd_ne_zero p q 1 0), vcLead_vcVadd,
            if_neg h0, if_neg h1]
          rw [iadd₁_vcVadd, if_neg (vcVadd_ne_zero p q (k + 1) 0), vcLead_vcVadd, if_neg h0,
            if_neg h1, ih r hr]

/-- A block sum stays below a term that dominates both summands' leading terms. -/
lemma iadd₁_block_lt {p q p' q' k r : V} (hr : isNF₁ r) (hk : k ≠ 0)
    (hrL : icmp₁ r (vcVadd p' q' 1 0) = 0)
    (hTL : icmp₁ (vcVadd p q 1 0) (vcVadd p' q' 1 0) = 0) :
    icmp₁ (iadd₁ r (vcVadd p q k 0)) (vcVadd p' q' 1 0) = 0 := by
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [iadd₁_zero_left]
    exact lt_of_lead_lt hk _root_.one_ne_zero hTL
  · obtain ⟨e, f, n, s, rfl⟩ : ∃ e f n s, r = vcVadd e f n s :=
      ⟨_, _, _, _, (vcVadd_destruct hr0).symm⟩
    obtain ⟨hn, -, -, -, -, -, -⟩ := nf_parts hr
    have hLr : icmp₁ (vcVadd e f 1 0) (vcVadd p' q' 1 0) = 0 :=
      lead_lt_of_lt hn _root_.one_ne_zero hrL
    rw [iadd₁_vcVadd, if_neg (vcVadd_ne_zero p q k 0), vcLead_vcVadd]
    by_cases h0 : icmp₁ (vcVadd e f 1 0) (vcVadd p q 1 0) = 0
    · rw [if_pos h0]
      exact lt_of_lead_lt hk _root_.one_ne_zero hTL
    · rw [if_neg h0]
      by_cases h1 : icmp₁ (vcVadd e f 1 0) (vcVadd p q 1 0) = 1
      · rw [if_pos h1, vcCoeff_vcVadd, vcTail_vcVadd]
        have hnk : n + k ≠ 0 :=
          (lt_of_lt_of_le (pos_iff_ne_zero.mpr hn) le_self_add).ne'
        exact lt_of_lead_lt hnk _root_.one_ne_zero hLr
      · rw [if_neg h1]
        exact lt_of_lead_lt hn _root_.one_ne_zero hLr

/-- Ordinary addition of a positive block of a normal single term preserves normal form. -/
lemma isNF₁_iadd₁_block {p q : V} (hT : isNF₁ (vcVadd p q 1 0)) {k : V} (hk : k ≠ 0) :
    ∀ b : V, isNF₁ b → isNF₁ (iadd₁ b (vcVadd p q k 0)) := by
  intro b
  induction b using ISigma1.sigma1_order_induction
  · definability
  case ind b ih =>
    intro hb
    obtain ⟨-, hp, hq, -, -, hfixT, -⟩ := nf_parts hT
    have hblock : isNF₁ (vcVadd p q k 0) :=
      isNF₁_of_parts hp hq hfixT hk isNF₁_zero (icmp₁_zero_vcVadd _ _ _ _)
    rcases eq_or_ne b 0 with rfl | hb0
    · rw [iadd₁_zero_left]
      exact hblock
    · obtain ⟨e, f, n, r, rfl⟩ : ∃ e f n r, b = vcVadd e f n r :=
        ⟨_, _, _, _, (vcVadd_destruct hb0).symm⟩
      have hrlt : r < vcVadd e f n r := tail_lt_code e f n r
      obtain ⟨hn, he, hf, hr, hLb, hfixb, htailb⟩ := nf_parts hb
      rw [iadd₁_vcVadd, if_neg (vcVadd_ne_zero p q k 0), vcLead_vcVadd]
      by_cases h0 : icmp₁ (vcVadd e f 1 0) (vcVadd p q 1 0) = 0
      · rw [if_pos h0]
        exact hblock
      · rw [if_neg h0]
        by_cases h1 : icmp₁ (vcVadd e f 1 0) (vcVadd p q 1 0) = 1
        · rw [if_pos h1, vcCoeff_vcVadd, vcTail_vcVadd]
          have hnk : n + k ≠ 0 :=
            (lt_of_lt_of_le (pos_iff_ne_zero.mpr hn) le_self_add).ne'
          exact isNF₁_of_parts he hf hfixb hnk isNF₁_zero (icmp₁_zero_vcVadd _ _ _ _)
        · rw [if_neg h1]
          have h2 : icmp₁ (vcVadd e f 1 0) (vcVadd p q 1 0) = 2 := by
            rcases icmp₁_cases hLb hT with h | h | h
            · exact absurd h h0
            · exact absurd h h1
            · exact h
          have hTL : icmp₁ (vcVadd p q 1 0) (vcVadd e f 1 0) = 0 := icmp₁_rev_two hLb hT h2
          exact isNF₁_of_parts he hf hfixb hn (ih r hrlt hr) (iadd₁_block_lt hr hk htailb hTL)

/-! ## The ω-cover -/

/-- Every nonzero normal `g` is below `b + L_g · (n_g + 1)`, `L_g` its leading term. -/
lemma lt_iadd₁_headBlock {b e f n s : V} (hb : isNF₁ b) (hg : isNF₁ (vcVadd e f n s)) :
    icmp₁ (vcVadd e f n s) (iadd₁ b (vcVadd e f (n + 1) 0)) = 0 := by
  obtain ⟨hn, -, -, -, hLg, -, -⟩ := nf_parts hg
  have hn1 : n + 1 ≠ 0 := by simp
  have hblock : icmp₁ (vcVadd e f n s) (vcVadd e f (n + 1) 0) = 0 := by
    rw [icmp₁_lead_form hn hn1, icmp₁_self hLg, thenV_one_left]
    exact thenV_eq_zero.mpr (Or.inl (cmpV_eq_zero.mpr (by simp)))
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [iadd₁_zero_left]
    exact hblock
  · obtain ⟨e', f', n', r', rfl⟩ : ∃ e f n r, b = vcVadd e f n r :=
      ⟨_, _, _, _, (vcVadd_destruct hb0).symm⟩
    obtain ⟨hn', -, -, -, hLb, -, -⟩ := nf_parts hb
    rw [iadd₁_vcVadd, if_neg (vcVadd_ne_zero e f (n + 1) 0), vcLead_vcVadd]
    by_cases h0 : icmp₁ (vcVadd e' f' 1 0) (vcVadd e f 1 0) = 0
    · rw [if_pos h0]
      exact hblock
    · rw [if_neg h0]
      by_cases h1 : icmp₁ (vcVadd e' f' 1 0) (vcVadd e f 1 0) = 1
      · rw [if_pos h1, vcCoeff_vcVadd, vcTail_vcVadd]
        have e12 := icmp₁_eq_imp_eq hLb hLg h1
        have hee : e' = e := by
          have := congrArg vcFst e12
          simpa using this
        have hff : f' = f := by
          have := congrArg vcSnd e12
          simpa using this
        subst hee
        subst hff
        have hnk : n' + (n + 1) ≠ 0 := by simp
        rw [icmp₁_lead_form hn hnk, icmp₁_self hLg, thenV_one_left]
        refine thenV_eq_zero.mpr (Or.inl (cmpV_eq_zero.mpr ?_))
        exact lt_of_lt_of_le (by simp) le_add_self
      · rw [if_neg h1]
        have h2 : icmp₁ (vcVadd e' f' 1 0) (vcVadd e f 1 0) = 2 := by
          rcases icmp₁_cases hLb hLg with h | h | h
          · exact absurd h h0
          · exact absurd h h1
          · exact h
        exact lt_of_lead_lt hn hn' (icmp₁_rev_two hLb hLg h2)

/-- Between two codes with the same leading term `L` a normal code has leading term `L`. -/
lemma lead_eq_of_between {p q n r m t g : V} (hg : isNF₁ g) (hg0 : g ≠ 0)
    (hL : isNF₁ (vcVadd p q 1 0)) (hn : n ≠ 0) (hm : m ≠ 0)
    (hlow : icmp₁ (vcVadd p q n r) g = 0) (hupp : icmp₁ g (vcVadd p q m t) = 0) :
    vcLead g = vcVadd p q 1 0 := by
  obtain ⟨e, f, k, s, rfl⟩ : ∃ e f k s, g = vcVadd e f k s :=
    ⟨_, _, _, _, (vcVadd_destruct hg0).symm⟩
  obtain ⟨hk, -, -, -, hLg, -, -⟩ := nf_parts hg
  rw [icmp₁_lead_form hn hk] at hlow
  rw [icmp₁_lead_form hk hm] at hupp
  rw [vcLead_vcVadd]
  have h1 : icmp₁ (vcVadd p q 1 0) (vcVadd e f 1 0) = 0 ∨
      icmp₁ (vcVadd p q 1 0) (vcVadd e f 1 0) = 1 := by
    rcases thenV_eq_zero.mp hlow with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have h2 : icmp₁ (vcVadd e f 1 0) (vcVadd p q 1 0) = 0 ∨
      icmp₁ (vcVadd e f 1 0) (vcVadd p q 1 0) = 1 := by
    rcases thenV_eq_zero.mp hupp with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  rcases h1 with h1 | h1
  · have h2' := icmp₁_rev_zero hL hLg h1
    rcases h2 with h2 | h2
    · rw [h2'] at h2; exact absurd h2 _root_.two_ne_zero
    · rw [h2'] at h2; exact absurd h2 (one_lt_two).ne'
  · exact (icmp₁_eq_imp_eq hL hLg h1).symm

/-- Between `L·n + r` and `L·n + t` a normal code is `L·n + s` with `r < s < t`. -/
lemma tails_of_between {p q n r t g : V} (hg : isNF₁ g) (hg0 : g ≠ 0)
    (hL : isNF₁ (vcVadd p q 1 0)) (hn : n ≠ 0)
    (hlow : icmp₁ (vcVadd p q n r) g = 0) (hupp : icmp₁ g (vcVadd p q n t) = 0) :
    ∃ s : V, g = vcVadd p q n s ∧ icmp₁ r s = 0 ∧ icmp₁ s t = 0 := by
  have hlead := lead_eq_of_between hg hg0 hL hn hn hlow hupp
  obtain ⟨e, f, k, s, rfl⟩ : ∃ e f k s, g = vcVadd e f k s :=
    ⟨_, _, _, _, (vcVadd_destruct hg0).symm⟩
  rw [vcLead_vcVadd] at hlead
  have hee : e = p := by
    have := congrArg vcFst hlead
    simpa using this
  have hff : f = q := by
    have := congrArg vcSnd hlead
    simpa using this
  subst hee
  subst hff
  obtain ⟨hk, -, -, -, -, -, -⟩ := nf_parts hg
  rw [icmp₁_lead_form hn hk, icmp₁_self hL, thenV_one_left] at hlow
  rw [icmp₁_lead_form hk hn, icmp₁_self hL, thenV_one_left] at hupp
  rcases thenV_eq_zero.mp hlow with hnk | ⟨hnk, hrs⟩
  · rcases thenV_eq_zero.mp hupp with hkn | ⟨hkn, -⟩
    · exact (_root_.lt_irrefl n (lt_trans (cmpV_eq_zero.mp hnk) (cmpV_eq_zero.mp hkn))).elim
    · have := cmpV_eq_one.mp hkn
      subst this
      exact (_root_.lt_irrefl _ (cmpV_eq_zero.mp hnk)).elim
  · rcases thenV_eq_zero.mp hupp with hkn | ⟨hkn, hst⟩
    · have := cmpV_eq_one.mp hnk
      subst this
      exact (_root_.lt_irrefl n (cmpV_eq_zero.mp hkn)).elim
    · have := cmpV_eq_one.mp hnk
      subst this
      exact ⟨s, rfl, hrs, hst⟩

/-- Between `L·n + r` and `L·(n+1)` a normal code is `L·n + s` with `r < s`. -/
lemma tail_of_between_succ {p q n r g : V} (hg : isNF₁ g) (hg0 : g ≠ 0)
    (hL : isNF₁ (vcVadd p q 1 0)) (hn : n ≠ 0)
    (hlow : icmp₁ (vcVadd p q n r) g = 0) (hupp : icmp₁ g (vcVadd p q (n + 1) 0) = 0) :
    ∃ s : V, g = vcVadd p q n s ∧ icmp₁ r s = 0 := by
  have hlead := lead_eq_of_between hg hg0 hL hn (by simp) hlow hupp
  obtain ⟨e, f, k, s, rfl⟩ : ∃ e f k s, g = vcVadd e f k s :=
    ⟨_, _, _, _, (vcVadd_destruct hg0).symm⟩
  rw [vcLead_vcVadd] at hlead
  have hee : e = p := by
    have := congrArg vcFst hlead
    simpa using this
  have hff : f = q := by
    have := congrArg vcSnd hlead
    simpa using this
  subst hee
  subst hff
  obtain ⟨hk, -, -, -, -, -, -⟩ := nf_parts hg
  rw [icmp₁_lead_form hn hk, icmp₁_self hL, thenV_one_left] at hlow
  rw [icmp₁_lead_form hk (by simp), icmp₁_self hL, thenV_one_left] at hupp
  have hkle : k ≤ n := by
    apply le_iff_lt_succ.mpr
    rcases thenV_eq_zero.mp hupp with hkn | ⟨-, hs0⟩
    · exact cmpV_eq_zero.mp hkn
    · exact absurd hs0 (icmp₁_right_zero_ne_zero s)
  rcases thenV_eq_zero.mp hlow with hnk | ⟨hnk, hrs⟩
  · exact absurd (cmpV_eq_zero.mp hnk) (not_lt_of_ge hkle)
  · have := cmpV_eq_one.mp hnk
    subst this
    exact ⟨s, rfl, hrs⟩

/-- Adding a block whose term is below the leading term goes into the tail. -/
lemma iadd₁_samePrefix_block {p q p' q' n r k : V}
    (h : icmp₁ (vcVadd p q 1 0) (vcVadd p' q' 1 0) = 2) :
    iadd₁ (vcVadd p q n r) (vcVadd p' q' k 0) =
      vcVadd p q n (iadd₁ r (vcVadd p' q' k 0)) := by
  rw [iadd₁_vcVadd, if_neg (vcVadd_ne_zero p' q' k 0), vcLead_vcVadd,
    if_neg (by rw [h]; exact _root_.two_ne_zero),
    if_neg (by rw [h]; exact (one_lt_two).ne')]

/-- Lifting a comparison of tails through a common prefix. -/
lemma lift_tail_lt {p q p' q' n r s k : V} (hL : isNF₁ (vcVadd p q 1 0)) (hn : n ≠ 0)
    (h : icmp₁ (vcVadd p q 1 0) (vcVadd p' q' 1 0) = 2)
    (htail : icmp₁ s (iadd₁ r (vcVadd p' q' k 0)) = 0) :
    icmp₁ (vcVadd p q n s) (iadd₁ (vcVadd p q n r) (vcVadd p' q' k 0)) = 0 := by
  rw [iadd₁_samePrefix_block h, icmp₁_lead_form hn hn, icmp₁_self hL, thenV_one_left,
    cmpV_self, thenV_one_left]
  exact htail

/-- The cover when `g` is below `ω ^ a` itself: take the logarithm of `g`. -/
lemma cover_of_lt_pow {a b g : V} (ha : isNF₁ a) (hb : isNF₁ b) (hg : isNF₁ g) (hg0 : g ≠ 0)
    (hga : icmp₁ g (iomegaPow a) = 0) :
    ∃ d k : V, isNF₁ d ∧ icmp₁ d a = 0 ∧ icmp₁ g (iadd₁ b (omegaBlock d (k + 1))) = 0 := by
  obtain ⟨e, f, n, s, rfl⟩ : ∃ e f n s, g = vcVadd e f n s :=
    ⟨_, _, _, _, (vcVadd_destruct hg0).symm⟩
  obtain ⟨hn, -, -, -, -, -, -⟩ := nf_parts hg
  refine ⟨ilog (vcVadd e f n s), n, isNF₁_ilog hg hg0, ?_, ?_⟩
  · apply ilog_lt_of_lead_lt hg hg0 ha
    rw [vcLead_vcVadd, iomegaPow_eq]
    rw [iomegaPow_eq] at hga
    exact lead_lt_of_lt hn _root_.one_ne_zero hga
  · unfold omegaBlock
    rw [ipowFst_ilog hg, ipowSnd_ilog hg]
    exact lt_iadd₁_headBlock hb hg

lemma iadd₁_omegaPow_cover_aux (a : V) (ha : isNF₁ a) :
    ∀ w : V, ∀ b ≤ w, ∀ g ≤ w,
      isNF₁ b → isNF₁ g → icmp₁ g b ≠ 0 → g ≠ b →
      icmp₁ g (iadd₁ b (iomegaPow a)) = 0 →
      ∃ d k : V, isNF₁ d ∧ icmp₁ d a = 0 ∧
        icmp₁ g (iadd₁ b (omegaBlock d (k + 1))) = 0 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro b hbw g hgw hb hg hgb hne hgz
    have hT : isNF₁ (iomegaPow a) := isNF₁_iomegaPow ha
    have hbg : icmp₁ b g = 0 := by
      rcases icmp₁_cases hg hb with h | h | h
      · exact absurd h hgb
      · exact absurd (icmp₁_eq_imp_eq hg hb h) hne
      · exact icmp₁_rev_two hg hb h
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact hgb (icmp₁_zero_pos (by rintro rfl; exact hne rfl))
    rcases eq_or_ne b 0 with rfl | hb0
    · rw [iadd₁_zero_left] at hgz
      exact cover_of_lt_pow ha isNF₁_zero hg hg0 hgz
    · obtain ⟨e, f, n, r, rfl⟩ : ∃ e f n r, b = vcVadd e f n r :=
        ⟨_, _, _, _, (vcVadd_destruct hb0).symm⟩
      obtain ⟨hn, he, hf, hr, hLb, hfixb, htailb⟩ := nf_parts hb
      have hrw : r < w := lt_of_lt_of_le (tail_lt_code e f n r) hbw
      rw [iomegaPow_eq] at hT
      rcases icmp₁_cases hLb hT with h0 | h1 | h2
      · -- `L_b < ω ^ a`: the sum is `ω ^ a` itself
        have hgz' : icmp₁ g (iomegaPow a) = 0 := by
          rw [iadd₁_vcVadd, if_neg (iomegaPow_ne_zero a), vcLead_iomegaPow, iomegaPow_eq,
            if_pos h0] at hgz
          rw [iomegaPow_eq]
          exact hgz
        exact cover_of_lt_pow ha hb hg hg0 hgz'
      · -- `L_b = ω ^ a`: the sum is `L_b · (n + 1)`
        have hgz' : icmp₁ g (vcVadd e f (n + 1) 0) = 0 := by
          rw [iadd₁_vcVadd, if_neg (iomegaPow_ne_zero a), vcLead_iomegaPow, iomegaPow_eq,
            if_neg (by rw [h1]; exact _root_.one_ne_zero), if_pos h1, vcCoeff_vcVadd,
            vcTail_vcVadd] at hgz
          exact hgz
        obtain ⟨s, rfl, hrs⟩ := tail_of_between_succ hg hg0 hLb hn hbg hgz'
        obtain ⟨-, -, -, hs, -, -, hsLb⟩ := nf_parts hg
        have hs0 : s ≠ 0 := by
          rintro rfl
          exact icmp₁_right_zero_ne_zero r hrs
        obtain ⟨e', f', n', s', rfl⟩ : ∃ e f n s', s = vcVadd e f n s' :=
          ⟨_, _, _, _, (vcVadd_destruct hs0).symm⟩
        obtain ⟨hn', -, -, -, hLs, -, -⟩ := nf_parts hs
        have hLsLb : icmp₁ (vcVadd e' f' 1 0) (vcVadd e f 1 0) = 0 :=
          lead_lt_of_lt hn' _root_.one_ne_zero hsLb
        refine ⟨ilog (vcVadd e' f' n' s'), n', isNF₁_ilog hs hs0, ?_, ?_⟩
        · apply ilog_lt_of_lead_lt hs hs0 ha
          rw [vcLead_vcVadd, iomegaPow_eq, ← icmp₁_eq_imp_eq hLb hT h1]
          exact hLsLb
        · unfold omegaBlock
          rw [ipowFst_ilog hs, ipowSnd_ilog hs]
          exact lift_tail_lt hLb hn (icmp₁_rev_zero hLs hLb hLsLb) (lt_iadd₁_headBlock hr hs)
      · -- `L_b > ω ^ a`: the sum goes into the tail
        have hgz' : icmp₁ g (vcVadd e f n (iadd₁ r (iomegaPow a))) = 0 := by
          rw [iadd₁_vcVadd, if_neg (iomegaPow_ne_zero a), vcLead_iomegaPow, iomegaPow_eq,
            if_neg (by rw [h2]; exact _root_.two_ne_zero),
            if_neg (by rw [h2]; exact (one_lt_two).ne')] at hgz
          rw [iomegaPow_eq]
          exact hgz
        obtain ⟨s, rfl, hrs, hsupp⟩ := tails_of_between hg hg0 hLb hn hbg hgz'
        obtain ⟨-, -, -, hs, -, -, -⟩ := nf_parts hg
        have hsw : s < w := lt_of_lt_of_le (tail_lt_code e f n s) hgw
        have hsr : icmp₁ s r ≠ 0 := by
          rw [icmp₁_rev_zero hr hs hrs]
          exact _root_.two_ne_zero
        have hsne : s ≠ r := by
          rintro rfl
          rw [icmp₁_self hr] at hrs
          exact _root_.one_ne_zero hrs
        obtain ⟨d, k, hd, hda, htail⟩ :=
          ih (max r s) (max_lt hrw hsw) r (le_max_left _ _) s (le_max_right _ _)
            hr hs hsr hsne hsupp
        refine ⟨d, k, hd, hda, ?_⟩
        have hdb : icmp₁ (iomegaPow d) (vcVadd e f 1 0) = 0 := by
          have h1 : icmp₁ (iomegaPow d) (iomegaPow a) = 0 := by
            rw [icmp₁_iomegaPow hd ha]
            exact hda
          have h2' : icmp₁ (iomegaPow a) (vcVadd e f 1 0) = 0 := by
            rw [iomegaPow_eq]
            exact icmp₁_rev_two hLb hT h2
          exact icmp₁_trans (isNF₁_iomegaPow hd) (isNF₁_iomegaPow ha) hLb h1 h2'
        rw [iomegaPow_eq] at hdb
        unfold omegaBlock
        exact lift_tail_lt hLb hn (icmp₁_rev_zero (by rw [← iomegaPow_eq]; exact isNF₁_iomegaPow hd)
          hLb hdb) htail

/--
**The ω-cover over the Veblen codes.**  Every normal code strictly between `b` and
`b + ω ^ a` lies below a finite block `b + ω ^ d · (k + 1)` for some normal `d < a`.
-/
lemma iadd₁_omegaPow_cover {a b g : V}
    (ha : isNF₁ a) (hb : isNF₁ b) (hg : isNF₁ g)
    (hgb : icmp₁ g b ≠ 0) (hne : g ≠ b)
    (hgz : icmp₁ g (iadd₁ b (iomegaPow a)) = 0) :
    ∃ d k : V, isNF₁ d ∧ icmp₁ d a = 0 ∧
      icmp₁ g (iadd₁ b (omegaBlock d (k + 1))) = 0 :=
  iadd₁_omegaPow_cover_aux a ha (max b g) b (le_max_left _ _)
    g (le_max_right _ _) hb hg hgb hne hgz

/-! ## Totalised addition and the unguarded finite iteration -/

/-- Ordinary coded ordinal addition on normal forms, and the left input otherwise. -/
noncomputable def safeIadd₁ (a b : V) : V :=
  if isNF₁ a then iadd₁ a b else a

/-- A `𝚺₁` graph for `safeIadd₁`, result first. -/
def safeIadd₁Def : 𝚺₁.Semisentence 3 := .mkSigma
  “z a b. ∃ q, !isNFb₁Def q a ∧
    ((q = 1 ∧ !iadd₁Def z a b) ∨ (q ≠ 1 ∧ z = a))”

instance safeIadd₁_defined : 𝚺₁-Function₂ (safeIadd₁ : V → V → V) via safeIadd₁Def :=
  .mk fun v ↦ by
  simp [safeIadd₁Def, safeIadd₁, isNF₁, isNFb₁_defined.iff, iadd₁_defined.iff]
  by_cases h : isNFb₁ (v 1) = 1 <;> simp [h]

instance safeIadd₁_definable : 𝚺₁-Function₂ (safeIadd₁ : V → V → V) :=
  safeIadd₁_defined.to_definable

@[simp] theorem safeIadd₁_of_nf {a b : V} (ha : isNF₁ a) :
    safeIadd₁ a b = iadd₁ a b := by simp [safeIadd₁, ha]

@[simp] theorem safeIadd₁_of_not_nf {a b : V} (ha : ¬isNF₁ a) :
    safeIadd₁ a b = a := by simp [safeIadd₁, ha]

@[simp] theorem safeIadd₁_zero_left (b : V) : safeIadd₁ 0 b = b := by
  simp [safeIadd₁]

def safeIter₁Blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y b w. y = b”
  succ := .mkSigma “y ih k b w. !safeIadd₁Def y ih w”

noncomputable def safeIter₁Construction {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : PR.Construction V safeIter₁Blueprint where
  zero := fun v ↦ v 0
  succ := fun v _ ih ↦ safeIadd₁ ih (v 1)
  zero_defined := .mk fun v ↦ by simp [safeIter₁Blueprint]
  succ_defined := .mk fun v ↦ by
    simp [safeIter₁Blueprint, safeIadd₁_defined.iff]

/-- Result-first graph of `k` successive safe additions of `w` to `b`. -/
def safeIter₁Def : 𝚺₁.Semisentence 4 :=
  safeIter₁Blueprint.resultDef.rew (Rew.subst ![#0, #3, #1, #2])

@[simp] theorem eval_safeIter₁Def (z b w k : V) :
    safeIter₁Def.val.Evalb ![z, b, w, k] ↔
      z = (safeIter₁Construction (V := V)).result ![b, w] k := by
  simp [safeIter₁Def, safeIter₁Construction.result_defined_iff]

/-- Iterating addition by `ω ^ d` for a positive number of steps gives the single block. -/
lemma safeIter₁_omegaBlock_succ (b d k : V) (hb : isNF₁ b) (hd : isNF₁ d) :
    (safeIter₁Construction (V := V)).result ![b, iomegaPow d] (k + 1) =
      iadd₁ b (omegaBlock d (k + 1)) := by
  have hT : isNF₁ (vcVadd (ipowFst d) (ipowSnd d) 1 0) := isNF₁_iomegaPow hd
  induction k using ISigma1.sigma1_succ_induction
  · apply HierarchySymbol.Definable.comp₂
    · exact ⟨safeIter₁Def.rew <| Rew.embSubsts
          ![(#0 : ArithmeticSemiterm V 2), &b, &(iomegaPow d), ‘#1 + 1’],
        by intro v; simp [eval_safeIter₁Def]⟩
    · definability
  case zero =>
    simp only [zero_add]
    have hstep :
        (safeIter₁Construction (V := V)).result ![b, iomegaPow d] 1 =
          safeIadd₁ b (iomegaPow d) := by
      calc
        (safeIter₁Construction (V := V)).result ![b, iomegaPow d] 1 =
            (safeIter₁Construction (V := V)).result
              ![b, iomegaPow d] (0 + 1) := by simp
        _ = safeIadd₁ b (iomegaPow d) := by
          rw [PR.Construction.result_succ, PR.Construction.result_zero]
          rfl
    rw [hstep, safeIadd₁_of_nf hb, omegaBlock_one]
  case succ k ih =>
    rw [PR.Construction.result_succ]
    change safeIadd₁
        ((safeIter₁Construction (V := V)).result ![b, iomegaPow d] (k + 1))
        (iomegaPow d) = iadd₁ b (omegaBlock d ((k + 1) + 1))
    rw [ih]
    show safeIadd₁ (iadd₁ b (vcVadd (ipowFst d) (ipowSnd d) (k + 1) 0))
        (vcVadd (ipowFst d) (ipowSnd d) 1 0) =
      iadd₁ b (vcVadd (ipowFst d) (ipowSnd d) (k + 1 + 1) 0)
    rw [safeIadd₁_of_nf (isNF₁_iadd₁_block hT (k := k + 1) (by simp) b hb)]
    exact iadd₁_block_succ hT (k + 1) b

end OrdinalAnalysis.Gentzen.InternalVNoteJump
