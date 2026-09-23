/-
  The internal ε-function and (EPSMONO).

  `InternalEpsCover` produces, for a normal code `x`, a base `e` which is `0` or an ε-number.
  The ACA progressiveness argument indexes its induction formula by

      `ψ₀(g) :≡ ∀²X TIupto(≺₁, ε_g, X)`,

  so it has to turn that `e` back into an *index*: `e = ε_h` for some `h`, and `h ≺₁ g`
  whenever `e ≼₁ x ≺₁ ε_g`.  That is design §2 (EPSMONO), and it needs the internal `φ_1`.

  `iepsilon` mirrors `VNote.veblenNote 1`: it is total, and it returns `g` itself when `g` is
  already a fixed point of `φ_1` — syntactically, when `g` is a single Veblen term `φ_p(q)`
  with `1 ≺₁ p`.  The three facts exported are

  * `eps_surj`   — every ε-number is `ε_h` for a normal `h`;
  * `iepsilon_mono` — `g ≺₁ h → ε_g ≺₁ ε_h`;
  * `eps_mono`  — `ε_h ≺₁ ε_g → h ≺₁ g`, i.e. (EPSMONO).

  The one delicate point is `lt_iepsilon_of_not_fix` (`g ≺₁ φ_1(g)`), which cannot go through
  `InternalVNoteOrder.lt_lead_of_lt_snd`: that lemma presupposes `isNF₁ (φ_1(g))`, whose
  normal-form clause *is* the statement being proved.  `lt_eps_of_lt` re-proves the relevant
  instance of (T'') by its own course-of-values induction, with no normal-form hypothesis on
  the right-hand term, which breaks the circle.
-/
import OrdinalAnalysis.Gentzen.InternalEpsCover

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OrdinalAnalysis.Gentzen.InternalEpsMono

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.InternalVNote
open OrdinalAnalysis.Gentzen.InternalVNoteOrder
open OrdinalAnalysis.Gentzen.InternalVNoteJump
open OrdinalAnalysis.Gentzen.CodedNotation (liftCode paLX_of_peano_semantic)
open OrdinalAnalysis.Gentzen.CodedVeblen
open OrdinalAnalysis.Gentzen.InternalEpsCover (isNF₁_one)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The syntactic fixed-point test of `φ_1` -/

/-- `0/1` flag: `g` is already a fixed point of `φ_1`, i.e. a single Veblen term `φ_p(q)`
with `1 ≺₁ p`.  This is the test inside `VNote.veblenNote 1`. -/
noncomputable def epsFixIndic (g : V) : V :=
  if g ≠ 0 ∧ vcCoeff g = 1 ∧ vcTail g = 0 ∧
      icmp₁ (vcVadd 0 0 1 0) (vcFst g) = 0 then 1 else 0

def _root_.LO.FirstOrder.Arithmetic.epsFixIndicDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y g. ∃ n, !vcCoeffDef n g ∧ ∃ t, !sndIdxDef t g ∧ ∃ a, !vcFstDef a g ∧
    ∃ o, !vcVaddDef o 0 0 1 0 ∧ ∃ c, !icmp₁Def c o a ∧
    ((g ≠ 0 ∧ n = 1 ∧ t = 0 ∧ c = 0 ∧ y = 1) ∨
      ((g = 0 ∨ n ≠ 1 ∨ t ≠ 0 ∨ c ≠ 0) ∧ y = 0))”

instance epsFixIndic_defined :
    𝚺₁-Function₁ (epsFixIndic : V → V) via epsFixIndicDef := .mk fun v ↦ by
  simp [epsFixIndicDef, epsFixIndic, vcCoeff_defined.iff, vcTail, sndIdx_defined.iff,
    vcFst_defined.iff, vcVadd_defined.iff, icmp₁_defined.iff]
  by_cases h0 : v 1 = 0 <;> by_cases h1 : vcCoeff (v 1) = 1 <;>
    by_cases h2 : sndIdx (v 1) = 0 <;>
    by_cases h3 : icmp₁ (vcVadd 0 0 1 0) (vcFst (v 1)) = 0 <;> simp [h0, h1, h2, h3]

instance epsFixIndic_definable : 𝚺₁-Function₁ (epsFixIndic : V → V) :=
  epsFixIndic_defined.to_definable

lemma epsFixIndic_eq_one_iff (g : V) :
    epsFixIndic g = 1 ↔
      (g ≠ 0 ∧ vcCoeff g = 1 ∧ vcTail g = 0 ∧
        icmp₁ (vcVadd 0 0 1 0) (vcFst g) = 0) := by
  unfold epsFixIndic
  split_ifs with h <;> simp [h]

/-- A fixed point of `φ_1` is a single Veblen term with first argument above `1`. -/
lemma epsFix_destruct {g : V} (h : epsFixIndic g = 1) :
    ∃ p q : V, g = vcVadd p q 1 0 ∧ icmp₁ (vcVadd 0 0 1 0) p = 0 := by
  obtain ⟨hg0, hn, ht, hc⟩ := (epsFixIndic_eq_one_iff g).1 h
  refine ⟨vcFst g, vcSnd g, ?_, hc⟩
  calc g = vcVadd (vcFst g) (vcSnd g) (vcCoeff g) (vcTail g) := (vcVadd_destruct hg0).symm
    _ = vcVadd (vcFst g) (vcSnd g) 1 0 := by rw [hn, ht]

/-! ## The internal `φ_1` -/

/-- **The internal ε-function** `iepsilon g = ε_g`, total, mirroring `VNote.veblenNote 1`. -/
noncomputable def iepsilon (g : V) : V :=
  if epsFixIndic g = 1 then g else vcVadd (vcVadd 0 0 1 0) g 1 0

def _root_.LO.FirstOrder.Arithmetic.iepsilonDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y g. ∃ q, !epsFixIndicDef q g ∧
    ((q = 1 ∧ y = g) ∨
      (q ≠ 1 ∧ ∃ o, !vcVaddDef o 0 0 1 0 ∧ !vcVaddDef y o g 1 0))”

instance iepsilon_defined :
    𝚺₁-Function₁ (iepsilon : V → V) via iepsilonDef := .mk fun v ↦ by
  simp [iepsilonDef, iepsilon, epsFixIndic_defined.iff, vcVadd_defined.iff]
  by_cases h : epsFixIndic (v 1) = 1 <;> simp [h]

instance iepsilon_definable : 𝚺₁-Function₁ (iepsilon : V → V) :=
  iepsilon_defined.to_definable

lemma iepsilon_of_fix {g : V} (h : epsFixIndic g = 1) : iepsilon g = g := by
  simp [iepsilon, h]

lemma iepsilon_of_not_fix {g : V} (h : epsFixIndic g ≠ 1) :
    iepsilon g = vcVadd (vcVadd 0 0 1 0) g 1 0 := by
  simp [iepsilon, h]

/-! ## `g ≺₁ φ_1(g)` -/

/--
**(T'') for `φ_1`, with no normal-form hypothesis on the right-hand term.**  `x ≺₁ g` gives
`x ≺₁ φ_1(g)`.  `InternalVNoteOrder.lt_lead_of_lt_snd` would need `isNF₁ (φ_1(g))`, which is
exactly what `lt_iepsilon_of_not_fix` is about to establish; this proof recurses on `x`
instead and so is free of that hypothesis.
-/
lemma lt_eps_of_lt (g : V) (hg : isNF₁ g) : ∀ x : V, isNF₁ x → icmp₁ x g = 0 →
    icmp₁ x (vcVadd (vcVadd 0 0 1 0) g 1 0) = 0 := by
  intro x
  induction x using ISigma1.sigma1_order_induction
  · definability
  case ind x ih =>
    intro hx h
    rcases eq_or_ne x 0 with rfl | hx0
    · exact icmp₁_zero_vcVadd _ _ _ _
    · obtain ⟨p, q, k, s, rfl⟩ : ∃ p q k s, x = vcVadd p q k s :=
        ⟨_, _, _, _, (vcVadd_destruct hx0).symm⟩
      obtain ⟨hk, hp, hq, -, hLx, hqL, -⟩ := nf_parts hx
      have hg0 : g ≠ 0 := by
        rintro rfl
        exact icmp₁_right_zero_ne_zero _ h
      obtain ⟨g₁, g₂, gk, gs, hgeq⟩ : ∃ a b n c, g = vcVadd a b n c :=
        ⟨_, _, _, _, (vcVadd_destruct hg0).symm⟩
      have hgk : gk ≠ 0 := by
        rw [hgeq] at hg
        exact (nf_parts hg).1
      have hLg : icmp₁ (vcVadd p q 1 0) g = 0 := by
        rw [hgeq] at h ⊢
        exact lead_lt_of_lt hk hgk h
      have hqg : icmp₁ q g = 0 := icmp₁_trans hq hLx hg hqL hLg
      apply lt_of_lead_lt hk _root_.one_ne_zero
      rw [icmp₁_lead_lead]
      rcases icmp₁_cases hp (isNF₁_one (V := V)) with hA | hA | hA
      · rw [hA, leadV_zero]
        exact ih q (snd_lt_code p q k s) hq hqg
      · rw [hA, leadV_one]
        exact hqg
      · rw [hA, leadV_two]
        exact hLg

/-- `g ≺₁ φ_1(g)` for a normal `g` which is not already a fixed point of `φ_1`. -/
lemma lt_iepsilon_of_not_fix {g : V} (hg : isNF₁ g) (h : epsFixIndic g ≠ 1) :
    icmp₁ g (vcVadd (vcVadd 0 0 1 0) g 1 0) = 0 := by
  rcases eq_or_ne g 0 with rfl | hg0
  · exact icmp₁_zero_vcVadd _ _ _ _
  · obtain ⟨a₁, a₂, m, d, rfl⟩ : ∃ a b n c, g = vcVadd a b n c :=
      ⟨_, _, _, _, (vcVadd_destruct hg0).symm⟩
    obtain ⟨hm, ha₁, ha₂, hd, hL, hfix, -⟩ := nf_parts hg
    rw [Ne, epsFixIndic_eq_one_iff] at h
    simp only [vcCoeff_vcVadd, vcTail_vcVadd, vcFst_vcVadd] at h
    have ha₂g : icmp₁ a₂ (vcVadd a₁ a₂ m d) = 0 := lt_of_lt_lead ha₂ hm hfix
    apply lt_of_lead_lt hm _root_.one_ne_zero
    rw [icmp₁_lead_lead]
    rcases icmp₁_cases ha₁ (isNF₁_one (V := V)) with hA | hA | hA
    · rw [hA, leadV_zero]
      exact lt_eps_of_lt _ hg a₂ ha₂ ha₂g
    · rw [hA, leadV_one]
      exact ha₂g
    · rw [hA, leadV_two]
      have hA' : icmp₁ (vcVadd 0 0 1 0 : V) a₁ = 0 :=
        icmp₁_rev_two ha₁ (isNF₁_one (V := V)) hA
      rcases eq_or_ne m 1 with rfl | hm1
      · have hd0 : d ≠ 0 := by
          rintro rfl
          exact h ⟨vcVadd_ne_zero _ _ _ _, rfl, rfl, hA'⟩
        rw [icmp₁_lead_form _root_.one_ne_zero _root_.one_ne_zero, icmp₁_self hL,
          thenV_one_left, cmpV_self, thenV_one_left]
        exact icmp₁_zero_pos hd0
      · rw [icmp₁_lead_form _root_.one_ne_zero hm, icmp₁_self hL, thenV_one_left]
        refine thenV_eq_zero.mpr (Or.inl (cmpV_eq_zero.mpr ?_))
        exact lt_of_le_of_ne (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hm)) (Ne.symm hm1)

/-! ## Normality, and the two directions of monotonicity -/

lemma isNF₁_iepsilon {g : V} (hg : isNF₁ g) : isNF₁ (iepsilon g) := by
  by_cases h : epsFixIndic g = 1
  · rw [iepsilon_of_fix h]; exact hg
  · rw [iepsilon_of_not_fix h]
    exact isNF₁_of_parts isNF₁_one hg (lt_iepsilon_of_not_fix hg h) _root_.one_ne_zero
      isNF₁_zero (icmp₁_zero_vcVadd _ _ _ _)

/-- Every value of the internal ε-function is an ε-number. -/
lemma fixIndic_iepsilon (g : V) : fixIndic (iepsilon g) = 1 := by
  by_cases h : epsFixIndic g = 1
  · rw [iepsilon_of_fix h, fixIndic_eq_one_iff]
    obtain ⟨hg0, hn, ht, hc⟩ := (epsFixIndic_eq_one_iff g).1 h
    refine ⟨hg0, hn, ht, ?_⟩
    intro h0
    rw [h0] at hc
    exact icmp₁_right_zero_ne_zero _ hc
  · rw [iepsilon_of_not_fix h, fixIndic_vcVadd]
    exact ⟨rfl, rfl, vcVadd_ne_zero 0 0 1 0⟩

/-- **Every ε-number is a value of the internal ε-function.** -/
theorem eps_surj {e : V} (he : isNF₁ e) (hfix : fixIndic e = 1) :
    ∃ h : V, isNF₁ h ∧ iepsilon h = e := by
  obtain ⟨p, q, rfl, hp⟩ := fix_destruct hfix
  obtain ⟨-, hpNF, hqNF, -, hL, hqL, -⟩ := nf_parts he
  rcases icmp₁_cases (isNF₁_one (V := V)) hpNF with hA | hA | hA
  · -- `1 ≺₁ p`: the term is itself a fixed point of `φ_1`
    refine ⟨vcVadd p q 1 0, he, iepsilon_of_fix ?_⟩
    rw [epsFixIndic_eq_one_iff]
    refine ⟨vcVadd_ne_zero _ _ _ _, by simp, by simp, ?_⟩
    simpa using hA
  · -- `p = 1`: the term is `φ_1(q)`
    have hp1 : (vcVadd 0 0 1 0 : V) = p :=
      icmp₁_eq_imp_eq (isNF₁_one (V := V)) hpNF hA
    subst hp1
    refine ⟨q, hqNF, iepsilon_of_not_fix ?_⟩
    intro hq
    obtain ⟨p', q', hq', hp'⟩ := epsFix_destruct hq
    have hrev : icmp₁ (vcVadd (vcVadd 0 0 1 0) q 1 0) q = 2 :=
      icmp₁_rev_zero hqNF hL hqL
    have hcalc :
        icmp₁ (vcVadd (vcVadd 0 0 1 0) q 1 0) (vcVadd p' q' 1 0) = 1 := by
      rw [icmp₁_lead_lead, hp', leadV_zero, ← hq', icmp₁_self hqNF]
    rw [← hq'] at hcalc
    rw [hcalc] at hrev
    exact (one_lt_two).ne' hrev.symm
  · -- `p ≺₁ 1`: impossible, `p ≠ 0`
    exact absurd
      (eq_zero_of_lt_one hpNF (icmp₁_rev_two (isNF₁_one (V := V)) hpNF hA)) hp

/-- The internal ε-function is strictly monotone. -/
theorem iepsilon_mono {g h : V} (hg : isNF₁ g) (hh : isNF₁ h)
    (hgh : icmp₁ g h = 0) : icmp₁ (iepsilon g) (iepsilon h) = 0 := by
  by_cases hfg : epsFixIndic g = 1 <;> by_cases hfh : epsFixIndic h = 1
  · rw [iepsilon_of_fix hfg, iepsilon_of_fix hfh]
    exact hgh
  · rw [iepsilon_of_fix hfg, iepsilon_of_not_fix hfh]
    exact lt_eps_of_lt _ hh g hg hgh
  · rw [iepsilon_of_not_fix hfg, iepsilon_of_fix hfh]
    obtain ⟨p, q, hq', hp'⟩ := epsFix_destruct hfh
    have hcalc :
        icmp₁ (vcVadd (vcVadd 0 0 1 0) g 1 0) (vcVadd p q 1 0) =
          icmp₁ g (vcVadd p q 1 0) := by
      rw [icmp₁_lead_lead, hp', leadV_zero]
    rw [← hq'] at hcalc
    rw [hcalc]
    exact hgh
  · rw [iepsilon_of_not_fix hfg, iepsilon_of_not_fix hfh, icmp₁_lead_lead,
      icmp₁_self (isNF₁_one (V := V)), leadV_one]
    exact hgh

/-- **(EPSMONO)**  `ε_h ≺₁ ε_g → h ≺₁ g`. -/
theorem eps_mono {g h : V} (hg : isNF₁ g) (hh : isNF₁ h)
    (hlt : icmp₁ (iepsilon h) (iepsilon g) = 0) : icmp₁ h g = 0 := by
  rcases icmp₁_cases hh hg with hc | hc | hc
  · exact hc
  · exfalso
    rw [icmp₁_eq_imp_eq hh hg hc, icmp₁_self (isNF₁_iepsilon hg)] at hlt
    exact _root_.one_ne_zero hlt
  · exfalso
    have hgh : icmp₁ g h = 0 := icmp₁_rev_two hh hg hc
    have hrev := icmp₁_rev_zero (isNF₁_iepsilon hg) (isNF₁_iepsilon hh)
      (iepsilon_mono hg hh hgh)
    rw [hlt] at hrev
    exact _root_.two_ne_zero hrev.symm

end OrdinalAnalysis.Gentzen.InternalEpsMono
