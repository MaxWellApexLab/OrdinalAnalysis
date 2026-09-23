/-
  The internal two-argument Veblen function on the Veblen codes.

  `iveblen a g` is the code of `φ_a(g)`, generalising `InternalEpsMono.iepsilon` (the case
  `a = 1`, since `φ_1 = ε`) from the fixed base "1" to an arbitrary normal code `a`.

  `vebFixIndic a g` generalises `epsFixIndic`: `g` is already a fixed point of `φ_a`,
  syntactically, when it is a single Veblen term `φ_p(q)` with `a ≺₁ p` (`epsFixIndic` is
  exactly the case `a = 1`, i.e. `a`'s code `vcVadd 0 0 1 0`).  `iveblen` mirrors
  `VNote.veblenNote`: it returns `g` itself when `g` already passes that test, and
  `vcVadd a g 1 0` otherwise.

  The two order facts generalise `InternalEpsMono.lt_eps_of_lt` /
  `InternalEpsMono.lt_iepsilon_of_not_fix` verbatim, replacing the hard-coded code of `1` by
  the parameter `a` and `InternalEpsCover.isNF₁_one` by the hypothesis `isNF₁ a`; the case
  split inside them is on `icmp₁ p a` instead of `icmp₁ p 1`, which is exactly the three-way
  Veblen comparison rule `Ordinal.cmp_veblen` read at the leading terms.  As in
  `InternalEpsMono`, `lt_veb_of_lt` cannot be replaced by `InternalVNoteOrder.lt_lead_of_lt_snd`
  because that lemma already assumes normality of the right-hand single term — exactly the
  fact `lt_iveblen_of_not_fix` is establishing — so it is re-proved by its own course-of-values
  induction on the left argument, with `a` and `g` as fixed parameters of the statement (not
  quantified inside the induction predicate).

  `iveblen_mono` / `veb_mono` are `iepsilon_mono` / `eps_mono` under the same substitution.
  `veb_surj` is stated exactly as design §4 G3 requests it, from the hypothesis that `e` is
  *already* a fixed point of `φ_a`; the harder statement — every single term `φ_p(q)` with
  `p` not below `a` is `φ_a(h)` for some `h` — is `InternalEpsMono.eps_surj`'s actual content
  at `a = 1` and is left as a follow-up (its proof needs a genuine trichotomy on `icmp₁ p a`,
  not just the fixed-point case).
-/
import OrdinalAnalysis.Gentzen.InternalEpsMono
import OrdinalAnalysis.Gentzen.VNoteBridge

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OrdinalAnalysis.Gentzen.InternalVeblen

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.InternalVNote
open OrdinalAnalysis.Gentzen.InternalVNoteOrder
open OrdinalAnalysis.Gentzen.InternalVNoteJump
open OrdinalAnalysis.Gentzen.InternalEpsMono
open OrdinalAnalysis.Gentzen.InternalEpsCover (isNF₁_one)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The syntactic fixed-point test of `φ_a` -/

/-- `0/1` flag: `g` is already a fixed point of `φ_a`, i.e. a single Veblen term `φ_p(q)` with
`a ≺₁ p`.  This generalises `InternalEpsMono.epsFixIndic` (the case `a = vcVadd 0 0 1 0`, the
code of `1`) from the fixed base `1` to an arbitrary base `a`. -/
noncomputable def vebFixIndic (a g : V) : V :=
  if g ≠ 0 ∧ vcCoeff g = 1 ∧ vcTail g = 0 ∧ icmp₁ a (vcFst g) = 0 then 1 else 0

def _root_.LO.FirstOrder.Arithmetic.vebFixIndicDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y a g. ∃ n, !vcCoeffDef n g ∧ ∃ t, !sndIdxDef t g ∧ ∃ f, !vcFstDef f g ∧
    ∃ c, !icmp₁Def c a f ∧
    ((g ≠ 0 ∧ n = 1 ∧ t = 0 ∧ c = 0 ∧ y = 1) ∨
      ((g = 0 ∨ n ≠ 1 ∨ t ≠ 0 ∨ c ≠ 0) ∧ y = 0))”

instance vebFixIndic_defined :
    𝚺₁-Function₂ (vebFixIndic : V → V → V) via vebFixIndicDef := .mk fun v ↦ by
  simp [vebFixIndicDef, vebFixIndic, vcCoeff_defined.iff, vcTail, sndIdx_defined.iff,
    vcFst_defined.iff, icmp₁_defined.iff]
  by_cases h0 : v 2 = 0 <;> by_cases h1 : vcCoeff (v 2) = 1 <;>
    by_cases h2 : sndIdx (v 2) = 0 <;>
    by_cases h3 : icmp₁ (v 1) (vcFst (v 2)) = 0 <;> simp [h0, h1, h2, h3]

instance vebFixIndic_definable : 𝚺₁-Function₂ (vebFixIndic : V → V → V) :=
  vebFixIndic_defined.to_definable

lemma vebFixIndic_eq_one_iff (a g : V) :
    vebFixIndic a g = 1 ↔
      (g ≠ 0 ∧ vcCoeff g = 1 ∧ vcTail g = 0 ∧ icmp₁ a (vcFst g) = 0) := by
  unfold vebFixIndic
  split_ifs with h <;> simp [h]

/-- `vebFixIndic` in constructor form, the shape the well-formedness proofs consume without an
extra decode step (compare `InternalVNoteJump.fixIndic_vcVadd`). -/
lemma vebFixIndic_vcVadd (a p q n c : V) :
    vebFixIndic a (vcVadd p q n c) = 1 ↔ (n = 1 ∧ c = 0 ∧ icmp₁ a p = 0) := by
  rw [vebFixIndic_eq_one_iff]
  simp

/-- A fixed point of `φ_a` is a single Veblen term with first argument above `a`. -/
lemma vebFix_destruct {a g : V} (h : vebFixIndic a g = 1) :
    ∃ p q : V, g = vcVadd p q 1 0 ∧ icmp₁ a p = 0 := by
  obtain ⟨hg0, hn, ht, hc⟩ := (vebFixIndic_eq_one_iff a g).1 h
  refine ⟨vcFst g, vcSnd g, ?_, hc⟩
  calc g = vcVadd (vcFst g) (vcSnd g) (vcCoeff g) (vcTail g) := (vcVadd_destruct hg0).symm
    _ = vcVadd (vcFst g) (vcSnd g) 1 0 := by rw [hn, ht]

/-! ## The internal two-argument Veblen function -/

/-- **The internal Veblen function** `iveblen a g = φ_a(g)`, total, mirroring
`VNote.veblenNote a`.  `iepsilon` is the case `a = vcVadd 0 0 1 0` (the code of `1`), see
`iveblen_one`. -/
noncomputable def iveblen (a g : V) : V :=
  if vebFixIndic a g = 1 then g else vcVadd a g 1 0

def _root_.LO.FirstOrder.Arithmetic.iveblenDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y a g. ∃ q, !vebFixIndicDef q a g ∧
    ((q = 1 ∧ y = g) ∨ (q ≠ 1 ∧ !vcVaddDef y a g 1 0))”

instance iveblen_defined :
    𝚺₁-Function₂ (iveblen : V → V → V) via iveblenDef := .mk fun v ↦ by
  simp [iveblenDef, iveblen, vebFixIndic_defined.iff, vcVadd_defined.iff]
  by_cases h : vebFixIndic (v 1) (v 2) = 1 <;> simp [h]

instance iveblen_definable : 𝚺₁-Function₂ (iveblen : V → V → V) :=
  iveblen_defined.to_definable

lemma iveblen_of_fix {a g : V} (h : vebFixIndic a g = 1) : iveblen a g = g := by
  simp [iveblen, h]

lemma iveblen_of_not_fix {a g : V} (h : vebFixIndic a g ≠ 1) :
    iveblen a g = vcVadd a g 1 0 := by
  simp [iveblen, h]

/-! ## `g ≺₁ φ_a(g)` -/

/--
**(T'') for `φ_a`, with no normal-form hypothesis on the right-hand term.**  `x ≺₁ g` gives
`x ≺₁ φ_a(g)`.  `InternalVNoteOrder.lt_lead_of_lt_snd` would need `isNF₁ (φ_a(g))`, which is
exactly what `lt_iveblen_of_not_fix` is about to establish; this proof recurses on `x` instead
and so is free of that hypothesis.  Generalises `InternalEpsMono.lt_eps_of_lt` (the case
`a = vcVadd 0 0 1 0`).
-/
lemma lt_veb_of_lt (a : V) (ha : isNF₁ a) (g : V) (hg : isNF₁ g) : ∀ x : V, isNF₁ x →
    icmp₁ x g = 0 → icmp₁ x (vcVadd a g 1 0) = 0 := by
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
      rcases icmp₁_cases hp ha with hA | hA | hA
      · rw [hA, leadV_zero]
        exact ih q (snd_lt_code p q k s) hq hqg
      · rw [hA, leadV_one]
        exact hqg
      · rw [hA, leadV_two]
        exact hLg

/-- `g ≺₁ φ_a(g)` for a normal `g` which is not already a fixed point of `φ_a`.  Generalises
`InternalEpsMono.lt_iepsilon_of_not_fix`. -/
lemma lt_iveblen_of_not_fix {a g : V} (ha : isNF₁ a) (hg : isNF₁ g)
    (h : vebFixIndic a g ≠ 1) : icmp₁ g (vcVadd a g 1 0) = 0 := by
  rcases eq_or_ne g 0 with rfl | hg0
  · exact icmp₁_zero_vcVadd _ _ _ _
  · obtain ⟨p, q, m, d, rfl⟩ : ∃ p q n c, g = vcVadd p q n c :=
      ⟨_, _, _, _, (vcVadd_destruct hg0).symm⟩
    obtain ⟨hm, hp, hq, hd, hL, hfix, -⟩ := nf_parts hg
    rw [Ne, vebFixIndic_eq_one_iff] at h
    simp only [vcCoeff_vcVadd, vcTail_vcVadd, vcFst_vcVadd] at h
    have hqg : icmp₁ q (vcVadd p q m d) = 0 := lt_of_lt_lead hq hm hfix
    apply lt_of_lead_lt hm _root_.one_ne_zero
    rw [icmp₁_lead_lead]
    rcases icmp₁_cases hp ha with hA | hA | hA
    · rw [hA, leadV_zero]
      exact lt_veb_of_lt a ha _ hg q hq hqg
    · rw [hA, leadV_one]
      exact hqg
    · rw [hA, leadV_two]
      have hA' : icmp₁ a p = 0 := icmp₁_rev_two hp ha hA
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

/-! ## Normality -/

/-- **The value of `iveblen` is always normal.** -/
theorem isNF₁_iveblen {a g : V} (ha : isNF₁ a) (hg : isNF₁ g) : isNF₁ (iveblen a g) := by
  by_cases h : vebFixIndic a g = 1
  · rw [iveblen_of_fix h]; exact hg
  · rw [iveblen_of_not_fix h]
    exact isNF₁_of_parts ha hg (lt_iveblen_of_not_fix ha hg h) _root_.one_ne_zero
      isNF₁_zero (icmp₁_zero_vcVadd _ _ _ _)

/-- **`iveblen a g` is an ω-fixed point** whenever the base `a` is nonzero: it is a single
Veblen term with nonzero first argument, hence `fixIndic (iveblen a g) = 1`.  (At `a = 0`,
`iveblen 0 g` collapses to `ω ^ g` only when `g` is not already `≥ 1` in index, which need not
be an ω-fixed point — the hypothesis `a ≠ 0` is exactly what is needed.) -/
theorem fixIndic_iveblen {a : V} (ha0 : a ≠ 0) (g : V) : fixIndic (iveblen a g) = 1 := by
  by_cases h : vebFixIndic a g = 1
  · rw [iveblen_of_fix h, fixIndic_eq_one_iff]
    obtain ⟨hg0, hn, ht, hc⟩ := (vebFixIndic_eq_one_iff a g).1 h
    refine ⟨hg0, hn, ht, ?_⟩
    intro h0
    rw [h0] at hc
    exact icmp₁_right_zero_ne_zero _ hc
  · rw [iveblen_of_not_fix h, fixIndic_vcVadd]
    exact ⟨rfl, rfl, ha0⟩

/-- **`iveblen a g` is a fixed point of every `φ_{a'}` with `a' ≺₁ a`.**  This is the coded form
of `Ordinal.veblen_veblen_of_lt`: once the base drops below `a`, `φ_a(g)` no longer moves. -/
theorem vebFixIndic_iveblen {a a' g : V} (ha' : isNF₁ a') (ha : isNF₁ a) (hg : isNF₁ g)
    (h : icmp₁ a' a = 0) : vebFixIndic a' (iveblen a g) = 1 := by
  by_cases hf : vebFixIndic a g = 1
  · rw [iveblen_of_fix hf]
    obtain ⟨p, q, hgeq, hp⟩ := vebFix_destruct hf
    rw [hgeq] at hg ⊢
    obtain ⟨-, hpNF, -, -, -, -, -⟩ := nf_parts hg
    rw [vebFixIndic_vcVadd]
    exact ⟨rfl, rfl, icmp₁_trans ha' ha hpNF h hp⟩
  · rw [iveblen_of_not_fix hf, vebFixIndic_vcVadd]
    exact ⟨rfl, rfl, h⟩

/-- **Agreement with the internal ε-function.**  `φ_1` is `iepsilon`: the case `a` = the code
of `1`. -/
lemma vebFixIndic_one (g : V) : vebFixIndic (vcVadd 0 0 1 0 : V) g = epsFixIndic g := rfl

theorem iveblen_one (g : V) : iveblen (vcVadd 0 0 1 0 : V) g = iepsilon g := by
  unfold iveblen iepsilon
  rw [vebFixIndic_one]

/-! ## Surjectivity onto the fixed points -/

/-- **Every fixed point of `φ_a` is a value of `iveblen a`.**  (The harder statement — every
single term `φ_p(q)` with `p` not below `a` is `φ_a(h)` for some `h`, generalising
`InternalEpsMono.eps_surj` past the fixed-point case — is left as a follow-up; see the file
header.) -/
theorem veb_surj {a e : V} (ha : isNF₁ a) (he : isNF₁ e) (hfix : vebFixIndic a e = 1) :
    ∃ h : V, isNF₁ h ∧ iveblen a h = e :=
  ⟨e, he, iveblen_of_fix hfix⟩

/-! ## Non-strict monotonicity in the first argument -/

/-- `g ⪯ φ_a(g)` always, on normal codes: the general fact `Ordinal.right_le_veblen`, coded. -/
lemma le_iveblen_right {a g : V} (ha : isNF₁ a) (hg : isNF₁ g) :
    icmp₁ g (iveblen a g) ≠ 2 := by
  by_cases h : vebFixIndic a g = 1
  · rw [iveblen_of_fix h, icmp₁_self hg]
    exact (one_lt_two).ne
  · rw [iveblen_of_not_fix h, lt_iveblen_of_not_fix ha hg h]
    exact fun h2 => _root_.two_ne_zero h2.symm

/-- **Non-strict monotonicity of `iveblen` in its first argument.**  `φ` is not strictly
monotone there (fixed points of `φ_a` are fixed points of every `φ_{a'}` with `a ≺₁ a'` too,
`vebFixIndic_iveblen`), but it never decreases. -/
theorem iveblen_mono_left {a a' g : V} (ha : isNF₁ a) (ha' : isNF₁ a') (hg : isNF₁ g)
    (hlt : icmp₁ a a' = 0) : icmp₁ (iveblen a g) (iveblen a' g) ≠ 2 := by
  by_cases hfa : vebFixIndic a g = 1 <;> by_cases hfa' : vebFixIndic a' g = 1
  · rw [iveblen_of_fix hfa, iveblen_of_fix hfa', icmp₁_self hg]
    exact (one_lt_two).ne
  · rw [iveblen_of_fix hfa]
    exact le_iveblen_right ha' hg
  · exfalso
    obtain ⟨p, q, hgeq, hp⟩ := vebFix_destruct hfa'
    rw [hgeq] at hg
    obtain ⟨-, hpNF, -, -, -, -, -⟩ := nf_parts hg
    have : vebFixIndic a g = 1 := by
      rw [hgeq, vebFixIndic_vcVadd]
      exact ⟨rfl, rfl, icmp₁_trans ha ha' hpNF hlt hp⟩
    exact hfa this
  · rw [iveblen_of_not_fix hfa, iveblen_of_not_fix hfa', icmp₁_lead_lead, hlt, leadV_zero,
      lt_iveblen_of_not_fix ha' hg hfa']
    exact fun h2 => _root_.two_ne_zero h2.symm

/-! ## The two directions of monotonicity in the second argument -/

/-- **The internal Veblen function is strictly monotone in its second argument.** -/
theorem iveblen_mono {a g h : V} (ha : isNF₁ a) (hg : isNF₁ g) (hh : isNF₁ h)
    (hlt : icmp₁ h g = 0) : icmp₁ (iveblen a h) (iveblen a g) = 0 := by
  by_cases hfh : vebFixIndic a h = 1 <;> by_cases hfg : vebFixIndic a g = 1
  · rw [iveblen_of_fix hfh, iveblen_of_fix hfg]
    exact hlt
  · rw [iveblen_of_fix hfh, iveblen_of_not_fix hfg]
    exact lt_veb_of_lt a ha g hg h hh hlt
  · rw [iveblen_of_not_fix hfh, iveblen_of_fix hfg]
    obtain ⟨p, q, hq', hp'⟩ := vebFix_destruct hfg
    have hcalc :
        icmp₁ (vcVadd a h 1 0) (vcVadd p q 1 0) = icmp₁ h (vcVadd p q 1 0) := by
      rw [icmp₁_lead_lead, hp', leadV_zero]
    rw [← hq'] at hcalc
    rw [hcalc]
    exact hlt
  · rw [iveblen_of_not_fix hfh, iveblen_of_not_fix hfg, icmp₁_lead_lead,
      icmp₁_self ha, leadV_one]
    exact hlt

/-- **The converse of `iveblen_mono`.** -/
theorem veb_mono {a g h : V} (ha : isNF₁ a) (hg : isNF₁ g) (hh : isNF₁ h)
    (hlt : icmp₁ (iveblen a h) (iveblen a g) = 0) : icmp₁ h g = 0 := by
  rcases icmp₁_cases hh hg with hc | hc | hc
  · exact hc
  · exfalso
    rw [icmp₁_eq_imp_eq hh hg hc, icmp₁_self (isNF₁_iveblen ha hg)] at hlt
    exact _root_.one_ne_zero hlt
  · exfalso
    have hgh : icmp₁ g h = 0 := icmp₁_rev_two hh hg hc
    have hrev := icmp₁_rev_zero (isNF₁_iveblen ha hg) (isNF₁_iveblen ha hh)
      (iveblen_mono ha hh hg hgh)
    rw [hlt] at hrev
    exact _root_.two_ne_zero hrev.symm

/-! ## The bridge to the external Veblen notations -/

open OrdinalAnalysis.Gentzen.VNoteBridge (vmodelCode vmodelCode_vadd vmodelCode_zero
  vmodelCode_vadd_one_zero icmp₁_modelCode_eq_zero_iff vcode_injective)

/-- **`iveblen` computes `VNote.veblenNote` on codes.**  This is what identifies the internal
`φ_a(g)` with the external one: the upper-bound argument produces internal Veblen values and
needs to recognise them as codes of genuine `Gamma0Note`s. -/
theorem iveblen_vmodelCode (a : VNote) {b : VNote} :
    iveblen (vmodelCode (V := V) a) (vmodelCode (V := V) b) =
      vmodelCode (V := V) (VNote.veblenNote a b) := by
  cases b with
  | zero =>
    have h0 : vebFixIndic (vmodelCode (V := V) a) (vmodelCode (V := V) (VNote.zero)) ≠ 1 := by
      simp only [VNote.zero_def, vmodelCode_zero]
      intro h
      rw [vebFixIndic_eq_one_iff] at h
      exact h.1 rfl
    rw [iveblen_of_not_fix h0]
    show vcVadd (vmodelCode (V := V) a) (vmodelCode (V := V) VNote.zero) 1 0 =
      vmodelCode (V := V) (VNote.veblenNote a VNote.zero)
    simp [VNote.veblenNote, vmodelCode_vadd]
  | vadd b₁ b₂ n c =>
    by_cases htest : n = 1 ∧ c = 0 ∧ VNote.cmp a b₁ = Ordering.lt
    · obtain ⟨hn, hc, hcmp⟩ := htest
      subst hn; subst hc
      have hval : VNote.veblenNote a (VNote.vadd b₁ b₂ 1 0) = VNote.vadd b₁ b₂ 1 0 := by
        simp [VNote.veblenNote, hcmp]
      rw [hval]
      apply iveblen_of_fix
      rw [vmodelCode_vadd, vebFixIndic_vcVadd]
      refine ⟨by norm_cast, rfl, (icmp₁_modelCode_eq_zero_iff a b₁).2 hcmp⟩
    · have hval : VNote.veblenNote a (VNote.vadd b₁ b₂ n c)
          = VNote.vadd a (VNote.vadd b₁ b₂ n c) 1 0 := by
        simp only [VNote.veblenNote, if_neg htest]
      rw [hval, vmodelCode_vadd_one_zero]
      apply iveblen_of_not_fix
      rw [vmodelCode_vadd]
      intro hfix
      rw [vebFixIndic_vcVadd] at hfix
      obtain ⟨hn1, hc0, hcmp0⟩ := hfix
      apply htest
      refine ⟨by exact_mod_cast hn1, ?_, (icmp₁_modelCode_eq_zero_iff a b₁).1 hcmp0⟩
      apply vcode_injective
      have hcast : (VNoteBridge.vcode c : V) = (VNoteBridge.vcode (0 : VNote) : V) := by
        show vmodelCode (V := V) c = vmodelCode (V := V) (0 : VNote)
        rw [vmodelCode_zero]
        exact hc0
      exact_mod_cast hcast

/-- The `Gamma0Note`-level form of `iveblen_vmodelCode`, using `VNoteBridge.gamma0ModelCode`. -/
theorem iveblen_gamma0ModelCode (a b : Gamma0Note) :
    iveblen (VNoteBridge.gamma0ModelCode (V := V) a) (VNoteBridge.gamma0ModelCode (V := V) b) =
      VNoteBridge.gamma0ModelCode (V := V) (Gamma0Note.veblenNote a b) := by
  simp only [VNoteBridge.gamma0ModelCode_eq]
  exact iveblen_vmodelCode a.1

end OrdinalAnalysis.Gentzen.InternalVeblen
