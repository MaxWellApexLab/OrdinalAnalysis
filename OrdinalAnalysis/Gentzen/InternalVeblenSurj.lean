/-
  The real surjectivity of the internal two-argument Veblen function.

  `InternalVeblen.veb_surj` is, as its own docstring says, trivial: from the hypothesis that
  `e` is *already* a fixed point of `φ_a` the witness is `e` itself.  The statement the Γ₀
  upper bound needs is the one `InternalEpsMono.eps_surj` proves at `a = 1`: **every common
  fixed point of all the `φ_{a'}` with `a' ≺₁ a` is a value of `φ_a`.**

  The `a = 1` instance is exactly `eps_surj`: `a' ≺₁ 1` forces `a' = 0`, and
  `vebFixIndic 0 = fixIndic` (`vebFixIndic_zero`), so the hypothesis degenerates to
  "`e` is an ε-number" — see `forall_fix_one_iff` and `veb_surj'_one`.

  ## The shape of the argument

  The `∀ a' ≺₁ a` hypothesis is not a bounded quantifier (the code order `≺₁` and the
  numerical order on codes are different), so it is **not** `𝚺₁` as it stands.  It is,
  however, equivalent to a plain `𝚺₁` test on the code shape of `e`:

      `vebBaseIndic a e = 1`  :⇔  `e = φ_p(q)` for some `p` with `a ≼₁ p`,

  and that equivalence (`vebBaseIndic_iff_forall`, for `a ≠ 0`) is what makes the object-language
  carry in `InternalVeblenCode.lean` possible at all.  Both directions are cheap:

  * `⇐` : instantiate the hypothesis at `a' := 0` to learn that `e` is a single term `φ_p(q)`
    with `p ≠ 0`, then at `a' := p` to rule out `p ≺₁ a` (it would give `p ≺₁ p`);
  * `⇒` : `a' ≺₁ a ≼₁ p` gives `a' ≺₁ p`, i.e. `vebFixIndic a' e = 1`, by transitivity.

  From `vebBaseIndic a e = 1` the surjectivity itself is the three-way Veblen trichotomy on
  `icmp₁ p a`, exactly as in `eps_surj`:

  * `a ≺₁ p` — `e` is already a fixed point of `φ_a`, so `h := e`;
  * `p = a`  — `e = φ_a(q)`, so `h := q`; the work is showing `q` is *not* itself a fixed
    point of `φ_a`, which is the middle case of `eps_surj` verbatim with `1` replaced by `a`;
  * `p ≺₁ a` — excluded by the hypothesis.

  ## `a ≠ 0` is necessary for the `∀`-form, and only for it

  At `a = 0` the hypothesis `∀ a' ≺₁ 0, …` is vacuous while the conclusion is false: `2`
  (the normal code `vcVadd 0 0 2 0`) is not a value of `iveblen 0 = ω ^ ·`, whose values all
  have coefficient `1`.  The code-shape form `veb_surj'` needs no such hypothesis — at `a = 0`
  it says every *additively principal* normal code is an ω-power, which is true.
-/
import OrdinalAnalysis.Gentzen.InternalVeblen

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OrdinalAnalysis.Gentzen.InternalVeblenSurj

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.InternalVNote
open OrdinalAnalysis.Gentzen.InternalVNoteOrder
open OrdinalAnalysis.Gentzen.InternalVNoteJump
open OrdinalAnalysis.Gentzen.InternalEpsMono
open OrdinalAnalysis.Gentzen.InternalVeblen
open OrdinalAnalysis.Gentzen.InternalEpsCover (isNF₁_one)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## `icmp₁` against `0` -/

lemma icmp₁_zero_eq_zero_iff (x : V) : icmp₁ (0 : V) x = 0 ↔ x ≠ 0 := by
  constructor
  · rintro h rfl
    rw [icmp₁_zero_zero] at h
    exact _root_.one_ne_zero h
  · exact icmp₁_zero_pos

/-- At base `0` the internal Veblen fixed-point test is the ω-power fixed-point test:
`φ_0 = ω ^ ·`, and its fixed points are the codes `φ_p(q)` with `p ≠ 0`. -/
lemma vebFixIndic_zero (g : V) : vebFixIndic (0 : V) g = fixIndic g := by
  unfold vebFixIndic fixIndic
  simp only [icmp₁_zero_eq_zero_iff]

/-- At base `0` the internal Veblen function is the ω-power. -/
lemma iveblen_zero (g : V) : iveblen (0 : V) g = iomegaPow g := by
  by_cases h : fixIndic g = 1
  · rw [iveblen_of_fix (by rw [vebFixIndic_zero]; exact h), iomegaPow_of_fix h]
  · rw [iveblen_of_not_fix (by rw [vebFixIndic_zero]; exact h), iomegaPow_of_not_fix h]

/-! ## The range indicator of `φ_a` -/

/-- `0/1` flag: `e` is a single Veblen term `φ_p(q)` with `a ≼₁ p` — equivalently (for `a ≠ 0`
and normal `e`, see `vebBaseIndic_iff_forall`) a common fixed point of every `φ_{a'}` with
`a' ≺₁ a`.  This is the `𝚺₁` form of "`e` is in the range of `φ_a`". -/
noncomputable def vebBaseIndic (a e : V) : V :=
  if e ≠ 0 ∧ vcCoeff e = 1 ∧ vcTail e = 0 ∧ icmp₁ (vcFst e) a ≠ 0 then 1 else 0

def _root_.LO.FirstOrder.Arithmetic.vebBaseIndicDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y a e. ∃ n, !vcCoeffDef n e ∧ ∃ t, !sndIdxDef t e ∧ ∃ f, !vcFstDef f e ∧
    ∃ c, !icmp₁Def c f a ∧
    ((e ≠ 0 ∧ n = 1 ∧ t = 0 ∧ c ≠ 0 ∧ y = 1) ∨
      ((e = 0 ∨ n ≠ 1 ∨ t ≠ 0 ∨ c = 0) ∧ y = 0))”

instance vebBaseIndic_defined :
    𝚺₁-Function₂ (vebBaseIndic : V → V → V) via vebBaseIndicDef := .mk fun v ↦ by
  simp [vebBaseIndicDef, vebBaseIndic, vcCoeff_defined.iff, vcTail, sndIdx_defined.iff,
    vcFst_defined.iff, icmp₁_defined.iff]
  by_cases h0 : v 2 = 0 <;> by_cases h1 : vcCoeff (v 2) = 1 <;>
    by_cases h2 : sndIdx (v 2) = 0 <;>
    by_cases h3 : icmp₁ (vcFst (v 2)) (v 1) = 0 <;> simp [h0, h1, h2, h3]

instance vebBaseIndic_definable : 𝚺₁-Function₂ (vebBaseIndic : V → V → V) :=
  vebBaseIndic_defined.to_definable

lemma vebBaseIndic_eq_one_iff (a e : V) :
    vebBaseIndic a e = 1 ↔
      (e ≠ 0 ∧ vcCoeff e = 1 ∧ vcTail e = 0 ∧ icmp₁ (vcFst e) a ≠ 0) := by
  unfold vebBaseIndic
  split_ifs with h <;> simp [h]

/-- `vebBaseIndic` in constructor form. -/
lemma vebBaseIndic_vcVadd (a p q n c : V) :
    vebBaseIndic a (vcVadd p q n c) = 1 ↔ (n = 1 ∧ c = 0 ∧ icmp₁ p a ≠ 0) := by
  rw [vebBaseIndic_eq_one_iff]
  simp

/-- A code in the range of `φ_a` is a single Veblen term with first argument `≽₁ a`. -/
lemma vebBase_destruct {a e : V} (h : vebBaseIndic a e = 1) :
    ∃ p q : V, e = vcVadd p q 1 0 ∧ icmp₁ p a ≠ 0 := by
  obtain ⟨he0, hn, ht, hc⟩ := (vebBaseIndic_eq_one_iff a e).1 h
  refine ⟨vcFst e, vcSnd e, ?_, hc⟩
  calc e = vcVadd (vcFst e) (vcSnd e) (vcCoeff e) (vcTail e) := (vcVadd_destruct he0).symm
    _ = vcVadd (vcFst e) (vcSnd e) 1 0 := by rw [hn, ht]

/-! ## The equivalence with the `∀`-form -/

/-- `⇒` of `vebBaseIndic_iff_forall`: a code of the form `φ_p(q)` with `a ≼₁ p` is a fixed
point of every `φ_{a'}` with `a' ≺₁ a`.  No hypothesis `a ≠ 0` is needed here. -/
theorem forall_of_vebBaseIndic_eq_one {a e : V} (ha : isNF₁ a) (he : isNF₁ e)
    (hbase : vebBaseIndic a e = 1) :
    ∀ a' : V, isNF₁ a' → icmp₁ a' a = 0 → vebFixIndic a' e = 1 := by
  obtain ⟨p, q, rfl, hpa⟩ := vebBase_destruct hbase
  obtain ⟨-, hp, -, -, -, -, -⟩ := nf_parts he
  intro a' ha' hlt
  rw [vebFixIndic_vcVadd]
  refine ⟨rfl, rfl, ?_⟩
  rcases icmp₁_cases hp ha with hc | hc | hc
  · exact absurd hc hpa
  · have hpe : p = a := icmp₁_eq_imp_eq hp ha hc
    rw [hpe]
    exact hlt
  · exact icmp₁_trans ha' ha hp hlt (icmp₁_rev_two hp ha hc)

/-- `⇐` of `vebBaseIndic_iff_forall`.  The hypothesis `a ≠ 0` is used twice: to instantiate at
`a' := 0` (which forces `e` to be a single term with nonzero first index) and nowhere else —
at `a = 0` the `∀`-hypothesis is vacuous and the conclusion genuinely fails. -/
theorem vebBaseIndic_eq_one_of_forall {a e : V} (ha0 : a ≠ 0) (he : isNF₁ e)
    (hfix : ∀ a' : V, isNF₁ a' → icmp₁ a' a = 0 → vebFixIndic a' e = 1) :
    vebBaseIndic a e = 1 := by
  have h0 := hfix 0 isNF₁_zero (icmp₁_zero_pos ha0)
  obtain ⟨p, q, rfl, -⟩ := vebFix_destruct h0
  obtain ⟨-, hp, -, -, -, -, -⟩ := nf_parts he
  rw [vebBaseIndic_vcVadd]
  refine ⟨rfl, rfl, ?_⟩
  intro hpa
  have h1 : icmp₁ p p = 0 := ((vebFixIndic_vcVadd p p q 1 0).1 (hfix p hp hpa)).2.2
  rw [icmp₁_self hp] at h1
  exact _root_.one_ne_zero h1

/-- **The `𝚺₁` form of "`e` is a common fixed point of every `φ_{a'}` with `a' ≺₁ a`".** -/
theorem vebBaseIndic_iff_forall {a e : V} (ha0 : a ≠ 0) (ha : isNF₁ a) (he : isNF₁ e) :
    vebBaseIndic a e = 1 ↔ ∀ a' : V, isNF₁ a' → icmp₁ a' a = 0 → vebFixIndic a' e = 1 :=
  ⟨forall_of_vebBaseIndic_eq_one ha he, vebBaseIndic_eq_one_of_forall ha0 he⟩

/-! ## The surjectivity -/

/--
**Surjectivity of `φ_a` onto the terms `φ_p(q)` with `a ≼₁ p`**, in destructed form.
The trichotomy on `icmp₁ p a` is `InternalEpsMono.eps_surj`'s, with the hard-coded code of `1`
replaced by `a`.
-/
theorem veb_surj_term {a p q : V} (ha : isNF₁ a) (he : isNF₁ (vcVadd p q 1 0))
    (hpa : icmp₁ p a ≠ 0) : ∃ h : V, isNF₁ h ∧ iveblen a h = vcVadd p q 1 0 := by
  obtain ⟨-, hp, hq, -, hL, hqL, -⟩ := nf_parts he
  rcases icmp₁_cases hp ha with hc | hc | hc
  · exact absurd hc hpa
  · -- `p = a`: the term is `φ_a(q)`, and `q` is not itself a fixed point of `φ_a`
    have hpe : p = a := icmp₁_eq_imp_eq hp ha hc
    subst hpe
    refine ⟨q, hq, iveblen_of_not_fix ?_⟩
    intro hfq
    obtain ⟨p', q', hq', hp'⟩ := vebFix_destruct hfq
    have hrev : icmp₁ (vcVadd p q 1 0) q = 2 := icmp₁_rev_zero hq hL hqL
    have hcalc : icmp₁ (vcVadd p q 1 0) (vcVadd p' q' 1 0) = 1 := by
      rw [icmp₁_lead_lead, hp', leadV_zero, ← hq', icmp₁_self hq]
    rw [← hq'] at hcalc
    rw [hcalc] at hrev
    exact (one_lt_two).ne' hrev.symm
  · -- `a ≺₁ p`: the term is already a fixed point of `φ_a`
    exact ⟨vcVadd p q 1 0, he,
      iveblen_of_fix ((vebFixIndic_vcVadd a p q 1 0).2 ⟨rfl, rfl, icmp₁_rev_two hp ha hc⟩)⟩

/-- **The real surjectivity**, in the `𝚺₁` code-shape form. -/
theorem veb_surj' {a e : V} (ha : isNF₁ a) (he : isNF₁ e) (hbase : vebBaseIndic a e = 1) :
    ∃ h : V, isNF₁ h ∧ iveblen a h = e := by
  obtain ⟨p, q, rfl, hpa⟩ := vebBase_destruct hbase
  exact veb_surj_term ha he hpa

/--
**The real surjectivity, as design §4 G3 states it.**  Every common fixed point of all the
`φ_{a'}` with `a' ≺₁ a` is a value of `φ_a`.  The extra hypothesis `a ≠ 0` cannot be dropped:
see the file header.
-/
theorem veb_surj'_forall {a e : V} (ha0 : a ≠ 0) (ha : isNF₁ a) (he : isNF₁ e)
    (hfix : ∀ a' : V, isNF₁ a' → icmp₁ a' a = 0 → vebFixIndic a' e = 1) :
    ∃ h : V, isNF₁ h ∧ iveblen a h = e :=
  veb_surj' ha he (vebBaseIndic_eq_one_of_forall ha0 he hfix)

/-! ## Agreement with `eps_surj` at `a = 1` -/

/-- At `a = 1` the `∀`-hypothesis of `veb_surj'_forall` is exactly "`e` is an ε-number". -/
theorem forall_fix_one_iff {e : V} :
    (∀ a' : V, isNF₁ a' → icmp₁ a' (vcVadd 0 0 1 0 : V) = 0 → vebFixIndic a' e = 1) ↔
      fixIndic e = 1 := by
  constructor
  · intro h
    have h0 := h 0 isNF₁_zero (icmp₁_zero_vcVadd 0 0 1 0)
    rwa [vebFixIndic_zero] at h0
  · intro h a' ha' hlt
    rw [eq_zero_of_lt_one ha' hlt, vebFixIndic_zero]
    exact h

/-- At `a = 1` the range indicator is the ε-number test. -/
theorem vebBaseIndic_one_iff {e : V} (he : isNF₁ e) :
    vebBaseIndic (vcVadd 0 0 1 0 : V) e = 1 ↔ fixIndic e = 1 := by
  constructor
  · intro h
    obtain ⟨p, q, rfl, hpa⟩ := vebBase_destruct h
    rw [fixIndic_vcVadd]
    refine ⟨rfl, rfl, ?_⟩
    rintro rfl
    exact hpa (icmp₁_zero_vcVadd 0 0 1 0)
  · intro h
    obtain ⟨p, q, rfl, hp⟩ := fix_destruct h
    obtain ⟨-, hpNF, -, -, -, -, -⟩ := nf_parts he
    rw [vebBaseIndic_vcVadd]
    refine ⟨rfl, rfl, ?_⟩
    intro hlt
    exact hp (eq_zero_of_lt_one hpNF hlt)

/-- **`veb_surj'` at `a = 1` is `InternalEpsMono.eps_surj`.** -/
theorem veb_surj'_one {e : V} (he : isNF₁ e) (hfix : fixIndic e = 1) :
    ∃ h : V, isNF₁ h ∧ iepsilon h = e := by
  obtain ⟨h, hh, hval⟩ := veb_surj' isNF₁_one he ((vebBaseIndic_one_iff he).2 hfix)
  refine ⟨h, hh, ?_⟩
  rw [← iveblen_one]
  exact hval

/-- `veb_surj'_forall` at `a = 1`, literally in the shape of `eps_surj`. -/
theorem veb_surj'_forall_one {e : V} (he : isNF₁ e)
    (hfix : ∀ a' : V, isNF₁ a' → icmp₁ a' (vcVadd 0 0 1 0 : V) = 0 → vebFixIndic a' e = 1) :
    ∃ h : V, isNF₁ h ∧ iepsilon h = e :=
  veb_surj'_one he (forall_fix_one_iff.1 hfix)

/-! ## (EPSMONO) at level `a` -/

/--
**(EPSMONO) at level `a`, with surjectivity folded in.**  If `e` is in the range of `φ_a` and
sits below `φ_a(g)`, then `e = φ_a(h)` for a normal `h ≺₁ g`.  This is
`InternalEpsMonoCode.eps_mono_of_surj` at an arbitrary base.
-/
theorem veb_mono_of_surj {a e g u : V} (ha : isNF₁ a) (he : isNF₁ e)
    (hbase : vebBaseIndic a e = 1) (hg : isNF₁ g) (hu : u = iveblen a g)
    (hlt : icmp₁ e u = 0) :
    ∃ h : V, isNF₁ h ∧ e = iveblen a h ∧ icmp₁ h g = 0 := by
  obtain ⟨h, hh, hhe⟩ := veb_surj' ha he hbase
  refine ⟨h, hh, hhe.symm, veb_mono ha hg hh ?_⟩
  rw [hhe, ← hu]
  exact hlt

end OrdinalAnalysis.Gentzen.InternalVeblenSurj
