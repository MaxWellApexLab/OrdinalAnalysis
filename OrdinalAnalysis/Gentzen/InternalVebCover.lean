/-
  The two-parameter cover of the Veblen codes: the Γ₀ analogue of `InternalEpsCover`.

  `InternalEpsCover.cover_aux` covers every normal code `x` by a finite **ω-tower** over a base
  which is `0` or an ε-number.  That is the `a = 1` case of what the Γ₀ upper bound needs, and
  the tower there iterates `φ_0 = ω ^ ·` because `a' ≺₁ 1` forces `a' = 0`.

  At a successor level `a = a₀ ⊕ 1` the same argument runs with `φ_0` replaced by `φ_{a₀}`:

  **(COV_{a₀})** for every normal code `x` there are `e` and `n` with

      `e = 0` or `vebFixIndic a₀ e = 1`,   `e ≼₁ x`,   and   `x ≺₁ φ_{a₀}^n(e ⊕ 1)`,

  where `φ_{a₀}^n` is the internal iteration `ivebTower a₀ · n` of `InternalVeblen.iveblen a₀`.
  The three cases of the induction are the design's, read at level `a₀`:

  * `x = 0` — take `e = 0`, `n = 0` (`φ_{a₀}^0(1) = 1`);
  * `x = φ_p(q)·m + t` with `a₀ ≺₁ p` — the head `φ_p(q)` is a fixed point of `φ_{a₀}`, so it is
    a base `≼₁ x`, and `φ_p(q)·m + t ≺₁ φ_{a₀}(φ_p(q) ⊕ 1)`: one tower level.  (At `a₀ = 0`
    this is `cover_aux`'s "the head is a fixed point" branch verbatim.)
  * `x = φ_p(q)·m + t` with `p ≼₁ a₀` — recurse on the *smaller code* `q` and spend one more
    tower level: `q ≺₁ u` gives `φ_p(q)·m + t ≺₁ φ_{a₀}(u)`, which is `lt_iveblen_of_lead`,
    the Veblen comparison rule at the leading terms.  (At `a₀ = 0` the side condition `p ≼₁ 0`
    is `p = 0` and the step is `ω^b·m + t ≺ ω^(ω_n(e+1))`.)

  At `a₀ = 0` the whole file degenerates to `InternalEpsCover`: `ivebTower 0 = itower`
  (`ivebTower_zero_left`) and `vebFixIndic 0 = fixIndic`
  (`InternalVeblenSurj.vebFixIndic_zero`), so `veb_cover_aux 0` *is* `cover_aux` —
  `tower_cover_level_one` re-derives `InternalEpsCover.tower_cover` from the general statement.

  ## Connecting the tower level `a₀` to the Veblen level `a`

  What the progressiveness argument for `ψ_a(g) :≡ ∀²X TIupto(≺₁, φ_a(g), X)` consumes is a
  base in the **range of `φ_a`** (`InternalVeblenSurj.vebBaseIndic a`), so that
  `InternalVeblenSurj.veb_surj'` can write it as `φ_a(h)` and `veb_mono` can place `h ≺₁ g`.
  The bridge from "fixed point of `φ_{a₀}`" to "in the range of `φ_a`" is the single hypothesis

      `hsucc : ∀ P, isNF₁ P → icmp₁ a₀ P = 0 → icmp₁ P a ≠ 0`      ("`a₀ ≺₁ P → a ≼₁ P`"),

  i.e. "`a` is the successor of `a₀`".  `veb_tower_cover_level` and `veb_cover_mono` are stated
  with it, so they are independent of how the successor is computed on codes; two instances are
  supplied here:

  * `succ_general` — `(a₀, a) = (a₀, a₀ ⊕ 1)` for an **arbitrary** normal `a₀`.  It rests on
    `no_between_succ`: *no normal code lies strictly between `z` and `z ⊕ 1`*, proved here by
    the bounded course-of-values idiom of `InternalVNoteOrder.icmp₁_trans_aux` (both codes
    bounded by a single `w`, so the induction predicate stays `Δ₁`) on top of
    `InternalVNoteJump.{tails_of_between, tail_of_between_succ}`;
  * `succ_zero_one` — `(a₀, a) = (0, 1)`, the ε-case, which *is* `InternalEpsMonoCode`'s setting;
  * `succ_term` — `(a₀, a) = (φ_p(q), φ_p(q) ⊕ 1)` for `p ≠ 0`, via
    `InternalVNoteOrder.lt_or_eq_of_lt_term_succ`.

  `veb_tower_cover_succ` and `veb_cover_mono_succ` are the resulting fully concrete
  successor-level statements, with `a := iadd₁ a₀ (code of 1)` throughout and no side
  hypothesis beyond `isNF₁ a₀`.

  ## The limit levels

  At a limit `a` there is no single `a₀`, and the fixed tower must be replaced by an iteration
  along a *finite sequence* of levels below `a`.  The statement the limit level needs is

      `∀ x, NF(x) → ∃ e w, NF(e) ∧ (e = 0 ∨ vebBaseIndic a e = 1) ∧ e ≼₁ x ∧
         Seq(w) ∧ (∀ i < lh w, NF(w_i) ∧ w_i ≺₁ a) ∧
         x ≺₁ φ_{w_{lh w - 1}}(… φ_{w_0}(e ⊕ 1) …)`,

  and the induction below proves it with **no new ordinal content**: case A uses the single
  level `0` (which is `≺₁ a` for `a ≠ 0`) and the computation is `cover_aux`'s, while case B
  uses the level `p` — the head index of `x`, which satisfies `p ≺₁ a` exactly in that branch —
  and the step is the same `lt_iveblen_of_lead` (its side condition `icmp₁ p p ≠ 0` is
  `icmp₁_self`).  The only missing ingredient is the internal sequence-indexed iteration
  `φ_{w_{k-1}}(…φ_{w_0}(c)…)` as a `PR.Construction` together with the fact that extending `w`
  on the right does not change the earlier stages; both are routine but were not built here.
-/
import OrdinalAnalysis.Gentzen.InternalVeblenSurj

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OrdinalAnalysis.Gentzen.InternalVebCover

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.InternalVNote
open OrdinalAnalysis.Gentzen.InternalVNoteOrder
open OrdinalAnalysis.Gentzen.InternalVNoteJump
open OrdinalAnalysis.Gentzen.VeblenTower
open OrdinalAnalysis.Gentzen.VeblenSuccStep (iadd₁_term_one)
open OrdinalAnalysis.Gentzen.InternalEpsCover (isNF₁_one isNF₁_succBase)
open OrdinalAnalysis.Gentzen.InternalEpsMono (iepsilon)
open OrdinalAnalysis.Gentzen.InternalVeblen
open OrdinalAnalysis.Gentzen.InternalVeblenSurj

/-! ## The internal Veblen tower -/

/-- `VebTow(a, c, 0) = c`, `VebTow(a, c, n+1) = φ_a(VebTow(a, c, n))`: `VeblenTower`'s
blueprint with `iomegaPow` replaced by `iveblen a`, carrying the level `a` as a second
parameter. -/
def vebTowerBlueprint : PR.Blueprint 2 where
  zero := .mkSigma “y a c. y = c”
  succ := .mkSigma “y ih k a c. !iveblenDef y a ih”

noncomputable def vebTowerConstruction {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : PR.Construction V vebTowerBlueprint where
  zero := fun v ↦ v 1
  succ := fun v _ ih ↦ iveblen (v 0) ih
  zero_defined := .mk fun v ↦ by simp [vebTowerBlueprint]
  succ_defined := .mk fun v ↦ by
    simp [vebTowerBlueprint, iveblen_defined.iff]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The internal Veblen tower**: `ivebTower a c n = φ_a(φ_a(…φ_a(c)…))` with `n`
applications. -/
noncomputable def ivebTower (a c n : V) : V := vebTowerConstruction.result ![a, c] n

@[simp] lemma ivebTower_zero (a c : V) : ivebTower a c 0 = c := by
  simp [ivebTower, vebTowerConstruction]

@[simp] lemma ivebTower_succ (a c n : V) :
    ivebTower a c (n + 1) = iveblen a (ivebTower a c n) := by
  simp [ivebTower, vebTowerConstruction]

lemma ivebTower_one (a c : V) : ivebTower a c 1 = iveblen a c := by
  have h := ivebTower_succ a c 0
  rwa [zero_add, ivebTower_zero] at h

/-- Result-first graph of the internal Veblen tower, argument order `(y, a, c, n)`. -/
def _root_.LO.FirstOrder.Arithmetic.ivebTowerDef : 𝚺₁.Semisentence 4 :=
  vebTowerBlueprint.resultDef.rew (Rew.subst ![#0, #3, #1, #2])

instance ivebTower_defined :
    𝚺₁-Function₃ (ivebTower : V → V → V → V) via ivebTowerDef := .mk
  fun v ↦ by simp [vebTowerConstruction.result_defined_iff, ivebTowerDef]; rfl

instance ivebTower_definable : 𝚺₁-Function₃ (ivebTower : V → V → V → V) :=
  ivebTower_defined.to_definable

instance ivebTower_definable' (Γ) (m : ℕ) :
    Γ-[m + 1]-Function₃ (ivebTower : V → V → V → V) :=
  ivebTower_definable.of_sigmaOne

/-- The Veblen tower stays inside the normal forms. -/
lemma isNF₁_ivebTower {a c : V} (ha : isNF₁ a) (hc : isNF₁ c) :
    ∀ n : V, isNF₁ (ivebTower a c n) := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using hc
  case succ n ih =>
      rw [ivebTower_succ]
      exact isNF₁_iveblen ha ih

/-- **At level `0` the Veblen tower is the ω-tower**, since `φ_0 = ω ^ ·`. -/
lemma ivebTower_zero_left (c : V) : ∀ n : V, ivebTower 0 c n = itower c n := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
      rw [ivebTower_succ, itower_succ, ih, iveblen_zero]

/-! ## Two small facts about `vebFixIndic` -/

/-- A fixed point of `φ_a` is in particular a fixed point of `ω ^ ·`. -/
lemma fixIndic_of_vebFixIndic {a e : V} (h : vebFixIndic a e = 1) : fixIndic e = 1 := by
  obtain ⟨p, q, rfl, hp⟩ := vebFix_destruct h
  rw [fixIndic_vcVadd]
  refine ⟨rfl, rfl, ?_⟩
  rintro rfl
  exact icmp₁_right_zero_ne_zero a hp

/-- `e + 1` is a normal code, for `e` zero or a fixed point of `φ_a`. -/
lemma isNF₁_vebSuccBase {a e : V} (he : isNF₁ e) (hbase : e = 0 ∨ vebFixIndic a e = 1) :
    isNF₁ (iadd₁ e (vcVadd 0 0 1 0)) :=
  isNF₁_succBase he (hbase.imp id fixIndic_of_vebFixIndic)

/-! ## The Veblen step of the cover -/

/-- `φ_a(u)` is always a single Veblen term with coefficient `1` and empty tail. -/
lemma iveblen_lead_shape (a u : V) : ∃ P Q : V, iveblen a u = vcVadd P Q 1 0 := by
  by_cases h : vebFixIndic a u = 1
  · obtain ⟨p, q, hu, -⟩ := vebFix_destruct h
    exact ⟨p, q, by rw [iveblen_of_fix h, hu]⟩
  · exact ⟨a, u, iveblen_of_not_fix h⟩

/--
**The Veblen step.**  If the head index `p` of `x` satisfies `p ≼₁ a` and the second index `q`
satisfies `q ≺₁ u`, then `x ≺₁ φ_a(u)`.  This is the three-way Veblen comparison rule read at
the leading terms, and it is the only ordinal content of the recursive case of the cover.
At `a = 0` (so `p = 0`) it is `cover_aux`'s `lt_of_lead_lt … icmp₁_zero_zero … leadV_one` step.
-/
lemma lt_iveblen_of_lead {a p q m t u : V} (ha : isNF₁ a) (hx : isNF₁ (vcVadd p q m t))
    (hu : isNF₁ u) (hpa : icmp₁ a p ≠ 0) (hqu : icmp₁ q u = 0) :
    icmp₁ (vcVadd p q m t) (iveblen a u) = 0 := by
  obtain ⟨hm, hp, hq, -, hL, -, -⟩ := nf_parts hx
  by_cases hf : vebFixIndic a u = 1
  · obtain ⟨P, Q, hueq, hP⟩ := vebFix_destruct hf
    subst hueq
    have hPNF : isNF₁ P := (nf_parts hu).2.1
    have hpP : icmp₁ p P = 0 := by
      rcases icmp₁_cases hp ha with hc | hc | hc
      · exact icmp₁_trans hp ha hPNF hc hP
      · rw [icmp₁_eq_imp_eq hp ha hc]
        exact hP
      · exact absurd (icmp₁_rev_two hp ha hc) hpa
    rw [iveblen_of_fix hf]
    apply lt_of_lead_lt hm _root_.one_ne_zero
    rw [icmp₁_lead_lead, hpP, leadV_zero]
    exact hqu
  · have hL' : isNF₁ (vcVadd a u 1 0) := by
      have h := isNF₁_iveblen ha hu
      rwa [iveblen_of_not_fix hf] at h
    rw [iveblen_of_not_fix hf]
    apply lt_of_lead_lt hm _root_.one_ne_zero
    rw [icmp₁_lead_lead]
    rcases icmp₁_cases hp ha with hc | hc | hc
    · rw [hc, leadV_zero]
      exact lt_lead_of_lt_snd hq hL' hqu
    · rw [hc, leadV_one]
      exact hqu
    · exact absurd (icmp₁_rev_two hp ha hc) hpa

/-- The leading term of a normal code is below it or equal to it.  (`InternalEpsCover`'s
`hlead_le`, factored out: it does not mention the level.) -/
lemma lead_le_self {p q m t : V} (hL : isNF₁ (vcVadd p q 1 0)) (hm : m ≠ 0) :
    icmp₁ (vcVadd p q 1 0) (vcVadd p q m t) = 0 ∨ (vcVadd p q 1 0 : V) = vcVadd p q m t := by
  rcases eq_or_ne m 1 with rfl | hm1
  · rcases eq_or_ne t 0 with rfl | ht0
    · exact Or.inr rfl
    · left
      rw [icmp₁_lead_form _root_.one_ne_zero _root_.one_ne_zero, icmp₁_self hL,
        thenV_one_left, cmpV_self, thenV_one_left]
      exact icmp₁_zero_pos ht0
  · left
    rw [icmp₁_lead_form _root_.one_ne_zero hm, icmp₁_self hL, thenV_one_left]
    refine thenV_eq_zero.mpr (Or.inl (cmpV_eq_zero.mpr ?_))
    exact lt_of_le_of_ne (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hm)) (Ne.symm hm1)

/-! ## (COV_{a₀}): the successor-level cover -/

/--
**The internal Veblen-tower cover at level `a₀`.**  Every normal code `x` lies below some
finite `φ_{a₀}`-tower `φ_{a₀}^n(e + 1)` over a base `e` which is `0` or a fixed point of
`φ_{a₀}`, and satisfies `e ≼₁ x`.
-/
lemma veb_cover_aux (a₀ : V) (ha₀ : isNF₁ a₀) : ∀ x : V, isNF₁ x →
    ∃ e n : V, isNF₁ e ∧ (e = 0 ∨ vebFixIndic a₀ e = 1) ∧
      (icmp₁ e x = 0 ∨ e = x) ∧
      icmp₁ x (ivebTower a₀ (iadd₁ e (vcVadd 0 0 1 0)) n) = 0 := by
  intro x
  induction x using ISigma1.sigma1_order_induction
  · definability
  case ind x ih =>
    intro hx
    rcases eq_or_ne x 0 with rfl | hx0
    · refine ⟨0, 0, isNF₁_zero, Or.inl rfl, Or.inr rfl, ?_⟩
      rw [iadd₁_zero_left, ivebTower_zero]
      exact icmp₁_zero_vcVadd 0 0 1 0
    · obtain ⟨p, q, m, t, rfl⟩ : ∃ p q m t, x = vcVadd p q m t :=
        ⟨_, _, _, _, (vcVadd_destruct hx0).symm⟩
      obtain ⟨hm, hp, hq, ht, hL, hfix, htail⟩ := nf_parts hx
      by_cases hA : icmp₁ a₀ p = 0
      · -- the head is a fixed point of `φ_{a₀}`: it is the witness, one tower level suffices
        have hp0 : p ≠ 0 := by
          rintro rfl
          exact icmp₁_right_zero_ne_zero a₀ hA
        have hnfs : vebFixIndic a₀ (vcVadd p q 1 (vcVadd 0 0 1 0) : V) ≠ 1 := by
          rw [Ne, vebFixIndic_vcVadd]
          rintro ⟨-, h, -⟩
          exact vcVadd_ne_zero 0 0 1 0 h
        refine ⟨vcVadd p q 1 0, 1, hL,
          Or.inr ((vebFixIndic_vcVadd a₀ p q 1 0).2 ⟨rfl, rfl, hA⟩), lead_le_self hL hm, ?_⟩
        rw [iadd₁_term_one hp0, ivebTower_one, iveblen_of_not_fix hnfs]
        apply lt_of_lead_lt hm _root_.one_ne_zero
        rw [icmp₁_lead_lead, icmp₁_rev_zero ha₀ hp hA, leadV_two,
          icmp₁_lead_form _root_.one_ne_zero _root_.one_ne_zero, icmp₁_self hL,
          thenV_one_left, cmpV_self, thenV_one_left]
        exact icmp₁_zero_vcVadd 0 0 1 0
      · -- `p ≼₁ a₀`: recurse on the second index and spend one more tower level
        obtain ⟨e, n, he, hbase, hle, hcov⟩ := ih q (snd_lt_code p q m t) hq
        have hqx : icmp₁ q (vcVadd p q m t) = 0 := lt_of_lt_lead hq hm hfix
        refine ⟨e, n + 1, he, hbase, ?_, ?_⟩
        · left
          rcases hle with h | h
          · exact icmp₁_trans he hq hx h hqx
          · rw [h]
            exact hqx
        · rw [ivebTower_succ]
          exact lt_iveblen_of_lead ha₀ hx
            (isNF₁_ivebTower ha₀ (isNF₁_vebSuccBase he hbase) n) hA hcov

/-- **(COV_{a₀})**, the general form. -/
theorem veb_tower_cover {a₀ : V} (ha₀ : isNF₁ a₀) {x : V} (hx : isNF₁ x) :
    ∃ e n : V, isNF₁ e ∧ (e = 0 ∨ vebFixIndic a₀ e = 1) ∧
      (icmp₁ e x = 0 ∨ e = x) ∧
      icmp₁ x (ivebTower a₀ (iadd₁ e (vcVadd 0 0 1 0)) n) = 0 :=
  veb_cover_aux a₀ ha₀ x hx

/-- **(COV) at level `1`**: `veb_cover_aux` at `a₀ = 0` re-derives
`InternalEpsCover.tower_cover`, since `φ_0 = ω ^ ·` on both the tower and the fixed-point
test. -/
theorem tower_cover_level_one {x : V} (hx : isNF₁ x) :
    ∃ e n : V, isNF₁ e ∧ (e = 0 ∨ fixIndic e = 1) ∧
      (icmp₁ e x = 0 ∨ e = x) ∧
      icmp₁ x (itower (iadd₁ e (vcVadd 0 0 1 0)) n) = 0 := by
  obtain ⟨e, n, he, hbase, hle, hcov⟩ := veb_cover_aux 0 isNF₁_zero x hx
  refine ⟨e, n, he, ?_, hle, ?_⟩
  · rcases hbase with h | h
    · exact Or.inl h
    · right
      rwa [vebFixIndic_zero] at h
  · rwa [ivebTower_zero_left] at hcov

/-! ## The level bridge: from `φ_{a₀}`-fixed points to the range of `φ_a` -/

/-- The coded successor of a normal code is normal: `isNF₁_iadd₁_block` at the block
`φ_0(0)·1 = 1`. -/
lemma isNF₁_succ {b : V} (hb : isNF₁ b) : isNF₁ (iadd₁ b (vcVadd 0 0 1 0)) :=
  isNF₁_iadd₁_block isNF₁_one _root_.one_ne_zero b hb

/--
**No normal code lies strictly between `z` and `z ⊕ 1`.**  Bounded course-of-values induction,
in the idiom of `InternalVNoteOrder.icmp₁_trans_aux`: both codes are bounded by a single `w`,
which keeps the induction predicate `Δ₁` (the unbounded `∀ y` form would be `Π₁`).  Three
cases, by comparing the leading term of `z` with the code of `1`: below `1` is impossible;
equal to `1` makes `z ⊕ 1` a coefficient bump and `tail_of_between_succ` forces a nonzero tail
below `1`; above `1` makes `z ⊕ 1` a tail step (`iadd₁_samePrefix_block`) and
`tails_of_between` hands the whole problem back to the strictly smaller tails.
-/
private lemma no_between_succ_aux : ∀ w : V, ∀ z ≤ w, ∀ y ≤ w, z + y ≤ w →
    isNF₁ z → isNF₁ y → icmp₁ z y = 0 →
    icmp₁ y (iadd₁ z (vcVadd 0 0 1 0)) = 0 → False := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro z hzw y hyw hsum hz hy hzy hupp
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact icmp₁_right_zero_ne_zero z hzy
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [iadd₁_zero_left] at hupp
      exact hy0 (eq_zero_of_lt_one hy hupp)
    · obtain ⟨p, q, n, r, rfl⟩ : ∃ p q n r, z = vcVadd p q n r :=
        ⟨_, _, _, _, (vcVadd_destruct hz0).symm⟩
      obtain ⟨hn, hp, hq, hr, hL, -, hrL⟩ := nf_parts hz
      rcases icmp₁_cases hL (isNF₁_one (V := V)) with hc | hc | hc
      · exact vcVadd_ne_zero p q 1 0 (eq_zero_of_lt_one hL hc)
      · have hLeq : (vcVadd p q 1 0 : V) = vcVadd 0 0 1 0 :=
          icmp₁_eq_imp_eq hL (isNF₁_one (V := V)) hc
        rw [hLeq] at hrL
        have hr0 : r = 0 := eq_zero_of_lt_one hr hrL
        have hzs : iadd₁ (vcVadd p q n r) (vcVadd 0 0 1 0 : V) = vcVadd p q (n + 1) 0 := by
          rw [iadd₁_vcVadd, if_neg (vcVadd_ne_zero 0 0 1 0), vcLead_vcVadd,
            if_neg (by rw [hc]; exact _root_.one_ne_zero), if_pos hc]
          simp
        rw [hzs] at hupp
        obtain ⟨s, hys, hrs⟩ := tail_of_between_succ hy hy0 hL hn hzy hupp
        subst hys
        obtain ⟨-, -, -, hs, -, -, hsL⟩ := nf_parts hy
        rw [hLeq] at hsL
        have hs0 : s = 0 := eq_zero_of_lt_one hs hsL
        rw [hr0, hs0, icmp₁_zero_zero] at hrs
        exact _root_.one_ne_zero hrs
      · have hzs : iadd₁ (vcVadd p q n r) (vcVadd 0 0 1 0 : V)
            = vcVadd p q n (iadd₁ r (vcVadd 0 0 1 0)) := iadd₁_samePrefix_block hc
        rw [hzs] at hupp
        obtain ⟨s, hys, hrs, hsr⟩ := tails_of_between hy hy0 hL hn hzy hupp
        subst hys
        obtain ⟨-, -, -, hs, -, -, -⟩ := nf_parts hy
        have hlt : r + s < w :=
          lt_of_lt_of_le
            (add_lt_add_of_lt_of_le (tail_lt_code p q n r) (tail_lt_code p q n s).le) hsum
        exact ih (r + s) hlt r le_self_add s le_add_self le_rfl hr hs hrs hsr

/-- **No normal code lies strictly between `z` and `z ⊕ 1`.** -/
theorem no_between_succ {z y : V} (hz : isNF₁ z) (hy : isNF₁ y)
    (hzy : icmp₁ z y = 0) (hupp : icmp₁ y (iadd₁ z (vcVadd 0 0 1 0)) = 0) : False :=
  no_between_succ_aux (z + y) z le_self_add y le_add_self le_rfl hz hy hzy hupp

/-- **`hsucc` at `a := a₀ ⊕ 1`, for an arbitrary normal `a₀`.** -/
theorem succ_general {a₀ : V} (ha₀ : isNF₁ a₀) :
    ∀ P : V, isNF₁ P → icmp₁ a₀ P = 0 → icmp₁ P (iadd₁ a₀ (vcVadd 0 0 1 0)) ≠ 0 :=
  fun _P hP h hcon ↦ no_between_succ ha₀ hP h hcon

/-- `(a₀, a) = (0, 1)`: nothing but `0` is `≺₁ 1`. -/
theorem succ_zero_one :
    ∀ P : V, isNF₁ P → icmp₁ (0 : V) P = 0 → icmp₁ P (vcVadd 0 0 1 0 : V) ≠ 0 :=
  fun P hP h hlt ↦ (icmp₁_zero_eq_zero_iff P).1 h (eq_zero_of_lt_one hP hlt)

/-- `(a₀, a) = (φ_p(q), φ_p(q) ⊕ 1)` for `p ≠ 0`: below the coded successor of a single term
a normal code is below the term or equal to it. -/
theorem succ_term {p q : V} (hp : p ≠ 0) (hL : isNF₁ (vcVadd p q 1 0)) :
    ∀ P : V, isNF₁ P → icmp₁ (vcVadd p q 1 0 : V) P = 0 →
      icmp₁ P (iadd₁ (vcVadd p q 1 0 : V) (vcVadd 0 0 1 0)) ≠ 0 := by
  intro P hP hlt hcon
  rw [iadd₁_term_one hp] at hcon
  rcases lt_or_eq_of_lt_term_succ hP hL hcon with h | h
  · have := icmp₁_rev_zero hL hP hlt
    rw [h] at this
    exact _root_.two_ne_zero this.symm
  · rw [h, icmp₁_self hL] at hlt
    exact _root_.one_ne_zero hlt

/--
**(COV_{a₀}) in the form the level-`a` progressiveness argument consumes.**  The base is
delivered as an element of the *range of `φ_a`* (`vebBaseIndic`), which is what
`InternalVeblenSurj.veb_surj'` needs.  `hsucc` says "`a` is the successor of `a₀`".
-/
theorem veb_tower_cover_level {a₀ a : V} (ha₀ : isNF₁ a₀)
    (hsucc : ∀ P : V, isNF₁ P → icmp₁ a₀ P = 0 → icmp₁ P a ≠ 0)
    {x : V} (hx : isNF₁ x) :
    ∃ e n : V, isNF₁ e ∧ (e = 0 ∨ vebBaseIndic a e = 1) ∧
      (icmp₁ e x = 0 ∨ e = x) ∧
      icmp₁ x (ivebTower a₀ (iadd₁ e (vcVadd 0 0 1 0)) n) = 0 := by
  obtain ⟨e, n, he, hbase, hle, hcov⟩ := veb_cover_aux a₀ ha₀ x hx
  refine ⟨e, n, he, ?_, hle, hcov⟩
  rcases hbase with h | h
  · exact Or.inl h
  · right
    obtain ⟨P, Q, hPQ, hP⟩ := vebFix_destruct h
    subst hPQ
    rw [vebBaseIndic_vcVadd]
    exact ⟨rfl, rfl, hsucc P (nf_parts he).2.1 hP⟩

/--
**The crux of the Γ₀ upper bound, assembled.**  Every normal `x ≺₁ φ_a(g)` is below a finite
`φ_{a₀}`-tower over `e ⊕ 1`, where `e ≼₁ x` is either `0` or `φ_a(h)` for a normal `h ≺₁ g`.

This is the level-`a` form of what `InternalEpsCover.tower_cover` +
`InternalEpsMonoCode.eps_mono_of_surj` give at `a = 1`, and it is exactly the datum the
progressiveness step for `ψ_a(g) :≡ ∀²X TIupto(≺₁, φ_a(g), X)` consumes: the base is handled
by the induction hypothesis `ψ_a(h)`, the `⊕ 1` by `VeblenSuccStep`, and the `n` tower levels
by `n` applications of the `φ_{a₀}`-jump.
-/
theorem veb_cover_mono {a₀ a g x : V} (ha₀ : isNF₁ a₀) (ha : isNF₁ a)
    (hsucc : ∀ P : V, isNF₁ P → icmp₁ a₀ P = 0 → icmp₁ P a ≠ 0)
    (hg : isNF₁ g) (hx : isNF₁ x) (hlt : icmp₁ x (iveblen a g) = 0) :
    ∃ e n : V, isNF₁ e ∧ (icmp₁ e x = 0 ∨ e = x) ∧
      icmp₁ x (ivebTower a₀ (iadd₁ e (vcVadd 0 0 1 0)) n) = 0 ∧
      (e = 0 ∨ ∃ h : V, isNF₁ h ∧ e = iveblen a h ∧ icmp₁ h g = 0) := by
  obtain ⟨e, n, he, hbase, hle, hcov⟩ := veb_tower_cover_level ha₀ hsucc hx
  refine ⟨e, n, he, hle, hcov, ?_⟩
  rcases hbase with h | h
  · exact Or.inl h
  · right
    have hex : icmp₁ e (iveblen a g) = 0 := by
      rcases hle with h' | h'
      · exact icmp₁_trans he hx (isNF₁_iveblen ha hg) h' hlt
      · rw [h']
        exact hlt
    exact veb_mono_of_surj ha he h hg rfl hex

/-! ## The fully concrete successor level -/

/-- **(COV) at the successor level `a₀ ⊕ 1`**, with no hypothesis beyond `isNF₁ a₀`: the base
is delivered in the range of `φ_{a₀ ⊕ 1}` and the tower iterates `φ_{a₀}`. -/
theorem veb_tower_cover_succ {a₀ : V} (ha₀ : isNF₁ a₀) {x : V} (hx : isNF₁ x) :
    ∃ e n : V, isNF₁ e ∧
      (e = 0 ∨ vebBaseIndic (iadd₁ a₀ (vcVadd 0 0 1 0)) e = 1) ∧
      (icmp₁ e x = 0 ∨ e = x) ∧
      icmp₁ x (ivebTower a₀ (iadd₁ e (vcVadd 0 0 1 0)) n) = 0 :=
  veb_tower_cover_level ha₀ (succ_general ha₀) hx

/-- **The crux at the successor level `a₀ ⊕ 1`**, with no hypothesis beyond `isNF₁ a₀`. -/
theorem veb_cover_mono_succ {a₀ g x : V} (ha₀ : isNF₁ a₀) (hg : isNF₁ g) (hx : isNF₁ x)
    (hlt : icmp₁ x (iveblen (iadd₁ a₀ (vcVadd 0 0 1 0)) g) = 0) :
    ∃ e n : V, isNF₁ e ∧ (icmp₁ e x = 0 ∨ e = x) ∧
      icmp₁ x (ivebTower a₀ (iadd₁ e (vcVadd 0 0 1 0)) n) = 0 ∧
      (e = 0 ∨ ∃ h : V, isNF₁ h ∧
        e = iveblen (iadd₁ a₀ (vcVadd 0 0 1 0)) h ∧ icmp₁ h g = 0) :=
  veb_cover_mono ha₀ (isNF₁_succ ha₀) (succ_general ha₀) hg hx hlt

/-- **`veb_cover_mono` at `(a₀, a) = (0, 1)` is the ε-case**: it reproduces
`InternalEpsCover.tower_cover` together with `InternalEpsMonoCode.eps_mono_of_surj`. -/
theorem veb_cover_mono_level_one {g x : V} (hg : isNF₁ g) (hx : isNF₁ x)
    (hlt : icmp₁ x (iepsilon g) = 0) :
    ∃ e n : V, isNF₁ e ∧ (icmp₁ e x = 0 ∨ e = x) ∧
      icmp₁ x (itower (iadd₁ e (vcVadd 0 0 1 0)) n) = 0 ∧
      (e = 0 ∨ ∃ h : V, isNF₁ h ∧ e = iepsilon h ∧ icmp₁ h g = 0) := by
  have hlt' : icmp₁ x (iveblen (vcVadd 0 0 1 0 : V) g) = 0 := by
    rw [iveblen_one]
    exact hlt
  obtain ⟨e, n, he, hle, hcov, hbase⟩ :=
    veb_cover_mono isNF₁_zero isNF₁_one succ_zero_one hg hx hlt'
  refine ⟨e, n, he, hle, ?_, ?_⟩
  · rwa [ivebTower_zero_left] at hcov
  · rcases hbase with h | ⟨h, hh, hval, hhg⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, hh, by rw [hval, iveblen_one], hhg⟩

end OrdinalAnalysis.Gentzen.InternalVebCover
