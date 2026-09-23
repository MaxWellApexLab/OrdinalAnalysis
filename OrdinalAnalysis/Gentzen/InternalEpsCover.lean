/-
  The internal ω-tower cover of the Veblen codes.

  This is the one genuinely new piece of arithmetic that the ACA upper bound needs.  The
  external cover is trivial (mathlib's `lt_epsilon_zero`), but the ACA argument runs the cover
  *inside* `IΣ₁`, at a variable code, because the progressiveness of

      `ψ₀(g) :≡ ∀²X TIupto(≺₁, ε_g, X)`

  has to decide, for an arbitrary `x ≺₁ ε_g`, which ε-number `x` sits above.

  **(COV)** For every normal code `x` there are `e` and `n` with

      `e = 0` or `e` an ε-number,  `e ≼₁ x`,  and  `x ≺₁ ω_n(e + 1)`,

  where `ω_n(·)` is the internal tower of `VeblenTower.itower`.  The proof is Σ₁
  course-of-values induction on the code, in the three cases of the design:

  * `x = 0` — take `e = 0`, `n = 0` (`ω_0(1) = 1`);
  * `x = φ_a(b)·m + t` with `a ≠ 0` — the head `φ_a(b)` is a fixed point of `ω ^ ·`, so it is
    an ε-number `≼ x`, and `φ_a(b)·m + t ≺ ω^(φ_a(b) + 1)`: one tower level;
  * `x = ω^b·m + t` — recurse on `b` (which is a *smaller code*), and spend one more tower
    level: `ω^b·m + t ≺ ω^(ω_n(e+1)) = ω_{n+1}(e+1)`.

  Specialised at `x ≺₁ ε₀` the witness must be `e = 0` (an ε-number `≼ x` would be `≺ ε₀`,
  which no ε-number is), giving the promised base-`0` form: **every normal code below `ε₀` is
  below some `ω_n(1)`**.
-/
import OrdinalAnalysis.Gentzen.VeblenSuccStep

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OrdinalAnalysis.Gentzen.InternalEpsCover

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.InternalVNote
open OrdinalAnalysis.Gentzen.InternalVNoteOrder
open OrdinalAnalysis.Gentzen.InternalVNoteJump
open OrdinalAnalysis.Gentzen.CodedNotation (liftCode paLX_of_peano_semantic)
open OrdinalAnalysis.Gentzen.CodedVeblen
open OrdinalAnalysis.Gentzen.CodedVeblenJump
open OrdinalAnalysis.Gentzen.VNoteBridge
open OrdinalAnalysis.Gentzen.OmegaTower (lMap_numeral)
open OrdinalAnalysis.Gentzen.Epsilon1UpperBound (gamma0Term modelCode_eps0)
open OrdinalAnalysis.Gentzen.VeblenTower
open OrdinalAnalysis.Gentzen.VeblenSuccStep
open OrdinalAnalysis.Gamma0Note (epsilonNote)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Two standard codes -/

/-- The code of `1 = φ_0(0)`. -/
lemma isNF₁_one : isNF₁ (vcVadd 0 0 1 0 : V) :=
  isNF₁_of_parts isNF₁_zero isNF₁_zero (icmp₁_zero_vcVadd 0 0 1 0)
    _root_.one_ne_zero isNF₁_zero (icmp₁_zero_vcVadd 0 0 1 0)

/-- The code of `ε₀ = φ_1(0)`. -/
lemma isNF₁_eps0code : isNF₁ (vcVadd (vcVadd 0 0 1 0) 0 1 0 : V) :=
  isNF₁_of_parts isNF₁_one isNF₁_zero (icmp₁_zero_vcVadd _ _ _ _)
    _root_.one_ne_zero isNF₁_zero (icmp₁_zero_vcVadd _ _ _ _)

/-- No ε-number is below `ε₀`. -/
lemma fix_not_lt_eps0 {e : V} (he : isNF₁ e) (hfix : fixIndic e = 1) :
    icmp₁ e (vcVadd (vcVadd 0 0 1 0) 0 1 0) ≠ 0 := by
  obtain ⟨p, q, rfl, hp⟩ := fix_destruct hfix
  obtain ⟨-, hpNF, -, -, -, -, -⟩ := nf_parts he
  rw [icmp₁_lead_lead]
  rcases icmp₁_cases hpNF (isNF₁_one (V := V)) with h | h | h
  · exact absurd (eq_zero_of_lt_one hpNF h) hp
  · rw [h, leadV_one]
    exact icmp₁_right_zero_ne_zero q
  · rw [h, leadV_two, icmp₁_vcVadd_zero]
    exact _root_.two_ne_zero

/-! ## The base of the cover tower is never a fixed point -/

/-- `e + 1` is never fixed-point-shaped, for `e` zero or an ε-number. -/
lemma fixIndic_succBase_ne_one {e : V} (hbase : e = 0 ∨ fixIndic e = 1) :
    fixIndic (iadd₁ e (vcVadd 0 0 1 0)) ≠ 1 := by
  rcases hbase with rfl | hfix
  · rw [iadd₁_zero_left, Ne, fixIndic_vcVadd]
    rintro ⟨-, -, h⟩
    exact h rfl
  · obtain ⟨p, q, rfl, hp⟩ := fix_destruct hfix
    rw [iadd₁_term_one hp, Ne, fixIndic_vcVadd]
    rintro ⟨-, h, -⟩
    exact vcVadd_ne_zero 0 0 1 0 h

/-- `e + 1` is a normal code, for `e` zero or an ε-number. -/
lemma isNF₁_succBase {e : V} (he : isNF₁ e) (hbase : e = 0 ∨ fixIndic e = 1) :
    isNF₁ (iadd₁ e (vcVadd 0 0 1 0)) := by
  rcases hbase with rfl | hfix
  · rw [iadd₁_zero_left]
    exact isNF₁_one
  · obtain ⟨p, q, rfl, hp⟩ := fix_destruct hfix
    obtain ⟨-, hpNF, hqNF, -, hL, hfix', -⟩ := nf_parts he
    rw [iadd₁_term_one hp]
    exact isNF₁_of_parts hpNF hqNF hfix' _root_.one_ne_zero isNF₁_one
      (icmp₁_rev_two hL isNF₁_one (term_gt_one hp))

@[simp] lemma itower_one (c : V) : itower c 1 = iomegaPow c := by
  have h := itower_succ c 0
  rwa [zero_add, itower_zero] at h

/-- A tower over a non-fixed-point base never becomes a fixed point. -/
lemma fixIndic_itower_ne_one {c : V} (hc : fixIndic c ≠ 1) :
    ∀ n : V, fixIndic (itower c n) ≠ 1 := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using hc
  case succ n ih =>
      rw [itower_succ, iomegaPow_of_not_fix ih, Ne, fixIndic_vcVadd]
      rintro ⟨-, -, h⟩
      exact h rfl

/-! ## (COV): the cover -/

/--
**The internal ω-tower cover.**  Every normal code `x` lies below some finite tower
`ω_n(e + 1)` over a base `e` which is `0` or an ε-number and satisfies `e ≼₁ x`.
-/
lemma cover_aux : ∀ x : V, isNF₁ x →
    ∃ e n : V, isNF₁ e ∧ (e = 0 ∨ fixIndic e = 1) ∧
      (icmp₁ e x = 0 ∨ e = x) ∧
      icmp₁ x (itower (iadd₁ e (vcVadd 0 0 1 0)) n) = 0 := by
  intro x
  induction x using ISigma1.sigma1_order_induction
  · definability
  case ind x ih =>
    intro hx
    rcases eq_or_ne x 0 with rfl | hx0
    · refine ⟨0, 0, isNF₁_zero, Or.inl rfl, Or.inr rfl, ?_⟩
      rw [iadd₁_zero_left, itower_zero]
      exact icmp₁_zero_vcVadd 0 0 1 0
    · obtain ⟨a, b, m, t, rfl⟩ : ∃ a b m t, x = vcVadd a b m t :=
        ⟨_, _, _, _, (vcVadd_destruct hx0).symm⟩
      obtain ⟨hm, ha, hb, ht, hL, hfix, htail⟩ := nf_parts hx
      rcases eq_or_ne a 0 with rfl | ha0
      · -- the head is `ω ^ b`: recurse on the exponent
        obtain ⟨e, n, he, hbase, hle, hcov⟩ := ih b (snd_lt_code 0 b m t) hb
        have hnfs : fixIndic (iadd₁ e (vcVadd 0 0 1 0)) ≠ 1 :=
          fixIndic_succBase_ne_one hbase
        have hbx : icmp₁ b (vcVadd 0 b m t) = 0 := lt_of_lt_lead hb hm hfix
        refine ⟨e, n + 1, he, hbase, ?_, ?_⟩
        · left
          rcases hle with h | h
          · exact icmp₁_trans he hb hx h hbx
          · rw [h]; exact hbx
        · rw [itower_succ, iomegaPow_of_not_fix (fixIndic_itower_ne_one hnfs n)]
          apply lt_of_lead_lt hm _root_.one_ne_zero
          rw [icmp₁_lead_lead, icmp₁_zero_zero, leadV_one]
          exact hcov
      · -- the head is a fixed point: it is the witness, one tower level suffices
        have hnfs : fixIndic (vcVadd a b 1 (vcVadd 0 0 1 0) : V) ≠ 1 := by
          rw [Ne, fixIndic_vcVadd]
          rintro ⟨-, h, -⟩
          exact vcVadd_ne_zero 0 0 1 0 h
        have hlead_le : icmp₁ (vcVadd a b 1 0) (vcVadd a b m t) = 0 ∨
            (vcVadd a b 1 0 : V) = vcVadd a b m t := by
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
        refine ⟨vcVadd a b 1 0, 1, hL,
          Or.inr ((fixIndic_vcVadd a b 1 0).2 ⟨rfl, rfl, ha0⟩), hlead_le, ?_⟩
        rw [iadd₁_term_one ha0, itower_one, iomegaPow_of_not_fix hnfs]
        apply lt_of_lead_lt hm _root_.one_ne_zero
        rw [icmp₁_lead_lead, icmp₁_pos_zero ha0, leadV_two,
          icmp₁_lead_form _root_.one_ne_zero _root_.one_ne_zero, icmp₁_self hL,
          thenV_one_left, cmpV_self, thenV_one_left]
        exact icmp₁_zero_vcVadd 0 0 1 0

/-- **(COV)**, the general form. -/
theorem tower_cover {x : V} (hx : isNF₁ x) :
    ∃ e n : V, isNF₁ e ∧ (e = 0 ∨ fixIndic e = 1) ∧
      (icmp₁ e x = 0 ∨ e = x) ∧
      icmp₁ x (itower (iadd₁ e (vcVadd 0 0 1 0)) n) = 0 :=
  cover_aux x hx

/-- **(COV) at the base `0`**: every normal code below `ε₀` is below some `ω_n(1)`. -/
theorem tower_cover_zero {x : V} (hx : isNF₁ x)
    (hlt : icmp₁ x (vcVadd (vcVadd 0 0 1 0) 0 1 0) = 0) :
    ∃ n : V, icmp₁ x (itower (vcVadd 0 0 1 0) n) = 0 := by
  obtain ⟨e, n, he, hbase, hle, hcov⟩ := cover_aux x hx
  have he0 : e = 0 := by
    rcases hbase with h | hf
    · exact h
    · exfalso
      have hex : icmp₁ e (vcVadd (vcVadd 0 0 1 0) 0 1 0) = 0 := by
        rcases hle with h' | h'
        · exact icmp₁_trans he hx isNF₁_eps0code h' hlt
        · rw [h']; exact hlt
      exact fix_not_lt_eps0 he hf hex
  subst he0
  rw [iadd₁_zero_left] at hcov
  exact ⟨n, hcov⟩

/-! ## The object-language statements -/

/-- `x ≼₁ y` packaged as a single `𝚺₁` graph, so that the cover statement needs no
object-language equality atom. -/
def leqDef₁ : 𝚺₁.Semisentence 2 := .mkSigma
  “x y. !isNFb₁Def 1 x ∧ !isNFb₁Def 1 y ∧ (!icmp₁Def 0 x y ∨ x = y)”

@[simp] theorem eval_leqDef₁ (x y : V) :
    leqDef₁.val.Evalb ![x, y] ↔
      isNF₁ x ∧ isNF₁ y ∧ (icmp₁ x y = 0 ∨ x = y) := by
  simp [leqDef₁, isNF₁, isNFb₁_defined.iff, icmp₁_defined.iff, eq_comm]

/-- `≼₁`, in `LX`. -/
def leqCode₁ : Semiformula LX ℕ 2 := liftCode leqDef₁

/--
`∀x (NF(x) → x ≺₁ ε̄₀ → ∃n ∃u (Tower(u, n, 1̄) ∧ x ≺₁ u))`.
-/
noncomputable def coverZeroStatement : Sentence LX :=
  (∀¹ (∼(formulaAt nfCode₁ (#0 : Semiterm LX ℕ 1)) ⋎
      (∼(precAt precCode₁ (#0 : Semiterm LX ℕ 1)
          ((gamma0Code (epsilonNote 0) : ℕ) : Semiterm LX ℕ 1)) ⋎
        (∃¹ ∃¹
          (towerAt towerCode₁ (#0 : Semiterm LX ℕ 3) #1
              ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 3) ⋏
            precAt precCode₁ #2 #0))))).univCl

/--
`∀x (NF(x) → ∃e ∃s ∃n ∃u (Base(e) ∧ e ≼₁ x ∧ Add(s,e,1̄) ∧ Tower(u,n,s) ∧ x ≺₁ u))`.
-/
noncomputable def coverStatement : Sentence LX :=
  (∀¹ (∼(formulaAt nfCode₁ (#0 : Semiterm LX ℕ 1)) ⋎
      (∃¹ ∃¹ ∃¹ ∃¹
        (formulaAt baseCode₁ (#3 : Semiterm LX ℕ 5) ⋏
          (precAt leqCode₁ #3 #4 ⋏
            (addAt addCode₁ #2 #3 ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 5) ⋏
              (towerAt towerCode₁ #0 #1 #2 ⋏
                precAt precCode₁ #4 #0))))))).univCl

private def arithNfAt {n : ℕ} (x : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![x] ▹ Rewriting.emb nfDef₁.val

private def arithBaseAt {n : ℕ} (e : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![e] ▹ Rewriting.emb baseDef₁.val

private def arithPrecAt {n : ℕ} (x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![x, y] ▹ Rewriting.emb precDef₁.val

private def arithLeqAt {n : ℕ} (x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![x, y] ▹ Rewriting.emb leqDef₁.val

private def arithAddAt {n : ℕ} (z x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, x, y] ▹ Rewriting.emb safeIadd₁Def.val

private def arithTowerAt {n : ℕ}
    (u k c : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![u, k, c] ▹ Rewriting.emb towerDef₁.val

noncomputable def arithmeticCoverZeroStatement : ArithmeticSentence :=
  (∀¹ (∼(arithNfAt (#0 : Semiterm ℒₒᵣ ℕ 1)) ⋎
      (∼(arithPrecAt (#0 : Semiterm ℒₒᵣ ℕ 1)
          ((gamma0Code (epsilonNote 0) : ℕ) : Semiterm ℒₒᵣ ℕ 1)) ⋎
        (∃¹ ∃¹
          (arithTowerAt (#0 : Semiterm ℒₒᵣ ℕ 3) #1
              ((gamma0Code 1 : ℕ) : Semiterm ℒₒᵣ ℕ 3) ⋏
            arithPrecAt #2 #0))))).univCl

noncomputable def arithmeticCoverStatement : ArithmeticSentence :=
  (∀¹ (∼(arithNfAt (#0 : Semiterm ℒₒᵣ ℕ 1)) ⋎
      (∃¹ ∃¹ ∃¹ ∃¹
        (arithBaseAt (#3 : Semiterm ℒₒᵣ ℕ 5) ⋏
          (arithLeqAt #3 #4 ⋏
            (arithAddAt #2 #3 ((gamma0Code 1 : ℕ) : Semiterm ℒₒᵣ ℕ 5) ⋏
              (arithTowerAt #0 #1 #2 ⋏
                arithPrecAt #4 #0))))))).univCl

/-! ## The `IΣ₁` proofs -/

theorem arithmetic_coverZero : 𝗜𝚺₁ ⊢ arithmeticCoverZeroStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp [arithmeticCoverZeroStatement, arithNfAt, arithPrecAt, arithTowerAt,
    eval_nfDef₁, eval_precDef₁, eval_towerDef₁,
    Structure.numeral_eq_numeral, numeral_eq_natCast]
  intro x
  have hone : ((gamma0Code 1 : ℕ) : M) = vcVadd 0 0 1 0 := modelCode_one
  have heps : ((gamma0Code (epsilonNote 0) : ℕ) : M) =
      vcVadd (vcVadd 0 0 1 0) 0 1 0 := modelCode_eps0
  by_cases hx : isNF₁ x
  · by_cases hlt : icmp₁ x ((gamma0Code (epsilonNote 0) : ℕ) : M) = 0
    · right
      right
      rw [heps] at hlt
      obtain ⟨n, hn⟩ := tower_cover_zero hx hlt
      rw [hone]
      exact ⟨isNF₁_one, hx, n, isNF₁_itower isNF₁_one n, hn⟩
    · right
      left
      intro _ _ h
      exact hlt h
  · left
    exact hx

theorem arithmetic_cover : 𝗜𝚺₁ ⊢ arithmeticCoverStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp [arithmeticCoverStatement, arithNfAt, arithBaseAt, arithPrecAt, arithLeqAt,
    arithAddAt, arithTowerAt, eval_nfDef₁, eval_baseDef₁, eval_precDef₁, eval_leqDef₁,
    eval_towerDef₁, safeIadd₁_defined.iff,
    Structure.numeral_eq_numeral, numeral_eq_natCast]
  intro x
  have hone : ((gamma0Code 1 : ℕ) : M) = vcVadd 0 0 1 0 := modelCode_one
  by_cases hx : isNF₁ x
  · right
    obtain ⟨e, n, he, hbase, hle, hcov⟩ := tower_cover hx
    refine ⟨e, ?_⟩
    rw [hone, safeIadd₁_of_nf he]
    exact ⟨⟨he, hbase⟩, ⟨he, hx, hle⟩, isNF₁_succBase he hbase, hx, n,
      isNF₁_itower (isNF₁_succBase he hbase) n, hcov⟩
  · left
    exact hx

/-! ## Transport to `PA[X]` -/

private lemma map_coverZero_body :
    Semiformula.lMap toLX
        (∀¹ (∼(arithNfAt (#0 : Semiterm ℒₒᵣ ℕ 1)) ⋎
          (∼(arithPrecAt (#0 : Semiterm ℒₒᵣ ℕ 1)
              ((gamma0Code (epsilonNote 0) : ℕ) : Semiterm ℒₒᵣ ℕ 1)) ⋎
            (∃¹ ∃¹
              (arithTowerAt (#0 : Semiterm ℒₒᵣ ℕ 3) #1
                  ((gamma0Code 1 : ℕ) : Semiterm ℒₒᵣ ℕ 3) ⋏
                arithPrecAt #2 #0))))) =
      (∀¹ (∼(formulaAt nfCode₁ (#0 : Semiterm LX ℕ 1)) ⋎
        (∼(precAt precCode₁ (#0 : Semiterm LX ℕ 1)
            ((gamma0Code (epsilonNote 0) : ℕ) : Semiterm LX ℕ 1)) ⋎
          (∃¹ ∃¹
            (towerAt towerCode₁ (#0 : Semiterm LX ℕ 3) #1
                ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 3) ⋏
              precAt precCode₁ #2 #0))))) := by
  simp [arithNfAt, arithPrecAt, arithTowerAt, formulaAt, precAt, towerAt,
    nfCode₁, precCode₁, towerCode₁, liftCode, Semiformula.lMap_subst, lMap_numeral]

private lemma map_cover_body :
    Semiformula.lMap toLX
        (∀¹ (∼(arithNfAt (#0 : Semiterm ℒₒᵣ ℕ 1)) ⋎
          (∃¹ ∃¹ ∃¹ ∃¹
            (arithBaseAt (#3 : Semiterm ℒₒᵣ ℕ 5) ⋏
              (arithLeqAt #3 #4 ⋏
                (arithAddAt #2 #3 ((gamma0Code 1 : ℕ) : Semiterm ℒₒᵣ ℕ 5) ⋏
                  (arithTowerAt #0 #1 #2 ⋏
                    arithPrecAt #4 #0))))))) =
      (∀¹ (∼(formulaAt nfCode₁ (#0 : Semiterm LX ℕ 1)) ⋎
        (∃¹ ∃¹ ∃¹ ∃¹
          (formulaAt baseCode₁ (#3 : Semiterm LX ℕ 5) ⋏
            (precAt leqCode₁ #3 #4 ⋏
              (addAt addCode₁ #2 #3 ((gamma0Code 1 : ℕ) : Semiterm LX ℕ 5) ⋏
                (towerAt towerCode₁ #0 #1 #2 ⋏
                  precAt precCode₁ #4 #0))))))) := by
  simp [arithNfAt, arithBaseAt, arithPrecAt, arithLeqAt, arithAddAt, arithTowerAt,
    formulaAt, precAt, addAt, towerAt, nfCode₁, baseCode₁, precCode₁, leqCode₁,
    addCode₁, towerCode₁, liftCode, Semiformula.lMap_subst, lMap_numeral]

lemma models_coverZero_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ coverZeroStatement ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticCoverZeroStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [coverZeroStatement, arithmeticCoverZeroStatement,
    Semiformula.eval_univCl]
  rw [← map_coverZero_body]
  simp [Semiformula.eval_lMap]

lemma models_cover_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ coverStatement ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticCoverStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [coverStatement, arithmeticCoverStatement, Semiformula.eval_univCl]
  rw [← map_cover_body]
  simp [Semiformula.eval_lMap]

/-- **(COV) at the base `0`, in `PA[X]`.** -/
theorem concrete_cover_zero : paLX ⊢ coverZeroStatement := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_coverZero)
  intro M _ _
  exact models_coverZero_iff_arithmetic

/-- **(COV), in `PA[X]`.** -/
theorem concrete_cover : paLX ⊢ coverStatement := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_cover)
  intro M _ _
  exact models_cover_iff_arithmetic

end OrdinalAnalysis.Gentzen.InternalEpsCover
