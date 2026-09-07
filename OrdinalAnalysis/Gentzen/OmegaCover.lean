/-
  The concrete omega-cover law for the coded ordinal notations.

  The main argument is carried out uniformly in every model of IΣ₁.  It uses
  bounded order induction on the common-prefix decomposition of Cantor normal
  forms; no external ordinal arithmetic is imported into the arithmetization.
-/
import OrdinalAnalysis.Gentzen.JumpArithmetic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OrdinalAnalysis.Gentzen.OmegaCover

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote
open OrdinalAnalysis.Gentzen.CodedNotation
open OrdinalAnalysis.Gentzen.JumpArithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private lemma isNF_ocExp_of_nf {c : V} (hc : isNF c) (hc0 : c ≠ 0) :
    isNF (ocExp c) := by
  have h := (isNF_ocOadd (ocExp c) (ocCoeff c) (ocTail c)).1
    (by rw [ocOadd_destruct hc0]; exact hc)
  exact h.2.1

private lemma icmp_transitive {a b c : V}
    (hab : icmp a b = 0) (hbc : icmp b c = 0) :
    icmp a c = 0 :=
  icmp_trans (max a (max b c)) a (le_max_left _ _)
    b (le_trans (le_max_left _ _) (le_max_right _ _))
    c (le_trans (le_max_right _ _) (le_max_right _ _)) hab hbc

private lemma icmp_reverse_of_zero {a b : V} (hab : icmp a b = 0) :
    icmp b a = 2 := by
  have hswap := icmp_swap a b
  rw [hab] at hswap
  simpa [oswap] using hswap

private lemma icmp_zero_of_reverse_two {a b : V} (hba : icmp b a = 2) :
    icmp a b = 0 := by
  have hswap := icmp_swap b a
  rw [hba] at hswap
  simpa [oswap] using hswap

private lemma icmp_reverse_of_not_lt_not_eq {a b : V}
    (hab : icmp a b ≠ 0) (hne : a ≠ b) :
    icmp b a = 0 := by
  rcases icmp_cases a b with h | h | h
  · exact absurd h hab
  · exact absurd (icmp_eq_imp_eq (max a b) a (le_max_left _ _)
      b (le_max_right _ _) h) hne
  · exact icmp_zero_of_reverse_two h

private lemma icmp_right_zero_ne_zero (c : V) : icmp c 0 ≠ 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [icmp_zero_zero]
    exact _root_.one_ne_zero
  · rw [icmp_pos_zero hc]
    exact _root_.two_ne_zero

private lemma exp_lt_of_lt_omegaPow {a g : V}
    (hg : isNF g) (hg0 : g ≠ 0)
    (hga : icmp g (ocOadd a 1 0) = 0) :
    icmp (ocExp g) a = 0 := by
  obtain ⟨e, n, r, rfl⟩ : ∃ e n r, g = ocOadd e n r :=
    ⟨_, _, _, (ocOadd_destruct hg0).symm⟩
  obtain ⟨hn, he, hr, hside⟩ := (isNF_ocOadd e n r).1 hg
  rw [icmp_ocOadd] at hga
  rcases thenV_eq_zero.mp hga with hecmp | ⟨heq, hrest⟩
  · simpa using hecmp
  · rcases thenV_eq_zero.mp hrest with hnlt | ⟨hneq, hrlt⟩
    · have : n = 0 := lt_one_iff_eq_zero.mp (cmpV_eq_zero.mp hnlt)
      exact absurd this hn
    · exact absurd hrlt (icmp_right_zero_ne_zero r)

private lemma lt_iadd_headBlock {b g : V}
    (hb : isNF b) (hg : isNF g) (hg0 : g ≠ 0) :
    icmp g (iadd b
      (ocOadd (ocExp g) (ocCoeff g + 1) 0)) = 0 := by
  obtain ⟨f, m, s, rfl⟩ : ∃ f m s, g = ocOadd f m s :=
    ⟨_, _, _, (ocOadd_destruct hg0).symm⟩
  obtain ⟨hm, hf, hs, hgside⟩ := (isNF_ocOadd f m s).1 hg
  simp only [ocExp_ocOadd, ocCoeff_ocOadd]
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [iadd_zero_left, icmp_ocOadd, icmp_self f f le_rfl,
      show cmpV m (m + 1) = 0 from cmpV_eq_zero.mpr (by simp)]
    simp [thenV]
  · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, b = ocOadd e n r :=
      ⟨_, _, _, (ocOadd_destruct hb0).symm⟩
    obtain ⟨hn, he, hr, hbside⟩ := (isNF_ocOadd e n r).1 hb
    rw [iadd_ocOadd,
      if_neg (ocOadd_ne_zero f (m + 1) 0), ocExp_ocOadd]
    by_cases h0 : icmp e f = 0
    · rw [if_pos h0, icmp_ocOadd, icmp_self f f le_rfl,
        show cmpV m (m + 1) = 0 from cmpV_eq_zero.mpr (by simp)]
      simp [thenV]
    · rw [if_neg h0]
      by_cases h1 : icmp e f = 1
      · have hef : e = f :=
          icmp_eq_imp_eq (max e f) e (le_max_left _ _) f
            (le_max_right _ _) h1
        subst e
        rw [if_pos h1, ocCoeff_ocOadd, ocTail_ocOadd, icmp_ocOadd,
          icmp_self f f le_rfl,
          show cmpV m (n + (m + 1)) = 0 from
            cmpV_eq_zero.mpr (lt_of_lt_of_le
              (lt_add_of_pos_right m one_pos)
              (by simpa [add_comm] using
                (le_self_add : m + 1 ≤ (m + 1) + n)))]
        simp [thenV]
      · have h2 : icmp e f = 2 := by
          rcases icmp_cases e f with h | h | h
          · exact absurd h h0
          · exact absurd h h1
          · exact h
        rw [if_neg h1]
        have hfe : icmp f e = 0 := by
          have hswap := icmp_swap e f
          rw [h2] at hswap
          simpa [oswap] using hswap
        rw [icmp_ocOadd, hfe]
        simp [thenV]

private lemma exp_eq_of_between_same_exp {e n r q t g : V}
    (hg0 : g ≠ 0)
    (hlow : icmp (ocOadd e n r) g = 0)
    (hupp : icmp g (ocOadd e q t) = 0) :
    ocExp g = e := by
  obtain ⟨f, m, s, rfl⟩ : ∃ f m s, g = ocOadd f m s :=
    ⟨_, _, _, (ocOadd_destruct hg0).symm⟩
  rw [icmp_ocOadd] at hlow hupp
  have hef : icmp e f = 0 ∨ icmp e f = 1 := by
    rcases thenV_eq_zero.mp hlow with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hfe : icmp f e = 0 ∨ icmp f e = 1 := by
    rcases thenV_eq_zero.mp hupp with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  simp only [ocExp_ocOadd]
  rcases hef with hef | hef
  · have hswap := icmp_swap e f
    rw [hef] at hswap
    have hfe2 : icmp f e = 2 := by simpa [oswap] using hswap
    rcases hfe with hfe | hfe
    · rw [hfe2] at hfe
      exact absurd hfe _root_.two_ne_zero
    · rw [hfe2] at hfe
      exact absurd hfe (one_lt_two).ne'
  · exact (icmp_eq_imp_eq (max e f) e (le_max_left _ _) f
      (le_max_right _ _) hef).symm

private lemma tails_of_between_same_prefix {e n r t g : V}
    (hg0 : g ≠ 0)
    (hlow : icmp (ocOadd e n r) g = 0)
    (hupp : icmp g (ocOadd e n t) = 0) :
    ∃ s : V, g = ocOadd e n s ∧ icmp r s = 0 ∧ icmp s t = 0 := by
  have hexp : ocExp g = e :=
    exp_eq_of_between_same_exp hg0 hlow hupp
  obtain ⟨f, m, s, rfl⟩ : ∃ f m s, g = ocOadd f m s :=
    ⟨_, _, _, (ocOadd_destruct hg0).symm⟩
  simp only [ocExp_ocOadd] at hexp
  subst f
  rw [icmp_ocOadd, icmp_self e e le_rfl] at hlow hupp
  simp only [thenV_one_left] at hlow hupp
  rcases thenV_eq_zero.mp hlow with hnm | ⟨hnm, hrs⟩
  · rcases thenV_eq_zero.mp hupp with hmn | ⟨hmn, hst⟩
    · exact (_root_.lt_irrefl n (lt_trans (cmpV_eq_zero.mp hnm)
        (cmpV_eq_zero.mp hmn))).elim
    · have hmn' : m = n := cmpV_eq_one.mp hmn
      subst m
      exact (_root_.lt_irrefl n (cmpV_eq_zero.mp hnm)).elim
  · rcases thenV_eq_zero.mp hupp with hmn | ⟨hmn, hst⟩
    · have hnm' : n = m := cmpV_eq_one.mp hnm
      subst m
      exact (_root_.lt_irrefl n (cmpV_eq_zero.mp hmn)).elim
    · have hnm' : n = m := cmpV_eq_one.mp hnm
      subst m
      exact ⟨s, rfl, hrs, hst⟩

private lemma tail_of_between_next_coeff {e n r g : V}
    (hg0 : g ≠ 0)
    (hlow : icmp (ocOadd e n r) g = 0)
    (hupp : icmp g (ocOadd e (n + 1) 0) = 0) :
    ∃ s : V, g = ocOadd e n s ∧ icmp r s = 0 := by
  have hexp : ocExp g = e :=
    exp_eq_of_between_same_exp hg0 hlow hupp
  obtain ⟨f, m, s, rfl⟩ : ∃ f m s, g = ocOadd f m s :=
    ⟨_, _, _, (ocOadd_destruct hg0).symm⟩
  simp only [ocExp_ocOadd] at hexp
  subst f
  rw [icmp_ocOadd, icmp_self e e le_rfl] at hlow hupp
  simp only [thenV_one_left] at hlow hupp
  have hmle : m ≤ n := by
    apply lt_succ_iff_le.mp
    rcases thenV_eq_zero.mp hupp with hmn | ⟨hmn, hs0⟩
    · exact cmpV_eq_zero.mp hmn
    · exact absurd hs0 (icmp_right_zero_ne_zero s)
  rcases thenV_eq_zero.mp hlow with hnm | ⟨hnm, hrs⟩
  · exact absurd (cmpV_eq_zero.mp hnm) (not_lt_of_ge hmle)
  · have hnm' : n = m := cmpV_eq_one.mp hnm
    subst m
    exact ⟨s, rfl, hrs⟩

private lemma iadd_samePrefix_omegaBlock {e n r d k : V}
    (hde : icmp d e = 0) :
    iadd (ocOadd e n r) (ocOadd d k 0) =
      ocOadd e n (iadd r (ocOadd d k 0)) := by
  have hed : icmp e d = 2 := by
    have hswap := icmp_swap d e
    rw [hde] at hswap
    simpa [oswap] using hswap
  rw [iadd_ocOadd, if_neg (ocOadd_ne_zero d k 0), ocExp_ocOadd,
    if_neg (by rw [hed]; exact _root_.two_ne_zero),
    if_neg (by rw [hed]; exact (one_lt_two).ne')]

private lemma lift_tail_lt_iadd_omegaBlock {e n s r d k : V}
    (hde : icmp d e = 0)
    (htail : icmp s (iadd r (ocOadd d k 0)) = 0) :
    icmp (ocOadd e n s)
      (iadd (ocOadd e n r) (ocOadd d k 0)) = 0 := by
  rw [iadd_samePrefix_omegaBlock hde, icmp_ocOadd,
    icmp_self e e le_rfl, cmpV_self]
  simpa [thenV] using htail

private lemma zero_omegaCover {a g : V}
    (hg : isNF g) (hg0 : g ≠ 0)
    (hga : icmp g (iadd 0 (ocOadd a 1 0)) = 0) :
    ∃ d k : V, isNF d ∧ icmp d a = 0 ∧
      icmp g (iadd 0 (ocOadd d (k + 1) 0)) = 0 := by
  rw [iadd_zero_left] at hga
  have hExp : icmp (ocExp g) a = 0 :=
    exp_lt_of_lt_omegaPow hg hg0 hga
  obtain ⟨e, n, r, rfl⟩ : ∃ e n r, g = ocOadd e n r :=
    ⟨_, _, _, (ocOadd_destruct hg0).symm⟩
  obtain ⟨hn, he, hr, hside⟩ := (isNF_ocOadd e n r).1 hg
  simp only [ocExp_ocOadd] at hExp
  refine ⟨e, n, he, hExp, ?_⟩
  rw [iadd_zero_left, icmp_ocOadd, icmp_self e e le_rfl,
    show cmpV n (n + 1) = 0 from cmpV_eq_zero.mpr (by simp)]
  simp [thenV]

private lemma iadd_omegaPow_cover_aux (a : V) (ha : isNF a) :
    ∀ w : V, ∀ b ≤ w, ∀ g ≤ w,
      isNF b → isNF g → icmp g b ≠ 0 → g ≠ b →
      icmp g (iadd b (ocOadd a 1 0)) = 0 →
      ∃ d k : V, isNF d ∧ icmp d a = 0 ∧
        icmp g (iadd b (ocOadd d (k + 1) 0)) = 0 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro b hbw g hgw hb hg hgb hne hgz
    have hbg : icmp b g = 0 :=
      icmp_reverse_of_not_lt_not_eq hgb hne
    rcases eq_or_ne b 0 with rfl | hb0
    · exact zero_omegaCover hg hne hgz
    · have hg0 : g ≠ 0 := by
        intro hg0
        subst g
        exact hgb (icmp_zero_pos hb0)
      obtain ⟨e, n, r, rfl⟩ : ∃ e n r, b = ocOadd e n r :=
        ⟨_, _, _, (ocOadd_destruct hb0).symm⟩
      obtain ⟨hn, he, hr, hbside⟩ := (isNF_ocOadd e n r).1 hb
      have hrw : r < w := lt_of_lt_of_le (by simpa using ocTail_lt e n r) hbw
      rcases icmp_cases e a with hea | hea | hea
      · have hgz' : icmp g (ocOadd a 1 0) = 0 := by
          rw [iadd_ocOadd, if_neg (ocOadd_ne_zero a 1 0),
            ocExp_ocOadd, if_pos hea] at hgz
          exact hgz
        exact ⟨ocExp g, ocCoeff g, isNF_ocExp_of_nf hg hg0,
          exp_lt_of_lt_omegaPow hg hg0 hgz',
          lt_iadd_headBlock hb hg hg0⟩
      · have heaEq : e = a :=
          icmp_eq_imp_eq (max e a) e (le_max_left _ _) a
            (le_max_right _ _) hea
        have hgz' : icmp g (ocOadd e (n + 1) 0) = 0 := by
          rw [iadd_ocOadd, if_neg (ocOadd_ne_zero a 1 0),
            ocExp_ocOadd,
            if_neg (by rw [hea]; exact _root_.one_ne_zero),
            if_pos hea, ocCoeff_ocOadd, ocTail_ocOadd] at hgz
          exact hgz
        obtain ⟨s, rfl, hrs⟩ :=
          tail_of_between_next_coeff hg0 hbg hgz'
        obtain ⟨_, _, hs, hgside⟩ := (isNF_ocOadd e n s).1 hg
        have hs0 : s ≠ 0 := by
          intro hs0
          subst s
          exact icmp_right_zero_ne_zero r hrs
        have hde : icmp (ocExp s) e = 0 := hgside.resolve_left hs0
        refine ⟨ocExp s, ocCoeff s, isNF_ocExp_of_nf hs hs0, ?_, ?_⟩
        · simpa [heaEq] using hde
        · exact lift_tail_lt_iadd_omegaBlock hde
            (lt_iadd_headBlock hr hs hs0)
      · have hae : icmp a e = 0 := icmp_zero_of_reverse_two hea
        have hgz' :
            icmp g (ocOadd e n (iadd r (ocOadd a 1 0))) = 0 := by
          rw [iadd_ocOadd, if_neg (ocOadd_ne_zero a 1 0),
            ocExp_ocOadd,
            if_neg (by rw [hea]; exact _root_.two_ne_zero),
            if_neg (by rw [hea]; exact (one_lt_two).ne')] at hgz
          exact hgz
        obtain ⟨s, rfl, hrs, hsupp⟩ :=
          tails_of_between_same_prefix hg0 hbg hgz'
        obtain ⟨_, _, hs, hgside⟩ := (isNF_ocOadd e n s).1 hg
        have hsw : s < w := lt_of_lt_of_le (by simpa using ocTail_lt e n s) hgw
        have hsr : icmp s r ≠ 0 := by
          rw [icmp_reverse_of_zero hrs]
          exact _root_.two_ne_zero
        have hsne : s ≠ r := by
          intro h
          subst s
          have hself := icmp_self r r le_rfl
          rw [hrs] at hself
          exact _root_.zero_ne_one hself
        obtain ⟨d, k, hd, hda, htail⟩ :=
          ih (max r s) (max_lt hrw hsw)
            r (le_max_left _ _) s (le_max_right _ _)
            hr hs hsr hsne hsupp
        refine ⟨d, k, hd, hda, ?_⟩
        exact lift_tail_lt_iadd_omegaBlock (icmp_transitive hda hae) htail

/--
Every normal-form code strictly between `b` and `b + ω^a` lies below a
finite block `b + ω^d · (k + 1)` for some normal-form exponent `d < a`.
-/
lemma iadd_omegaPow_cover {a b g : V}
    (ha : isNF a) (hb : isNF b) (hg : isNF g)
    (hgb : icmp g b ≠ 0) (hne : g ≠ b)
    (hgz : icmp g (iadd b (ocOadd a 1 0)) = 0) :
    ∃ d k : V, isNF d ∧ icmp d a = 0 ∧
      icmp g (iadd b (ocOadd d (k + 1) 0)) = 0 :=
  iadd_omegaPow_cover_aux a ha (max b g) b (le_max_left _ _)
    g (le_max_right _ _) hb hg hgb hne hgz

/-- Iterating addition by `ω^d` for a positive number of steps gives the
corresponding single Cantor-normal-form block. -/
lemma safeIter_omegaBlock_succ (b d k : V) (hb : isNF b) (hd : isNF d) :
    (safeIterConstruction (V := V)).result ![b, ocOadd d 1 0] (k + 1) =
      iadd b (ocOadd d (k + 1) 0) := by
  induction k using ISigma1.sigma1_succ_induction
  · apply HierarchySymbol.Definable.comp₂
    · exact ⟨safeIterDef.rew <| Rew.embSubsts
          ![(#0 : ArithmeticSemiterm V 2), &b, &(ocOadd d 1 0), ‘#1 + 1’],
        by intro v; simp [eval_safeIterDef]⟩
    · definability
  case zero =>
    simp only [zero_add]
    have hstep :
        (safeIterConstruction (V := V)).result ![b, ocOadd d 1 0] 1 =
          safeIadd b (ocOadd d 1 0) := by
      calc
        (safeIterConstruction (V := V)).result ![b, ocOadd d 1 0] 1 =
            (safeIterConstruction (V := V)).result
              ![b, ocOadd d 1 0] (0 + 1) := by simp
        _ = safeIadd b (ocOadd d 1 0) := by
          rw [PR.Construction.result_succ, PR.Construction.result_zero]
          rfl
    rw [hstep, safeIadd_of_nf hb]
  case succ k ih =>
    rw [PR.Construction.result_succ]
    change safeIadd
        ((safeIterConstruction (V := V)).result ![b, ocOadd d 1 0] (k + 1))
        (ocOadd d 1 0) = iadd b (ocOadd d ((k + 1) + 1) 0)
    rw [ih, safeIadd_of_nf (isNF_iadd_omegaBlock hd (by simp) b hb),
      iadd_omegaBlock_succ]

/-! ### Pure-arithmetic omega-cover statement -/

private def arithAddAt {n : ℕ}
    (z x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, x, y] ▹ Rewriting.emb safeIaddDef.val

private def arithIterAt {n : ℕ}
    (z b w k : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, b, w, k] ▹ Rewriting.emb safeIterDef.val

private def arithPrecAt {n : ℕ}
    (x y : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![x, y] ▹ Rewriting.emb precDef.val

private def arithOmegaPowAt {n : ℕ}
    (z a : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₒᵣ ℕ n :=
  Rew.subst ![z, a] ▹ Rewriting.emb omegaPowDef.val

/-- The omega-cover premise, stated wholly in the language of arithmetic. -/
def arithmeticOmegaCoverStatement : Sentence ℒₒᵣ :=
  (∀¹ ∀¹ ∀¹ ∀¹ ∀¹
    (∼(arithOmegaPowAt #2 #4) ⋎
      (∼(arithAddAt #1 #3 #2) ⋎
        (∼(arithPrecAt #0 #1) ⋎
          (arithPrecAt #0 #3 ⋎
            ((“#0 = #3” : Semiformula ℒₒᵣ ℕ 5) ⋎
              (∃¹ ∃¹ ∃¹ ∃¹
                (arithPrecAt #3 #8 ⋏
                  (arithOmegaPowAt #2 #3 ⋏
                    (arithIterAt #0 #7 #2 #1 ⋏
                      arithPrecAt #4 #0)))))))))).univCl

/-- IΣ₁ proves the concrete omega-cover law for the internal CNF codes. -/
theorem arithmetic_omegaCover : 𝗜𝚺₁ ⊢ arithmeticOmegaCoverStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simp [models_iff, arithmeticOmegaCoverStatement, arithOmegaPowAt,
    arithAddAt, arithPrecAt, arithIterAt, eval_safeIterDef]
  intro a b u z g
  by_cases hω : isNF a ∧ u = ocOadd a 1 0
  · right
    by_cases hadd : z = safeIadd b u
    · right
      by_cases hprec : isNF g ∧ isNF z ∧ icmp g z = 0
      · right
        rcases hω with ⟨ha, hu⟩
        rcases hprec with ⟨hg, hz, hgz⟩
        have hb : isNF b := by
          by_contra hb
          have hzb : z = b := by
            calc
              z = safeIadd b u := hadd
              _ = b := safeIadd_of_not_nf hb
          exact hb (hzb ▸ hz)
        have hzi : z = iadd b (ocOadd a 1 0) := by
          calc
            z = safeIadd b u := hadd
            _ = safeIadd b (ocOadd a 1 0) := by rw [hu]
            _ = iadd b (ocOadd a 1 0) := safeIadd_of_nf hb
        rw [hzi] at hgz
        by_cases hgb : icmp g b = 0
        · exact Or.inl ⟨hg, hb, hgb⟩
        · right
          by_cases hEq : g = b
          · exact Or.inl hEq
          · right
            obtain ⟨d, k, hd, hda, hgk⟩ :=
              iadd_omegaPow_cover ha hb hg hgb hEq hgz
            refine ⟨d, ⟨hd, ha, hda⟩, hd, hg, k + 1, ?_, ?_⟩
            · rw [safeIter_omegaBlock_succ b d k hb hd]
              exact isNF_iadd_omegaBlock hd (by simp) b hb
            · rw [safeIter_omegaBlock_succ b d k hb hd]
              exact hgk
      · left
        intro hg hz hgz
        exact hprec ⟨hg, hz, hgz⟩
    · left
      exact hadd
  · left
    intro ha hu
    exact hω ⟨ha, hu⟩

/-! ### Transport to PA[X] and the concrete jump lemmas -/

lemma models_omegaCover_iff_arithmetic {M : Type*} [Nonempty M]
    [sLX : Structure LX M] :
    M↓[LX] ⊧ omegaCoverStatement precCode safeAddCode omegaPowCode safeIterCode ↔
      (sLX.lMap toLX).toStruc ⊧ arithmeticOmegaCoverStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  simp [models_iff, omegaCoverStatement, arithmeticOmegaCoverStatement,
    arithOmegaPowAt, arithAddAt, arithPrecAt, arithIterAt,
    omegaPowAt, addAt, precAt, iterAt, precCode, safeAddCode,
    omegaPowCode, safeIterCode, liftCode, Semiformula.eval_lMap]
  rfl

/-- Concrete omega-cover premise for Gentzen's Lemma A. -/
theorem concrete_omegaCover :
    paLX ⊢ omegaCoverStatement precCode safeAddCode omegaPowCode safeIterCode := by
  apply paLX_of_peano_semantic
    (Entailment.WeakerThan.pbl arithmetic_omegaCover)
  intro M _ _
  exact models_omegaCover_iff_arithmetic

/-- Gentzen's Lemma A for the internal CNF codes and totalized addition. -/
theorem concrete_jump_A (φ : Semiformula LX ℕ 1) :
    paLX ⊢ jumpAStatement precCode safeAddCode omegaPowCode φ :=
  jump_A precCode safeAddCode omegaPowCode safeIterCode φ
    concrete_iterZero concrete_iterSucc concrete_omegaCover

/-- Gentzen's Lemma B for the internal CNF codes and totalized addition. -/
theorem concrete_jump_B (φ : Semiformula LX ℕ 1) :
    paLX ⊢ jumpBStatement precCode safeAddCode omegaPowCode φ :=
  jump_B precCode safeAddCode omegaPowCode φ
    (concrete_jump_A φ) concrete_noPredZero concrete_zeroAdd

end OrdinalAnalysis.Gentzen.OmegaCover
