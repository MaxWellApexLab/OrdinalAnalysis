/-
  Strict monotonicity of the natural sum.

  The reduction lemma rebuilds a rule around a recursive call: the premise
  arrives with ordinal `nadd β' γ` where `β' < β`, and the conclusion must be
  reported at `nadd β γ`.  Every inference rule of the calculus demands
  premise < conclusion, so that step needs

      β' < β  →  nadd β' γ < nadd β γ

  and nothing weaker will do.
-/
import OrdinalAnalysis.Ordinal.NaturalSum

namespace OrdinalAnalysis

open ONote

/-- A nonzero notation contributes strictly to the natural sum. -/
theorem lt_nadd_of_pos : ∀ (a b : ONote), NF a → NF b → 0 < ONote.repr a →
    ONote.repr b < ONote.repr (nadd a b)
  | 0, _, _, _, h => by simp at h
  | oadd e n a, 0, _, _, _ => by
      simpa [ONote.lt_def] using ONote.oadd_pos e n a
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂, _ => by
      have hc : ((e₁.cmp e₂).Compares e₁ e₂) := @cmp_compares _ _ h₁.fst h₂.fst
      rw [nadd.eq_def]
      cases h : e₁.cmp e₂ <;> simp only [h] <;> rw [h] at hc
      · -- e₁ < e₂ : head unchanged, tail strictly grows
        have hp : (0 : Ordinal) < ONote.repr (oadd e₁ n₁ a₁) := by
          simpa [ONote.lt_def] using ONote.oadd_pos e₁ n₁ a₁
        have ih := lt_nadd_of_pos (oadd e₁ n₁ a₁) a₂ h₁ h₂.snd hp
        simp only [ONote.repr]
        gcongr
      · -- e₁ = e₂ : the coefficient strictly increases
        obtain rfl := eq_of_cmp_eq h
        exact ONote.oadd_lt_oadd_2 h₂ (by simp)
      · -- e₂ < e₁ : the head is strictly larger
        exact ONote.oadd_lt_oadd_1 h₂ hc

/-- The three sources of a strict inequality between Cantor normal forms.
mathlib supplies the three introduction rules `oadd_lt_oadd_1/2/3` but no
elimination rule; this is it. -/
theorem lt_oadd_cases {e x e' x' : ONote} {n n' : ℕ+}
    (ha : NF (oadd e n x)) (ha' : NF (oadd e' n' x'))
    (h : ONote.repr (oadd e n x) < ONote.repr (oadd e' n' x')) :
    ONote.repr e < ONote.repr e'
      ∨ (e = e' ∧ ((n : ℕ) < (n' : ℕ)
          ∨ ((n : ℕ) = (n' : ℕ) ∧ ONote.repr x < ONote.repr x'))) := by
  have hcmp : (((oadd e n x).cmp (oadd e' n' x')).Compares (oadd e n x) (oadd e' n' x')) :=
    @cmp_compares _ _ ha ha'
  have hlt : (oadd e n x).cmp (oadd e' n' x') = Ordering.lt := by
    rcases hh : (oadd e n x).cmp (oadd e' n' x') with _ | _ | _
    · rfl
    · rw [hh] at hcmp
      have heq : oadd e n x = oadd e' n' x' := hcmp
      rw [heq] at h
      exact absurd h (lt_irrefl _)
    · rw [hh] at hcmp
      exact absurd h (not_lt_of_gt hcmp)
  simp only [ONote.cmp, Ordering.then_eq_lt] at hlt
  have hee : ((e.cmp e').Compares e e') := @cmp_compares _ _ ha.fst ha'.fst
  rcases hlt with hl | ⟨he, hrest⟩
  · left; rw [hl] at hee; exact hee
  · right
    have hefeq : e = e' := eq_of_cmp_eq he
    refine ⟨hefeq, ?_⟩
    rcases hrest with hn | ⟨hn, hx⟩
    · left
      exact (_root_.cmp_eq_lt_iff _ _).mp hn
    · right
      have hneq : (n : ℕ) = (n' : ℕ) := (_root_.cmp_eq_eq_iff _ _).mp hn
      refine ⟨hneq, ?_⟩
      have hxx : ((x.cmp x').Compares x x') := @cmp_compares _ _ ha.snd ha'.snd
      rw [hx] at hxx
      exact hxx

/-- Strict monotonicity in the left argument.  This is what the reduction
lemma's rule-rebuilding step needs.

The case analysis is forced by the two structures involved: `a < a'` on Cantor
normal forms has three sources (smaller exponent, equal exponent with smaller
coefficient, both equal with smaller tail), and `nadd` branches three ways on
each argument. -/
theorem nadd_lt_nadd_left : ∀ (a a' b : ONote), NF a → NF a' → NF b →
    ONote.repr a < ONote.repr a' →
    ONote.repr (nadd a b) < ONote.repr (nadd a' b)
  | a, a', 0, _, _, _, h => by simpa using h
  | 0, a', oadd f m y, _, ha', hb, h => by
      have hpos : (0 : Ordinal) < ONote.repr a' := by simpa using h
      simpa using lt_nadd_of_pos a' (oadd f m y) ha' hb hpos
  | oadd e n x, 0, oadd f m y, _, _, _, h => by
      exfalso
      have : (0 : Ordinal) < ONote.repr (oadd e n x) := by
        simpa [ONote.lt_def] using ONote.oadd_pos e n x
      simp only [ONote.repr_zero] at h
      exact absurd h (not_lt_of_gt this)
  | oadd e n x, oadd e' n' x', oadd f m y, ha, ha', hb, h => by
      rcases lt_oadd_cases ha ha' h with hee' | ⟨rfl, hrest⟩
      · -- the exponents differ.  Only five of the nine branch combinations are
        -- reachable: `e' ≤ f` forces `e < f`, because `e < e'`.
        have hef : ((e.cmp f).Compares e f) := @cmp_compares _ _ ha.fst hb.fst
        have he'f : ((e'.cmp f).Compares e' f) := @cmp_compares _ _ ha'.fst hb.fst
        rw [nadd.eq_def, nadd.eq_def]
        cases hb1 : e.cmp f <;> cases hb2 : e'.cmp f <;>
          simp only [hb1, hb2] <;> rw [hb1] at hef <;> rw [hb2] at he'f
        · -- e < f, e' < f : shared head and coefficient, recurse on the tails
          exact ONote.oadd_lt_oadd_3
            (nadd_lt_nadd_left (oadd e n x) (oadd e' n' x') y ha ha' hb.snd h)
        · -- e < f, e' = f : coefficient m against n' + m
          obtain rfl := eq_of_cmp_eq hb2
          exact ONote.oadd_lt_oadd_2
            (ONote.NF.oadd hb.fst m (nadd_nfBelow (ONote.NF.below_of_lt hef ha) hb.snd'))
            (by simp)
        · -- e < f, f < e' : head f against head e'
          exact ONote.oadd_lt_oadd_1
            (ONote.NF.oadd hb.fst m (nadd_nfBelow (ONote.NF.below_of_lt hef ha) hb.snd'))
            he'f
        · -- e = f, e' < f : impossible, e < e' ≤ f = e
          exact absurd (lt_trans hee' he'f) (by rw [eq_of_cmp_eq hb1]; exact lt_irrefl _)
        · exact absurd (eq_of_cmp_eq hb2 ▸ eq_of_cmp_eq hb1 ▸ hee') (lt_irrefl _)
        · -- e = f, f < e' : head e = f against head e'
          obtain rfl := eq_of_cmp_eq hb1
          exact ONote.oadd_lt_oadd_1
            (ONote.NF.oadd ha.fst (n + m) (nadd_nfBelow ha.snd' hb.snd')) he'f
        · -- f < e, e' < f : impossible
          exact absurd (lt_trans hee' he'f) (not_lt_of_gt hef)
        · -- f < e, e' = f : impossible
          exact absurd (eq_of_cmp_eq hb2 ▸ hee') (not_lt_of_gt hef)
        · -- f < e, f < e' : heads e and e'
          exact ONote.oadd_lt_oadd_1
            (ONote.NF.oadd ha.fst n
              (nadd_nfBelow ha.snd' (ONote.NF.below_of_lt hef hb))) hee'
      · -- equal exponents: both merges branch on the same comparison with `f`
        have hef : ((e.cmp f).Compares e f) := @cmp_compares _ _ ha.fst hb.fst
        rw [nadd.eq_def, nadd.eq_def]
        cases hb1 : e.cmp f <;> simp only [hb1] <;> rw [hb1] at hef
        · -- e < f : shared head `f` and coefficient `m`, recurse on the tails
          refine ONote.oadd_lt_oadd_3 ?_
          exact nadd_lt_nadd_left (oadd e n x) (oadd e n' x') y ha ha' hb.snd h
        · -- e = f : the coefficients add on both sides
          obtain rfl := eq_of_cmp_eq hb1
          rcases hrest with hlt | ⟨heq, hx⟩
          · refine ONote.oadd_lt_oadd_2 ?_ ?_
            · exact ONote.NF.oadd ha.fst (n + m) (nadd_nfBelow ha.snd' hb.snd')
            · simpa using Nat.add_lt_add_right hlt (m : ℕ)
          · have hnn : n = n' := by
              exact Subtype.ext heq
            subst hnn
            refine ONote.oadd_lt_oadd_3 ?_
            exact nadd_lt_nadd_left x x' y ha.snd ha'.snd hb.snd hx
        · -- f < e : shared head `e`, coefficients `n` and `n'`
          rcases hrest with hlt | ⟨heq, hx⟩
          · refine ONote.oadd_lt_oadd_2 ?_ ?_
            · exact ONote.NF.oadd ha.fst n
                (nadd_nfBelow ha.snd' (ONote.NF.below_of_lt hef hb))
            · exact hlt
          · have hnn : n = n' := Subtype.ext heq
            subst hnn
            refine ONote.oadd_lt_oadd_3 ?_
            exact nadd_lt_nadd_left x x' (oadd f m y) ha.snd ha'.snd hb hx
  termination_by a a' b => (nsize b, nsize a + nsize a')
  decreasing_by
    all_goals simp_wf
    all_goals (try simp only [nsize_oadd, nsize_zero])
    all_goals omega

/-- Strict monotonicity in the right argument, by commutativity. -/
theorem nadd_lt_nadd_right (a b b' : ONote) (ha : NF a) (hb : NF b) (hb' : NF b')
    (h : ONote.repr b < ONote.repr b') :
    ONote.repr (nadd a b) < ONote.repr (nadd a b') := by
  have := nadd_lt_nadd_left b b' a hb hb' ha h
  rwa [nadd_comm b a, nadd_comm b' a] at this

end OrdinalAnalysis
