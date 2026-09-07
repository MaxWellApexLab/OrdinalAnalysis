/-
  The natural (Hessenberg) sum of Veblen notations.

  This is the `VNote` analogue of `OrdinalAnalysis/Ordinal/NaturalSum.lean`,
  `NaturalSumMono.lean` and `NONatSum.lean`, which do the same job for `ONote`.  Ordinal
  addition is not commutative, and the cut-reduction lemma needs a commutative sum because
  the two premises of a cut enter symmetrically; the natural sum merges the two normal forms
  by leading terms and adds the multiplicities of equal leading terms.

  Three things are different from the `ONote` development, all of them simplifications.

  * The leading term of `vadd a b n c` is the *Veblen value* `φ_a(b)`, not `ω ^ e`, and what
    the merge needs to know about it is exactly that it is additively principal.  Every
    value of `veblen` is (`isPrincipal_add_veblen`), so the normal-form proof, the domination
    lemmas and additive indecomposability are all instances of one lemma,
    `nadd_lt_of_isPrincipal`, rather than three separate arguments.
  * `ONote.NFBelow o b` says "all exponents below `b`"; here `NFBelow o s` says
    "normal, and `repr o < s`" — a genuine bound rather than a syntactic one.  That is what
    lets `nadd_nfBelow` be stated for an arbitrary additively principal `s` and be reused at
    `s = Γ₀` (normality), `s = ω ^ α` (indecomposability) and `s = φ_1(α)` (ε-numbers).
  * The three-way case split on `<` between normal forms is `lt_mul_natCast_add_cases`,
    the elimination rule matching `cmp_mul_natCast_add`; `ONote`'s `lt_oadd_cases` had to be
    reconstructed from `cmp` by hand.

  One thing is *not* like `ONote`: `nadd` is **not** commutative without the normal-form
  hypothesis.  `cmp x y = Ordering.eq` does not imply `x = y` on raw notations, because
  `φ_a(φ_{a'}(b')) = φ_{a'}(b')` when `a < a'`; the two sides of `nadd_comm` then really are
  different terms, and one of them is not a normal form.  So `VNote.nadd_comm` carries `NF`
  hypotheses, unlike `OrdinalAnalysis.nadd_comm` on `ONote`.
-/
import OrdinalAnalysis.Ordinal.Veblen.Gamma0Note

set_option autoImplicit false

namespace OrdinalAnalysis

open Ordinal

namespace VNote

/-! ### Ordinal preliminaries -/

/-- The elimination rule matching `cmp_mul_natCast_add`: a strict inequality between two
normal forms `p * m + x < q * k + y` has exactly three sources — a smaller leading term, an
equal leading term with a smaller multiplicity, or both equal with a smaller tail.

This is the `VNote` counterpart of `OrdinalAnalysis.lt_oadd_cases`, and it is much shorter
because `cmp_mul_natCast_add` already did the arithmetic. -/
theorem lt_mul_natCast_add_cases {p q x y : Ordinal} {m k : ℕ}
    (hp : IsPrincipal (· + ·) p) (hq : IsPrincipal (· + ·) q)
    (hx : x < p) (hy : y < q) (hm : 0 < m) (hk : 0 < k)
    (h : p * m + x < q * k + y) :
    p < q ∨ (p = q ∧ (m < k ∨ (m = k ∧ x < y))) := by
  have hc := cmp_mul_natCast_add hp hq hx hy hm hk
  rw [h.cmp_eq_lt] at hc
  rcases Ordering.then_eq_lt.1 hc.symm with h1 | ⟨h1, h2⟩
  · exact Or.inl ((_root_.cmp_eq_lt_iff _ _).1 h1)
  · refine Or.inr ⟨(_root_.cmp_eq_eq_iff _ _).1 h1, ?_⟩
    rcases Ordering.then_eq_lt.1 h2 with h3 | ⟨h3, h4⟩
    · exact Or.inl ((_root_.cmp_eq_lt_iff _ _).1 h3)
    · exact Or.inr ⟨(_root_.cmp_eq_eq_iff _ _).1 h3, (_root_.cmp_eq_lt_iff _ _).1 h4⟩

/-! ### Multiplicities

`ℕ+` addition is `Subtype`-wrapped `ℕ` addition, so all three facts are `rfl` plus `omega`;
they are separated out because `omega` cannot see through the coercion on its own. -/

theorem pnat_add_coe (n m : ℕ+) : ((n + m : ℕ+) : ℕ) = (n : ℕ) + (m : ℕ) := rfl

theorem pnat_lt_add_right (n m : ℕ+) : (n : ℕ) < ((n + m : ℕ+) : ℕ) :=
  Nat.lt_add_of_pos_right m.property

theorem pnat_lt_add_left (n m : ℕ+) : (m : ℕ) < ((n + m : ℕ+) : ℕ) :=
  Nat.lt_add_of_pos_left n.property

theorem pnat_add_lt_add_right {n n' : ℕ+} (m : ℕ+) (h : (n : ℕ) < (n' : ℕ)) :
    ((n + m : ℕ+) : ℕ) < ((n' + m : ℕ+) : ℕ) :=
  Nat.add_lt_add_right h _

/-! ### The leading term -/

/-- The leading Veblen value of a notation is at most the notation's value. -/
theorem lead_le_repr (a b : VNote) (n : ℕ+) (c : VNote) :
    veblen (repr a) (repr b) ≤ repr (VNote.vadd a b n c) := by
  rw [repr_vadd]
  refine le_trans ?_ le_self_add
  have h1 : (1 : Ordinal) ≤ ((n : ℕ) : Ordinal) := by
    have : 1 ≤ (n : ℕ) := n.property
    exact_mod_cast this
  calc veblen (repr a) (repr b) = veblen (repr a) (repr b) * 1 := (mul_one _).symm
    _ ≤ veblen (repr a) (repr b) * ((n : ℕ) : Ordinal) := mul_le_mul_right h1 _

/-- On normal forms, comparing the two single Veblen terms `vadd a b 1 0` and
`vadd a' b' 1 0` computes the comparison of the leading Veblen values.  This is the bridge
between the syntactic test that `nadd` branches on and the ordinal arithmetic of the
proofs. -/
theorem lead_cmp_eq_cmp_repr {a b c a' b' c' : VNote} {n n' : ℕ+}
    (hx : NF (VNote.vadd a b n c)) (hy : NF (VNote.vadd a' b' n' c')) :
    cmp (VNote.vadd a b 1 0) (VNote.vadd a' b' 1 0)
      = _root_.cmp (veblen (repr a) (repr b)) (veblen (repr a') (repr b')) := by
  have h := cmp_eq_cmp_repr (VNote.vadd a b 1 0) (VNote.vadd a' b' 1 0)
    (NF.vadd_zero 1 hx.fst hx.snd hx.snd_lt) (NF.vadd_zero 1 hy.fst hy.snd hy.snd_lt)
  rwa [repr_vadd_one_zero, repr_vadd_one_zero] at h

/-! ### The natural sum -/

/-- Natural (Hessenberg) sum of Veblen notations: merge the two normal forms, adding the
multiplicities of equal leading terms.  Unlike ordinal addition this is commutative on
normal forms (`VNote.nadd_comm`). -/
def nadd : VNote → VNote → VNote
  | 0, y => y
  | VNote.vadd a b n c, 0 => VNote.vadd a b n c
  | VNote.vadd a b n c, VNote.vadd a' b' n' c' =>
    match cmp (VNote.vadd a b 1 0) (VNote.vadd a' b' 1 0) with
    | Ordering.eq => VNote.vadd a b (n + n') (nadd c c')
    | Ordering.gt => VNote.vadd a b n (nadd c (VNote.vadd a' b' n' c'))
    | Ordering.lt => VNote.vadd a' b' n' (nadd (VNote.vadd a b n c) c')
termination_by x y => size x + size y
decreasing_by
  all_goals
    simp only [size_vadd]
    omega

@[simp] theorem zero_nadd (y : VNote) : nadd 0 y = y := by rw [nadd.eq_def]

@[simp] theorem nadd_zero (x : VNote) : nadd x 0 = x := by
  cases x with
  | zero => rw [nadd.eq_def]; rfl
  | vadd a b n c => rw [nadd.eq_def]

theorem nadd_vadd_vadd (a b : VNote) (n : ℕ+) (c a' b' : VNote) (n' : ℕ+) (c' : VNote) :
    nadd (VNote.vadd a b n c) (VNote.vadd a' b' n' c') =
      match cmp (VNote.vadd a b 1 0) (VNote.vadd a' b' 1 0) with
      | Ordering.eq => VNote.vadd a b (n + n') (nadd c c')
      | Ordering.gt => VNote.vadd a b n (nadd c (VNote.vadd a' b' n' c'))
      | Ordering.lt => VNote.vadd a' b' n' (nadd (VNote.vadd a b n c) c') := by
  rw [nadd.eq_def]

theorem nadd_of_eq {a b c a' b' c' : VNote} {n n' : ℕ+}
    (h : cmp (VNote.vadd a b 1 0) (VNote.vadd a' b' 1 0) = Ordering.eq) :
    nadd (VNote.vadd a b n c) (VNote.vadd a' b' n' c')
      = VNote.vadd a b (n + n') (nadd c c') := by
  rw [nadd_vadd_vadd, h]

theorem nadd_of_gt {a b c a' b' c' : VNote} {n n' : ℕ+}
    (h : cmp (VNote.vadd a b 1 0) (VNote.vadd a' b' 1 0) = Ordering.gt) :
    nadd (VNote.vadd a b n c) (VNote.vadd a' b' n' c')
      = VNote.vadd a b n (nadd c (VNote.vadd a' b' n' c')) := by
  rw [nadd_vadd_vadd, h]

theorem nadd_of_lt {a b c a' b' c' : VNote} {n n' : ℕ+}
    (h : cmp (VNote.vadd a b 1 0) (VNote.vadd a' b' 1 0) = Ordering.lt) :
    nadd (VNote.vadd a b n c) (VNote.vadd a' b' n' c')
      = VNote.vadd a' b' n' (nadd (VNote.vadd a b n c) c') := by
  rw [nadd_vadd_vadd, h]

/-! ### Normal form, and additive indecomposability

Both come from the same induction.  `NFBelow x s` is "`x` is a normal form and `repr x < s`";
for additively principal `s` the natural sum preserves it, because the merge never
manufactures a leading term that was not already there. -/

theorem nadd_nfBelow : ∀ (x y : VNote) {s : Ordinal}, IsPrincipal (· + ·) s →
    NFBelow x s → NFBelow y s → NFBelow (nadd x y) s
  | 0, _, _, _, _, hy => by rw [zero_nadd]; exact hy
  | VNote.vadd _ _ _ _, 0, _, _, hx, _ => by rw [nadd_zero]; exact hx
  | VNote.vadd a b n c, VNote.vadd a' b' n' c', _, hs, hx, hy => by
    have hxn : NF (VNote.vadd a b n c) := hx.1
    have hyn : NF (VNote.vadd a' b' n' c') := hy.1
    have hP : IsPrincipal (· + ·) (veblen (repr a) (repr b)) := isPrincipal_add_veblen _ _
    have hP' : IsPrincipal (· + ·) (veblen (repr a') (repr b')) := isPrincipal_add_veblen _ _
    have hPs : veblen (repr a) (repr b) < _ := (lead_le_repr a b n c).trans_lt hx.2
    have hP's : veblen (repr a') (repr b') < _ := (lead_le_repr a' b' n' c').trans_lt hy.2
    have hcmp := lead_cmp_eq_cmp_repr hxn hyn
    rcases lt_trichotomy (veblen (repr a) (repr b)) (veblen (repr a') (repr b')) with
      hlt | heq | hgt
    · rw [nadd_of_lt (by rw [hcmp, hlt.cmp_eq_lt])]
      have hb1 : NFBelow (VNote.vadd a b n c) (veblen (repr a') (repr b')) :=
        ⟨hxn, NF.repr_lt_of_lead_lt hxn hP' hlt⟩
      have hb2 : NFBelow c' (veblen (repr a') (repr b')) := ⟨hyn.tail, hyn.tail_lt⟩
      have ih := nadd_nfBelow (VNote.vadd a b n c) c' hP' hb1 hb2
      have hnf : NF (VNote.vadd a' b' n' (nadd (VNote.vadd a b n c) c')) :=
        NF.vadd hyn.fst hyn.snd ih.1 hyn.snd_lt ih.2
      exact ⟨hnf, NF.repr_lt_of_lead_lt hnf hs hP's⟩
    · rw [nadd_of_eq (by rw [hcmp, (_root_.cmp_eq_eq_iff _ _).2 heq])]
      have hb1 : NFBelow c (veblen (repr a) (repr b)) := ⟨hxn.tail, hxn.tail_lt⟩
      have hb2 : NFBelow c' (veblen (repr a) (repr b)) := ⟨hyn.tail, by
        rw [heq]; exact hyn.tail_lt⟩
      have ih := nadd_nfBelow c c' hP hb1 hb2
      have hnf : NF (VNote.vadd a b (n + n') (nadd c c')) :=
        NF.vadd hxn.fst hxn.snd ih.1 hxn.snd_lt ih.2
      exact ⟨hnf, NF.repr_lt_of_lead_lt hnf hs hPs⟩
    · rw [nadd_of_gt (by rw [hcmp, hgt.cmp_eq_gt])]
      have hb1 : NFBelow c (veblen (repr a) (repr b)) := ⟨hxn.tail, hxn.tail_lt⟩
      have hb2 : NFBelow (VNote.vadd a' b' n' c') (veblen (repr a) (repr b)) :=
        ⟨hyn, NF.repr_lt_of_lead_lt hyn hP hgt⟩
      have ih := nadd_nfBelow c (VNote.vadd a' b' n' c') hP hb1 hb2
      have hnf : NF (VNote.vadd a b n (nadd c (VNote.vadd a' b' n' c'))) :=
        NF.vadd hxn.fst hxn.snd ih.1 hxn.snd_lt ih.2
      exact ⟨hnf, NF.repr_lt_of_lead_lt hnf hs hPs⟩
termination_by x y => size x + size y
decreasing_by
  all_goals
    simp only [size_vadd]
    omega

/-- **The natural sum of normal forms is a normal form.** -/
theorem nf_nadd {x y : VNote} (hx : NF x) (hy : NF y) : NF (nadd x y) :=
  (nadd_nfBelow x y isPrincipal_add_gamma_zero ⟨hx, hx.repr_lt_gamma_zero⟩
    ⟨hy, hy.repr_lt_gamma_zero⟩).1

/-- **Additive indecomposability, in its general form.**  Every additively principal bound is
closed under the natural sum of normal forms.  `nadd_lt_omegaPow` and `nadd_lt_veblen` are
the two instances the calculus uses. -/
theorem nadd_lt_of_isPrincipal {x y : VNote} {s : Ordinal} (hx : NF x) (hy : NF y)
    (hs : IsPrincipal (· + ·) s) (h1 : repr x < s) (h2 : repr y < s) :
    repr (nadd x y) < s :=
  (nadd_nfBelow x y hs ⟨hx, h1⟩ ⟨hy, h2⟩).2

/-- Every Veblen value is closed under the natural sum. -/
theorem nadd_lt_veblen {x y : VNote} {p q : Ordinal} (hx : NF x) (hy : NF y)
    (h1 : repr x < veblen p q) (h2 : repr y < veblen p q) : repr (nadd x y) < veblen p q :=
  nadd_lt_of_isPrincipal hx hy (isPrincipal_add_veblen p q) h1 h2

/-- **Additive indecomposability of `ω ^ a` for the natural sum**, on raw notations. -/
theorem nadd_lt_omega0_opow {x y : VNote} {a : Ordinal} (hx : NF x) (hy : NF y)
    (h1 : repr x < ω ^ a) (h2 : repr y < ω ^ a) : repr (nadd x y) < ω ^ a :=
  nadd_lt_of_isPrincipal hx hy (isPrincipal_add_omega0_opow a) h1 h2

/-! ### Commutativity -/

/-- The natural sum is commutative on normal forms.

It is *not* commutative on raw notations: `cmp x y = Ordering.eq` does not force `x = y`,
because `φ_a(φ_{a'}(b')) = φ_{a'}(b')` for `a < a'`.  The normal-form side condition
"`b` is not a fixed point of `φ_a`" is exactly what rules that out, through
`veblen_eq_veblen_of_lt`. -/
theorem nadd_comm : ∀ (x y : VNote), NF x → NF y → nadd x y = nadd y x
  | 0, _, _, _ => by rw [zero_nadd, nadd_zero]
  | VNote.vadd _ _ _ _, 0, _, _ => by rw [nadd_zero, zero_nadd]
  | VNote.vadd a b n c, VNote.vadd a' b' n' c', hx, hy => by
    have hcmp := lead_cmp_eq_cmp_repr hx hy
    have hcmp' := lead_cmp_eq_cmp_repr hy hx
    rcases lt_trichotomy (veblen (repr a) (repr b)) (veblen (repr a') (repr b')) with
      hlt | heq | hgt
    · rw [nadd_of_lt (by rw [hcmp, hlt.cmp_eq_lt]),
        nadd_of_gt (by rw [hcmp', hlt.cmp_eq_gt])]
      rw [nadd_comm (VNote.vadd a b n c) c' hx hy.tail]
    · obtain ⟨ha, hb⟩ := veblen_eq_veblen_of_lt heq hx.snd_lt hy.snd_lt
      have ea : a = a' := repr_inj hx.fst hy.fst ha
      have eb : b = b' := repr_inj hx.snd hy.snd hb
      subst ea; subst eb
      rw [nadd_of_eq (by rw [hcmp, (_root_.cmp_eq_eq_iff _ _).2 heq]),
        nadd_of_eq (by rw [hcmp', (_root_.cmp_eq_eq_iff _ _).2 heq.symm]),
        nadd_comm c c' hx.tail hy.tail, add_comm n n']
    · rw [nadd_of_gt (by rw [hcmp, hgt.cmp_eq_gt]),
        nadd_of_lt (by rw [hcmp', hgt.cmp_eq_lt])]
      rw [nadd_comm c (VNote.vadd a' b' n' c') hx.tail hy]
termination_by x y => size x + size y
decreasing_by
  all_goals
    simp only [size_vadd]
    omega

/-! ### Domination and monotonicity

Stated on `repr`, as in `NaturalSumMono.lean`: the order on notations is the order on the
ordinals they denote, and the notations that are not normal forms denote nothing sensible. -/

/-- A nonzero summand contributes strictly. -/
theorem lt_nadd_of_pos : ∀ (x y : VNote), NF x → NF y → 0 < repr x →
    repr y < repr (nadd x y)
  | 0, _, _, _, h => by simp at h
  | VNote.vadd a b n c, 0, _, _, _ => by
    rw [nadd_zero, repr_zero]; exact repr_pos_of_vadd a b n c
  | VNote.vadd a b n c, VNote.vadd f g m z, hx, hy, _ => by
    have hP : IsPrincipal (· + ·) (veblen (repr a) (repr b)) := isPrincipal_add_veblen _ _
    have hM : IsPrincipal (· + ·) (veblen (repr f) (repr g)) := isPrincipal_add_veblen _ _
    have hcmp := lead_cmp_eq_cmp_repr hx hy
    rcases lt_trichotomy (veblen (repr a) (repr b)) (veblen (repr f) (repr g)) with
      hlt | heq | hgt
    · rw [nadd_of_lt (by rw [hcmp, hlt.cmp_eq_lt])]
      simp only [repr_vadd]
      exact add_lt_add_right
        (lt_nadd_of_pos (VNote.vadd a b n c) z hx hy.tail (repr_pos_of_vadd a b n c)) _
    · rw [nadd_of_eq (by rw [hcmp, (_root_.cmp_eq_eq_iff _ _).2 heq])]
      simp only [repr_vadd, heq]
      exact mul_natCast_add_lt_of_lt hy.tail_lt (pnat_lt_add_left n m)
    · rw [nadd_of_gt (by rw [hcmp, hgt.cmp_eq_gt])]
      simp only [repr_vadd]
      exact mul_natCast_add_lt_of_lead_lt hP hy.tail_lt hgt n.property
termination_by x y => size x + size y
decreasing_by
  all_goals
    simp only [size_vadd]
    omega

/-- The natural sum dominates its left summand. -/
theorem le_nadd_left : ∀ (x y : VNote), NF x → NF y → repr x ≤ repr (nadd x y)
  | 0, _, _, _ => by rw [zero_nadd, repr_zero]; exact zero_le
  | VNote.vadd _ _ _ _, 0, _, _ => by rw [nadd_zero]
  | VNote.vadd a b n c, VNote.vadd f g m z, hx, hy => by
    have hP : IsPrincipal (· + ·) (veblen (repr a) (repr b)) := isPrincipal_add_veblen _ _
    have hM : IsPrincipal (· + ·) (veblen (repr f) (repr g)) := isPrincipal_add_veblen _ _
    have hcmp := lead_cmp_eq_cmp_repr hx hy
    rcases lt_trichotomy (veblen (repr a) (repr b)) (veblen (repr f) (repr g)) with
      hlt | heq | hgt
    · rw [nadd_of_lt (by rw [hcmp, hlt.cmp_eq_lt])]
      exact le_trans (NF.repr_lt_of_lead_lt hx hM hlt).le (lead_le_repr f g m _)
    · rw [nadd_of_eq (by rw [hcmp, (_root_.cmp_eq_eq_iff _ _).2 heq])]
      simp only [repr_vadd]
      exact le_of_lt (mul_natCast_add_lt_of_lt hx.tail_lt (pnat_lt_add_right n m))
    · rw [nadd_of_gt (by rw [hcmp, hgt.cmp_eq_gt])]
      simp only [repr_vadd]
      exact add_le_add_right (le_nadd_left c (VNote.vadd f g m z) hx.tail hy) _
termination_by x y => size x + size y
decreasing_by
  all_goals
    simp only [size_vadd]
    omega

theorem le_nadd_right (x y : VNote) (hx : NF x) (hy : NF y) : repr y ≤ repr (nadd x y) := by
  rw [nadd_comm x y hx hy]
  exact le_nadd_left y x hy hx

/-- **Strict monotonicity of the natural sum in its left argument.**

This is what the reduction lemma's rule-rebuilding step needs.  The case analysis is forced
by the two structures involved: `<` between normal forms has three sources
(`lt_mul_natCast_add_cases`) and `nadd` branches three ways on each argument; of the nine
combinations in the first case only five are reachable. -/
theorem nadd_lt_nadd_left : ∀ (x x' y : VNote), NF x → NF x' → NF y →
    repr x < repr x' → repr (nadd x y) < repr (nadd x' y)
  | _, _, 0, _, _, _, h => by rwa [nadd_zero, nadd_zero]
  | 0, x', VNote.vadd f g m z, _, hx', hy, h => by
    rw [zero_nadd]
    exact lt_nadd_of_pos x' (VNote.vadd f g m z) hx' hy (by simpa using h)
  | VNote.vadd a b n c, 0, VNote.vadd _ _ _ _, _, _, _, h => by
    rw [repr_zero] at h
    exact absurd h not_lt_zero
  | VNote.vadd a b n c, VNote.vadd a' b' n' c', VNote.vadd f g m z, hx, hx', hy, h => by
    have hP : IsPrincipal (· + ·) (veblen (repr a) (repr b)) := isPrincipal_add_veblen _ _
    have hP' : IsPrincipal (· + ·) (veblen (repr a') (repr b')) := isPrincipal_add_veblen _ _
    have hM : IsPrincipal (· + ·) (veblen (repr f) (repr g)) := isPrincipal_add_veblen _ _
    have hcx := lead_cmp_eq_cmp_repr hx hy
    have hcx' := lead_cmp_eq_cmp_repr hx' hy
    have h' : veblen (repr a) (repr b) * ((n : ℕ) : Ordinal) + repr c
        < veblen (repr a') (repr b') * ((n' : ℕ) : Ordinal) + repr c' := by
      rw [← repr_vadd, ← repr_vadd]; exact h
    rcases lt_mul_natCast_add_cases hP hP' hx.tail_lt hx'.tail_lt n.property n'.property h'
      with hPP | ⟨hPP, hrest⟩
    · -- The leading terms differ.  Nine branch combinations, five reachable.
      rcases lt_trichotomy (veblen (repr a) (repr b)) (veblen (repr f) (repr g)) with
        h1 | h1 | h1 <;>
      rcases lt_trichotomy (veblen (repr a') (repr b')) (veblen (repr f) (repr g)) with
        h2 | h2 | h2
      · -- P < M, P' < M
        rw [nadd_of_lt (by rw [hcx, h1.cmp_eq_lt]), nadd_of_lt (by rw [hcx', h2.cmp_eq_lt])]
        simp only [repr_vadd]
        exact add_lt_add_right (nadd_lt_nadd_left (VNote.vadd a b n c)
          (VNote.vadd a' b' n' c') z hx hx' hy.tail h) _
      · -- P < M, P' = M
        rw [nadd_of_lt (by rw [hcx, h1.cmp_eq_lt]),
          nadd_of_eq (by rw [hcx', (_root_.cmp_eq_eq_iff _ _).2 h2])]
        simp only [repr_vadd, h2]
        exact mul_natCast_add_lt_of_lt
          (nadd_lt_of_isPrincipal hx hy.tail hM (NF.repr_lt_of_lead_lt hx hM h1) hy.tail_lt)
          (pnat_lt_add_left n' m)
      · -- P < M, M < P'
        rw [nadd_of_lt (by rw [hcx, h1.cmp_eq_lt]), nadd_of_gt (by rw [hcx', h2.cmp_eq_gt])]
        simp only [repr_vadd]
        exact mul_natCast_add_lt_of_lead_lt hP'
          (nadd_lt_of_isPrincipal hx hy.tail hM (NF.repr_lt_of_lead_lt hx hM h1) hy.tail_lt)
          h2 n'.property
      · exact absurd (h2.trans (h1 ▸ hPP)) (lt_irrefl _)
      · exact absurd (h1.trans h2.symm ▸ hPP) (lt_irrefl _)
      · -- P = M, M < P'
        rw [nadd_of_eq (by rw [hcx, (_root_.cmp_eq_eq_iff _ _).2 h1]),
          nadd_of_gt (by rw [hcx', h2.cmp_eq_gt])]
        simp only [repr_vadd]
        refine mul_natCast_add_lt_of_lead_lt hP' ?_ hPP n'.property
        exact nadd_lt_of_isPrincipal hx.tail hy.tail hP hx.tail_lt (by rw [h1]; exact hy.tail_lt)
      · exact absurd (hPP.trans (h2.trans h1)) (lt_irrefl _)
      · exact absurd (hPP.trans (h2 ▸ h1)) (lt_irrefl _)
      · -- M < P, M < P'
        rw [nadd_of_gt (by rw [hcx, h1.cmp_eq_gt]), nadd_of_gt (by rw [hcx', h2.cmp_eq_gt])]
        simp only [repr_vadd]
        refine mul_natCast_add_lt_of_lead_lt hP' ?_ hPP n'.property
        exact nadd_lt_of_isPrincipal hx.tail hy hP hx.tail_lt
          (NF.repr_lt_of_lead_lt hy hP h1)
    · -- Equal leading terms: both merges branch on the same comparison with the head of `y`.
      rcases lt_trichotomy (veblen (repr a) (repr b)) (veblen (repr f) (repr g)) with
        h1 | h1 | h1
      · rw [nadd_of_lt (by rw [hcx, h1.cmp_eq_lt]),
          nadd_of_lt (by rw [hcx', (hPP ▸ h1 : veblen (repr a') (repr b') < _).cmp_eq_lt])]
        simp only [repr_vadd]
        exact add_lt_add_right (nadd_lt_nadd_left (VNote.vadd a b n c)
          (VNote.vadd a' b' n' c') z hx hx' hy.tail h) _
      · rw [nadd_of_eq (by rw [hcx, (_root_.cmp_eq_eq_iff _ _).2 h1]),
          nadd_of_eq (by rw [hcx', (_root_.cmp_eq_eq_iff _ _).2 (hPP ▸ h1)])]
        simp only [repr_vadd, ← hPP]
        have hcz : repr (nadd c z) < veblen (repr a) (repr b) :=
          nadd_lt_of_isPrincipal hx.tail hy.tail hP hx.tail_lt (by rw [h1]; exact hy.tail_lt)
        rcases hrest with hn | ⟨hn, hc⟩
        · exact mul_natCast_add_lt_of_lt hcz (pnat_add_lt_add_right m hn)
        · have hnn : n = n' := Subtype.ext hn
          subst hnn
          exact add_lt_add_right
            (nadd_lt_nadd_left c c' z hx.tail hx'.tail hy.tail hc) _
      · rw [nadd_of_gt (by rw [hcx, h1.cmp_eq_gt]),
          nadd_of_gt (by rw [hcx', (hPP ▸ h1 : _ < veblen (repr a') (repr b')).cmp_eq_gt])]
        simp only [repr_vadd, ← hPP]
        have hcy : repr (nadd c (VNote.vadd f g m z)) < veblen (repr a) (repr b) :=
          nadd_lt_of_isPrincipal hx.tail hy hP hx.tail_lt (NF.repr_lt_of_lead_lt hy hP h1)
        rcases hrest with hn | ⟨hn, hc⟩
        · exact mul_natCast_add_lt_of_lt hcy hn
        · have hnn : n = n' := Subtype.ext hn
          subst hnn
          exact add_lt_add_right
            (nadd_lt_nadd_left c c' (VNote.vadd f g m z) hx.tail hx'.tail hy hc) _
termination_by x x' y => (size y, size x + size x')
decreasing_by
  all_goals simp_wf
  all_goals (try simp only [size_vadd])
  all_goals omega

/-- Strict monotonicity in the right argument, by commutativity. -/
theorem nadd_lt_nadd_right (x y y' : VNote) (hx : NF x) (hy : NF y) (hy' : NF y')
    (h : repr y < repr y') : repr (nadd x y) < repr (nadd x y') := by
  rw [nadd_comm x y hx hy, nadd_comm x y' hx hy']
  exact nadd_lt_nadd_left y y' x hy hy' hx h

end VNote

/-! ### The natural sum on `Gamma0Note`

Exactly the shapes of `OrdinalAnalysis/Ordinal/NONatSum.lean`; the normal-form hypotheses
are carried by the type, so they disappear from every statement. -/

namespace Gamma0Note

open VNote

/-- Natural (Hessenberg) sum of normal Veblen notations. -/
def nadd (a b : Gamma0Note) : Gamma0Note :=
  ⟨VNote.nadd a.1 b.1, VNote.nf_nadd a.2 b.2⟩

@[simp] theorem nadd_coe (a b : Gamma0Note) : (nadd a b).1 = VNote.nadd a.1 b.1 := rfl

@[simp] theorem val_zero : (0 : Gamma0Note).1 = (0 : VNote) := rfl

@[simp] theorem val_one : (1 : Gamma0Note).1 = (1 : VNote) := rfl

@[simp] theorem repr_nadd (a b : Gamma0Note) :
    repr (nadd a b) = VNote.repr (VNote.nadd a.1 b.1) := rfl

@[simp] theorem nadd_zero (a : Gamma0Note) : nadd a 0 = a := by
  apply Subtype.ext; simp [nadd]

@[simp] theorem zero_nadd (a : Gamma0Note) : nadd 0 a = a := by
  apply Subtype.ext; simp [nadd]

theorem nadd_comm (a b : Gamma0Note) : nadd a b = nadd b a :=
  Subtype.ext (VNote.nadd_comm a.1 b.1 a.2 b.2)

theorem le_nadd_left (a b : Gamma0Note) : a ≤ nadd a b :=
  VNote.le_nadd_left a.1 b.1 a.2 b.2

theorem le_nadd_right (a b : Gamma0Note) : b ≤ nadd a b :=
  VNote.le_nadd_right a.1 b.1 a.2 b.2

theorem nadd_lt_nadd_left {a a' : Gamma0Note} (b : Gamma0Note) (h : a < a') :
    nadd a b < nadd a' b :=
  VNote.nadd_lt_nadd_left a.1 a'.1 b.1 a.2 a'.2 b.2 h

theorem nadd_lt_nadd_right {b b' : Gamma0Note} (a : Gamma0Note) (h : b < b') :
    nadd a b < nadd a b' :=
  VNote.nadd_lt_nadd_right a.1 b.1 b'.1 a.2 b.2 b'.2 h

theorem nadd_le_nadd_left {a a' : Gamma0Note} (b : Gamma0Note) (h : a ≤ a') :
    nadd a b ≤ nadd a' b := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (nadd_lt_nadd_left b h)
  · exact le_rfl

theorem nadd_le_nadd_right {b b' : Gamma0Note} (a : Gamma0Note) (h : b ≤ b') :
    nadd a b ≤ nadd a b' := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (nadd_lt_nadd_right a h)
  · exact le_rfl

/-- A nonzero summand contributes strictly. -/
theorem lt_nadd_of_pos {a : Gamma0Note} (b : Gamma0Note) (h : 0 < a) : b < nadd a b :=
  VNote.lt_nadd_of_pos a.1 b.1 a.2 b.2 h

/-- **Additive indecomposability of every Veblen value for the natural sum.** -/
theorem nadd_lt_veblenNote {a b x y : Gamma0Note} (hx : x < veblenNote a b)
    (hy : y < veblenNote a b) : nadd x y < veblenNote a b := by
  show VNote.repr (VNote.nadd x.1 y.1) < VNote.repr (veblenNote a b).1
  have hx' : VNote.repr x.1 < veblen (repr a) (repr b) := by
    have := hx; rw [lt_def, repr_veblenNote] at this; exact this
  have hy' : VNote.repr y.1 < veblen (repr a) (repr b) := by
    have := hy; rw [lt_def, repr_veblenNote] at this; exact this
  have := VNote.nadd_lt_veblen x.2 y.2 hx' hy'
  show VNote.repr (VNote.nadd x.1 y.1) < repr (veblenNote a b)
  rw [repr_veblenNote]
  exact this

/-- **Additive indecomposability of `ω ^ a` for the natural sum.**

This is the one lemma cut elimination truly needs: any finite amount of natural-sum slack
below `ω ^ a` stays below `ω ^ a`. -/
theorem nadd_lt_omegaPow {a x y : Gamma0Note} (hx : x < omegaPow a) (hy : y < omegaPow a) :
    nadd x y < omegaPow a :=
  nadd_lt_veblenNote hx hy

end Gamma0Note

end OrdinalAnalysis
