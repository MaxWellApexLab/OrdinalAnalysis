/-
  Comparison of Veblen notations.

  The core of the file is `VNote.cmp_eq_cmp_repr`: on normal forms, the syntactic
  comparison `VNote.cmp` computes the comparison of the denoted ordinals.  Everything else
  (`cmp_compares`, `eq_of_cmp_eq`, `repr_inj`, `repr_lt_iff`) is a corollary.

  The shape of `cmp` is forced by `Ordinal.cmp_veblen`: to compare `φ_a(b)` with `φ_a'(b')`
  one compares `a` with `a'` first, and then, in the two unequal cases, one argument against
  the *whole* Veblen value on the other side.  That last recursion is on a freshly built
  term `vadd a' b' 1 0`, which is why `cmp` cannot be structurally recursive and needs the
  measure `size x + size y`.
-/
import OrdinalAnalysis.Ordinal.Veblen.Basic

set_option autoImplicit false

namespace OrdinalAnalysis

open Ordinal

namespace VNote

/-- Comparison of Veblen notations.

`φ_a(b) · n + c` is compared with `φ_a'(b') · n' + c'` by comparing the leading Veblen terms
first, then the multiplicities, then the tails.  The leading terms are compared by the
three-case Veblen rule (`Ordinal.cmp_veblen`):

* if `a = a'`, compare `b` with `b'`;
* if `a < a'`, compare `b` with `φ_a'(b')`;
* if `a' < a`, compare `φ_a(b)` with `b'`.

This is the order of the Coq `hydra-battles` type `T2`.  It is correct only on normal
forms; see `VNote.cmp_eq_cmp_repr`. -/
def cmp : VNote → VNote → Ordering
  | 0, 0 => Ordering.eq
  | 0, vadd _ _ _ _ => Ordering.lt
  | vadd _ _ _ _, 0 => Ordering.gt
  | vadd a b n c, vadd a' b' n' c' =>
    (match cmp a a' with
      | Ordering.eq => cmp b b'
      | Ordering.lt => cmp b (vadd a' b' 1 0)
      | Ordering.gt => cmp (vadd a b 1 0) b').then
      ((_root_.cmp (n : ℕ) (n' : ℕ)).then (cmp c c'))
termination_by x y => size x + size y
decreasing_by
  all_goals
    simp only [size_vadd, size_zero]
    omega

-- Note: `cmp` is defined by well-founded recursion, so its defining equations are *not*
-- `rfl` and `rw [cmp]` does not fire; one has to go through `cmp.eq_def`.

@[simp]
theorem cmp_zero_zero : cmp 0 0 = Ordering.eq := by
  rw [cmp.eq_def]

@[simp]
theorem cmp_zero_vadd (a b : VNote) (n : ℕ+) (c : VNote) :
    cmp 0 (vadd a b n c) = Ordering.lt := by
  rw [cmp.eq_def]

@[simp]
theorem cmp_vadd_zero (a b : VNote) (n : ℕ+) (c : VNote) :
    cmp (vadd a b n c) 0 = Ordering.gt := by
  rw [cmp.eq_def]

theorem cmp_vadd_vadd (a b : VNote) (n : ℕ+) (c a' b' : VNote) (n' : ℕ+) (c' : VNote) :
    cmp (vadd a b n c) (vadd a' b' n' c') =
      (match cmp a a' with
        | Ordering.eq => cmp b b'
        | Ordering.lt => cmp b (vadd a' b' 1 0)
        | Ordering.gt => cmp (vadd a b 1 0) b').then
        ((_root_.cmp (n : ℕ) (n' : ℕ)).then (cmp c c')) := by
  rw [cmp.eq_def]

/-- **Correctness of `cmp`.**  On normal forms, the syntactic comparison of notations agrees
with the comparison of the ordinals they denote. -/
theorem cmp_eq_cmp_repr : ∀ (x y : VNote), NF x → NF y → cmp x y = _root_.cmp (repr x) (repr y)
  | 0, 0, _, _ => by simp
  | 0, vadd a' b' n' c', _, _ => by
    rw [cmp_zero_vadd, repr_zero]
    exact ((repr_pos_of_vadd a' b' n' c').cmp_eq_lt).symm
  | vadd a b n c, 0, _, _ => by
    rw [cmp_vadd_zero, repr_zero]
    exact ((repr_pos_of_vadd a b n c).cmp_eq_gt).symm
  | vadd a b n c, vadd a' b' n' c', hx, hy => by
    have hnfx : NF (VNote.vadd a b 1 0) := NF.vadd_zero 1 hx.fst hx.snd hx.snd_lt
    have hnfy : NF (VNote.vadd a' b' 1 0) := NF.vadd_zero 1 hy.fst hy.snd hy.snd_lt
    have hA : _root_.cmp (repr a) (repr a') = cmp a a' :=
      (cmp_eq_cmp_repr a a' hx.fst hy.fst).symm
    have hmul : _root_.cmp (repr (VNote.vadd a b n c)) (repr (VNote.vadd a' b' n' c')) =
        (_root_.cmp (veblen (repr a) (repr b)) (veblen (repr a') (repr b'))).then
          ((_root_.cmp (n : ℕ) (n' : ℕ)).then (_root_.cmp (repr c) (repr c'))) := by
      rw [repr_vadd, repr_vadd]
      exact cmp_mul_natCast_add (isPrincipal_add_veblen _ _) (isPrincipal_add_veblen _ _)
        hx.tail_lt hy.tail_lt n.property n'.property
    rw [cmp_vadd_vadd, cmp_eq_cmp_repr c c' hx.tail hy.tail, hmul]
    congr 1
    rw [cmp_veblen, hA]
    cases cmp a a' with
    | eq => exact cmp_eq_cmp_repr b b' hx.snd hy.snd
    | lt =>
      have h := cmp_eq_cmp_repr b (VNote.vadd a' b' 1 0) hx.snd hnfy
      rwa [repr_vadd_one_zero] at h
    | gt =>
      have h := cmp_eq_cmp_repr (VNote.vadd a b 1 0) b' hnfx hy.snd
      rwa [repr_vadd_one_zero] at h
termination_by x y => size x + size y
decreasing_by
  all_goals
    simp only [size_vadd, size_zero]
    omega

/-- `cmp` compares the denoted ordinals, in the sense of `Ordering.Compares`. -/
theorem cmp_compares (x y : VNote) [hx : NF x] [hy : NF y] :
    (cmp x y).Compares (repr x) (repr y) := by
  rw [cmp_eq_cmp_repr x y hx hy]
  exact _root_.cmp_compares _ _

/-! ### Injectivity of `repr` on normal forms -/

/-- **`repr` is injective on normal forms.**

The proof is the uniqueness of the Veblen normal form: `mul_natCast_add_lt_of_lead_lt` and
`mul_natCast_add_lt_of_lt` force the leading terms and the multiplicities to agree, then
`veblen_eq_veblen_of_lt` (which is where the "not a fixed point" side condition is used)
splits the leading term into its two arguments. -/
theorem repr_inj : ∀ {x y : VNote}, NF x → NF y → repr x = repr y → x = y
  | 0, 0, _, _, _ => rfl
  | 0, VNote.vadd a' b' n' c', _, _, h => by
    rw [repr_zero] at h
    exact absurd h.symm (repr_pos_of_vadd a' b' n' c').ne'
  | VNote.vadd a b n c, 0, _, _, h => by
    rw [repr_zero] at h
    exact absurd h (repr_pos_of_vadd a b n c).ne'
  | VNote.vadd a b n c, VNote.vadd a' b' n' c', hx, hy, h => by
    rw [repr_vadd, repr_vadd] at h
    have hlead : veblen (repr a) (repr b) = veblen (repr a') (repr b') := by
      rcases lt_trichotomy (veblen (repr a) (repr b)) (veblen (repr a') (repr b')) with
        hlt | heq | hlt
      · exact absurd h (mul_natCast_add_lt_of_lead_lt (isPrincipal_add_veblen _ _)
          hx.tail_lt hlt n'.property).ne
      · exact heq
      · exact absurd h.symm (mul_natCast_add_lt_of_lead_lt (isPrincipal_add_veblen _ _)
          hy.tail_lt hlt n.property).ne
    obtain ⟨hfst, hsnd⟩ := veblen_eq_veblen_of_lt hlead hx.snd_lt hy.snd_lt
    have hc : repr c < veblen (repr a') (repr b') := hlead ▸ hx.tail_lt
    have hc' : repr c' < veblen (repr a') (repr b') := hy.tail_lt
    rw [hlead] at h
    have hn : (n : ℕ) = (n' : ℕ) := by
      rcases lt_trichotomy (n : ℕ) (n' : ℕ) with hlt | heq | hlt
      · exact absurd h (mul_natCast_add_lt_of_lt hc hlt).ne
      · exact heq
      · exact absurd h.symm (mul_natCast_add_lt_of_lt hc' hlt).ne
    rw [hn] at h
    have htail : repr c = repr c' := by
      exact add_left_cancel h
    have e1 : a = a' := repr_inj hx.fst hy.fst hfst
    have e2 : b = b' := repr_inj hx.snd hy.snd hsnd
    have e3 : c = c' := repr_inj hx.tail hy.tail htail
    have e4 : n = n' := Subtype.ext hn
    rw [e1, e2, e3, e4]

/-- The `Iff` form of `repr_inj`.  (`Gamma0Note.repr_injective` is the genuine
`Function.Injective` statement, once the normality hypothesis is packed into the type.) -/
theorem repr_eq_iff {x y : VNote} (hx : NF x) (hy : NF y) : repr x = repr y ↔ x = y :=
  ⟨repr_inj hx hy, fun h => by rw [h]⟩

theorem eq_of_cmp_eq {x y : VNote} (hx : NF x) (hy : NF y) (h : cmp x y = Ordering.eq) :
    x = y := by
  rw [cmp_eq_cmp_repr x y hx hy] at h
  exact repr_inj hx hy ((cmp_eq_eq_iff _ _).1 h)

theorem cmp_eq_eq_of_eq {x y : VNote} (hx : NF x) (hy : NF y) (h : x = y) :
    cmp x y = Ordering.eq := by
  subst h
  rw [cmp_eq_cmp_repr x x hx hx, cmp_self_eq_eq]

theorem repr_lt_iff {x y : VNote} (hx : NF x) (hy : NF y) :
    repr x < repr y ↔ cmp x y = Ordering.lt := by
  rw [cmp_eq_cmp_repr x y hx hy, cmp_eq_lt_iff]

theorem repr_le_iff {x y : VNote} (hx : NF x) (hy : NF y) :
    repr x ≤ repr y ↔ cmp x y ≠ Ordering.gt := by
  rw [cmp_eq_cmp_repr x y hx hy, ne_eq, cmp_eq_gt_iff, not_lt]

end VNote

end OrdinalAnalysis
