/-
  Associativity of the natural sum of Veblen notations.

  This is the `VNote` port of `OrdinalAnalysis/Ordinal/NaturalSumAssoc.lean`, which proves the
  same statement for the `ONote` natural sum.  Together with `VNote.nadd_comm` and the
  monotonicity lemmas of `Ordinal/Veblen/NaturalSum.lean` it completes the algebraic interface
  that `OrdinalNotation` asks of a notation system.

  The shape of the proof is the one of the `ONote` version and is forced by the definition of
  `nadd`: the merge of two normal forms branches three ways on the comparison of the leading
  terms, so associativity for three summands branches on two such comparisons, and in the case
  where the outer two merges disagree (`gt.lt`) a third comparison has to be resolved as well —
  eleven leaf cases in all.

  Two things replace the `ONote` machinery.

  * `ONote.nadd` compares exponents (`cmp e₁ e₂`); `VNote.nadd` compares whole leading Veblen
    terms (`cmp (vadd a b 1 0) (vadd a' b' 1 0)`).  Transitivity of that comparison is not
    available syntactically, so every comparison is pushed through `cmp_eq_cmp_repr` to the
    ordinals `φ_a(b)` (`lead_cmp` below) and the case analysis is a plain `lt_trichotomy` on
    those; transitivity is then transitivity of `<` on `Ordinal`.
  * `cmp e₁ e₂ = Ordering.eq` gives `e₁ = e₂` by `ONote.cmp_compares`; here the corresponding
    step is `veblen_eq_veblen_of_lt` followed by `repr_inj`, exactly as in `VNote.nadd_comm`.
    This is where the normal-form side condition "`b` is not a fixed point of `φ_a`" is used,
    and it is why `nadd_assoc`, like `nadd_comm`, needs `NF` hypotheses.

  Each of the eleven cases is a separate `private` lemma taking the relevant instance of the
  induction hypothesis as an argument.  The case lemmas are purely syntactic — they consume
  only the three `cmp … = Ordering.…` equations, no `NF` — which keeps every declaration small
  and keeps the well-founded recursion in `nadd_assoc_aux` to a dispatch.
-/
import OrdinalAnalysis.Ordinal.Veblen.NaturalSum

set_option autoImplicit false

namespace OrdinalAnalysis

open Ordinal

namespace VNote

/-! ### The leading comparison

`nadd` branches on `cmp (vadd a b 1 0) (vadd a' b' 1 0)`.  Only the *leading terms* have to be
normal for that comparison to be meaningful, so these three lemmas ask for `NF (vadd a b 1 0)`
rather than for normality of the notations the leading terms came from; the intermediate
notations built by the merge then need no normal-form proof at all. -/

/-- The leading term of a normal form is a normal form. -/
private theorem nf_lead {a b c : VNote} {n : ℕ+} (h : NF (VNote.vadd a b n c)) :
    NF (VNote.vadd a b 1 0) :=
  NF.vadd_zero 1 h.fst h.snd h.snd_lt

/-- Comparing two normal leading terms computes the comparison of the Veblen values. -/
private theorem lead_cmp {a b a' b' : VNote}
    (hx : NF (VNote.vadd a b 1 0)) (hy : NF (VNote.vadd a' b' 1 0)) :
    VNote.cmp (VNote.vadd a b 1 0) (VNote.vadd a' b' 1 0)
      = _root_.cmp (veblen (repr a) (repr b)) (veblen (repr a') (repr b')) := by
  have h := cmp_eq_cmp_repr (VNote.vadd a b 1 0) (VNote.vadd a' b' 1 0) hx hy
  rwa [repr_vadd_one_zero, repr_vadd_one_zero] at h

private theorem lead_lt {a b a' b' : VNote}
    (hx : NF (VNote.vadd a b 1 0)) (hy : NF (VNote.vadd a' b' 1 0))
    (h : veblen (repr a) (repr b) < veblen (repr a') (repr b')) :
    VNote.cmp (VNote.vadd a b 1 0) (VNote.vadd a' b' 1 0) = Ordering.lt := by
  rw [lead_cmp hx hy, h.cmp_eq_lt]

private theorem lead_gt {a b a' b' : VNote}
    (hx : NF (VNote.vadd a b 1 0)) (hy : NF (VNote.vadd a' b' 1 0))
    (h : veblen (repr a') (repr b') < veblen (repr a) (repr b)) :
    VNote.cmp (VNote.vadd a b 1 0) (VNote.vadd a' b' 1 0) = Ordering.gt := by
  rw [lead_cmp hx hy, h.cmp_eq_gt]

/-! ### The eleven cases

Naming: `assoc_r₁₂_r₂₃` where `r_ij` is the comparison of the `i`-th and `j`-th leading terms.
When two leading terms are equal the corresponding notations have already been identified by
the caller, so the two heads are literally the same pair of notations.  The `gt.lt` case is
the one where the two outer merges disagree; it splits again on the first-versus-third
comparison. -/

/-- `φ₁ < φ₂ < φ₃`. -/
private theorem assoc_lt_lt {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : VNote} {n₁ n₂ n₃ : ℕ+}
    (e₁₂ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₂ b₂ 1 0) = Ordering.lt)
    (e₂₃ : VNote.cmp (VNote.vadd a₂ b₂ 1 0) (VNote.vadd a₃ b₃ 1 0) = Ordering.lt)
    (e₁₃ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₃ b₃ 1 0) = Ordering.lt)
    (ih : nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₂ b₂ n₂ c₂)) c₃
      = nadd (VNote.vadd a₁ b₁ n₁ c₁) (nadd (VNote.vadd a₂ b₂ n₂ c₂) c₃)) :
    nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₂ b₂ n₂ c₂)) (VNote.vadd a₃ b₃ n₃ c₃)
      = nadd (VNote.vadd a₁ b₁ n₁ c₁)
          (nadd (VNote.vadd a₂ b₂ n₂ c₂) (VNote.vadd a₃ b₃ n₃ c₃)) := by
  simp only [nadd_of_lt e₁₂, nadd_of_lt e₂₃, nadd_of_lt e₁₃]
  exact congrArg (VNote.vadd a₃ b₃ n₃) (by simpa only [nadd_of_lt e₁₂] using ih)

/-- `φ₁ < φ₂ = φ₃`. -/
private theorem assoc_lt_eq {a₁ b₁ c₁ a₂ b₂ c₂ c₃ : VNote} {n₁ n₂ n₃ : ℕ+}
    (e₁₂ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₂ b₂ 1 0) = Ordering.lt)
    (e₂₂ : VNote.cmp (VNote.vadd a₂ b₂ 1 0) (VNote.vadd a₂ b₂ 1 0) = Ordering.eq)
    (ih : nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) c₂) c₃
      = nadd (VNote.vadd a₁ b₁ n₁ c₁) (nadd c₂ c₃)) :
    nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₂ b₂ n₂ c₂)) (VNote.vadd a₂ b₂ n₃ c₃)
      = nadd (VNote.vadd a₁ b₁ n₁ c₁)
          (nadd (VNote.vadd a₂ b₂ n₂ c₂) (VNote.vadd a₂ b₂ n₃ c₃)) := by
  simp only [nadd_of_lt e₁₂, nadd_of_eq e₂₂]
  exact congrArg (VNote.vadd a₂ b₂ (n₂ + n₃)) ih

/-- `φ₁ < φ₂`, `φ₃ < φ₂`. -/
private theorem assoc_lt_gt {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : VNote} {n₁ n₂ n₃ : ℕ+}
    (e₁₂ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₂ b₂ 1 0) = Ordering.lt)
    (e₂₃ : VNote.cmp (VNote.vadd a₂ b₂ 1 0) (VNote.vadd a₃ b₃ 1 0) = Ordering.gt)
    (ih : nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) c₂) (VNote.vadd a₃ b₃ n₃ c₃)
      = nadd (VNote.vadd a₁ b₁ n₁ c₁) (nadd c₂ (VNote.vadd a₃ b₃ n₃ c₃))) :
    nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₂ b₂ n₂ c₂)) (VNote.vadd a₃ b₃ n₃ c₃)
      = nadd (VNote.vadd a₁ b₁ n₁ c₁)
          (nadd (VNote.vadd a₂ b₂ n₂ c₂) (VNote.vadd a₃ b₃ n₃ c₃)) := by
  simp only [nadd_of_lt e₁₂, nadd_of_gt e₂₃]
  exact congrArg (VNote.vadd a₂ b₂ n₂) ih

/-- `φ₁ = φ₂ < φ₃`. -/
private theorem assoc_eq_lt {a₁ b₁ c₁ c₂ a₃ b₃ c₃ : VNote} {n₁ n₂ n₃ : ℕ+}
    (e₁₁ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₁ b₁ 1 0) = Ordering.eq)
    (e₁₃ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₃ b₃ 1 0) = Ordering.lt)
    (ih : nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₁ b₁ n₂ c₂)) c₃
      = nadd (VNote.vadd a₁ b₁ n₁ c₁) (nadd (VNote.vadd a₁ b₁ n₂ c₂) c₃)) :
    nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₁ b₁ n₂ c₂)) (VNote.vadd a₃ b₃ n₃ c₃)
      = nadd (VNote.vadd a₁ b₁ n₁ c₁)
          (nadd (VNote.vadd a₁ b₁ n₂ c₂) (VNote.vadd a₃ b₃ n₃ c₃)) := by
  simp only [nadd_of_eq e₁₁, nadd_of_lt e₁₃]
  exact congrArg (VNote.vadd a₃ b₃ n₃) (by simpa only [nadd_of_eq e₁₁] using ih)

/-- `φ₁ = φ₂ = φ₃`: the only case where the multiplicities move, and the associativity used
is that of `ℕ+`. -/
private theorem assoc_eq_eq {a₁ b₁ c₁ c₂ c₃ : VNote} {n₁ n₂ n₃ : ℕ+}
    (e₁₁ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₁ b₁ 1 0) = Ordering.eq)
    (ih : nadd (nadd c₁ c₂) c₃ = nadd c₁ (nadd c₂ c₃)) :
    nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₁ b₁ n₂ c₂)) (VNote.vadd a₁ b₁ n₃ c₃)
      = nadd (VNote.vadd a₁ b₁ n₁ c₁)
          (nadd (VNote.vadd a₁ b₁ n₂ c₂) (VNote.vadd a₁ b₁ n₃ c₃)) := by
  simp only [nadd_of_eq e₁₁]
  rw [add_assoc, ih]

/-- `φ₁ = φ₂`, `φ₃ < φ₁`. -/
private theorem assoc_eq_gt {a₁ b₁ c₁ c₂ a₃ b₃ c₃ : VNote} {n₁ n₂ n₃ : ℕ+}
    (e₁₁ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₁ b₁ 1 0) = Ordering.eq)
    (e₁₃ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₃ b₃ 1 0) = Ordering.gt)
    (ih : nadd (nadd c₁ c₂) (VNote.vadd a₃ b₃ n₃ c₃)
      = nadd c₁ (nadd c₂ (VNote.vadd a₃ b₃ n₃ c₃))) :
    nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₁ b₁ n₂ c₂)) (VNote.vadd a₃ b₃ n₃ c₃)
      = nadd (VNote.vadd a₁ b₁ n₁ c₁)
          (nadd (VNote.vadd a₁ b₁ n₂ c₂) (VNote.vadd a₃ b₃ n₃ c₃)) := by
  simp only [nadd_of_eq e₁₁, nadd_of_gt e₁₃]
  exact congrArg (VNote.vadd a₁ b₁ (n₁ + n₂)) ih

/-- `φ₂ < φ₁`, `φ₂ < φ₃`, `φ₁ < φ₃`. -/
private theorem assoc_gt_lt_lt {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : VNote} {n₁ n₂ n₃ : ℕ+}
    (e₁₂ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₂ b₂ 1 0) = Ordering.gt)
    (e₂₃ : VNote.cmp (VNote.vadd a₂ b₂ 1 0) (VNote.vadd a₃ b₃ 1 0) = Ordering.lt)
    (e₁₃ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₃ b₃ 1 0) = Ordering.lt)
    (ih : nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₂ b₂ n₂ c₂)) c₃
      = nadd (VNote.vadd a₁ b₁ n₁ c₁) (nadd (VNote.vadd a₂ b₂ n₂ c₂) c₃)) :
    nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₂ b₂ n₂ c₂)) (VNote.vadd a₃ b₃ n₃ c₃)
      = nadd (VNote.vadd a₁ b₁ n₁ c₁)
          (nadd (VNote.vadd a₂ b₂ n₂ c₂) (VNote.vadd a₃ b₃ n₃ c₃)) := by
  simp only [nadd_of_gt e₁₂, nadd_of_lt e₂₃, nadd_of_lt e₁₃]
  exact congrArg (VNote.vadd a₃ b₃ n₃) (by simpa only [nadd_of_gt e₁₂] using ih)

/-- `φ₂ < φ₁ = φ₃`, `φ₂ < φ₃`. -/
private theorem assoc_gt_lt_eq {a₁ b₁ c₁ a₂ b₂ c₂ c₃ : VNote} {n₁ n₂ n₃ : ℕ+}
    (e₁₂ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₂ b₂ 1 0) = Ordering.gt)
    (e₂₁ : VNote.cmp (VNote.vadd a₂ b₂ 1 0) (VNote.vadd a₁ b₁ 1 0) = Ordering.lt)
    (e₁₁ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₁ b₁ 1 0) = Ordering.eq)
    (ih : nadd (nadd c₁ (VNote.vadd a₂ b₂ n₂ c₂)) c₃
      = nadd c₁ (nadd (VNote.vadd a₂ b₂ n₂ c₂) c₃)) :
    nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₂ b₂ n₂ c₂)) (VNote.vadd a₁ b₁ n₃ c₃)
      = nadd (VNote.vadd a₁ b₁ n₁ c₁)
          (nadd (VNote.vadd a₂ b₂ n₂ c₂) (VNote.vadd a₁ b₁ n₃ c₃)) := by
  simp only [nadd_of_gt e₁₂, nadd_of_lt e₂₁, nadd_of_eq e₁₁]
  exact congrArg (VNote.vadd a₁ b₁ (n₁ + n₃)) ih

/-- `φ₂ < φ₁`, `φ₂ < φ₃`, `φ₃ < φ₁`. -/
private theorem assoc_gt_lt_gt {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : VNote} {n₁ n₂ n₃ : ℕ+}
    (e₁₂ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₂ b₂ 1 0) = Ordering.gt)
    (e₂₃ : VNote.cmp (VNote.vadd a₂ b₂ 1 0) (VNote.vadd a₃ b₃ 1 0) = Ordering.lt)
    (e₁₃ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₃ b₃ 1 0) = Ordering.gt)
    (ih : nadd (nadd c₁ (VNote.vadd a₂ b₂ n₂ c₂)) (VNote.vadd a₃ b₃ n₃ c₃)
      = nadd c₁ (nadd (VNote.vadd a₂ b₂ n₂ c₂) (VNote.vadd a₃ b₃ n₃ c₃))) :
    nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₂ b₂ n₂ c₂)) (VNote.vadd a₃ b₃ n₃ c₃)
      = nadd (VNote.vadd a₁ b₁ n₁ c₁)
          (nadd (VNote.vadd a₂ b₂ n₂ c₂) (VNote.vadd a₃ b₃ n₃ c₃)) := by
  simp only [nadd_of_gt e₁₂, nadd_of_lt e₂₃, nadd_of_gt e₁₃]
  exact congrArg (VNote.vadd a₁ b₁ n₁) (by simpa only [nadd_of_lt e₂₃] using ih)

/-- `φ₂ = φ₃ < φ₁`. -/
private theorem assoc_gt_eq {a₁ b₁ c₁ a₂ b₂ c₂ c₃ : VNote} {n₁ n₂ n₃ : ℕ+}
    (e₁₂ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₂ b₂ 1 0) = Ordering.gt)
    (e₂₂ : VNote.cmp (VNote.vadd a₂ b₂ 1 0) (VNote.vadd a₂ b₂ 1 0) = Ordering.eq)
    (ih : nadd (nadd c₁ (VNote.vadd a₂ b₂ n₂ c₂)) (VNote.vadd a₂ b₂ n₃ c₃)
      = nadd c₁ (nadd (VNote.vadd a₂ b₂ n₂ c₂) (VNote.vadd a₂ b₂ n₃ c₃))) :
    nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₂ b₂ n₂ c₂)) (VNote.vadd a₂ b₂ n₃ c₃)
      = nadd (VNote.vadd a₁ b₁ n₁ c₁)
          (nadd (VNote.vadd a₂ b₂ n₂ c₂) (VNote.vadd a₂ b₂ n₃ c₃)) := by
  simp only [nadd_of_gt e₁₂, nadd_of_eq e₂₂]
  exact congrArg (VNote.vadd a₁ b₁ n₁) (by simpa only [nadd_of_eq e₂₂] using ih)

/-- `φ₃ < φ₂ < φ₁`. -/
private theorem assoc_gt_gt {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : VNote} {n₁ n₂ n₃ : ℕ+}
    (e₁₂ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₂ b₂ 1 0) = Ordering.gt)
    (e₂₃ : VNote.cmp (VNote.vadd a₂ b₂ 1 0) (VNote.vadd a₃ b₃ 1 0) = Ordering.gt)
    (e₁₃ : VNote.cmp (VNote.vadd a₁ b₁ 1 0) (VNote.vadd a₃ b₃ 1 0) = Ordering.gt)
    (ih : nadd (nadd c₁ (VNote.vadd a₂ b₂ n₂ c₂)) (VNote.vadd a₃ b₃ n₃ c₃)
      = nadd c₁ (nadd (VNote.vadd a₂ b₂ n₂ c₂) (VNote.vadd a₃ b₃ n₃ c₃))) :
    nadd (nadd (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₂ b₂ n₂ c₂)) (VNote.vadd a₃ b₃ n₃ c₃)
      = nadd (VNote.vadd a₁ b₁ n₁ c₁)
          (nadd (VNote.vadd a₂ b₂ n₂ c₂) (VNote.vadd a₃ b₃ n₃ c₃)) := by
  simp only [nadd_of_gt e₁₂, nadd_of_gt e₂₃, nadd_of_gt e₁₃]
  exact congrArg (VNote.vadd a₁ b₁ n₁) (by simpa only [nadd_of_gt e₂₃] using ih)

/-! ### Associativity -/

/-- The recursion behind `VNote.nadd_assoc`.  Two `lt_trichotomy`s on the leading Veblen
values, a third one in the case where the two outer merges disagree, and a call to the
matching case lemma. -/
private theorem nadd_assoc_aux : ∀ (x y z : VNote), NF x → NF y → NF z →
    nadd (nadd x y) z = nadd x (nadd y z)
  | 0, _, _, _, _, _ => by simp
  | VNote.vadd _ _ _ _, 0, _, _, _, _ => by simp
  | VNote.vadd _ _ _ _, VNote.vadd _ _ _ _, 0, _, _, _ => by simp
  | VNote.vadd a₁ b₁ n₁ c₁, VNote.vadd a₂ b₂ n₂ c₂, VNote.vadd a₃ b₃ n₃ c₃, h₁, h₂, h₃ => by
    have l₁ : NF (VNote.vadd a₁ b₁ 1 0) := nf_lead h₁
    have l₂ : NF (VNote.vadd a₂ b₂ 1 0) := nf_lead h₂
    have l₃ : NF (VNote.vadd a₃ b₃ 1 0) := nf_lead h₃
    rcases lt_trichotomy (veblen (repr a₁) (repr b₁)) (veblen (repr a₂) (repr b₂)) with
      h₁₂ | h₁₂ | h₁₂
    · -- `φ₁ < φ₂`
      rcases lt_trichotomy (veblen (repr a₂) (repr b₂)) (veblen (repr a₃) (repr b₃)) with
        h₂₃ | h₂₃ | h₂₃
      · exact assoc_lt_lt (lead_lt l₁ l₂ h₁₂) (lead_lt l₂ l₃ h₂₃)
          (lead_lt l₁ l₃ (h₁₂.trans h₂₃))
          (nadd_assoc_aux (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₂ b₂ n₂ c₂) c₃ h₁ h₂ h₃.tail)
      · obtain ⟨ha, hb⟩ := veblen_eq_veblen_of_lt h₂₃ h₂.snd_lt h₃.snd_lt
        have ea : a₂ = a₃ := repr_inj h₂.fst h₃.fst ha
        have eb : b₂ = b₃ := repr_inj h₂.snd h₃.snd hb
        subst ea; subst eb
        exact assoc_lt_eq (lead_lt l₁ l₂ h₁₂) (cmp_eq_eq_of_eq l₂ l₂ rfl)
          (nadd_assoc_aux (VNote.vadd a₁ b₁ n₁ c₁) c₂ c₃ h₁ h₂.tail h₃.tail)
      · exact assoc_lt_gt (lead_lt l₁ l₂ h₁₂) (lead_gt l₂ l₃ h₂₃)
          (nadd_assoc_aux (VNote.vadd a₁ b₁ n₁ c₁) c₂ (VNote.vadd a₃ b₃ n₃ c₃)
            h₁ h₂.tail h₃)
    · -- `φ₁ = φ₂`
      obtain ⟨ha, hb⟩ := veblen_eq_veblen_of_lt h₁₂ h₁.snd_lt h₂.snd_lt
      have ea : a₁ = a₂ := repr_inj h₁.fst h₂.fst ha
      have eb : b₁ = b₂ := repr_inj h₁.snd h₂.snd hb
      subst ea; subst eb
      rcases lt_trichotomy (veblen (repr a₁) (repr b₁)) (veblen (repr a₃) (repr b₃)) with
        h₁₃ | h₁₃ | h₁₃
      · exact assoc_eq_lt (cmp_eq_eq_of_eq l₁ l₁ rfl) (lead_lt l₁ l₃ h₁₃)
          (nadd_assoc_aux (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₁ b₁ n₂ c₂) c₃ h₁ h₂ h₃.tail)
      · obtain ⟨ha₃, hb₃⟩ := veblen_eq_veblen_of_lt h₁₃ h₁.snd_lt h₃.snd_lt
        have ea₃ : a₁ = a₃ := repr_inj h₁.fst h₃.fst ha₃
        have eb₃ : b₁ = b₃ := repr_inj h₁.snd h₃.snd hb₃
        subst ea₃; subst eb₃
        exact assoc_eq_eq (cmp_eq_eq_of_eq l₁ l₁ rfl)
          (nadd_assoc_aux c₁ c₂ c₃ h₁.tail h₂.tail h₃.tail)
      · exact assoc_eq_gt (cmp_eq_eq_of_eq l₁ l₁ rfl) (lead_gt l₁ l₃ h₁₃)
          (nadd_assoc_aux c₁ c₂ (VNote.vadd a₃ b₃ n₃ c₃) h₁.tail h₂.tail h₃)
    · -- `φ₂ < φ₁`
      rcases lt_trichotomy (veblen (repr a₂) (repr b₂)) (veblen (repr a₃) (repr b₃)) with
        h₂₃ | h₂₃ | h₂₃
      · rcases lt_trichotomy (veblen (repr a₁) (repr b₁)) (veblen (repr a₃) (repr b₃)) with
          h₁₃ | h₁₃ | h₁₃
        · exact assoc_gt_lt_lt (lead_gt l₁ l₂ h₁₂) (lead_lt l₂ l₃ h₂₃) (lead_lt l₁ l₃ h₁₃)
            (nadd_assoc_aux (VNote.vadd a₁ b₁ n₁ c₁) (VNote.vadd a₂ b₂ n₂ c₂) c₃
              h₁ h₂ h₃.tail)
        · obtain ⟨ha₃, hb₃⟩ := veblen_eq_veblen_of_lt h₁₃ h₁.snd_lt h₃.snd_lt
          have ea₃ : a₁ = a₃ := repr_inj h₁.fst h₃.fst ha₃
          have eb₃ : b₁ = b₃ := repr_inj h₁.snd h₃.snd hb₃
          subst ea₃; subst eb₃
          exact assoc_gt_lt_eq (lead_gt l₁ l₂ h₁₂) (lead_lt l₂ l₁ h₂₃)
            (cmp_eq_eq_of_eq l₁ l₁ rfl)
            (nadd_assoc_aux c₁ (VNote.vadd a₂ b₂ n₂ c₂) c₃ h₁.tail h₂ h₃.tail)
        · exact assoc_gt_lt_gt (lead_gt l₁ l₂ h₁₂) (lead_lt l₂ l₃ h₂₃) (lead_gt l₁ l₃ h₁₃)
            (nadd_assoc_aux c₁ (VNote.vadd a₂ b₂ n₂ c₂) (VNote.vadd a₃ b₃ n₃ c₃)
              h₁.tail h₂ h₃)
      · obtain ⟨ha, hb⟩ := veblen_eq_veblen_of_lt h₂₃ h₂.snd_lt h₃.snd_lt
        have ea : a₂ = a₃ := repr_inj h₂.fst h₃.fst ha
        have eb : b₂ = b₃ := repr_inj h₂.snd h₃.snd hb
        subst ea; subst eb
        exact assoc_gt_eq (lead_gt l₁ l₂ h₁₂) (cmp_eq_eq_of_eq l₂ l₂ rfl)
          (nadd_assoc_aux c₁ (VNote.vadd a₂ b₂ n₂ c₂) (VNote.vadd a₂ b₂ n₃ c₃)
            h₁.tail h₂ h₃)
      · exact assoc_gt_gt (lead_gt l₁ l₂ h₁₂) (lead_gt l₂ l₃ h₂₃)
          (lead_gt l₁ l₃ (h₂₃.trans h₁₂))
          (nadd_assoc_aux c₁ (VNote.vadd a₂ b₂ n₂ c₂) (VNote.vadd a₃ b₃ n₃ c₃)
            h₁.tail h₂ h₃)
termination_by x y z => size x + size y + size z
-- The measure on the right of each goal is built from the *original* arguments, so in the
-- branches where two leading terms have been identified the goal still mentions both copies;
-- `subst_vars` replays the identification the proof made.
decreasing_by
  all_goals (try subst_vars)
  all_goals (try simp only [size_vadd])
  all_goals omega

/-- **The natural sum of Veblen notations is associative on normal forms.**

Like `VNote.nadd_comm`, this needs the normal-form hypotheses: the merge identifies two
leading terms when they denote the same ordinal, and on raw notations `φ_a(b) = φ_{a'}(b')`
does not force `(a, b) = (a', b')`. -/
theorem nadd_assoc (a b c : VNote) (ha : NF a) (hb : NF b) (hc : NF c) :
    VNote.nadd (VNote.nadd a b) c = VNote.nadd a (VNote.nadd b c) :=
  nadd_assoc_aux a b c ha hb hc

end VNote

namespace Gamma0Note

/-- **Associativity of the natural sum on `Gamma0Note`.**  The normal-form hypotheses of
`VNote.nadd_assoc` are carried by the type. -/
theorem nadd_assoc (a b c : Gamma0Note) :
    Gamma0Note.nadd (Gamma0Note.nadd a b) c = Gamma0Note.nadd a (Gamma0Note.nadd b c) :=
  Subtype.ext (VNote.nadd_assoc a.1 b.1 c.1 a.2 b.2 c.2)

/-- `1 ≤ ω ^ a`, the notation-level form of `Ordinal.opow_pos`. -/
theorem one_le_omegaPow (a : Gamma0Note) : 1 ≤ Gamma0Note.omegaPow a := by
  rw [le_def, repr_one, repr_omegaPow]
  exact Order.one_le_iff_pos.2 (opow_pos (repr a) omega0_pos)

end Gamma0Note

end OrdinalAnalysis
