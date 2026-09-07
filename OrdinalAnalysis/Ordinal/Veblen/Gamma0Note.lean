/-
  `Gamma0Note`: the type of ordinals below `Γ₀` in Veblen normal form.

  This is to `VNote` what mathlib's `NONote` is to `ONote`: the subtype cut out by `NF`,
  carrying a `LinearOrder` (built from `cmp` through `linearOrderOfCompares`) and
  `WellFoundedLT` (pulled back from `Ordinal.lt_wf` along `repr`).

  The file also builds the *total* constructors `veblenNote` and `omegaPow` on notations.
  These need care: `vadd a b 1 0` denotes `φ_a(b)` but is a normal form only when `b` is not
  a fixed point of `φ_a`, and when it is one the correct notation for `φ_a(b)` is `b` itself.
  On normal forms that test is syntactic (`VNote.veblen_repr_eq_of_test` /
  `VNote.repr_lt_veblen_of_test`), so both operations are total, with no side hypothesis.
-/
import OrdinalAnalysis.Ordinal.Veblen.Cmp

set_option autoImplicit false

namespace OrdinalAnalysis

open Ordinal

namespace VNote

/-! ### Which notations denote additively principal ordinals -/

/-- If `b = φ_{b₁}(b₂) · n + c` with `n ≠ 1` or `c ≠ 0`, then `repr b` is not additively
principal.  Every value of `veblen` *is* additively principal
(`isPrincipal_add_veblen`), so such a `b` is never a fixed point of any `φ_a`. -/
theorem not_isPrincipal_add_repr_vadd {b₁ b₂ c : VNote} {n : ℕ+}
    (hc : repr c < veblen (repr b₁) (repr b₂)) (hne : n ≠ 1 ∨ c ≠ 0) :
    ¬ IsPrincipal (· + ·) (repr (VNote.vadd b₁ b₂ n c)) := by
  rw [repr_vadd]
  intro hP
  have hφ0 : (0 : Ordinal) < veblen (repr b₁) (repr b₂) := veblen_pos
  have hn1 : 1 ≤ (n : ℕ) := n.property
  rcases eq_or_ne (n : ℕ) 1 with h1 | h1
  · have hc0 : c ≠ 0 := by
      rcases hne with h | h
      · exact absurd (by exact_mod_cast h1 : n = 1) h
      · exact h
    have hγ : 0 < repr c := by
      cases c with
      | zero => exact absurd rfl hc0
      | vadd c₁ c₂ m d => exact repr_pos_of_vadd c₁ c₂ m d
    have hx : veblen (repr b₁) (repr b₂) * ((n : ℕ) : Ordinal)
        < veblen (repr b₁) (repr b₂) * ((n : ℕ) : Ordinal) + repr c := by
      simpa using add_lt_add_right hγ (veblen (repr b₁) (repr b₂) * ((n : ℕ) : Ordinal))
    have hy : repr c < veblen (repr b₁) (repr b₂) * ((n : ℕ) : Ordinal) + repr c := by
      refine hc.trans_le (le_trans ?_ le_self_add)
      conv_lhs => rw [← mul_one (veblen (repr b₁) (repr b₂))]
      exact mul_le_mul_right (by exact_mod_cast hn1) _
    exact absurd (hP hx hy) (lt_irrefl _)
  · have h2 : 1 < (n : ℕ) := lt_of_le_of_ne hn1 (Ne.symm h1)
    obtain ⟨M, hM⟩ : ∃ M : ℕ, (n : ℕ) = 1 + M := ⟨(n : ℕ) - 1, by omega⟩
    have hMlt : M < (n : ℕ) := by omega
    have hx : veblen (repr b₁) (repr b₂)
        < veblen (repr b₁) (repr b₂) * ((n : ℕ) : Ordinal) + repr c := by
      have h := mul_natCast_add_lt_of_lt (p := veblen (repr b₁) (repr b₂)) (x := 0)
        (y := repr c) (m := 1) (k := (n : ℕ)) hφ0 h2
      simpa using h
    have hy : veblen (repr b₁) (repr b₂) * (M : Ordinal) + repr c
        < veblen (repr b₁) (repr b₂) * ((n : ℕ) : Ordinal) + repr c :=
      mul_natCast_add_lt_of_lt hc hMlt
    have hsum : veblen (repr b₁) (repr b₂)
        + (veblen (repr b₁) (repr b₂) * (M : Ordinal) + repr c)
        = veblen (repr b₁) (repr b₂) * ((n : ℕ) : Ordinal) + repr c := by
      rw [← add_assoc, hM]
      push_cast
      rw [mul_add, mul_one]
    exact absurd hsum (hP hx hy).ne

/-! ### The fixed-point test

For a normal form `b`, `φ_a(b) = b` holds exactly when `b` is a single Veblen term
`vadd b₁ b₂ 1 0` with `a < b₁`.  One direction is `Ordinal.veblen_veblen_of_lt`; the other
uses `Ordinal.veblen_veblen_eq_veblen_iff` together with the normal-form side condition. -/

/-- If `b` passes the syntactic fixed-point test for `a`, then `b` really is a fixed point of
`φ_a`. -/
theorem veblen_repr_eq_of_test {a b₁ b₂ : VNote} (ha : NF a) (hb₁ : NF b₁)
    (hcmp : cmp a b₁ = Ordering.lt) :
    veblen (repr a) (repr (VNote.vadd b₁ b₂ 1 0)) = repr (VNote.vadd b₁ b₂ 1 0) := by
  have hlt : repr a < repr b₁ := (repr_lt_iff ha hb₁).2 hcmp
  rw [repr_vadd_one_zero]
  exact veblen_veblen_of_lt hlt (repr b₂)

/-- If `b` fails the syntactic fixed-point test for `a`, then `b` is not a fixed point of
`φ_a`, i.e. `vadd a b 1 0` is a legitimate normal form for `φ_a(b)`. -/
theorem repr_lt_veblen_of_test {a b₁ b₂ c : VNote} {n : ℕ+} (ha : NF a)
    (hb : NF (VNote.vadd b₁ b₂ n c)) (htest : ¬ (n = 1 ∧ c = 0 ∧ cmp a b₁ = Ordering.lt)) :
    repr (VNote.vadd b₁ b₂ n c) < veblen (repr a) (repr (VNote.vadd b₁ b₂ n c)) := by
  refine (right_le_veblen _ _).lt_of_ne fun heq => ?_
  by_cases hn : n = 1
  · by_cases hc : c = 0
    · subst hn; subst hc
      have hcmp : cmp a b₁ ≠ Ordering.lt := fun h => htest ⟨rfl, rfl, h⟩
      have hle : repr b₁ ≤ repr a := by
        by_contra hlt
        exact hcmp ((repr_lt_iff ha hb.fst).1 (lt_of_not_ge hlt))
      rw [repr_vadd_one_zero] at heq
      have h1 : veblen (repr a) (veblen (repr b₁) (repr b₂)) = veblen (repr b₁) (repr b₂) :=
        heq.symm
      have h2 : veblen (repr a) (repr b₂) = repr b₂ :=
        (veblen_veblen_eq_veblen_iff hle).1 h1
      exact absurd (veblen_eq_self_of_le hle h2) hb.snd_lt.ne'
    · have hprin : IsPrincipal (· + ·) (repr (VNote.vadd b₁ b₂ n c)) := by
        rw [heq]; exact isPrincipal_add_veblen _ _
      exact not_isPrincipal_add_repr_vadd hb.tail_lt (Or.inr hc) hprin
  · have hprin : IsPrincipal (· + ·) (repr (VNote.vadd b₁ b₂ n c)) := by
      rw [heq]; exact isPrincipal_add_veblen _ _
    exact not_isPrincipal_add_repr_vadd hb.tail_lt (Or.inl hn) hprin

/-! ### Total `veblen` on notations -/

/-- The notation for `φ_a(b)`.

If `b` is a fixed point of `φ_a` — which for normal forms means `b = vadd b₁ b₂ 1 0` with
`a < b₁` — the answer is `b` itself; otherwise it is the single term `vadd a b 1 0`.  So
`veblenNote` is total and always lands in normal form; see `VNote.nf_veblenNote` and
`VNote.repr_veblenNote`. -/
def veblenNote (a b : VNote) : VNote :=
  match b with
  | 0 => VNote.vadd a 0 1 0
  | VNote.vadd b₁ b₂ n c =>
    if n = 1 ∧ c = 0 ∧ cmp a b₁ = Ordering.lt then VNote.vadd b₁ b₂ n c
    else VNote.vadd a (VNote.vadd b₁ b₂ n c) 1 0

theorem nf_and_repr_veblenNote {a b : VNote} (ha : NF a) (hb : NF b) :
    NF (veblenNote a b) ∧ repr (veblenNote a b) = veblen (repr a) (repr b) := by
  cases b with
  | zero =>
    refine ⟨NF.vadd_zero 1 ha NF.zero (by simp), ?_⟩
    show repr (VNote.vadd a 0 1 0) = _
    simp
  | vadd b₁ b₂ n c =>
    by_cases htest : n = 1 ∧ c = 0 ∧ cmp a b₁ = Ordering.lt
    · obtain ⟨hn, hc, hcmp⟩ := htest
      subst hn; subst hc
      have hval : veblenNote a (VNote.vadd b₁ b₂ 1 0) = VNote.vadd b₁ b₂ 1 0 := by
        rw [veblenNote, if_pos ⟨rfl, rfl, hcmp⟩]
      rw [hval]
      exact ⟨hb, (veblen_repr_eq_of_test ha hb.fst hcmp).symm⟩
    · have hval : veblenNote a (VNote.vadd b₁ b₂ n c)
          = VNote.vadd a (VNote.vadd b₁ b₂ n c) 1 0 := by
        rw [veblenNote, if_neg htest]
      rw [hval]
      exact ⟨NF.vadd_zero 1 ha hb (repr_lt_veblen_of_test ha hb htest), repr_vadd_one_zero _ _⟩

theorem nf_veblenNote {a b : VNote} (ha : NF a) (hb : NF b) : NF (veblenNote a b) :=
  (nf_and_repr_veblenNote ha hb).1

theorem repr_veblenNote {a b : VNote} (ha : NF a) (hb : NF b) :
    repr (veblenNote a b) = veblen (repr a) (repr b) :=
  (nf_and_repr_veblenNote ha hb).2

/-- The total `ω ^ ·` on notations: `φ_0(a)`.  It differs from `VNote.omegaPow` exactly when
`a` is an ε-number, where the right answer is `a` itself. -/
def omegaPowNote (a : VNote) : VNote :=
  veblenNote 0 a

theorem nf_omegaPowNote {a : VNote} (ha : NF a) : NF (omegaPowNote a) :=
  nf_veblenNote NF.zero ha

theorem repr_omegaPowNote {a : VNote} (ha : NF a) : repr (omegaPowNote a) = ω ^ repr a := by
  rw [omegaPowNote, repr_veblenNote NF.zero ha, repr_zero, veblen_zero_apply]

instance nf_one : NF (1 : VNote) :=
  NF.vadd_zero 1 NF.zero NF.zero (by simp)

end VNote

/-! ### The type of ordinals below `Γ₀` -/

/-- The type of Veblen normal forms: notations for the ordinals below `Γ₀`.

This is the `Γ₀` analogue of mathlib's `NONote`, which does the same job for `ε₀`. -/
def Gamma0Note :=
  { o : VNote // VNote.NF o }
deriving DecidableEq

namespace Gamma0Note

instance NF (o : Gamma0Note) : VNote.NF o.1 :=
  o.2

/-- Build a `Gamma0Note` from a notation whose normality can be inferred. -/
def mk (o : VNote) [h : VNote.NF o] : Gamma0Note :=
  ⟨o, h⟩

/-- The ordinal denoted by a normal Veblen notation.

Noncomputable, like `NONote.repr`: it is there so that correctness can be *stated*.  All the
operations themselves are computable. -/
noncomputable def repr (o : Gamma0Note) : Ordinal.{0} :=
  o.1.repr

@[simp]
theorem repr_mk (o : VNote) [VNote.NF o] : repr (mk o) = o.repr :=
  rfl

instance : Preorder Gamma0Note where
  le x y := repr x ≤ repr y
  lt x y := repr x < repr y
  le_refl _ := @le_refl Ordinal _ _
  le_trans _ _ _ := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_ge _ _ := @lt_iff_le_not_ge Ordinal _ _ _

theorem lt_def {x y : Gamma0Note} : x < y ↔ repr x < repr y := Iff.rfl

theorem le_def {x y : Gamma0Note} : x ≤ y ↔ repr x ≤ repr y := Iff.rfl

theorem repr_lt_iff {x y : Gamma0Note} : x < y ↔ repr x < repr y := Iff.rfl

theorem repr_le_iff {x y : Gamma0Note} : x ≤ y ↔ repr x ≤ repr y := Iff.rfl

instance : Zero Gamma0Note :=
  ⟨⟨0, VNote.NF.zero⟩⟩

instance : Inhabited Gamma0Note :=
  ⟨0⟩

instance : One Gamma0Note :=
  ⟨⟨1, VNote.nf_one⟩⟩

@[simp] theorem repr_zero : repr 0 = 0 := rfl

@[simp] theorem repr_one : repr 1 = 1 := VNote.repr_one

theorem lt_wf : @WellFounded Gamma0Note (· < ·) :=
  InvImage.wf repr Ordinal.lt_wf

instance : WellFoundedLT Gamma0Note :=
  ⟨lt_wf⟩

instance : WellFoundedRelation Gamma0Note :=
  ⟨(· < ·), lt_wf⟩

/-- Comparison of normal Veblen notations. -/
def cmp (a b : Gamma0Note) : Ordering :=
  VNote.cmp a.1 b.1

theorem cmp_compares : ∀ a b : Gamma0Note, (cmp a b).Compares a b
  | ⟨a, ha⟩, ⟨b, hb⟩ => by
    show (VNote.cmp a b).Compares _ _
    rw [VNote.cmp_eq_cmp_repr a b ha hb]
    cases hc : _root_.cmp (VNote.repr a) (VNote.repr b) with
    | lt => exact (cmp_eq_lt_iff _ _).1 hc
    | eq => exact Subtype.ext (VNote.repr_inj ha hb ((cmp_eq_eq_iff _ _).1 hc))
    | gt => exact (cmp_eq_gt_iff _ _).1 hc

instance : LinearOrder Gamma0Note :=
  linearOrderOfCompares cmp cmp_compares

theorem repr_injective : Function.Injective repr := fun x y h =>
  Subtype.ext (VNote.repr_inj x.2 y.2 h)

@[simp]
theorem repr_inj {x y : Gamma0Note} : repr x = repr y ↔ x = y :=
  repr_injective.eq_iff

/-- `repr` as an order embedding of `Gamma0Note` into the ordinals. -/
noncomputable def reprEmbedding : Gamma0Note ↪o Ordinal.{0} where
  toFun := repr
  inj' := repr_injective
  map_rel_iff' := Iff.rfl

@[simp] theorem coe_reprEmbedding : ⇑reprEmbedding = repr := rfl

/-- Every notation denotes an ordinal below `Γ₀`. -/
theorem repr_lt_gamma_zero (o : Gamma0Note) : repr o < Γ₀ :=
  o.2.repr_lt_gamma_zero

/-! ### The Veblen function on notations -/

/-- `veblenNote a b` is the notation for `φ_a(b)`.  Total: the fixed-point case is handled
inside `VNote.veblenNote`. -/
def veblenNote (a b : Gamma0Note) : Gamma0Note :=
  ⟨VNote.veblenNote a.1 b.1, VNote.nf_veblenNote a.2 b.2⟩

@[simp]
theorem repr_veblenNote (a b : Gamma0Note) :
    repr (veblenNote a b) = veblen (repr a) (repr b) :=
  VNote.repr_veblenNote a.2 b.2

/-- `omegaPow a` is the notation for `ω ^ a`.  Total: when `a` is an ε-number the answer is
`a` itself. -/
def omegaPow (a : Gamma0Note) : Gamma0Note :=
  veblenNote 0 a

@[simp]
theorem repr_omegaPow (a : Gamma0Note) : repr (omegaPow a) = ω ^ repr a := by
  rw [omegaPow, repr_veblenNote, repr_zero, veblen_zero_apply]

/-! ### Order facts -/

theorem omegaPow_pos (a : Gamma0Note) : 0 < omegaPow a := by
  rw [lt_def]
  simpa using opow_pos (repr a) omega0_pos

theorem omegaPow_lt_omegaPow {a b : Gamma0Note} (h : a < b) : omegaPow a < omegaPow b := by
  rw [lt_def] at h ⊢
  simpa using (opow_lt_opow_iff_right one_lt_omega0).2 h

theorem omegaPow_le_omegaPow {a b : Gamma0Note} (h : a ≤ b) : omegaPow a ≤ omegaPow b := by
  rw [le_def] at h ⊢
  simpa using (opow_le_opow_iff_right one_lt_omega0).2 h

/-- `a ≤ ω ^ a` always.  Equality happens exactly at the ε-numbers, which — unlike in
`ONote`, whose notations all stay below `ε₀` — do occur in `Gamma0Note`; so the strict
version needs `omegaPow a ≠ a`, see `lt_omegaPow_self`. -/
theorem le_omegaPow_self (a : Gamma0Note) : a ≤ omegaPow a := by
  rw [le_def]
  simpa using right_le_veblen 0 (repr a)

theorem lt_omegaPow_self {a : Gamma0Note} (h : omegaPow a ≠ a) : a < omegaPow a :=
  (le_omegaPow_self a).lt_of_ne (Ne.symm h)

theorem veblenNote_lt_veblenNote_right {a b b' : Gamma0Note} (h : b < b') :
    veblenNote a b < veblenNote a b' := by
  rw [lt_def] at h ⊢
  simpa using (veblen_right_strictMono (repr a)) h

theorem veblenNote_le_veblenNote_right {a b b' : Gamma0Note} (h : b ≤ b') :
    veblenNote a b ≤ veblenNote a b' := by
  rw [le_def] at h ⊢
  simpa using (veblen_right_strictMono (repr a)).monotone h

/-- `veblen` is monotone, but **not** strictly monotone, in its first argument: for a fixed
point `b` of `φ_a`, `φ_a b = φ_a' b = b` for every `a' ≥ a`.  The strict version holds at
`b = 0`; see `veblenNote_zero_lt_veblenNote_zero`. -/
theorem veblenNote_le_veblenNote_left {a a' b : Gamma0Note} (h : a ≤ a') :
    veblenNote a b ≤ veblenNote a' b := by
  rw [le_def] at h ⊢
  simpa using veblen_left_monotone (repr b) h

theorem veblenNote_zero_lt_veblenNote_zero {a a' : Gamma0Note} (h : a < a') :
    veblenNote a 0 < veblenNote a' 0 := by
  rw [lt_def] at h ⊢
  simpa using veblen_zero_strictMono h

theorem veblenNote_pos (a b : Gamma0Note) : 0 < veblenNote a b := by
  rw [lt_def]
  simp

theorem lt_veblenNote_self (a : Gamma0Note) : a < veblenNote a a := by
  rw [lt_def]
  simpa using lt_veblen (repr a)

theorem le_veblenNote_right (a b : Gamma0Note) : b ≤ veblenNote a b := by
  rw [le_def]
  simpa using right_le_veblen (repr a) (repr b)

end Gamma0Note

end OrdinalAnalysis
