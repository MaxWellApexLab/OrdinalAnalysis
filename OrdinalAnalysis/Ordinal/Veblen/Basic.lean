/-
  Veblen normal form notations for the ordinals below `Γ₀`.

  `VNote` is to `Ordinal.veblen` what mathlib's `ONote` is to `ω ^ ·`: a computable
  syntax whose meaning is read off by `repr`, together with a normal-form predicate
  `NF` under which `repr` is an order embedding into the ordinals.  The architecture
  (`repr`, `NF`, `cmp`, `cmp_compares`, `repr_inj`, and the subtype `Gamma0Note` carrying
  the `LinearOrder`) is copied from `Mathlib/SetTheory/Ordinal/Notation.lean`; the shape of
  the order and of the normal-form side conditions is the one of the Coq `hydra-battles`
  type `T2`.

  Well-foundedness is free: it is pulled back from `Ordinal.lt_wf` along `repr`.

  This file: the type, `repr`, the normal form, and `repr o < Γ₀`.
-/
import Mathlib.SetTheory.Ordinal.Veblen
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Data.PNat.Basic

set_option autoImplicit false

namespace OrdinalAnalysis

open Ordinal

/-! ### Ordinal preliminaries

Facts about `Ordinal.veblen` and `Γ₀` that justify the normal form but are not themselves
about notations. -/

/-- Every value of the Veblen function is a power of `ω`, hence additively principal. -/
theorem isPrincipal_add_veblen (a b : Ordinal) : IsPrincipal (· + ·) (veblen a b) := by
  obtain ⟨z, hz⟩ := veblen_mem_range_opow a b
  exact hz ▸ isPrincipal_add_omega0_opow z

/-- `Γ₀` is a fixed point of `ω ^ ·`. -/
theorem omega0_opow_gamma_zero : (ω : Ordinal) ^ (Γ₀ : Ordinal) = Γ₀ := by
  have h := veblen_veblen_of_lt (o₁ := 0) (o₂ := Γ₀) gamma_pos 0
  rwa [veblen_gamma_zero, veblen_zero_apply] at h

/-- `Γ₀` is additively principal. -/
theorem isPrincipal_add_gamma_zero : IsPrincipal (· + ·) (Γ₀ : Ordinal) :=
  omega0_opow_gamma_zero ▸ isPrincipal_add_omega0_opow _

/-- `Γ₀` is closed under the Veblen function; this is what makes it the supremum of the
ordinals denoted by normal `VNote`s. -/
theorem veblen_lt_gamma_zero {a b : Ordinal} (ha : a < Γ₀) (hb : b < Γ₀) : veblen a b < Γ₀ := by
  have key : veblen a b < veblen Γ₀ 0 := by
    rw [veblen_lt_veblen_iff]
    exact Or.inr (Or.inl ⟨ha, by rwa [veblen_gamma_zero]⟩)
  rwa [veblen_gamma_zero] at key

/-- A smaller leading term wins, whatever the multiplicities and tails: if `p < q` with `q`
additively principal, `x < p` and `k > 0`, then `p * m + x < q * k + y`. -/
theorem mul_natCast_add_lt_of_lead_lt {p q x y : Ordinal} {m k : ℕ}
    (hq : IsPrincipal (· + ·) q) (hx : x < p) (hpq : p < q) (hk : 0 < k) :
    p * m + x < q * k + y := by
  have h1 : p * m + x < q := hq (hq.mul_natCast_lt hpq m) (hx.trans hpq)
  have hk1 : (1 : Ordinal) ≤ ((k : ℕ) : Ordinal) := by exact_mod_cast hk
  have h2 : q ≤ q * k + y :=
    le_trans (by simpa using mul_le_mul_right hk1 q) le_self_add
  exact h1.trans_le h2

/-- With equal leading terms, a smaller multiplicity wins: if `x < p` and `m < k` then
`p * m + x < p * k + y`. -/
theorem mul_natCast_add_lt_of_lt {p x y : Ordinal} {m k : ℕ} (hx : x < p) (hmk : m < k) :
    p * m + x < p * k + y := by
  have h1 : p * m + x < p * ((m : Ordinal) + 1) := by
    rw [mul_add_one]
    exact add_lt_add_right hx _
  have h2 : p * ((m : Ordinal) + 1) ≤ p * k := by
    have hc : ((m : Ordinal) + 1) ≤ (k : Ordinal) := by exact_mod_cast hmk
    exact mul_le_mul_right hc p
  exact (h1.trans_le h2).trans_le le_self_add

/-- The comparison rule for `p * m + x` against `q * k + y`, when `p` and `q` are additively
principal, `x < p`, `y < q`, and `m`, `k` are positive: compare `p` with `q`, then `m` with
`k`, then `x` with `y`.  This is the ordinal content of `VNote.cmp`. -/
theorem cmp_mul_natCast_add {p q x y : Ordinal} {m k : ℕ}
    (hp : IsPrincipal (· + ·) p) (hq : IsPrincipal (· + ·) q)
    (hx : x < p) (hy : y < q) (hm : 0 < m) (hk : 0 < k) :
    cmp (p * m + x) (q * k + y) = (cmp p q).then ((cmp m k).then (cmp x y)) := by
  rcases lt_trichotomy p q with h | rfl | h
  · rw [h.cmp_eq_lt]
    exact (mul_natCast_add_lt_of_lead_lt hq hx h hk).cmp_eq_lt
  · rw [cmp_self_eq_eq]
    rcases lt_trichotomy m k with h | rfl | h
    · rw [h.cmp_eq_lt]
      exact (mul_natCast_add_lt_of_lt hx h).cmp_eq_lt
    · rw [cmp_self_eq_eq]
      show _ = cmp x y
      rcases lt_trichotomy x y with h | rfl | h
      · rw [h.cmp_eq_lt, (add_lt_add_right h (p * (m : ℕ))).cmp_eq_lt]
      · rw [cmp_self_eq_eq, cmp_self_eq_eq]
      · rw [h.cmp_eq_gt, (add_lt_add_right h (p * (m : ℕ))).cmp_eq_gt]
    · rw [h.cmp_eq_gt]
      exact (mul_natCast_add_lt_of_lt hy h).cmp_eq_gt
  · rw [h.cmp_eq_gt]
    exact (mul_natCast_add_lt_of_lead_lt hp hy h hm).cmp_eq_gt

/-- **Uniqueness of the Veblen pair.**  If `veblen α β = veblen α' β'` and neither `β` nor
`β'` is a fixed point of the corresponding `φ`, then `α = α'` and `β = β'`.

This is exactly what makes the normal-form side condition `repr b < veblen (repr a) (repr b)`
the right one: without it, `veblen 0 (veblen 1 0) = veblen 1 0` would give two names for the
same ordinal. -/
theorem veblen_eq_veblen_of_lt {α β α' β' : Ordinal} (h : veblen α β = veblen α' β')
    (hβ : β < veblen α β) (hβ' : β' < veblen α' β') : α = α' ∧ β = β' := by
  rcases veblen_eq_veblen_iff.1 h with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
  · exact ⟨h1, h2⟩
  · exact absurd (h2.trans h.symm) hβ.ne
  · exact absurd (h2.symm.trans h) hβ'.ne

/-! ### The type of Veblen notations -/

set_option genSizeOfSpec false in
/-- Recursive definition of a Veblen ordinal notation.  `zero` denotes the ordinal `0`, and
`vadd a b n c` denotes `φ_a(b) · n + c`, where `φ` is the two-argument Veblen function
`Ordinal.veblen`.

Taking `a = 0` recovers Cantor normal form, since `φ_0(b) = ω ^ b`; so `VNote` extends
`ONote`, and reaches all the way to `Γ₀` instead of stopping at `ε₀`.

For this to be a *normal* form we need `b` not to be a fixed point of `φ_a` and the tail `c`
to be smaller than the leading term, but neither condition can be stated before `repr`
exists, so they are split off into `NF`. -/
inductive VNote : Type
  /-- The notation for `0`. -/
  | zero : VNote
  /-- `vadd a b n c` denotes `φ_a(b) · n + c`. -/
  | vadd (a b : VNote) (n : ℕ+) (c : VNote) : VNote
  deriving DecidableEq

namespace VNote

/-- Notation for `0`. -/
instance : Zero VNote :=
  ⟨zero⟩

@[simp]
theorem zero_def : zero = 0 :=
  rfl

instance : Inhabited VNote :=
  ⟨0⟩

/-- The ordinal denoted by a Veblen notation. -/
noncomputable def repr : VNote → Ordinal.{0}
  | 0 => 0
  | vadd a b n c => veblen (repr a) (repr b) * (n : ℕ) + repr c

@[simp]
theorem repr_zero : repr 0 = 0 :=
  rfl

@[simp]
theorem repr_vadd (a b : VNote) (n : ℕ+) (c : VNote) :
    repr (vadd a b n c) = veblen (repr a) (repr b) * (n : ℕ) + repr c :=
  rfl

/-- A hand-written size function, used as the termination measure for `VNote.cmp`.

The generated `sizeOf` is unusable here (`genSizeOfSpec` is off, and it also counts the
`ℕ+`), and `cmp` is not structurally recursive anyway: it recurses on the freshly built term
`vadd a b 1 0`, which is not a subterm of either argument.  With this `size`,
`size (vadd a b 1 0) = size a + size b + 1`, and every recursive call of `cmp` strictly
decreases `size x + size y` by plain arithmetic. -/
def size : VNote → ℕ
  | 0 => 0
  | vadd a b _ c => size a + size b + size c + 1

@[simp] theorem size_zero : size 0 = 0 := rfl

@[simp]
theorem size_vadd (a b : VNote) (n : ℕ+) (c : VNote) :
    size (vadd a b n c) = size a + size b + size c + 1 :=
  rfl

/-- `ω ^ a`, as a notation: `φ_0(a)`.  This is in normal form exactly when `a` is not an
ε-number; `OrdinalAnalysis.Gamma0Note.omegaPow` is the total version. -/
def omegaPow (a : VNote) : VNote :=
  vadd 0 a 1 0

/-- Notation for `1 = ω ^ 0`. -/
instance : One VNote :=
  ⟨omegaPow 0⟩

theorem one_def : (1 : VNote) = vadd 0 0 1 0 :=
  rfl

@[simp]
theorem repr_omegaPow (a : VNote) : repr (omegaPow a) = ω ^ repr a := by
  simp [omegaPow, veblen_zero_apply]

@[simp]
theorem repr_one : repr (1 : VNote) = 1 := by
  rw [show (1 : VNote) = omegaPow 0 from rfl, repr_omegaPow, repr_zero, opow_zero]

/-- `repr (vadd a b 1 0) = φ_a(b)`: the notation of a single Veblen term.  This is the term
`cmp` recurses on when it has to compare an argument against a whole Veblen value. -/
@[simp]
theorem repr_vadd_one_zero (a b : VNote) :
    repr (vadd a b 1 0) = veblen (repr a) (repr b) := by
  simp

theorem repr_pos_of_vadd (a b : VNote) (n : ℕ+) (c : VNote) : 0 < repr (vadd a b n c) := by
  rw [repr_vadd]
  refine lt_of_lt_of_le ?_ le_self_add
  have h1 : (1 : Ordinal) ≤ ((n : ℕ) : Ordinal) := by
    have : 1 ≤ (n : ℕ) := n.property
    exact_mod_cast this
  calc (0 : Ordinal) < veblen (repr a) (repr b) := veblen_pos
    _ = veblen (repr a) (repr b) * 1 := (mul_one _).symm
    _ ≤ veblen (repr a) (repr b) * ((n : ℕ) : Ordinal) := mul_le_mul_right h1 _

theorem repr_eq_zero_iff {o : VNote} : repr o = 0 ↔ o = 0 := by
  constructor
  · intro h
    cases o with
    | zero => rfl
    | vadd a b n c => exact absurd h (repr_pos_of_vadd a b n c).ne'
  · rintro rfl; rfl

/-! ### Normal form -/

/-- `NF o` says that the notation `o` is a Veblen normal form.

For `vadd a b n c`, denoting `φ_a(b) · n + c`, this asks that

* `a`, `b`, `c` are themselves in normal form;
* `repr b < veblen (repr a) (repr b)`, i.e. `b` is **not** a fixed point of `φ_a` — the side
  condition that makes the pair `(a, b)` unique for a given value `φ_a(b)` (compare
  `Ordinal.invVeblen₁` / `Ordinal.invVeblen₂`, and the `nf` predicate of the Coq
  `hydra-battles` type `T2`);
* `repr c < veblen (repr a) (repr b)`, i.e. the tail is smaller than the leading term.

Together these force `repr` to be injective and to reflect `cmp` on normal forms. -/
class inductive NF : VNote → Prop
  /-- `0` is in normal form. -/
  | zero : NF 0
  /-- `φ_a(b) · n + c` is in normal form when `a`, `b`, `c` are, `b` is not a fixed point of
  `φ_a`, and the tail `c` is below the leading term. -/
  | vadd {a b c : VNote} {n : ℕ+} : NF a → NF b → NF c →
      repr b < veblen (repr a) (repr b) →
      repr c < veblen (repr a) (repr b) →
      NF (VNote.vadd a b n c)

attribute [instance] NF.zero

/-- `NFBelow o s` says that `o` is a normal form denoting an ordinal `< s`. -/
def NFBelow (o : VNote) (s : Ordinal) : Prop :=
  NF o ∧ repr o < s

theorem NFBelow.nf {o : VNote} {s : Ordinal} (h : NFBelow o s) : NF o := h.1

theorem NFBelow.repr_lt {o : VNote} {s : Ordinal} (h : NFBelow o s) : repr o < s := h.2

theorem NFBelow.mono {o : VNote} {s t : Ordinal} (h : NFBelow o s) (hst : s ≤ t) :
    NFBelow o t :=
  ⟨h.1, h.2.trans_le hst⟩

theorem NF.fst {a b c : VNote} {n : ℕ+} : NF (VNote.vadd a b n c) → NF a
  | .vadd h _ _ _ _ => h

theorem NF.snd {a b c : VNote} {n : ℕ+} : NF (VNote.vadd a b n c) → NF b
  | .vadd _ h _ _ _ => h

theorem NF.tail {a b c : VNote} {n : ℕ+} : NF (VNote.vadd a b n c) → NF c
  | .vadd _ _ h _ _ => h

/-- In a normal form `vadd a b n c`, the second argument is not a fixed point of `φ_a`. -/
theorem NF.snd_lt {a b c : VNote} {n : ℕ+} :
    NF (VNote.vadd a b n c) → repr b < veblen (repr a) (repr b)
  | .vadd _ _ _ h _ => h

/-- In a normal form `vadd a b n c`, the tail is smaller than the leading term. -/
theorem NF.tail_lt {a b c : VNote} {n : ℕ+} :
    NF (VNote.vadd a b n c) → repr c < veblen (repr a) (repr b)
  | .vadd _ _ _ _ h => h

theorem NF.vadd_zero {a b : VNote} (n : ℕ+) (ha : NF a) (hb : NF b)
    (h : repr b < veblen (repr a) (repr b)) : NF (VNote.vadd a b n 0) :=
  NF.vadd ha hb NF.zero h (by simp)

/-- The leading term of a normal form dominates the whole notation: if the leading Veblen
value is below an additively principal `s`, then so is the value of the notation.  This is
the analogue of `ONote.NFBelow.repr_lt`, and it is the workhorse behind `cmp_compares`. -/
theorem NF.repr_lt_of_lead_lt {a b c : VNote} {n : ℕ+} {s : Ordinal}
    (h : NF (VNote.vadd a b n c)) (hs : IsPrincipal (· + ·) s)
    (hlt : veblen (repr a) (repr b) < s) : repr (VNote.vadd a b n c) < s := by
  rw [repr_vadd]
  exact hs (hs.mul_natCast_lt hlt _) (h.tail_lt.trans hlt)

/-- Every normal form denotes an ordinal below `Γ₀`. -/
theorem NF.repr_lt_gamma_zero {o : VNote} (h : NF o) : repr o < Γ₀ := by
  induction h with
  | zero => simp
  | @vadd a b c n _ _ _ _ _ iha ihb ihc =>
    have hv : veblen (repr a) (repr b) < Γ₀ := veblen_lt_gamma_zero iha ihb
    rw [repr_vadd]
    exact isPrincipal_add_gamma_zero (isPrincipal_add_gamma_zero.mul_natCast_lt hv _) ihc

end VNote

end OrdinalAnalysis
