/-
  Rank segments of `Gamma0Note`: the `ω`-power arithmetic that predicative cut
  elimination consumes.

  `Ramified/PredicativeCut.lean` reduced Pohlers' theorem
  `⊢^α_{ρ ⊕ ω^ξ} Γ ⇒ ⊢^{φ_ξ(α)}_ρ Γ` to a single hypothesis about the *rank
  notation*, `RankAbsorbed A I ρ (ρ ⊕ ω^ξ) V ξ`, and discharged it at `ξ = 1`.
  Its module docstring names the two facts the main induction on `ξ` still
  needs, both of them about `Gamma0Note` alone:

  1. *(successor)* every `a < ρ ⊕ ω^{η+1}` satisfies `a < ρ ⊕ ω^η · m` for some
     `m : ℕ` — and even the term `ω^η · m` has to be built, `Gamma0Note` having
     no multiplication;
  2. *(limit)* every `a < ρ ⊕ ω^ξ` satisfies `a < ρ ⊕ ω^η` for some `η < ξ`.

  Both come from one lemma proved here, `exists_lt_nadd_omegaPow`: the segment
  `[ρ, ρ ⊕ ω^ξ)` is *exhausted from inside* by the notations `ρ ⊕ d` with
  `d < ω^ξ`.  Given that, (1) is `exists_lt_omegaPowMul` (`d < ω^{η+1}` implies
  `d < ω^η · m`) and (2) is `leadExpNote` (`d < ω^ξ` implies `d < ω^{e+1}` for
  `e` the exponent of `d`'s leading term, and `e + 1 ≤ ξ`).

  Three things had to be settled before any of that could be stated.

  * **The segment statement is false for a general `ρ`.**  `⊕` is the *natural*
    sum, and `1 ⊕ ω = ω + 1`, so the segment `[1, 1 ⊕ ω)` contains the limit
    rank `ω`; no finite descent reaches `1` from it, and `φ_1` does not pay for
    an infinite one.  What makes the segment well behaved is that `ρ` is a
    *multiple of* `ω^ξ`, which on notations is the syntactic condition
    `PowClosed ξ ρ`: every Veblen term of `ρ` has value at least `ω^ξ`.  It is
    preserved by exactly the operations the induction performs
    (`PowClosed.mono`, `powClosed_nadd_omegaPowMul`) and holds of `ρ = 0`, which
    is the case the theorem is stated at.

  * **`Gamma0Note.nadd` has no `repr` equation in the repository.**  Only order
    facts are proved about it (`NaturalSum.lean`), never
    `repr (x ⊕ y) = Ordinal.nadd (repr x) (repr y)`, and mathlib has no Cantor-normal-form
    description of `Ordinal.nadd` to transport.  Nothing here needs the general
    equation: what the induction adds to `ρ` is always *smaller than every term
    of `ρ`*, and in that situation the natural sum is plain concatenation, so
    `repr (x ⊕ y) = repr x + repr y` with *ordinal* addition.  That is
    `VNote.repr_nadd_of_lt` (a strictly smaller summand) and
    `VNote.nadd_single_spec` (a single term, possibly equal to the last term of
    `x`, where the two multiplicities merge).  They are the only bridge between
    the syntactic merge and ordinal arithmetic used anywhere below.

  * **`repr` is not surjective onto the ordinals below `Γ₀`**, so a witness
    obtained from a mathlib limit lemma is an ordinal, not a notation.  Every
    witness produced here is therefore read off the *syntax* instead:
    `splitLo`/`splitHi` cut a notation at a threshold, and `leadExp` returns the
    exponent of the leading term (`lead x = ω ^ repr (leadExp x)` uniformly —
    for `a = 0` because `φ_0(b) = ω^b`, and for `a ≠ 0` because `φ_a(b)` is then
    an ε-number).
-/
import OrdinalAnalysis.Ordinal.Veblen.Instance

set_option autoImplicit false

namespace OrdinalAnalysis

open Ordinal

namespace VNote

/-! ### Every Veblen value is a power of `ω` -/

/-- Every value of the Veblen function is `ω ^ e` for some `e`: for `p = 0` because
`φ_0(b) = ω ^ b`, and for `p ≠ 0` because `φ_p(q)` is then a fixed point of `ω ^ ·`. -/
theorem exists_opow_veblen (p q : Ordinal) : ∃ e : Ordinal, veblen p q = ω ^ e := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨q, veblen_zero_apply q⟩
  · refine ⟨veblen p q, ?_⟩
    have h := veblen_veblen_of_lt (o₁ := 0) (o₂ := p) (zero_lt_iff.mpr hp) q
    rw [veblen_zero_apply] at h
    exact h.symm

theorem one_le_veblen (p q : Ordinal) : (1 : Ordinal) ≤ veblen p q := by
  have h : (0 : Ordinal) < veblen p q := veblen_pos
  simpa using Order.add_one_le_iff.2 h

/-! ### Notations all of whose terms are at least `s` -/

/-- `AllTermsGe s x`: every Veblen term of `x` has value at least `s`.

For `s = ω ^ e` this says exactly that `repr x` is a multiple of `ω ^ e`
(`exists_mul_of_allTermsGe`), but as a *syntactic* condition it is also what makes the
natural sum with anything below `s` a concatenation. -/
def AllTermsGe (s : Ordinal) : VNote → Prop
  | 0 => True
  | VNote.vadd a b _ c => s ≤ veblen (repr a) (repr b) ∧ AllTermsGe s c

theorem allTermsGe_zero (s : Ordinal) : AllTermsGe s 0 := trivial

theorem allTermsGe_vadd_iff {s : Ordinal} {a b c : VNote} {n : ℕ+} :
    AllTermsGe s (VNote.vadd a b n c) ↔ s ≤ veblen (repr a) (repr b) ∧ AllTermsGe s c :=
  Iff.rfl

theorem allTermsGe_head {s : Ordinal} {a b c : VNote} {n : ℕ+}
    (h : AllTermsGe s (VNote.vadd a b n c)) : s ≤ veblen (repr a) (repr b) :=
  (allTermsGe_vadd_iff.1 h).1

theorem allTermsGe_tail {s : Ordinal} {a b c : VNote} {n : ℕ+}
    (h : AllTermsGe s (VNote.vadd a b n c)) : AllTermsGe s c :=
  (allTermsGe_vadd_iff.1 h).2

theorem allTermsGe_mono {s t : Ordinal} (hts : t ≤ s) :
    ∀ x : VNote, AllTermsGe s x → AllTermsGe t x
  | 0, _ => allTermsGe_zero t
  | VNote.vadd _ _ _ c, h =>
    allTermsGe_vadd_iff.2
      ⟨hts.trans (allTermsGe_head h), allTermsGe_mono hts c (allTermsGe_tail h)⟩

/-- Every Veblen value is at least `1`, so every notation has all its terms `≥ 1`. -/
theorem allTermsGe_one : ∀ x : VNote, AllTermsGe 1 x
  | 0 => allTermsGe_zero 1
  | VNote.vadd a b _ c =>
    allTermsGe_vadd_iff.2 ⟨one_le_veblen (repr a) (repr b), allTermsGe_one c⟩

/-- A notation whose terms are all `≥ s` but whose value is `< s` is `0`. -/
theorem eq_zero_of_allTermsGe_of_lt {s : Ordinal} :
    ∀ x : VNote, AllTermsGe s x → repr x < s → x = 0
  | 0, _, _ => rfl
  | VNote.vadd a b n c, h, hlt =>
    absurd ((allTermsGe_head h).trans (lead_le_repr a b n c)) (not_le.2 hlt)

/-- If every term of `x` is a multiple of `ω ^ e`, so is `repr x`. -/
theorem exists_mul_of_allTermsGe (e : Ordinal) :
    ∀ x : VNote, NF x → AllTermsGe (ω ^ e) x → ∃ γ : Ordinal, repr x = ω ^ e * γ
  | 0, _, _ => ⟨0, by simp⟩
  | VNote.vadd a b n c, hx, hall => by
    obtain ⟨δ, hδ⟩ := exists_opow_veblen (repr a) (repr b)
    have hle : ω ^ e ≤ ω ^ δ := hδ ▸ allTermsGe_head hall
    have hed : e ≤ δ := (opow_le_opow_iff_right one_lt_omega0).1 hle
    obtain ⟨γ, hγ⟩ := exists_mul_of_allTermsGe e c hx.tail (allTermsGe_tail hall)
    refine ⟨ω ^ (δ - e) * (n : ℕ) + γ, ?_⟩
    have hsplit : ω ^ δ = ω ^ e * ω ^ (δ - e) := by
      rw [← opow_add, Ordinal.add_sub_cancel_of_le hed]
    rw [repr_vadd, hδ, hγ, hsplit, mul_add, mul_assoc]

/-! ### The natural sum as concatenation

The two `repr` equations for `VNote.nadd` used in this file.  Both say that when the right
summand sits below every term of the left one, the syntactic merge is a concatenation and
computes ordinary ordinal addition. -/

/-- **Appending a strictly smaller notation.**  If every term of `x` is `≥ s` and
`repr y < s`, the merge never reaches the multiplicities, so it adds. -/
theorem repr_nadd_of_lt {s : Ordinal} :
    ∀ (x y : VNote), NF x → NF y → AllTermsGe s x → repr y < s →
      repr (nadd x y) = repr x + repr y
  | 0, _, _, _, _, _ => by rw [zero_nadd, repr_zero, zero_add]
  | VNote.vadd _ _ _ _, 0, _, _, _, _ => by rw [nadd_zero, repr_zero, add_zero]
  | VNote.vadd a b n c, VNote.vadd a' b' n' c', hx, hy, hall, hlt => by
    have hlead : veblen (repr a') (repr b') < veblen (repr a) (repr b) :=
      lt_of_le_of_lt (lead_le_repr a' b' n' c')
        (lt_of_lt_of_le hlt (allTermsGe_head hall))
    have hcmp := lead_cmp_eq_cmp_repr hx hy
    rw [nadd_of_gt (by rw [hcmp, hlead.cmp_eq_gt]), repr_vadd, repr_vadd,
      repr_nadd_of_lt (s := s) c (VNote.vadd a' b' n' c') hx.tail hy (allTermsGe_tail hall) hlt,
      ← add_assoc]

/-- **Appending a single term that may merge with the last one.**  If every term of `x` is
`≥ φ_p(q)`, then `x ⊕ φ_p(q)·k` again has all its terms `≥ φ_p(q)`, and its value is
`repr x + φ_p(q)·k`.  The boundary case — `x`'s last term is exactly `φ_p(q)`, so the two
multiplicities merge — is why this is not an instance of `repr_nadd_of_lt`. -/
theorem nadd_single_spec (p q : VNote) (k : ℕ+) (ht : NF (VNote.vadd p q k 0)) :
    ∀ (x : VNote), NF x → AllTermsGe (veblen (repr p) (repr q)) x →
      repr (nadd x (VNote.vadd p q k 0))
          = repr x + veblen (repr p) (repr q) * (k : ℕ) ∧
        AllTermsGe (veblen (repr p) (repr q)) (nadd x (VNote.vadd p q k 0))
  | 0, _, _ => by
    refine ⟨by rw [zero_nadd, repr_zero, repr_vadd, repr_zero, add_zero, zero_add], ?_⟩
    rw [zero_nadd]
    exact allTermsGe_vadd_iff.2 ⟨le_rfl, allTermsGe_zero _⟩
  | VNote.vadd a b n c, hx, hall => by
    have hhead : veblen (repr p) (repr q) ≤ veblen (repr a) (repr b) := allTermsGe_head hall
    have hcmp := lead_cmp_eq_cmp_repr hx ht
    rcases lt_trichotomy (veblen (repr a) (repr b)) (veblen (repr p) (repr q)) with
      hlt | heq | hgt
    · exact absurd hhead (not_le.2 hlt)
    · -- the last term of `x` is the term being appended: the tail must be `0`
      have hc : c = 0 :=
        eq_zero_of_allTermsGe_of_lt c (allTermsGe_tail hall) (heq ▸ hx.tail_lt)
      subst hc
      rw [nadd_of_eq (by rw [hcmp, (_root_.cmp_eq_eq_iff _ _).2 heq]), nadd_zero]
      refine ⟨?_, allTermsGe_vadd_iff.2 ⟨hhead, allTermsGe_zero _⟩⟩
      rw [repr_vadd, repr_vadd, repr_zero, add_zero, add_zero, pnat_add_coe,
        Nat.cast_add, mul_add, heq]
    · rw [nadd_of_gt (by rw [hcmp, hgt.cmp_eq_gt])]
      obtain ⟨ih1, ih2⟩ := nadd_single_spec p q k ht c hx.tail (allTermsGe_tail hall)
      exact ⟨by rw [repr_vadd, repr_vadd, ih1, ← add_assoc],
        allTermsGe_vadd_iff.2 ⟨hhead, ih2⟩⟩

/-! ### Splitting a notation at a threshold

`splitHi s x` keeps the leading terms of value `≥ s`, `splitLo s x` the trailing terms of
value `< s`; together they reconstruct `x`.  The threshold is an ordinal, so the test is
made decidable classically; the functions only ever *produce witnesses*, they are never
evaluated. -/

open scoped Classical in
/-- The leading block of `x`: the terms of value at least `s`. -/
noncomputable def splitHi (s : Ordinal) : VNote → VNote
  | 0 => 0
  | VNote.vadd a b n c =>
    if s ≤ veblen (repr a) (repr b) then VNote.vadd a b n (splitHi s c) else 0

open scoped Classical in
/-- The trailing block of `x`: the terms of value below `s`. -/
noncomputable def splitLo (s : Ordinal) : VNote → VNote
  | 0 => 0
  | VNote.vadd a b n c =>
    if s ≤ veblen (repr a) (repr b) then splitLo s c else VNote.vadd a b n c

theorem splitHi_zero (s : Ordinal) : splitHi s 0 = 0 := rfl

theorem splitLo_zero (s : Ordinal) : splitLo s 0 = 0 := rfl

open scoped Classical in
theorem splitHi_vadd (s : Ordinal) (a b : VNote) (n : ℕ+) (c : VNote) :
    splitHi s (VNote.vadd a b n c)
      = if s ≤ veblen (repr a) (repr b) then VNote.vadd a b n (splitHi s c) else 0 := rfl

open scoped Classical in
theorem splitLo_vadd (s : Ordinal) (a b : VNote) (n : ℕ+) (c : VNote) :
    splitLo s (VNote.vadd a b n c)
      = if s ≤ veblen (repr a) (repr b) then splitLo s c else VNote.vadd a b n c := rfl

theorem repr_splitHi_add_splitLo (s : Ordinal) :
    ∀ x : VNote, repr (splitHi s x) + repr (splitLo s x) = repr x
  | 0 => by rw [splitHi_zero, splitLo_zero, repr_zero, add_zero]
  | VNote.vadd a b n c => by
    by_cases h : s ≤ veblen (repr a) (repr b)
    · rw [splitHi_vadd, splitLo_vadd, if_pos h, if_pos h, repr_vadd, repr_vadd, add_assoc,
        repr_splitHi_add_splitLo s c]
    · rw [splitHi_vadd, splitLo_vadd, if_neg h, if_neg h, repr_zero, zero_add]

theorem repr_splitHi_le (s : Ordinal) (x : VNote) : repr (splitHi s x) ≤ repr x := by
  rw [← repr_splitHi_add_splitLo s x]
  exact le_self_add

theorem allTermsGe_splitHi (s : Ordinal) : ∀ x : VNote, AllTermsGe s (splitHi s x)
  | 0 => by rw [splitHi_zero]; exact allTermsGe_zero s
  | VNote.vadd a b n c => by
    by_cases h : s ≤ veblen (repr a) (repr b)
    · rw [splitHi_vadd, if_pos h]
      exact allTermsGe_vadd_iff.2 ⟨h, allTermsGe_splitHi s c⟩
    · rw [splitHi_vadd, if_neg h]
      exact allTermsGe_zero s

theorem nf_splitHi (s : Ordinal) : ∀ (x : VNote), NF x → NF (splitHi s x)
  | 0, _ => by rw [splitHi_zero]; exact NF.zero
  | VNote.vadd a b n c, hx => by
    by_cases h : s ≤ veblen (repr a) (repr b)
    · rw [splitHi_vadd, if_pos h]
      exact NF.vadd hx.fst hx.snd (nf_splitHi s c hx.tail) hx.snd_lt
        (lt_of_le_of_lt (repr_splitHi_le s c) hx.tail_lt)
    · rw [splitHi_vadd, if_neg h]
      exact NF.zero

theorem nf_splitLo (s : Ordinal) : ∀ (x : VNote), NF x → NF (splitLo s x)
  | 0, _ => by rw [splitLo_zero]; exact NF.zero
  | VNote.vadd a b n c, hx => by
    by_cases h : s ≤ veblen (repr a) (repr b)
    · rw [splitLo_vadd, if_pos h]
      exact nf_splitLo s c hx.tail
    · rw [splitLo_vadd, if_neg h]
      exact hx

theorem repr_splitLo_lt {s : Ordinal} (hs : IsPrincipal (· + ·) s) (hs0 : 0 < s) :
    ∀ (x : VNote), NF x → repr (splitLo s x) < s
  | 0, _ => by rw [splitLo_zero, repr_zero]; exact hs0
  | VNote.vadd a b n c, hx => by
    by_cases h : s ≤ veblen (repr a) (repr b)
    · rw [splitLo_vadd, if_pos h]
      exact repr_splitLo_lt hs hs0 c hx.tail
    · rw [splitLo_vadd, if_neg h]
      exact NF.repr_lt_of_lead_lt hx hs (not_le.1 h)

/-! ### The exponent of the leading term -/

/-- A notation for the exponent of the leading term of `x`: the leading Veblen value of `x`
is `ω ^ repr (leadExp x)`.  For `a = 0` the leading value is `φ_0(b) = ω ^ b`; otherwise it
is an ε-number, hence its own `ω`-exponent. -/
def leadExp : VNote → VNote
  | 0 => 0
  | VNote.vadd a b _ _ => if a = 0 then b else VNote.vadd a b 1 0

theorem leadExp_zero : leadExp 0 = 0 := rfl

theorem leadExp_vadd (a b : VNote) (n : ℕ+) (c : VNote) :
    leadExp (VNote.vadd a b n c) = if a = 0 then b else VNote.vadd a b 1 0 := rfl

theorem lead_eq_opow_leadExp {a b c : VNote} {n : ℕ+} (hx : NF (VNote.vadd a b n c)) :
    veblen (repr a) (repr b) = ω ^ repr (leadExp (VNote.vadd a b n c)) := by
  rw [leadExp_vadd]
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl, repr_zero, veblen_zero_apply]
  · rw [if_neg ha, repr_vadd_one_zero]
    have hpos : (0 : Ordinal) < repr a :=
      zero_lt_iff.mpr (fun h => ha (repr_eq_zero_iff.1 h))
    have h := veblen_veblen_of_lt (o₁ := 0) (o₂ := repr a) hpos (repr b)
    rw [veblen_zero_apply] at h
    exact h.symm

theorem nf_leadExp : ∀ (x : VNote), NF x → NF (leadExp x)
  | 0, _ => by rw [leadExp_zero]; exact NF.zero
  | VNote.vadd a b n c, hx => by
    rw [leadExp_vadd]
    by_cases ha : a = 0
    · rw [if_pos ha]; exact hx.snd
    · rw [if_neg ha]; exact NF.vadd_zero 1 hx.fst hx.snd hx.snd_lt

/-- The leading term is at most the whole notation. -/
theorem opow_leadExp_le_repr {a b c : VNote} {n : ℕ+} (hx : NF (VNote.vadd a b n c)) :
    ω ^ repr (leadExp (VNote.vadd a b n c)) ≤ repr (VNote.vadd a b n c) := by
  rw [← lead_eq_opow_leadExp hx]
  exact lead_le_repr a b n c

/-- **Every notation is below `ω ^ (e + 1)` for `e` the exponent of its leading term.** -/
theorem repr_lt_opow_leadExp_succ : ∀ (x : VNote), NF x → repr x < ω ^ (repr (leadExp x) + 1)
  | 0, _ => by
    rw [leadExp_zero, repr_zero, zero_add, opow_one]
    exact omega0_pos
  | VNote.vadd a b n c, hx => by
    have hlead : veblen (repr a) (repr b) = ω ^ repr (leadExp (VNote.vadd a b n c)) :=
      lead_eq_opow_leadExp hx
    have h1 : repr (VNote.vadd a b n c)
        < ω ^ repr (leadExp (VNote.vadd a b n c)) * (((n : ℕ) + 1 : ℕ) : Ordinal) := by
      have h := mul_natCast_add_lt_of_lt (p := ω ^ repr (leadExp (VNote.vadd a b n c)))
        (x := repr c) (y := 0) (m := (n : ℕ)) (k := (n : ℕ) + 1)
        (hlead ▸ hx.tail_lt) (Nat.lt_succ_self _)
      rw [add_zero] at h
      rw [repr_vadd, hlead]
      exact h
    have h2 : ω ^ repr (leadExp (VNote.vadd a b n c)) * (((n : ℕ) + 1 : ℕ) : Ordinal)
        ≤ ω ^ repr (leadExp (VNote.vadd a b n c)) * ω :=
      mul_le_mul_right (le_of_lt (natCast_lt_omega0 _)) _
    calc repr (VNote.vadd a b n c) < _ := h1
      _ ≤ ω ^ repr (leadExp (VNote.vadd a b n c)) * ω := h2
      _ = ω ^ (repr (leadExp (VNote.vadd a b n c)) + 1) := by rw [opow_add, opow_one]

/-- The exponent of the leading term of a notation below `ω ^ e` is below `e`. -/
theorem leadExp_lt_of_lt_opow {e : Ordinal} (he : 0 < e) :
    ∀ (x : VNote), NF x → repr x < ω ^ e → repr (leadExp x) < e
  | 0, _, _ => by rw [leadExp_zero, repr_zero]; exact he
  | VNote.vadd a b n c, hx, hlt => by
    have hle := opow_leadExp_le_repr hx
    exact (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hle hlt)

end VNote

/-! ### The `Gamma0Note` layer -/

namespace Gamma0Note

open VNote

/-! #### `ρ` is a multiple of `ω ^ ξ` -/

/-- **`ρ` is a multiple of `ω ^ ξ`**, syntactically: every Veblen term of `ρ` has value at
least `ω ^ ξ`.

This is the side condition under which the rank segment `[ρ, ρ ⊕ ω^ξ)` behaves: the natural
sum with anything below `ω ^ ξ` becomes ordinal addition, and the segment is exhausted by
the `ρ ⊕ d` with `d < ω ^ ξ`.  Without it the segment statement is false — `1 ⊕ ω = ω + 1`,
so the segment above `ρ = 1` at `ξ = 1` contains the limit rank `ω`. -/
def PowClosed (ξ ρ : Gamma0Note) : Prop :=
  VNote.AllTermsGe (ω ^ repr ξ) ρ.1

theorem powClosed_zero (ξ : Gamma0Note) : PowClosed ξ 0 :=
  VNote.allTermsGe_zero _

theorem PowClosed.mono {η ξ ρ : Gamma0Note} (h : η ≤ ξ) (hρ : PowClosed ξ ρ) :
    PowClosed η ρ :=
  VNote.allTermsGe_mono ((opow_le_opow_iff_right one_lt_omega0).2 h) ρ.1 hρ

/-- `repr ρ` really is a multiple of `ω ^ repr ξ`. -/
theorem PowClosed.exists_mul {ξ ρ : Gamma0Note} (h : PowClosed ξ ρ) :
    ∃ γ : Ordinal, repr ρ = ω ^ repr ξ * γ :=
  VNote.exists_mul_of_allTermsGe _ ρ.1 ρ.2 h

/-- Two distinct multiples of `ω ^ e` are at least `ω ^ e` apart. -/
theorem add_opow_le_of_mul_lt {e x y : Ordinal} (hx : ∃ γ : Ordinal, x = ω ^ e * γ)
    (hy : ∃ γ : Ordinal, y = ω ^ e * γ) (h : x < y) : x + ω ^ e ≤ y := by
  obtain ⟨γ, rfl⟩ := hx
  obtain ⟨γ', rfl⟩ := hy
  have hγ : γ < γ' := by
    by_contra hcon
    exact absurd (mul_le_mul_right (not_lt.1 hcon) (ω ^ e)) (not_le.2 h)
  calc ω ^ e * γ + ω ^ e = ω ^ e * (γ + 1) := by rw [mul_add, mul_one]
    _ ≤ ω ^ e * γ' := mul_le_mul_right (Order.add_one_le_iff.2 hγ) _

/-! #### `ω ^ η` as a single Veblen term, and its finite multiples -/

/-- `φ_0(y)` is always a single Veblen term with multiplicity `1` and empty tail: either
`y` is a fixed point, and then `φ_0(y) = y` is itself such a term, or the notation built is
`vadd 0 y 1 0`. -/
theorem VNote.exists_term_veblenNote_zero (y : VNote) :
    ∃ p q : VNote, VNote.veblenNote 0 y = VNote.vadd p q 1 0 := by
  cases y with
  | zero => exact ⟨0, 0, rfl⟩
  | vadd b₁ b₂ n c =>
    by_cases htest : n = 1 ∧ c = 0 ∧ VNote.cmp 0 b₁ = Ordering.lt
    · obtain ⟨hn, hc, hcmp⟩ := htest
      subst hn; subst hc
      exact ⟨b₁, b₂, by rw [VNote.veblenNote, if_pos ⟨rfl, rfl, hcmp⟩]⟩
    · exact ⟨0, VNote.vadd b₁ b₂ n c, by rw [VNote.veblenNote, if_neg htest]⟩

/-- `ω ^ η` is a single Veblen term with multiplicity `1` and empty tail. -/
theorem exists_term_omegaPow (η : Gamma0Note) :
    ∃ p q : VNote, (omegaPow η).1 = VNote.vadd p q 1 0 ∧
      veblen (VNote.repr p) (VNote.repr q) = ω ^ repr η := by
  obtain ⟨p, q, hpq⟩ := VNote.exists_term_veblenNote_zero η.1
  have hpq' : (omegaPow η).1 = VNote.vadd p q 1 0 := hpq
  refine ⟨p, q, hpq', ?_⟩
  have h : VNote.repr ((omegaPow η).1) = ω ^ repr η := repr_omegaPow η
  rw [hpq', VNote.repr_vadd_one_zero] at h
  exact h

/-- `ω ^ η · m`, built as the `m`-fold natural sum of `ω ^ η`.  `Gamma0Note` has no
multiplication; this is the term the successor step of predicative cut elimination descends
through, one level-`η` elimination per unit. -/
def omegaPowMul (η : Gamma0Note) : ℕ → Gamma0Note
  | 0 => 0
  | (m + 1) => nadd (omegaPowMul η m) (omegaPow η)

@[simp] theorem omegaPowMul_zero (η : Gamma0Note) : omegaPowMul η 0 = 0 := rfl

@[simp] theorem omegaPowMul_succ (η : Gamma0Note) (m : ℕ) :
    omegaPowMul η (m + 1) = nadd (omegaPowMul η m) (omegaPow η) := rfl

theorem val_repr (x : Gamma0Note) : VNote.repr x.1 = repr x := rfl

/-- **The rank block `ρ ⊕ ω^η·m`**: it is again a multiple of `ω ^ η`, and its value is
`repr ρ + ω ^ repr η * m`. -/
theorem powClosed_nadd_omegaPowMul {η ρ : Gamma0Note} (hρ : PowClosed η ρ) :
    ∀ m : ℕ, PowClosed η (nadd ρ (omegaPowMul η m)) ∧
      repr (nadd ρ (omegaPowMul η m)) = repr ρ + ω ^ repr η * m
  | 0 => by
    rw [omegaPowMul_zero, nadd_zero, Nat.cast_zero, mul_zero, add_zero]
    exact ⟨hρ, rfl⟩
  | (m + 1) => by
    obtain ⟨p, q, hpq, hval⟩ := exists_term_omegaPow η
    obtain ⟨ih1, ih2⟩ := powClosed_nadd_omegaPowMul hρ m
    have hassoc : nadd ρ (omegaPowMul η (m + 1))
        = nadd (nadd ρ (omegaPowMul η m)) (omegaPow η) := by
      rw [omegaPowMul_succ, nadd_assoc]
    have ht : VNote.NF (VNote.vadd p q 1 0) := hpq ▸ (omegaPow η).2
    have hall : VNote.AllTermsGe (veblen (VNote.repr p) (VNote.repr q))
        ((nadd ρ (omegaPowMul η m)).1) := by
      rw [hval]; exact ih1
    obtain ⟨hr, ha⟩ :=
      VNote.nadd_single_spec p q 1 ht _ (nadd ρ (omegaPowMul η m)).2 hall
    have hcoe : (nadd (nadd ρ (omegaPowMul η m)) (omegaPow η)).1
        = VNote.nadd ((nadd ρ (omegaPowMul η m)).1) (VNote.vadd p q 1 0) := by
      rw [← hpq]; rfl
    constructor
    · show VNote.AllTermsGe (ω ^ repr η) ((nadd ρ (omegaPowMul η (m + 1))).1)
      rw [hassoc, hcoe, ← hval]
      exact ha
    · show VNote.repr ((nadd ρ (omegaPowMul η (m + 1))).1) = _
      rw [hassoc, hcoe, hr, val_repr, ih2, hval, PNat.one_coe, Nat.cast_one, mul_one,
        add_assoc, Nat.cast_add, Nat.cast_one, mul_add, mul_one]

/-- The value of `ω ^ η · m`. -/
theorem repr_omegaPowMul (η : Gamma0Note) (m : ℕ) :
    repr (omegaPowMul η m) = ω ^ repr η * m := by
  have h := (powClosed_nadd_omegaPowMul (ρ := 0) (powClosed_zero η) m).2
  rw [zero_nadd, repr_zero, zero_add] at h
  exact h

/-- The value of `ρ ⊕ ω^ξ`, for `ρ` a multiple of `ω ^ ξ`. -/
theorem repr_nadd_omegaPow {ξ ρ : Gamma0Note} (hρ : PowClosed ξ ρ) :
    repr (nadd ρ (omegaPow ξ)) = repr ρ + ω ^ repr ξ := by
  have h := (powClosed_nadd_omegaPowMul hρ 1).2
  rw [omegaPowMul_succ, omegaPowMul_zero, zero_nadd, Nat.cast_one, mul_one] at h
  exact h

/-! #### Adding something strictly below every term -/

/-- The value of `ρ ⊕ d` when `d` is below `ω ^ ξ` and `ρ` is a multiple of `ω ^ ξ`. -/
theorem repr_nadd_of_lt {ξ ρ d : Gamma0Note} (hρ : PowClosed ξ ρ) (hd : d < omegaPow ξ) :
    repr (nadd ρ d) = repr ρ + repr d := by
  have hd' : VNote.repr d.1 < ω ^ repr ξ := by
    have h : repr d < repr (omegaPow ξ) := hd
    rwa [repr_omegaPow] at h
  exact VNote.repr_nadd_of_lt (s := ω ^ repr ξ) ρ.1 d.1 ρ.2 d.2 hρ hd'

/-- `ρ ⊕ n` has value `repr ρ + n`: `ofNat n` is the single term `1 · n`, and every notation
has all its terms `≥ 1`. -/
theorem repr_nadd_ofNat (ρ : Gamma0Note) : ∀ n : ℕ, repr (nadd ρ (ofNat n)) = repr ρ + n
  | 0 => by
    have h0 : (ofNat 0 : Gamma0Note) = 0 := Subtype.ext rfl
    rw [h0, nadd_zero, Nat.cast_zero, add_zero]
  | (n + 1) => by
    have hone : veblen (VNote.repr (0 : VNote)) (VNote.repr (0 : VNote)) = 1 := by
      rw [VNote.repr_zero, veblen_zero_apply, opow_zero]
    have ht : VNote.NF (VNote.vadd 0 0 ⟨n + 1, Nat.succ_pos n⟩ 0) := VNote.nf_ofNat (n + 1)
    obtain ⟨hr, _⟩ := VNote.nadd_single_spec 0 0 ⟨n + 1, Nat.succ_pos n⟩ ht ρ.1 ρ.2
      (VNote.allTermsGe_mono (le_of_eq hone) ρ.1 (VNote.allTermsGe_one ρ.1))
    show VNote.repr (VNote.nadd ρ.1 (VNote.ofNat (n + 1))) = _
    rw [show VNote.ofNat (n + 1) = VNote.vadd 0 0 ⟨n + 1, Nat.succ_pos n⟩ 0 from rfl, hr, hone,
      one_mul, val_repr]
    rfl

/-- `ρ ⊕ 1` has value `repr ρ + 1`. -/
theorem repr_nadd_one (ρ : Gamma0Note) : repr (nadd ρ 1) = repr ρ + 1 := by
  have hone : veblen (VNote.repr (0 : VNote)) (VNote.repr (0 : VNote)) = 1 := by
    rw [VNote.repr_zero, veblen_zero_apply, opow_zero]
  have ht : VNote.NF (VNote.vadd 0 0 1 0) := VNote.nf_one
  obtain ⟨hr, _⟩ := VNote.nadd_single_spec 0 0 1 ht ρ.1 ρ.2
    (VNote.allTermsGe_mono (le_of_eq hone) ρ.1 (VNote.allTermsGe_one ρ.1))
  show VNote.repr (VNote.nadd ρ.1 (1 : VNote)) = _
  rw [show (1 : VNote) = VNote.vadd 0 0 1 0 from rfl, hr, hone, one_mul, PNat.one_coe,
    Nat.cast_one, val_repr]

theorem lt_nadd_one_iff {a ρ : Gamma0Note} : a < nadd ρ 1 ↔ a ≤ ρ := by
  rw [lt_def, repr_nadd_one, ← Order.succ_eq_add_one, Order.lt_succ_iff, ← le_def]

/-! #### The segment `[ρ, ρ ⊕ ω^ξ)` is exhausted from inside -/

/-- **The key segment lemma.**  Every notation below `ρ ⊕ ω^ξ` is already below `ρ ⊕ d` for
some `d < ω ^ ξ`.

This is the fact `Ramified/PredicativeCut.lean` is missing, in the form that yields both of
the two facts its docstring asks for.  The witness is read off the syntax of `a`: `d` is the
trailing block of `a` below `ω ^ ξ`, plus one.  That the leading block of `a` does not
exceed `ρ` is where `PowClosed` is used — both are multiples of `ω ^ ξ`, so if the leading
block exceeded `ρ` it would exceed it by a whole `ω ^ ξ`. -/
theorem exists_lt_nadd_omegaPow {ξ ρ a : Gamma0Note} (hξ : 0 < ξ) (hρ : PowClosed ξ ρ)
    (ha : a < nadd ρ (omegaPow ξ)) : ∃ d : Gamma0Note, d < omegaPow ξ ∧ a < nadd ρ d := by
  have hξ' : (0 : Ordinal) < repr ξ := by simpa using lt_def.mp hξ
  have hsP : IsPrincipal (· + ·) (ω ^ repr ξ) := isPrincipal_add_omega0_opow _
  have hs1 : (1 : Ordinal) < ω ^ repr ξ := by
    calc (1 : Ordinal) = ω ^ (0 : Ordinal) := (opow_zero ω).symm
      _ < ω ^ repr ξ := (opow_lt_opow_iff_right one_lt_omega0).2 hξ'
  have hs0 : (0 : Ordinal) < ω ^ repr ξ := opow_pos _ omega0_pos
  -- the trailing block of `a`, and the leading one
  obtain ⟨T, hTval⟩ : ∃ T : Gamma0Note, T.1 = VNote.splitLo (ω ^ repr ξ) a.1 :=
    ⟨⟨VNote.splitLo (ω ^ repr ξ) a.1, VNote.nf_splitLo _ a.1 a.2⟩, rfl⟩
  obtain ⟨P, hPval⟩ : ∃ P : Gamma0Note, P.1 = VNote.splitHi (ω ^ repr ξ) a.1 :=
    ⟨⟨VNote.splitHi (ω ^ repr ξ) a.1, VNote.nf_splitHi _ a.1 a.2⟩, rfl⟩
  have hTlt : repr T < ω ^ repr ξ := by
    rw [← val_repr, hTval]
    exact VNote.repr_splitLo_lt hsP hs0 a.1 a.2
  have hsplit : repr P + repr T = repr a := by
    rw [← val_repr P, ← val_repr T, ← val_repr a, hTval, hPval]
    exact VNote.repr_splitHi_add_splitLo _ a.1
  have hPmul : ∃ γ : Ordinal, repr P = ω ^ repr ξ * γ := by
    rw [← val_repr, hPval]
    exact VNote.exists_mul_of_allTermsGe _ _ (hPval ▸ P.2) (VNote.allTermsGe_splitHi _ a.1)
  have haρ : repr a < repr ρ + ω ^ repr ξ := by
    have h : repr a < repr (nadd ρ (omegaPow ξ)) := ha
    rwa [repr_nadd_omegaPow hρ] at h
  have hPle : repr P ≤ repr ρ := by
    by_contra hcon
    have h1 : repr ρ + ω ^ repr ξ ≤ repr P :=
      add_opow_le_of_mul_lt hρ.exists_mul hPmul (not_le.1 hcon)
    have h2 : repr P ≤ repr a := by rw [← hsplit]; exact le_self_add
    exact absurd (h1.trans h2) (not_le.2 haρ)
  -- the witness
  have hdlt : nadd T 1 < omegaPow ξ := by
    rw [lt_def, repr_omegaPow, repr_nadd_one]
    exact hsP hTlt hs1
  refine ⟨nadd T 1, hdlt, ?_⟩
  rw [lt_def, repr_nadd_of_lt hρ hdlt, repr_nadd_one]
  calc repr a = repr P + repr T := hsplit.symm
    _ ≤ repr ρ + repr T := add_le_add_left hPle _
    _ < repr ρ + (repr T + 1) := add_lt_add_right (lt_add_one _) _

/-! #### The two facts the main induction on `ξ` needs -/

/-- **(1) The successor step.**  Everything below `ω ^ (η ⊕ 1)` is below `ω ^ η · m` for
some finite `m`. -/
theorem exists_lt_omegaPowMul {η d : Gamma0Note} (hd : d < omegaPow (nadd η 1)) :
    ∃ m : ℕ, d < omegaPowMul η m := by
  have h : repr d < ω ^ (repr η + 1) := by
    have h' : repr d < repr (omegaPow (nadd η 1)) := hd
    rwa [repr_omegaPow, repr_nadd_one] at h'
  rw [opow_add, opow_one] at h
  obtain ⟨c, hc, hdc⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 h
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.1 hc
  exact ⟨m, by rw [lt_def, repr_omegaPowMul]; exact hdc⟩

/-- The notation for the exponent of the leading term. -/
def leadExpNote (x : Gamma0Note) : Gamma0Note :=
  ⟨VNote.leadExp x.1, VNote.nf_leadExp x.1 x.2⟩

@[simp] theorem repr_leadExpNote (x : Gamma0Note) :
    repr (leadExpNote x) = VNote.repr (VNote.leadExp x.1) := rfl

/-- Every notation is below `ω ^ (e ⊕ 1)` for `e` the exponent of its leading term. -/
theorem lt_omegaPow_leadExp_succ (x : Gamma0Note) :
    x < omegaPow (nadd (leadExpNote x) 1) := by
  rw [lt_def, repr_omegaPow, repr_nadd_one, repr_leadExpNote]
  exact VNote.repr_lt_opow_leadExp_succ x.1 x.2

/-- **(2) The limit step**, in the form that also covers the successor one: if `x < ω ^ ξ`
then the exponent `e` of `x`'s leading term is below `ξ`, and `x < ω ^ (e ⊕ 1)`.  When `ξ`
is a limit this gives a genuine `e ⊕ 1 < ξ`; when `ξ = e ⊕ 1` it gives `ξ` back, which is
the successor case. -/
theorem leadExpNote_lt_of_lt_omegaPow {ξ x : Gamma0Note} (hξ : 0 < ξ) (h : x < omegaPow ξ) :
    leadExpNote x < ξ := by
  have hξ' : (0 : Ordinal) < repr ξ := by simpa using lt_def.mp hξ
  have hx : VNote.repr x.1 < ω ^ repr ξ := by
    have h' : repr x < repr (omegaPow ξ) := h
    rwa [repr_omegaPow] at h'
  rw [lt_def, repr_leadExpNote]
  exact VNote.leadExp_lt_of_lt_opow hξ' x.1 x.2 hx

/-- `e ⊕ 1 ≤ ξ` whenever `e < ξ`. -/
theorem nadd_one_le_of_lt {e ξ : Gamma0Note} (h : e < ξ) : nadd e 1 ≤ ξ := by
  rw [le_def, repr_nadd_one, ← Order.succ_eq_add_one]
  exact Order.succ_le_of_lt (lt_def.mp h)

/-- `1 ≤ e ⊕ 1` always. -/
theorem one_le_nadd_one (e : Gamma0Note) : (1 : Gamma0Note) ≤ nadd e 1 := by
  rw [le_def, repr_nadd_one, repr_one]
  exact le_add_self

end Gamma0Note

end OrdinalAnalysis
