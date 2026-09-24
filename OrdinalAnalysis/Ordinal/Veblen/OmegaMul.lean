/-
  `ω · x` and `−1 + x` on Veblen notations, and the rank blocks of transfinite levels.

  `Gamma0Note` has no multiplication.  Left multiplication by `ω` is nevertheless a term-wise
  operation on normal forms: `ω · (φ_a(b) · n + c) = (ω · φ_a(b)) · n + ω · c`, and

  * `ω · φ_0(b) = ω ^ (1 + b) = φ_0(1 + b)`,
  * `ω · φ_a(b) = φ_a(b)` for `a ≠ 0`, because `φ_a(b)` is then a fixed point of `ω ^ ·`.

  `1 + b` is `b + 1` for finite `b` and `b` otherwise.  So `omegaMulV` rewrites the exponent of
  every `φ_0`-term and leaves every other term alone (`repr_omegaMulV`, `nf_omegaMulV`).
  Likewise `−1 + x` (the ordinal `x - 1`, which is left subtraction) lowers a finite notation
  by one and fixes every infinite one (`predV`).

  **The rank block of a level.**  A level-`ℓ` set atom is priced inside the block

      [blk ℓ, blk ℓ ⊕ ω]        with   blk ℓ := ω · (−1 + ℓ),

  so `blk (n + 1) = ω · n` at a finite level and `blk ℓ = ω · ℓ` at an infinite one.  The
  facts cut elimination needs are proved here on `repr`:

  * `blk ℓ` is a multiple of `ω` (`powClosed_blk`), so `blk ℓ ⊕ ω` is `blk ℓ + ω`;
  * a lower level's whole block sits below a higher level's base
    (`blkTop_le_blk : κ < ℓ → blkTop κ ≤ blk ℓ`, with `blkTop ℓ := blk ℓ ⊕ ω` for `ℓ ≠ 0` and
    `blkTop 0 := 0`);
  * `blkTop ℓ` is a limit, so closed under successor (`succ_lt_blkTop`);
  * at a limit level `λ`, every lower block lies below `blk λ` (`blkTop_lt_blk_of_limit`).

  The finite values are `repr (blk (n + 1)) = ω · n` and `repr (blkTop n) = ω · n`.
-/
import OrdinalAnalysis.Ordinal.Veblen.RankSegments
import OrdinalAnalysis.Ordinal.Veblen.Encodable

set_option autoImplicit false

namespace OrdinalAnalysis

open Ordinal

/-! ### Ordinal preliminaries -/

/-- A Veblen value other than `φ_0(0) = 1` is at least `ω`. -/
theorem omega0_le_veblen {α β : Ordinal} (h : α ≠ 0 ∨ β ≠ 0) : ω ≤ veblen α β := by
  rcases eq_or_ne α 0 with rfl | hα
  · have hβ : β ≠ 0 := h.resolve_left (fun h' => h' rfl)
    rw [veblen_zero_apply]
    calc ω = ω ^ (1 : Ordinal) := (opow_one ω).symm
      _ ≤ ω ^ β := opow_le_opow_right omega0_pos (Order.one_le_iff_ne_zero.2 hβ)
  · have hfix : veblen 0 (veblen α β) = veblen α β :=
      veblen_veblen_of_lt (pos_iff_ne_zero.2 hα) β
    rw [veblen_zero_apply] at hfix
    rw [← hfix]
    calc ω = ω ^ (1 : Ordinal) := (opow_one ω).symm
      _ ≤ ω ^ veblen α β := opow_le_opow_right omega0_pos (Order.one_le_iff_ne_zero.2 veblen_pos.ne')

/-- `ω · φ_α(β) = φ_α(β)` for `α ≠ 0`: `φ_α(β)` is an ε-number. -/
theorem omega0_mul_veblen {α : Ordinal} (hα : α ≠ 0) (β : Ordinal) :
    ω * veblen α β = veblen α β := by
  have hfix : ω ^ veblen α β = veblen α β := by
    have h := veblen_veblen_of_lt (pos_iff_ne_zero.2 hα) β (o₁ := 0)
    rwa [veblen_zero_apply] at h
  have h1 : 1 + veblen α β = veblen α β := one_add_of_omega0_le (omega0_le_veblen (Or.inl hα))
  calc ω * veblen α β = ω ^ (1 : Ordinal) * ω ^ veblen α β := by rw [opow_one, hfix]
    _ = ω ^ (1 + veblen α β) := (opow_add ω 1 _).symm
    _ = veblen α β := by rw [h1, hfix]

/-- `ω · ω^β = ω^(1 + β)`. -/
theorem omega0_mul_opow (β : Ordinal) : ω * ω ^ β = ω ^ (1 + β) := by
  rw [opow_add, opow_one]

/-- `x < ω^x` survives `x ↦ 1 + x`. -/
theorem one_add_lt_opow {β : Ordinal} (h : β < ω ^ β) : 1 + β < ω ^ (1 + β) := by
  rcases lt_or_ge β ω with hβ | hβ
  · have h1 : 1 + β < ω := isPrincipal_add_omega0 one_lt_omega0 hβ
    exact h1.trans_le (left_le_opow ω (lt_of_lt_of_le zero_lt_one (le_self_add (a := (1 : Ordinal)) (b := β))))
  · rwa [one_add_of_omega0_le hβ]

namespace VNote

/-! ### `1 + x` -/

/-- `1 + x` on notations: a finite notation goes up by one, an infinite one is fixed. -/
def onePlus : VNote → VNote
  | .zero => 1
  | .vadd a b n c => if a = 0 ∧ b = 0 then .vadd 0 0 (n + 1) c else .vadd a b n c

/-- A notation whose leading term is not `φ_0(0)` denotes an infinite ordinal. -/
theorem omega0_le_repr_vadd {a b c : VNote} {n : ℕ+} (h : ¬(a = 0 ∧ b = 0)) :
    ω ≤ repr (.vadd a b n c) := by
  refine le_trans (omega0_le_veblen ?_) (lead_le_repr a b n c)
  by_cases ha : a = 0
  · refine Or.inr (fun hb => h ⟨ha, repr_eq_zero_iff.1 hb⟩)
  · exact Or.inl (fun ha' => ha (repr_eq_zero_iff.1 ha'))

theorem repr_onePlus : ∀ x : VNote, repr (onePlus x) = 1 + repr x
  | .zero => by
    show repr (1 : VNote) = 1 + repr 0
    rw [repr_one, repr_zero, add_zero]
  | .vadd a b n c => by
    by_cases h : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := h
      rw [onePlus, if_pos ⟨rfl, rfl⟩, repr_vadd, repr_vadd, repr_zero, veblen_zero_apply,
        opow_zero, one_mul, one_mul, PNat.add_coe, PNat.one_coe, ← add_assoc]
      congr 1
      push_cast
      rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
    · rw [onePlus, if_neg h, one_add_of_omega0_le (omega0_le_repr_vadd h)]

theorem nf_onePlus : ∀ {x : VNote}, NF x → NF (onePlus x)
  | .zero, _ => nf_one
  | .vadd a b n c, hx => by
    by_cases h : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := h
      rw [onePlus, if_pos ⟨rfl, rfl⟩]
      exact NF.vadd hx.fst hx.snd hx.tail hx.snd_lt hx.tail_lt
    · rw [onePlus, if_neg h]
      exact hx

/-! ### `ω · x` -/

/-- **`ω · x` on notations.**  Every `φ_0`-term `ω^b` becomes `ω^(1+b)`; every other term is
an ε-number and is fixed. -/
def omegaMulV : VNote → VNote
  | .zero => .zero
  | .vadd a b n c =>
      if a = 0 then .vadd 0 (onePlus b) n (omegaMulV c) else .vadd a b n (omegaMulV c)

theorem repr_omegaMulV : ∀ x : VNote, repr (omegaMulV x) = ω * repr x
  | .zero => by show repr (0 : VNote) = ω * repr 0; rw [repr_zero, mul_zero]
  | .vadd a b n c => by
    by_cases ha : a = 0
    · subst ha
      rw [omegaMulV, if_pos rfl, repr_vadd, repr_vadd, repr_omegaMulV c, repr_onePlus,
        repr_zero, veblen_zero_apply, veblen_zero_apply, mul_add, ← mul_assoc, omega0_mul_opow]
    · rw [omegaMulV, if_neg ha, repr_vadd, repr_vadd, repr_omegaMulV c, mul_add, ← mul_assoc,
        omega0_mul_veblen (fun h => ha (repr_eq_zero_iff.1 h))]

theorem nf_omegaMulV : ∀ {x : VNote}, NF x → NF (omegaMulV x)
  | .zero, _ => NF.zero
  | .vadd a b n c, hx => by
    by_cases ha : a = 0
    · subst ha
      rw [omegaMulV, if_pos rfl]
      have hsnd := hx.snd_lt
      have htl := hx.tail_lt
      rw [repr_zero, veblen_zero_apply] at hsnd htl
      refine NF.vadd NF.zero (nf_onePlus hx.snd) (nf_omegaMulV hx.tail) ?_ ?_
      · rw [repr_zero, veblen_zero_apply, repr_onePlus]
        exact one_add_lt_opow hsnd
      · rw [repr_zero, veblen_zero_apply, repr_onePlus, repr_omegaMulV, ← omega0_mul_opow]
        exact (mul_lt_mul_iff_right₀ omega0_pos).2 htl
    · rw [omegaMulV, if_neg ha]
      refine NF.vadd hx.fst hx.snd (nf_omegaMulV hx.tail) hx.snd_lt ?_
      rw [repr_omegaMulV, ← omega0_mul_veblen (fun h => ha (repr_eq_zero_iff.1 h)) (repr b)]
      exact (mul_lt_mul_iff_right₀ omega0_pos).2 hx.tail_lt

/-- Every term of `ω · x` is at least `ω`. -/
theorem allTermsGe_omegaMulV : ∀ x : VNote, AllTermsGe ω (omegaMulV x)
  | .zero => allTermsGe_zero ω
  | .vadd a b n c => by
    by_cases ha : a = 0
    · subst ha
      rw [omegaMulV, if_pos rfl]
      refine allTermsGe_vadd_iff.2 ⟨?_, allTermsGe_omegaMulV c⟩
      rw [repr_zero, veblen_zero_apply, repr_onePlus]
      calc ω = ω ^ (1 : Ordinal) := (opow_one ω).symm
        _ ≤ ω ^ (1 + repr b) := opow_le_opow_right omega0_pos le_self_add
    · rw [omegaMulV, if_neg ha]
      exact allTermsGe_vadd_iff.2
        ⟨omega0_le_veblen (Or.inl (fun h => ha (repr_eq_zero_iff.1 h))), allTermsGe_omegaMulV c⟩

/-! ### `−1 + x` -/

/-- **`−1 + x` on notations**: a positive finite notation goes down by one, `0` and every
infinite notation are fixed. -/
def predV : VNote → VNote
  | .zero => .zero
  | .vadd a b n c =>
      if a = 0 ∧ b = 0 then (if n = 1 then c else .vadd 0 0 (n - 1) c) else .vadd a b n c

theorem repr_predV : ∀ x : VNote, repr (predV x) = repr x - 1
  | .zero => by show repr (0 : VNote) = repr 0 - 1; rw [repr_zero, zero_sub]
  | .vadd a b n c => by
    by_cases h : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := h
      rw [predV, if_pos ⟨rfl, rfl⟩, repr_vadd, repr_zero, veblen_zero_apply, opow_zero, one_mul]
      by_cases hn : n = 1
      · rw [if_pos hn, hn, PNat.one_coe, Nat.cast_one, Ordinal.add_sub_cancel]
      · rw [if_neg hn, repr_vadd, repr_zero, veblen_zero_apply, opow_zero, one_mul]
        have h1 : 1 < n := lt_of_le_of_ne one_le (Ne.symm hn)
        have hsub : ((n - 1 : ℕ+) : ℕ) + 1 = (n : ℕ) := by
          rw [PNat.sub_coe, if_pos h1, PNat.one_coe]
          have : 1 < (n : ℕ) := h1
          omega
        symm
        apply sub_eq_of_add_eq
        rw [← add_assoc, ← hsub]
        push_cast
        rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
    · rw [predV, if_neg h]
      exact (sub_eq_of_add_eq (one_add_of_omega0_le (omega0_le_repr_vadd h))).symm

theorem nf_predV : ∀ {x : VNote}, NF x → NF (predV x)
  | .zero, _ => NF.zero
  | .vadd a b n c, hx => by
    by_cases h : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := h
      rw [predV, if_pos ⟨rfl, rfl⟩]
      by_cases hn : n = 1
      · rw [if_pos hn]; exact hx.tail
      · rw [if_neg hn]; exact NF.vadd hx.fst hx.snd hx.tail hx.snd_lt hx.tail_lt
    · rw [predV, if_neg h]; exact hx

end VNote

namespace Gamma0Note

/-! ### Basic order facts -/

/-- `0` is the least notation. -/
@[simp] theorem zero_le_note (x : Gamma0Note) : (0 : Gamma0Note) ≤ x := by
  rw [le_def, repr_zero]
  exact zero_le

theorem pos_iff_ne_zero' {x : Gamma0Note} : 0 < x ↔ x ≠ 0 :=
  ⟨ne_of_gt, fun h => lt_of_le_of_ne (zero_le_note x) (Ne.symm h)⟩

theorem one_le_of_pos {x : Gamma0Note} (h : 0 < x) : 1 ≤ x := by
  rw [lt_def, repr_zero] at h
  rw [le_def, repr_one]
  exact Order.one_le_iff_pos.2 h

@[simp] theorem ofNat_zero : ofNat 0 = 0 := rfl

@[simp] theorem ofNat_one : ofNat 1 = 1 := rfl

theorem ofNat_lt_ofNat_iff {m n : ℕ} : ofNat m < ofNat n ↔ m < n := by
  rw [lt_def, repr_ofNat, repr_ofNat]
  exact_mod_cast Iff.rfl

theorem ofNat_le_ofNat_iff {m n : ℕ} : ofNat m ≤ ofNat n ↔ m ≤ n := by
  rw [le_def, repr_ofNat, repr_ofNat]
  exact_mod_cast Iff.rfl

theorem ofNat_injective : Function.Injective ofNat := fun m n h => by
  have := congrArg repr h
  rw [repr_ofNat, repr_ofNat] at this
  exact_mod_cast this

@[simp] theorem ofNat_inj {m n : ℕ} : ofNat m = ofNat n ↔ m = n := ofNat_injective.eq_iff

theorem ofNat_eq_zero {n : ℕ} : ofNat n = 0 ↔ n = 0 := by
  rw [← ofNat_zero, ofNat_inj]

/-- **Below a finite notation every notation is finite.** -/
theorem eq_ofNat_of_lt_ofNat {x : Gamma0Note} {n : ℕ} (h : x < ofNat n) :
    ∃ m : ℕ, m < n ∧ x = ofNat m := by
  rw [lt_def, repr_ofNat] at h
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.1 (h.trans (Ordinal.natCast_lt_omega0 n))
  refine ⟨m, ?_, ?_⟩
  · rw [hm] at h; exact_mod_cast h
  · rw [← repr_inj, repr_ofNat, hm]

theorem ofNat_succ_eq_nadd_one (n : ℕ) : ofNat (n + 1) = nadd (ofNat n) 1 := by
  rw [← repr_inj, repr_nadd_one, repr_ofNat, repr_ofNat, Nat.cast_add, Nat.cast_one]

theorem one_le_ofNat {n : ℕ} (h : 1 ≤ n) : 1 ≤ ofNat n := by
  rw [← ofNat_one]; exact ofNat_le_ofNat_iff.2 h

theorem le_ofNat_of_lt_ofNat_succ {x : Gamma0Note} {n : ℕ} (h : x < ofNat (n + 1)) :
    x ≤ ofNat n := by
  obtain ⟨m, hm, rfl⟩ := eq_ofNat_of_lt_ofNat h
  exact ofNat_le_ofNat_iff.2 (Nat.lt_succ_iff.1 hm)

/-! ### `ω · x`, `−1 + x` and the blocks -/

/-- **`ω · x`.** -/
def omegaMulNote (x : Gamma0Note) : Gamma0Note := ⟨VNote.omegaMulV x.1, VNote.nf_omegaMulV x.2⟩

@[simp] theorem repr_omegaMulNote (x : Gamma0Note) : repr (omegaMulNote x) = ω * repr x :=
  VNote.repr_omegaMulV x.1

/-- **`−1 + x`.** -/
def predNote (x : Gamma0Note) : Gamma0Note := ⟨VNote.predV x.1, VNote.nf_predV x.2⟩

@[simp] theorem repr_predNote (x : Gamma0Note) : repr (predNote x) = repr x - 1 :=
  VNote.repr_predV x.1

/-- **The base of the level-`ℓ` rank block**, `ω · (−1 + ℓ)`. -/
def blk (ℓ : Gamma0Note) : Gamma0Note := omegaMulNote (predNote ℓ)

theorem repr_blk (ℓ : Gamma0Note) : repr (blk ℓ) = ω * (repr ℓ - 1) := by
  rw [blk, repr_omegaMulNote, repr_predNote]

/-- `blk ℓ` is a multiple of `ω`. -/
theorem powClosed_blk (ℓ : Gamma0Note) : PowClosed 1 (blk ℓ) := by
  show VNote.AllTermsGe (ω ^ repr 1) (VNote.omegaMulV (predNote ℓ).1)
  rw [repr_one, opow_one]
  exact VNote.allTermsGe_omegaMulV _

/-- The value of `blk ℓ ⊕ ω`. -/
theorem repr_blk_nadd_omega (ℓ : Gamma0Note) :
    repr (nadd (blk ℓ) (omegaPow 1)) = ω * (repr ℓ - 1) + ω := by
  rw [repr_nadd_omegaPow (powClosed_blk ℓ), repr_one, opow_one, repr_blk]

/-- **The top of the level-`ℓ` block**: the price of an open level-`ℓ` atom, `0` at level `0`. -/
def blkTop (ℓ : Gamma0Note) : Gamma0Note := if ℓ = 0 then 0 else nadd (blk ℓ) (omegaPow 1)

@[simp] theorem blkTop_zero : blkTop 0 = 0 := if_pos rfl

theorem blkTop_of_ne_zero {ℓ : Gamma0Note} (h : ℓ ≠ 0) :
    blkTop ℓ = nadd (blk ℓ) (omegaPow 1) := if_neg h

theorem blk_lt_blkTop {ℓ : Gamma0Note} (h : ℓ ≠ 0) : blk ℓ < blkTop ℓ := by
  rw [blkTop_of_ne_zero h, lt_def, repr_blk_nadd_omega, repr_blk]
  exact lt_add_of_pos_right _ omega0_pos

theorem blkTop_pos {ℓ : Gamma0Note} (h : ℓ ≠ 0) : 0 < blkTop ℓ :=
  lt_of_le_of_lt (zero_le_note _) (blk_lt_blkTop h)

/-- `κ < ℓ`, `κ ≠ 0` gives `−1 + κ < −1 + ℓ`. -/
theorem sub_one_lt_sub_one {κ ℓ : Ordinal} (hκ : κ ≠ 0) (h : κ < ℓ) : κ - 1 < ℓ - 1 := by
  have h1 : (1 : Ordinal) ≤ κ := Order.one_le_iff_ne_zero.2 hκ
  have h2 : (1 : Ordinal) ≤ ℓ := h1.trans h.le
  have e1 := Ordinal.add_sub_cancel_of_le h1
  have e2 := Ordinal.add_sub_cancel_of_le h2
  rw [← e1, ← e2] at h
  exact (add_lt_add_iff_left 1).1 h

/-- **A lower level's whole block sits below a higher level's base.** -/
theorem blkTop_le_blk {κ ℓ : Gamma0Note} (h : κ < ℓ) : blkTop κ ≤ blk ℓ := by
  by_cases hκ : κ = 0
  · rw [hκ, blkTop_zero]; exact zero_le_note _
  rw [blkTop_of_ne_zero hκ, le_def, repr_blk_nadd_omega, repr_blk, ← mul_add_one]
  refine mul_le_mul_right (Order.add_one_le_of_lt (sub_one_lt_sub_one ?_ h)) ω
  intro h0; exact hκ (repr_inj.1 (by rw [h0, repr_zero]))

theorem blkTop_lt_blkTop {κ ℓ : Gamma0Note} (h : κ < ℓ) : blkTop κ < blkTop ℓ :=
  lt_of_le_of_lt (blkTop_le_blk h) (blk_lt_blkTop (ne_of_gt (lt_of_le_of_lt (zero_le_note κ) h)))

theorem blkTop_mono {κ ℓ : Gamma0Note} (h : κ ≤ ℓ) : blkTop κ ≤ blkTop ℓ := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · exact le_of_lt (blkTop_lt_blkTop h)

/-- The base is monotone. -/
theorem blk_mono {κ ℓ : Gamma0Note} (h : κ ≤ ℓ) : blk κ ≤ blk ℓ := by
  rw [le_def, repr_blk, repr_blk]
  exact mul_le_mul_right (Ordinal.sub_le.2 ((le_def.1 h).trans (Ordinal.le_add_sub _ 1))) ω

/-- **`blkTop ℓ` is a limit.** -/
theorem succ_lt_blkTop {ℓ x : Gamma0Note} (h : x < blkTop ℓ) : nadd x 1 < blkTop ℓ := by
  by_cases hℓ : ℓ = 0
  · rw [hℓ, blkTop_zero] at h; exact absurd h (not_lt.2 (zero_le_note x))
  rw [blkTop_of_ne_zero hℓ] at h ⊢
  rw [lt_def, repr_blk_nadd_omega] at h ⊢
  rw [repr_nadd_one, ← Order.succ_eq_add_one]
  exact (Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0).succ_lt h

/-- **`blk ℓ` is a limit** (or `0`). -/
theorem succ_lt_blk {ℓ x : Gamma0Note} (h : x < blk ℓ) : nadd x 1 < blk ℓ := by
  rw [lt_def, repr_blk] at h ⊢
  have hpos : 0 < repr ℓ - 1 := by
    rcases (zero_le : 0 ≤ repr ℓ - 1).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at h; exact absurd h (not_lt.2 zero_le)
    · exact h0
  rw [repr_nadd_one, ← Order.succ_eq_add_one]
  exact (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hpos).succ_lt h

/-- `blk ℓ ⊕ k` never leaves the block. -/
theorem blk_nadd_ofNat_lt_blkTop {ℓ : Gamma0Note} (h : ℓ ≠ 0) (k : ℕ) :
    nadd (blk ℓ) (ofNat k) < blkTop ℓ := by
  rw [blkTop_of_ne_zero h, lt_def, repr_blk_nadd_omega, repr_nadd_ofNat, repr_blk]
  exact (add_lt_add_iff_left _).2 (Ordinal.natCast_lt_omega0 k)

theorem blk_le_nadd (ℓ x : Gamma0Note) : blk ℓ ≤ nadd (blk ℓ) x := le_nadd_left (blk ℓ) x

/-- **At a limit level every lower block lies below the base.** -/
theorem blkTop_lt_blk_of_limit {κ ℓ : Gamma0Note} (hℓ : ∀ μ < ℓ, nadd μ 1 < ℓ) (h : κ < ℓ) :
    blkTop κ < blk ℓ := by
  have h1 : nadd κ 1 < ℓ := hℓ κ h
  refine lt_of_le_of_lt (blkTop_le_blk (lt_nadd_one κ)) ?_
  rw [lt_def, repr_blk, repr_blk]
  refine (mul_lt_mul_iff_right₀ omega0_pos).2 (sub_one_lt_sub_one ?_ h1)
  rw [repr_nadd_one]
  exact (add_pos_of_right (α := Ordinal) (b := 1) (by exact_mod_cast Nat.one_pos) _).ne'

/-! ### The finite values -/

theorem natCast_succ_sub_one (n : ℕ) : ((n + 1 : ℕ) : Ordinal) - 1 = n := by
  apply sub_eq_of_add_eq
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.add_comm]

theorem repr_blk_ofNat_succ (n : ℕ) : repr (blk (ofNat (n + 1))) = ω * n := by
  rw [repr_blk, repr_ofNat, natCast_succ_sub_one]

theorem repr_blkTop_ofNat (n : ℕ) : repr (blkTop (ofNat n)) = ω * n := by
  rcases n with _ | n
  · rw [ofNat_zero, blkTop_zero, repr_zero, Nat.cast_zero, mul_zero]
  · rw [blkTop_of_ne_zero (fun h => Nat.succ_ne_zero n (ofNat_eq_zero.1 h)),
      repr_blk_nadd_omega, repr_ofNat, natCast_succ_sub_one, Nat.cast_add, Nat.cast_one,
      ← mul_add_one]

end Gamma0Note

end OrdinalAnalysis
