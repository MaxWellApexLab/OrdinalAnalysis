/-
  Natural (Hessenberg) sum on ordinal notations.

  Mathlib has `ONote.add`, which is ordinal addition and is therefore not
  commutative: `1 + ω = ω` while `ω + 1 > ω`.  Cut elimination needs the
  commutative sum, because the two premises of a cut enter symmetrically and
  neither may be allowed to absorb the other.

  Measured on mathlib at `edc39bf7bc` on 2026-08-31: `nadd` occurs zero times,
  there is no `NaturalOps` file, and "natural addition" appears in no file.
  (GitHub code search reports hits on master, but they are substring matches
  inside unrelated identifiers such as `AtomM` and `Arctan`.)

  On a Cantor normal form `ω ^ e₁ * n₁ + … + ω ^ e_k * n_k` with strictly
  decreasing exponents, the natural sum merges the two exponent lists and adds
  the coefficients of equal exponents.  That is what `nadd` below does.
-/
import Mathlib.SetTheory.Ordinal.Notation

namespace OrdinalAnalysis

open ONote

/-- A structural size for `ONote`.  `ONote` is declared with
`genSizeOfSpec false`, so the automatic `sizeOf` lemmas that a `termination_by`
on `sizeOf` would need are not available; this supplies the measure directly. -/
def nsize : ONote → ℕ
  | 0 => 0
  | oadd e _n a => nsize e + nsize a + 1

@[simp] theorem nsize_zero : nsize 0 = 0 := rfl

@[simp] theorem nsize_oadd (e : ONote) (_n : ℕ+) (a : ONote) :
    nsize (oadd e _n a) = nsize e + nsize a + 1 := rfl

/-- Natural (Hessenberg) sum of ordinal notations: merge the two Cantor normal
forms, adding coefficients at equal exponents.  Unlike `ONote.add` this is
commutative. -/
def nadd : ONote → ONote → ONote
  | 0, o => o
  | oadd e₁ n₁ a₁, 0 => oadd e₁ n₁ a₁
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂ =>
    match e₁.cmp e₂ with
    | Ordering.gt => oadd e₁ n₁ (nadd a₁ (oadd e₂ n₂ a₂))
    | Ordering.lt => oadd e₂ n₂ (nadd (oadd e₁ n₁ a₁) a₂)
    | Ordering.eq => oadd e₁ (n₁ + n₂) (nadd a₁ a₂)
  termination_by o₁ o₂ => nsize o₁ + nsize o₂
  decreasing_by all_goals (simp [nsize]; try omega)

@[inherit_doc] infixl:65 " ⊕ₙ " => nadd

@[simp] theorem zero_nadd (o : ONote) : nadd 0 o = o := by
  rw [nadd.eq_def]

@[simp] theorem nadd_zero (o : ONote) : nadd o 0 = o := by
  cases o with
  | zero => rw [nadd.eq_def]; rfl
  | oadd e n a => rw [nadd.eq_def]

/-! ### Commutativity

`ONote.cmp` is only shown to compare correctly under `NF` hypotheses
(`ONote.cmp_compares`), but it is *syntactically* antisymmetric: that follows
from the shape of its definition, with no normal-form assumption.  mathlib does
not state this, and it is what makes `nadd` commutative on the nose. -/

/-- `ONote.cmp` is antisymmetric as a function, before any normal-form
assumption. -/
theorem cmp_swap : ∀ a b : ONote, (a.cmp b).swap = b.cmp a
  | 0, 0 => rfl
  | 0, oadd _ _ _ => rfl
  | oadd _ _ _, 0 => rfl
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂ => by
      simp only [ONote.cmp, ← cmp_swap e₁ e₂, ← cmp_swap a₁ a₂,
        ← _root_.cmp_swap (n₁ : ℕ) n₂]
      cases e₁.cmp e₂ <;> cases _root_.cmp (n₁ : ℕ) (n₂ : ℕ) <;>
        cases a₁.cmp a₂ <;> rfl

theorem cmp_eq_gt_iff {a b : ONote} : a.cmp b = Ordering.gt ↔ b.cmp a = Ordering.lt := by
  constructor
  · intro h; rw [← cmp_swap a b, h]; rfl
  · intro h; rw [← cmp_swap b a, h]; rfl

theorem cmp_eq_eq_symm {a b : ONote} (h : a.cmp b = Ordering.eq) : b.cmp a = Ordering.eq := by
  rw [← cmp_swap a b, h]; rfl

/-- The natural sum is commutative.  Ordinary ordinal addition is not:
`1 + ω = ω` but `ω + 1 > ω`.  This is the property the cut-reduction lemma
needs, since the two premises of a cut enter symmetrically. -/
theorem nadd_comm : ∀ a b : ONote, nadd a b = nadd b a
  | 0, b => by simp
  | oadd _ _ _, 0 => by simp
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂ => by
      rw [nadd.eq_def, nadd.eq_def]
      rcases h : e₁.cmp e₂ with _ | _ | _
      · have h' : e₂.cmp e₁ = Ordering.gt := by
          rw [← cmp_swap e₁ e₂, h]; rfl
        simp only [h, h', nadd_comm (oadd e₁ n₁ a₁) a₂]
      · obtain rfl := eq_of_cmp_eq h
        simp only [h, nadd_comm a₁ a₂, add_comm n₁ n₂]
      · have h' : e₂.cmp e₁ = Ordering.lt := cmp_eq_gt_iff.mp h
        simp only [h, h', nadd_comm a₁ (oadd e₂ n₂ a₂)]
  termination_by a b => nsize a + nsize b
  decreasing_by all_goals (simp [nsize]; try omega)

/-! ### Normal form

Without this the operation is not an ordinal operation at all: `nadd` could
produce a term whose exponents are out of order, and `repr` of such a term is
not the sum of anything.  The shape follows mathlib's `ONote.add_nfBelow`. -/

theorem nadd_nfBelow {b : Ordinal} :
    ∀ {o₁ o₂ : ONote}, NFBelow o₁ b → NFBelow o₂ b → NFBelow (nadd o₁ o₂) b
  | 0, _, _, h₂ => by rw [zero_nadd]; exact h₂
  | oadd _ _ _, 0, h₁, _ => by rw [nadd_zero]; exact h₁
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ => by
      have hc : ((e₁.cmp e₂).Compares e₁ e₂) := @cmp_compares _ _ h₁.fst h₂.fst
      rw [nadd.eq_def]
      cases h : e₁.cmp e₂ <;> simp only [h] <;> rw [h] at hc
      · -- e₁ < e₂
        refine NFBelow.oadd h₂.fst ?_ h₂.lt
        exact nadd_nfBelow (NF.below_of_lt hc ⟨⟨_, h₁⟩⟩) h₂.snd
      · -- e₁ = e₂
        obtain rfl := hc
        exact NFBelow.oadd h₁.fst (nadd_nfBelow h₁.snd h₂.snd) h₁.lt
      · -- e₂ < e₁
        refine NFBelow.oadd h₁.fst ?_ h₁.lt
        exact nadd_nfBelow h₁.snd (NF.below_of_lt hc ⟨⟨_, h₂⟩⟩)
  termination_by o₁ o₂ => nsize o₁ + nsize o₂
  decreasing_by all_goals (simp [nsize]; try omega)

instance nadd_nf (o₁ o₂ : ONote) : ∀ [NF o₁] [NF o₂], NF (nadd o₁ o₂)
  | ⟨⟨b₁, h₁⟩⟩, ⟨⟨b₂, h₂⟩⟩ =>
    ⟨(le_total b₁ b₂).elim (fun h => ⟨b₂, nadd_nfBelow (h₁.mono h) h₂⟩) fun h =>
        ⟨b₁, nadd_nfBelow h₁ (h₂.mono h)⟩⟩

/-! ### Domination and monotonicity

The reduction lemma recurses on sub-derivations, whose ordinals are strictly
smaller, and reports the natural sum of the two.  For that bookkeeping to close
the natural sum has to dominate each summand.  Proved on `repr`, since
`ONote`'s order is defined through it. -/

theorem repr_le_nadd_left : ∀ (a b : ONote), NF a → NF b →
    ONote.repr a ≤ ONote.repr (nadd a b)
  | 0, b, _, _ => by simp
  | oadd e n a, 0, _, _ => by simp
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ => by
      have hc : ((e₁.cmp e₂).Compares e₁ e₂) := @cmp_compares _ _ h₁.fst h₂.fst
      rw [nadd.eq_def]
      cases h : e₁.cmp e₂ <;> simp only [h] <;> rw [h] at hc
      · -- e₁ < e₂ : the sum starts with the larger exponent
        have hlt : ONote.repr (oadd e₁ n₁ a₁) < ONote.repr (oadd e₂ n₂ a₂) :=
          @ONote.oadd_lt_oadd_1 _ _ _ _ _ _ h₁ hc
        have hstep : ONote.repr (oadd e₂ n₂ a₂)
            ≤ ONote.repr (oadd e₂ n₂ (nadd (oadd e₁ n₁ a₁) a₂)) := by
          have hr : ONote.repr a₂ ≤ ONote.repr (nadd (oadd e₁ n₁ a₁) a₂) := by
            have := repr_le_nadd_left a₂ (oadd e₁ n₁ a₁) h₂.snd h₁
            rwa [nadd_comm a₂ (oadd e₁ n₁ a₁)] at this
          simp only [ONote.repr]
          gcongr
        exact le_trans (le_of_lt hlt) hstep
      · -- e₁ = e₂ : coefficients add
        obtain rfl := eq_of_cmp_eq h
        have ih := repr_le_nadd_left a₁ a₂ h₁.snd h₂.snd
        simp only [ONote.repr]
        gcongr
        · exact_mod_cast Nat.le_add_right (n₁ : ℕ) (n₂ : ℕ)
      · -- e₂ < e₁ : the sum starts with e₁, the tail grows
        have ih := repr_le_nadd_left a₁ (oadd e₂ n₂ a₂) h₁.snd h₂
        simp only [ONote.repr]
        gcongr
  termination_by a b => nsize a + nsize b
  decreasing_by all_goals (simp [nsize]; try omega)

theorem repr_le_nadd_right (a b : ONote) (ha : NF a) (hb : NF b) :
    ONote.repr b ≤ ONote.repr (nadd a b) := by
  have := repr_le_nadd_left b a hb ha
  rwa [nadd_comm b a] at this

end OrdinalAnalysis
