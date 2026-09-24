/-
  Lower bounds at the transfinite level `ω^γ`, for an arbitrary notation index `γ`.

  `Ramified/TransfiniteLower.lean` proved the semiformal bound and the finitary bound at the
  levels `ω^n`, `n : ℕ` a numeral.  This file removes that restriction: `γ` ranges over an
  arbitrary `Gamma0Note` with `1 ≤ γ`, finite or transfinite.

  ## The rank bound of the block, at every `γ`

  The block base `blk ℓ = ω · (−1 + ℓ)` (`Ordinal/Veblen/OmegaMul.lean`) satisfies, at
  `ℓ = ω^γ` with `γ ≥ 1`,

      blk (ω^γ) = ω^{1 + γ},

  where `1 + γ` is *genuine* ordinal addition (`Ordinal.add`, left absorbing: `1 + γ = γ`
  once `γ ≥ ω`), **not** the natural sum `Gamma0Note.nadd`.  This is `onePlusNote`, the
  `Gamma0Note` wrapper of `Ordinal/Veblen/OmegaMul.lean`'s `VNote.onePlus`, and
  `blk_omegaPow` below is the exact transfinite generalisation of `TransfiniteLower.lean`'s
  `blk_omegaPow_ofNat`, by literally the same computation (no case split on `γ`).

  This value is *not* what predicative cut elimination consumes, though: `descend`
  (`Ramified/PredicativeCutGeneral.lean`) needs a cut rank below `ω^{e ⊕ 1}` for the
  *natural*-sum successor `e ⊕ 1 = Gamma0Note.nadd e 1`, which is the genuine order-theoretic
  successor of `e` (`Order.succ e`, always strictly above `e`) and does **not** collapse at
  infinite `e`.  So the two candidate readings of "`1 + γ`" that the design note leaves open
  really are different notations once `γ` is infinite:

  * `onePlusNote γ` (real `1 + γ`) is the *exact* value of `blk (ω^γ)`, and can equal `γ`
    itself;
  * `Gamma0Note.nadd γ 1` (real `γ + 1`, i.e. `γ ⊕ 1`) is always strictly above `γ`, and is
    the exponent the cut-elimination machinery is stated for.

  `onePlusNote γ ≤ nadd γ 1` always (`onePlusNote_le_nadd_one`, an ordinary ordinal fact,
  `1 + g ≤ g + 1`, proved by cases on `g < ω`), with equality exactly at finite `γ`.  So
  `blk (ω^γ) ≤ ω^{γ ⊕ 1}`, which is all `sf_lower_omegaPow'` needs to invoke
  `cutFree_below_omegaPow_succ` at `e := γ`; the height/segment bound is stated at
  `veblenNote (γ ⊕ 1) 0`, matching `TransfiniteLower.lean`'s `veblenNote (ofNat (n+1)) 0`
  once `γ = ofNat n` (`Gamma0Note.ofNat_succ_eq_nadd_one : ofNat (n+1) = nadd (ofNat n) 1`).

  ## The theorems

  * `sf_lower_omegaPow'` — **the semiformal bound at `ω^γ`**, any `γ ≥ 1`: no derivation of
    cut rank below `blk (ω^γ)` and height below `φ_{γ ⊕ 1}(0)` derives transfinite induction
    along the segment below `φ_{γ ⊕ 1}(0)`, with the junk literals among the axioms.  Proved
    exactly as `TransfiniteLower.lean`'s `sf_lower_omegaPow`, with `e := γ` fed straight into
    `cutFree_below_omegaPow_succ` (no `ofNat`-successor bookkeeping needed at all — that was
    only ever needed to *name* the successor, and `nadd γ 1` names it uniformly).
  * `sf_lower_omegaPow_ofNat'` — `sf_lower_omegaPow'` at `γ = ofNat n`, `n ≥ 1`, stated with
    the bound spelled `nadd (ofNat n) 1` throughout.  This is `TransfiniteLower.lean`'s
    `sf_lower_omegaPow` up to the (proved, non-definitional) renaming
    `ofNat (n+1) = nadd (ofNat n) 1`: the two statements agree because `CodedOrderR`/
    `vebSegOrderR` at a level depend only on that level's *value*, and the two spellings
    denote the same `Gamma0Note`.  (The reduction is not restated as a literal Lean `rw` on
    `sf_lower_omegaPow`'s conclusion: that conclusion's third `vebSegOrderR` argument is a
    proof of `0 < ofNat (n+1)`, so rewriting the index there is a rewrite under a dependent,
    non-`rfl` proof obligation, which is exactly the situation `rw` cannot discharge without
    reproving the surrounding term; restating with the same value under a different but
    provably-equal name is the honest way to record the agreement.)
  * `ramified_lower_bound_omegaPow'` — **the finitary bound**, `RAlt (ω^γ)` does not prove
    `TI` along the segment below `φ_{γ ⊕ 1}(0)`, any `γ ≥ 1`.  Sound but, as in
    `TransfiniteLower.lean`, not claimed to be attained for the finitary theory.
-/
import OrdinalAnalysis.Ramified.TransfiniteLower

set_option autoImplicit false

namespace OrdinalAnalysis

/-! ### An ordinal inequality: `1 + g ≤ g + 1`, with equality exactly at finite `g` -/

/-- **`1 + g ≤ g + 1`, for every ordinal `g`.**  Equality holds at finite `g` (both sides
compute the same natural-number sum); at infinite `g` the left side absorbs (`1 + g = g`)
while the right side is the genuine successor `Order.succ g > g`. -/
theorem one_add_le_add_one (g : Ordinal) : (1 : Ordinal) + g ≤ g + 1 := by
  by_cases hg : g < Ordinal.omega0
  · obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 hg
    apply le_of_eq
    rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
  · rw [not_lt] at hg
    rw [Ordinal.one_add_of_omega0_le hg, ← Order.succ_eq_add_one]
    exact le_of_lt (Order.lt_succ g)

namespace Gamma0Note

/-! ### `onePlusNote`: genuine ordinal `1 + x`, as a notation -/

/-- **`1 + x`, as a notation.**  The `Gamma0Note` wrapper of
`Ordinal/Veblen/OmegaMul.lean`'s `VNote.onePlus`, exactly as `omegaMulNote`/`predNote` wrap
`omegaMulV`/`predV` there: a finite notation goes up by one, an infinite one is fixed. -/
def onePlusNote (x : Gamma0Note) : Gamma0Note :=
  ⟨VNote.onePlus x.1, VNote.nf_onePlus x.2⟩

@[simp] theorem repr_onePlusNote (x : Gamma0Note) : repr (onePlusNote x) = 1 + repr x :=
  VNote.repr_onePlus x.1

theorem one_le_onePlusNote {γ : Gamma0Note} (hγ : (1 : Gamma0Note) ≤ γ) :
    (1 : Gamma0Note) ≤ onePlusNote γ := by
  rw [le_def, repr_onePlusNote]
  rw [le_def] at hγ
  exact hγ.trans le_add_self

/-- **`onePlusNote γ ≤ γ ⊕ 1` always.**  The gap between real `1 + γ` and the natural-sum
successor `γ ⊕ 1`, closed at every `γ` (not just finite `γ`). -/
theorem onePlusNote_le_nadd_one (γ : Gamma0Note) : onePlusNote γ ≤ Gamma0Note.nadd γ 1 := by
  rw [le_def, repr_onePlusNote, repr_nadd_one]
  exact one_add_le_add_one (repr γ)

/-! ### The base of the level-`ω^γ` block, at every `γ ≥ 1` -/

/-- **The base of the level-`ω^γ` block is `ω^{1+γ}`**, `γ ≥ 1`, `1+γ` genuine ordinal
addition (`onePlusNote`).  The exact transfinite generalisation of
`TransfiniteLower.lean`'s `blk_omegaPow_ofNat`: the same computation, with `repr γ` in place
of the numeral `n`, needs no case split on whether `γ` is finite. -/
theorem blk_omegaPow (γ : Gamma0Note) (hγ : (1 : Gamma0Note) ≤ γ) :
    blk (omegaPow γ) = omegaPow (onePlusNote γ) := by
  rw [← repr_inj, repr_blk, repr_omegaPow, repr_omegaPow, repr_onePlusNote]
  have hω : (Ordinal.omega0 : Ordinal.{0}) ≤ Ordinal.omega0 ^ repr γ := by
    calc (Ordinal.omega0 : Ordinal.{0}) = Ordinal.omega0 ^ (1 : Ordinal.{0}) :=
          (Ordinal.opow_one _).symm
      _ ≤ Ordinal.omega0 ^ repr γ :=
          Ordinal.opow_le_opow_right Ordinal.omega0_pos (by
            rw [le_def, repr_one] at hγ; exact hγ)
  rw [Ordinal.sub_eq_of_add_eq (Ordinal.one_add_of_omega0_le hω), omega0_mul_opow]

/-! ### `1 < ω^γ`, `ω^γ` a limit, and `ofNat k < ω^ζ`, for `γ, ζ ≥ 1` -/

/-- `1 < ω^γ`, `γ ≥ 1`. -/
theorem one_lt_omegaPow {γ : Gamma0Note} (hγ : (1 : Gamma0Note) ≤ γ) :
    (1 : Gamma0Note) < omegaPow γ := by
  have hpos : (0 : Gamma0Note) < γ := lt_of_lt_of_le zero_lt_one hγ
  rw [lt_def, repr_zero] at hpos
  rw [lt_def, repr_one, repr_omegaPow]
  exact Ordinal.one_lt_omega0.trans_le (Ordinal.left_le_opow _ hpos)

/-- **`ω^γ` is a limit level**, `γ ≥ 1`. -/
theorem omegaPow_limit {γ : Gamma0Note} (hγ : (1 : Gamma0Note) ≤ γ) :
    ∀ μ < omegaPow γ, nadd μ 1 < omegaPow γ :=
  fun _ hμ => nadd_lt_omegaPow hμ (one_lt_omegaPow hγ)

/-- Every finite notation lies below `ω^ζ`, `ζ ≥ 1`. -/
theorem ofNat_lt_omegaPow {ζ : Gamma0Note} (hζ : (1 : Gamma0Note) ≤ ζ) (k : ℕ) :
    ofNat k < omegaPow ζ := by
  have hpos : (0 : Gamma0Note) < ζ := lt_of_lt_of_le zero_lt_one hζ
  rw [lt_def, repr_zero] at hpos
  rw [lt_def, repr_ofNat, repr_omegaPow]
  exact (Ordinal.natCast_lt_omega0 k).trans_le (Ordinal.left_le_opow _ hpos)

/-! ### `0 < γ ⊕ 1` and `1 < γ ⊕ 1`, for `γ ≥ 1` -/

/-- `0 < γ ⊕ 1` always: `γ ⊕ 1` is `Order.succ`-shaped, so it is strictly above `γ ≥ 0`. -/
theorem zero_lt_nadd_one (γ : Gamma0Note) : (0 : Gamma0Note) < nadd γ 1 :=
  lt_of_le_of_lt (zero_le_note γ) (lt_nadd_one γ)

/-- `1 < γ ⊕ 1`, `γ ≥ 1`. -/
theorem one_lt_nadd_one {γ : Gamma0Note} (hγ : (1 : Gamma0Note) ≤ γ) :
    (1 : Gamma0Note) < nadd γ 1 := by
  rw [lt_def, repr_one, repr_nadd_one]
  rw [le_def, repr_one] at hγ
  rw [← Order.succ_eq_add_one]
  exact lt_of_le_of_lt hγ (Order.lt_succ (repr γ))

end Gamma0Note

namespace Ramified

open OrdinalAnalysis.Gamma0Note (veblenNote epsilonNote VeblenBelow)
open OrdinalAnalysis.Ramified.OmegaDerivableR (veblenIter veblenIter_lt_veblen)
open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### The semiformal bound at `ω^γ`, any `γ ≥ 1` -/

/-- **No derivation of cut rank below `blk (ω^γ) = ω^{1+γ}` and height below `φ_{γ⊕1}(0)`
derives transfinite induction along the segment below `φ_{γ⊕1}(0)`**, `γ ≥ 1`, with the junk
literals among the axioms.  The transfinite generalisation of `TransfiniteLower.lean`'s
`sf_lower_omegaPow`; see `sf_lower_omegaPow_ofNat'` for the reduction to that statement at
`γ = ofNat n`. -/
theorem sf_lower_omegaPow' (γ : Gamma0Note) (hγ : (1 : Gamma0Note) ≤ γ) {ρ h : Gamma0Note}
    (hρ : ρ < Gamma0Note.blk (Gamma0Note.omegaPow γ))
    (hh : h < veblenNote (Gamma0Note.nadd γ 1) 0) :
    ¬ OmegaDerivableR junkLitsR evInstR ρ h
      [evR (TIR (vebSegOrderR (Gamma0Note.nadd γ 1) 0
        (Gamma0Note.zero_lt_nadd_one γ)).prec)] := by
  intro hder
  have hρ0 : ρ < Gamma0Note.omegaPow (Gamma0Note.onePlusNote γ) := by
    rwa [Gamma0Note.blk_omegaPow γ hγ] at hρ
  have hρ' : ρ < Gamma0Note.omegaPow (Gamma0Note.nadd γ 1) :=
    lt_of_lt_of_le hρ0 (Gamma0Note.omegaPow_le_omegaPow (Gamma0Note.onePlusNote_le_nadd_one γ))
  obtain ⟨m, hd⟩ := cutFree_below_omegaPow_succ memFree_junkLitsR hγ hρ' hder
  have hβ : veblenIter γ m h < veblenNote (Gamma0Note.nadd γ 1) 0 :=
    veblenIter_lt_veblen (Gamma0Note.lt_nadd_one γ) 0 m h hh
  have : OrdinalNotation (VeblenBelow (Gamma0Note.nadd γ 1) 0) :=
    Gamma0Note.VeblenBelow.ordinalNotation _ _ (Gamma0Note.zero_lt_nadd_one γ)
  exact not_derivable_TI_R_junk _ (Below.mk _ hβ) (OmegaDerivableR.toBelow hd hβ)

/-- **`sf_lower_omegaPow` (`TransfiniteLower.lean`) is the special case `γ = ofNat n`** of
`sf_lower_omegaPow'`.  The bound `ofNat (n+1)` of that theorem and the bound
`nadd (ofNat n) 1` used here name the *same* notation
(`Gamma0Note.ofNat_succ_eq_nadd_one : ofNat (n+1) = nadd (ofNat n) 1`); this is
`sf_lower_omegaPow'` instantiated at `γ = ofNat n`, restated with the second spelling, which
is exactly what that instantiation produces. -/
theorem sf_lower_omegaPow_ofNat' {n : ℕ} (hn : 1 ≤ n) {ρ h : Gamma0Note}
    (hρ : ρ < Gamma0Note.blk (Gamma0Note.omegaPow (Gamma0Note.ofNat n)))
    (hh : h < veblenNote (Gamma0Note.nadd (Gamma0Note.ofNat n) 1) 0) :
    ¬ OmegaDerivableR junkLitsR evInstR ρ h
      [evR (TIR (vebSegOrderR (Gamma0Note.nadd (Gamma0Note.ofNat n) 1) 0
        (Gamma0Note.zero_lt_nadd_one (Gamma0Note.ofNat n))).prec)] :=
  sf_lower_omegaPow' (Gamma0Note.ofNat n) (Gamma0Note.one_le_ofNat hn) hρ hh

/-! ### The finitary bound, at `RAlt (ω^γ)`, any `γ ≥ 1` -/

/-- **`RAlt (ω^γ)` does not prove transfinite induction along the segment below
`φ_{γ⊕1}(0)`**, `γ ≥ 1`.  The transfinite generalisation of `TransfiniteLower.lean`'s
`ramified_lower_bound_omegaPow`; sound but, as there, not claimed to be attained for the
finitary theory. -/
theorem ramified_lower_bound_omegaPow' (γ : Gamma0Note) (hγ : (1 : Gamma0Note) ≤ γ) :
    RAlt (Gamma0Note.omegaPow γ) ⊬
      (Semiformula.univCl (TIR (vebSegOrderR (Gamma0Note.nadd γ 1) 0
        (Gamma0Note.zero_lt_nadd_one γ)).prec) : Sentence LRA) := by
  rintro ⟨h⟩
  set L := Gamma0Note.omegaPow γ with hLdef
  set C := vebSegOrderR (Gamma0Note.nadd γ 1) 0 (Gamma0Note.zero_lt_nadd_one γ) with hCdef
  have hL1 : 1 ≤ L := (Gamma0Note.one_lt_omegaPow hγ).le
  obtain ⟨ν, k, α, hν, hα, hd⟩ := provable_rank_height_of_exists (RAlt L)
    (fun τ hτ => RAlt_axiom_derivable_lt_epsilon hL1 τ hτ) h
  have hνL : ν < L := by
    rcases hν with rfl | ⟨τ, hτ, rfl⟩
    · exact lt_of_lt_of_le Gamma0Note.zero_lt_one hL1
    · exact lvlOf_emb_lt_of_mem_RAlt hL1 hτ
  have hρ : Gamma0Note.nadd (Gamma0Note.blkTop ν) (Gamma0Note.ofNat k) < Gamma0Note.blk L := by
    have h1 : Gamma0Note.blkTop ν < Gamma0Note.blk L :=
      Gamma0Note.blkTop_lt_blk_of_limit (Gamma0Note.omegaPow_limit hγ) hνL
    rw [hLdef, Gamma0Note.blk_omegaPow γ hγ] at h1 ⊢
    exact Gamma0Note.nadd_lt_omegaPow h1
      (Gamma0Note.ofNat_lt_omegaPow (Gamma0Note.one_le_onePlusNote hγ) k)
  have hαlt : α < veblenNote (Gamma0Note.nadd γ 1) 0 :=
    lt_trans hα (Gamma0Note.veblenNote_zero_lt_veblenNote_zero (Gamma0Note.one_lt_nadd_one hγ))
  have hemb : (Rewriting.emb (Semiformula.univCl (TIR C.prec)) : Proposition LRA) = TIR C.prec :=
    emb_univCl_of_freeVariables_eq_empty (CodedOrderR.freeVariables_TIR C)
  rw [hemb] at hd
  exact sf_lower_omegaPow' γ hγ hρ hαlt (hd.mono_lits trueArithLitsR_le_junkLitsR)

end Ramified

end OrdinalAnalysis
