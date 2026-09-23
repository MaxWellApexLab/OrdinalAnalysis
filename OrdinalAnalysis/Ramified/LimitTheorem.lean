/-
  The ordinal analysis of `RA_{<ω} = RA Set.univ`, the ungraded theory of ramified
  analysis with names at every finite level, at `φ_2(0)`.

  `RA Set.univ` is the union, over every level, of the graded theories `RAlt ν`
  studied in `Ramified/UpperBound.lean`.  Its two-sided analysis sits exactly at
  the ordinal `φ_2(0)`, the first fixed point of `a ↦ ε_a`, i.e. the limit of the
  finite iteration of `φ_1` starting at `ε₀`.

  **Lower half** (`ramified_lower_bound_univ`).  A hypothetical `RA Set.univ`-proof
  of `TI(≺_{φ_2(0)}, X)` unpacks, by `Theory.Proof.provable_iff`, into a raw `LK`
  derivation together with a *finite* list of axioms of `RA Set.univ`.  Every
  finite list has a common level bound `ν`, and an axiom of `RA Set.univ` whose own
  embedded level is `≤ ν` already satisfies the level guard of `RAlt (ν+1)`
  (`mem_RAlt_succ_of_mem_RA_univ`) — so the *same* derivation is a proof from
  `RAlt (ν+1)`.  Since `φ_1^ν(ε₀) ≤ φ_2(0)` for *every* `ν`
  (`veblenIter_le_phiTwoZeroR`, `φ_2(0)` being the supremum of the whole tower,
  not just cofinal with it), `Ramified/LowerBound.lean`'s
  `not_provable_TIR_of_cutFree` refutes this `RAlt (ν+1)`-proof outright, for
  whichever `ν` the finite proof happened to use.

  **Upper half** (`ramified_upper_bound_univ`).  `Ramified/UpperBound.lean`'s
  model argument (`upper_M`) never actually needs its "outer" segment bound `b` to
  coincide with the internal tower height `φ_1^ν(ε₀)` that drives the
  transfinite-induction step (`level_one_M`) — the two are connected only through
  the point `a` common to both, via `precM_trans`.  So the very same proof, with
  `b` left as a free parameter (`upper_M_at`, `ramified_upper_bound_at`), gives
  `RAlt (ν+1) ⊢ tiUptoSegR φ_2(0) a` directly, once `a` is known to lie below
  `φ_1^ν(ε₀)` for *some* `ν` — the ordinary cofinality of the `φ_1`-tower below
  `φ_2(0)` (`exists_lt_phiTwoZeroR`).  Monotonicity of `RAlt`/`RA` in their level
  parameter (`RAlt_weakerThan_RA_univ`) then moves the `RAlt (ν+1)`-proof to
  `RA Set.univ`.

  So no genuine "segment-bridging" implication between `tiUptoSegR b a` and
  `tiUptoSegR b' a` (for `a < b ≤ b'`) is needed: the outer bound of `upper_M`'s
  conclusion was never tied to its internal machinery in the first place.
-/
import OrdinalAnalysis.Ramified.UpperBound

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace OrdinalAnalysis

namespace Ramified

open OrdinalAnalysis.Gamma0Note (epsilonNote veblenNote)
open OrdinalAnalysis.Ramified.OmegaDerivableR (veblenIter veblenIter_zero)

/-! ### `φ_2(0)`, restated for the ramified calculus

This section is entirely about `Gamma0Note`/`Ordinal` arithmetic, and deliberately
does *not* open `LO`/`LO.FirstOrder`/`LO.FirstOrder.Arithmetic` (done further down,
just before the model-theoretic sections that need them): opening those together
with mathlib's ordinal fixed-point API confuses instance search for `Ordinal`'s
order structure.

`ACA/OmegaJumpUpperBound.lean` already has `phiTwoZero`/`repr_phiTwoZero`/
`exists_lt_epsIter`; we restate the ordinal and its cofinality directly here
instead of importing that (second-order) file, exactly as suggested by the task
note. -/

/-- The notation for `φ_2(0)`, the first fixed point of `a ↦ ε_a`. -/
def phiTwoZeroR : Gamma0Note := Gamma0Note.veblenNote (Gamma0Note.ofNat 2) 0

private theorem zero_lt_ofNat_two : (0 : Gamma0Note) < Gamma0Note.ofNat 2 := by
  rw [Gamma0Note.lt_def, Gamma0Note.repr_zero, Gamma0Note.repr_ofNat]
  norm_num

theorem repr_phiTwoZeroR : Gamma0Note.repr phiTwoZeroR = Ordinal.veblen 2 0 := by
  simp [phiTwoZeroR]

/-- `φ_2(0) = nfp (φ_1) 0`: mathlib's own spelling of the first fixed point. -/
theorem phiTwoZeroR_eq_nfp :
    Gamma0Note.repr phiTwoZeroR = Ordinal.nfp (Ordinal.veblen 1) 0 := by
  rw [repr_phiTwoZeroR, show (2 : Ordinal) = 1 + 1 from one_add_one_eq_two.symm,
    Ordinal.veblen_add_one, Ordinal.deriv_zero_right]

private theorem epsilon_zero_eq_veblen_one_zero : Ordinal.epsilon 0 = Ordinal.veblen 1 0 := rfl

/-- **Every `a < φ_2(0)` lies below some finite iterate `φ_1^n(ε₀)`.**  The
cofinality of the `φ_1`-tower in its own supremum. -/
theorem exists_lt_phiTwoZeroR {a : Gamma0Note} (ha : a < phiTwoZeroR) :
    ∃ n : ℕ, a < veblenIter 1 n (epsilonNote 0) := by
  have ha' : Gamma0Note.repr a < Ordinal.nfp (Ordinal.veblen 1) 0 :=
    phiTwoZeroR_eq_nfp ▸ Gamma0Note.lt_def.mp ha
  obtain ⟨n, hn⟩ := Ordinal.lt_nfp_iff.mp ha'
  refine ⟨n, Gamma0Note.lt_def.mpr ?_⟩
  rw [repr_veblenIter_one, Gamma0Note.epsilonNote_zero_repr]
  exact lt_of_lt_of_le hn ((isNormal_iterate_veblen_one n).monotone _root_.zero_le)

/-- **`φ_1^ν(ε₀) ≤ φ_2(0)` for every `ν`**: `φ_2(0)` is not just cofinal with the
`φ_1`-tower, it is an upper bound of every one of its finite stages. -/
theorem veblenIter_le_phiTwoZeroR (ν : ℕ) :
    veblenIter 1 ν (epsilonNote 0) ≤ phiTwoZeroR := by
  have h : Gamma0Note.repr (veblenIter 1 ν (epsilonNote 0)) ≤ Ordinal.nfp (Ordinal.veblen 1) 0 := by
    rw [repr_veblenIter_one, Gamma0Note.epsilonNote_zero_repr, epsilon_zero_eq_veblen_one_zero,
      ← Function.iterate_succ_apply]
    exact Ordinal.iterate_le_nfp (Ordinal.veblen 1) 0 (ν + 1)
  exact Gamma0Note.le_def.mpr (phiTwoZeroR_eq_nfp ▸ h)

/-- `φ_1` iterated one more time only grows. -/
theorem veblenIter_one_le_succ (n : ℕ) (x : Gamma0Note) :
    veblenIter 1 n x ≤ veblenIter 1 (n + 1) x := by
  rw [veblenIter_succ']
  exact Gamma0Note.le_veblenNote_right 1 _

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)

/-! ### From `RA Set.univ` down to `RAlt (ν+1)`, one finite proof at a time

A finite proof from `RA Set.univ` only ever uses finitely many axioms, each of some
level; raised to any `ν` above all their levels, every one of them already
satisfies `RAlt (ν+1)`'s level guard (`Theory.lean`'s `lvlOf_emb_lt_of_mem_RAlt`
runs the same case split in the other direction). -/

/-- A finite list of sentences has a common level bound (of their `emb` images).
Restates `LowerBound.lean`'s private `exists_level_bound` here, since that lemma
belongs to this file's argument just as much and is not exported. -/
private theorem exists_level_bound_list (Δ : List (Sentence LRA)) :
    ∃ ν : Lv, ∀ ψ ∈ Δ, lvlOf (Rewriting.emb ψ : Proposition LRA) ≤ ν := by
  induction Δ with
  | nil => exact ⟨0, by simp⟩
  | cons ψ Δ ih =>
      obtain ⟨ν, hν⟩ := ih
      refine ⟨max ν (lvlOf (Rewriting.emb ψ : Proposition LRA)), fun τ hτ => ?_⟩
      rcases List.mem_cons.mp hτ with rfl | hτ'
      · exact le_max_right _ _
      · exact le_trans (hν τ hτ') (le_max_left _ _)

/-- **An axiom of `RA Set.univ` of level `≤ ν` already lies in `RAlt (ν+1)`.**  Every
block of `RA Set.univ` widens the corresponding block of `RAlt (ν+1)` only by
dropping its level guard, so an individual axiom that happens to have low level
qualifies regardless. -/
private theorem mem_RAlt_succ_of_mem_RA_univ {ν : Lv} {τ : Sentence LRA} (hτ : τ ∈ RA Set.univ)
    (hlvl : lvlOf (Rewriting.emb τ : Proposition LRA) ≤ ν) : τ ∈ RAlt (ν + 1) := by
  rcases hτ with hτ | hτ | hτ | hτ
  · exact mem_RAlt_of_eq hτ (Nat.lt_succ_of_le hlvl)
  · exact mem_RAlt_of_peanoMinus hτ
  · obtain ⟨φ, -, rfl⟩ := hτ
    rw [lvlOf_emb_univCl, lvlOf_succInd] at hlvl
    exact induction_mem_RAlt φ (Nat.lt_succ_of_le hlvl)
  · obtain ⟨μ, A, -, h0, hA, rfl | rfl⟩ := hτ
    · rw [lvlOf_emb_univCl, lvlOf_nameOutP hA] at hlvl
      exact naming_mem_RAlt ⟨μ, A, Nat.lt_succ_of_le hlvl, h0, hA, Or.inl rfl⟩
    · rw [lvlOf_emb_univCl, lvlOf_nameInP hA] at hlvl
      exact naming_mem_RAlt ⟨μ, A, Nat.lt_succ_of_le hlvl, h0, hA, Or.inr rfl⟩

/-- **`RAlt ν ⪯ RA Set.univ`**, for every `ν`. -/
private theorem RAlt_weakerThan_RA_univ (ν : Lv) : RAlt ν ⪯ RA Set.univ :=
  Theory.Proof.weakerThan_of_le (Set.Subset.trans (RAlt_subset_RA ν) (RA_subset (Set.subset_univ _)))

/-! ### The upper bound at an arbitrary outer segment, in a model

`UpperBound.lean`'s `upper_M` ties its outer segment bound to the exact height
`veblenIter 1 ν (epsilonNote 0)` its cofinality step produces; but the proof never
uses that coincidence beyond obtaining `(c, hc, hac)`.  With that triple supplied
directly, the outer bound `b` is free. -/

section Model

variable {M : Type} [Nonempty M] [s : Structure LRA M] [Structure.Eq LRA M] {ν : ℕ}

/-- **The upper bound in a model, at an arbitrary outer segment `b`.**  Verbatim
`upper_M`, with the outer bound generalised from `veblenIter 1 ν (epsilonNote 0)`
to any `b`, and the cofinal witness `(c, hc, hac)` taken as a hypothesis instead of
being produced by `exists_lt_veblenIter` from `a < veblenIter 1 ν (epsilonNote 0)`. -/
theorem upper_M_at (b : Gamma0Note) (hM : M↓[LRA] ⊧* RAlt (ν + 1)) (hν : 1 ≤ ν)
    {a c : Gamma0Note} (hc : c < epsilonNote 0) (hac : a < veblenIter 1 ν c) :
    (∀ x : M, (∀ y : M, precM y x ∧
        precM x (numVal M (gamma0Code b)) → XM y) → XM x) →
      ∀ y : M, precM y (numVal M (gamma0Code a)) ∧
        precM (numVal M (gamma0Code a)) (numVal M (gamma0Code b)) → XM y := by
  have hν1 : 1 ≤ ν + 1 := Nat.succ_le_succ (Nat.zero_le ν)
  set B : M := numVal M (gamma0Code b)
  have h1 := level_one_M hM hν hc
  have hshape : Shape 1 (segGuardR b) :=
    shape_of_lvlOf_lt (by rw [lvlOf_segGuardR]; exact Nat.one_pos)
  obtain ⟨w, hw⟩ := comprM hM Nat.one_pos (Nat.succ_lt_succ (lt_of_lt_of_le Nat.zero_lt_one hν))
    hshape (Classical.arbitrary M)
  have hG : ∀ x, memM 1 x w ↔ (precM x B → XM x) := fun x =>
    (hw x).trans (eval_segGuardR _ x _)
  have hTI := (TIupM_congr hG _).mp (h1 w)
  intro hprog y hy
  have hprogG : ProgM (fun x : M => precM x B → XM x) := fun x hx hxB =>
    hprog x fun y hy' => hx y hy'.1 (precM_trans hM hν1 hy'.1 hxB)
  have hAc := precM_code (M := M) hM hν1 hac
  exact hTI hprogG y (precM_trans hM hν1 hy.1 hAc) (precM_trans hM hν1 hy.1 hy.2)

end Model

/-- **`RAlt (ν+1)` proves TI along `≺_b` up to `a`**, for an arbitrary outer segment
`b`, given a cofinal witness `c < ε₀` with `a < φ_1^ν(c)`.  Verbatim
`ramified_upper_bound`, with the outer bound generalised. -/
theorem ramified_upper_bound_at (b : Gamma0Note) {ν : ℕ} (hν : 1 ≤ ν) (a c : Gamma0Note)
    (hc : c < epsilonNote 0) (hac : a < veblenIter 1 ν c) :
    RAlt (ν + 1) ⊢ tiUptoSegR b a := by
  have hν1 : 1 ≤ ν + 1 := Nat.le_add_left 1 ν
  refine provable_of_eqModels hν1 ?_ ?_
  · rw [tiUptoSegR, lvlOf_emb_univCl]
    have h0 : lvlOf (∼(Prog (precBelowR b)) ⋎
        (∀¹ (∼(precAt (precBelowR b) (#0 : Semiterm LRA ℕ 1)
          (numAtR (gamma0Code a))) ⋎ Xat (#0 : Semiterm LRA ℕ 1)))) = 0 := by
      simp [Prog, below, precAt, precBelowR, precCode₁R, lvlOf_lMap_toLRA]
    rw [h0]
    exact Nat.succ_pos ν
  · intro N _ sN _ hN
    rw [tiUptoSegR, models_iff_proposition]
    intro f
    exact (eval_tiUptoSegR_body b a f).mpr (upper_M_at b hN hν hc hac)

/-! ### The two headline theorems for `RA Set.univ` at `φ_2(0)` -/

/-- **The provability half of the ordinal analysis of `RA_{<ω}`.**  For every
Veblen notation `a < φ_2(0)`, `RA Set.univ` proves transfinite induction for `X`
along the coded Veblen ordering restricted to the segment below `φ_2(0)`, up to
`a`. -/
theorem ramified_upper_bound_univ (a : Gamma0Note) (ha : a < phiTwoZeroR) :
    RA Set.univ ⊢ tiUptoSegR phiTwoZeroR a := by
  obtain ⟨n, hn⟩ := exists_lt_phiTwoZeroR ha
  have han1 : a < veblenIter 1 (n + 1) (epsilonNote 0) :=
    lt_of_lt_of_le hn (veblenIter_one_le_succ n (epsilonNote 0))
  obtain ⟨c, hc, hac⟩ := exists_lt_veblenIter (n + 1) a han1
  have hderiv := ramified_upper_bound_at phiTwoZeroR (Nat.le_add_left 1 n) a c hc hac
  exact (RAlt_weakerThan_RA_univ (n + 2)).wk hderiv

/-- **The non-provability half of the ordinal analysis of `RA_{<ω}`.**  `RA Set.univ`
does not prove transfinite induction along the coded Veblen ordering restricted to
the whole segment below `φ_2(0)`. -/
theorem ramified_lower_bound_univ :
    RA Set.univ ⊬ (Semiformula.univCl (TIR (precBelowR phiTwoZeroR)) : Sentence LRA) := by
  intro hp
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := RA_provable_iff.mp hp
  obtain ⟨ν0, hν0⟩ := exists_level_bound_list Δ
  set ν : Lv := max ν0 1 with hνdef
  have hmem : ∀ τ ∈ Δ, τ ∈ RAlt (ν + 1) := fun τ hτ =>
    mem_RAlt_succ_of_mem_RA_univ (hΔ τ hτ) (le_trans (hν0 τ hτ) (le_max_left _ _))
  have hRAlt : RAlt (ν + 1) ⊢ (Semiformula.univCl (TIR (precBelowR phiTwoZeroR)) : Sentence LRA) :=
    RAlt_provable_iff.mpr ⟨Δ, hmem, ⟨d⟩⟩
  exact not_provable_TIR_of_cutFree (Gamma0Note.ofNat 2) 0 zero_lt_ofNat_two
    (veblenIter_le_phiTwoZeroR ν) hRAlt

/-- **The ordinal analysis of `RA_{<ω} = RA Set.univ`, both halves**, at `φ_2(0)`:
`RA Set.univ` proves transfinite induction for `X` along the segment ordering
`≺_{φ_2(0)}` up to every `a < φ_2(0)`, and does not prove transfinite induction for
`X` along the whole of `≺_{φ_2(0)}`. -/
theorem ramified_theorem_univ :
    (∀ a : Gamma0Note, a < phiTwoZeroR → RA Set.univ ⊢ tiUptoSegR phiTwoZeroR a) ∧
      RA Set.univ ⊬ (Semiformula.univCl (TIR (precBelowR phiTwoZeroR)) : Sentence LRA) :=
  ⟨ramified_upper_bound_univ, ramified_lower_bound_univ⟩

end Ramified

end OrdinalAnalysis
