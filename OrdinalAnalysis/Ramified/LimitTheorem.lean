/-
  The ordinal analysis of `RA_{<ω} = RAlt ω`, the theory of ramified analysis
  with names, equality and induction at every finite level, at `φ_2(0)`.

  `RAlt ω` is the union, over every finite `ν`, of the graded theories
  `RAlt (ν+1)` studied in `Ramified/UpperBound.lean`.  Its two-sided analysis sits
  exactly at the ordinal `φ_2(0)`, the first fixed point of `a ↦ ε_a`, i.e. the
  limit of the finite iteration of `φ_1` starting at `ε₀`.

  **Lower half** (`ramified_lower_bound_univ`).  A hypothetical `RAlt ω`-proof of
  `TI(≺_{φ_2(0)}, X)` unpacks, by `Theory.Proof.provable_iff`, into a raw `LK`
  derivation together with a *finite* list of axioms of `RAlt ω`.  Every such
  axiom has a finite level, so the list has a common finite level bound `ν`, and
  an axiom of level `≤ ν` already satisfies the level guard of `RAlt (ν+1)`
  (`mem_RAlt_of_mem_RAlt_of_lvl_lt`) — so the *same* derivation is a proof from
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
  `φ_2(0)` (`exists_lt_phiTwoZeroR`).  Monotonicity of `RAlt` in its level
  parameter (`RAlt_ofNat_weakerThan_omega`) then moves the `RAlt (ν+1)`-proof to
  `RAlt ω`, and from there to `RA Set.univ` (`ramified_upper_bound_RA_univ`).

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
instead of importing that (second-order) file, exactly as suggested
previously. -/

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

/-! ### The finite levels

`RA_{<ω}` is `RAlt ω`: every axiom has a finite level.  With notation levels,
`RA Set.univ` also contains names at every infinite level below `Γ₀`; the theory
of this file is the one with names, equality and induction at the finite levels
only. -/

/-- The level `ω`. -/
def omegaLv : Lv := Gamma0Note.omegaPow 1

/-- **Below `ω` exactly the finite levels.** -/
theorem lt_omegaLv_iff {μ : Lv} : μ < omegaLv ↔ ∃ n : ℕ, μ = Gamma0Note.ofNat n := by
  constructor
  · intro h
    rw [omegaLv, Gamma0Note.lt_def, Gamma0Note.repr_omegaPow, Gamma0Note.repr_one,
      Ordinal.opow_one] at h
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 h
    exact ⟨n, Gamma0Note.repr_inj.1 (by rw [hn, Gamma0Note.repr_ofNat])⟩
  · rintro ⟨n, rfl⟩
    rw [omegaLv, Gamma0Note.lt_def, Gamma0Note.repr_omegaPow, Gamma0Note.repr_one,
      Ordinal.opow_one, Gamma0Note.repr_ofNat]
    exact Ordinal.natCast_lt_omega0 n

theorem ofNat_lt_omegaLv (n : ℕ) : Gamma0Note.ofNat n < omegaLv := lt_omegaLv_iff.2 ⟨n, rfl⟩

theorem one_le_omegaLv : 1 ≤ omegaLv :=
  le_of_lt (by rw [← Gamma0Note.ofNat_one]; exact ofNat_lt_omegaLv 1)

/-! ### From `RA_{<ω}` down to `RAlt (ν+1)`, one finite proof at a time

A finite proof from `RAlt ω` only ever uses finitely many axioms, each of some
finite level; raised to any `ν` above all their levels, every one of them already
satisfies `RAlt (ν+1)`'s level guard. -/

/-- A finite list of axioms of `RAlt ω` has a common finite level bound. -/
private theorem exists_level_bound_list (Δ : List (Sentence LRA))
    (hΔ : ∀ τ ∈ Δ, τ ∈ RAlt omegaLv) :
    ∃ ν : ℕ, ∀ ψ ∈ Δ, lvlOf (Rewriting.emb ψ : Proposition LRA) ≤ Gamma0Note.ofNat ν := by
  induction Δ with
  | nil => exact ⟨0, by simp⟩
  | cons ψ Δ ih =>
      obtain ⟨ν, hν⟩ := ih (fun τ hτ => hΔ τ (List.mem_cons_of_mem _ hτ))
      obtain ⟨m, hm⟩ := lt_omegaLv_iff.1
        (lvlOf_emb_lt_of_mem_RAlt one_le_omegaLv (hΔ ψ List.mem_cons_self))
      refine ⟨max ν m, fun τ hτ => ?_⟩
      rcases List.mem_cons.mp hτ with rfl | hτ'
      · rw [hm]; exact Gamma0Note.ofNat_le_ofNat_iff.2 (le_max_right _ _)
      · exact le_trans (hν τ hτ') (Gamma0Note.ofNat_le_ofNat_iff.2 (le_max_left _ _))

/-- **An axiom of `RAlt L` of level `< ν` already lies in `RAlt ν`.**  Every
block of `RAlt L` is cut out by a level condition, which an individual axiom of
low level meets at `ν` as well. -/
theorem mem_RAlt_of_mem_RAlt_of_lvl_lt {L ν : Lv} {τ : Sentence LRA} (hτ : τ ∈ RAlt L)
    (hlvl : lvlOf (Rewriting.emb τ : Proposition LRA) < ν) : τ ∈ RAlt ν := by
  rcases hτ with ⟨hτ, -⟩ | hτ | ⟨φ, -, rfl⟩ | hτ
  · exact mem_RAlt_of_eq hτ hlvl
  · exact mem_RAlt_of_peanoMinus hτ
  · rw [lvlOf_emb_univCl, lvlOf_succInd] at hlvl
    exact induction_mem_RAlt φ hlvl
  · obtain ⟨μ, A, -, h0, hA, rfl | rfl⟩ := hτ
    · rw [lvlOf_emb_univCl, lvlOf_nameOutP hA] at hlvl
      exact naming_mem_RAlt ⟨μ, A, hlvl, h0, hA, Or.inl rfl⟩
    · rw [lvlOf_emb_univCl, lvlOf_nameInP hA] at hlvl
      exact naming_mem_RAlt ⟨μ, A, hlvl, h0, hA, Or.inr rfl⟩

/-- **`RAlt (ofNat n) ⪯ RAlt ω`**, for every `n`. -/
theorem RAlt_ofNat_weakerThan_omega (n : ℕ) : RAlt (Gamma0Note.ofNat n) ⪯ RAlt omegaLv :=
  RAlt_weakerThan (le_of_lt (ofNat_lt_omegaLv n))

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
theorem upper_M_at (b : Gamma0Note) (hM : M↓[LRA] ⊧* RAlt (Gamma0Note.ofNat (ν + 1)))
    (hν : 1 ≤ ν) {a c : Gamma0Note} (hc : c < epsilonNote 0) (hac : a < veblenIter 1 ν c) :
    (∀ x : M, (∀ y : M, precM y x ∧
        precM x (numVal M (gamma0Code b)) → XM y) → XM x) →
      ∀ y : M, precM y (numVal M (gamma0Code a)) ∧
        precM (numVal M (gamma0Code a)) (numVal M (gamma0Code b)) → XM y := by
  have hν1 : 1 ≤ Gamma0Note.ofNat (ν + 1) :=
    Gamma0Note.one_le_ofNat (Nat.succ_le_succ (Nat.zero_le ν))
  set B : M := numVal M (gamma0Code b)
  have h1 := level_one_M hM hν hc
  have hshape : Shape 1 (segGuardR b) :=
    shape_of_lvlOf_lt (by rw [lvlOf_segGuardR]; exact Gamma0Note.zero_lt_one)
  obtain ⟨w, hw⟩ := comprM hM Gamma0Note.zero_lt_one
    (by rw [← Gamma0Note.ofNat_one]; exact Gamma0Note.ofNat_lt_ofNat (by omega))
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
    RAlt (Gamma0Note.ofNat (ν + 1)) ⊢ tiUptoSegR b a := by
  have hν1 : 1 ≤ Gamma0Note.ofNat (ν + 1) :=
    Gamma0Note.one_le_ofNat (Nat.le_add_left 1 ν)
  refine provable_of_eqModels hν1 ?_ ?_
  · rw [tiUptoSegR, lvlOf_emb_univCl]
    have h0 : lvlOf (∼(Prog (precBelowR b)) ⋎
        (∀¹ (∼(precAt (precBelowR b) (#0 : Semiterm LRA ℕ 1)
          (numAtR (gamma0Code a))) ⋎ Xat (#0 : Semiterm LRA ℕ 1)))) = 0 := by
      simp [Prog, below, precAt, precBelowR, precCode₁R, lvlOf_lMap_toLRA]
    rw [h0]
    exact ofNat_pos' (Nat.succ_pos ν)
  · intro N _ sN _ hN
    rw [tiUptoSegR, models_iff_proposition]
    intro f
    exact (eval_tiUptoSegR_body b a f).mpr (upper_M_at b hN hν hc hac)

/-! ### The two headline theorems for `RA_{<ω}` at `φ_2(0)` -/

/-- **The provability half of the ordinal analysis of `RA_{<ω}`.**  For every
Veblen notation `a < φ_2(0)`, `RAlt ω` proves transfinite induction for `X`
along the coded Veblen ordering restricted to the segment below `φ_2(0)`, up to
`a`. -/
theorem ramified_upper_bound_univ (a : Gamma0Note) (ha : a < phiTwoZeroR) :
    RAlt omegaLv ⊢ tiUptoSegR phiTwoZeroR a := by
  obtain ⟨n, hn⟩ := exists_lt_phiTwoZeroR ha
  have han1 : a < veblenIter 1 (n + 1) (epsilonNote 0) :=
    lt_of_lt_of_le hn (veblenIter_one_le_succ n (epsilonNote 0))
  obtain ⟨c, hc, hac⟩ := exists_lt_veblenIter (n + 1) a han1
  have hderiv := ramified_upper_bound_at phiTwoZeroR (Nat.le_add_left 1 n) a c hc hac
  exact (RAlt_ofNat_weakerThan_omega (n + 2)).wk hderiv

/-- **The non-provability half of the ordinal analysis of `RA_{<ω}`.**  `RAlt ω`
does not prove transfinite induction along the coded Veblen ordering restricted to
the whole segment below `φ_2(0)`. -/
theorem ramified_lower_bound_univ :
    RAlt omegaLv ⊬ (Semiformula.univCl (TIR (precBelowR phiTwoZeroR)) : Sentence LRA) := by
  intro hp
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := RAlt_provable_iff.mp hp
  obtain ⟨ν0, hν0⟩ := exists_level_bound_list Δ hΔ
  set ν : ℕ := max ν0 1 with hνdef
  have hmem : ∀ τ ∈ Δ, τ ∈ RAlt (Gamma0Note.ofNat (ν + 1)) := fun τ hτ =>
    mem_RAlt_of_mem_RAlt_of_lvl_lt (hΔ τ hτ)
      (lt_of_le_of_lt (le_trans (hν0 τ hτ)
        (Gamma0Note.ofNat_le_ofNat_iff.2 (le_max_left _ _)))
        (Gamma0Note.ofNat_lt_ofNat (Nat.lt_succ_self ν)))
  have hRAlt : RAlt (Gamma0Note.ofNat (ν + 1)) ⊢
      (Semiformula.univCl (TIR (precBelowR phiTwoZeroR)) : Sentence LRA) :=
    RAlt_provable_iff.mpr ⟨Δ, hmem, ⟨d⟩⟩
  exact not_provable_TIR_of_cutFree (Gamma0Note.ofNat 2) 0 zero_lt_ofNat_two
    (veblenIter_le_phiTwoZeroR ν) hRAlt

/-- **The ordinal analysis of `RA_{<ω} = RAlt ω`, both halves**, at `φ_2(0)`:
`RAlt ω` proves transfinite induction for `X` along the segment ordering
`≺_{φ_2(0)}` up to every `a < φ_2(0)`, and does not prove transfinite induction for
`X` along the whole of `≺_{φ_2(0)}`. -/
theorem ramified_theorem_univ :
    (∀ a : Gamma0Note, a < phiTwoZeroR → RAlt omegaLv ⊢ tiUptoSegR phiTwoZeroR a) ∧
      RAlt omegaLv ⊬ (Semiformula.univCl (TIR (precBelowR phiTwoZeroR)) : Sentence LRA) :=
  ⟨ramified_upper_bound_univ, ramified_lower_bound_univ⟩

/-- The provability half survives in the theory with names at every level:
`RA Set.univ` proves everything `RAlt ω` does. -/
theorem ramified_upper_bound_RA_univ (a : Gamma0Note) (ha : a < phiTwoZeroR) :
    RA Set.univ ⊢ tiUptoSegR phiTwoZeroR a :=
  (Theory.Proof.weakerThan_of_le
    (Set.Subset.trans (RAlt_subset_RA omegaLv) (RA_subset (Set.subset_univ _)))).wk
    (ramified_upper_bound_univ a ha)

end Ramified

end OrdinalAnalysis
