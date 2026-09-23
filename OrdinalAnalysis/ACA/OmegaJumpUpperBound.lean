/-
  The ε-jump in `ACA^+`, and the upper bound `|ACA^+| ≥ φ_2(0)`.

  **The ε-jump** (`epsJump_plus`): if `ACA^+` proves transfinite induction along `≺₁`
  up to `b̄` for all sets, it proves it up to `ε̄_b` for all sets.  Let `Z` be a set and
  `Y` its omega-jump (`omegaJumpAxiom`, `ACA/OmegaJump.lean`).

  1. The formula `χ_Y(g) :≡ ∀u (Eps(u,g) → ∀j TI(≺₁, col_j Y, u))` is arithmetical in
     `Y`, so `∀²X TI(≺₁, b̄, X)` instantiated at it (the `exs₂` rule, i.e. arithmetical
     comprehension) gives `TI(≺₁, χ_Y, b̄)`.
  2. `ACA/OmegaJumpProg.lean`'s `colEpsJump_lifted` turns this, under the step condition
     of the omega-jump, into `TI(≺₁, col_0 Y, ε̄_b)`.
  3. The base condition `∀x (x ∈ col_0 Y ↔ x ∈ Z)` and the extensionality of
     transfinite induction in its parameter (`tiExt`) give `TI(≺₁, Z, ε̄_b)`.

  `tiExt` is the one genuinely second-order derivation here: its two parameters are
  liftings of first-order formulas at *different* set variables, so it cannot come
  from a single lifted `PA[X]`-theorem.  It is a short sequent derivation
  (`Prog(Ψ₂) → Prog(Ψ₁)` and `Below(Ψ₁, ū) → Below(Ψ₂, ū)`, one eigenvariable each).
  The bookkeeping of the two free set variables `Y := 0`, `Z := 1` when the axiom
  `∀Z ∃Y` is opened is done once, by `app_toSOAtB_of`: a second-order rewriting of a
  lifted formula is the lifting at the rewritten witness.

  **The upper bound** (`aca_plus_upper_bound`): starting from `ACA ⊢ ∀²X TI(≺₁, ε̄₀, X)`
  (`EpsProg.ti_epsilon_all`), `n` ε-jumps give the ε-tower `ε₀, ε_{ε₀}, ...` (`epsIter`),
  which is cofinal in `φ_2(0) = sup_n (a ↦ ε_a)^n(0)` (`exists_lt_epsIter`, from
  `veblen 2 = deriv (veblen 1)` and `deriv f 0 = nfp f 0`).  The segment bridge of
  `ACA/SegmentBridge.lean`, generalised from `ε_{ε₀}` to the segment below an
  arbitrary `ε_e` (`SegBridgeE`), turns `∀²X TI(≺₁, b̄, X)` into transfinite induction
  along `EpsilonSegmentOrder.precCodeSeg e` below any `ā ≺ b̄`: this is the sentence
  `tiUptoSegSO₂ e a`, of which `ACA/TI.lean`'s `tiUptoSegSO a` is the case `e = ε₀`.
  With `e := φ_2(0)` the ordering is `EpsilonSegmentOrder.epsilonOrder φ_2(0)`, the
  notations below `ε_{φ_2(0)} = φ_2(0)`, the ordering of the corresponding lower bound.
-/
import OrdinalAnalysis.ACA.OmegaJumpProg
import OrdinalAnalysis.ACA.SegmentBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX Xat paLX)
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁ freeVariables_precCode₁)

/-! ### Transfinite induction is extensional in its parameter -/

section TIExt

/-- `Ψ(t)`, for the lifting `Ψ` of `φ` at the witness `w`. -/
def fAt {n : ℕ} (w : Semiformula ℒₒᵣ ℕ Empty 0 1) (φ : FirstOrder.Semiformula LX ℕ 1)
    (t : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  toSOAtB w (Gentzen.formulaAt φ t)

/-- `Below(Ψ, t)`. -/
def bAt {n : ℕ} (w : Semiformula ℒₒᵣ ℕ Empty 0 1) (φ : FirstOrder.Semiformula LX ℕ 1)
    (t : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  toSOAtB w (Gentzen.belowAt precCode₁ φ t)

/-- `Prog(Ψ)`. -/
def pAt {n : ℕ} (w : Semiformula ℒₒᵣ ℕ Empty 0 1) (φ : FirstOrder.Semiformula LX ℕ 1) :
    Semiproposition ℒₒᵣ 0 n :=
  toSOAtB w (Gentzen.progAt precCode₁ φ)

/-- `y ≺₁ x`, lifted (the lifting does not depend on the witness). -/
def rAt {n : ℕ} (y x : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  toSOAtB segWitness (Gentzen.precAt precCode₁ y x)

theorem precAt_indep (w : Semiformula ℒₒᵣ ℕ Empty 0 1) {n : ℕ}
    (y x : FirstOrder.Semiterm LX ℕ n) :
    (toSOAtB w (Gentzen.precAt precCode₁ y x) : Semiproposition ℒₒᵣ 0 n) = rAt y x := by
  simp only [rAt, toSOAtB_precAt, toSOAtB_precCode₁]

section Rew

variable {n₁ n₂ : ℕ} {ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂} {ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂}
  (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
include hb hf

theorem rew_fAt (w : Semiformula ℒₒᵣ ℕ Empty 0 1) {φ : FirstOrder.Semiformula LX ℕ 1}
    (hφ : φ.freeVariables = ∅) (t : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ fAt w φ t = fAt w φ (ω t) := by
  rw [fAt, fAt, ← toSOAtB_rew hb hf, TowerSyntax.rew_formulaAt hφ]

theorem rew_bAt (w : Semiformula ℒₒᵣ ℕ Empty 0 1) {φ : FirstOrder.Semiformula LX ℕ 1}
    (hφ : φ.freeVariables = ∅) (t : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ bAt w φ t = bAt w φ (ω t) := by
  rw [bAt, bAt, ← toSOAtB_rew hb hf, TowerSyntax.rew_belowAt freeVariables_precCode₁ hφ]

theorem rew_pAt (w : Semiformula ℒₒᵣ ℕ Empty 0 1) {φ : FirstOrder.Semiformula LX ℕ 1}
    (hφ : φ.freeVariables = ∅) :
    ω' ▹ (pAt w φ : Semiproposition ℒₒᵣ 0 n₁) = (pAt w φ : Semiproposition ℒₒᵣ 0 n₂) := by
  rw [pAt, pAt, ← toSOAtB_rew hb hf, TowerSyntax.rew_progAt freeVariables_precCode₁ hφ]

theorem rew_rAt (y x : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ rAt y x = rAt (ω y) (ω x) := by
  rw [rAt, rAt, ← toSOAtB_rew hb hf, TowerSyntax.rew_precAt' freeVariables_precCode₁]

end Rew

theorem bAt_eq (w : Semiformula ℒₒᵣ ℕ Empty 0 1) (φ : FirstOrder.Semiformula LX ℕ 1) {n : ℕ}
    (b : FirstOrder.Semiterm LX ℕ n) :
    bAt w φ b = ∀¹ (∼(rAt (#0 : FirstOrder.Semiterm LX ℕ (n + 1)) (FirstOrder.Rew.bShift b)) ⋎
      fAt w φ (#0 : FirstOrder.Semiterm LX ℕ (n + 1))) := by
  show toSOAtB w (∀¹ (∼(Gentzen.precAt precCode₁ (#0 : FirstOrder.Semiterm LX ℕ (n + 1))
    (FirstOrder.Rew.bShift b)) ⋎ Gentzen.formulaAt φ #0)) = _
  rw [toSOAtB_all, toSOAtB_or, toSOAtB_neg, precAt_indep]
  rfl

theorem pAt_eq (w : Semiformula ℒₒᵣ ℕ Empty 0 1) (φ : FirstOrder.Semiformula LX ℕ 1) {n : ℕ} :
    (pAt w φ : Semiproposition ℒₒᵣ 0 n) =
      ∀¹ (∼(bAt w φ (#0 : FirstOrder.Semiterm LX ℕ (n + 1))) ⋎
        fAt w φ (#0 : FirstOrder.Semiterm LX ℕ (n + 1))) := by
  show toSOAtB w (∀¹ (∼(Gentzen.belowAt precCode₁ φ (#0 : FirstOrder.Semiterm LX ℕ (n + 1))) ⋎
    Gentzen.formulaAt φ #0)) = _
  rw [toSOAtB_all, toSOAtB_or, toSOAtB_neg]
  rfl

theorem ti_eq (w : Semiformula ℒₒᵣ ℕ Empty 0 1) (φ : FirstOrder.Semiformula LX ℕ 1) {n : ℕ}
    (a : FirstOrder.Semiterm LX ℕ n) :
    toSOAtB w (Gentzen.tiUptoAt precCode₁ φ a) = ∼(pAt w φ) ⋎ bAt w φ a := by
  show toSOAtB w (∼(Gentzen.progAt precCode₁ φ) ⋎ Gentzen.belowAt precCode₁ φ a) = _
  rw [toSOAtB_or, toSOAtB_neg]
  rfl

theorem neg_bAt_eq (w : Semiformula ℒₒᵣ ℕ Empty 0 1) (φ : FirstOrder.Semiformula LX ℕ 1) {n : ℕ}
    (b : FirstOrder.Semiterm LX ℕ n) :
    ∼(bAt w φ b) = ∃¹ (rAt (#0 : FirstOrder.Semiterm LX ℕ (n + 1)) (FirstOrder.Rew.bShift b) ⋏
      ∼(fAt w φ (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))) := by
  rw [bAt_eq]
  show ∃¹ ((∼∼(rAt (#0 : FirstOrder.Semiterm LX ℕ (n + 1)) (FirstOrder.Rew.bShift b))) ⋏
    ∼(fAt w φ (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))) = _
  rw [Semiformula.neg_neg]

theorem neg_pAt_eq (w : Semiformula ℒₒᵣ ℕ Empty 0 1) (φ : FirstOrder.Semiformula LX ℕ 1) {n : ℕ} :
    ∼(pAt w φ : Semiproposition ℒₒᵣ 0 n) =
      ∃¹ (bAt w φ (#0 : FirstOrder.Semiterm LX ℕ (n + 1)) ⋏
        ∼(fAt w φ (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))) := by
  rw [pAt_eq]
  show ∃¹ ((∼∼(bAt w φ (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))) ⋏
    ∼(fAt w φ (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))) = _
  rw [Semiformula.neg_neg]

/-- The extensionality hypothesis `∀x (Ψ₁(x) ↔ Ψ₂(x))`. -/
def extHyp (w₁ w₂ : Semiformula ℒₒᵣ ℕ Empty 0 1) (φ₁ φ₂ : FirstOrder.Semiformula LX ℕ 1) :
    Proposition ℒₒᵣ :=
  ∀¹ ((toSOAtB w₁ φ₁ : Semiproposition ℒₒᵣ 0 1) 🡘 toSOAtB w₂ φ₂)

section Terms

theorem free_bvar_zero_LX : (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0)
    (#0 : FirstOrder.Semiterm LX ℕ 1) = &0 := by
  rw [show (0 : Fin 1) = Fin.last 0 from rfl]
  exact FirstOrder.Rew.free_bvar_last

theorem hb_subst_z0 : ∀ i,
    unTerm ((FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm LX ℕ 0)]) #i) =
      (FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)]) #i := by
  intro i
  fin_cases i
  simp

theorem hf_subst_z0 : ∀ x,
    unTerm ((FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm LX ℕ 0)]) &x) =
      (FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)]) &x := by
  intro x
  simp

end Terms

section Derivation

variable {𝓢 : Set (Proposition ℒₒᵣ)} (h𝓢 : ∀ χ ∈ 𝓢, Semiproposition.shift₀ χ = χ)
  (w₁ w₂ : Semiformula ℒₒᵣ ℕ Empty 0 1) {φ₁ φ₂ : FirstOrder.Semiformula LX ℕ 1}
  (hφ₁ : φ₁.freeVariables = ∅) (hφ₂ : φ₂.freeVariables = ∅)

include hφ₁ hφ₂ in
theorem shift₀_extHyp :
    Semiproposition.shift₀ (extHyp w₁ w₂ φ₁ φ₂) = extHyp w₁ w₂ φ₁ φ₂ := by
  have e : ∀ (w : Semiformula ℒₒᵣ ℕ Empty 0 1) {φ : FirstOrder.Semiformula LX ℕ 1},
      φ.freeVariables = ∅ →
      ((FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0).q) ▹
        (toSOAtB w φ : Semiproposition ℒₒᵣ 0 1) = toSOAtB w φ := by
    intro w φ hφ
    rw [← toSOAtB_rew (q_hb hb_shift) (q_hf hf_shift)]
    congr 1
    refine FirstOrder.Semiformula.rew_eq_self_of (fun x => ?_) (fun x hx => ?_)
    · fin_cases x; simp
    · have hx' : x ∈ φ.freeVariables := hx
      rw [hφ] at hx'
      exact absurd hx' (by simp)
  show (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹
    (∀¹ ((toSOAtB w₁ φ₁ : Semiproposition ℒₒᵣ 0 1) 🡘 toSOAtB w₂ φ₂)) = _
  rw [Semiformula.rew_all₀, LogicalConnective.HomClass.map_iff, e w₁ hφ₁, e w₂ hφ₂]
  rfl

/-- One instance of the extensionality hypothesis closes `Ψ₁(t) → Ψ₂(t)`. -/
theorem extAt (t : FirstOrder.Semiterm LX ℕ 0) :
    PSeq 𝓢 [∼(fAt w₁ φ₁ t), fAt w₂ φ₂ t, ∼(extHyp w₁ w₂ φ₁ φ₂)] := by
  have hinst : ((∼((toSOAtB w₁ φ₁ : Semiproposition ℒₒᵣ 0 1) 🡘 toSOAtB w₂ φ₂))/[unTerm t] :
      Proposition ℒₒᵣ) = ((fAt w₁ φ₁ t ⋏ ∼(fAt w₂ φ₂ t)) ⋎ (fAt w₂ φ₂ t ⋏ ∼(fAt w₁ φ₁ t))) := by
    have h1 : ((toSOAtB w₁ φ₁ : Semiproposition ℒₒᵣ 0 1))/[unTerm t] = fAt w₁ φ₁ t :=
      (toSOAtB_subst₁ φ₁ t).symm
    have h2 : ((toSOAtB w₂ φ₂ : Semiproposition ℒₒᵣ 0 1))/[unTerm t] = fAt w₂ φ₂ t :=
      (toSOAtB_subst₁ φ₂ t).symm
    show (FirstOrder.Rew.subst ![unTerm t]) ▹
      (∼((toSOAtB w₁ φ₁ : Semiproposition ℒₒᵣ 0 1) 🡘 toSOAtB w₂ φ₂)) = _
    rw [LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_iff]
    rw [show (FirstOrder.Rew.subst ![unTerm t]) ▹ (toSOAtB w₁ φ₁ : Semiproposition ℒₒᵣ 0 1) =
      fAt w₁ φ₁ t from h1, show (FirstOrder.Rew.subst ![unTerm t]) ▹
      (toSOAtB w₂ φ₂ : Semiproposition ℒₒᵣ 0 1) = fAt w₂ φ₂ t from h2]
    simp [LogicalConnective.iff, LogicalConnective.DeMorgan.imply]
  have core : PSeq 𝓢 [((fAt w₁ φ₁ t ⋏ ∼(fAt w₂ φ₂ t)) ⋎ (fAt w₂ φ₂ t ⋏ ∼(fAt w₁ φ₁ t))),
      ∼(fAt w₁ φ₁ t), fAt w₂ φ₂ t] := by
    refine PSeq.or (PSeq.and ?_ ?_)
    · exact PSeq.id (φ := fAt w₁ φ₁ t) (by simp) (by simp)
    · exact PSeq.id (φ := fAt w₂ φ₂ t) (by simp) (by simp)
  have core' : PSeq 𝓢
      [((∼((toSOAtB w₁ φ₁ : Semiproposition ℒₒᵣ 0 1) 🡘 toSOAtB w₂ φ₂))/[unTerm t]),
        ∼(fAt w₁ φ₁ t), fAt w₂ φ₂ t] := by
    rw [hinst]; exact core
  have hE : PSeq 𝓢 [∼(extHyp w₁ w₂ φ₁ φ₂), ∼(fAt w₁ φ₁ t), fAt w₂ φ₂ t] :=
    PSeq.exs₁ (unTerm t) core'
  exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hE

/-- The other direction: `Ψ₂(t) → Ψ₁(t)`. -/
theorem extAt' (t : FirstOrder.Semiterm LX ℕ 0) :
    PSeq 𝓢 [∼(fAt w₂ φ₂ t), fAt w₁ φ₁ t, ∼(extHyp w₁ w₂ φ₁ φ₂)] := by
  have hinst : ((∼((toSOAtB w₁ φ₁ : Semiproposition ℒₒᵣ 0 1) 🡘 toSOAtB w₂ φ₂))/[unTerm t] :
      Proposition ℒₒᵣ) = ((fAt w₁ φ₁ t ⋏ ∼(fAt w₂ φ₂ t)) ⋎ (fAt w₂ φ₂ t ⋏ ∼(fAt w₁ φ₁ t))) := by
    have h1 : ((toSOAtB w₁ φ₁ : Semiproposition ℒₒᵣ 0 1))/[unTerm t] = fAt w₁ φ₁ t :=
      (toSOAtB_subst₁ φ₁ t).symm
    have h2 : ((toSOAtB w₂ φ₂ : Semiproposition ℒₒᵣ 0 1))/[unTerm t] = fAt w₂ φ₂ t :=
      (toSOAtB_subst₁ φ₂ t).symm
    show (FirstOrder.Rew.subst ![unTerm t]) ▹
      (∼((toSOAtB w₁ φ₁ : Semiproposition ℒₒᵣ 0 1) 🡘 toSOAtB w₂ φ₂)) = _
    rw [LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_iff]
    rw [show (FirstOrder.Rew.subst ![unTerm t]) ▹ (toSOAtB w₁ φ₁ : Semiproposition ℒₒᵣ 0 1) =
      fAt w₁ φ₁ t from h1, show (FirstOrder.Rew.subst ![unTerm t]) ▹
      (toSOAtB w₂ φ₂ : Semiproposition ℒₒᵣ 0 1) = fAt w₂ φ₂ t from h2]
    simp [LogicalConnective.iff, LogicalConnective.DeMorgan.imply]
  have core : PSeq 𝓢 [(fAt w₂ φ₂ t ⋏ ∼(fAt w₁ φ₁ t)), (fAt w₁ φ₁ t ⋏ ∼(fAt w₂ φ₂ t)),
      ∼(fAt w₂ φ₂ t), fAt w₁ φ₁ t] := by
    refine PSeq.and ?_ ?_
    · exact PSeq.id (φ := fAt w₂ φ₂ t) (by simp) (by simp)
    · exact PSeq.id (φ := fAt w₁ φ₁ t) (by simp) (by simp)
  have core1 : PSeq 𝓢 [((fAt w₁ φ₁ t ⋏ ∼(fAt w₂ φ₂ t)) ⋎ (fAt w₂ φ₂ t ⋏ ∼(fAt w₁ φ₁ t))),
      ∼(fAt w₂ φ₂ t), fAt w₁ φ₁ t] :=
    PSeq.or (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) core)
  have core' : PSeq 𝓢
      [((∼((toSOAtB w₁ φ₁ : Semiproposition ℒₒᵣ 0 1) 🡘 toSOAtB w₂ φ₂))/[unTerm t]),
        ∼(fAt w₂ φ₂ t), fAt w₁ φ₁ t] := by
    rw [hinst]; exact core1
  have hE : PSeq 𝓢 [∼(extHyp w₁ w₂ φ₁ φ₂), ∼(fAt w₂ φ₂ t), fAt w₁ φ₁ t] :=
    PSeq.exs₁ (unTerm t) core'
  exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hE

/-! #### The rewriting instances used by the derivation -/

section Instances

variable {w : Semiformula ℒₒᵣ ℕ Empty 0 1} {φ : FirstOrder.Semiformula LX ℕ 1}

theorem free₀_bAt_body (hφ : φ.freeVariables = ∅) (b : FirstOrder.Semiterm LX ℕ 0) :
    Semiproposition.free₀ (∼(rAt (#0 : FirstOrder.Semiterm LX ℕ 1) (FirstOrder.Rew.bShift b)) ⋎
      fAt w φ (#0 : FirstOrder.Semiterm LX ℕ 1)) =
    ∼(rAt (&0 : FirstOrder.Semiterm LX ℕ 0) (FirstOrder.Rew.free (FirstOrder.Rew.bShift b))) ⋎
      fAt w φ (&0 : FirstOrder.Semiterm LX ℕ 0) := by
  show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹ _ = _
  rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    rew_rAt hb_free hf_free, rew_fAt hb_free hf_free w hφ, free_bvar_zero_LX]

theorem free₀_pAt_body (hφ : φ.freeVariables = ∅) :
    Semiproposition.free₀ (∼(bAt w φ (#0 : FirstOrder.Semiterm LX ℕ 1)) ⋎
      fAt w φ (#0 : FirstOrder.Semiterm LX ℕ 1)) =
    ∼(bAt w φ (&0 : FirstOrder.Semiterm LX ℕ 0)) ⋎ fAt w φ (&0 : FirstOrder.Semiterm LX ℕ 0) := by
  show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹ _ = _
  rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    rew_bAt hb_free hf_free w hφ, rew_fAt hb_free hf_free w hφ, free_bvar_zero_LX]

theorem subst_bAt_negbody (hφ : φ.freeVariables = ∅) (b : FirstOrder.Semiterm LX ℕ 0) :
    (rAt (#0 : FirstOrder.Semiterm LX ℕ 1) (FirstOrder.Rew.bShift b) ⋏
      ∼(fAt w φ (#0 : FirstOrder.Semiterm LX ℕ 1)))/[(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)] =
    rAt (&0 : FirstOrder.Semiterm LX ℕ 0)
        ((FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm LX ℕ 0)]) (FirstOrder.Rew.bShift b)) ⋏
      ∼(fAt w φ (&0 : FirstOrder.Semiterm LX ℕ 0)) := by
  show (FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)]) ▹ _ = _
  rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg,
    rew_rAt hb_subst_z0 hf_subst_z0, rew_fAt hb_subst_z0 hf_subst_z0 w hφ]
  simp

theorem subst_pAt_negbody (hφ : φ.freeVariables = ∅) :
    (bAt w φ (#0 : FirstOrder.Semiterm LX ℕ 1) ⋏
      ∼(fAt w φ (#0 : FirstOrder.Semiterm LX ℕ 1)))/[(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)] =
    bAt w φ (&0 : FirstOrder.Semiterm LX ℕ 0) ⋏ ∼(fAt w φ (&0 : FirstOrder.Semiterm LX ℕ 0)) := by
  show (FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)]) ▹ _ = _
  rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg,
    rew_bAt hb_subst_z0 hf_subst_z0 w hφ, rew_fAt hb_subst_z0 hf_subst_z0 w hφ]
  simp

theorem shift₀_bAt (hφ : φ.freeVariables = ∅) (b : FirstOrder.Semiterm LX ℕ 0) :
    Semiproposition.shift₀ (bAt w φ b) = bAt w φ (FirstOrder.Rew.shift b) :=
  rew_bAt hb_shift hf_shift w hφ b

theorem shift₀_fAt (hφ : φ.freeVariables = ∅) (b : FirstOrder.Semiterm LX ℕ 0) :
    Semiproposition.shift₀ (fAt w φ b) = fAt w φ (FirstOrder.Rew.shift b) :=
  rew_fAt hb_shift hf_shift w hφ b

theorem shift₀_pAt (hφ : φ.freeVariables = ∅) :
    Semiproposition.shift₀ (pAt w φ : Proposition ℒₒᵣ) = pAt w φ :=
  rew_pAt hb_shift hf_shift w hφ

end Instances

include h𝓢 hφ₁ hφ₂ in
/-- **Transfinite induction is extensional in its parameter.**  If `Ψ₁` and `Ψ₂` agree
pointwise, `TI(≺₁, Ψ₁, ū)` gives `TI(≺₁, Ψ₂, ū)`.  The two parameters are liftings of
first-order formulas at two possibly different witnesses, so this is genuinely a
second-order derivation: `Prog(Ψ₂) → Prog(Ψ₁)` and `Below(Ψ₁, ū) → Below(Ψ₂, ū)`,
each by eigenvariables and one instance of the hypothesis. -/
theorem tiExt (k : ℕ) :
    Provable 𝓢 (∼(extHyp w₁ w₂ φ₁ φ₂) ⋎
      (∼(toSOAtB w₁ (Gentzen.tiUptoAt precCode₁ φ₁
          (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0))) ⋎
        toSOAtB w₂ (Gentzen.tiUptoAt precCode₁ φ₂
          (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)))) := by
  -- the two eigenvariables and the bound
  have hu_free : (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0)
      (FirstOrder.Rew.bShift (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)) =
      FirstOrder.Semiterm.numeral k := by simp
  have hu_shift : (FirstOrder.Rew.shift : FirstOrder.Rew LX ℕ 0 ℕ 0)
      (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0) =
      FirstOrder.Semiterm.numeral k := by simp
  have hu_sub : (FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm LX ℕ 0)])
      (FirstOrder.Rew.bShift (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)) =
      FirstOrder.Semiterm.numeral k := by simp
  have hz_free : (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0)
      (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0)) = &1 := by simp
  have hz_shift : (FirstOrder.Rew.shift : FirstOrder.Rew LX ℕ 0 ℕ 0)
      (&0 : FirstOrder.Semiterm LX ℕ 0) = &1 := by simp
  have hz_sub : (FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm LX ℕ 0)])
      (FirstOrder.Rew.bShift (&1 : FirstOrder.Semiterm LX ℕ 0)) = &1 := by simp
  have hE := shift₀_extHyp w₁ w₂ hφ₁ hφ₂
  -- Branch II: `Below(Ψ₁, ū) → Below(Ψ₂, ū)`
  have bII : PSeq 𝓢 [bAt w₂ φ₂ (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0),
      ∼(bAt w₁ φ₁ (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)),
      ∼(pAt w₂ φ₂), ∼(extHyp w₁ w₂ φ₁ φ₂)] := by
    have a1 : PSeq 𝓢 ((rAt (&0 : FirstOrder.Semiterm LX ℕ 0)
          (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0) ⋏
          ∼(fAt w₁ φ₁ (&0 : FirstOrder.Semiterm LX ℕ 0))) ::
        [∼(rAt (&0 : FirstOrder.Semiterm LX ℕ 0)
          (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)),
          fAt w₂ φ₂ (&0 : FirstOrder.Semiterm LX ℕ 0), ∼(pAt w₂ φ₂),
          ∼(extHyp w₁ w₂ φ₁ φ₂)]) := by
      refine PSeq.and ?_ ?_
      · exact PSeq.id (φ := rAt (&0 : FirstOrder.Semiterm LX ℕ 0)
          (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)) (by simp) (by simp)
      · exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
          (extAt (𝓢 := 𝓢) w₁ w₂ (φ₁ := φ₁) (φ₂ := φ₂) (&0 : FirstOrder.Semiterm LX ℕ 0))
    have a2 : PSeq 𝓢 ((∃¹ (rAt (#0 : FirstOrder.Semiterm LX ℕ 1)
          (FirstOrder.Rew.bShift (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)) ⋏
          ∼(fAt w₁ φ₁ (#0 : FirstOrder.Semiterm LX ℕ 1)))) ::
        [∼(rAt (&0 : FirstOrder.Semiterm LX ℕ 0)
          (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)),
          fAt w₂ φ₂ (&0 : FirstOrder.Semiterm LX ℕ 0), ∼(pAt w₂ φ₂),
          ∼(extHyp w₁ w₂ φ₁ φ₂)]) := by
      refine PSeq.exs₁ (&0) ?_
      rw [subst_bAt_negbody hφ₁, hu_sub]
      exact a1
    rw [← neg_bAt_eq] at a2
    have a3 : PSeq 𝓢 ((∼(rAt (&0 : FirstOrder.Semiterm LX ℕ 0)
          (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)) ⋎
          fAt w₂ φ₂ (&0 : FirstOrder.Semiterm LX ℕ 0)) ::
        [∼(bAt w₁ φ₁ (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)),
          ∼(pAt w₂ φ₂), ∼(extHyp w₁ w₂ φ₁ φ₂)]) :=
      PSeq.or (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) a2)
    rw [bAt_eq]
    refine PSeq.all₁ h𝓢 ?_
    have hsh : SecondOrder.Sequent.shift₀
        [∼(bAt w₁ φ₁ (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)),
          ∼(pAt w₂ φ₂), ∼(extHyp w₁ w₂ φ₁ φ₂)] =
        [∼(bAt w₁ φ₁ (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)),
          ∼(pAt w₂ φ₂), ∼(extHyp w₁ w₂ φ₁ φ₂)] := by
      simp only [SecondOrder.Sequent.shift₀, List.map_cons, List.map_nil,
        LogicalConnective.HomClass.map_neg, shift₀_bAt hφ₁, hu_shift, shift₀_pAt hφ₂, hE]
    rw [hsh, free₀_bAt_body hφ₂, hu_free]
    exact a3
  -- Branch I: `Prog(Ψ₂) → Prog(Ψ₁)`
  have bI : PSeq 𝓢 [pAt w₁ φ₁, ∼(pAt w₂ φ₂), ∼(extHyp w₁ w₂ φ₁ φ₂)] := by
    have c1 : PSeq 𝓢 ((rAt (&0 : FirstOrder.Semiterm LX ℕ 0) (&1 : FirstOrder.Semiterm LX ℕ 0) ⋏
          ∼(fAt w₁ φ₁ (&0 : FirstOrder.Semiterm LX ℕ 0))) ::
        [∼(rAt (&0 : FirstOrder.Semiterm LX ℕ 0) (&1 : FirstOrder.Semiterm LX ℕ 0)),
          fAt w₂ φ₂ (&0 : FirstOrder.Semiterm LX ℕ 0), ∼(extHyp w₁ w₂ φ₁ φ₂)]) := by
      refine PSeq.and ?_ ?_
      · exact PSeq.id (φ := rAt (&0 : FirstOrder.Semiterm LX ℕ 0)
          (&1 : FirstOrder.Semiterm LX ℕ 0)) (by simp) (by simp)
      · exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
          (extAt (𝓢 := 𝓢) w₁ w₂ (φ₁ := φ₁) (φ₂ := φ₂) (&0 : FirstOrder.Semiterm LX ℕ 0))
    have c2 : PSeq 𝓢 ((∃¹ (rAt (#0 : FirstOrder.Semiterm LX ℕ 1)
          (FirstOrder.Rew.bShift (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋏
          ∼(fAt w₁ φ₁ (#0 : FirstOrder.Semiterm LX ℕ 1)))) ::
        [∼(rAt (&0 : FirstOrder.Semiterm LX ℕ 0) (&1 : FirstOrder.Semiterm LX ℕ 0)),
          fAt w₂ φ₂ (&0 : FirstOrder.Semiterm LX ℕ 0), ∼(extHyp w₁ w₂ φ₁ φ₂)]) := by
      refine PSeq.exs₁ (&0) ?_
      rw [subst_bAt_negbody hφ₁, hz_sub]
      exact c1
    rw [← neg_bAt_eq] at c2
    have c3 : PSeq 𝓢 ((∼(rAt (&0 : FirstOrder.Semiterm LX ℕ 0) (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋎
          fAt w₂ φ₂ (&0 : FirstOrder.Semiterm LX ℕ 0)) ::
        [∼(bAt w₁ φ₁ (&1 : FirstOrder.Semiterm LX ℕ 0)), ∼(extHyp w₁ w₂ φ₁ φ₂)]) :=
      PSeq.or (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) c2)
    have c4 : PSeq 𝓢 [bAt w₂ φ₂ (&0 : FirstOrder.Semiterm LX ℕ 0),
        ∼(bAt w₁ φ₁ (&0 : FirstOrder.Semiterm LX ℕ 0)), ∼(extHyp w₁ w₂ φ₁ φ₂)] := by
      rw [bAt_eq]
      refine PSeq.all₁ h𝓢 ?_
      have hsh : SecondOrder.Sequent.shift₀
          [∼(bAt w₁ φ₁ (&0 : FirstOrder.Semiterm LX ℕ 0)), ∼(extHyp w₁ w₂ φ₁ φ₂)] =
          [∼(bAt w₁ φ₁ (&1 : FirstOrder.Semiterm LX ℕ 0)), ∼(extHyp w₁ w₂ φ₁ φ₂)] := by
        simp only [SecondOrder.Sequent.shift₀, List.map_cons, List.map_nil,
          LogicalConnective.HomClass.map_neg, shift₀_bAt hφ₁, hz_shift, hE]
      rw [hsh, free₀_bAt_body hφ₂, hz_free]
      exact c3
    have c5 : PSeq 𝓢 ((bAt w₂ φ₂ (&0 : FirstOrder.Semiterm LX ℕ 0) ⋏
          ∼(fAt w₂ φ₂ (&0 : FirstOrder.Semiterm LX ℕ 0))) ::
        [∼(bAt w₁ φ₁ (&0 : FirstOrder.Semiterm LX ℕ 0)),
          fAt w₁ φ₁ (&0 : FirstOrder.Semiterm LX ℕ 0), ∼(extHyp w₁ w₂ φ₁ φ₂)]) := by
      refine PSeq.and ?_ ?_
      · exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) c4
      · exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
          (extAt' (𝓢 := 𝓢) w₁ w₂ (φ₁ := φ₁) (φ₂ := φ₂) (&0 : FirstOrder.Semiterm LX ℕ 0))
    have c6 : PSeq 𝓢 ((∃¹ (bAt w₂ φ₂ (#0 : FirstOrder.Semiterm LX ℕ 1) ⋏
          ∼(fAt w₂ φ₂ (#0 : FirstOrder.Semiterm LX ℕ 1)))) ::
        [∼(bAt w₁ φ₁ (&0 : FirstOrder.Semiterm LX ℕ 0)),
          fAt w₁ φ₁ (&0 : FirstOrder.Semiterm LX ℕ 0), ∼(extHyp w₁ w₂ φ₁ φ₂)]) := by
      refine PSeq.exs₁ (&0) ?_
      rw [subst_pAt_negbody hφ₂]
      exact c5
    rw [← neg_pAt_eq] at c6
    have c7 : PSeq 𝓢 ((∼(bAt w₁ φ₁ (&0 : FirstOrder.Semiterm LX ℕ 0)) ⋎
          fAt w₁ φ₁ (&0 : FirstOrder.Semiterm LX ℕ 0)) ::
        [∼(pAt w₂ φ₂), ∼(extHyp w₁ w₂ φ₁ φ₂)]) :=
      PSeq.or (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) c6)
    rw [pAt_eq]
    refine PSeq.all₁ h𝓢 ?_
    have hsh : SecondOrder.Sequent.shift₀ [∼(pAt w₂ φ₂ : Proposition ℒₒᵣ),
        ∼(extHyp w₁ w₂ φ₁ φ₂)] = [∼(pAt w₂ φ₂), ∼(extHyp w₁ w₂ φ₁ φ₂)] := by
      simp only [SecondOrder.Sequent.shift₀, List.map_cons, List.map_nil,
        LogicalConnective.HomClass.map_neg, shift₀_pAt hφ₂, hE]
    rw [hsh, free₀_pAt_body hφ₁]
    exact c7
  -- assembly
  have hT₁ : ∼(toSOAtB w₁ (Gentzen.tiUptoAt precCode₁ φ₁
      (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)) : Proposition ℒₒᵣ) =
      pAt w₁ φ₁ ⋏ ∼(bAt w₁ φ₁ (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)) := by
    rw [ti_eq]
    show (∼∼(pAt w₁ φ₁ : Proposition ℒₒᵣ)) ⋏ _ = _
    rw [Semiformula.neg_neg]
    rfl
  have hT₂ : (toSOAtB w₂ (Gentzen.tiUptoAt precCode₁ φ₂
      (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)) : Proposition ℒₒᵣ) =
      ∼(pAt w₂ φ₂) ⋎ bAt w₂ φ₂ (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0) :=
    ti_eq w₂ φ₂ _
  rw [hT₁, hT₂]
  have d1 : PSeq 𝓢 ((pAt w₁ φ₁ ⋏
        ∼(bAt w₁ φ₁ (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0))) ::
      [∼(pAt w₂ φ₂), bAt w₂ φ₂ (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0),
        ∼(extHyp w₁ w₂ φ₁ φ₂)]) := by
    refine PSeq.and ?_ ?_
    · exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) bI
    · exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) bII
  have d2 : PSeq 𝓢 ((∼(pAt w₂ φ₂) ⋎
        bAt w₂ φ₂ (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0)) ::
      [(pAt w₁ φ₁ ⋏
        ∼(bAt w₁ φ₁ (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0))),
        ∼(extHyp w₁ w₂ φ₁ φ₂)]) :=
    PSeq.or (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) d1)
  have d3 : PSeq 𝓢 (((pAt w₁ φ₁ ⋏
        ∼(bAt w₁ φ₁ (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0))) ⋎
      (∼(pAt w₂ φ₂) ⋎
        bAt w₂ φ₂ (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ℕ 0))) ::
      [∼(extHyp w₁ w₂ φ₁ φ₂)]) :=
    PSeq.or (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) d2)
  exact PSeq.to_provable (PSeq.or
    (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) d3))

end Derivation

end TIExt

/-! ### Second-order rewritings of a lifted formula -/

/-- **A second-order rewriting of a lifted formula is the lifting at the rewritten
witness**, as soon as it rewrites the (embedded) witness to an embedded witness.  This
is `Translate.subst₁_toSOAtB` for an arbitrary rewriting (renaming of free set
variables, `free₁`, compositions of these). -/
theorem app_toSOAtB_of {N₁ N₂ : ℕ} (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ)
    {ψ : Semiformula ℒₒᵣ ℕ Empty N₁ 1} {ψ' : Semiformula ℒₒᵣ ℕ Empty N₂ 1}
    (hψ : Ω.app (FirstOrder.Rewriting.emb ψ : Semiformula ℒₒᵣ ℕ ℕ N₁ 1) =
      FirstOrder.Rewriting.emb ψ') :
    ∀ {n : ℕ} (χ : FirstOrder.Semiformula LX ℕ n), Ω.app (toSOAtB ψ χ) = toSOAtB ψ' χ
  | _, .verum => rfl
  | _, .falsum => rfl
  | _, .rel (Sum.inl _) _ => rfl
  | _, .nrel (Sum.inl _) _ => rfl
  | _, .rel (Sum.inr Gentzen.XRel.X) v => by
      show Ω.app ((FirstOrder.Rewriting.emb ψ)/[unTerm (v 0)]) =
        (FirstOrder.Rewriting.emb ψ')/[unTerm (v 0)]
      rw [SecondOrder.Rew.app_comm_subst, hψ]
  | _, .nrel (Sum.inr Gentzen.XRel.X) v => by
      show Ω.app (∼((FirstOrder.Rewriting.emb ψ)/[unTerm (v 0)])) =
        ∼((FirstOrder.Rewriting.emb ψ')/[unTerm (v 0)])
      rw [LogicalConnective.HomClass.map_neg, SecondOrder.Rew.app_comm_subst, hψ]
  | _, .and φ χ => by
      show Ω.app (toSOAtB ψ φ ⋏ toSOAtB ψ χ) = toSOAtB ψ' φ ⋏ toSOAtB ψ' χ
      rw [LogicalConnective.HomClass.map_and, app_toSOAtB_of Ω hψ φ, app_toSOAtB_of Ω hψ χ]
  | _, .or φ χ => by
      show Ω.app (toSOAtB ψ φ ⋎ toSOAtB ψ χ) = toSOAtB ψ' φ ⋎ toSOAtB ψ' χ
      rw [LogicalConnective.HomClass.map_or, app_toSOAtB_of Ω hψ φ, app_toSOAtB_of Ω hψ χ]
  | _, .all φ => by
      show Ω.app (∀¹ (toSOAtB ψ φ)) = ∀¹ (toSOAtB ψ' φ)
      rw [SecondOrder.Rew.app_all₀, app_toSOAtB_of Ω hψ φ]
  | _, .exs φ => by
      show Ω.app (∃¹ (toSOAtB ψ φ)) = ∃¹ (toSOAtB ψ' φ)
      rw [SecondOrder.Rew.app_exs₀, app_toSOAtB_of Ω hψ φ]

/-- The witness reading `X` as the free set variable `1`. -/
def wZ1 : Semiformula ℒₒᵣ ℕ Empty 0 1 := (#0 : FirstOrder.Semiterm ℒₒᵣ Empty 1) ∈& (1 : ℕ)

/-- `shift₁` moves the free set variable `0` to `1`. -/
theorem shift₁_toSOAt_segWitness {n : ℕ} (χ : FirstOrder.Semiformula LX ℕ n) :
    Semiproposition.shift₁ (toSOAt segWitness χ) = toSOAt wZ1 χ := by
  refine app_toSOAtB_of SecondOrder.Rew.shift ?_ χ
  simp [segWitness, wZ1]

/-- Instantiating the outer `∀²Z` of the omega-jump axiom at the free set variable `0`
and then opening the inner `∃²Y` with the eigenvariable `0`: `Y` becomes the free set
variable `0` and `Z` the free set variable `1`. -/
def axRew : SecondOrder.Rew ℒₒᵣ ℕ 2 ℕ 0 ℕ :=
  SecondOrder.Rew.free.comp (SecondOrder.Rew.subst ![freeWitness]).q

theorem free_bv_zero :
    (SecondOrder.Rew.free : SecondOrder.Rew ℒₒᵣ ℕ 1 ℕ 0 ℕ).bv 0 =
      (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0 :=
  SecondOrder.Rew.free_bvar_last 0

theorem axRew_bv_zero :
    axRew.bv 0 = (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 0 := by
  show SecondOrder.Rew.free.app ((SecondOrder.Rew.subst ![freeWitness]).q.bv 0) = _
  rw [SecondOrder.Rew.q_bv_zero, SecondOrder.Rew.app_bvar, free_bv_zero]
  simp

theorem axRew_bv_one :
    axRew.bv 1 = (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& 1 := by
  show SecondOrder.Rew.free.app ((SecondOrder.Rew.subst ![freeWitness]).q.bv (Fin.succ 0)) = _
  rw [SecondOrder.Rew.q_bv_succ]
  simp [freeWitness]

theorem axRew_yWit :
    axRew.app (FirstOrder.Rewriting.emb yWit2 : Semiformula ℒₒᵣ ℕ ℕ 2 1) =
      FirstOrder.Rewriting.emb yWitFree := by
  simp [yWit2, yWitFree, axRew_bv_zero]

theorem axRew_z :
    axRew.app ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (1 : Fin 2)) =
      (toSOAtB wZ1 (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) : Semiproposition ℒₒᵣ 0 1) := by
  rw [toSOAtB_Xat_bvar]
  simp [wZ1, axRew_bv_one]

theorem axRew_base :
    axRew.app hierBase =
      extHyp yWitFree wZ1 hierBaseColLX (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) := by
  show axRew.app (∀¹ ((toSOAtB yWit2 hierBaseColLX : Semiproposition ℒₒᵣ 2 1) 🡘
    ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (1 : Fin 2)))) = _
  rw [SecondOrder.Rew.app_all₀, LogicalConnective.HomClass.map_iff,
    app_toSOAtB_of axRew axRew_yWit, axRew_z]
  rfl

theorem axRew_step :
    axRew.app hierStep = toSOAt yWitFree ColumnTower.stepHypLX := by
  show axRew.app (∀¹ ∀¹ (toSOAtB yWit2 hierStepColLX : Semiproposition ℒₒᵣ 2 2)) = _
  rw [SecondOrder.Rew.app_all₀, SecondOrder.Rew.app_all₀, app_toSOAtB_of axRew axRew_yWit]
  rfl

/-- **The omega-jump condition at `Y := 0`, `Z := 1`.** -/
theorem free₁_axBody :
    Semiproposition.free₁ ((SecondOrder.Rew.subst ![freeWitness]).q.app IsOmegaJump) =
      extHyp yWitFree wZ1 hierBaseColLX (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) ⋏
        toSOAt yWitFree ColumnTower.stepHypLX := by
  show SecondOrder.Rew.free.app ((SecondOrder.Rew.subst ![freeWitness]).q.app
    (hierBase ⋏ hierStep)) = _
  rw [← SecondOrder.Rew.app_comp]
  show axRew.app (hierBase ⋏ hierStep) = _
  rw [LogicalConnective.HomClass.map_and, axRew_base, axRew_step]

/-! ### The ε-jump -/

open OrdinalAnalysis.Gentzen.Epsilon1UpperBound (gamma0Term) in
open OrdinalAnalysis.Gamma0Note (epsilonNote) in
/-- **The ε-jump in `ACA^+`**: transfinite induction up to `b̄` for all sets gives
transfinite induction up to `ε̄_b` for all sets.

For a set `Z` (the free set variable `0`), the omega-jump axiom supplies `Y` with
`IsOmegaJump(Y, Z)`.  Instantiating `∀²X TI(≺₁, b̄, X)` at the arithmetical formula
`χ_Y` (arithmetical comprehension) and the lifted `ColumnTower.concrete_colEpsJump`
give `TI(≺₁, col_0 Y, ε̄_b)` from the step condition; the base condition
`col_0 Y = Z` and `tiExt` turn it into `TI(≺₁, Z, ε̄_b)`. -/
theorem epsJump_plus (b : Gamma0Note)
    (h : Provable ACAplus (allTI (gamma0Term b))) :
    Provable ACAplus (allTI (gamma0Term (epsilonNote b))) := by
  -- `TI(χ_Y, b̄)`, by arithmetical comprehension
  have hχ : Provable ACAplus (toSOAt yWitFree
      (Gentzen.tiUptoAt precCode₁ ColumnTower.chiLX (gamma0Term b))) := by
    have h2 := spec₂ h (arith_toSOAt arith_segWitness ColumnTower.chiLX)
    rw [subst₁_tiBody_gen] at h2
    exact h2
  -- `H(Y) → TI(col_0 Y, ε̄_b)`
  have J1 : PSeq ACAplus [∼(toSOAt yWitFree ColumnTower.stepHypLX),
      toSOAt yWitFree (Gentzen.tiUptoAt precCode₁ hierBaseColLX
        (gamma0Term (epsilonNote b)))] := by
    have hj : PSeq ACAplus [∼(toSOAt yWitFree ColumnTower.stepHypLX),
        (∼(toSOAt yWitFree (Gentzen.tiUptoAt precCode₁ ColumnTower.chiLX (gamma0Term b))) ⋎
          toSOAt yWitFree (Gentzen.tiUptoAt precCode₁ hierBaseColLX
            (gamma0Term (epsilonNote b))))] :=
      PSeq.orInv (PSeq.of_provable (Provable_mono_ACAplus (colEpsJump_lifted b)))
    have hj1 : PSeq ACAplus
        [(∼(toSOAt yWitFree (Gentzen.tiUptoAt precCode₁ ColumnTower.chiLX (gamma0Term b))) ⋎
          toSOAt yWitFree (Gentzen.tiUptoAt precCode₁ hierBaseColLX
            (gamma0Term (epsilonNote b)))), ∼(toSOAt yWitFree ColumnTower.stepHypLX)] :=
      PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hj
    have hj2 : PSeq ACAplus
        [∼(toSOAt yWitFree (Gentzen.tiUptoAt precCode₁ ColumnTower.chiLX (gamma0Term b))),
          toSOAt yWitFree (Gentzen.tiUptoAt precCode₁ hierBaseColLX
            (gamma0Term (epsilonNote b))), ∼(toSOAt yWitFree ColumnTower.stepHypLX)] :=
      PSeq.orInv hj1
    refine PSeq.cut (toSOAt yWitFree
      (Gentzen.tiUptoAt precCode₁ ColumnTower.chiLX (gamma0Term b))) (PSeq.ofProvable hχ _) ?_
    exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hj2
  -- `col_0 Y = Z → TI(col_0 Y, ε̄_b) → TI(Z, ε̄_b)`
  have J2 : PSeq ACAplus
      [∼(extHyp yWitFree wZ1 hierBaseColLX (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))),
        ∼(toSOAt yWitFree (Gentzen.tiUptoAt precCode₁ hierBaseColLX
          (gamma0Term (epsilonNote b)))),
        toSOAt wZ1 (tiX (gamma0Term (epsilonNote b)))] := by
    have hx : Provable ACAplus
        (∼(extHyp yWitFree wZ1 hierBaseColLX (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))) ⋎
          (∼(toSOAt yWitFree (Gentzen.tiUptoAt precCode₁ hierBaseColLX
            (gamma0Term (epsilonNote b)))) ⋎
          toSOAt wZ1 (tiX (gamma0Term (epsilonNote b))))) :=
      tiExt ACAplus_shift₀_invariant yWitFree wZ1 ColumnTower.freeVariables_hierBaseColLX
        (TowerSyntax.freeVariables_XatZero (n := 0))
        (Gentzen.VNoteBridge.gamma0Code (epsilonNote b))
    have hx1 : PSeq ACAplus
        [∼(extHyp yWitFree wZ1 hierBaseColLX (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))),
          (∼(toSOAt yWitFree (Gentzen.tiUptoAt precCode₁ hierBaseColLX
            (gamma0Term (epsilonNote b)))) ⋎
          toSOAt wZ1 (tiX (gamma0Term (epsilonNote b))))] :=
      PSeq.orInv (PSeq.of_provable hx)
    have hx2 : PSeq ACAplus
        [(∼(toSOAt yWitFree (Gentzen.tiUptoAt precCode₁ hierBaseColLX
            (gamma0Term (epsilonNote b)))) ⋎
          toSOAt wZ1 (tiX (gamma0Term (epsilonNote b)))),
          ∼(extHyp yWitFree wZ1 hierBaseColLX (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)))] :=
      PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hx1
    exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) (PSeq.orInv hx2)
  -- combine: `¬(col_0 Y = Z ∧ H(Y)) ∨ TI(Z, ε̄_b)` at `Y = 0`, `Z = 1`
  have J3 : PSeq ACAplus
      [∼(extHyp yWitFree wZ1 hierBaseColLX (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) ⋏
          toSOAt yWitFree ColumnTower.stepHypLX),
        toSOAt wZ1 (tiX (gamma0Term (epsilonNote b)))] := by
    have c : PSeq ACAplus
        [∼(extHyp yWitFree wZ1 hierBaseColLX (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))),
          ∼(toSOAt yWitFree ColumnTower.stepHypLX),
          toSOAt wZ1 (tiX (gamma0Term (epsilonNote b)))] :=
      PSeq.cut (toSOAt yWitFree (Gentzen.tiUptoAt precCode₁ hierBaseColLX
          (gamma0Term (epsilonNote b))))
        (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) J1)
        (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) J2)
    exact PSeq.or c
  -- open the `∃²Y` of the axiom instance at `Z := 0`
  have hax : Provable ACAplus
      (∃² ((SecondOrder.Rew.subst ![freeWitness]).q.app IsOmegaJump)) :=
    spec₂ (ofAxiom omegaJumpAxiom_mem_ACAplus) arith_freeWitness
  have J4 : PSeq ACAplus [∀² (∼((SecondOrder.Rew.subst ![freeWitness]).q.app IsOmegaJump)),
      toSOAt segWitness (tiX (gamma0Term (epsilonNote b)))] := by
    refine PSeq.all₂ ACAplus_shift₁_invariant ?_
    have e1 : Semiproposition.free₁ (∼((SecondOrder.Rew.subst ![freeWitness]).q.app
        IsOmegaJump)) =
        ∼(extHyp yWitFree wZ1 hierBaseColLX (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) ⋏
          toSOAt yWitFree ColumnTower.stepHypLX) := by
      rw [← free₁_axBody]
      exact LogicalConnective.HomClass.map_neg _ _
    have e2 : SecondOrder.Sequent.shift₁ [toSOAt segWitness (tiX (gamma0Term (epsilonNote b)))] =
        [toSOAt wZ1 (tiX (gamma0Term (epsilonNote b)))] := by
      simp only [SecondOrder.Sequent.shift₁, List.map_cons, List.map_nil,
        shift₁_toSOAt_segWitness]
    rw [e1, e2]
    exact J3
  have J5 : PSeq ACAplus [toSOAt segWitness (tiX (gamma0Term (epsilonNote b)))] :=
    PSeq.cut (∃² ((SecondOrder.Rew.subst ![freeWitness]).q.app IsOmegaJump))
      (PSeq.ofProvable hax _) J4
  refine gen₂ ACAplus_shift₁_invariant ?_
  rw [free₁_tiBody]
  exact PSeq.to_provable J5

end OrdinalAnalysis.ACA

/-! ## The segment bridge, for the segment below an arbitrary `ε_e` -/

namespace OrdinalAnalysis.ACA.SegBridgeE

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.CodedVeblen
open OrdinalAnalysis.Gentzen.CodedVeblenJump
open OrdinalAnalysis.Gentzen.Epsilon1UpperBound
open OrdinalAnalysis.Gentzen.EpsilonSegmentOrder
open OrdinalAnalysis.Gentzen.Order (precTransStatement models_precTransStatement)
open OrdinalAnalysis.Gamma0Note (epsilonNote)
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)

/-- The code of `ε_e`, the right-hand end of the segment `precCodeSeg e`. -/
def segBoundE (e : Gamma0Note) : ℕ := gamma0Code (epsilonNote e)

/-- **The relativising formula** `y ≺₁ ε̄_e → X y`. -/
def segGuardE (e : Gamma0Note) : Semiformula LX ℕ 1 :=
  ∼(precAt precCode₁ (#0 : Semiterm LX ℕ 1) (Semiterm.numeral (segBoundE e))) ⋎
    Xat (#0 : Semiterm LX ℕ 1)

private theorem val_numeral_eq {M : Type*} [Nonempty M] [Structure LX M] (k : ℕ) {n : ℕ}
    (e : Fin n → M) (f : ℕ → M) :
    (Semiterm.numeral k : Semiterm LX ℕ n).val e f =
      (Semiterm.numeral k : Semiterm LX ℕ 0).val ![] f := by
  simp

@[simp] theorem freeVariables_segGuardE (e : Gamma0Note) : (segGuardE e).freeVariables = ∅ := by
  have h : (precAt precCode₁ (#0 : Semiterm LX ℕ 1)
      (Semiterm.numeral (segBoundE e))).freeVariables = ∅ :=
    LowerSyntax.freeVariables_precAt_eq_empty freeVariables_precCode₁ (by simp) (by simp)
  show (∼(precAt precCode₁ (#0 : Semiterm LX ℕ 1) (Semiterm.numeral (segBoundE e))) ⋎
    Xat (#0 : Semiterm LX ℕ 1)).freeVariables = ∅
  simp [h]

/-- The matrix of the relativisation implication for the segment below `ε_e`. -/
noncomputable def relImpBodyE (e : Gamma0Note) (a b : Semiterm LX ℕ 0) : Semiformula LX ℕ 0 :=
  ∼(tiUptoAt precCode₁ (segGuardE e) b) ⋎
    tiUptoAt (precCodeSeg e) (Xat (#0 : Semiterm LX ℕ 1)) a

theorem freeVariables_relImpBodyE (e : Gamma0Note) {a b : Semiterm LX ℕ 0}
    (ha : a.freeVariables = ∅) (hb : b.freeVariables = ∅) :
    (relImpBodyE e a b).freeVariables = ∅ := by
  have h1 : (tiUptoAt precCode₁ (segGuardE e) b).freeVariables = ∅ :=
    TowerSyntax.freeVariables_tiUptoAt freeVariables_precCode₁ (freeVariables_segGuardE e) hb
  have h2 : (tiUptoAt (precCodeSeg e) (Xat (#0 : Semiterm LX ℕ 1)) a).freeVariables = ∅ :=
    TowerSyntax.freeVariables_tiUptoAt (freeVariables_precCodeSeg e) (by simp) ha
  show (∼(tiUptoAt precCode₁ (segGuardE e) b) ⋎
    tiUptoAt (precCodeSeg e) (Xat (#0 : Semiterm LX ℕ 1)) a).freeVariables = ∅
  simp [h1, h2]

/-- **The relativisation implication is a `PA[X]`-theorem** whenever `ā ≺₁ b̄`:
transfinite induction along `≺₁` below `b̄` for the guarded formula gives transfinite
induction along the segment ordering below `ε_e`, below `ā`. -/
theorem concrete_relImpE (e : Gamma0Note) (a b : Semiterm LX ℕ 0)
    (hab : paLX ⊢ closedPrec₁ a b) :
    paLX ⊢ (relImpBodyE e a b).univCl := by
  classical
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  have hTransM : M↓[LX] ⊧ precTransStatement precCode₁ :=
    consequence_iff_eq'.mp (Theory.Proof.sound concrete_precTrans₁) M
  have hTrans := (models_precTransStatement precCode₁).mp hTransM
  have habM : M↓[LX] ⊧ closedPrec₁ a b :=
    consequence_iff_eq'.mp (Theory.Proof.sound hab) M
  rw [models_iff] at habM
  simp only [closedPrec₁, Semiformula.eval_univCl, eval_precAt] at habM
  rw [models_iff]
  simp only [relImpBodyE, Semiformula.eval_univCl, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq, eval_tiUptoAt]
  intro f
  have hguard : ∀ z : M,
      (Semiformula.Eval ![z] f (segGuardE e) ↔
        (¬ Semiformula.Eval
            ![z, (Semiterm.numeral (segBoundE e) : Semiterm LX ℕ 0).val ![] f] f precCode₁ ∨
          Semiformula.Eval ![z] f (Xat (#0 : Semiterm LX ℕ 1)))) := by
    intro z
    show Semiformula.Eval ![z] f
        (∼(precAt precCode₁ (#0 : Semiterm LX ℕ 1) (Semiterm.numeral (segBoundE e))) ⋎
          Xat (#0 : Semiterm LX ℕ 1)) ↔ _
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
      LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, eval_precAt,
      Semiterm.val_bvar, Matrix.cons_val_fin_one, val_numeral_eq]
  have hseg : ∀ y x : M,
      (Semiformula.Eval ![y, x] f (precCodeSeg e) ↔
        Semiformula.Eval ![y, x] f precCode₁ ∧
          Semiformula.Eval
            ![x, (Semiterm.numeral (segBoundE e) : Semiterm LX ℕ 0).val ![] f] f precCode₁) := by
    intro y x
    show Semiformula.Eval ![y, x] f
        (precCode₁ ⋏ precAt precCode₁ (#1 : Semiterm LX ℕ 2) (epsilonNumeral e)) ↔ _
    have he : epsilonNumeral e = (Semiterm.numeral (segBoundE e) : Semiterm LX ℕ 2) := rfl
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq, he,
      eval_precAt, Semiterm.val_bvar, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      val_numeral_eq]
  by_cases hTIb :
      (∀ x : M,
          (∀ y : M, Semiformula.Eval ![y, x] f precCode₁ →
            Semiformula.Eval ![y] f (segGuardE e)) → Semiformula.Eval ![x] f (segGuardE e)) →
        ∀ y : M, Semiformula.Eval ![y, b.val ![] f] f precCode₁ →
          Semiformula.Eval ![y] f (segGuardE e)
  · refine Or.inr ?_
    intro hProgSeg
    have hProg₁ : ∀ x : M,
        (∀ y : M, Semiformula.Eval ![y, x] f precCode₁ →
          Semiformula.Eval ![y] f (segGuardE e)) → Semiformula.Eval ![x] f (segGuardE e) := by
      intro x hx
      rw [hguard x]
      by_cases hxE :
          Semiformula.Eval
            ![x, (Semiterm.numeral (segBoundE e) : Semiterm LX ℕ 0).val ![] f] f precCode₁
      · refine Or.inr (hProgSeg x ?_)
        intro y hy
        rw [hseg y x] at hy
        rcases (hguard y).mp (hx y hy.1) with hn | hp
        · exact absurd (hTrans f y x _ hy.1 hxE) hn
        · exact hp
      · exact Or.inl hxE
    have hbelow := hTIb hProg₁
    intro y hy
    rw [hseg y (a.val ![] f)] at hy
    have hyb : Semiformula.Eval ![y, b.val ![] f] f precCode₁ :=
      hTrans f y (a.val ![] f) (b.val ![] f) hy.1 (habM f)
    rcases (hguard y).mp (hbelow y hyb) with hn | hp
    · exact absurd (hTrans f y (a.val ![] f) _ hy.1 hy.2) hn
    · exact hp
  · exact Or.inl hTIb

end OrdinalAnalysis.ACA.SegBridgeE

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX Xat TIupto paLX)
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁)
open OrdinalAnalysis.Gentzen.Epsilon1UpperBound (gamma0Term)
open OrdinalAnalysis.Gamma0Note (epsilonNote)
open OrdinalAnalysis.ACA.TowerSyntax (emb_univCl_of_closed)

/-- **`TIupto(≺_e, ā, X)` at the free set variable `0`**, along the segment of `≺₁`
below `ε_e` (`EpsilonSegmentOrder.precCodeSeg e`, the ordering of
`EpsilonSegmentOrder.epsilonOrder e`).  `ACA/TI.lean`'s `tiUptoSegSO a` is the case
`e = ε₀` (`tiUptoSegSO_eq`). -/
noncomputable def tiUptoSegSO₂ (e a : Gamma0Note) : Proposition ℒₒᵣ :=
  toSOAt segWitness
    (FirstOrder.Rewriting.emb
      (TIupto (Gentzen.EpsilonSegmentOrder.precCodeSeg e) (gamma0Term a)).univCl)

theorem tiUptoSegSO_eq (a : Gamma0Note) : tiUptoSegSO a = tiUptoSegSO₂ (epsilonNote 0) a := rfl

theorem arith_tiUptoSegSO₂ (e a : Gamma0Note) : Arith (tiUptoSegSO₂ e a) :=
  arith_toSOAt arith_segWitness _

/-- **From `∀²X TI(≺₁, b̄, X)` to transfinite induction along the segment below `ε_e`,
below `ā`**, for any `a < b`: `spec₂` at the guarded formula, the lifted relativisation
implication, modus ponens. -/
theorem acaplus_tiUptoSeg_of_allTI (e a b : Gamma0Note) (hab : a < b)
    (h : Provable ACAplus (allTI (gamma0Term b))) :
    Provable ACAplus (tiUptoSegSO₂ e a) := by
  have h1 : Provable ACAplus (toSOAt segWitness
      (Gentzen.tiUptoAt precCode₁ (SegBridgeE.segGuardE e) (gamma0Term b))) := by
    have h2 := spec₂ h (arith_toSOAt arith_segWitness (SegBridgeE.segGuardE e))
    rwa [subst₁_tiBody_gen] at h2
  have h3 : Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      ((SegBridgeE.relImpBodyE e (gamma0Term a) (gamma0Term b)).univCl))) :=
    lift_paLX_seg (SegBridgeE.concrete_relImpE e _ _
      (Gentzen.Epsilon1UpperBound.concrete_gamma0_prec hab))
  rw [emb_univCl_of_closed (SegBridgeE.freeVariables_relImpBodyE e
    (by simp [gamma0Term]) (by simp [gamma0Term]))] at h3
  have h4 : Provable ACAplus
      (∼(toSOAt segWitness (Gentzen.tiUptoAt precCode₁ (SegBridgeE.segGuardE e)
          (gamma0Term b))) ⋎
        toSOAt segWitness (Gentzen.tiUptoAt (Gentzen.EpsilonSegmentOrder.precCodeSeg e)
          (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) (gamma0Term a))) := by
    have e1 : toSOAt segWitness (SegBridgeE.relImpBodyE e (gamma0Term a) (gamma0Term b)) =
        ∼(toSOAt segWitness (Gentzen.tiUptoAt precCode₁ (SegBridgeE.segGuardE e)
            (gamma0Term b))) ⋎
          toSOAt segWitness (Gentzen.tiUptoAt (Gentzen.EpsilonSegmentOrder.precCodeSeg e)
            (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) (gamma0Term a)) := by
      show toSOAtB segWitness (∼(Gentzen.tiUptoAt precCode₁ (SegBridgeE.segGuardE e)
          (gamma0Term b)) ⋎
        Gentzen.tiUptoAt (Gentzen.EpsilonSegmentOrder.precCodeSeg e)
          (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) (gamma0Term a)) = _
      rw [toSOAtB_or, toSOAtB_neg]
    rw [e1] at h3
    exact Provable_mono_ACAplus h3
  have h5 := cutP h1 h4
  have e2 : tiUptoSegSO₂ e a = toSOAt segWitness (Gentzen.tiUptoAt
      (Gentzen.EpsilonSegmentOrder.precCodeSeg e)
      (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) (gamma0Term a)) := by
    have hp : (Gentzen.EpsilonSegmentOrder.precCodeSeg e).freeVariables = ∅ :=
      Gentzen.EpsilonSegmentOrder.freeVariables_precCodeSeg e
    have ht : (gamma0Term a).freeVariables = ∅ := by simp [gamma0Term]
    have hcl : (TIupto (Gentzen.EpsilonSegmentOrder.precCodeSeg e)
        (gamma0Term a)).freeVariables = ∅ :=
      Gentzen.LowerSyntax.freeVariables_TIupto hp ht
    rw [Gentzen.Epsilon1UpperBound.tiUptoAt_X_eq']
    show toSOAt segWitness (FirstOrder.Rewriting.emb
      ((TIupto (Gentzen.EpsilonSegmentOrder.precCodeSeg e) (gamma0Term a)).univCl)) = _
    rw [emb_univCl_of_closed hcl]
  rw [e2]
  exact h5

/-! ### Iterating the ε-jump, up to `φ_2(0)` -/

/-- The ε-tower `ε₀, ε_{ε₀}, ε_{ε_{ε₀}}, ...`. -/
def epsIter : ℕ → Gamma0Note
  | 0 => epsilonNote 0
  | n + 1 => epsilonNote (epsIter n)

/-- **`ACA^+ ⊢ ∀²X TI(≺₁, ε̄-tower_n, X)` for every `n`**: `EpsProg.ti_epsilon_all` at
`ε₀`, then `n` ε-jumps. -/
theorem allTI_epsIter : ∀ n : ℕ, Provable ACAplus (allTI (gamma0Term (epsIter n)))
  | 0 => Provable_mono_ACAplus (ti_epsilon_all 0 (Gamma0Note.epsilon_pos 0))
  | n + 1 => epsJump_plus (epsIter n) (allTI_epsIter n)

/-- The notation for `φ_2(0)`, the first fixed point of `a ↦ ε_a`. -/
def phiTwoZero : Gamma0Note := Gamma0Note.veblenNote (Gamma0Note.ofNat 2) 0

theorem repr_phiTwoZero : Gamma0Note.repr phiTwoZero = Ordinal.veblen 2 0 := by
  simp [phiTwoZero]

theorem repr_epsIter : ∀ n : ℕ,
    Gamma0Note.repr (epsIter n) = (Ordinal.veblen 1)^[n + 1] 0
  | 0 => by simp [epsIter]
  | n + 1 => by
      rw [Function.iterate_succ_apply', ← repr_epsIter n]
      simp [epsIter]

/-- **The ε-tower is cofinal in `φ_2(0)`**: `φ_2(0) = sup_n ε-tower_n`. -/
theorem exists_lt_epsIter {a : Gamma0Note} (ha : a < phiTwoZero) : ∃ n, a < epsIter n := by
  rw [Gamma0Note.lt_def, repr_phiTwoZero,
    show (2 : Ordinal) = 1 + 1 from one_add_one_eq_two.symm, Ordinal.veblen_add_one,
    Ordinal.deriv_zero_right, Ordinal.lt_nfp_iff] at ha
  obtain ⟨n, hn⟩ := ha
  refine ⟨n, ?_⟩
  rw [Gamma0Note.lt_def, repr_epsIter, Function.iterate_succ_apply']
  exact lt_of_lt_of_le hn (Ordinal.right_le_veblen 1 _)

/-- **The upper bound for `ACA^+`**: for every notation `a < φ_2(0)`, `ACA^+` proves
transfinite induction along the segment of `≺₁` below `φ_2(0) = ε_{φ_2(0)}`, up to `ā`,
for the free set variable. -/
theorem aca_plus_upper_bound (a : Gamma0Note) (ha : a < phiTwoZero) :
    Provable ACAplus (tiUptoSegSO₂ phiTwoZero a) := by
  obtain ⟨n, hn⟩ := exists_lt_epsIter ha
  exact acaplus_tiUptoSeg_of_allTI phiTwoZero a (epsIter n) hn (allTI_epsIter n)

/-- The segment `EpsilonSegmentOrder.epsilonOrder phiTwoZero` (the notations below
`ε_{φ_2(0)}`) is the segment below `φ_2(0)`. -/
theorem lt_phiTwoZero_of_epsilonBelow (a : Gamma0Note.EpsilonBelow phiTwoZero) :
    a.1 < phiTwoZero := by
  have h := a.2
  rw [Gamma0Note.lt_def, Gamma0Note.repr_epsilonNote, repr_phiTwoZero,
    Ordinal.veblen_veblen_of_lt (by norm_num : (1 : Ordinal) < 2)] at h
  rw [Gamma0Note.lt_def, repr_phiTwoZero]
  exact h

/-- **The upper bound, on the segment the lower bound works over**: every element of
`Gamma0Note.EpsilonBelow phiTwoZero`. -/
theorem aca_plus_upper_bound_seg (a : Gamma0Note.EpsilonBelow phiTwoZero) :
    Provable ACAplus (tiUptoSegSO₂ phiTwoZero a.1) :=
  aca_plus_upper_bound a.1 (lt_phiTwoZero_of_epsilonBelow a)

end OrdinalAnalysis.ACA
