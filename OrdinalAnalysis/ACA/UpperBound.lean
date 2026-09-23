/-
  **The upper half of `|ACA| = ε_{ε₀}`, and the
  assembly of the two-sided theorem.**

  ### What the two halves say

  The ordinal analysis of `ACA` — arithmetical comprehension with the induction
  scheme for *every* second-order formula — is `ε_{ε₀}` (Schütte; the modern
  proof-theoretic treatment is Afshari–Rathjen, *Reverse mathematics and
  well-ordering principles: a pilot study*, APAL 160 (2009), and their
  *Ordinal analysis and the infinite Ramsey theorem*, CiE 2012, which is where
  the `ACA_∞`-style presentation replayed by `ACAOmega/` comes from).  The
  statement has two halves, about **one** sentence — `ACA/TI.lean`'s single
  source, transfinite induction along `EpsilonSegmentOrder.precCodeSeg
  (epsilonNote 0)`, the coded Veblen ordering restricted to the notations
  below `ε_{ε₀}`:

  * **upper** for every `a < ε_{ε₀}`, `Provable ACA (tiUptoSegSO a)` — every
    proper initial segment of that ordering carries transfinite induction;
  * **lower** `¬ Provable ACA TIsegSO` — the whole of it does not.

  The lower half is complete (`ACAOmega/ACATheorem.lean`); this
  file holds the upper half and the join.

  ### State of the upper half in this file

  Delivered here: every `a < ε₀` (milestone `M0` of the design note), by
  `ACA/Lifted.lean` — Gentzen's `ε₀` bound over the Veblen coding, lifted at the
  parameter `segWitness` through `ACA/Lift.lean`'s bridge, and relativised from
  `≺₁` to the segment ordering inside `paLX`.

  Not yet delivered: `ε₀ ≤ a < ε_{ε₀}`.  That range needs the internal ω-tower
  induction (⋆⋆) of design note §2 — `ACA ⊢ ∀c∀n∀u (Tower(u,n,c) → (∀²X TI(c,X))
  → (∀²X TI(u,X)))`, the single use of the full second-order induction scheme,
  and the one place where `ACA` outruns `ACA₀` — together with the
  `ε`-progressiveness (Prog) built on top of it.  `aca_theorem_of` below is the
  join, stated so that the two-sided theorem follows from that range and nothing
  else: when (⋆⋆)/(Prog) land, `aca_theorem` is one application away and this
  file is the only place that changes.
-/
import OrdinalAnalysis.ACA.EpsProg
import OrdinalAnalysis.ACA.SegmentBridge
import OrdinalAnalysis.ACAOmega.ACATheorem

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open scoped LO.FirstOrder

/-! ### Picking the notation: `ε_{ε₀}` is the sup of `ε_c` over notations `c < ε₀`

The last ordinal-arithmetic step of the upper bound.  `Ordinal.epsilon` is normal
and `ε₀` is a successor-limit ordinal, so continuity gives an *ordinal* `γ < ε₀`
with `repr a < ε_γ`; the ω-tower `0, ω^0, ω^{ω^0}, …` — cofinal below `ε₀` and
already `Gamma0Note`-valued — then supplies a *notation* above `γ`.  No
surjectivity of `Gamma0Note.repr` is needed. -/

open Ordinal in
private theorem isSuccLimit_epsilon (o : Ordinal) : Order.IsSuccLimit (Ordinal.epsilon o) := by
  rw [← Ordinal.omega0_opow_epsilon o]
  exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (Ordinal.epsilon_pos o).ne'

/-- The ω-tower `0, ω^0, ω^{ω^0}, …` inside `Gamma0Note` (the `vtower` of
`Gentzen/VeblenEpsilon0UpperBound.lean`, reproduced so this file is
self-contained). -/
private def epsTower : ℕ → Gamma0Note
  | 0 => 0
  | n + 1 => Gamma0Note.omegaPow (epsTower n)

@[simp] private theorem epsTower_zero : epsTower 0 = 0 := rfl

private theorem epsTower_succ (n : ℕ) : epsTower (n + 1) = Gamma0Note.omegaPow (epsTower n) :=
  rfl

open Ordinal in
private theorem repr_epsTower : ∀ n : ℕ,
    Gamma0Note.repr (epsTower n) = (fun x : Ordinal => ω ^ x)^[n] 0
  | 0 => by
      rw [epsTower_zero, Function.iterate_zero, id]
      exact Gamma0Note.repr_zero
  | n + 1 => by
      rw [epsTower_succ, Gamma0Note.repr_omegaPow, repr_epsTower n,
        Function.iterate_succ_apply']

/-- Every ordinal below `ε₀` lies below some stage of `epsTower`. -/
private theorem exists_lt_epsTower {γ : Ordinal} (hγ : γ < Ordinal.epsilon 0) :
    ∃ n : ℕ, γ < Gamma0Note.repr (epsTower n) := by
  rw [Ordinal.lt_epsilon_zero] at hγ
  obtain ⟨n, hn⟩ := hγ
  exact ⟨n, by rw [repr_epsTower]; exact hn⟩

/-- **Given `a < ε_{ε₀}`, a notation `c < ε₀` with `a < ε_c`.**  This is the step
that turns the `(Prog)`/`(TIψ)` output — one `ACA`-proof of `∀²X TI(≺₁, ε̄_c, X)`
for each external `c < ε₀` — into a statement about the whole segment below
`ε_{ε₀}`. -/
theorem exists_lt_epsilon_of_lt_epsEps (a : Gamma0Note)
    (ha : a < Gamma0Note.epsilonNote (Gamma0Note.epsilonNote 0)) :
    ∃ c, c < Gamma0Note.epsilonNote 0 ∧ a < Gamma0Note.epsilonNote c := by
  have ha' : Gamma0Note.repr a < Ordinal.epsilon (Ordinal.epsilon 0) := by
    have h1 := Gamma0Note.repr_epsilonNote_eq_epsilon (Gamma0Note.epsilonNote 0)
    rw [Gamma0Note.epsilonNote_zero_repr] at h1
    rw [Gamma0Note.lt_def] at ha
    rwa [h1] at ha
  obtain ⟨γ, hγlt, hγ⟩ :=
    (Ordinal.isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_epsilon 0) |>.mp ha'
  obtain ⟨n, hn⟩ := exists_lt_epsTower hγlt
  refine ⟨epsTower n, ?_, ?_⟩
  · rw [Gamma0Note.lt_def, Gamma0Note.epsilonNote_zero_repr, repr_epsTower]
    exact Ordinal.iterate_omega0_opow_lt_epsilon_zero n
  · rw [Gamma0Note.lt_def, Gamma0Note.repr_epsilonNote_eq_epsilon]
    calc Gamma0Note.repr a < Ordinal.epsilon γ := hγ
      _ < Ordinal.epsilon (Gamma0Note.repr (epsTower n)) :=
          (Ordinal.isNormal_veblen 1).strictMono hn

/-! ### The upper half, on the range reached -/

/-- **The upper bound below `ε₀`** (milestone `M0`).  For every Veblen notation
`a < ε₀`, `ACA` proves transfinite induction along the `ε_{ε₀}`-segment ordering
below `ā`, for the free set variable `X₀`.

Two steps, both inside the two-layer discipline: the *first-order* content is
`VeblenEpsilon0UpperBound.concrete_eps0_ti` at the relativising formula
`y ≺₁ ε̄_{ε₀} → X y` (`Relativise.segGuard`), converted to the segment ordering
by `Relativise.concrete_tiUptoSeg_of_closedTI₁`; the *second-order* content is
one application of `ACA/LiftTI.lean`'s `lift_tiUptoSeg`. -/
theorem aca_upper_bound_below_eps0 (a : Gamma0Note) (ha : a < Gamma0Note.epsilonNote 0) :
    Provable ACA (tiUptoSegSO a) :=
  aca_tiUptoSeg_of_lt_eps0 a ha

/-- The same, for an element of the segment `SegNote` itself. -/
theorem aca_upper_bound_seg_below_eps0 (a : SegNote) (ha : a.val < Gamma0Note.epsilonNote 0) :
    Provable ACA (tiUptoSegSO a.val) :=
  aca_upper_bound_below_eps0 a.val ha

/-! ### The lower half -/

/-- **The lower half**, re-exported from `ACAOmega/ACATheorem.lean`. -/
theorem aca_lower_bound : ¬ Provable ACA TIsegSO :=
  ACAOmega.ACATheorem.aca_lower_bound_statement

/-- **`ACA` is consistent**, by the same chain. -/
theorem aca_consistent : ¬ Provable ACA (⊥ : Proposition ℒₒᵣ) :=
  ACAOmega.ACATheorem.aca_consistent_statement

/-! ### The join

`aca_theorem_of` is the two-sided theorem with the upper half as a hypothesis.
Its only content is that the two halves are about the *same* sentence — the
`Provable ACA (tiUptoSegSO a)` that `ACA/TI.lean` defines and that
`ACAOmega/LowerBound₂.lean` refutes the unrestricted version of — which is the
integration risk the design note's §5.3 contract exists to retire.  It is
discharged here by type-checking, not by comment. -/

/-- **`|ACA| = ε_{ε₀}`, given the upper half.**  The hypothesis is exactly the
range `[0, ε_{ε₀})` of design-note milestone `M3`; everything else is in place. -/
theorem aca_theorem_of
    (H : ∀ a : SegNote, Provable ACA (tiUptoSegSO a.val)) :
    (∀ a : SegNote, Provable ACA (tiUptoSegSO a.val)) ∧ ¬ Provable ACA TIsegSO :=
  ⟨H, aca_lower_bound⟩

/-! ### The join, with the remaining gap reduced to `(Prog)`

`aca_theorem_of` above takes the whole segment `[0, ε_{ε₀})` as its hypothesis.
`ACA/TowerInduction.lean`'s `towerInduction` (design-note (⋆⋆)) and
`ACA/SegmentBridge.lean`'s `aca_tiUptoSeg_of_allTI` (the relativisation as a
`paLX`-implication, plus `exists_lt_epsilon_of_lt_epsEps`) shrink that hypothesis
to the single remaining mathematical input of the design note: **one `ACA`-proof
of `∀²X TI(≺₁, ε̄_c, X)` for each external `c < ε₀`** — i.e. items (Prog) +
(TIψ) + (Final).  Nothing else is missing. -/

/-- **The upper half, from the `(Prog)`/`(TIψ)` output.**  For `a < ε_{ε₀}`, pick
an external `c < ε₀` with `a < ε_c` (`exists_lt_epsilon_of_lt_epsEps`), then
instantiate `∀²X TI(≺₁, ε̄_c, X)` at the relativising formula and relativise
(`aca_tiUptoSeg_of_allTI`). -/
theorem aca_upper_bound_of_ti_epsilon
    (H : ∀ c : Gamma0Note, c < Gamma0Note.epsilonNote 0 →
      Provable ACA (allTI (Gentzen.Epsilon1UpperBound.gamma0Term
        (Gamma0Note.epsilonNote c))))
    (a : Gamma0Note) (ha : a < Gamma0Note.epsilonNote (Gamma0Note.epsilonNote 0)) :
    Provable ACA (tiUptoSegSO a) := by
  obtain ⟨c, hc, hac⟩ := exists_lt_epsilon_of_lt_epsEps a ha
  exact aca_tiUptoSeg_of_allTI a (Gamma0Note.epsilonNote c) hac (H c hc)

/-- **`|ACA| = ε_{ε₀}`, with `(Prog)` as the only hypothesis.**  When design-note
item (Prog) lands, `aca_theorem` is this theorem applied to it, and no other file
changes. -/
theorem aca_theorem_of_ti_epsilon
    (H : ∀ c : Gamma0Note, c < Gamma0Note.epsilonNote 0 →
      Provable ACA (allTI (Gentzen.Epsilon1UpperBound.gamma0Term
        (Gamma0Note.epsilonNote c)))) :
    (∀ a : SegNote, Provable ACA (tiUptoSegSO a.val)) ∧ ¬ Provable ACA TIsegSO :=
  ⟨fun a => aca_upper_bound_of_ti_epsilon H a.val a.property, aca_lower_bound⟩

/-- **The two-sided statement on the range reached so far.**  Below `ε₀` the
upper half is unconditional; the lower half is unconditional throughout. -/
theorem aca_theorem_below_eps0 :
    (∀ a : SegNote, a.val < Gamma0Note.epsilonNote 0 →
      Provable ACA (tiUptoSegSO a.val)) ∧ ¬ Provable ACA TIsegSO :=
  ⟨fun a ha => aca_upper_bound_seg_below_eps0 a ha, aca_lower_bound⟩

/-! ### `|ACA| = ε_{ε₀}`

The hypothesis of `aca_theorem_of_ti_epsilon` is discharged by
`ACA/EpsProg.lean`'s `ti_epsilon_all` — design-note items (Prog), (TIψ) and
(Final): the `Π¹₁` formula

    `ψ₀(g) :≡ ∀u (Eps(u,g) → ∀²X TI(≺₁, u, X))`

is `≺₁`-progressive (`epsProg`, which consumes the internal ε-cover of
`Gentzen/InternalEpsCover.lean`, the internal ω-tower induction (⋆⋆) of
`ACA/TowerInduction.lean`, and the successor step of
`Gentzen/VeblenSuccStep.lean`), and Gentzen's `ε₀` bound lifted at `ψ₀`
(`tiPsi`) then carries it along `≺₁` below every external `c < ε₀`. -/

/-- **The upper half, unconditionally.**  For every Veblen notation
`a < ε_{ε₀}`, `ACA` proves transfinite induction along the segment ordering
below `ā`. -/
theorem aca_upper_bound (a : Gamma0Note)
    (ha : a < Gamma0Note.epsilonNote (Gamma0Note.epsilonNote 0)) :
    Provable ACA (tiUptoSegSO a) :=
  aca_upper_bound_of_ti_epsilon ti_epsilon_all a ha

/--
**`|ACA| = ε_{ε₀}`.**

`ACA` — arithmetical comprehension with the induction scheme for *every*
second-order formula — proves transfinite induction along every proper initial
segment of the coded Veblen ordering below `ε_{ε₀}`, and does not prove it for
the whole of that ordering.  Both halves are about the *one* sentence
`ACA/TI.lean` defines.

The upper half is Schütte's; the modern proof-theoretic treatment replayed here
is Afshari–Rathjen (*Reverse mathematics and well-ordering principles*, APAL 160
(2009); *Ordinal analysis and the infinite Ramsey theorem*, CiE 2012), whose
`ACA_∞`-style presentation is what `ACAOmega/` formalises for the lower half.
-/
theorem aca_theorem :
    (∀ a : SegNote, Provable ACA (tiUptoSegSO a.val)) ∧ ¬ Provable ACA TIsegSO :=
  aca_theorem_of_ti_epsilon ti_epsilon_all

end OrdinalAnalysis.ACA
