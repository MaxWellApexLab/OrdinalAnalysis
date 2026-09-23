/-
  The non-provability half of the ordinal analysis of ramified analysis:
  `RA_{<ν+1}` does not prove transfinite induction along the coded Veblen
  ordering restricted to the segment below `φ_1^ν(ε₀)`, the `ν`-fold
  `ε`-function at `ε₀`.

  This is the composition of every piece the neighbouring files supply.

  * `Theory.lean`'s `RAlt_provable_iff` unpacks a proof into a finitary `LK`
    derivation of the goal together with finitely many negated axioms.
  * Foundation's `hauptsatz` (`FirstOrder/Hauptsatz.lean`) makes that
    derivation cut-free.
  * `Embed.lean`'s `replayR_closed` replays it into `RA_∞`, at cut rank `0`
    (the derivation is cut-free: `cutRankR_eq_zero_of_isCutFree` below) and at
    the derivation's own finite-recursion height `ordN d`, which lies below
    `ε₀` (`ordN_lt_epsilonNote`).
  * `Axioms.lean`/`NamingAxioms.lean`/`CutAxioms.lean` supply the derivability,
    at heights below `ε₀`, and the rank bound of every axiom of `RAlt (ν+1)`:
    an axiom of level `≤ ν` has rank at most `ω · ν ⊕ complexity`
    (`Rank.rank_le_omegaMul_lvlOf_nadd`).  `cut_axioms_below_epsilon` cuts the
    finitely many negated axioms away, landing at a cut rank `ω · ν ⊕ k` — a
    `Chain` of length `k` above `ω · ν` — and a height still below `ε₀`.
  * `BlockCut.lean`'s block elimination removes the finite part with
    `cutElimination_chain` (height `ω_k(α) < ε₀`) and then the `ν` blocks of
    width `ω` one at a time, each by predicative cut elimination at `ξ = 1`,
    landing at cut rank `0` and height `φ_1^ν(ω_k(α)) < φ_1^ν(ε₀)`
    (`veblenIter_lt_veblenIter`).
  * `SegOrder.lean`'s `vebSegOrderR 1 b` is the segment ordering below
    `φ_1(b)`, and `φ_1^ν(ε₀) = φ_1(φ_1^{ν−1}(ε₀))` (`veblenIter_succ'`);
    `OmegaDerivableR.toBelow` transports the cut-free derivation into that
    segment's own notation system.
  * `Boundedness.lean`'s `not_derivable_TI_R` then refutes the very derivation
    the assumption `RAlt (ν+1) ⊢! …` was shown to produce.

  The coarser statement at the segment below `φ_ν(ε₀)` follows at no cost,
  since `φ_1^ν(ε₀) ≤ φ_ν(ε₀)` (`veblenIter_one_le_veblenNote`).  For the
  ordinals of the theories see the boundedness and upper-bound files.

  Three auxiliary facts belong to no existing file and are proved here instead.

  * **`Language.DecidableEq LRA`.**  `hauptsatz` needs decidable equality on the
    language; `LRA = ℒₒᵣ + RALang` is a sum of two languages that already have
    it, so the instance is assembled, not proved.
  * **`cutRankR_eq_zero_of_isCutFree`.**  `cutRankR` only ever produces something
    other than `0` at a `cut` node, and `Derivation.IsCutFree` rules those out.
  * **`ordN_lt_epsilonNote`.**  `Proof/Bridge.lean`'s `ordN` produces, for a
    *finite* `LK`-derivation, a value built from finitely many
    `ofNat`/`succ`/`nadd` operations — so, read in `Gamma0Note`, it always sits
    below `ε₀`, `ε₀` being closed under exactly those three operations.
-/
import OrdinalAnalysis.Ramified.SegOrder
import OrdinalAnalysis.Ramified.Embed
import OrdinalAnalysis.Ramified.Axioms
import OrdinalAnalysis.Ramified.NamingAxioms
import OrdinalAnalysis.Ramified.CutAxioms
import OrdinalAnalysis.Ramified.BlockCut
import OrdinalAnalysis.Ramified.Boundedness
import Foundation.FirstOrder.Hauptsatz

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Derivation
open LO.FirstOrder.Derivation.Canonical (hauptsatz)
open OrdinalAnalysis.Gamma0Note (veblenNote epsilonNote VeblenBelow)
open OrdinalAnalysis.Ramified.OmegaDerivableR (Chain chain_nadd_ofNat veblenIter veblenIter_succ
  veblenIter_zero)

/-! ### `LRA` has decidable equality

`Foundation`'s `hauptsatz` needs `[L.DecidableEq]`; `LRA = ℒₒᵣ.add RALang` is a
sum of two languages that already have it. -/

instance instDecidableEqFuncLRA (k : ℕ) : DecidableEq (LRA.Func k) := by
  show DecidableEq ((ℒₒᵣ : Language).Func k ⊕ RALang.Func k)
  infer_instance

instance instDecidableEqRelLRA (k : ℕ) : DecidableEq (LRA.Rel k) := by
  show DecidableEq ((ℒₒᵣ : Language).Rel k ⊕ RALang.Rel k)
  infer_instance

instance instDecidableEqLRA : Language.DecidableEq LRA :=
  ⟨instDecidableEqFuncLRA, instDecidableEqRelLRA⟩

/-! ### A cut-free derivation has cut rank `0`

`cutRankR` only ever produces something other than `0` at a `cut` node
(`cutRankR_cut`); `Derivation.IsCutFree` rules that node out entirely, so the
induction is immediate at every other case. -/

theorem cutRankR_eq_zero_of_isCutFree :
    ∀ {Δ : Sequent LRA} {d : ⊢ᴸᴷ¹ Δ}, Derivation.IsCutFree d → cutRankR d = 0
  | _, _, .identity _ _ => rfl
  | _, _, .verum => rfl
  | _, _, .or h => by rw [cutRankR_or]; exact cutRankR_eq_zero_of_isCutFree h
  | _, _, .and hφ hψ => by
      rw [cutRankR_and, cutRankR_eq_zero_of_isCutFree hφ, cutRankR_eq_zero_of_isCutFree hψ]
      simp
  | _, _, .all h => by rw [cutRankR_all]; exact cutRankR_eq_zero_of_isCutFree h
  | _, _, .exs _ h => by rw [cutRankR_exs]; exact cutRankR_eq_zero_of_isCutFree h
  | _, _, .contraction _ h => by rw [cutRankR_contraction]; exact cutRankR_eq_zero_of_isCutFree h

/-! ### The replay height of a finite `LK`-derivation is below `ε₀`

`ordN` is built by finitely many applications of `ofNat 0`/`succ`/`nadd`
following the shape of the concrete derivation `d`; `ε₀` is closed under all
three (`Gamma0Note.ofNat_lt_epsilon`, `Gamma0Note.nadd_lt_epsilon`, and `succ`
being `(· ⊕ 1)` together with `Gamma0Note.one_lt_epsilon`). -/

private theorem succ_lt_epsilonNote_zero {x : Gamma0Note} (hx : x < epsilonNote 0) :
    OrdinalNotation.succ x < epsilonNote 0 := by
  rw [OrdinalNotation.Gamma0Note_succ]
  exact Gamma0Note.nadd_lt_epsilon hx (Gamma0Note.one_lt_epsilon 0)

theorem ordN_lt_epsilonNote : ∀ {Δ : Sequent LRA} (d : ⊢ᴸᴷ¹ Δ),
    (ordN d : Gamma0Note) < epsilonNote 0 := by
  intro Δ d
  induction d with
  | identity r v =>
      show (OrdinalNotation.ofNat 0 : Gamma0Note) < epsilonNote 0
      rw [OrdinalNotation.Gamma0Note_ofNat]
      exact Gamma0Note.ofNat_lt_epsilon 0 0
  | verum =>
      show (OrdinalNotation.ofNat 0 : Gamma0Note) < epsilonNote 0
      rw [OrdinalNotation.Gamma0Note_ofNat]
      exact Gamma0Note.ofNat_lt_epsilon 0 0
  | contraction d ss ih => exact ih
  | or d ih => exact succ_lt_epsilonNote_zero ih
  | and dp dq ihp ihq => exact succ_lt_epsilonNote_zero (Gamma0Note.nadd_lt_epsilon ihp ihq)
  | all d ih => exact succ_lt_epsilonNote_zero ih
  | exs d ih => exact succ_lt_epsilonNote_zero ih
  | cut dp dn ihp ihn => exact succ_lt_epsilonNote_zero (Gamma0Note.nadd_lt_epsilon ihp ihn)

/-! ### Every axiom of `RAlt ν` (or `RA Set.univ`) has a cut-free derivation below `ε₀`

None of `Ramified/AxiomsLogic.lean`, `AxiomsInduction.lean`, `NamingAxioms.lean` states
this — each of their derivability theorems packages its height inside an anonymous
`∃ β, …`, hiding the concrete value.  Since every one of those concrete values is,
inspected at the source, some finite combination of `hgtR`/`omegaGR`/finite numerals
under `nadd`, the bound is provable by unfolding the very same constructions with the
witness left visible, rather than by reasoning about the packaged theorems abstractly. -/

theorem hgtR_lt_epsilonNote (φ : Proposition LRA) (a : Gamma0Note) : hgtR φ < epsilonNote a := by
  show (OrdinalNotation.ofNat φ.complexity : Gamma0Note) < epsilonNote a
  rw [OrdinalNotation.Gamma0Note_ofNat]
  exact Gamma0Note.ofNat_lt_epsilon _ _

theorem omegaGR_lt_epsilonNote (a : Gamma0Note) : omegaGR < epsilonNote a :=
  Gamma0Note.omegaPow_lt_epsilon (Gamma0Note.one_lt_epsilon a)

/-- **`derivable_of_rFree_eqAxiom`, with its height exposed and bounded.** -/
theorem derivable_of_rFree_eqAxiom_lt_epsilon {σ : Sentence LRA} (h : σ ∈ 𝗘𝗤 LRA) (hR : RFree σ) :
    ∃ β : Gamma0Note, β < epsilonNote 0 ∧ OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb σ : Proposition LRA)] :=
  ⟨hgtR (Rewriting.emb σ : Proposition LRA), hgtR_lt_epsilonNote _ 0,
    omega_completeR (Rewriting.emb σ : Proposition LRA) (rFree_emb hR) (by simp)
      (by simpa only [Semiformula.eval_emb] using eval_of_eqAxiom h)⟩

/-- **`relExtX_derivable`, with its height exposed and bounded.**  Copies the proof of
`Ramified/AxiomsLogic.lean`'s `relExtX_derivable` verbatim; the height there is the visible
numeral `ofNat 5`. -/
theorem relExtX_derivable_lt_epsilon :
    ∃ β : Gamma0Note, β < epsilonNote 0 ∧ OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb (Theory.Eq.relExt (Sum.inr RARel.X : LRA.Rel 1)) : Proposition LRA)] := by
  refine ⟨OrdinalNotation.ofNat 5, ?_, ?_⟩
  · show (OrdinalNotation.ofNat 5 : Gamma0Note) < epsilonNote 0
    rw [OrdinalNotation.Gamma0Note_ofNat]; exact Gamma0Note.ofNat_lt_epsilon _ _
  · rw [emb_relExtX, evR_all]
    refine OmegaDerivableR.omegaRule (fun _ => OrdinalNotation.ofNat 4)
      (fun _ => OrdinalNotation.ofNat_lt_ofNat (by omega)) (fun m => ?_)
    rw [evInstR_inst_ev, subst_relX2, evR_all]
    refine OmegaDerivableR.omegaRule (fun _ => OrdinalNotation.ofNat 3)
      (fun _ => OrdinalNotation.ofNat_lt_ofNat (by omega)) (fun n => ?_)
    rw [evInstR_inst_ev, subst_relX1, ev_relX0]
    exact relX0_derivable m n

/-- **`relExtMem_derivable`, with its height exposed and bounded.**  Copies the proof of
`Ramified/AxiomsLogic.lean`'s `relExtMem_derivable` verbatim; the height there is
`nadd (ofNat 4) (ofNat 4)`. -/
theorem relExtMem_derivable_lt_epsilon (ν : Lv) :
    ∃ β : Gamma0Note, β < epsilonNote 0 ∧ OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb (Theory.Eq.relExt (Sum.inr (RARel.mem ν) : LRA.Rel 2)) : Proposition LRA)] := by
  refine ⟨OrdinalNotation.nadd (OrdinalNotation.ofNat 4) (OrdinalNotation.ofNat 4), ?_, ?_⟩
  · exact Gamma0Note.nadd_lt_epsilon (Gamma0Note.ofNat_lt_epsilon _ _) (Gamma0Note.ofNat_lt_epsilon _ _)
  · rw [emb_memExt]
    refine allClosureR_derivable (memX4 ν) (β := OrdinalNotation.ofNat 4) (fun w => ?_)
    have hw : (memX4 ν ⇜ fun i => (numAtR (w i) : SyntacticTerm LRA))
        = (∼(eqA (numAtR (w 0) : SyntacticTerm LRA) (numAtR (w 2))
              ⋏ (eqA (numAtR (w 1) : SyntacticTerm LRA) (numAtR (w 3)) ⋏ ⊤)))
          ⋎ (∼(memAtG ν (numAtR (w 0) : SyntacticTerm LRA) (numAtR (w 1)))
              ⋎ memAtG ν (numAtR (w 2) : SyntacticTerm LRA) (numAtR (w 3))) := by
      simp [memX4, rew_memAtG]
    rw [hw]
    have hmem1 : evR (memAtG ν (numAtR (w 0) : SyntacticTerm LRA) (numAtR (w 1)))
        = memAtG ν (numAtR (w 0) : SyntacticTerm LRA) (numAtR (w 1)) := by
      have h : (fun i : Fin 2 => evTR ((![(numAtR (w 0) : SyntacticTerm LRA), numAtR (w 1)]
          : Fin 2 → SyntacticTerm LRA) i)) = ![numAtR (w 0), numAtR (w 1)] := by
        funext i; fin_cases i <;> simp
      exact congrArg (Semiformula.rel (Sum.inr (RARel.mem ν) : LRA.Rel 2)) h
    have hmem2 : evR (memAtG ν (numAtR (w 2) : SyntacticTerm LRA) (numAtR (w 3)))
        = memAtG ν (numAtR (w 2) : SyntacticTerm LRA) (numAtR (w 3)) := by
      have h : (fun i : Fin 2 => evTR ((![(numAtR (w 2) : SyntacticTerm LRA), numAtR (w 3)]
          : Fin 2 → SyntacticTerm LRA) i)) = ![numAtR (w 2), numAtR (w 3)] := by
        funext i; fin_cases i <;> simp
      exact congrArg (Semiformula.rel (Sum.inr (RARel.mem ν) : LRA.Rel 2)) h
    have heq1 : evR (eqA (numAtR (w 0) : SyntacticTerm LRA) (numAtR (w 2)))
        = eqA (numAtR (w 0) : SyntacticTerm LRA) (numAtR (w 2)) := by
      have h : (fun i : Fin 2 => evTR ((![(numAtR (w 0) : SyntacticTerm LRA), numAtR (w 2)]
          : Fin 2 → SyntacticTerm LRA) i)) = ![numAtR (w 0), numAtR (w 2)] := by
        funext i; fin_cases i <;> simp
      exact congrArg (Semiformula.rel (Language.Eq.eq : LRA.Rel 2)) h
    have heq2 : evR (eqA (numAtR (w 1) : SyntacticTerm LRA) (numAtR (w 3)))
        = eqA (numAtR (w 1) : SyntacticTerm LRA) (numAtR (w 3)) := by
      have h : (fun i : Fin 2 => evTR ((![(numAtR (w 1) : SyntacticTerm LRA), numAtR (w 3)]
          : Fin 2 → SyntacticTerm LRA) i)) = ![numAtR (w 1), numAtR (w 3)] := by
        funext i; fin_cases i <;> simp
      exact congrArg (Semiformula.rel (Language.Eq.eq : LRA.Rel 2)) h
    simp only [evR_or, evR_and, evR_neg, evR_verum, hmem1, hmem2, heq1, heq2]
    exact memX0_derivable ν (w 0) (w 1) (w 2) (w 3)

/-- **`relExt_inl_derivable`, with its height exposed and bounded.** -/
theorem relExt_inl_derivable_lt_epsilon {k : ℕ} (r : (ℒₒᵣ : Language).Rel k) :
    ∃ β : Gamma0Note, β < epsilonNote 0 ∧ OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb (Theory.Eq.relExt (Sum.inl r : LRA.Rel k)) : Proposition LRA)] :=
  derivable_of_rFree_eqAxiom_lt_epsilon (Theory.eqAxiom.relExt (L := LRA) (Sum.inl r))
    (rFree_relExt_inl r)

/-- **`eq_axiom_derivable`, with its height exposed and bounded.** -/
theorem eq_axiom_derivable_lt_epsilon {σ : Sentence LRA} (h : σ ∈ 𝗘𝗤 LRA) :
    ∃ β : Gamma0Note, β < epsilonNote 0 ∧ OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb σ : Proposition LRA)] := by
  cases h with
  | refl => exact derivable_of_rFree_eqAxiom_lt_epsilon Theory.eqAxiom.refl rFree_eqRefl
  | symm => exact derivable_of_rFree_eqAxiom_lt_epsilon Theory.eqAxiom.symm rFree_eqSymm
  | trans => exact derivable_of_rFree_eqAxiom_lt_epsilon Theory.eqAxiom.trans rFree_eqTrans
  | funcExt f => exact derivable_of_rFree_eqAxiom_lt_epsilon (Theory.eqAxiom.funcExt f) (rFree_funcExt f)
  | relExt r =>
      cases r with
      | inl r => exact relExt_inl_derivable_lt_epsilon r
      | inr rX =>
          cases rX with
          | X => exact relExtX_derivable_lt_epsilon
          | mem ν => exact relExtMem_derivable_lt_epsilon ν

/-- **`paMinus_axiom_derivable`, with its height exposed and bounded.** -/
theorem paMinus_axiom_derivable_lt_epsilon {σ : Sentence LRA} (h : σ ∈ Theory.lMap toLRA 𝗣𝗔⁻) :
    ∃ β : Gamma0Note, β < epsilonNote 0 ∧ OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb σ : Proposition LRA)] := by
  obtain ⟨τ, hτ, rfl⟩ := h
  exact ⟨hgtR (Rewriting.emb (Semiformula.lMap toLRA τ) : Proposition LRA),
    hgtR_lt_epsilonNote _ 0, omega_completeR_sentence τ (Theory.models ℕ 𝗣𝗔⁻ hτ)⟩

/-- **`induction_axiom_derivable`, with its height exposed and bounded.**  Copies the
proof of `Ramified/AxiomsInduction.lean`'s `induction_axiom_derivable` verbatim; the
height there is visibly `nadd (nadd omegaGR (ofNat 2)) (ofNat (0 + (succInd φ).fvSup))`. -/
theorem induction_axiom_derivable_lt_epsilon {Γ : Semiformula LRA ℕ 1 → Prop}
    {σ : Sentence LRA} (h : σ ∈ InductionScheme LRA Γ) :
    ∃ β : Gamma0Note, β < epsilonNote 0 ∧ OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb σ : Proposition LRA)] := by
  obtain ⟨φ, -, rfl⟩ := h
  refine ⟨OrdinalNotation.nadd (OrdinalNotation.nadd omegaGR (OrdinalNotation.ofNat 2))
      (OrdinalNotation.ofNat (0 + (succInd φ).fvSup)), ?_, ?_⟩
  · exact Gamma0Note.nadd_lt_epsilon
      (Gamma0Note.nadd_lt_epsilon (omegaGR_lt_epsilonNote 0) (Gamma0Note.ofNat_lt_epsilon _ _))
      (Gamma0Note.ofNat_lt_epsilon _ _)
  · have hemb : (Rewriting.emb (Semiformula.univCl (succInd φ)) : Proposition LRA)
        = ∀¹* (Rew.fixitr 0 (succInd φ).fvSup ▹ (succInd φ)) := by
      simp [Semiformula.univCl']
    rw [hemb]
    refine allClosureR_derivable (Rew.fixitr 0 (succInd φ).fvSup ▹ (succInd φ)) (fun w => ?_)
    have key : (Rew.fixitr 0 (succInd φ).fvSup ▹ (succInd φ))
          ⇜ (fun i : Fin (0 + (succInd φ).fvSup) => (numAtR (w i) : SyntacticTerm LRA))
        = Rew.rewrite (fun y => (numAtR (if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0)
            : SyntacticTerm LRA)) ▹ (succInd φ) := by
      have hvec : (fun i : Fin (0 + (succInd φ).fvSup) => (numAtR (w i) : SyntacticTerm LRA))
          = (fun i : Fin (0 + (succInd φ).fvSup) =>
              (fun y => (numAtR (if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0)
                : SyntacticTerm LRA)) (i : ℕ)) := by
        funext i
        simp only [dif_pos i.isLt, Fin.eta]
      rw [hvec]
      exact Semiformula.subst_comp_fixitr_eq_map (succInd φ)
        (fun y => (numAtR (if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0) : SyntacticTerm LRA))
    have hns : Rew.rewrite
          (fun y => (numAtR (if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0) : SyntacticTerm LRA))
        = numSubstR (fun y => if hy : y < 0 + (succInd φ).fvSup then w ⟨y, hy⟩ else 0) := rfl
    rw [key, hns, numSubstR_succInd]
    exact succIndR_derivable _

/-- **`naming_axiom_derivable`, with its height exposed and bounded.**  The heights
of `Ramified/NamingAxioms.lean`'s `nameOutP_derivable`/`nameInP_derivable` are the
visible finite sums `ofNat (g + 2c + 4) ⊕ ofNat 3`. -/
theorem naming_axiom_derivable_lt_epsilon {Λ : Set Lv} {σ : Sentence LRA} (h : σ ∈ NamingAxioms Λ) :
    ∃ β : Gamma0Note, β < epsilonNote 0 ∧ OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb σ : Proposition LRA)] := by
  obtain ⟨μ, A, -, h0, hA, rfl | rfl⟩ := h
  · exact ⟨_, Gamma0Note.nadd_lt_epsilon (Gamma0Note.ofNat_lt_epsilon _ _)
      (Gamma0Note.ofNat_lt_epsilon _ _), nameOutP_derivable h0 hA⟩
  · exact ⟨_, Gamma0Note.nadd_lt_epsilon (Gamma0Note.ofNat_lt_epsilon _ _)
      (Gamma0Note.ofNat_lt_epsilon _ _), nameInP_derivable h0 hA⟩

/-- **Every axiom of `RAlt ν` (`ν ≥ 1`) has a cut-free derivation below `ε₀`.** -/
theorem RAlt_axiom_derivable_lt_epsilon {ν : Lv} (hν : 1 ≤ ν) :
    ∀ σ ∈ RAlt ν, ∃ β : Gamma0Note, β < epsilonNote 0 ∧
      OmegaDerivableR trueArithLitsR evInstR 0 β [evR (Rewriting.emb σ : Proposition LRA)] := by
  -- `hν` is not needed by any case below (none of them reads the level guard);
  -- kept in the signature to match `RAlt_axiom_derivable`'s API.
  have _hν := hν
  rintro σ (⟨hσ, -⟩ | hσ | hσ | hσ)
  · exact eq_axiom_derivable_lt_epsilon hσ
  · exact paMinus_axiom_derivable_lt_epsilon hσ
  · exact induction_axiom_derivable_lt_epsilon hσ
  · exact naming_axiom_derivable_lt_epsilon hσ

/-- **Every axiom of `RA Set.univ` has a cut-free derivation below `ε₀`.** -/
theorem RA_univ_axiom_derivable_lt_epsilon :
    ∀ σ ∈ RA Set.univ, ∃ β : Gamma0Note, β < epsilonNote 0 ∧
      OmegaDerivableR trueArithLitsR evInstR 0 β [evR (Rewriting.emb σ : Proposition LRA)] := by
  rintro σ (hσ | hσ | hσ | hσ)
  · exact eq_axiom_derivable_lt_epsilon hσ
  · exact paMinus_axiom_derivable_lt_epsilon hσ
  · exact induction_axiom_derivable_lt_epsilon hσ
  · exact naming_axiom_derivable_lt_epsilon hσ

/-! ### `1 = OrdinalNotation.ofNat 1`, and its consequences -/

theorem ofNat_one_eq_one : (OrdinalNotation.ofNat 1 : Gamma0Note) = 1 := by
  rw [OrdinalNotation.Gamma0Note_ofNat]
  apply Gamma0Note.repr_injective
  rw [Gamma0Note.repr_ofNat, Gamma0Note.repr_one]
  norm_num

/-! ### The replay-and-cut chain, generic in the theory

Everything from here on is stated for an arbitrary `T : Theory LRA` supplied with its
own axiom-derivability and rank/level bounds, so that it survives unchanged across a
future revision of `RAlt`/`RA` (for instance, codes gaining set parameters): the chain
never inspects `T`'s definition, only the hypotheses `hax`/`hrk`/`hlvl` supplied at each
call site. -/

/-- **The replay of a finitary proof, generic in the theory.**  Unpacks `h : T ⊢! σ`
into a cut-free `LK` derivation of `σ` together with finitely many negated axioms of
`T`, and replays it into `RA_∞` at cut rank `0` and at a height already known to be
below `ε₀` (`ordN_lt_epsilonNote`). -/
private theorem replay_of_provable {T : Theory LRA} {σ : Sentence LRA} (h : T ⊢! σ) :
    ∃ (Δ : List (Sentence LRA)) (α : Gamma0Note), (∀ τ ∈ Δ, τ ∈ T) ∧ α < epsilonNote 0 ∧
      OmegaDerivableR trueArithLitsR evInstR 0 α
        (((σ : Proposition LRA) :: ∼Sequent.embed Δ).map evR) := by
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp ⟨h⟩
  obtain ⟨d', hcf⟩ := hauptsatz d
  have hcr0 : cutRankR d' = 0 := cutRankR_eq_zero_of_isCutFree hcf
  have hclosed : ∀ φ ∈ ((σ : Proposition LRA) :: ∼Sequent.embed Δ), φ.freeVariables = ∅ := by
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ'
    · exact Semiformula.freeVariables_emb σ
    · obtain ⟨ψ, hψ, hφeq⟩ : ∃ ψ ∈ Δ, ∼(Rewriting.emb ψ : Proposition LRA) = φ := by
        simpa [List.tilde_def, Sequent.embed, List.mem_map] using hφ'
      rw [← hφeq, Semiformula.freeVariables_not]; exact Semiformula.freeVariables_emb ψ
  have hreplay := replayR_closed (O := Gamma0Note) d' hclosed
  rw [hcr0] at hreplay
  exact ⟨Δ, ordN d', hΔ, ordN_lt_epsilonNote d', hreplay⟩

/-- A finite list of formulas has a common complexity bound (of its `evR`/`emb`
images) — the finite-part analogue of `Embed.lean`'s `exists_omegaMul_bound`. -/
private theorem exists_complexity_bound (Δ : List (Sentence LRA)) :
    ∃ k : ℕ, ∀ ψ ∈ Δ, (evR (Rewriting.emb ψ : Proposition LRA)).complexity < k := by
  induction Δ with
  | nil => exact ⟨0, by simp⟩
  | cons ψ Δ ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨max k ((evR (Rewriting.emb ψ : Proposition LRA)).complexity + 1), fun τ hτ => ?_⟩
      rcases List.mem_cons.mp hτ with rfl | hτ'
      · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
      · exact lt_of_lt_of_le (hk τ hτ') (le_max_left _ _)

/-- A finite list of formulas has a common level bound (of its `emb` images). -/
private theorem exists_level_bound (Δ : List (Sentence LRA)) :
    ∃ ν : Lv, ∀ ψ ∈ Δ, lvlOf (Rewriting.emb ψ : Proposition LRA) ≤ ν := by
  induction Δ with
  | nil => exact ⟨0, by simp⟩
  | cons ψ Δ ih =>
      obtain ⟨ν, hν⟩ := ih
      refine ⟨max ν (lvlOf (Rewriting.emb ψ : Proposition LRA)), fun τ hτ => ?_⟩
      rcases List.mem_cons.mp hτ with rfl | hτ'
      · exact le_max_right _ _
      · exact le_trans (hν τ hτ') (le_max_left _ _)

/-- **The finite-part rank bound at a level `ν`, from a per-axiom level bound.**
Given every axiom of `Δ` (a finite list contained in `T`) has level `≤ ν`, there is a
finite `k` such that every axiom's rank is strictly below `ρ := ω · ν ⊕ k`, and `ρ` is
exactly `k` predecessor-bound steps above `ω · ν`. -/
private theorem exists_rank_chain_bound {ν : Lv} {Δ : List (Sentence LRA)}
    (hlvl : ∀ τ ∈ Δ, lvlOf (Rewriting.emb τ : Proposition LRA) ≤ ν) :
    ∃ ρ : Gamma0Note, ∃ k : ℕ, Chain k (omegaMul ν) ρ ∧
      ∀ τ ∈ Δ, rank (evR (Rewriting.emb τ : Proposition LRA)) < ρ := by
  obtain ⟨k, hk⟩ := exists_complexity_bound Δ
  refine ⟨Gamma0Note.nadd (omegaMul ν) (Gamma0Note.ofNat k), k, chain_nadd_ofNat _ k,
    fun τ hτ => ?_⟩
  have hbound := rank_le_nadd_ofNat_complexity_of_level (ν := ν)
    (φ := evR (Rewriting.emb τ : Proposition LRA)) (by rw [lvlOf_evR]; exact hlvl τ hτ)
  exact lt_of_le_of_lt hbound
    (Gamma0Note.nadd_lt_nadd_right _ (Gamma0Note.ofNat_lt_ofNat (hk τ hτ)))

/-- **Step 1, plain.**  The replay-and-cut chain at a uniform cut rank `ρ`, generic in
the theory `T`. -/
theorem provable_omegaDerivable_of (T : Theory LRA) {ρ : Gamma0Note}
    (hax : ∀ σ ∈ T, ∃ β : Gamma0Note, OmegaDerivableR trueArithLitsR evInstR 0 β
        [evR (Rewriting.emb σ : Proposition LRA)])
    (hrk : ∀ σ ∈ T, rank (evR (Rewriting.emb σ : Proposition LRA)) < ρ)
    {σ : Sentence LRA} (h : T ⊢! σ) :
    ∃ α : Gamma0Note,
      OmegaDerivableR trueArithLitsR evInstR ρ α [evR (Rewriting.emb σ : Proposition LRA)] := by
  obtain ⟨Δ, α, hΔ, -, hreplay⟩ := replay_of_provable h
  have hreplay' : OmegaDerivableR trueArithLitsR evInstR ρ α
      ([evR (Rewriting.emb σ : Proposition LRA)] ++ (∼Sequent.embed Δ).map evR) := by
    have := hreplay.mono_rank (gamma0_zero_le ρ)
    simpa [List.map_cons] using this
  obtain ⟨α', hα'⟩ := cut_axioms_of T hax hrk Δ hΔ hreplay'
  exact ⟨α', hα'⟩

/-- **Step 1, sharp form, at a fixed level `ν`.**  Generic in the theory `T`, given a
uniform per-axiom level bound at `ν`; this is the shape `RAlt (ν+1)` supplies. -/
theorem provable_omegaDerivable_chain_of (T : Theory LRA) {ν : Lv}
    (hax : ∀ σ ∈ T, ∃ β : Gamma0Note, OmegaDerivableR trueArithLitsR evInstR 0 β
        [evR (Rewriting.emb σ : Proposition LRA)])
    (hlvl : ∀ σ ∈ T, lvlOf (Rewriting.emb σ : Proposition LRA) ≤ ν)
    {σ : Sentence LRA} (h : T ⊢! σ) :
    ∃ (k : ℕ) (ρ α : Gamma0Note), Chain k (omegaMul ν) ρ ∧
      OmegaDerivableR trueArithLitsR evInstR ρ α [evR (Rewriting.emb σ : Proposition LRA)] := by
  obtain ⟨Δ, α₀, hΔ, -, hreplay⟩ := replay_of_provable h
  obtain ⟨ρ, k', hchain, hrk⟩ := exists_rank_chain_bound (fun τ hτ => hlvl τ (hΔ τ hτ))
  have hreplay' : OmegaDerivableR trueArithLitsR evInstR ρ α₀
      ([evR (Rewriting.emb σ : Proposition LRA)] ++ (∼Sequent.embed Δ).map evR) := by
    have := hreplay.mono_rank (gamma0_zero_le ρ)
    simpa [List.map_cons] using this
  obtain ⟨α, hα⟩ := cut_axioms_of {τ | τ ∈ Δ} (fun τ hτ => hax τ (hΔ τ hτ)) hrk Δ
    (fun τ hτ => hτ) hreplay'
  exact ⟨k', ρ, α, hchain, hα⟩

/-- **Step 1, sharp form, with the level found from the finite proof itself.**  Generic
in the theory `T`, needing *no* level hypothesis on `T` at all — only that every axiom
is derivable — because the level bound is read off the finitely many axioms the proof
actually uses.  This is the shape `RA Set.univ` needs: no single level bounds the
theory, but every individual finite proof only ever uses finitely many levels. -/
theorem provable_omegaDerivable_chain_of_exists (T : Theory LRA)
    (hax : ∀ σ ∈ T, ∃ β : Gamma0Note, OmegaDerivableR trueArithLitsR evInstR 0 β
        [evR (Rewriting.emb σ : Proposition LRA)])
    {σ : Sentence LRA} (h : T ⊢! σ) :
    ∃ (ν : Lv), 1 ≤ ν ∧ ∃ (k : ℕ) (ρ α : Gamma0Note), Chain k (omegaMul ν) ρ ∧
      OmegaDerivableR trueArithLitsR evInstR ρ α [evR (Rewriting.emb σ : Proposition LRA)] := by
  obtain ⟨Δ, α₀, hΔ, -, hreplay⟩ := replay_of_provable h
  obtain ⟨ν₀, hν₀⟩ := exists_level_bound Δ
  set ν : Lv := max ν₀ 1 with hνdef
  have hν1 : 1 ≤ ν := le_max_right _ _
  have hlvl : ∀ τ ∈ Δ, lvlOf (Rewriting.emb τ : Proposition LRA) ≤ ν :=
    fun τ hτ => le_trans (hν₀ τ hτ) (le_max_left _ _)
  obtain ⟨ρ, k', hchain, hrk⟩ := exists_rank_chain_bound hlvl
  have hreplay' : OmegaDerivableR trueArithLitsR evInstR ρ α₀
      ([evR (Rewriting.emb σ : Proposition LRA)] ++ (∼Sequent.embed Δ).map evR) := by
    have := hreplay.mono_rank (gamma0_zero_le ρ)
    simpa [List.map_cons] using this
  obtain ⟨α, hα⟩ := cut_axioms_of {τ | τ ∈ Δ} (fun τ hτ => hax τ (hΔ τ hτ)) hrk Δ
    (fun τ hτ => hτ) hreplay'
  exact ⟨ν, hν1, k', ρ, α, hchain, hα⟩

/-! ### The `RAlt`/`RA Set.univ` instances of step 1 -/

/-- **Step 1, plain, for `RAlt ν`**: cut rank `ω · ν`. -/
theorem provable_omegaDerivable {ν : Lv} (hν : 1 ≤ ν) {σ : Sentence LRA} (h : RAlt ν ⊢! σ) :
    ∃ α : Gamma0Note, OmegaDerivableR trueArithLitsR evInstR (omegaMul ν) α
      [evR (Rewriting.emb σ : Proposition LRA)] :=
  provable_omegaDerivable_of (RAlt ν) (RAlt_axiom_derivable' hν)
    (fun _τ hτ => rank_evR_emb_lt_of_mem_RAlt hν hτ) h

/-- Every axiom of `RAlt (ν+1)` has level `≤ ν`. -/
theorem lvlOf_emb_le_of_mem_RAlt_succ {ν : Lv} {τ : Sentence LRA} (hτ : τ ∈ RAlt (ν + 1)) :
    lvlOf (Rewriting.emb τ : Proposition LRA) ≤ ν :=
  Nat.lt_succ_iff.mp (lvlOf_emb_lt_of_mem_RAlt (ν := ν + 1) (Nat.le_add_left 1 ν) hτ)

/-- **Step 1, sharp form, for `RAlt (ν+1)`**: a chain above `ω · ν`. -/
theorem provable_omegaDerivable_chain {ν : Lv} {σ : Sentence LRA}
    (h : RAlt (ν + 1) ⊢! σ) :
    ∃ (k : ℕ) (ρ α : Gamma0Note), Chain k (omegaMul ν) ρ ∧
      OmegaDerivableR trueArithLitsR evInstR ρ α [evR (Rewriting.emb σ : Proposition LRA)] :=
  provable_omegaDerivable_chain_of (RAlt (ν + 1)) (ν := ν)
    (RAlt_axiom_derivable' (Nat.le_add_left 1 ν)) (fun _ hτ => lvlOf_emb_le_of_mem_RAlt_succ hτ) h

/-- **Step 1, sharp form, for `RA Set.univ`.** -/
theorem provable_omegaDerivable_univ {σ : Sentence LRA} (h : RA Set.univ ⊢! σ) :
    ∃ (ν : Lv), 1 ≤ ν ∧ ∃ (k : ℕ) (ρ α : Gamma0Note), Chain k (omegaMul ν) ρ ∧
      OmegaDerivableR trueArithLitsR evInstR ρ α [evR (Rewriting.emb σ : Proposition LRA)] :=
  provable_omegaDerivable_chain_of_exists (RA Set.univ) RA_univ_axiom_derivable' h

/-! ### Step 2: cut elimination down to a height below `φ_1^ν(ε₀)`

`cut_axioms_below_epsilon` is `CutAxioms.lean`'s `cut_axioms_of`, specialised to track,
alongside the cut rank bound, that every height in play — the axioms' and the
accumulating result's — stays below `ε₀`; this is what lets the *final* height, after
the block elimination, be bounded by `φ_1^ν(ε₀)` rather than left unbounded. -/

private theorem cut_axioms_below_epsilon (T : Theory LRA) {ρ : Gamma0Note}
    (hax : ∀ σ ∈ T, ∃ β : Gamma0Note, β < epsilonNote 0 ∧ OmegaDerivableR trueArithLitsR evInstR 0 β
      [evR (Rewriting.emb σ : Proposition LRA)])
    (hrk : ∀ σ ∈ T, rank (evR (Rewriting.emb σ : Proposition LRA)) < ρ) :
    ∀ (Δ : List (Sentence LRA)), (∀ σ ∈ Δ, σ ∈ T) → ∀ {α : Gamma0Note}, α < epsilonNote 0 →
      ∀ {Θ : Sequent LRA}, OmegaDerivableR trueArithLitsR evInstR ρ α
        (Θ ++ (∼Sequent.embed Δ).map evR) →
      ∃ α' : Gamma0Note, α' < epsilonNote 0 ∧ OmegaDerivableR trueArithLitsR evInstR ρ α' Θ
  | [], _, α, hα, Θ, h => ⟨α, hα, by simpa [List.tilde_def] using h⟩
  | σ :: Δ, hΔ, α, hα, Θ, h => by
      obtain ⟨β, hβε, hσ⟩ := hax σ (hΔ σ (by simp))
      set φ : Proposition LRA := evR (Rewriting.emb σ : Proposition LRA) with hφ
      set rest : Sequent LRA := (∼Sequent.embed Δ).map evR with hrest
      have h' : OmegaDerivableR trueArithLitsR evInstR ρ α (Θ ++ ((∼φ) :: rest)) := by
        have e : (∼Sequent.embed (σ :: Δ)).map evR = (∼φ) :: rest := by
          simp only [Sequent.embed_cons, List.tilde_def, List.map_cons, hφ, hrest, evR_neg]
        rw [← e]
        exact h
      have hL : OmegaDerivableR trueArithLitsR evInstR ρ α ((∼φ) :: (Θ ++ rest)) := by
        refine OmegaDerivableR.contraction ?_ h'
        intro x hx
        simp only [List.mem_append, List.mem_cons] at hx ⊢
        tauto
      have hR : OmegaDerivableR trueArithLitsR evInstR ρ β (φ :: []) :=
        hσ.mono_rank (gamma0_zero_le ρ)
      have hcrk : rank φ < ρ := hrk σ (hΔ σ (by simp))
      have hcut : OmegaDerivableR trueArithLitsR evInstR ρ
          (OrdinalNotation.succ (OrdinalNotation.nadd β α)) ([] ++ (Θ ++ rest)) :=
        OmegaDerivableR.cut hcrk
          (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_left _ _))
          (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_right _ _)) hR hL
      have hbound : OrdinalNotation.succ (OrdinalNotation.nadd β α) < epsilonNote 0 :=
        succ_lt_epsilonNote_zero (Gamma0Note.nadd_lt_epsilon hβε hα)
      exact cut_axioms_below_epsilon T hax hrk Δ (fun τ hτ => hΔ τ (List.mem_cons_of_mem _ hτ))
        hbound (by simpa using hcut)

/-! ### Iterating `φ_1` -/

/-- The iteration may be peeled on the outside as well as on the inside:
`φ_e^{m+1}(α) = φ_e(φ_e^m(α))`. -/
theorem veblenIter_succ' (e : Gamma0Note) :
    ∀ (m : ℕ) (α : Gamma0Note), veblenIter e (m + 1) α = veblenNote e (veblenIter e m α)
  | 0, _ => rfl
  | (m + 1), α => by
      show veblenIter e (m + 1) (Gamma0Note.veblenStructure.veblen e α) = _
      rw [veblenIter_succ' e m]
      rfl

/-- `φ_e^m` is strictly monotone. -/
theorem veblenIter_lt_veblenIter (e : Gamma0Note) :
    ∀ (m : ℕ) {x y : Gamma0Note}, x < y → veblenIter e m x < veblenIter e m y
  | 0, _, _, h => h
  | (m + 1), _, _, h => by
      rw [veblenIter_succ, veblenIter_succ]
      exact veblenIter_lt_veblenIter e m (Gamma0Note.veblenNote_lt_veblenNote_right h)

/-- `φ_e^m` is monotone. -/
theorem veblenIter_le_veblenIter (e : Gamma0Note) (m : ℕ) {x y : Gamma0Note} (h : x ≤ y) :
    veblenIter e m x ≤ veblenIter e m y := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · exact le_of_lt (veblenIter_lt_veblenIter e m h)

/-- **`φ_1^{m+1}(x) ≤ φ_{m+1}(x)`**: iterating `φ_1` never overtakes the Veblen
function of the same index. -/
theorem veblenIter_one_le_veblenNote (x : Gamma0Note) :
    ∀ m : ℕ, veblenIter 1 (m + 1) x ≤ veblenNote (OrdinalNotation.ofNat (m + 1)) x
  | 0 => by
      rw [veblenIter_succ', veblenIter_zero, ofNat_one_eq_one]
  | (m + 1) => by
      have hlt : (1 : Gamma0Note) < OrdinalNotation.ofNat (m + 1 + 1) := by
        rw [← ofNat_one_eq_one]
        exact OrdinalNotation.ofNat_lt_ofNat (by omega)
      have hstep : veblenIter 1 (m + 1) x ≤ veblenNote (OrdinalNotation.ofNat (m + 1 + 1)) x :=
        le_trans (veblenIter_one_le_veblenNote x m)
          (Gamma0Note.veblenNote_le_veblenNote_left (ofNat_le_ofNat (by omega)))
      rw [veblenIter_succ']
      calc veblenNote 1 (veblenIter 1 (m + 1) x)
          ≤ veblenNote 1 (veblenNote (OrdinalNotation.ofNat (m + 1 + 1)) x) :=
            Gamma0Note.veblenNote_le_veblenNote_right hstep
        _ = veblenNote (OrdinalNotation.ofNat (m + 1 + 1)) x :=
            Gamma0Note.veblenStructure.veblen_veblen_of_lt hlt

/-- **Step 2, generic in the theory.**  The replay-and-cut chain at a fixed level `ν`,
followed by the block elimination of `BlockCut.lean`: `T ⊢! σ` yields a cut-free
derivation of `σ` at a height strictly below `φ_1^ν(ε₀)`, given a uniform per-axiom
level bound at `ν` and axiom derivability *below `ε₀`*. -/
theorem provable_cutFree_of (T : Theory LRA) {ν : Lv}
    (hax : ∀ σ ∈ T, ∃ β : Gamma0Note, β < epsilonNote 0 ∧
        OmegaDerivableR trueArithLitsR evInstR 0 β [evR (Rewriting.emb σ : Proposition LRA)])
    (hlvl : ∀ σ ∈ T, lvlOf (Rewriting.emb σ : Proposition LRA) ≤ ν)
    {σ : Sentence LRA} (h : T ⊢! σ) :
    ∃ β : Gamma0Note, β < veblenIter 1 ν (epsilonNote 0) ∧
      OmegaDerivableR trueArithLitsR evInstR 0 β [evR (Rewriting.emb σ : Proposition LRA)] := by
  obtain ⟨Δ, α₀, hΔ, hα₀, hreplay⟩ := replay_of_provable h
  obtain ⟨ρ, k', hchain, hrk⟩ := exists_rank_chain_bound (fun τ hτ => hlvl τ (hΔ τ hτ))
  have hreplay' : OmegaDerivableR trueArithLitsR evInstR ρ α₀
      ([evR (Rewriting.emb σ : Proposition LRA)] ++ (∼Sequent.embed Δ).map evR) := by
    have := hreplay.mono_rank (gamma0_zero_le ρ)
    simpa [List.map_cons] using this
  obtain ⟨α, hαε, hα⟩ := cut_axioms_below_epsilon {τ | τ ∈ Δ}
    (fun τ hτ => hax τ (hΔ τ hτ)) hrk Δ (fun τ hτ => hτ) hα₀ hreplay'
  have hstep := OmegaDerivableR.blocks memFree_trueArithLitsR ν
    (OmegaDerivableR.cutElimination_chain memFree_trueArithLitsR k' hchain hα)
  refine ⟨_, veblenIter_lt_veblenIter 1 ν ?_, hstep⟩
  exact Gamma0Note.omegaTower_lt_epsilon k' α hαε

/-- **Step 2, for `RAlt (ν+1)`.**  The cuts, all at levels `≤ ν`, are eliminated
block by block, landing at cut rank `0` and a height strictly below `φ_1^ν(ε₀)`. -/
theorem provable_cutFree {ν : Lv} {σ : Sentence LRA} (h : RAlt (ν + 1) ⊢! σ) :
    ∃ β : Gamma0Note, β < veblenIter 1 ν (epsilonNote 0) ∧
      OmegaDerivableR trueArithLitsR evInstR 0 β [evR (Rewriting.emb σ : Proposition LRA)] :=
  provable_cutFree_of (RAlt (ν + 1))
    (fun τ hτ => RAlt_axiom_derivable_lt_epsilon (Nat.le_add_left 1 ν) τ hτ)
    (fun _ hτ => lvlOf_emb_le_of_mem_RAlt_succ hτ) h

/-! ### `0 < ofNat ν`, for `ν ≥ 1`, needed for the segment order below `φ_ν(ε₀)` -/

theorem ofNat_zero_eq_zero : (OrdinalNotation.ofNat 0 : Gamma0Note) = 0 := by
  rw [OrdinalNotation.Gamma0Note_ofNat]
  apply Gamma0Note.repr_injective
  rw [Gamma0Note.repr_ofNat, Gamma0Note.repr_zero]
  norm_num

theorem zero_lt_ofNat_of_pos {ν : Lv} (hν : 0 < ν) :
    (0 : Gamma0Note) < OrdinalNotation.ofNat ν := by
  have h : (OrdinalNotation.ofNat 0 : Gamma0Note) < OrdinalNotation.ofNat ν :=
    OrdinalNotation.ofNat_lt_ofNat hν
  rwa [ofNat_zero_eq_zero] at h

/-! ### The theorems -/

/-- **A cut-free derivation below a segment bound refutes `TI` on the segment.**
The last two steps of the chain, shared by both headline theorems. -/
theorem not_provable_TIR_of_cutFree {ν : Lv} (a b : Gamma0Note) (ha : 0 < a)
    (hbound : veblenIter 1 ν (epsilonNote 0) ≤ veblenNote a b) :
    RAlt (ν + 1) ⊬ (Semiformula.univCl (TIR (vebSegOrderR a b ha).prec) : Sentence LRA) := by
  rintro ⟨h⟩
  set C := vebSegOrderR a b ha with hCdef
  obtain ⟨β, hβ, hd⟩ := provable_cutFree h
  have hβ' : β < veblenNote a b := lt_of_lt_of_le hβ hbound
  have hemb : (Rewriting.emb (Semiformula.univCl (TIR C.prec)) : Proposition LRA) = TIR C.prec :=
    emb_univCl_of_freeVariables_eq_empty (CodedOrderR.freeVariables_TIR C)
  rw [hemb] at hd
  have : OrdinalNotation (Gamma0Note.VeblenBelow a b) :=
    Gamma0Note.VeblenBelow.ordinalNotation a b ha
  exact not_derivable_TI_R C (Below.mk β hβ') (OmegaDerivableR.toBelow hd hβ')

/-- **The non-provability half of the ordinal analysis of `RA_{<ν+1}`.**
`RA_{<ν+1}` does not prove transfinite induction along the coded Veblen ordering
restricted to the segment below `φ_1(φ_1^{ν−1}(ε₀)) = φ_1^ν(ε₀)`. -/
theorem ramified_lower_bound (ν : Lv) (hν : 1 ≤ ν) :
    RAlt (ν + 1) ⊬ (Semiformula.univCl (TIR
        (vebSegOrderR 1 (veblenIter 1 (ν - 1) (epsilonNote 0))
          Gamma0Note.zero_lt_one).prec) : Sentence LRA) := by
  refine not_provable_TIR_of_cutFree _ _ _ (le_of_eq ?_)
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, (Nat.sub_add_cancel hν).symm⟩
  rw [Nat.add_sub_cancel, veblenIter_succ']

/-- **The coarser form, at the segment below `φ_ν(ε₀)`.**  Immediate from
`ramified_lower_bound`'s chain, since `φ_1^ν(ε₀) ≤ φ_ν(ε₀)`. -/
theorem ramified_lower_bound_veblen (ν : Lv) (hν : 1 ≤ ν) :
    RAlt (ν + 1) ⊬ (Semiformula.univCl (TIR
        (vebSegOrderR (OrdinalNotation.ofNat ν) (epsilonNote 0)
          (zero_lt_ofNat_of_pos hν)).prec) : Sentence LRA) := by
  refine not_provable_TIR_of_cutFree _ _ _ ?_
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, (Nat.sub_add_cancel hν).symm⟩
  exact veblenIter_one_le_veblenNote _ m

end Ramified

end OrdinalAnalysis
