/-
  **The `ACA` lower bound**: `ACA ⊬ TI(≺₁ ↾ ε_{ε₀}, X)`.

  The chain is `Gentzen/Epsilon1LowerBoundScheme.lean`'s, one level up.

      Provable ACA TIsegSO
        →  provable_iff                    a finitary derivation of
                                           `TIsegSO :: ∼axioms`
        →  replay₂_closed                  an `ACA_∞`-derivation of the same
                                           sequent, evaluated, at cut rank
                                           `cutRank₂ d` and height `ordN₂ d`
        →  cut_axioms₂_of                  the negated axioms cut away, at cut
                                           rank `ω + K`
        →  cutElimination_omegaAdd_ev      cut free, at height `ε_{ω_K(α)}`
        →  not_derivable_TI₂_epsilonSeg    contradiction.

  ### Why the heights are carried in `Below ε₀`

  The second cut elimination sends height `α` and rank `ω + K` to height
  `ε_{ω_K(α)}`, and the boundedness lemma refutes `TI₂` only at heights below
  `ε_{ε₀}`.  So `ε_{ω_K(α)} < ε_{ε₀}`, i.e. `ω_K(α) < ε₀`, i.e. **`α < ε₀`** —
  every height *before* the cut elimination must be below `ε₀`, not merely
  below `ε_{ε₀}`.

  `cut_axioms₂_of` produces its height existentially, so rather than re-prove it
  with the bound threaded through, the whole replay is run **inside the notation
  system `Below ε₀` itself** (`Gamma0Note.EpsilonBelow 0`): `replay₂` and
  `cut_axioms₂_of` are generic in the height system, `ε₀` is a closed bound
  (`Gamma0Note.closed_epsilonNote`), and the axiom heights — all `< ε₀` by
  `SchemeAxioms₂.aca_axiom_derivable_lt_eps₀` — are moved into it by
  `OmegaDerivable₂.toBelow`.  Whatever height comes out is then below `ε₀` *by
  its type*, and `OmegaDerivable₂.map_height` carries it back to `Gamma0Note`
  for the cut elimination.  Both transports are ported here from
  `Ordinal/BelowDerivation.lean` and `Omega/HeightMap.lean`; each rule of the
  calculus only ever compares heights, so both are one induction.

  ### The two bridges

  * **`numClosed₂_of_shift₀`.**  `replay₂_closed` asks every member of the
    sequent to be `NumClosed₂`; `ACA/LK.lean` proves every axiom is fixed by
    `shift₀`.  A term fixed by `Rew.shift` has no free variable — `shift` moves
    every one of them — and the formula statement follows by induction.
  * **`TIsegSO_eq`.**  The sentence the *upper* bound aims at
    (`ACA/TI.lean`'s `TIsegSO = toSOAt segWitness (TI precSeg)`, a translation
    out of the first-order language `LX`) and the one boundedness refutes
    (`TI₂ (epsilonSegOrder₂ (epsilonNote 0)).prec`, built directly in the
    second-order syntax) are **equal on the nose**.  `toSOAt segWitness`
    commutes with `precAt`/`below`/`Prog`/`TI` — that is `toSOAtB_rew` plus the
    structural clauses — and sends `Xat t` to `t ∈& 0`; on the ordering itself
    it is `toSOAtB_lMap` (both `precCode₁` and `precFO₁` are
    `InternalVNote.precDef₁`, one `lMap toLX`-ed and one not) together with
    `unTerm (numeral k) = numeral k` (`Gentzen.lMap_toLX_numeral`).  So both
    halves of `|ACA| = ε_{ε₀}` speak about one sentence.
-/
import OrdinalAnalysis.ACAOmega.SchemeAxioms₂
import OrdinalAnalysis.ACAOmega.RankBound
import OrdinalAnalysis.ACAOmega.Embed₂
import OrdinalAnalysis.ACAOmega.Boundedness₂
import OrdinalAnalysis.ACA.TI
import OrdinalAnalysis.Ordinal.BelowDerivation
import OrdinalAnalysis.Ordinal.NONoteSucc

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA
open OrdinalAnalysis.ACAOmega.NumSubst₂
open OrdinalAnalysis.Gentzen (LX Xat)

/-! ### Transporting a derivation between height systems

Both are the second-order copies of the first-order lemmas
(`Omega/HeightMap.lean`, `Ordinal/BelowDerivation.lean`): every rule of the
ω-calculus mentions the height only through `<` between a premise's height and
the conclusion's. -/

namespace OmegaDerivable₂

variable {L : FirstOrder.Language}
variable {O O' : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
  [LinearOrder O'] [WellFoundedLT O'] [OrdinalNotation O']

/-- **Height transport.**  A strictly monotone map of heights preserves
derivability, at the same rank and of the same sequent. -/
theorem map_height {A : Literals₂ L} {I : Instantiation₂ L} {ρ : NONote}
    (e : O → O') (he : StrictMono e) :
    ∀ {α : O} {Γ : SecondOrder.Sequent L}, OmegaDerivable₂ A I ρ α Γ →
      OmegaDerivable₂ A I ρ (e α) Γ := by
  intro α Γ h
  induction h with
  | atom hφ => exact .atom hφ
  | identity φ => exact .identity φ
  | verum => exact .verum
  | or hβ _ ih => exact .or (he hβ) ih
  | and hβ hγ _ _ ihφ ihψ => exact .and (he hβ) (he hγ) ihφ ihψ
  | omegaRule β hβ _ ih => exact .omegaRule (fun n => e (β n)) (fun n => he (hβ n)) ih
  | exs n hβ _ ih => exact .exs n (he hβ) ih
  | all₂ hβ _ ih => exact .all₂ (he hβ) ih
  | exs₂ hψ hβ _ ih => exact .exs₂ hψ (he hβ) ih
  | contraction ss _ ih => exact .contraction ss ih
  | cut hc hβ hγ _ _ ihφ ihψ => exact .cut hc (he hβ) (he hγ) ihφ ihψ

/-- **Restriction to the notations below `ε`.**  A derivation of height below
`ε` is a derivation in `Below ε`, at the same rank, of the same sequent. -/
theorem toBelow {ε : O} [OrdinalNotation (Below ε)] {A : Literals₂ L}
    {I : Instantiation₂ L} {ρ : NONote} :
    ∀ {α : O} {Γ : SecondOrder.Sequent L}, OmegaDerivable₂ A I ρ α Γ →
      ∀ (hα : α < ε), OmegaDerivable₂ (O := Below ε) A I ρ (Below.mk α hα) Γ := by
  intro α Γ h
  induction h with
  | atom hφ => intro _; exact .atom hφ
  | identity φ => intro _; exact .identity φ
  | verum => intro _; exact .verum
  | or hβ _ ih => intro hα; exact .or (Below.mk_lt_mk _ _ hβ) (ih (lt_trans hβ hα))
  | and hβ hγ _ _ ihφ ihψ =>
      intro hα
      exact .and (Below.mk_lt_mk _ _ hβ) (Below.mk_lt_mk _ _ hγ)
        (ihφ (lt_trans hβ hα)) (ihψ (lt_trans hγ hα))
  | omegaRule β hβ _ ih =>
      intro hα
      exact .omegaRule (fun n => Below.mk (β n) (lt_trans (hβ n) hα))
        (fun n => Below.mk_lt_mk _ _ (hβ n)) (fun n => ih n (lt_trans (hβ n) hα))
  | exs n hβ _ ih => intro hα; exact .exs n (Below.mk_lt_mk _ _ hβ) (ih (lt_trans hβ hα))
  | all₂ hβ _ ih => intro hα; exact .all₂ (Below.mk_lt_mk _ _ hβ) (ih (lt_trans hβ hα))
  | exs₂ hψ hβ _ ih => intro hα; exact .exs₂ hψ (Below.mk_lt_mk _ _ hβ) (ih (lt_trans hβ hα))
  | contraction ss _ ih => intro hα; exact .contraction ss (ih hα)
  | cut hc hβ hγ _ _ ihφ ihψ =>
      intro hα
      exact .cut hc (Below.mk_lt_mk _ _ hβ) (Below.mk_lt_mk _ _ hγ)
        (ihφ (lt_trans hβ hα)) (ihψ (lt_trans hγ hα))

end OmegaDerivable₂

namespace LowerBound₂

/-! ### From `shift₀`-invariance to `NumClosed₂` -/

/-- A term fixed by `Rew.shift` has no free variable: `shift` moves every free
variable, so a fixed point can contain none. -/
theorem freeVariables_eq_empty_of_shift {n : ℕ} : ∀ (t : FirstOrder.Semiterm ℒₒᵣ ℕ n),
    (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) t = t → t.freeVariables = ∅ := by
  intro t
  induction t with
  | bvar x => intro _; simp
  | fvar x => intro h; simp at h
  | func f v ih =>
      intro h
      rw [FirstOrder.Rew.func] at h
      simp only [FirstOrder.Semiterm.func.injEq, heq_eq_eq, true_and] at h
      rw [FirstOrder.Semiterm.freeVariables_func]
      exact Finset.biUnion_eq_empty.mpr (fun i _ => ih i (congrFun h i))

/-- **The bridge from `ACA_shift₀_invariant` to `NumClosed₂`**, which is what
`replay₂_closed` asks for. -/
theorem numClosed₂_of_shift₀ : ∀ {N n : ℕ} {φ : Semiformula ℒₒᵣ ℕ ℕ N n},
    (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) ▹ φ = φ → NumClosed₂ φ := by
  intro N n φ
  induction φ using Semiformula.rec' with
  | hRel r v =>
      intro h
      rw [Semiformula.rew_rel] at h
      simp only [Semiformula.rel.injEq, heq_eq_eq, true_and] at h
      exact fun i => freeVariables_eq_empty_of_shift _ (congrFun h i)
  | hNrel r v =>
      intro h
      rw [Semiformula.rew_nrel] at h
      simp only [Semiformula.nrel.injEq, heq_eq_eq, true_and] at h
      exact fun i => freeVariables_eq_empty_of_shift _ (congrFun h i)
  | hBvar X t =>
      intro h
      rw [Semiformula.rew_bvar] at h
      injection h with _ _ _ ht
      exact freeVariables_eq_empty_of_shift _ ht
  | hNbvar X t =>
      intro h
      rw [Semiformula.rew_nbvar] at h
      injection h with _ _ _ ht
      exact freeVariables_eq_empty_of_shift _ ht
  | hFvar X t =>
      intro h
      rw [Semiformula.rew_fvar] at h
      injection h with _ _ _ ht
      exact freeVariables_eq_empty_of_shift _ ht
  | hNfvar X t =>
      intro h
      rw [Semiformula.rew_nfvar] at h
      injection h with _ _ _ ht
      exact freeVariables_eq_empty_of_shift _ ht
  | hVerum => intro _; trivial
  | hFalsum => intro _; trivial
  | hAnd φ ψ ihφ ihψ =>
      intro h
      rw [LogicalConnective.HomClass.map_and] at h
      injection h with _ _ h₁ h₂
      exact ⟨ihφ h₁, ihψ h₂⟩
  | hOr φ ψ ihφ ihψ =>
      intro h
      rw [LogicalConnective.HomClass.map_or] at h
      injection h with _ _ h₁ h₂
      exact ⟨ihφ h₁, ihψ h₂⟩
  | hAll₁ φ ih =>
      intro h
      rw [Semiformula.rew_all₀, FirstOrder.Rew.q_shift] at h
      injection h with _ _ h'
      exact ih h'
  | hExs₁ φ ih =>
      intro h
      rw [Semiformula.rew_exs₀, FirstOrder.Rew.q_shift] at h
      injection h with _ _ h'
      exact ih h'
  | hAll₂ φ ih =>
      intro h
      rw [Semiformula.rew_all₁] at h
      injection h with _ _ h'
      exact ih h'
  | hExs₂ φ ih =>
      intro h
      rw [Semiformula.rew_exs₁] at h
      injection h with _ _ h'
      exact ih h'

/-- Every axiom of `ACA` is `NumClosed₂`, and so is its negation. -/
theorem numClosed₂_neg_of_mem_ACA {σ : Proposition ℒₒᵣ} (h : σ ∈ ACA) : NumClosed₂ (∼σ) := by
  refine numClosed₂_of_shift₀ ?_
  show (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹ (∼σ) = ∼σ
  rw [LogicalConnective.HomClass.map_neg]
  exact congrArg (∼·) (ACA_shift₀_invariant σ h)

/-! ### `TIsegSO` is the sentence boundedness refutes

`toSOAt segWitness` commutes with every shape of `TI`, and sends the fresh
predicate's atom to the free set variable's. -/

@[simp] theorem emb_segWitness :
    (FirstOrder.Rewriting.emb segWitness : Semiformula ℒₒᵣ ℕ ℕ 0 1)
      = ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& (0 : ℕ)) := by
  simp [segWitness]

theorem toSOAt_Xat_seg {n : ℕ} (t : FirstOrder.Semiterm LX ℕ n) :
    toSOAt segWitness (Xat t) = ((unTerm t) ∈& (0 : ℕ)) := by
  simp

theorem toSOAt_precAt {n : ℕ} (p : FirstOrder.Semiformula LX ℕ 2)
    (y x : FirstOrder.Semiterm LX ℕ n) :
    toSOAt segWitness (Gentzen.precAt p y x)
      = precAt₂ (toSOAt segWitness p) (unTerm y) (unTerm x) :=
  toSOAtB_rew (ψ := segWitness) (ω := FirstOrder.Rew.subst ![y, x])
    (ω' := FirstOrder.Rew.subst ![unTerm y, unTerm x])
    (Fin.forall_fin_two.mpr ⟨by simp, by simp⟩) (fun _ => by simp) p

theorem toSOAt_below (p : FirstOrder.Semiformula LX ℕ 2) :
    toSOAt segWitness (Gentzen.below p) = below₂ (toSOAt segWitness p) := by
  simp [Gentzen.below, below₂, toSOAt_precAt]

theorem toSOAt_Prog (p : FirstOrder.Semiformula LX ℕ 2) :
    toSOAt segWitness (Gentzen.Prog p) = Prog₂ (toSOAt segWitness p) := by
  simp [Gentzen.Prog, Prog₂, toSOAt_below]

theorem toSOAt_TI (p : FirstOrder.Semiformula LX ℕ 2) :
    toSOAt segWitness (Gentzen.TI p) = TI₂ (toSOAt segWitness p) := by
  simp [Gentzen.TI, TI₂, toSOAt_Prog]

/-- `unTerm` undoes `toLX` on a numeral. -/
theorem unTerm_numeral {ξ : Type*} {n : ℕ} (k : ℕ) :
    unTerm (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm LX ξ n)
      = (FirstOrder.Semiterm.numeral k : FirstOrder.Semiterm ℒₒᵣ ξ n) := by
  rw [← Gentzen.lMap_toLX_numeral k, unTerm_lMap]

theorem toSOAt_precCode₁ :
    toSOAt segWitness Gentzen.CodedVeblen.precCode₁
      = (lift precFO₁ : Semiproposition ℒₒᵣ 0 2) :=
  toSOAtB_lMap _

theorem toSOAt_precSeg (a : Gamma0Note) :
    toSOAt segWitness (Gentzen.EpsilonSegmentOrder.precCodeSeg a)
      = (lift (precSeg₀ a) : Semiproposition ℒₒᵣ 0 2) := by
  rw [Gentzen.EpsilonSegmentOrder.precCodeSeg, precSeg₀]
  simp only [toSOAtB_and, lift_and, toSOAt_precAt, toSOAt_precCode₁, lift_rew]
  congr 1
  have hv : ![unTerm (#1 : FirstOrder.Semiterm LX ℕ 2),
      unTerm (Gentzen.EpsilonSegmentOrder.epsilonNumeral a)]
      = ![(#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2),
        (numAt (Gentzen.VNoteBridge.gamma0Code (Gamma0Note.epsilonNote a)) :
          FirstOrder.Semiterm ℒₒᵣ ℕ 2)] := by
    funext i
    match i with
    | 0 => simp
    | 1 =>
        show unTerm (Gentzen.EpsilonSegmentOrder.epsilonNumeral a) = _
        rw [Gentzen.EpsilonSegmentOrder.epsilonNumeral]
        exact unTerm_numeral _
  show FirstOrder.Rew.subst
      ![unTerm (#1 : FirstOrder.Semiterm LX ℕ 2),
        unTerm (Gentzen.EpsilonSegmentOrder.epsilonNumeral a)]
      ▹ (lift precFO₁ : Semiproposition ℒₒᵣ 0 2) = _
  rw [hv]

/-- **The two spellings of the transfinite-induction sentence are the same
formula.**  `ACA/TI.lean`'s `TIsegSO` — what the upper bound aims at — is
`ACAOmega/CodedOrder₂.lean`'s `TI₂` over the coded `ε_{ε₀}`-segment, which is
what `ACAOmega/Boundedness₂.lean` refutes. -/
theorem TIsegSO_eq :
    TIsegSO = TI₂ (epsilonSegOrder₂ (Gamma0Note.epsilonNote 0)).prec := by
  show toSOAt segWitness (Gentzen.TI precSeg) = _
  rw [toSOAt_TI]
  show TI₂ (toSOAt segWitness (Gentzen.EpsilonSegmentOrder.precCodeSeg
    (Gamma0Note.epsilonNote 0))) = _
  rw [toSOAt_precSeg]
  rfl

/-- `TIsegSO` has no free number variable. -/
theorem shift₀_TIsegSO : Semiproposition.shift₀ TIsegSO = TIsegSO := by
  show FirstOrder.Rewriting.shift (toSOAt segWitness (Gentzen.TI precSeg)) = _
  rw [← toSOAtB_shift]
  congr 1
  refine FirstOrder.Semiformula.rew_eq_self_of (by simp) (fun x hx => ?_)
  have hfv : (Gentzen.TI precSeg).freeVariables = ∅ :=
    Gentzen.LowerSyntax.freeVariables_TI
      (Gentzen.EpsilonSegmentOrder.freeVariables_precCodeSeg _)
  rw [FirstOrder.Semiformula.FVar?, hfv] at hx
  simp at hx

theorem numClosed₂_TIsegSO : NumClosed₂ TIsegSO := numClosed₂_of_shift₀ shift₀_TIsegSO

/-! ### The cut rank of a finitary derivation is below some `ω + k` -/

theorem succ_le_of_lt {a b : NONote} (h : a < b) : NONote.succ a ≤ b := by
  show ONote.repr (NONote.succ a).1 ≤ ONote.repr b.1
  rw [NONote.repr_succ a]
  exact Order.add_one_le_iff.mpr h

/-- **The finitary derivation's own cut rank is bounded by some `ω + k`.**  Its
`cut` nodes are finitely many, and each cut formula's rank is below
`ω + (complexity + 1)` (`RankBound.lean`). -/
theorem exists_omegaAdd_cutRank : ∀ {Γ : SecondOrder.Sequent ℒₒᵣ} (d : ACA.Derivation Γ),
    ∃ k : ℕ, cutRank₂ d ≤ OmegaDerivable₂.omegaAdd k
  | _, .identity => ⟨0, NONote.zero_le' _⟩
  | _, .verum => ⟨0, NONote.zero_le' _⟩
  | _, .wk d _ => exists_omegaAdd_cutRank d
  | _, .or d => exists_omegaAdd_cutRank d
  | _, .all₁ d => exists_omegaAdd_cutRank d
  | _, .exs₁ d => exists_omegaAdd_cutRank d
  | _, .all₂ d => exists_omegaAdd_cutRank d
  | _, .exs₂ _ d => exists_omegaAdd_cutRank d
  | _, .and dp dq => by
      obtain ⟨k₁, h₁⟩ := exists_omegaAdd_cutRank dp
      obtain ⟨k₂, h₂⟩ := exists_omegaAdd_cutRank dq
      refine ⟨max k₁ k₂, ?_⟩
      rw [cutRank₂_and]
      exact max_le (le_trans h₁ (OmegaDerivable₂.omegaAdd_le_omegaAdd (le_max_left _ _)))
        (le_trans h₂ (OmegaDerivable₂.omegaAdd_le_omegaAdd (le_max_right _ _)))
  | _, @ACA.Derivation.cut φ _ dp dn => by
      obtain ⟨k₁, h₁⟩ := exists_omegaAdd_cutRank dp
      obtain ⟨k₂, h₂⟩ := exists_omegaAdd_cutRank dn
      refine ⟨max (φ.complexity + 1) (max k₁ k₂), ?_⟩
      rw [cutRank₂_cut]
      refine max_le ?_ (max_le ?_ ?_)
      · exact le_trans (succ_le_of_lt (OmegaDerivable₂.rank_lt_omegaAdd_succ φ))
          (OmegaDerivable₂.omegaAdd_le_omegaAdd (le_max_left _ _))
      · exact le_trans h₁ (OmegaDerivable₂.omegaAdd_le_omegaAdd
          (le_trans (le_max_left _ _) (le_max_right _ _)))
      · exact le_trans h₂ (OmegaDerivable₂.omegaAdd_le_omegaAdd
          (le_trans (le_max_right _ _) (le_max_right _ _)))

/-! ### The assembly -/

/-- Every axiom of `ACA` is cut-free derivable at a height *in the notation
system `Below ε₀`*. -/
theorem aca_axiom_derivable_below : ∀ σ ∈ ACA, ∃ β : Gamma0Note.EpsilonBelow 0,
    OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ σ] := by
  intro σ hσ
  obtain ⟨β, hβ, hd⟩ := SchemeAxioms₂.aca_axiom_derivable_lt_eps₀ σ hσ
  have hβ' : β < Gamma0Note.epsilonNote 0 := hβ
  exact ⟨Below.mk β hβ', hd.toBelow hβ'⟩

/-- **`ACA` does not prove transfinite induction along the coded ordering of
the notations below `ε_{ε₀}`.**  The lower half of `|ACA| = ε_{ε₀}`. -/
theorem aca_lower_bound : ¬ Provable ACA TIsegSO := by
  intro hprov
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := provable_iff.mp hprov
  -- every member of the replayed sequent has no free number variable
  have hclosed : ∀ φ ∈ (TIsegSO :: ∼Δ), NumClosed₂ φ := by
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact numClosed₂_TIsegSO
    · have hφ' : φ ∈ Δ.map (∼·) := hφ
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hφ'
      exact numClosed₂_neg_of_mem_ACA (hΔ σ hσ)
  -- replay, with all heights already below `ε₀`
  have h₁ := Embed₂.replay₂_closed (O := Gamma0Note.EpsilonBelow 0) d hclosed
  rw [List.map_cons] at h₁
  -- a common rank bound `ω + K` for the derivation's cuts and the axioms
  obtain ⟨k₁, hk₁⟩ := exists_omegaAdd_cutRank d
  obtain ⟨k₂, hk₂⟩ := OmegaDerivable₂.exists_omegaAdd_bound Δ
  have hρ : cutRank₂ d ≤ OmegaDerivable₂.omegaAdd (max k₁ k₂) :=
    le_trans hk₁ (OmegaDerivable₂.omegaAdd_le_omegaAdd (le_max_left _ _))
  have hrk : ∀ σ ∈ Δ, rank (ev₂ σ) < OmegaDerivable₂.omegaAdd (max k₁ k₂) := fun σ hσ =>
    lt_of_lt_of_le (hk₂ σ hσ) (OmegaDerivable₂.omegaAdd_le_omegaAdd (le_max_right _ _))
  -- cut the negated axioms away
  obtain ⟨α, h₂⟩ := Axioms₂.cut_axioms₂_of ACA (OmegaDerivable₂.omegaAdd (max k₁ k₂))
    aca_axiom_derivable_below Δ hΔ hrk hρ (Θ := [ev₂ TIsegSO]) (by simpa using h₁)
  -- back to `Gamma0Note`, where the ε-numbers live
  have h₃ := h₂.map_height (Below.val (ε := Gamma0Note.epsilonNote 0)) Below.val_strictMono
  -- the second cut elimination
  have h₄ := OmegaDerivable₂.cutElimination_omegaAdd_ev (max k₁ k₂) h₃
  have hlt : Gamma0Note.epsilonNote (OrdinalNotation.omegaTower (max k₁ k₂) α.val)
      < Gamma0Note.epsilonNote (Gamma0Note.epsilonNote 0) :=
    Gamma0Note.epsilon_lt_epsilon
      (Gamma0Note.epsilonStructure.omegaTower_lt_epsilon (max k₁ k₂) α.val α.2)
  have h₅ := h₄.toBelow hlt
  rw [TIsegSO_eq] at h₅
  exact not_derivable_TI₂_epsilonSeg (Gamma0Note.epsilonNote 0) _ h₅

/-- **`ACA` is consistent.**  From `⊥` everything follows, `TIsegSO` included,
so this is `aca_lower_bound` and one cut. -/
theorem aca_consistent : ¬ Provable ACA (⊥ : Proposition ℒₒᵣ) := by
  intro h
  refine aca_lower_bound ?_
  obtain ⟨Γ, hΓ, ⟨d⟩⟩ := provable_iff.mp h
  refine provable_iff.mpr ⟨Γ, hΓ, ⟨?_⟩⟩
  refine ACA.Derivation.cut (φ := ⊥) (d.wk ?_) (ACA.Derivation.wk ACA.Derivation.verum ?_)
  · intro x hx
    simp only [List.mem_cons] at hx ⊢
    tauto
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp only [List.mem_cons]
    left
    rfl

end LowerBound₂

end OrdinalAnalysis.ACAOmega
