/-
  Cutting the negated axioms of `ACA` out of a replayed derivation.

  Two things live here.

  * **`cut_axioms₂_of`** — the second-order twin of
    `Gentzen/CutAxioms.lean`'s `cut_axioms_of`.  Given that every axiom of a
    theory `T` is cut-free derivable, it removes the negated axioms of a finite
    list from a derivation, one cut at a time.  The differences from the
    first-order version are both about the cut rank.

    - `ACA_∞`'s ranks are **ordinal notations**, not naturals, and the rank of an
      axiom is *not* bounded by anything uniform: `indScheme₂ φ` for a `φ` with
      nested set quantifiers has rank `ω + k` with `k` depending on `φ`.  The
      lemma therefore takes the target rank `ρ'` as a **parameter**, together
      with the hypothesis `rank (ev₂ σ) < ρ'` for each axiom on the list; a
      caller picks `ρ'` after seeing the finitely many axioms its derivation
      uses.  This is what `cutElimination_omegaAdd_ev` wants — it consumes a
      rank in the shape `omegaAdd k = ω + k` — and it keeps this file free of
      the ordinal arithmetic of §"Not done" below.
    - The starting rank is a parameter too, with `ρ ≤ ρ'`; `mono_rank` lifts the
      input derivation once and the output is at `ρ'` throughout, so no `max`
      has to be taken inside the recursion.

    Heights are `succ (β ⊕ α)`, exactly as in the first order, where `β` is the
    axiom's own height and `α` the running height.

  * **The four non-schema blocks of `ACA₀`** — `eqAxioms`, `paMinus`, `setExt`
    and `setInduction` — packaged as `aca_logical_axiom_derivable`, with their
    heights certified below `ε_{ε₀}`.  All four are at `ω + k` for a `k ≤ 5`:
    `hgt₂ χ` (finite) for the two lifted blocks, `ofNat 5` for `setExt`,
    `ω ⊕ 3` for `setInduction`.

  ### Not done here, and why

  `aca_axiom_derivable` for the two **schema** blocks `indScheme₂ φ` and
  `arithComp₂ ψ` is not proved.  Every *structural* ingredient is:
  `AxiomsInduction₂.allN₂_derivable` peels `allSets`,
  `AxiomsInduction₂.allN₁_derivable` peels `allNums`, `freeN₁_allN₁` says the
  two prefixes may be peeled independently, and the bodies are
  `succInd₂_derivable` (induction) and `iff_self_derivable` (comprehension).
  What is missing is purely the *instantiation computation*: identifying
  `Rew.subst w ▹ freeN₁ N (indBody φ)` with `succInd₂` of the instantiated body,
  which needs `(Rew.subst w).comp (Rew.subst (indZeroSub n))
  = (Rew.subst ![zeroT]).comp (Rew.subst w).q` and its `indSuccSub` twin, and
  the corresponding identification for `compBody`, where the `(∃₂)` witness has
  additionally to be pulled out of `ψ.bmap Fin.succ` after `free₁`.

  Likewise **the rank bound** `rank φ ≤ ω + k` is not proved.  It needs
  `repr (NONote.succ a) = Order.succ (repr a)`, i.e. `repr` of the project's
  natural sum, and `Ordinal/NaturalSum.lean` proves only order facts about
  `nadd`, never computing its `repr`.  `cut_axioms₂_of` is stated so that the
  bound is a hypothesis rather than a lemma, so nothing downstream is blocked by
  it.
-/
import OrdinalAnalysis.ACAOmega.AxiomsInduction₂

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA
open OrdinalAnalysis.ACAOmega.OmegaTruth₂
open OrdinalAnalysis.ACAOmega.AxiomsLogic₂
open OrdinalAnalysis.ACAOmega.AxiomsInduction₂

namespace Axioms₂

/-! ### Cutting the negated axioms away -/

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- **Cutting away the negated axioms of a theory `T`**, one at a time, given
that every axiom of `T` is cut-free derivable and that the cut rank `ρ'` lies
above the rank of each of them.

The second-order twin of `Gentzen/CutAxioms.lean`'s `cut_axioms_of`; see the
module docstring for why `ρ'` is a parameter. -/
theorem cut_axioms₂_of (T : Set (Proposition ℒₒᵣ)) (ρ' : NONote)
    (hax : ∀ σ ∈ T, ∃ β : O,
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ σ]) :
    ∀ (Δ : SecondOrder.Sequent ℒₒᵣ), (∀ σ ∈ Δ, σ ∈ T) →
      (∀ σ ∈ Δ, rank (ev₂ σ) < ρ') →
      ∀ {ρ : NONote} (_ : ρ ≤ ρ') {α : O} {Θ : SecondOrder.Sequent ℒₒᵣ},
        OmegaDerivable₂ trueArithLits₂ evInst₂ ρ α (Θ ++ (∼Δ).map ev₂) →
        ∃ α' : O, OmegaDerivable₂ trueArithLits₂ evInst₂ ρ' α' Θ
  | [], _, _, ρ, hρ, α, Θ, h =>
      ⟨α, (by simpa using h : OmegaDerivable₂ trueArithLits₂ evInst₂ ρ α Θ).mono_rank hρ⟩
  | σ :: Δ, hΔ, hrk, ρ, hρ, α, Θ, h => by
      obtain ⟨β, hσ⟩ := hax σ (hΔ σ (by simp))
      set φ : Proposition ℒₒᵣ := ev₂ σ with hφ
      set rest : SecondOrder.Sequent ℒₒᵣ := (∼Δ).map ev₂ with hrest
      have h' : OmegaDerivable₂ trueArithLits₂ evInst₂ ρ' α (Θ ++ ((∼φ) :: rest)) := by
        have e : (∼(σ :: Δ) : SecondOrder.Sequent ℒₒᵣ).map ev₂ = (∼φ) :: rest := by
          simp only [SecondOrder.Sequent.tilde_cons, List.map_cons, hφ, hrest, ev₂_neg]
        rw [← e]
        exact h.mono_rank hρ
      have hL : OmegaDerivable₂ trueArithLits₂ evInst₂ ρ' α ((∼φ) :: (Θ ++ rest)) := by
        refine OmegaDerivable₂.contraction ?_ h'
        intro x hx
        simp only [List.mem_append, List.mem_cons] at hx ⊢
        tauto
      have hR : OmegaDerivable₂ trueArithLits₂ evInst₂ ρ' β (φ :: []) :=
        hσ.mono_rank (NONote.zero_le' ρ')
      have hcut : OmegaDerivable₂ trueArithLits₂ evInst₂ ρ'
          (OrdinalNotation.succ (OrdinalNotation.nadd β α)) ([] ++ (Θ ++ rest)) :=
        OmegaDerivable₂.cut (hrk σ (by simp))
          (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_left _ _))
          (OrdinalNotation.lt_succ_of_le (OrdinalNotation.le_nadd_right _ _)) hR hL
      exact cut_axioms₂_of T ρ' hax Δ (fun τ hτ => hΔ τ (List.mem_cons_of_mem _ hτ))
        (fun τ hτ => hrk τ (List.mem_cons_of_mem _ hτ)) le_rfl (by simpa using hcut)

/-! ### The heights are far below `ε_{ε₀}` -/

/-- `ε_{ε₀}`, the target of the `ACA` lower bound. -/
def epsEps : Gamma0Note := Gamma0Note.epsilonNote (Gamma0Note.epsilonNote 0)

theorem ofNat_lt_epsEps (n : ℕ) : (OrdinalNotation.ofNat n : Gamma0Note) < epsEps := by
  show Gamma0Note.ofNat n < epsEps
  rw [Gamma0Note.lt_def, Gamma0Note.repr_ofNat, epsEps,
    Gamma0Note.repr_epsilonNote_eq_epsilon]
  exact Ordinal.natCast_lt_epsilon n _

theorem one_lt_epsEps : (1 : Gamma0Note) < epsEps := by
  rw [Gamma0Note.lt_def, Gamma0Note.repr_one, epsEps,
    Gamma0Note.repr_epsilonNote_eq_epsilon]
  exact_mod_cast Ordinal.natCast_lt_epsilon 1 _

theorem omegaG_lt_epsEps : omegaG < epsEps := by
  rw [omegaG]
  exact Gamma0Note.omegaPow_lt_epsilon one_lt_epsEps

theorem nadd_omegaG_ofNat_lt_epsEps (k : ℕ) :
    OrdinalNotation.nadd omegaG (OrdinalNotation.ofNat k) < epsEps :=
  Gamma0Note.nadd_lt_epsilon omegaG_lt_epsEps (ofNat_lt_epsEps k)

/-! ### The four non-schema blocks of `ACA₀`

`eqAxioms`, `paMinus`, `setExt` and `setInduction`.  Each is cut-free derivable
at a height below `ε_{ε₀}` — in fact at `ω + k` for a `k ≤ 5`. -/

/-- The non-schema part of `ACA₀`. -/
def acaCore : Set (Proposition ℒₒᵣ) := eqAxioms ∪ paMinus ∪ {setInduction, setExt}

theorem acaCore_subset_ACA₀ : acaCore ⊆ ACA₀ := fun _ h => Or.inl h

/-- **Every axiom of `acaCore` is cut-free derivable at a height below
`ε_{ε₀}`.** -/
theorem aca_logical_axiom_derivable (χ : Proposition ℒₒᵣ) (h : χ ∈ acaCore) :
    ∃ β : Gamma0Note, β < epsEps ∧
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ χ] := by
  rcases h with (h | h) | h | h
  · exact ⟨hgt₂ χ, by
      obtain ⟨σ, -, rfl⟩ := h
      exact ofNat_lt_epsEps _, eq_axiom_derivable χ h⟩
  · exact ⟨hgt₂ χ, by
      obtain ⟨σ, -, rfl⟩ := h
      exact ofNat_lt_epsEps _, paMinus_axiom_derivable χ h⟩
  · refine ⟨OrdinalNotation.nadd omegaG (OrdinalNotation.ofNat 3),
      nadd_omegaG_ofNat_lt_epsEps 3, ?_⟩
    rw [h]
    exact setInduction_derivable
  · refine ⟨OrdinalNotation.ofNat 5, ofNat_lt_epsEps 5, ?_⟩
    rw [h]
    exact setExt_derivable

/-- The same, in the shape `cut_axioms₂_of` consumes. -/
theorem acaCore_derivable : ∀ σ ∈ acaCore, ∃ β : Gamma0Note,
    OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ σ] := by
  intro σ hσ
  obtain ⟨β, -, hd⟩ := aca_logical_axiom_derivable σ hσ
  exact ⟨β, hd⟩

/-- **Cutting away the negated axioms of `acaCore`.** -/
theorem cut_acaCore (ρ' : NONote) (Δ : SecondOrder.Sequent ℒₒᵣ)
    (hΔ : ∀ σ ∈ Δ, σ ∈ acaCore) (hrk : ∀ σ ∈ Δ, rank (ev₂ σ) < ρ')
    {ρ : NONote} (hρ : ρ ≤ ρ') {α : Gamma0Note} {Θ : SecondOrder.Sequent ℒₒᵣ}
    (h : OmegaDerivable₂ trueArithLits₂ evInst₂ ρ α (Θ ++ (∼Δ).map ev₂)) :
    ∃ α' : Gamma0Note, OmegaDerivable₂ trueArithLits₂ evInst₂ ρ' α' Θ :=
  cut_axioms₂_of acaCore ρ' acaCore_derivable Δ hΔ hrk hρ h

end Axioms₂

end OrdinalAnalysis.ACAOmega
