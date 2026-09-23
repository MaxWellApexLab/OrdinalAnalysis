/-
  **The segment corollaries**: `ACA + TI(<φ_a(b)) ⊬ TI(≺₁ ↾ φ_a(b), X)` for
  every `a > 1`.

  `Gamma0Theorem.lean` runs the whole chain in `Gamma0Note` itself, because
  `not_derivable_TI₂_gamma0` refutes its conclusion at *every* notation.  For a
  segment the bound is real again, and the file is `ACAOmega/LowerBound₂.lean`'s
  assembly with `ε₀`/`ε_{ε₀}` replaced by `φ_a(b)` throughout: every height
  before the cut elimination is moved into `Gamma0Note.VeblenBelow a b` by
  `OmegaDerivable₂.toBelow`, carried back by `map_height`, and the cut
  elimination's output `ε_{ω_K(α)}` is below `φ_a(b)` again because — for
  `1 < a` — `φ_a(b)` is a fixed point of `φ_1 = ε_·`.  That last fact is
  `epsilon_lt_veblenNote`, two lines from `Gamma0Note.veblenNote_veblenNote_of_lt`
  (`Ordinal/Veblen/VeblenStructureInstance.lean`).

  ### Honesty

  As in `Gamma0Theorem.lean`, **the content is the non-provability half**, and
  here *only* that half is formalised.  `ACAΓBelow c` has, for every `a < c`, the
  axiom of transfinite induction below `ā` along the **unsegmented** `≺₁`; what
  is refuted is transfinite induction along the **segment** ordering
  `≺₁ ↾ φ_a(b)`.  The two orderings agree below `φ_a(b)` — the segment's second
  conjunct is automatic there — but identifying them *syntactically*, which is
  what a matching provability statement would need, is not done here.  So this
  file states `|ACA + TI(<φ_a(b))| ≤ φ_a(b)` in the non-provability sense, not
  the two-sided equality.  With `a := 2, b := 0` it is the `φ_2(0)` corollary and
  with `a := ω, b := 0` the `φ_ω(0)` one.

  `not_derivable_TI₂_vebSeg` needs `OrdinalNotation (VeblenBelow a b)`, which is
  a `def` and not an `instance` (`Ordinal/Veblen/VeblenBelow.lean`), so — exactly
  as there — the theorems here take it as an ordinary instance parameter;
  callers supply `Gamma0Note.VeblenBelow.ordinalNotation a b ha`.

  Contents.

    `epsilon_lt_veblenNote`      `φ_a(b)` is closed under `ε_·`, for `1 < a`
    `epsilon_omegaTower_lt_veblenNote`   …and under the cut elimination's output
    `ACAΓBelow`                  `ACA` plus the `TI`-axioms below the cut-off `c`
    `acaΓBelow_axiom_derivable_below`    every axiom, at a height in `VeblenBelow`
    `vebSeg_lower_bound`         **the corollary**, for every `a > 1`
    `phi2_lower_bound`           the named instance at `φ_2(0)`

  `φ_ω(0)` and the rest of the family are the same theorem at another `a`: all
  `vebSeg_lower_bound` asks of `a` is `1 < a`.
-/
import OrdinalAnalysis.ACAOmega.Gamma0Theorem
import OrdinalAnalysis.Ordinal.Veblen.VeblenStructureInstance

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA
open OrdinalAnalysis.ACAOmega.NumSubst₂
open OrdinalAnalysis.Gamma0Note (veblenNote VeblenBelow)

namespace Gamma0Segment

/-! ### `φ_a(b)` is closed under the `ε`-jump, for `1 < a`

`ε_x = φ_1(x)` (`Ordinal/Veblen/Epsilon.lean`, definitionally), and `φ_a(b)` is a
fixed point of `φ_1` as soon as `1 < a`. -/

/-- **`φ_a(b)` is closed under `ε_·`, for `1 < a`.** -/
theorem epsilon_lt_veblenNote {a b x : Gamma0Note} (ha : (1 : Gamma0Note) < a)
    (hx : x < veblenNote a b) : Gamma0Note.epsilonNote x < veblenNote a b := by
  have h1 : veblenNote 1 x < veblenNote 1 (veblenNote a b) :=
    Gamma0Note.veblenNote_lt_veblenNote_right hx
  rwa [Gamma0Note.veblenNote_veblenNote_of_lt ha] at h1

/-- **The cut elimination's output stays below `φ_a(b)`, for `1 < a`.**  The
`ω`-tower does not escape (`VeblenStructure.omegaTower_lt_veblen`), and neither
does the `ε`-jump. -/
theorem epsilon_omegaTower_lt_veblenNote {a b α : Gamma0Note} (ha : (1 : Gamma0Note) < a)
    (hα : α < veblenNote a b) (k : ℕ) :
    Gamma0Note.epsilonNote (OrdinalNotation.omegaTower k α) < veblenNote a b :=
  epsilon_lt_veblenNote ha
    (Gamma0Note.veblenStructure.omegaTower_lt_veblen (le_of_lt ha) k α b hα)

theorem zero_lt_veblenNote {a b : Gamma0Note} (ha : (1 : Gamma0Note) < a) :
    (0 : Gamma0Note) < veblenNote a b :=
  lt_trans Gamma0Note.zero_lt_one (Gamma0Note.one_lt_veblenNote (le_of_lt ha))

theorem epsZero_lt_veblenNote {a b : Gamma0Note} (ha : (1 : Gamma0Note) < a) :
    SchemeAxioms₂.epsZero < veblenNote a b :=
  epsilon_lt_veblenNote ha (zero_lt_veblenNote ha)

/-! ### The theory with the `TI`-axioms cut off at `c` -/

/-- **`ACA + TI(<c)`**: `ACAΓ` with the transfinite-induction axioms kept only
for the notations below `c`. -/
def ACAΓBelow (c : Gamma0Note) : Set (Proposition ℒₒᵣ) :=
  ACA ∪ {χ | ∃ (N n : ℕ) (a : Gamma0Note) (ψ : Semiproposition ℒₒᵣ N (n + 1)), a < c ∧
    Arith ψ ∧ NoSetFvar ψ ∧ Semiproposition.shift₀ ψ = ψ ∧ χ = tiUptoScheme a ψ}

theorem ACAΓBelow_subset_ACAΓ (c : Gamma0Note) : ACAΓBelow c ⊆ ACAΓ := by
  rintro χ (h | ⟨N, n, a, ψ, -, hψ, hns, h0, rfl⟩)
  · exact ACA_subset_ACAΓ h
  · exact tiUptoScheme_mem_ACAΓ a hψ hns h0

theorem ACAΓBelow_shift₀_invariant (c : Gamma0Note) :
    ∀ χ ∈ ACAΓBelow c, Semiproposition.shift₀ χ = χ :=
  fun χ h => ACAΓ_shift₀_invariant χ (ACAΓBelow_subset_ACAΓ c h)

theorem numClosed₂_neg_of_mem_ACAΓBelow {c : Gamma0Note} {σ : Proposition ℒₒᵣ}
    (h : σ ∈ ACAΓBelow c) : NumClosed₂ (∼σ) :=
  Gamma0Theorem.numClosed₂_neg_of_mem_ACAΓ (ACAΓBelow_subset_ACAΓ c h)

/-! ### Every axiom is derivable at a height *below* `φ_a(b)`

The `ACA` block is below `ε₀` (`SchemeAxioms₂.aca_axiom_derivable_lt_eps₀`) and
`ε₀ < φ_a(b)`; the `TI` block for `a₀ < φ_a(b)` is below `ε_{a₀ ⊕ 1}`
(`AxiomsTI₂.tiUptoScheme_derivable_lt`) and that is below `φ_a(b)` too, since
`a₀ ⊕ 1 < φ_a(b)` and `φ_a(b)` is `ε`-closed. -/

theorem acaΓBelow_axiom_derivable_lt (a b : Gamma0Note) (ha : (1 : Gamma0Note) < a) :
    ∀ σ ∈ ACAΓBelow (veblenNote a b), ∃ β : Gamma0Note, β < veblenNote a b ∧
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ σ] := by
  rintro σ (h | ⟨N, n, a₀, ψ, ha₀, hψ, -, -, rfl⟩)
  · obtain ⟨β, hβ, hd⟩ := SchemeAxioms₂.aca_axiom_derivable_lt_eps₀ σ h
    exact ⟨β, lt_trans hβ (epsZero_lt_veblenNote ha), hd⟩
  · obtain ⟨β, hβ, hd⟩ := AxiomsTI₂.tiUptoScheme_derivable_lt a₀ ψ hψ
    refine ⟨β, lt_trans hβ ?_, hd⟩
    exact epsilon_lt_veblenNote ha (Gamma0Note.nadd_lt_veblenNote ha₀
      (Gamma0Note.one_lt_veblenNote (le_of_lt ha)))

/-- The same, with the heights already living in the notation system
`VeblenBelow a b` — which is the form `Axioms₂.cut_axioms₂_of` consumes when the
whole replay is run there. -/
theorem acaΓBelow_axiom_derivable_below (a b : Gamma0Note) (ha : (1 : Gamma0Note) < a)
    [OrdinalNotation (VeblenBelow a b)] :
    ∀ σ ∈ ACAΓBelow (veblenNote a b), ∃ β : VeblenBelow a b,
      OmegaDerivable₂ trueArithLits₂ evInst₂ 0 β [ev₂ σ] := by
  intro σ hσ
  obtain ⟨β, hβ, hd⟩ := acaΓBelow_axiom_derivable_lt a b ha σ hσ
  exact ⟨Below.mk β hβ, hd.toBelow hβ⟩

/-! ### The corollary -/

/-- **`ACA + TI(<φ_a(b))` does not prove transfinite induction along the coded
Veblen ordering restricted to the segment below `φ_a(b)`**, for every `a > 1`.
The non-provability half; see the module docstring. -/
theorem vebSeg_lower_bound (a b : Gamma0Note) (ha0 : 0 < a) (ha : (1 : Gamma0Note) < a)
    [OrdinalNotation (VeblenBelow a b)] :
    ¬ Provable (ACAΓBelow (veblenNote a b)) (TI₂ (vebSegOrder₂ a b ha0).prec) := by
  intro hprov
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := provable_iff.mp hprov
  have hclosed : ∀ φ ∈ (TI₂ (vebSegOrder₂ a b ha0).prec :: ∼Δ), NumClosed₂ φ := by
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact Gamma0Theorem.numClosed₂_TI₂_of (vebSegOrder₂ a b ha0)
    · have hφ' : φ ∈ Δ.map (∼·) := hφ
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hφ'
      exact numClosed₂_neg_of_mem_ACAΓBelow (hΔ σ hσ)
  -- replay, with all heights already below `φ_a(b)`
  have h₁ := Embed₂.replay₂_closed (O := VeblenBelow a b) d hclosed
  rw [List.map_cons] at h₁
  obtain ⟨k₁, hk₁⟩ := LowerBound₂.exists_omegaAdd_cutRank d
  obtain ⟨k₂, hk₂⟩ := OmegaDerivable₂.exists_omegaAdd_bound Δ
  have hρ : cutRank₂ d ≤ OmegaDerivable₂.omegaAdd (max k₁ k₂) :=
    le_trans hk₁ (OmegaDerivable₂.omegaAdd_le_omegaAdd (le_max_left _ _))
  have hrk : ∀ σ ∈ Δ, rank (ev₂ σ) < OmegaDerivable₂.omegaAdd (max k₁ k₂) := fun σ hσ =>
    lt_of_lt_of_le (hk₂ σ hσ) (OmegaDerivable₂.omegaAdd_le_omegaAdd (le_max_right _ _))
  obtain ⟨α, h₂⟩ := Axioms₂.cut_axioms₂_of (ACAΓBelow (veblenNote a b))
    (OmegaDerivable₂.omegaAdd (max k₁ k₂)) (acaΓBelow_axiom_derivable_below a b ha) Δ hΔ hrk hρ
    (Θ := [ev₂ (TI₂ (vebSegOrder₂ a b ha0).prec)]) (by simpa using h₁)
  -- back to `Gamma0Note`, where the Veblen values live
  have h₃ := h₂.map_height (Below.val (ε := veblenNote a b)) Below.val_strictMono
  have h₄ := OmegaDerivable₂.cutElimination_omegaAdd_ev (max k₁ k₂) h₃
  have hlt : Gamma0Note.epsilonNote (OrdinalNotation.omegaTower (max k₁ k₂) α.val)
      < veblenNote a b := epsilon_omegaTower_lt_veblenNote ha α.2 _
  exact not_derivable_TI₂_vebSeg a b ha0 _ (h₄.toBelow hlt)

/-! ### The two named instances

`φ_2(0)` and `φ_ω(0)` — the `ACA₀⁺`-strength and `Σ¹₁-DC₀`-strength
stations, on the `ACA + TI(<·)` side of the Avigad family. -/

/-- `1 < 2`, in `Gamma0Note`. -/
theorem one_lt_ofNat_two : (1 : Gamma0Note) < Gamma0Note.ofNat 2 := by
  rw [Gamma0Note.lt_def, Gamma0Note.repr_one, Gamma0Note.repr_ofNat]
  exact_mod_cast Nat.one_lt_two

theorem zero_lt_ofNat_two : (0 : Gamma0Note) < Gamma0Note.ofNat 2 :=
  lt_trans Gamma0Note.zero_lt_one one_lt_ofNat_two

/-- **`ACA + TI(<φ_2(0)) ⊬ TI(≺₁ ↾ φ_2(0), X)`.**  The `φ_2(0)` station, in the
non-provability sense. -/
theorem phi2_lower_bound :
    ¬ Provable (ACAΓBelow (veblenNote (Gamma0Note.ofNat 2) 0))
      (TI₂ (vebSegOrder₂ (Gamma0Note.ofNat 2) 0 zero_lt_ofNat_two).prec) :=
  @vebSeg_lower_bound (Gamma0Note.ofNat 2) 0 zero_lt_ofNat_two one_lt_ofNat_two
    (Gamma0Note.VeblenBelow.ordinalNotation (Gamma0Note.ofNat 2) 0 zero_lt_ofNat_two)

end Gamma0Segment

end OrdinalAnalysis.ACAOmega
