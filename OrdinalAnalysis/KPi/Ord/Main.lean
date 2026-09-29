import OrdinalAnalysis.KPi.Ord.Sanity

/-!
# Buchholz 1992, §4: ordinal notation system for `KPi` -- Lemmas 4.4 and 4.5 under B92 names

Setting: `O = Ordinal.{1}`; `Iord` is the least weakly inaccessible ordinal `I`;
`Rset = R = {I} ∪ {Ω_{σ+1} | σ < I}`; `C α β = C(α, β)`; `psiK κ α = ψ_κ α`;
`Ck κ α = C_κ(α) = C(α, ψ_κ α)`; `Om σ = Ω_σ`.

Lemmas 4.6 (a)-(e) and 4.7 ((A1)-(A4)) are stated in `Hull.lean` (`Hop_niceOp`, `Hop_veblen`, `Hop_psi`,
`Hop_Om`, `Hop_mono`, `A1`-`A4`); the sanity statements are in `Sanity.lean`.

## Deviations from the printed statements

None of these weakens the mathematical content.

1. **Natural sum (Def 3.5, Lemma 4.5 (e)).**  Mathlib provides no natural sum on `Ordinal`.  B92's
   `ω^{α₀} # … # ω^{αₙ}` is rendered as the ordinary sum `pw [ξ₀, …, ξₙ] = ω^{ξ₀} + … + ω^{ξₙ}` over a weakly
   decreasing list (`Srt`), which is the natural sum of `ω`-powers.  Existence and uniqueness of this
   Cantor normal form are proved in `CNF.lean`; `Nice X` is `∀ l, Srt l → (pw l ∈ X ↔ ∀ ξ ∈ l, ξ ∈ X)`
   (the empty list gives `0 ∈ X`).
2. **`H_γ[Θ]` (Def 4.3).**  The operator is `Hop γ K` with `K = k(Θ)`, the set of ordinals occurring in the
   sequence `Θ`; `Θ` enters only through `K`, so it is abstracted.  `𝒜(Θ; γ, κ, μ)` is `AA K γ κ μ`.
3. **Lemma 4.6 (e) and Lemma 4.7.**  `Hop_mono` is stated for `γ ≤ δ` (this contains B92's `γ < δ`).
   Lemma 4.7 carries the hypothesis `κ ∈ R` explicitly as the field `AA.kR` (B92's standing convention).
4. **Parametrised closure.**  `Cl f α β` takes the collapsing function `f` as a parameter, so the cardinality
   bound of Lemma 4.4 (a) is proved once for all `f`; `psiK` is total (defined by `sInf`), with junk values for
   `κ ∉ R`, which no statement uses.
5. **Order of proofs.**  Lemmas 4.4 (c), (d) are proved after 4.5 (a) (totality of `ψ`), on which they depend.
6. **Universes.**  Cardinals of sets of ordinals live in `Cardinal.{2}`; 4.4 (a) is stated as
   `#(C α β) < Cardinal.lift.{2, 1} π.card`.
-/

set_option autoImplicit false

open Ordinal Cardinal Set Order

noncomputable section

namespace OrdinalAnalysis.KPi.Ord

/-- Lemma 4.4a -/
theorem B92_4_4a {π α β : O} (hπ : π ∈ Rset) (hβ : β < π) :
    #(C α β) < Cardinal.lift.{2, 1} π.card := card_Cl_lt hπ hβ

/-- Lemma 4.4b -/
theorem B92_4_4b {α β : O} (hβ : IsSuccLimit β) : C α β = ⋃ η ∈ Iio β, C α η := by
  ext x
  constructor
  · intro hx
    obtain ⟨η, hη, h⟩ := Cl.of_limit hβ hx
    exact mem_iUnion₂.2 ⟨η, hη, h⟩
  · intro hx
    obtain ⟨η, hη, h⟩ := mem_iUnion₂.1 hx
    exact Cl.mono_beta (mem_Iio.1 hη).le h

/-- Lemma 4.4c -/
theorem B92_4_4c {κ : O} (hκ : κ ∈ Rset) (α : O) : κ ∈ C α κ := kappa_mem_C hκ α

/-- Lemma 4.4d -/
theorem B92_4_4d {κ : O} (hκ : κ ∈ Rset) (α : O) : Ck κ α ∩ Iio κ = Iio (psiK κ α) :=
  Ck_inter hκ α

/-- Lemma 4.5a -/
theorem B92_4_5a {κ : O} (hκ : κ ∈ Rset) (α : O) : psiK κ α < κ ∧ psiK κ α ∉ Ck κ α :=
  ⟨psiK_lt hκ α, psiK_not_mem_Ck hκ α⟩

/-- Lemma 4.5b -/
theorem B92_4_5b {κ α α0 : O} (hκ : κ ∈ Rset) (h : α0 < α) (h0 : α0 ∈ Ck κ α) :
    psiK κ α0 < psiK κ α := psiK_lt_psiK hκ h h0

/-- Lemma 4.5c -/
theorem B92_4_5c {κ : O} (hκ : κ ∈ Rset) (α : O) :
    psiK κ α ∉ {x | ∃ σ, σ < Om σ ∧ x = Om σ} ∪ {0} ∧
      ∀ ξ η, ξ < psiK κ α → η < psiK κ α → veblen ξ η < psiK κ α := by
  refine ⟨?_, fun ξ η hξ hη => psiK_veblen_lt hκ α hξ hη⟩
  rintro (⟨σ, hσ, h⟩ | h)
  · exact psiK_ne_Om hκ α hσ h
  · exact psiK_ne_zero hκ α h

/-- Lemma 4.5d -/
theorem B92_4_5d {α β σ : O} (h : Om σ ∈ C α β) : σ ∈ C α β := Om_mem_C h

/-- Lemma 4.5e (natural sums of `ω`-powers = sorted ordinary sums) -/
theorem B92_4_5e {α β : O} {l : List O} (hl : Srt l) :
    pw l ∈ C α β ↔ ∀ ξ ∈ l, ξ ∈ C α β := nice_C hl

/-- Lemma 4.5f -/
theorem B92_4_5f {σ : O} (hσ : σ < Iord) (α : O) :
    Om σ < psiK (ω_ (σ + 1)) α ∧ psiK (ω_ (σ + 1)) α < ω_ (σ + 1) := psiK_between hσ α

/-- Lemma 4.5g -/
theorem B92_4_5g (α : O) : Om (psiK Iord α) = psiK Iord α := Om_psiI α

/-- Lemma 4.5h -/
theorem B92_4_5h {α β σ γ : O} (h1 : Om σ ≤ γ) (h2 : γ ≤ Om (σ + 1)) (hγ : γ ∈ C α β) :
    σ ∈ C α β := mem_of_between h1 h2 hγ

/-- Lemma 4.5i -/
theorem B92_4_5i {κ α α0 : O} (hκ : κ ∈ Rset) (h : α0 ≤ α) :
    psiK κ α0 ≤ psiK κ α ∧ Ck κ α0 ⊆ Ck κ α := psiK_mono hκ h

end OrdinalAnalysis.KPi.Ord

#print axioms OrdinalAnalysis.KPi.Ord.B92_4_4a
#print axioms OrdinalAnalysis.KPi.Ord.B92_4_4b
#print axioms OrdinalAnalysis.KPi.Ord.B92_4_4c
#print axioms OrdinalAnalysis.KPi.Ord.B92_4_4d
#print axioms OrdinalAnalysis.KPi.Ord.B92_4_5a
#print axioms OrdinalAnalysis.KPi.Ord.B92_4_5b
#print axioms OrdinalAnalysis.KPi.Ord.B92_4_5c
#print axioms OrdinalAnalysis.KPi.Ord.B92_4_5d
#print axioms OrdinalAnalysis.KPi.Ord.B92_4_5e
#print axioms OrdinalAnalysis.KPi.Ord.B92_4_5f
#print axioms OrdinalAnalysis.KPi.Ord.B92_4_5g
#print axioms OrdinalAnalysis.KPi.Ord.B92_4_5h
#print axioms OrdinalAnalysis.KPi.Ord.B92_4_5i
