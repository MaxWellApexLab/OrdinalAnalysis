/-
  Derived rules for `Provable`, built entirely at
  that level (never a new `Derivation` constructor — the replay handles the primitive
  constructors of `LK.lean`, so this file must not add to their number).

  Everything here is a combination of `identity`/`cut`/`wk`/`and`/`or`/`all₁`/
  `exs₁`/`all₂`/`exs₂`packaged so that later files (`Translate.lean`, and
  eventually the assembly of the upper half) never have to build a raw `Derivation` by
  hand for routine steps: modus ponens, specializing a quantifier, and
  generalizing one back up (the latter needing exactly the `shift₀`/`shift₁`
  invariance that `LK.lean` established for `ACA₀`/`ACA`).
-/
import OrdinalAnalysis.ACA.LK

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder

variable {𝓢 : Set (Proposition ℒₒᵣ)}

/-! ### The basic package -/

/-- **Every axiom is provable.** -/
theorem ofAxiom {φ : Proposition ℒₒᵣ} (h : φ ∈ 𝓢) : Provable 𝓢 φ :=
  provable_iff.mpr ⟨[φ], by simpa using h, ⟨Derivation.identity⟩⟩

/-- **Cut, at the `Provable` level, through a disjunction.**  From `⊢ φ` and
`⊢ ∼φ ⋎ ψ`, conclude `⊢ ψ`.  Built from `identity`, `and`, `cut`, `wk` only:
`and` gives `⊢ φ ⋏ ∼ψ, ψ, …` (the `∼ψ` side is just `identity` on `ψ`, read
backwards into the same context), `φ ⋏ ∼ψ` is `∼(∼φ ⋎ ψ)` by `neg_neg`, and
`cut` against the `∼φ ⋎ ψ` hypothesis finishes it. -/
theorem cutP {φ ψ : Proposition ℒₒᵣ} (hφ : Provable 𝓢 φ) (hd : Provable 𝓢 (∼φ ⋎ ψ)) :
    Provable 𝓢 ψ := by
  obtain ⟨Γ1, hΓ1, ⟨d1⟩⟩ := provable_iff.mp hφ
  obtain ⟨Γ2, hΓ2, ⟨d2⟩⟩ := provable_iff.mp hd
  refine provable_iff.mpr ⟨Γ1 ++ Γ2, ?_, ⟨?_⟩⟩
  · intro χ hχ
    rcases List.mem_append.mp hχ with h | h
    exacts [hΓ1 _ h, hΓ2 _ h]
  · have hsub1 : φ :: (∼Γ1) ⊆ φ :: (ψ :: (∼Γ1) ++ (∼Γ2)) := by
      intro x hx; simp only [List.mem_cons, List.mem_append] at hx ⊢; tauto
    have hsub2 : (∼φ ⋎ ψ) :: (∼Γ2) ⊆ (∼φ ⋎ ψ) :: (ψ :: (∼Γ1) ++ (∼Γ2)) := by
      intro x hx; simp only [List.mem_cons, List.mem_append] at hx ⊢; tauto
    have hsubId : ([ψ, ∼ψ] : SecondOrder.Sequent ℒₒᵣ) ⊆ (∼ψ :: (ψ :: (∼Γ1) ++ (∼Γ2))) := by
      intro x hx; simp only [List.mem_cons, List.mem_append] at hx ⊢; tauto
    have hcast : (∼(∼φ ⋎ ψ) : Proposition ℒₒᵣ) = φ ⋏ ∼ψ := by
      show (∼(∼φ)) ⋏ (∼ψ) = φ ⋏ ∼ψ
      rw [Semiformula.neg_neg]
    have A : Derivation (φ :: (ψ :: (∼Γ1) ++ (∼Γ2))) := Derivation.wk d1 hsub1
    have hid : Derivation (∼ψ :: (ψ :: (∼Γ1) ++ (∼Γ2))) :=
      Derivation.wk Derivation.identity hsubId
    have andD : Derivation ((φ ⋏ ∼ψ) :: (ψ :: (∼Γ1) ++ (∼Γ2))) := Derivation.and A hid
    have andD' : Derivation ((∼(∼φ ⋎ ψ)) :: (ψ :: (∼Γ1) ++ (∼Γ2))) :=
      Derivation.cast andD (by rw [hcast])
    have B : Derivation ((∼φ ⋎ ψ) :: (ψ :: (∼Γ1) ++ (∼Γ2))) := Derivation.wk d2 hsub2
    have final : Derivation (ψ :: (∼Γ1) ++ (∼Γ2)) := Derivation.cut B andD'
    have hΓeq : (∼(Γ1 ++ Γ2) : SecondOrder.Sequent ℒₒᵣ) = (∼Γ1) ++ (∼Γ2) := by simp
    exact Derivation.cast final (by simp [hΓeq])

/-- **Modus ponens.**  `φ 🡒 ψ` unfolds (definitionally) to `∼φ ⋎ ψ`, so this is
`cutP` with the arguments read the other way round. -/
theorem mp {φ ψ : Proposition ℒₒᵣ} (h1 : Provable 𝓢 (φ 🡒 ψ)) (h2 : Provable 𝓢 φ) :
    Provable 𝓢 ψ :=
  cutP h2 h1

/-! ### Specializing a quantifier -/

/-- **`spec₂`.**  From `⊢ ∀² φ`, specialize the set variable to an arithmetical
`ψ`.  `∼(∀² φ) = ∃² (∼φ)` (`neg_neg` again), so `exs₂` at the witness `ψ`
supplies the other half of a `cut` on `∀² φ`. -/
theorem spec₂ {φ : Semiproposition ℒₒᵣ 1 0} (h : Provable 𝓢 (∀² φ))
    {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1} (hψ : Arith ψ) : Provable 𝓢 (φ/⟦ψ⟧) := by
  obtain ⟨Γ, hΓ, ⟨d⟩⟩ := provable_iff.mp h
  refine provable_iff.mpr ⟨Γ, hΓ, ⟨?_⟩⟩
  have hsubA : (∀² φ) :: (∼Γ) ⊆ (∀² φ) :: ((φ/⟦ψ⟧) :: ∼Γ) := by
    intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  have hsubId : ([(φ/⟦ψ⟧), ∼(φ/⟦ψ⟧)] : SecondOrder.Sequent ℒₒᵣ) ⊆
      (∼(φ/⟦ψ⟧)) :: ((φ/⟦ψ⟧) :: ∼Γ) := by
    intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  have hnegcast : ((∼φ)/⟦ψ⟧ : Proposition ℒₒᵣ) = ∼(φ/⟦ψ⟧) := by
    simp [Semiproposition.subst₁]
  have A : Derivation ((∀² φ) :: ((φ/⟦ψ⟧) :: ∼Γ)) := Derivation.wk d hsubA
  have hid : Derivation ((∼(φ/⟦ψ⟧)) :: ((φ/⟦ψ⟧) :: ∼Γ)) :=
    Derivation.wk Derivation.identity hsubId
  have hid' : Derivation (((∼φ)/⟦ψ⟧) :: ((φ/⟦ψ⟧) :: ∼Γ)) :=
    Derivation.cast hid (by rw [hnegcast])
  have B : Derivation ((∃² (∼φ)) :: ((φ/⟦ψ⟧) :: ∼Γ)) := Derivation.exs₂ hψ hid'
  exact Derivation.cut A (Derivation.cast B rfl)

/-- **`spec₁`.**  From `⊢ ∀¹ φ`, specialize the number variable to a closed
term `t`.  Mirrors `spec₂` with `exs₁` in place of `exs₂`. -/
theorem spec₁ {φ : Semiproposition ℒₒᵣ 0 1} (h : Provable 𝓢 (∀¹ φ))
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ 0) : Provable 𝓢 (φ/[t]) := by
  obtain ⟨Γ, hΓ, ⟨d⟩⟩ := provable_iff.mp h
  refine provable_iff.mpr ⟨Γ, hΓ, ⟨?_⟩⟩
  have hsubA : (∀¹ φ) :: (∼Γ) ⊆ (∀¹ φ) :: ((φ/[t]) :: ∼Γ) := by
    intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  have hsubId : ([(φ/[t]), ∼(φ/[t])] : SecondOrder.Sequent ℒₒᵣ) ⊆
      (∼(φ/[t])) :: ((φ/[t]) :: ∼Γ) := by
    intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
  have hnegcast : ((∼φ)/[t] : Proposition ℒₒᵣ) = ∼(φ/[t]) := by simp
  have A : Derivation ((∀¹ φ) :: ((φ/[t]) :: ∼Γ)) := Derivation.wk d hsubA
  have hid : Derivation ((∼(φ/[t])) :: ((φ/[t]) :: ∼Γ)) :=
    Derivation.wk Derivation.identity hsubId
  have hid' : Derivation (((∼φ)/[t]) :: ((φ/[t]) :: ∼Γ)) :=
    Derivation.cast hid (by rw [hnegcast])
  have B : Derivation ((∃¹ (∼φ)) :: ((φ/[t]) :: ∼Γ)) := Derivation.exs₁ hid'
  exact Derivation.cut A (Derivation.cast B rfl)

/-! ### Generalizing a quantifier back up

`all₂`/`all₁` (the `Derivation` constructors) demand that the *whole context*
be `shift₁`/`shift₀`-fixed before the eigenvariable can be introduced safely.
The context here is `∼Γ` for the axiom list `Γ` a `Provable` proof happens to
use; since every `χ ∈ Γ` comes from `𝓢`, `ACA₀_shift₁_invariant` /
`ACA_shift₁_invariant` (and their `shift₀` counterparts) supply exactly the
hypothesis `gen₂`/`gen₁` need, at `𝓢 = ACA₀` or `ACA`. -/

private theorem shift₁_tilde_of_forall {Γ : SecondOrder.Sequent ℒₒᵣ}
    (h : ∀ χ ∈ Γ, Semiproposition.shift₁ χ = χ) :
    SecondOrder.Sequent.shift₁ (∼Γ) = ∼Γ := by
  induction Γ with
  | nil => rfl
  | cons a l ih =>
      have ha : Semiproposition.shift₁ a = a := h a List.mem_cons_self
      have hl : SecondOrder.Sequent.shift₁ (∼l) = ∼l :=
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      simp [SecondOrder.Sequent.shift₁_cons, LogicalConnective.HomClass.map_neg, ha, hl]

private theorem shift₀_tilde_of_forall {Γ : SecondOrder.Sequent ℒₒᵣ}
    (h : ∀ χ ∈ Γ, Semiproposition.shift₀ χ = χ) :
    SecondOrder.Sequent.shift₀ (∼Γ) = ∼Γ := by
  induction Γ with
  | nil => rfl
  | cons a l ih =>
      have ha : Semiproposition.shift₀ a = a := h a List.mem_cons_self
      have hl : SecondOrder.Sequent.shift₀ (∼l) = ∼l :=
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      simp [SecondOrder.Sequent.shift₀_cons, LogicalConnective.HomClass.map_neg, ha, hl]

/-- **`gen₂`.**  Generalize a proof of `φ.free₁` (the eigenvariable form) to
`∀² φ`, provided every axiom of `𝓢` is `shift₁`-fixed
(`ACA₀_shift₁_invariant` / `ACA_shift₁_invariant`). -/
theorem gen₂ {φ : Semiproposition ℒₒᵣ 1 0} (h𝓢 : ∀ χ ∈ 𝓢, Semiproposition.shift₁ χ = χ)
    (h : Provable 𝓢 φ.free₁) : Provable 𝓢 (∀² φ) := by
  obtain ⟨Γ, hΓ, ⟨d⟩⟩ := provable_iff.mp h
  refine provable_iff.mpr ⟨Γ, hΓ, ⟨?_⟩⟩
  have heq : SecondOrder.Sequent.shift₁ (∼Γ) = ∼Γ :=
    shift₁_tilde_of_forall (fun x hx => h𝓢 x (hΓ x hx))
  exact Derivation.all₂ (Derivation.cast d (by rw [heq]))

/-- **`gen₁`.**  The number-variable analogue of `gen₂`, needing `shift₀`
instead of `shift₁` (`ACA₀_shift₀_invariant` / `ACA_shift₀_invariant`). -/
theorem gen₁ {φ : Semiproposition ℒₒᵣ 0 1} (h𝓢 : ∀ χ ∈ 𝓢, Semiproposition.shift₀ χ = χ)
    (h : Provable 𝓢 φ.free₀) : Provable 𝓢 (∀¹ φ) := by
  obtain ⟨Γ, hΓ, ⟨d⟩⟩ := provable_iff.mp h
  refine provable_iff.mpr ⟨Γ, hΓ, ⟨?_⟩⟩
  have heq : SecondOrder.Sequent.shift₀ (∼Γ) = ∼Γ :=
    shift₀_tilde_of_forall (fun x hx => h𝓢 x (hΓ x hx))
  exact Derivation.all₁ (Derivation.cast d (by rw [heq]))

/-! ### Discharging several provable hypotheses at once -/

private theorem tilde_tilde_sequent (Γ : SecondOrder.Sequent ℒₒᵣ) : ∼(∼Γ) = Γ := by
  induction Γ with
  | nil => rfl
  | cons a l ih => simp [Semiformula.neg_neg, ih]

/-- **`cutMany`**, generalized with an extra fixed list `Θ0` of *already
negated* side hypotheses (each of whose own negation is an axiom) to make the
induction on `Δ` go through (`cutMany` itself is the `Θ0 = []` case). -/
private theorem cutMany_aux {Δ : SecondOrder.Sequent ℒₒᵣ} :
    ∀ {ψ : Proposition ℒₒᵣ} {Θ0 : SecondOrder.Sequent ℒₒᵣ}, (∀ ρ ∈ Θ0, ∼ρ ∈ 𝓢) →
      (∀ χ ∈ Δ, Provable 𝓢 χ) → Derivation (ψ :: (∼Δ) ++ Θ0) → Provable 𝓢 ψ := by
  induction Δ with
  | nil =>
      intro ψ Θ0 hΘ0 _ d
      refine provable_iff.mpr ⟨∼Θ0, ?_, ⟨?_⟩⟩
      · intro x hx
        obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hx
        exact hΘ0 ρ hρ
      · exact Derivation.cast d (by rw [tilde_tilde_sequent]; simp)
  | cons χ Δ' ih =>
      intro ψ Θ0 hΘ0 hΔ d
      obtain ⟨Γχ, hΓχ, ⟨dχ⟩⟩ := provable_iff.mp (hΔ χ List.mem_cons_self)
      have hΔ' : ∀ x ∈ Δ', Provable 𝓢 x := fun x hx => hΔ x (List.mem_cons_of_mem _ hx)
      have hsubA : χ :: (∼Γχ) ⊆ χ :: (ψ :: (∼Δ') ++ ((∼Γχ) ++ Θ0)) := by
        intro x hx; simp only [List.mem_cons, List.mem_append] at hx ⊢; tauto
      have hsubB : (ψ :: (∼χ :: (∼Δ')) ++ Θ0) ⊆ (∼χ) :: (ψ :: (∼Δ') ++ ((∼Γχ) ++ Θ0)) := by
        intro x hx
        simp only [List.mem_cons, List.mem_append] at hx ⊢
        tauto
      have A : Derivation (χ :: (ψ :: (∼Δ') ++ ((∼Γχ) ++ Θ0))) := Derivation.wk dχ hsubA
      have B : Derivation ((∼χ) :: (ψ :: (∼Δ') ++ ((∼Γχ) ++ Θ0))) := Derivation.wk d hsubB
      have combined : Derivation (ψ :: (∼Δ') ++ ((∼Γχ) ++ Θ0)) := Derivation.cut A B
      refine ih (Θ0 := (∼Γχ) ++ Θ0) (fun ρ hρ => ?_) hΔ' combined
      rcases List.mem_append.mp hρ with h | h
      · obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp h
        simpa [Semiformula.neg_neg] using hΓχ σ hσ
      · exact hΘ0 ρ h

/-- **`cutMany`.**  If every formula of `Δ` is separately provable in `𝓢`, and
there is a raw derivation of `ψ` from `Δ` as hypotheses, then `ψ` is provable
in `𝓢`.  This is exactly what `Translate.lean`'s `lift_paLX` needs after
`translate`: the translated derivation's hypothesis list is a list of
*images* of `paLX`'s axioms, each individually shown `Provable ACA`, not
literal members of `ACA`. -/
theorem cutMany {Δ : SecondOrder.Sequent ℒₒᵣ} {ψ : Proposition ℒₒᵣ}
    (hΔ : ∀ χ ∈ Δ, Provable 𝓢 χ) (d : Derivation (ψ :: ∼Δ)) : Provable 𝓢 ψ :=
  cutMany_aux (Θ0 := []) (by simp) hΔ (by simpa using d)

/-! ### Peeling a whole universal-closure prefix

`ACA`'s schemes are stated universally closed over *all* their set and number
parameters (`LK.lean`'s `allSets`/`allNums`).  `specSets`/`specNums` strip the
two prefixes in one step each: `spec₂` is iterated over the `N` bound set
slots (outermost quantifier = slot `N-1` first, slot `0` last) and `spec₁` over
the `n` bound number slots, leaving the matrix with each slot `i` replaced by
the supplied witness `Φ i` / term `v i`. -/

private theorem so_rew_id_of_fv (Ω : SecondOrder.Rew ℒₒᵣ ℕ 0 ℕ 0 ℕ)
    (h : ∀ X : ℕ, Ω.fv X = ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& X)) :
    Ω = SecondOrder.Rew.id := by
  ext X
  · exact X.elim0
  · simp [h]

/-- **A second-order substitution commutes with the `∀¹`-closure.** -/
theorem subst₁_allNums {N₁ N₂ : ℕ} (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ) :
    ∀ (n : ℕ) (χ : Semiproposition ℒₒᵣ N₁ n), Ω.app (allNums χ) = allNums (Ω.app χ)
  |       0, _ => rfl
  | (n + 1), χ => subst₁_allNums Ω n (∀¹ χ)

/-- **`specSets`.**  Instantiate the whole `∀²`-prefix of `allSets φ`: bound set
slot `i` becomes the arithmetical witness `Φ i`. -/
theorem specSets : ∀ {N : ℕ} (φ : Semiproposition ℒₒᵣ N 0)
    (Φ : Fin N → Semiformula ℒₒᵣ ℕ ℕ 0 1), (∀ i, Arith (Φ i)) →
      Provable 𝓢 (allSets φ) → Provable 𝓢 (Semiproposition.subst₁ φ Φ)
  | 0, φ, Φ, _, h => by
      have hid : (SecondOrder.Rew.subst Φ : SecondOrder.Rew ℒₒᵣ ℕ 0 ℕ 0 ℕ) =
          SecondOrder.Rew.id := so_rew_id_of_fv _ (fun _ => rfl)
      have e : Semiproposition.subst₁ φ Φ = φ := by
        show (SecondOrder.Rew.subst Φ).app φ = φ
        rw [hid]; simp
      rw [e]; exact h
  | (N + 1), φ, Φ, hΦ, h => by
      have ih := specSets (∀² φ) (fun i => Φ i.succ) (fun i => hΦ i.succ) h
      have e1 : Semiproposition.subst₁ (∀² φ) (fun i => Φ i.succ) =
          ∀² (Semiproposition.subst₁ φ
            (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)) :>
              fun X => (Φ X.succ).bmap Fin.succ)) := by
        show (SecondOrder.Rew.subst (fun i => Φ i.succ)).app (∀² φ) = _
        show ∀² ((SecondOrder.Rew.subst (fun i => Φ i.succ)).q.app φ) = _
        rw [SecondOrder.Rew.q_subst]
      rw [e1] at ih
      have hspec := spec₂ ih (hΦ 0)
      have hcomp : (SecondOrder.Rew.subst ![Φ 0]).comp
            (SecondOrder.Rew.subst
              (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)) :>
                fun X => (Φ X.succ).bmap Fin.succ)) = SecondOrder.Rew.subst Φ := by
        ext X
        · cases X using Fin.cases with
          | zero =>
              show (SecondOrder.Rew.subst ![Φ 0]).app
                ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)) = Φ 0
              simp only [SecondOrder.Rew.app_bvar, SecondOrder.Rew.subst_bv,
                Matrix.cons_val_fin_one]
              exact FirstOrder.Rewriting.subst1_bvar0_eq _
          | succ X =>
              show (SecondOrder.Rew.subst ![Φ 0]).app ((Φ X.succ).bmap Fin.succ) = Φ X.succ
              rw [SecondOrder.Rew.bmap_app_eq]
              rw [so_rew_id_of_fv ((SecondOrder.Rew.subst ![Φ 0]).bRight Fin.succ)
                (fun _ => rfl)]
              simp
        · show (SecondOrder.Rew.subst ![Φ 0]).app
            ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& X) = _
          simp only [SecondOrder.Rew.app_fvar, SecondOrder.Rew.subst_fv]
          exact FirstOrder.Rewriting.subst1_bvar0_eq _
      have e2 : (Semiproposition.subst₁ φ
            (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)) :>
              fun X => (Φ X.succ).bmap Fin.succ))/⟦Φ 0⟧ = Semiproposition.subst₁ φ Φ := by
        show (SecondOrder.Rew.subst ![Φ 0]).app ((SecondOrder.Rew.subst _).app φ) = _
        rw [← SecondOrder.Rew.app_comp, hcomp]
      rwa [e2] at hspec

/-- **`specNums`.**  Instantiate the whole `∀¹`-prefix of `allNums φ`: bound
number slot `i` becomes the closed term `v i`. -/
theorem specNums : ∀ {n : ℕ} (φ : Semiproposition ℒₒᵣ 0 n)
    (v : Fin n → FirstOrder.Semiterm ℒₒᵣ ℕ 0),
      Provable 𝓢 (allNums φ) → Provable 𝓢 (FirstOrder.Rew.subst v ▹ φ)
  | 0, φ, v, h => by
      have hid : (FirstOrder.Rew.subst v : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) = FirstOrder.Rew.id := by
        ext x
        · exact x.elim0
        · simp
      rw [hid]; simpa using h
  | (n + 1), φ, v, h => by
      have ih := specNums (∀¹ φ) (fun i => v i.succ) h
      have e1 : (FirstOrder.Rew.subst (fun i => v i.succ) ▹ (∀¹ φ) : Proposition ℒₒᵣ) =
          ∀¹ (FirstOrder.Rew.subst
            ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) :>
              fun i => FirstOrder.Rew.bShift (v i.succ)) ▹ φ) := by
        rw [Semiformula.rew_all₀, FirstOrder.Rew.q_subst]
        rfl
      rw [e1] at ih
      have hspec := spec₁ ih (v 0)
      have hcomp : (FirstOrder.Rew.subst ![v 0]).comp
            (FirstOrder.Rew.subst
              ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) :>
                fun i => FirstOrder.Rew.bShift (v i.succ))) = FirstOrder.Rew.subst v := by
        ext x
        · cases x using Fin.cases with
          | zero => simp [FirstOrder.Rew.comp_app]
          | succ i => simp [FirstOrder.Rew.comp_app]
        · simp [FirstOrder.Rew.comp_app]
      have e2 : (FirstOrder.Rew.subst
            ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) :>
              fun i => FirstOrder.Rew.bShift (v i.succ)) ▹ φ)/[v 0] =
          FirstOrder.Rew.subst v ▹ φ := by
        show FirstOrder.Rew.subst ![v 0] ▹ (FirstOrder.Rew.subst _ ▹ φ) = _
        rw [← FirstOrder.TransitiveRewriting.comp_app, hcomp]
      rwa [e2] at hspec

/-! ### The standard instances of the two schemes -/

/-- **An arbitrary instance of the induction scheme.**  Every set parameter is
instantiated at an arithmetical witness `Φ i`, every number parameter at a
closed term `v i`; the result is ordinary induction for the resulting formula.
`φ` has no free variable of either kind (`NoSetFvar`/`shift₀`-fixed) — the
requirement `indScheme₂_mem_ACA` places on membership in `ACA`. -/
theorem indScheme_inst {N n : ℕ} {φ : Semiproposition ℒₒᵣ N (n + 1)} (hns : NoSetFvar φ)
    (h0 : Semiproposition.shift₀ φ = φ) (Φ : Fin N → Semiformula ℒₒᵣ ℕ ℕ 0 1)
    (hΦ : ∀ i, Arith (Φ i)) (v : Fin n → FirstOrder.Semiterm ℒₒᵣ ℕ 0) :
    Provable ACA (FirstOrder.Rew.subst v ▹ Semiproposition.subst₁ (indBody φ) Φ) := by
  have h1 : Provable ACA (Semiproposition.subst₁ (allNums (indBody φ)) Φ) :=
    specSets _ Φ hΦ (ofAxiom (indScheme₂_mem_ACA hns h0))
  rw [show Semiproposition.subst₁ (allNums (indBody φ)) Φ =
      allNums (Semiproposition.subst₁ (indBody φ) Φ) from subst₁_allNums _ n _] at h1
  exact specNums _ v h1

/-- **An arbitrary instance of arithmetical comprehension.** -/
theorem arithComp_inst {N n : ℕ} {ψ : Semiproposition ℒₒᵣ N (n + 1)} (hψ : Arith ψ)
    (hns : NoSetFvar ψ) (h0 : Semiproposition.shift₀ ψ = ψ)
    (Φ : Fin N → Semiformula ℒₒᵣ ℕ ℕ 0 1) (hΦ : ∀ i, Arith (Φ i))
    (v : Fin n → FirstOrder.Semiterm ℒₒᵣ ℕ 0) :
    Provable ACA₀ (FirstOrder.Rew.subst v ▹ Semiproposition.subst₁ (compBody ψ) Φ) := by
  have h1 : Provable ACA₀ (Semiproposition.subst₁ (allNums (compBody ψ)) Φ) :=
    specSets _ Φ hΦ (ofAxiom (arithComp₂_mem_ACA₀ hψ hns h0))
  rw [show Semiproposition.subst₁ (allNums (compBody ψ)) Φ =
      allNums (Semiproposition.subst₁ (compBody ψ) Φ) from subst₁_allNums _ n _] at h1
  exact specNums _ v h1

/-! ### Recovering free-variable instances

`setExt` states its content with the parameter as a *bound* set variable;
`spec₂` at the arithmetical witness `#0 ∈& 0` (`Arith` since it is a bare atom)
recovers the familiar free-variable-parametrized statement. -/

/-- The arithmetical witness recovering a free set variable: `#0 ∈& 0`. -/
abbrev freeWitness : Semiformula ℒₒᵣ ℕ ℕ 0 1 := (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& (0 : ℕ)

theorem arith_freeWitness : Arith freeWitness := trivial

/-- **The free-variable instance of `setExt`.**  `ACA₀ ⊢ ∀x∀y (x = y → x ∈& 0
→ y ∈& 0)`. -/
theorem setExt_spec :
    Provable ACA₀
      ((∀¹ (∀¹
        ((Semiformula.rel FirstOrder.Language.Eq.eq
            ![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2), (#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2)] :
            Semiproposition ℒₒᵣ 1 2) 🡒
          (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) ∈# (0 : Fin 1)) 🡒
            ((#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) ∈# (0 : Fin 1))))))/⟦freeWitness⟧) :=
  spec₂ (ofAxiom setExt_mem_ACA₀) arith_freeWitness

end OrdinalAnalysis.ACA
