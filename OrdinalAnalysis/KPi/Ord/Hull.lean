import OrdinalAnalysis.KPi.Ord.Lemma45

/-!
# Buchholz 1992, Def 3.5 / 4.3 (operators `H_γ`), Lemma 4.6 and Lemma 4.7 ((A1)-(A4))

`Hop γ X = H_γ(X) = ⋂ {C(α, β) | X ⊆ C(α, β) ∧ γ < α}`.  For B92's `H_γ[Θ] = H_γ(k(Θ))` the finite
sequence `Θ` only enters through the set `K = k(Θ) ⊆ On` of ordinals occurring in it, so `Θ` is
abstracted to `K`.

* `Hop_niceOp` (4.6a), `Hop_veblen` (4.6b), `Hop_psi` (4.6c), `Hop_Om` (4.6d), `Hop_mono` (4.6e);
* `Ombar`, `Kbar`, `AA` (`𝒜(Θ; γ, κ, μ)`), and `A1`-`A4` (Lemma 4.7).
-/

set_option autoImplicit false

open Ordinal Cardinal Set Order

noncomputable section

namespace OrdinalAnalysis.KPi.Ord

/-- B92 Def 4.3. -/
def Hop (γ : O) (X : Set O) : Set O := {x | ∀ α β, γ < α → X ⊆ C α β → x ∈ C α β}

theorem mem_Hop {γ x : O} {X : Set O} :
    x ∈ Hop γ X ↔ ∀ α β, γ < α → X ⊆ C α β → x ∈ C α β := Iff.rfl

/-- B92 Def 3.5(i): `X` is nice (`ω^{α₀}#…#ω^{αₙ} ∈ X ⇔ all αᵢ ∈ X`; with `n = 0 … ` and the empty
sum this includes `0 ∈ X`; natural sums of ω-powers are sorted ordinary sums, see `CNF.lean`). -/
def Nice (X : Set O) : Prop := ∀ l : List O, Srt l → (pw l ∈ X ↔ ∀ ξ ∈ l, ξ ∈ X)

/-- B92 Def 3.5(ii): nice operators. -/
def NiceOp (H : Set O → Set O) : Prop :=
  (∀ X, Nice (H X)) ∧ (∀ X, X ⊆ H X) ∧ (∀ X X', X' ⊆ H X → H X' ⊆ H X)

/-! ### Lemma 4.6 -/

theorem Hop_nice (γ : O) (X : Set O) : Nice (Hop γ X) := by
  intro l hl
  constructor
  · intro h ξ hξ α β hα hX
    exact (nice_C hl).1 (h α β hα hX) ξ hξ
  · intro h α β hα hX
    exact (nice_C hl).2 (fun ξ hξ => h ξ hξ α β hα hX)

theorem Hop_sub (γ : O) (X : Set O) : X ⊆ Hop γ X := fun _ hx _ _ _ hX => hX hx

theorem Hop_trans (γ : O) {X X' : Set O} (h : X' ⊆ Hop γ X) : Hop γ X' ⊆ Hop γ X := by
  intro x hx α β hα hX
  exact hx α β hα (fun y hy => h hy α β hα hX)

/-- Lemma 4.6a: `H_γ` is a nice operator. -/
theorem Hop_niceOp (γ : O) : NiceOp (Hop γ) :=
  ⟨Hop_nice γ, Hop_sub γ, fun _ _ h => Hop_trans γ h⟩

/-- Lemma 4.6b: `H_γ` is closed under `φ`. -/
theorem Hop_veblen {γ : O} {X : Set O} {x y : O} (hx : x ∈ Hop γ X) (hy : y ∈ Hop γ X) :
    veblen x y ∈ Hop γ X :=
  fun α β hα hX => Cl.phi (hx α β hα hX) (hy α β hα hX)

theorem Hop_add {γ : O} {X : Set O} {x y : O} (hx : x ∈ Hop γ X) (hy : y ∈ Hop γ X) :
    x + y ∈ Hop γ X :=
  fun α β hα hX => Cl.add (hx α β hα hX) (hy α β hα hX)

theorem Hop_opow {γ : O} {X : Set O} {x : O} (hx : x ∈ Hop γ X) : ω ^ x ∈ Hop γ X :=
  fun α β hα hX => Cl.opow (hx α β hα hX)

theorem Hop_zero {γ : O} {X : Set O} : (0 : O) ∈ Hop γ X := fun _ _ _ _ => Cl.zero

/-- Lemma 4.6c: `ξ ≤ γ`, `ξ, π ∈ H_γ(X)`, `π ∈ R` imply `ψ_π ξ ∈ H_γ(X)`. -/
theorem Hop_psi {γ : O} {X : Set O} {ξ π : O} (hξγ : ξ ≤ γ) (hξ : ξ ∈ Hop γ X)
    (hπ : π ∈ Hop γ X) (hR : π ∈ Rset) : psiK π ξ ∈ Hop γ X :=
  fun α β hα hX => Cl.psi (hξ α β hα hX) (hπ α β hα hX) (lt_of_le_of_lt hξγ hα) hR

/-- Lemma 4.6d: `Ω_σ ≤ α ≤ Ω_{σ+1}` and `α ∈ H_γ(X)` imply `Ω_σ, Ω_{σ+1} ∈ H_γ(X)`. -/
theorem Hop_Om {γ : O} {X : Set O} {σ a : O} (h1 : Om σ ≤ a) (h2 : a ≤ Om (σ + 1))
    (ha : a ∈ Hop γ X) : Om σ ∈ Hop γ X ∧ Om (σ + 1) ∈ Hop γ X := by
  refine ⟨fun α β hα hX => ?_, fun α β hα hX => ?_⟩
  · exact Cl.om (mem_of_between h1 h2 (ha α β hα hX))
  · exact Cl.om (Cl.succ (mem_of_between h1 h2 (ha α β hα hX)))

/-- Lemma 4.6e (in the form `γ ≤ δ`; `γ < δ` is B92's statement). -/
theorem Hop_mono {γ δ : O} (h : γ ≤ δ) (X : Set O) : Hop γ X ⊆ Hop δ X :=
  fun _ hx α β hα hX => hx α β (lt_of_le_of_lt h hα) hX

/-! ### Lemma 4.7 -/

open scoped Classical in
/-- `Ω̄_σ := Ω_σ + 1` if `Ω_σ ∈ R`, else `Ω_σ`. -/
def Ombar (σ : O) : O := if Om σ ∈ Rset then Om σ + 1 else Om σ

/-- `K̄ = {Ω̄_σ : σ ≤ I}`. -/
def Kbar : Set O := {μ | ∃ σ ≤ Iord, μ = Ombar σ}

/-- `𝒜(Θ; γ, κ, μ)` with `K = k(Θ)`; `κ ∈ R` is B92's convention. -/
structure AA (K : Set O) (γ κ μ : O) : Prop where
  kR : κ ∈ Rset
  muK : μ ∈ Kbar
  gam : γ ∈ Hop γ K
  kap : κ ∈ Hop γ K
  mu : μ ∈ Hop γ K
  sub : ∀ τ ∈ Rset, κ ≤ τ → K ⊆ Ck τ (γ + 1)

section A47
variable {K : Set O} {γ κ μ : O}

theorem AA.Hsub (h : AA K γ κ μ) : Hop γ K ⊆ Ck κ (γ + 1) := by
  intro x hx
  exact hx (γ + 1) (psiK κ (γ + 1)) (lt_add_one γ) (h.sub κ h.kR le_rfl)

/-- (A1) -/
theorem A1 (h : AA K γ κ μ) {ξ γ' : O} (hξ : ξ ∈ Hop γ K) (hγ' : γ' = γ + ω ^ (μ + ξ)) :
    γ' ∈ Hop γ K ∧ psiK κ γ' ∈ Hop γ' K := by
  have h1 : γ' ∈ Hop γ K := by
    rw [hγ']; exact Hop_add h.gam (Hop_opow (Hop_add h.mu hξ))
  have hle : γ ≤ γ' := by rw [hγ']; exact le_self_add
  refine ⟨h1, Hop_psi le_rfl (Hop_mono hle K h1) (Hop_mono hle K h.kap) h.kR⟩

/-- (A2) -/
theorem A2 (h : AA K γ κ μ) {ξ η : O} (hξ : ξ ∈ Hop γ K) (hlt : γ + ω ^ (μ + ξ) < η) :
    psiK κ (γ + ω ^ (μ + ξ)) < psiK κ η := by
  have h1 : γ + ω ^ (μ + ξ) ∈ Hop γ K := Hop_add h.gam (Hop_opow (Hop_add h.mu hξ))
  have h2 : γ + ω ^ (μ + ξ) ∈ Ck κ (γ + 1) := h.Hsub h1
  have h3 : γ < γ + ω ^ (μ + ξ) := lt_add_of_pos_right γ (opow_pos _ omega0_pos)
  have h4 : γ + 1 ≤ η := (Order.add_one_le_iff.2 h3).trans hlt.le
  have h5 : γ + ω ^ (μ + ξ) ∈ Ck κ η := (psiK_mono h.kR h4).2 h2
  exact psiK_lt_psiK h.kR hlt h5

/-- (A3) -/
theorem A3 (h : AA K γ κ μ) {τ : O} (hτ : τ ∈ Rset) (hκτ : κ ≤ τ) :
    ∀ x ∈ Hop γ K, x < τ → x < psiK τ (γ + 1) := by
  intro x hx hxτ
  have h1 : x ∈ Ck τ (γ + 1) := hx (γ + 1) (psiK τ (γ + 1)) (lt_add_one γ) (h.sub τ hτ hκτ)
  have := (Ck_inter hτ (γ + 1)).subset (show x ∈ Ck τ (γ + 1) ∩ Iio τ from ⟨h1, hxτ⟩)
  exact mem_Iio.1 this

/-- (A4) -/
theorem A4 {γ γ' μ μ' α α' : O} (h1 : γ' < γ + ω ^ (μ + α)) (h2 : μ' + α' < μ + α) :
    γ' + ω ^ (μ' + α') < γ + ω ^ (μ + α) := by
  have hp : ω ^ (μ' + α') < ω ^ (μ + α) := (opow_lt_opow_iff_right one_lt_omega0).2 h2
  rcases le_or_gt γ' γ with hle | hlt
  · calc γ' + ω ^ (μ' + α') ≤ γ + ω ^ (μ' + α') := add_le_add_left hle _
      _ < γ + ω ^ (μ + α) := add_lt_add_right hp γ
  · obtain ⟨ξ, hξ⟩ := exists_add_of_le hlt.le
    subst hξ
    have hξ' : ξ < ω ^ (μ + α) := by
      by_contra hnot
      exact absurd h1 (not_lt.2 (add_le_add_right (not_lt.1 hnot) γ))
    calc γ + ξ + ω ^ (μ' + α') = γ + (ξ + ω ^ (μ' + α')) := add_assoc _ _ _
      _ < γ + ω ^ (μ + α) :=
        add_lt_add_right (isPrincipal_add_omega0_opow (μ + α) hξ' hp) γ

end A47

end OrdinalAnalysis.KPi.Ord
