/-
  Derivability below a height bound, and three ways of producing derivations
  of `RA_∞` with the junk literals from outside the calculus.

  `DerLt ρ Γ H`: `Γ` has a derivation of cut rank `ρ` and some height `< H`.
  The rules of the calculus, restated for `DerLt`, turn premises derivable below
  `H` into a conclusion derivable below any `H' > H`; the ω-rule needs no uniform
  premise height, only a common bound.

  The three sources of derivations, all of height below `ε₀`:

  * **Validities** (`DerLt.of_valid`): a closed formula true in every
    `LRA`-structure under every assignment is a theorem of the empty theory
    (completeness), whose cut-free replay has finite cut rank.
  * **Theorems of `RAlt ν`** (`DerLt.of_RAlt`): the embedded proof has cut rank
    `blkTop ν' ⊕ k` for some `ν' < ν`, which is below `blkTop ν`.
  * **True arithmetic** (`DerLt.of_true`): `omega_completeR`.

  `DerLt.discharge` combines the first with cuts: if `C` follows logically from
  hypotheses `A₁, …, Aₙ`, each derivable in the context `Γ` and each of rank below
  `ρ`, then `C` is derivable in the context `Γ`, `n` inferences higher.  The
  conclusion `C` itself is never cut, so its rank is unrestricted.
-/
import OrdinalAnalysis.Ramified.DescentBetaAux1

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder

/-- `Γ` is derivable in `RA_∞` with the junk literals, at cut rank `ρ`, below the
height `H`. -/
def DerLt (ρ : Gamma0Note) (Γ : Sequent LRA) (H : Gamma0Note) : Prop :=
  ∃ α : Gamma0Note, α < H ∧ OmegaDerivableR junkLitsR evInstR ρ α Γ

/-! ### Small facts on heights -/

theorem ofNat_lt_epsilonNote_zero (n : ℕ) :
    Gamma0Note.ofNat n < Gamma0Note.epsilonNote 0 := by
  rw [Gamma0Note.lt_def, Gamma0Note.repr_epsilonNote_eq_epsilon]
  have h : (Gamma0Note.repr (Gamma0Note.ofNat n)) = (n : Ordinal) := Gamma0Note.repr_ofNat n
  rw [h]
  exact lt_of_lt_of_le (Ordinal.natCast_lt_omega0 n)
    (le_trans (Ordinal.omega0_le_of_isSuccLimit Ordinal.isSuccLimit_omega0)
      (Ordinal.omega0_lt_epsilon 0).le)

theorem ofNat_lt_omegaPow_one (n : ℕ) :
    Gamma0Note.ofNat n < Gamma0Note.omegaPow 1 := by
  rw [Gamma0Note.lt_def, Gamma0Note.repr_omegaPow, Gamma0Note.repr_one, Ordinal.opow_one]
  rw [Gamma0Note.repr_ofNat]
  exact Ordinal.natCast_lt_omega0 n

theorem nadd_ofNat_lt_nadd_ofNat (H : Gamma0Note) {m n : ℕ} (h : m < n) :
    Gamma0Note.nadd H (Gamma0Note.ofNat m) < Gamma0Note.nadd H (Gamma0Note.ofNat n) :=
  Gamma0Note.nadd_lt_nadd_right H (Gamma0Note.ofNat_lt_ofNat h)

theorem nadd_ofNat_le_nadd_ofNat (H : Gamma0Note) {m n : ℕ} (h : m ≤ n) :
    Gamma0Note.nadd H (Gamma0Note.ofNat m) ≤ Gamma0Note.nadd H (Gamma0Note.ofNat n) := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (nadd_ofNat_lt_nadd_ofNat H h)
  · exact le_rfl

theorem le_nadd_ofNat (H : Gamma0Note) (n : ℕ) : H ≤ Gamma0Note.nadd H (Gamma0Note.ofNat n) :=
  Gamma0Note.le_nadd_left H _

theorem nadd_ofNat_add (H : Gamma0Note) (m n : ℕ) :
    Gamma0Note.nadd (Gamma0Note.nadd H (Gamma0Note.ofNat m)) (Gamma0Note.ofNat n) =
      Gamma0Note.nadd H (Gamma0Note.ofNat (m + n)) := by
  apply Gamma0Note.repr_injective
  rw [Gamma0Note.repr_nadd_ofNat, Gamma0Note.repr_nadd_ofNat, Gamma0Note.repr_nadd_ofNat,
    add_assoc, Nat.cast_add]

namespace DerLt

variable {ρ : Gamma0Note}

theorem of_der {α H : Gamma0Note} {Γ : Sequent LRA}
    (h : OmegaDerivableR junkLitsR evInstR ρ α Γ) (hα : α < H) : DerLt ρ Γ H :=
  ⟨α, hα, h⟩

theorem mono {Γ : Sequent LRA} {H H' : Gamma0Note} (h : DerLt ρ Γ H) (hH : H ≤ H') :
    DerLt ρ Γ H' := by
  obtain ⟨α, hα, d⟩ := h
  exact ⟨α, lt_of_lt_of_le hα hH, d⟩

theorem weak {Γ Δ : Sequent LRA} {H : Gamma0Note} (h : DerLt ρ Γ H) (hs : Γ ⊆ Δ) :
    DerLt ρ Δ H := by
  obtain ⟨α, hα, d⟩ := h
  exact ⟨α, hα, .contraction hs d⟩

theorem mono_rank {ρ' : Gamma0Note} {Γ : Sequent LRA} {H : Gamma0Note} (h : DerLt ρ Γ H)
    (hρ : ρ ≤ ρ') : DerLt ρ' Γ H := by
  obtain ⟨α, hα, d⟩ := h
  exact ⟨α, hα, d.mono_rank hρ⟩

/-- A derivation below `H` is a derivation at height `H`. -/
theorem toDer {Γ : Sequent LRA} {H : Gamma0Note} (h : DerLt ρ Γ H) :
    OmegaDerivableR junkLitsR evInstR ρ H Γ := by
  obtain ⟨α, hα, d⟩ := h
  exact d.mono_ord (le_of_lt hα)

theorem or {φ ψ : Proposition LRA} {Γ : Sequent LRA} {H H' : Gamma0Note}
    (h : DerLt ρ (φ :: ψ :: Γ) H) (hH : H < H') : DerLt ρ ((φ ⋎ ψ) :: Γ) H' :=
  ⟨H, hH, .or (lt_of_lt_of_le h.choose_spec.1 le_rfl) h.choose_spec.2⟩

theorem and {φ ψ : Proposition LRA} {Γ : Sequent LRA} {H H' : Gamma0Note}
    (h₁ : DerLt ρ (φ :: Γ) H) (h₂ : DerLt ρ (ψ :: Γ) H) (hH : H < H') :
    DerLt ρ ((φ ⋏ ψ) :: Γ) H' :=
  ⟨H, hH, .and h₁.choose_spec.1 h₂.choose_spec.1 h₁.choose_spec.2 h₂.choose_spec.2⟩

/-- **The ω-rule**: premises below a common bound. -/
theorem all {φ : Semiproposition LRA 1} {Γ : Sequent LRA} {H H' : Gamma0Note}
    (h : ∀ n : ℕ, DerLt ρ (evInstR.inst φ n :: Γ) H) (hH : H < H') :
    DerLt ρ ((∀¹ φ) :: Γ) H' := by
  choose β hβ d using h
  exact ⟨H, hH, .omegaRule β hβ d⟩

theorem exs {φ : Semiproposition LRA 1} {Γ : Sequent LRA} {H H' : Gamma0Note} (n : ℕ)
    (h : DerLt ρ (evInstR.inst φ n :: Γ) H) (hH : H < H') : DerLt ρ ((∃¹ φ) :: Γ) H' :=
  ⟨H, hH, .exs n h.choose_spec.1 h.choose_spec.2⟩

theorem cut {φ : Proposition LRA} {Γ Δ : Sequent LRA} {H H' : Gamma0Note}
    (hrk : rank φ < ρ) (h₁ : DerLt ρ (φ :: Γ) H) (h₂ : DerLt ρ (∼φ :: Δ) H) (hH : H < H') :
    DerLt ρ (Γ ++ Δ) H' :=
  ⟨H, hH, .cut hrk h₁.choose_spec.1 h₂.choose_spec.1 h₁.choose_spec.2 h₂.choose_spec.2⟩

theorem pr {a n : ℕ} {Γ : Sequent LRA} {H H' : Gamma0Note} (ha : Good a)
    (h : DerLt ρ (evInstR.inst (body a) n :: Γ) H) (hH : H < H') :
    DerLt ρ (memAt (lvl a) (num n) (num a) :: Γ) H' :=
  ⟨H, hH, .pr ha h.choose_spec.1 h.choose_spec.2⟩

theorem npr {a n : ℕ} {Γ : Sequent LRA} {H H' : Gamma0Note} (ha : Good a)
    (h : DerLt ρ (∼(evInstR.inst (body a) n) :: Γ) H) (hH : H < H') :
    DerLt ρ (nmemAt (lvl a) (num n) (num a) :: Γ) H' :=
  ⟨H, hH, .npr ha h.choose_spec.1 h.choose_spec.2⟩

theorem invOr {φ ψ : Proposition LRA} {Γ : Sequent LRA} {H : Gamma0Note}
    (h : DerLt ρ ((φ ⋎ ψ) :: Γ) H) : DerLt ρ (φ :: ψ :: Γ) H := by
  obtain ⟨α, hα, d⟩ := h
  exact ⟨α, hα, d.invOr⟩

theorem invAll {φ : Semiproposition LRA 1} {Γ : Sequent LRA} {H : Gamma0Note}
    (h : DerLt ρ ((∀¹ φ) :: Γ) H) (n : ℕ) : DerLt ρ (evInstR.inst φ n :: Γ) H := by
  obtain ⟨α, hα, d⟩ := h
  exact ⟨α, hα, d.invAll n⟩

/-- **Identity**, below any height at least `ε₀`. -/
theorem identity (φ : Proposition LRA) {H : Gamma0Note} (hH : Gamma0Note.epsilonNote 0 ≤ H) :
    DerLt ρ [φ, ∼φ] H :=
  ⟨_, lt_of_lt_of_le (ofNat_lt_epsilonNote_zero _) hH, OmegaDerivableR.identity_formula φ⟩

/-- **Cut against a derivable hypothesis**: from `∼A, Γ` and `A, Δ` derive `Γ, Δ`. -/
theorem cutHyp {A : Proposition LRA} {Γ Δ : Sequent LRA} {H H' : Gamma0Note}
    (hrk : rank A < ρ) (h₁ : DerLt ρ (∼A :: Γ) H) (h₂ : DerLt ρ (A :: Δ) H) (hH : H < H') :
    DerLt ρ (Γ ++ Δ) H' :=
  (cut hrk h₂ h₁ hH).weak (by subset_tac)

/-! ### Derivations from outside the calculus -/

/-- **A theorem of `RAlt ν`**, embedded: cut rank below `blkTop ν`, height below `ε₀`. -/
theorem of_RAlt {ν : Lv} (hν : 1 ≤ ν) {φ : Proposition LRA} (hφ : φ.freeVariables = ∅)
    (h : RAlt ν ⊢ Semiformula.univCl φ) (hρ : Gamma0Note.blkTop ν ≤ ρ) {H : Gamma0Note}
    (hH : Gamma0Note.epsilonNote 0 ≤ H) : DerLt ρ [evR φ] H := by
  obtain ⟨h⟩ := h
  obtain ⟨ν', k, α, hν', hα, hd⟩ := provable_rank_height_of_exists (RAlt ν)
    (fun τ hτ => RAlt_axiom_derivable_lt_epsilon hν τ hτ) h
  have hν'lt : ν' < ν := by
    rcases hν' with rfl | ⟨τ, hτ, rfl⟩
    · exact lt_of_lt_of_le Gamma0Note.zero_lt_one hν
    · exact lvlOf_emb_lt_of_mem_RAlt hν hτ
  rw [emb_univCl_of_freeVariables_eq_empty hφ] at hd
  have hν0 : ν ≠ 0 := ne_of_gt (lt_of_lt_of_le Gamma0Note.zero_lt_one hν)
  have hrk : Gamma0Note.nadd (Gamma0Note.blkTop ν') (Gamma0Note.ofNat k) ≤ ρ :=
    le_trans (le_of_lt (lt_of_le_of_lt
      (Gamma0Note.nadd_le_nadd_left _ (Gamma0Note.blkTop_le_blk hν'lt))
      (Gamma0Note.blk_nadd_ofNat_lt_blkTop hν0 k))) hρ
  exact ⟨α, lt_of_lt_of_le hα hH, (hd.mono_lits trueArithLitsR_le_junkLitsR).mono_rank hrk⟩

/-- **A validity**, embedded: finite cut rank, height below `ε₀`. -/
theorem of_valid {φ : Proposition LRA} (hφ : φ.freeVariables = ∅)
    (hv : ∀ (M : Type) [Nonempty M] [Structure LRA M] (f : ℕ → M), Semiformula.Evalf f φ)
    (hρ : Gamma0Note.omegaPow 1 ≤ ρ) {H : Gamma0Note}
    (hH : Gamma0Note.epsilonNote 0 ≤ H) : DerLt ρ [evR φ] H := by
  have hprov : (∅ : Theory LRA) ⊢ Semiformula.univCl φ := by
    apply Theory.Proof.complete.{0, 0}
    rw [consequence_iff]
    intro M _ _ _
    rw [models_iff_proposition]
    intro f
    exact hv M f
  obtain ⟨h⟩ := hprov
  obtain ⟨ν', k, α, hν', hα, hd⟩ := provable_rank_height_of_exists (∅ : Theory LRA)
    (fun τ hτ => absurd hτ (Set.notMem_empty τ)) h
  have h0 : ν' = 0 := by
    rcases hν' with h0 | ⟨τ, hτ, -⟩
    · exact h0
    · exact absurd hτ (Set.notMem_empty τ)
  subst h0
  rw [emb_univCl_of_freeVariables_eq_empty hφ, Gamma0Note.blkTop_zero,
    Gamma0Note.zero_nadd] at hd
  exact ⟨α, lt_of_lt_of_le hα hH, (hd.mono_lits trueArithLitsR_le_junkLitsR).mono_rank
    (le_trans (le_of_lt (ofNat_lt_omegaPow_one k)) hρ)⟩

/-- **A true closed arithmetical formula**: `omega_completeR`. -/
theorem of_true {φ : Proposition LRA} (hR : RFree φ) (hc : φ.freeVariables = ∅)
    (ht : Semiformula.Eval (s := stdLRA) ![] (fun _ => 0) φ) {H : Gamma0Note}
    (hH : Gamma0Note.epsilonNote 0 ≤ H) : DerLt ρ [evR φ] H :=
  ⟨_, lt_of_lt_of_le (hgtR_lt_epsilonNote φ 0) hH,
    ((omega_completeR φ hR hc ht).mono_rank (gamma0_zero_le ρ)).mono_lits
      trueArithLitsR_le_junkLitsR⟩

/-! ### Discharging hypotheses of a validity -/

/-- `∼A₁ ⋎ (∼A₂ ⋎ ⋯ ⋎ C)`. -/
def impList : List (Proposition LRA) → Proposition LRA → Proposition LRA
  | [], C => C
  | A :: As, C => ∼A ⋎ impList As C

theorem freeVariables_impList (C : Proposition LRA) (hC : C.freeVariables = ∅) :
    ∀ (As : List (Proposition LRA)), (∀ A ∈ As, A.freeVariables = ∅) →
      (impList As C).freeVariables = ∅
  | [], _ => hC
  | A :: As, h => by
      rw [impList, Semiformula.freeVariables_or, Semiformula.freeVariables_not,
        h A List.mem_cons_self, freeVariables_impList C hC As
          (fun B hB => h B (List.mem_cons_of_mem _ hB)), Finset.union_empty]

theorem evalf_impList {M : Type} [Structure LRA M] (f : ℕ → M) (C : Proposition LRA) :
    ∀ (As : List (Proposition LRA)),
      ((∀ A ∈ As, Semiformula.Evalf f A) → Semiformula.Evalf f C) →
        Semiformula.Evalf f (impList As C)
  | [], h => h (fun _ h => absurd h List.not_mem_nil)
  | A :: As, h => by
      rw [impList]
      simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
        LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq]
      by_cases hA : Semiformula.Evalf f A
      · exact Or.inr (evalf_impList f C As
          (fun hAs => h (fun B hB => by
            rcases List.mem_cons.mp hB with rfl | hB
            · exact hA
            · exact hAs B hB)))
      · exact Or.inl hA

theorem discharge_aux {C : Proposition LRA} {Γ : Sequent LRA} {H : Gamma0Note} :
    ∀ (As : List (Proposition LRA)), (∀ A ∈ As, rank A < ρ) →
      (∀ A ∈ As, DerLt ρ (evR A :: Γ) H) →
      ∀ (m : ℕ), DerLt ρ (evR (impList As C) :: Γ) (Gamma0Note.nadd H (Gamma0Note.ofNat m)) →
        DerLt ρ (evR C :: Γ) (Gamma0Note.nadd H (Gamma0Note.ofNat (m + As.length)))
  | [], _, _, m, h => by simpa [impList] using h
  | A :: As, hrk, hd, m, h => by
      rw [impList, evR_or, evR_neg] at h
      have h1 := invOr h
      have h2 : DerLt ρ (evR A :: Γ) (Gamma0Note.nadd H (Gamma0Note.ofNat m)) :=
        (hd A List.mem_cons_self).mono (le_nadd_ofNat H m)
      have h3 : DerLt ρ (evR (impList As C) :: Γ) (Gamma0Note.nadd H (Gamma0Note.ofNat (m + 1))) :=
        (cutHyp (by rw [rank_evR]; exact hrk A List.mem_cons_self) h1 h2
          (nadd_ofNat_lt_nadd_ofNat H (Nat.lt_succ_self m))).weak (by subset_tac)
      have h4 := discharge_aux As (fun B hB => hrk B (List.mem_cons_of_mem _ hB))
        (fun B hB => hd B (List.mem_cons_of_mem _ hB)) (m + 1) h3
      rw [show m + 1 + As.length = m + (A :: As).length by simp; omega] at h4
      exact h4

/-- **Discharging the hypotheses of a validity.**  If `C` holds wherever
`A₁, …, Aₙ` hold, all closed, each `Aᵢ` of rank below `ρ` and derivable in the
context `Γ` below `H ≥ ε₀`, then `C` is derivable in the context `Γ` below
`H ⊕ n`.  `ρ ≥ ω` pays for the finite cut rank of the embedded validity. -/
theorem discharge {C : Proposition LRA} {Γ : Sequent LRA} {H : Gamma0Note}
    (As : List (Proposition LRA)) (hC : C.freeVariables = ∅)
    (hAc : ∀ A ∈ As, A.freeVariables = ∅)
    (hv : ∀ (M : Type) [Nonempty M] [Structure LRA M] (f : ℕ → M),
      (∀ A ∈ As, Semiformula.Evalf f A) → Semiformula.Evalf f C)
    (hrk : ∀ A ∈ As, rank A < ρ) (hd : ∀ A ∈ As, DerLt ρ (evR A :: Γ) H)
    (hρ : Gamma0Note.omegaPow 1 ≤ ρ) (hH : Gamma0Note.epsilonNote 0 ≤ H) :
    DerLt ρ (evR C :: Γ) (Gamma0Note.nadd H (Gamma0Note.ofNat (As.length + 1))) := by
  have h0 : DerLt ρ [evR (impList As C)] H :=
    of_valid (freeVariables_impList C hC As hAc)
      (fun M _ _ f => evalf_impList f C As (hv M f)) hρ hH
  have h1 : DerLt ρ (evR (impList As C) :: Γ) (Gamma0Note.nadd H (Gamma0Note.ofNat 1)) :=
    (h0.weak (by subset_tac)).mono (le_nadd_ofNat H 1)
  have h2 := discharge_aux As hrk hd 1 h1
  rw [Nat.add_comm] at h2
  exact h2

end DerLt

end Ramified

end OrdinalAnalysis
