module

public import OrdinalAnalysis.KPi.RS.StarDefs
public import OrdinalAnalysis.KPi.Ord.CNF

/-!
# The RS calculus, part 25: `H`-controlled derivations in `RS^∞` (B92 Definitions 3.3--3.8, Lemma 3.9 (a))

* `Op`, `Hext H K`        : operators `H : P(On) → P(On)`, and `H[Θ] (X) := H (k(Θ) ∪ X)` (Def 3.4);
* `NiceSet`, `NiceOp`      : Def 3.5 (the natural sum `ω^α₀ # … # ω^αₙ` is the sorted sum `Ord.pw`);
* `HInf R H Γ α ρ`        : `H ⊢^α_ρ Γ`, **defined by the characterisation of Theorem 3.8**
                             (`{α} ∪ k(Γ) ⊆ H` and one of `(⋀) (⋁) (Cut) (Ref)`); the operator is an *index*
                             because the `(⋀)`-premises are `H[ι]`-controlled;
* the principal formula of `(Ref)` is given up to presentation (`Sim R X S.refl`), exactly as for `Star.ref`;
* Lemma 3.6 (b), (c), `NiceOp.ext`, and Lemma 3.9 (a) (`HInf.weaken`).
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

/-! ### operators -/

/-- operators `H : P(On) → P(On)` (B92 Def 3.3). -/
abbrev Op : Type 2 := Set Ordinal.{1} → Set Ordinal.{1}

/-- `H[K] (X) := H (K ∪ X)`; for `K = k(Θ)` this is `H[Θ]` (B92 Def 3.4). -/
def Hext (H : Op) (K : Set Ordinal.{1}) : Op := fun X => H (K ∪ X)

theorem Hext_apply (H : Op) (K X : Set Ordinal.{1}) : Hext H K X = H (K ∪ X) := rfl

theorem Hext_empty_apply (H : Op) (K : Set Ordinal.{1}) : Hext H K ∅ = H K := by
  simp [Hext]

/-- (B92 Def 3.5 i)) a set `X` of ordinals is *nice* iff `0 ∈ X` and
`ω^α₀ # … # ω^αₙ ∈ X ⇔ {α₀,…,αₙ} ⊆ X` (the natural sum of `ω`-powers is the sorted sum). -/
def NiceSet (X : Set Ordinal.{1}) : Prop :=
  0 ∈ X ∧ ∀ l : List Ordinal.{1}, Ord.Srt l → (Ord.pw l ∈ X ↔ ∀ ξ ∈ l, ξ ∈ X)

/-- (B92 Def 3.5 ii)) a *nice operator*. -/
structure NiceOp (H : Op) : Prop where
  nice : ∀ X, NiceSet (H X)
  sub : ∀ X, X ⊆ H X
  mono : ∀ X X', X' ⊆ H X → H X' ⊆ H X

namespace NiceOp

variable {H : Op}

/-- B92 Lemma 3.6 (c). -/
theorem mono' (hH : NiceOp H) {X X' : Set Ordinal.{1}} (h : X' ⊆ X) : H X' ⊆ H X :=
  hH.mono X X' (h.trans (hH.sub X))

theorem empty_sub (hH : NiceOp H) (X : Set Ordinal.{1}) : H ∅ ⊆ H X :=
  hH.mono' (Set.empty_subset X)

/-- B92 Lemma 3.6 (a). -/
theorem ext (hH : NiceOp H) (K : Set Ordinal.{1}) : NiceOp (Hext H K) where
  nice X := hH.nice (K ∪ X)
  sub X := fun x hx => hH.sub _ (Or.inr hx)
  mono X X' h := by
    intro x hx
    refine hH.mono (K ∪ X) (K ∪ X') ?_ hx
    rintro y (hy | hy)
    · exact hH.sub _ (Or.inl hy)
    · exact h hy

/-- B92 Lemma 3.6 (b): `k(Θ) ⊆ H ⇒ H[Θ] = H`. -/
theorem Hext_eq (hH : NiceOp H) {K : Set Ordinal.{1}} (hK : K ⊆ H ∅) : Hext H K = H := by
  funext X
  apply Set.Subset.antisymm
  · refine hH.mono X (K ∪ X) ?_
    rintro y (hy | hy)
    · exact hH.empty_sub X (hK hy)
    · exact hH.sub X hy
  · exact hH.mono' (Set.subset_union_right)

end NiceOp

/-! ### `kSeq` -/

theorem kSeq_union (Γ Δ : Set RSS) : kSeq (Γ ∪ Δ) = kSeq Γ ∪ kSeq Δ := by
  ext ξ
  constructor
  · rintro ⟨A, hA | hA, hξ⟩
    · exact Or.inl ⟨A, hA, hξ⟩
    · exact Or.inr ⟨A, hA, hξ⟩
  · rintro (⟨A, hA, hξ⟩ | ⟨A, hA, hξ⟩)
    · exact ⟨A, Or.inl hA, hξ⟩
    · exact ⟨A, Or.inr hA, hξ⟩

theorem kSeq_insert (A : RSS) (Γ : Set RSS) : kSeq (insert A Γ) = A.k ∪ kSeq Γ := by
  ext ξ
  constructor
  · rintro ⟨B, rfl | hB, hξ⟩
    · exact Or.inl hξ
    · exact Or.inr ⟨B, hB, hξ⟩
  · rintro (hξ | ⟨B, hB, hξ⟩)
    · exact ⟨A, Set.mem_insert _ _, hξ⟩
    · exact ⟨B, Set.mem_insert_of_mem _ hB, hξ⟩

/-! ### `H`-controlled derivations -/

/-- `HInf R H Γ α ρ` is `H ⊢^α_ρ Γ` (B92 Def 3.7), taken in the form of the characterisation
Theorem 3.8: `{α} ∪ k(Γ) ⊆ H` and one of the four cases.  `ρ` bounds the cut ranks. -/
inductive HInf (R : Set Ordinal.{1}) : Op → Set RSS → Ordinal.{1} → Ordinal.{1} → Prop
  | all {H : Op} {Γ : Set RSS} {A : RSS} {α ρ : Ordinal.{1}}
      (hα : α ∈ H ∅) (hk : kSeq (insert A Γ) ⊆ H ∅) (hA : (expand R A).isOr = false)
      (α₀ : (expand R A).J → Ordinal.{1}) (h0 : ∀ j, α₀ j < α)
      (h : ∀ j : (expand R A).J,
        HInf R (Hext H ((expand R A).ks j)) (insert ((expand R A).child j) Γ) (α₀ j) ρ) :
      HInf R H (insert A Γ) α ρ
  | ex {H : Op} {Γ : Set RSS} {A : RSS} {α ρ α₀ : Ordinal.{1}}
      (hα : α ∈ H ∅) (hk : kSeq (insert A Γ) ⊆ H ∅) (j : (expand R A).J)
      (hA : (expand R A).isOr = true) (h0 : α₀ < α) (hl : (expand R A).lvl j < α)
      (h : HInf R H (insert ((expand R A).child j) Γ) α₀ ρ) : HInf R H (insert A Γ) α ρ
  | cut {H : Op} {Γ : Set RSS} {C : RSS} {α ρ α₀ : Ordinal.{1}}
      (hα : α ∈ H ∅) (hk : kSeq Γ ⊆ H ∅) (hC : C.rk < ρ) (h0 : α₀ < α)
      (h1 : HInf R H (insert C.neg Γ) α₀ ρ) (h2 : HInf R H (insert C Γ) α₀ ρ) : HInf R H Γ α ρ
  | ref {H : Op} {Γ : Set RSS} {α ρ α₀ κ : Ordinal.{1}} (S : SigmaData κ) (hκ : κ ∈ R)
      {X : RSS} (hX : Sim R X S.refl)
      (hα : α ∈ H ∅) (hk : kSeq (insert X Γ) ⊆ H ∅) (h0 : α₀ + 1 < α)
      (h : HInf R H (insert S.sentence Γ) α₀ ρ) : HInf R H (insert X Γ) α ρ

namespace HInf

variable {R : Set Ordinal.{1}} {H : Op} {Γ : Set RSS} {α ρ : Ordinal.{1}}

theorem alpha_mem (h : HInf R H Γ α ρ) : α ∈ H ∅ := by
  cases h <;> assumption

theorem k_sub (h : HInf R H Γ α ρ) : kSeq Γ ⊆ H ∅ := by
  cases h <;> assumption

/-- **B92 Lemma 3.9 (a)** (weakening of the sequent, the length and the cut rank). -/
theorem weaken {R : Set Ordinal.{1}} {H : Op} {Γ : Set RSS} {α ρ : Ordinal.{1}}
    (h : HInf R H Γ α ρ) (hH : NiceOp H) :
    ∀ {Γ' : Set RSS} {α' ρ' : Ordinal.{1}}, α ≤ α' → α' ∈ H ∅ → ρ ≤ ρ' → kSeq Γ' ⊆ H ∅ →
      HInf R H (Γ ∪ Γ') α' ρ' := by
  induction h with
  | @all H Γ A α ρ hα hk hA α₀ h0 h ih =>
    intro Γ' α' ρ' hαα' hα' hρ hk'
    rw [Set.insert_union]
    refine HInf.all hα' ?_ hA α₀ (fun j => lt_of_lt_of_le (h0 j) hαα') ?_
    · rw [← Set.insert_union, kSeq_union]
      exact Set.union_subset hk hk'
    · intro j
      have hH' := hH.ext ((expand R A).ks j)
      have := (h j).k_sub
      have h1 := ih j hH' (Γ' := Γ') (α' := α₀ j) (ρ' := ρ') le_rfl (h j).alpha_mem hρ
        (fun x hx => by
          show x ∈ Hext H _ ∅
          rw [Hext_empty_apply]
          exact hH.empty_sub _ (hk' hx))
      rwa [Set.insert_union] at h1
  | @ex H Γ A α ρ α₀ hα hk j hA h0 hl h ih =>
    intro Γ' α' ρ' hαα' hα' hρ hk'
    rw [Set.insert_union]
    refine HInf.ex hα' ?_ j hA (lt_of_lt_of_le h0 hαα') (lt_of_lt_of_le hl hαα') ?_
    · rw [← Set.insert_union, kSeq_union]
      exact Set.union_subset hk hk'
    · have h1 := ih hH (Γ' := Γ') (α' := α₀) le_rfl h.alpha_mem hρ hk'
      rwa [Set.insert_union] at h1
  | @cut H Γ C α ρ α₀ hα hk hC h0 h1 h2 ih1 ih2 =>
    intro Γ' α' ρ' hαα' hα' hρ hk'
    refine HInf.cut (C := C) hα' ?_ (lt_of_lt_of_le hC hρ) (lt_of_lt_of_le h0 hαα') ?_ ?_
    · rw [kSeq_union]
      exact Set.union_subset hk hk'
    · have := ih1 hH (Γ' := Γ') (α' := α₀) le_rfl h1.alpha_mem hρ hk'
      rwa [Set.insert_union] at this
    · have := ih2 hH (Γ' := Γ') (α' := α₀) le_rfl h2.alpha_mem hρ hk'
      rwa [Set.insert_union] at this
  | @ref H Γ α ρ α₀ κ S hκ X hX hα hk h0 h ih =>
    intro Γ' α' ρ' hαα' hα' hρ hk'
    rw [Set.insert_union]
    refine HInf.ref S hκ hX hα' ?_ (lt_of_lt_of_le h0 hαα') ?_
    · rw [← Set.insert_union, kSeq_union]
      exact Set.union_subset hk hk'
    · have := ih hH (Γ' := Γ') (α' := α₀) le_rfl h.alpha_mem hρ hk'
      rwa [Set.insert_union] at this

end HInf

end OrdinalAnalysis.KPi.RS
