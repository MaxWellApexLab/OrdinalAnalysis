import OrdinalAnalysis.IDw.TransferAux
/-
  The transfer lemmas of the uniform embedding of `IDw A` into `IDwDerivable`: they move between
  the full binary atom `Jlev ⊤` and the level-`k` atoms `I_k`, `Jlev k`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §6 (Lemma 6.1, Exercise 6.3), for the uniform theory
  `IDw A` (`IDw/Theory.lean`: a binary `J(y,x)`, `y` a bound variable).  Throughout `Ω_{k+1}` is `ThetaVNoteD.Omega k`, `H` is any nice operator
  (`ThetaVNoteD.NiceS H`), the derivations have cut rank `0`, and `s`, `a`, `j` are closed terms.

    T1  `⊢ ¬Jlev ⊤ (k̄, a), I_k a`                     height `Ω_{k+1} ⊕ 1`   (`transfer1`)
    T2  `⊢ ¬I_k a, Jlev ⊤ (k̄, a)`                     height `Ω_{k+1} ⊕ 1`   (`transfer2`)
    T3  `⊢ ¬(j < k̄ ∧ Jlev ⊤ (j, a)), Jlev k (j, a)`     height `Ω_{k+1} ⊕ 4`   (`transfer3`)
    T4  `⊢ ¬Jlev k (j, a), j < k̄ ∧ Jlev ⊤ (j, a)`       height `Ω_{k+1} ⊕ 3`   (`transfer4`)
    T5  `⊢ ¬B, B'` for `B'` obtained from `B` by replacing atoms along T1-T4
        (`Cong (OkFwd k)` resp. `Cong (OkBwd k)`), height `Ω_{k+1} ⊕ (4 + 2c)`, `c` the
        connective/quantifier depth of `B` (`transfer5_fwd`, `transfer5_bwd`).

  The heights depend on `k` only through `Ω_{k+1}`, and the additive constants (`1`, `4`, `3`,
  `4 + 2c`) not at all, so a uniform derivation over all levels stays below `Ω_ω`.  T3 and T4
  are unconditional in the value `val j`: for `val j ≥ k` the disjunct `¬(j < k̄)` is a true
  literal, resp. the rule (njlev) has no premise.

  All of this rests on Lemma 6.1 for `IDwDerivable` (`IDw/TransferAux.lean`, `Transfer.taut`),
  including the new atoms `Jlev ℓ`.

  Contents.

    `ltW`, `qTop`                                the formulas `s < t`, `j < k̄ ∧ Jlev ⊤ (j,a)`
    `identity_IOmega`                            `⊢ I_k a, ¬I_k a` at height `Ω_{k+1}`
    `njlev_to_stage`, `stage_to_jlev`            T1, T2 for a general `Jlev ℓ`, `val s = k < ℓ`
    `transfer1`, `transfer2`, `transfer3`, `transfer4`
    `Cong`, `cong_derivable`                     the monotone congruence lemma (Exercise 6.3)
    `OkFwd`, `OkBwd`, `transfer5_fwd`, `transfer5_bwd`
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Transfer

open LO LO.FirstOrder

/-! ### The formulas of the transfer -/

section Formulas

variable {ξ : Type*} {m : ℕ}

/-- `s < t`. -/
def ltW (s t : Semiterm LIinfW ξ m) : Semiformula LIinfW ξ m :=
  Semiformula.rel (Sum.inl Language.LT.lt : LIinfW.Rel 2) ![s, t]

/-- `j < k̄ ∧ Jlev ⊤ (j, a)`: the image of `Q(j,a)` in `A_{k̄}` under `embed`. -/
def qTop (k : ℕ) (j a : Semiterm LIinfW ξ m) : Semiformula LIinfW ξ m :=
  ltW j (Semiterm.numeral k) ⋏ jlevAt ⊤ j a

theorem params_ltW (s t : Semiterm LIinfW ξ m) : params (ltW s t) = ∅ := rfl

theorem params_qTop (k : ℕ) (j a : Semiterm LIinfW ξ m) : params (qTop k j a) = ∅ := by
  simp [qTop, params_ltW, params_jlevAt]

end Formulas

/-- The standard value of `j < k̄`. -/
theorem trueN_ltW (j : SyntacticTerm LIinfW) (k : ℕ) : TrueN (ltW j (numI k)) ↔ termVal j < k := by
  unfold TrueN ltW
  refine (Semiformula.eval_rel (s := stdW) (b := ![]) (f := fun _ => 0)
    (r := (Sum.inl Language.LT.lt : LIinfW.Rel 2)) (v := ![j, numI k])).trans ?_
  have e : (Semiterm.val (s := stdW) ![] (fun _ => 0)) ∘ ![j, numI k] = ![termVal j, k] := by
    funext i
    match i with
    | 0 => rfl
    | 1 => exact val_numI k _ _
  simp only [e]
  show Structure.rel (L := ℒₒᵣ) (Language.LT.lt : Language.Rel ℒₒᵣ 2) ![termVal j, k] ↔
    termVal j < k
  simp

theorem trueLit_ltW {j : SyntacticTerm LIinfW} (hj : j.freeVariables = ∅) {k : ℕ}
    (h : termVal j < k) : TrueLit (ltW j (numI k)) := by
  refine ⟨⟨2, Language.LT.lt, ![j, numI k], Or.inl rfl, fun i => ?_⟩, (trueN_ltW j k).mpr h⟩
  match i with
  | 0 => exact hj
  | 1 => exact numI_freeVariables k

theorem trueLit_nltW {j : SyntacticTerm LIinfW} (hj : j.freeVariables = ∅) {k : ℕ}
    (h : k ≤ termVal j) : TrueLit (∼(ltW j (numI k))) := by
  refine ⟨⟨2, Language.LT.lt, ![j, numI k], Or.inr rfl, fun i => ?_⟩, ?_⟩
  · match i with
    | 0 => exact hj
    | 1 => exact numI_freeVariables k
  · rw [trueN_neg]
    intro hh
    exact absurd ((trueN_ltW j k).mp hh) (by omega)

theorem one_lt_Omega (k : ℕ) : ThetaVNoteD.one < ThetaVNoteD.Omega k :=
  ThetaVNoteD.one_lt_prin (ThetaVTerm.isPrin_Omega k)

/-! ### The identity for `I_k` at height `Ω_{k+1}` -/

section Identity

variable {A : FormJ} {H : Set ThetaVNoteD → Set ThetaVNoteD}

/-- **`⊢ I_k a, ¬I_k a` at height `Ω_{k+1}`, rank `0`, in every nice `H`** (Lemma 6.1 at the stage
atom `I_k a`, `ω · rk (I_k a) = ω · Ω_{k+1} = Ω_{k+1}`). -/
theorem identity_IOmega (hH : ThetaVNoteD.NiceS H) (k : ℕ) {a : SyntacticTerm LIinfW}
    (ha : a.freeVariables = ∅) :
    IDwDerivable A ThetaVNoteD.zero H (ThetaVNoteD.Omega k) [IOmegaAt k a, ∼(IOmegaAt k a)] := by
  have T := taut (A := A) hH (IOmegaAt k a) (freeVariables_IOmegaAt ha k)
  have hZ : Stage.val '' params (IOmegaAt k a) ⊆ H ∅ := by
    rw [params_IOmegaAt, Set.image_singleton]
    exact Set.singleton_subset_iff.mpr (hH.Omega_mem k)
  rw [ThetaVNoteD.adjoin_eq_self hH.1 hZ, rk_IOmegaAt, ThetaVNoteD.omegaMul_Omega] at T
  exact T

end Identity

/-! ### T1, T2: the stage atom and the full `Jlev ⊤` at level `k` -/

section T12

variable {A : FormJ} {H : Set ThetaVNoteD → Set ThetaVNoteD}

/-- The parameters of a sequent all of whose formulas have parameter values in `H(∅)`. -/
theorem paramsVal_subset {Γ : Sequent LIinfW} (h : ∀ φ ∈ Γ, Stage.val '' params φ ⊆ H ∅) :
    paramsVal Γ ⊆ H ∅ := by
  intro x hx
  obtain ⟨s, ⟨χ, hχ, hs⟩, rfl⟩ := hx
  exact h χ hχ ⟨s, hs, rfl⟩

theorem omega_image (hH : ThetaVNoteD.NiceS H) (k : ℕ) {t : SyntacticTerm LIinfW} :
    Stage.val '' params (IOmegaAt k t) ⊆ H ∅ := by
  rw [params_IOmegaAt, Set.image_singleton]
  exact Set.singleton_subset_iff.mpr (hH.Omega_mem k)

theorem omega_image_neg (hH : ThetaVNoteD.NiceS H) (k : ℕ) {t : SyntacticTerm LIinfW} :
    Stage.val '' params (∼(IOmegaAt k t)) ⊆ H ∅ := by
  rw [params_neg]; exact omega_image hH k

theorem nadd_Omega_mem (hH : ThetaVNoteD.NiceS H) (k c : ℕ) :
    ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat c) ∈ H ∅ :=
  hH.nadd_mem (hH.Omega_mem k) (hH.ofNat_mem c)

/-- **T1, general form**: `⊢ ¬Jlev ℓ (s,a), I_k a` for closed `s`, `a`, `val s = k < ℓ`, at height
`Ω_{k+1} ⊕ 1`. -/
theorem njlev_to_stage (hH : ThetaVNoteD.NiceS H) {ℓ : WithTop ℕ} {s a : SyntacticTerm LIinfW}
    (hs : s.freeVariables = ∅) (ha : a.freeVariables = ∅) {k : ℕ} (hk : termVal s = k)
    (hl : (k : WithTop ℕ) < ℓ) :
    IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 1))
      [njlevAt ℓ s a, IOmegaAt k a] := by
  subst hk
  have T := identity_IOmega (A := A) hH (termVal s) ha
  have hP : paramsVal [njlevAt ℓ s a, IOmegaAt (termVal s) a] ⊆ H ∅ :=
    paramsVal_subset fun φ hφ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
      rcases hφ with rfl | rfl
      · rw [params_njlevAt, Set.image_empty]; exact Set.empty_subset _
      · exact omega_image hH _
  refine .njlev (nadd_Omega_mem hH _ 1) hP List.mem_cons_self hs ha
    (fun _ => lt_nadd_ofNat_succ _ 0) fun _ => ?_
  refine T.weaken hH.1 le_rfl ?_ (hH.Omega_mem _) ?_
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto
  · exact paramsVal_subset fun φ hφ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
      rcases hφ with rfl | rfl | rfl
      · exact omega_image_neg hH _
      · rw [params_njlevAt, Set.image_empty]; exact Set.empty_subset _
      · exact omega_image hH _

/-- **T2, general form**: `⊢ ¬I_k a, Jlev ℓ (s,a)` for closed `s`, `a`, `val s = k < ℓ`, at height
`Ω_{k+1} ⊕ 1`. -/
theorem stage_to_jlev (hH : ThetaVNoteD.NiceS H) {ℓ : WithTop ℕ} {s a : SyntacticTerm LIinfW}
    (hs : s.freeVariables = ∅) (ha : a.freeVariables = ∅) {k : ℕ} (hk : termVal s = k)
    (hl : (k : WithTop ℕ) < ℓ) :
    IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 1))
      [∼(IOmegaAt k a), jlevAt ℓ s a] := by
  subst hk
  have T := identity_IOmega (A := A) hH (termVal s) ha
  have hP : paramsVal [∼(IOmegaAt (termVal s) a), jlevAt ℓ s a] ⊆ H ∅ :=
    paramsVal_subset fun φ hφ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
      rcases hφ with rfl | rfl
      · exact omega_image_neg hH _
      · rw [params_jlevAt, Set.image_empty]; exact Set.empty_subset _
  refine .jlev (nadd_Omega_mem hH _ 1) hP (List.mem_cons_of_mem _ List.mem_cons_self) hs ha hl
    (lt_nadd_ofNat_succ _ 0) ?_
  refine T.weaken hH.1 le_rfl ?_ (hH.Omega_mem _) ?_
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto
  · exact paramsVal_subset fun φ hφ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
      rcases hφ with rfl | rfl | rfl
      · exact omega_image hH _
      · exact omega_image_neg hH _
      · rw [params_jlevAt, Set.image_empty]; exact Set.empty_subset _

/-- **T1**: `⊢ ¬Jlev ⊤ (k̄, a), I_k a`, height `Ω_{k+1} ⊕ 1`, rank `0`. -/
theorem transfer1 (hH : ThetaVNoteD.NiceS H) (k : ℕ) {a : SyntacticTerm LIinfW}
    (ha : a.freeVariables = ∅) :
    IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 1))
      [njlevAt ⊤ (numI k) a, IOmegaAt k a] :=
  njlev_to_stage hH (numI_freeVariables k) ha (termVal_numI k) (WithTop.coe_lt_top k)

/-- **T2**: `⊢ ¬I_k a, Jlev ⊤ (k̄, a)`, height `Ω_{k+1} ⊕ 1`, rank `0`. -/
theorem transfer2 (hH : ThetaVNoteD.NiceS H) (k : ℕ) {a : SyntacticTerm LIinfW}
    (ha : a.freeVariables = ∅) :
    IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 1))
      [∼(IOmegaAt k a), jlevAt ⊤ (numI k) a] :=
  stage_to_jlev hH (numI_freeVariables k) ha (termVal_numI k) (WithTop.coe_lt_top k)

end T12

/-! ### T3, T4: `Jlev k` against `j < k̄ ∧ Jlev ⊤` -/

section T34

variable {A : FormJ} {H : Set ThetaVNoteD → Set ThetaVNoteD}

/-- **T3**: `⊢ ¬(j < k̄ ∧ Jlev ⊤ (j,a)), Jlev k (j,a)` for closed `j`, `a`, at height
`Ω_{k+1} ⊕ 4` (independent of `j`), rank `0`. For `val j ≥ k` the left disjunct `¬(j < k̄)` is a
true literal; for `val j < k` the derivation is `(orL)`, `(orR)`, `(njlev)`, `(jlev)` over the
identity for `I_{val j}`. -/
theorem transfer3 (hH : ThetaVNoteD.NiceS H) (k : ℕ) {j a : SyntacticTerm LIinfW}
    (hj : j.freeVariables = ∅) (ha : a.freeVariables = ∅) :
    IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 4))
      [∼(qTop k j a), jlevAt (k : WithTop ℕ) j a] := by
  set φ : Proposition LIinfW := ltW j (numI k) with hφ
  set ψ : Proposition LIinfW := jlevAt ⊤ j a with hψ
  set J : Proposition LIinfW := jlevAt (k : WithTop ℕ) j a with hJ
  have hN : ∼(qTop k j a) = ∼φ ⋎ ∼ψ := by simp [qTop, hφ, hψ]
  rw [hN]
  set N : Proposition LIinfW := ∼φ ⋎ ∼ψ with hNdef
  have hHi : ∀ i : ℕ, ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat i) ∈ H ∅ :=
    fun i => nadd_Omega_mem hH k i
  have hlt : ∀ i i' : ℕ, i < i' → ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat i) <
      ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat i') :=
    fun i i' h => nadd_ofNat_lt_nadd_ofNat' _ h
  have hpar0 : ∀ χ ∈ [N, J], Stage.val '' params χ ⊆ H ∅ := by
    intro χ hχ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
    rcases hχ with rfl | rfl
    · simp [hNdef, hφ, hψ, params_ltW]
    · simp [hJ, params_jlevAt]
  by_cases hv : termVal j < k
  · -- the main case
    set v := termVal j with hvdef
    have T := identity_IOmega (A := A) hH v ha
    have hΩv : ThetaVNoteD.Omega v ≤ ThetaVNoteD.Omega k :=
      (ThetaVNoteD.Omega_lt_Omega_iff.mpr hv).le
    have hvk : (v : WithTop ℕ) < (k : WithTop ℕ) := WithTop.coe_lt_coe.mpr hv
    have hpS : ∀ χ ∈ [∼ψ, ∼φ, N, J, IOmegaAt v a, ∼(IOmegaAt v a)],
        Stage.val '' params χ ⊆ H ∅ := by
      intro χ hχ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
      rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [hψ]
      · simp [hφ, params_ltW]
      · simp [hNdef, hφ, hψ, params_ltW]
      · simp [hJ, params_jlevAt]
      · exact omega_image hH v
      · exact omega_image_neg hH v
    have hpsub : ∀ Δ : Sequent LIinfW, Δ ⊆ [∼ψ, ∼φ, N, J, IOmegaAt v a, ∼(IOmegaAt v a)] →
        paramsVal Δ ⊆ H ∅ := fun Δ hΔ => paramsVal_subset fun χ hχ => hpS χ (hΔ hχ)
    -- the identity, at height `Ω_{k+1} ⊕ 0`
    have d0 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 0))
        (IOmegaAt v a :: ∼(IOmegaAt v a) :: [∼ψ, ∼φ, N, J]) := by
      refine T.weaken hH.1 ?_ ?_ (hHi 0) (hpsub _ ?_)
      · rw [ThetaVNoteD.ofNat_zero, ThetaVNoteD.nadd_zero]; exact hΩv
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto
    have d1 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 1))
        (∼(IOmegaAt v a) :: [∼ψ, ∼φ, N, J]) :=
      .jlev (hHi 1) (hpsub _ (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto))
        (by simp [hJ]) hj ha hvk (hlt 0 1 (by omega)) d0
    have d2 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 2))
        [∼ψ, ∼φ, N, J] :=
      .njlev (ℓ := ⊤) (hHi 2) (hpsub _ (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto))
        (List.mem_cons_self : ∼ψ ∈ _) hj ha (fun _ => hlt 1 2 (by omega)) (fun _ => d1)
    have d3 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 3))
        [∼φ, N, J] :=
      .orR (φ := ∼φ) (ψ := ∼ψ) (hHi 3) (hpsub _ (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto))
        (List.mem_cons_of_mem _ List.mem_cons_self : N ∈ _)
        (lt_of_lt_of_le (one_lt_Omega k) (ThetaVNoteD.le_nadd_left _ _))
        (hlt 2 3 (by omega)) d2
    exact .orL (hHi 4) (paramsVal_subset hpar0) List.mem_cons_self (hlt 3 4 (by omega)) d3
  · -- `val j ≥ k`: `¬(j < k̄)` is a true literal
    have hl := trueLit_nltW hj (le_of_not_gt hv)
    have d3 : IDwDerivable A ThetaVNoteD.zero H ThetaVNoteD.zero [∼φ, N, J] :=
      .literal (hH.zero_mem) (paramsVal_subset fun χ hχ => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl | rfl
        · simp [hφ, params_ltW]
        · exact hpar0 _ (by simp)
        · exact hpar0 _ (by simp)) hl List.mem_cons_self
    exact .orL (hHi 4) (paramsVal_subset hpar0) List.mem_cons_self
      (lt_of_lt_of_le (ThetaVNoteD.zero_lt_Omega k) (ThetaVNoteD.le_nadd_left _ _)) d3

/-- **T4**: `⊢ ¬Jlev k (j,a), j < k̄ ∧ Jlev ⊤ (j,a)` for closed `j`, `a`, at height `Ω_{k+1} ⊕ 3`
(independent of `j`), rank `0`. For `val j ≥ k` the rule (njlev) has no premise; for `val j < k` it
has the premise `¬I_{val j} a`, and `(∧)` splits the conclusion into the true literal `j < k̄` and
`Jlev ⊤ (j,a)`, by `(jlev)` over the identity for `I_{val j}`. -/
theorem transfer4 (hH : ThetaVNoteD.NiceS H) (k : ℕ) {j a : SyntacticTerm LIinfW}
    (hj : j.freeVariables = ∅) (ha : a.freeVariables = ∅) :
    IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 3))
      [njlevAt (k : WithTop ℕ) j a, qTop k j a] := by
  set φ : Proposition LIinfW := ltW j (numI k) with hφ
  set ψ : Proposition LIinfW := jlevAt ⊤ j a with hψ
  have hHi : ∀ i : ℕ, ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat i) ∈ H ∅ :=
    fun i => nadd_Omega_mem hH k i
  have hlt : ∀ i i' : ℕ, i < i' → ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat i) <
      ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat i') :=
    fun i i' h => nadd_ofNat_lt_nadd_ofNat' _ h
  have hpQ : Stage.val '' params (qTop k j a) ⊆ H ∅ := by simp [params_qTop]
  have hQeq : qTop k j a = φ ⋏ ψ := rfl
  generalize qTop k j a = Q at hpQ hQeq ⊢
  have hpN : Stage.val '' params (njlevAt (k : WithTop ℕ) j a) ⊆ H ∅ := by simp [params_njlevAt]
  by_cases hv : termVal j < k
  · set v := termVal j with hvdef
    have T := identity_IOmega (A := A) hH v ha
    have hΩv : ThetaVNoteD.Omega v ≤ ThetaVNoteD.Omega k :=
      (ThetaVNoteD.Omega_lt_Omega_iff.mpr hv).le
    have hpS : ∀ χ ∈ [φ, ψ, ∼(IOmegaAt v a), njlevAt (k : WithTop ℕ) j a, Q, IOmegaAt v a],
        Stage.val '' params χ ⊆ H ∅ := by
      intro χ hχ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
      rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [hφ, params_ltW]
      · simp [hψ]
      · exact omega_image_neg hH v
      · exact hpN
      · exact hpQ
      · exact omega_image hH v
    have hpsub : ∀ Δ : Sequent LIinfW,
        Δ ⊆ [φ, ψ, ∼(IOmegaAt v a), njlevAt (k : WithTop ℕ) j a, Q, IOmegaAt v a] →
        paramsVal Δ ⊆ H ∅ := fun Δ hΔ => paramsVal_subset fun χ hχ => hpS χ (hΔ hχ)
    have hsub : ∀ Δ : Sequent LIinfW, ∀ Δ' : Sequent LIinfW,
        (∀ x ∈ Δ, x ∈ Δ') → Δ' ⊆ [φ, ψ, ∼(IOmegaAt v a), njlevAt (k : WithTop ℕ) j a, Q,
          IOmegaAt v a] → paramsVal Δ ⊆ H ∅ := fun Δ Δ' h1 h2 => paramsVal_subset fun χ hχ => hpS χ (h2 (h1 _ hχ))
    have hvk : (v : WithTop ℕ) < (k : WithTop ℕ) := WithTop.coe_lt_coe.mpr hv
    have d0 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 0))
        (IOmegaAt v a :: ψ :: ∼(IOmegaAt v a) :: [njlevAt (k : WithTop ℕ) j a, Q]) := by
      refine T.weaken hH.1 ?_ ?_ (hHi 0) (hpsub _ ?_)
      · rw [ThetaVNoteD.ofNat_zero, ThetaVNoteD.nadd_zero]; exact hΩv
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto
    have dψ : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 1))
        (ψ :: ∼(IOmegaAt v a) :: [njlevAt (k : WithTop ℕ) j a, Q]) :=
      .jlev (hHi 1) (hpsub _ (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto))
        List.mem_cons_self hj ha (WithTop.coe_lt_top v) (hlt 0 1 (by omega)) d0
    have dφ : IDwDerivable A ThetaVNoteD.zero H ThetaVNoteD.zero
        (φ :: ∼(IOmegaAt v a) :: [njlevAt (k : WithTop ℕ) j a, Q]) :=
      .literal hH.zero_mem (hpsub _ (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto))
        (trueLit_ltW hj hv) List.mem_cons_self
    have dQ : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 2))
        (∼(IOmegaAt v a) :: [njlevAt (k : WithTop ℕ) j a, Q]) :=
      .and (φ := φ) (ψ := ψ) (hHi 2)
        (hpsub _ (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto))
        (by rw [← hQeq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (lt_of_lt_of_le (ThetaVNoteD.zero_lt_Omega k) (ThetaVNoteD.le_nadd_left _ _))
        (hlt 1 2 (by omega)) dφ dψ
    exact .njlev (ℓ := (k : WithTop ℕ)) (s := j) (t := a) (α₀ := ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 2))
      (hHi 3)
      (hpsub [njlevAt (k : WithTop ℕ) j a, Q]
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl <;> simp))
      List.mem_cons_self hj ha (fun _ => hlt 2 3 (by omega)) (fun _ => dQ)
  · exact .njlev (α₀ := ThetaVNoteD.zero) (hHi 3)
      (paramsVal_subset fun χ hχ => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
        rcases hχ with rfl | rfl
        · exact hpN
        · exact hpQ)
      List.mem_cons_self hj ha (fun h => absurd (WithTop.coe_lt_coe.mp h) hv)
      (fun h => absurd (WithTop.coe_lt_coe.mp h) hv)

end T34

/-! ### T5: the monotone congruence lemma (Freund, Exercise 6.3, in atom-generic form)

`Cong Ok c B B'` says that the closed formula `B'` arises from the closed formula `B` by replacing
atoms (`Ok`-related pairs) while keeping the connectives and quantifiers (the ω-rule: for `∀`, `∃`
the relation is required at every numeral instance, so no commutation of the replacement with
substitution has to be proved here).  If `⊢ ¬a, b` for every `Ok`-pair, then `⊢ ¬B, B'` at the
height `α ⊕ 2c`: the induction is that of `IDn`'s `ex63`, with the atom case the hypothesis.
Instantiated with `OkFwd`/`OkBwd` below it moves T1-T4 through a formula. -/

section T5

variable {A : FormJ} {H : Set ThetaVNoteD → Set ThetaVNoteD}

/-- The congruence relation of the monotone plugging lemma; `c` bounds the number of connectives
and quantifiers along a branch. -/
inductive Cong (Ok : Proposition LIinfW → Proposition LIinfW → Prop) :
    ℕ → Proposition LIinfW → Proposition LIinfW → Prop
  | atom {B B' : Proposition LIinfW} : Ok B B' → Cong Ok 0 B B'
  | verum : Cong Ok 0 ⊤ ⊤
  | falsum : Cong Ok 0 ⊥ ⊥
  | and {c₀ c₁ : ℕ} {B₀ B₁ B₀' B₁' : Proposition LIinfW} :
      Cong Ok c₀ B₀ B₀' → Cong Ok c₁ B₁ B₁' →
      Cong Ok (max c₀ c₁ + 1) (B₀ ⋏ B₁) (B₀' ⋏ B₁')
  | or {c₀ c₁ : ℕ} {B₀ B₁ B₀' B₁' : Proposition LIinfW} :
      Cong Ok c₀ B₀ B₀' → Cong Ok c₁ B₁ B₁' →
      Cong Ok (max c₀ c₁ + 1) (B₀ ⋎ B₁) (B₀' ⋎ B₁')
  | all {c : ℕ} {φ φ' : Semiproposition LIinfW 1} :
      (∀ m : ℕ, Cong Ok c (φ/[numI m]) (φ'/[numI m])) → Cong Ok (c + 1) (∀¹ φ) (∀¹ φ')
  | exs {c : ℕ} {φ φ' : Semiproposition LIinfW 1} :
      (∀ m : ℕ, Cong Ok c (φ/[numI m]) (φ'/[numI m])) → Cong Ok (c + 1) (∃¹ φ) (∃¹ φ')

/-- **T5, generic form.** If `⊢^α ¬a, b, Γ` for every `Ok`-related pair (with parameters in
`H(∅)`), then `⊢^{α ⊕ 2c} ¬B, B', Γ` whenever `Cong Ok c B B'` (and `B`, `B'` have parameters in
`H(∅)`).  `α` must exceed every numeral and `1` (as in `ex63`: `ω ⪯ α`), so that the witnesses
of (exs) and the second disjunct of (orR) are admissible. -/
theorem cong_derivable (hH : ThetaVNoteD.NiceS H) {α : ThetaVNoteD} (hα : α ∈ H ∅)
    (hone : ThetaVNoteD.one < α) (hnum : ∀ m : ℕ, ThetaVNoteD.ofNat m < α)
    {Ok : Proposition LIinfW → Proposition LIinfW → Prop} {Γ : Sequent LIinfW}
    (hΓ : paramsVal Γ ⊆ H ∅)
    (hOk : ∀ B B' : Proposition LIinfW, Ok B B' → Stage.val '' params B ⊆ H ∅ →
      Stage.val '' params B' ⊆ H ∅ → IDwDerivable A ThetaVNoteD.zero H α (∼B :: B' :: Γ)) :
    ∀ {c : ℕ} {B B' : Proposition LIinfW}, Cong Ok c B B' →
      Stage.val '' params B ⊆ H ∅ → Stage.val '' params B' ⊆ H ∅ →
      IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd α (ThetaVNoteD.ofNat (2 * c))) (∼B :: B' :: Γ) := by
  have hmem : ∀ j : ℕ, ThetaVNoteD.nadd α (ThetaVNoteD.ofNat j) ∈ H ∅ := fun j =>
    hH.nadd_mem hα (hH.ofNat_mem j)
  have hlt : ∀ i j : ℕ, i < j → ThetaVNoteD.nadd α (ThetaVNoteD.ofNat i) <
      ThetaVNoteD.nadd α (ThetaVNoteD.ofNat j) := fun i j h => nadd_ofNat_lt_nadd_ofNat' _ h
  have hone' : ∀ j : ℕ, ThetaVNoteD.one < ThetaVNoteD.nadd α (ThetaVNoteD.ofNat j) := fun j =>
    lt_of_lt_of_le hone (ThetaVNoteD.le_nadd_left _ _)
  have hnum' : ∀ m j : ℕ, ThetaVNoteD.ofNat m < ThetaVNoteD.nadd α (ThetaVNoteD.ofNat j) :=
    fun m j => lt_of_lt_of_le (hnum m) (ThetaVNoteD.le_nadd_left _ _)
  have plΓ : ∀ χ ∈ Γ, Stage.val '' params χ ⊆ H ∅ := fun χ hχ =>
    (Set.image_mono (params_subset_paramsList hχ) (f := Stage.val)).trans hΓ
  -- the parameters of the sequents that occur
  have pseq : ∀ B B' : Proposition LIinfW, Stage.val '' params B ⊆ H ∅ →
      Stage.val '' params B' ⊆ H ∅ → paramsVal (∼B :: B' :: Γ) ⊆ H ∅ := by
    intro B B' hB hB'
    rw [paramsVal_cons, paramsVal_cons, params_neg]
    exact Set.union_subset hB (Set.union_subset hB' hΓ)
  intro c B B' hC
  induction hC with
  | atom h =>
    intro hp hp'
    rw [Nat.mul_zero, ThetaVNoteD.ofNat_zero, ThetaVNoteD.nadd_zero]
    exact hOk _ _ h hp hp'
  | verum =>
    intro hp hp'
    exact .verum (hmem _) (pseq _ _ hp hp') (List.mem_cons_of_mem _ List.mem_cons_self)
  | falsum =>
    intro hp hp'
    exact .verum (hmem _) (pseq _ _ hp hp') List.mem_cons_self
  | and h0 h1 ih0 ih1 =>
    rename_i c₀ c₁ B₀ B₁ B₀' B₁'
    intro hp hp'
    rw [params_and, Set.image_union] at hp hp'
    have hp0 : Stage.val '' params B₀ ⊆ H ∅ := Set.subset_union_left.trans hp
    have hp1 : Stage.val '' params B₁ ⊆ H ∅ := Set.subset_union_right.trans hp
    have hq0 : Stage.val '' params B₀' ⊆ H ∅ := Set.subset_union_left.trans hp'
    have hq1 : Stage.val '' params B₁' ⊆ H ∅ := Set.subset_union_right.trans hp'
    have eX : ∼(B₀ ⋏ B₁) = ∼B₀ ⋎ ∼B₁ := by simp
    have hpo : Stage.val '' params (∼B₀ ⋎ ∼B₁) ⊆ H ∅ := by
      rw [params_or, params_neg, params_neg, Set.image_union]; exact hp
    have hpa : Stage.val '' params (B₀' ⋏ B₁') ⊆ H ∅ := by
      rw [params_and, Set.image_union]; exact hp'
    rw [eX]
    have hP : paramsVal ((∼B₀ ⋎ ∼B₁) :: (B₀' ⋏ B₁') :: Γ) ⊆ H ∅ := by
      rw [paramsVal_cons, paramsVal_cons]; exact Set.union_subset hpo (Set.union_subset hpa hΓ)
    have step : ∀ (Xi Yi : Proposition LIinfW), Stage.val '' params Xi ⊆ H ∅ →
        Stage.val '' params Yi ⊆ H ∅ → ∀ h : ThetaVNoteD,
        IDwDerivable A ThetaVNoteD.zero H h (∼Xi :: Yi :: Γ) →
        IDwDerivable A ThetaVNoteD.zero H h
          (∼Xi :: Yi :: (∼B₀ ⋎ ∼B₁) :: (B₀' ⋏ B₁') :: Γ) := by
      intro Xi Yi hXi hYi h d
      refine d.weaken_seq hH.1 (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        tauto) ?_
      refine paramsVal_subset fun χ hχ => ?_
      simp only [List.mem_cons] at hχ
      rcases hχ with rfl | rfl | rfl | rfl | hχ
      · rw [params_neg]; exact hXi
      · exact hYi
      · exact hpo
      · exact hpa
      · exact plΓ χ hχ
    have d0 := step B₀ B₀' hp0 hq0 _ (ih0 hp0 hq0)
    have d1 := step B₁ B₁' hp1 hq1 _ (ih1 hp1 hq1)
    have pY : ∀ Yi : Proposition LIinfW, Stage.val '' params Yi ⊆ H ∅ →
        paramsVal (Yi :: (∼B₀ ⋎ ∼B₁) :: (B₀' ⋏ B₁') :: Γ) ⊆ H ∅ := by
      intro Yi hYi
      rw [paramsVal_cons]; exact Set.union_subset hYi hP
    have e0 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd α (ThetaVNoteD.ofNat (2 * c₀ + 1)))
        (B₀' :: (∼B₀ ⋎ ∼B₁) :: (B₀' ⋏ B₁') :: Γ) :=
      .orL (hmem _) (pY B₀' hq0) (List.mem_cons_of_mem _ List.mem_cons_self)
        (hlt _ _ (by omega)) d0
    have e1 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd α (ThetaVNoteD.ofNat (2 * c₁ + 1)))
        (B₁' :: (∼B₀ ⋎ ∼B₁) :: (B₀' ⋏ B₁') :: Γ) :=
      .orR (hmem _) (pY B₁' hq1) (List.mem_cons_of_mem _ List.mem_cons_self) (hone' _)
        (hlt _ _ (by omega)) d1
    exact .and (hmem _) hP (List.mem_cons_of_mem _ List.mem_cons_self)
      (hlt _ _ (by omega)) (hlt _ _ (by omega)) e0 e1
  | or h0 h1 ih0 ih1 =>
    rename_i c₀ c₁ B₀ B₁ B₀' B₁'
    intro hp hp'
    rw [params_or, Set.image_union] at hp hp'
    have hp0 : Stage.val '' params B₀ ⊆ H ∅ := Set.subset_union_left.trans hp
    have hp1 : Stage.val '' params B₁ ⊆ H ∅ := Set.subset_union_right.trans hp
    have hq0 : Stage.val '' params B₀' ⊆ H ∅ := Set.subset_union_left.trans hp'
    have hq1 : Stage.val '' params B₁' ⊆ H ∅ := Set.subset_union_right.trans hp'
    have eX : ∼(B₀ ⋎ B₁) = ∼B₀ ⋏ ∼B₁ := by simp
    have hpa : Stage.val '' params (∼B₀ ⋏ ∼B₁) ⊆ H ∅ := by
      rw [params_and, params_neg, params_neg, Set.image_union]; exact hp
    have hpo : Stage.val '' params (B₀' ⋎ B₁') ⊆ H ∅ := by
      rw [params_or, Set.image_union]; exact hp'
    rw [eX]
    have hP : paramsVal ((∼B₀ ⋏ ∼B₁) :: (B₀' ⋎ B₁') :: Γ) ⊆ H ∅ := by
      rw [paramsVal_cons, paramsVal_cons]; exact Set.union_subset hpa (Set.union_subset hpo hΓ)
    have step : ∀ (Xi Yi : Proposition LIinfW), Stage.val '' params Xi ⊆ H ∅ →
        Stage.val '' params Yi ⊆ H ∅ → ∀ h : ThetaVNoteD,
        IDwDerivable A ThetaVNoteD.zero H h (∼Xi :: Yi :: Γ) →
        IDwDerivable A ThetaVNoteD.zero H h
          (Yi :: ∼Xi :: (∼B₀ ⋏ ∼B₁) :: (B₀' ⋎ B₁') :: Γ) := by
      intro Xi Yi hXi hYi h d
      refine d.weaken_seq hH.1 (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        tauto) ?_
      refine paramsVal_subset fun χ hχ => ?_
      simp only [List.mem_cons] at hχ
      rcases hχ with rfl | rfl | rfl | rfl | hχ
      · exact hYi
      · rw [params_neg]; exact hXi
      · exact hpa
      · exact hpo
      · exact plΓ χ hχ
    have d0 := step B₀ B₀' hp0 hq0 _ (ih0 hp0 hq0)
    have d1 := step B₁ B₁' hp1 hq1 _ (ih1 hp1 hq1)
    have pX : ∀ Xi : Proposition LIinfW, Stage.val '' params Xi ⊆ H ∅ →
        paramsVal (∼Xi :: (∼B₀ ⋏ ∼B₁) :: (B₀' ⋎ B₁') :: Γ) ⊆ H ∅ := by
      intro Xi hXi
      rw [paramsVal_cons, params_neg]; exact Set.union_subset hXi hP
    have e0 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd α (ThetaVNoteD.ofNat (2 * c₀ + 1)))
        (∼B₀ :: (∼B₀ ⋏ ∼B₁) :: (B₀' ⋎ B₁') :: Γ) :=
      .orL (hmem _) (pX B₀ hp0)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (hlt _ _ (by omega)) d0
    have e1 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd α (ThetaVNoteD.ofNat (2 * c₁ + 1)))
        (∼B₁ :: (∼B₀ ⋏ ∼B₁) :: (B₀' ⋎ B₁') :: Γ) :=
      .orR (hmem _) (pX B₁ hp1)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (hone' _)
        (hlt _ _ (by omega)) d1
    exact .and (hmem _) hP List.mem_cons_self (hlt _ _ (by omega)) (hlt _ _ (by omega)) e0 e1
  | all h ih =>
    rename_i c φ φ'
    intro hp hp'
    rw [params_all] at hp hp'
    have eX : ∼(∀¹ φ) = ∃¹ (∼φ) := by simp
    rw [eX]
    have hpe : Stage.val '' params (∃¹ (∼φ)) ⊆ H ∅ := by rw [params_exs, params_neg]; exact hp
    have hpu : Stage.val '' params (∀¹ φ') ⊆ H ∅ := by rw [params_all]; exact hp'
    have hP : paramsVal ((∃¹ (∼φ)) :: (∀¹ φ') :: Γ) ⊆ H ∅ := by
      rw [paramsVal_cons, paramsVal_cons]
      exact Set.union_subset hpe (Set.union_subset hpu hΓ)
    refine .all (φ := φ') (fun _ => ThetaVNoteD.nadd α (ThetaVNoteD.ofNat (2 * c + 1)))
      (hmem _) hP (List.mem_cons_of_mem _ List.mem_cons_self)
      (fun _ => hlt _ _ (by omega)) (fun m' => ?_)
    have hpn : Stage.val '' params (φ/[numI m']) ⊆ H ∅ := by rw [params_subst1]; exact hp
    have hqn : Stage.val '' params (φ'/[numI m']) ⊆ H ∅ := by rw [params_subst1]; exact hp'
    have d := ih m' hpn hqn
    have hneg : (∼φ)/[numI m'] = ∼(φ/[numI m']) := by simp
    refine .exs (α₀ := ThetaVNoteD.nadd α (ThetaVNoteD.ofNat (2 * c))) m' (hmem _) ?_
      (List.mem_cons_of_mem _ List.mem_cons_self) (hnum' _ _) (hlt _ _ (by omega)) ?_
    · rw [paramsVal_cons]
      exact Set.union_subset hqn hP
    · rw [hneg]
      refine d.weaken_seq hH.1 (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        tauto) ?_
      refine paramsVal_subset fun χ hχ => ?_
      simp only [List.mem_cons] at hχ
      rcases hχ with rfl | rfl | rfl | rfl | hχ
      · rw [params_neg]; exact hpn
      · exact hqn
      · exact hpe
      · exact hpu
      · exact plΓ χ hχ
  | exs h ih =>
    rename_i c φ φ'
    intro hp hp'
    rw [params_exs] at hp hp'
    have eX : ∼(∃¹ φ) = ∀¹ (∼φ) := by simp
    rw [eX]
    have hpu : Stage.val '' params (∀¹ (∼φ)) ⊆ H ∅ := by rw [params_all, params_neg]; exact hp
    have hpe : Stage.val '' params (∃¹ φ') ⊆ H ∅ := by rw [params_exs]; exact hp'
    have hP : paramsVal ((∀¹ (∼φ)) :: (∃¹ φ') :: Γ) ⊆ H ∅ := by
      rw [paramsVal_cons, paramsVal_cons]
      exact Set.union_subset hpu (Set.union_subset hpe hΓ)
    refine .all (φ := ∼φ) (fun _ => ThetaVNoteD.nadd α (ThetaVNoteD.ofNat (2 * c + 1)))
      (hmem _) hP List.mem_cons_self
      (fun _ => hlt _ _ (by omega)) (fun m' => ?_)
    have hpn : Stage.val '' params (φ/[numI m']) ⊆ H ∅ := by rw [params_subst1]; exact hp
    have hqn : Stage.val '' params (φ'/[numI m']) ⊆ H ∅ := by rw [params_subst1]; exact hp'
    have d := ih m' hpn hqn
    have hneg : (∼φ)/[numI m'] = ∼(φ/[numI m']) := by simp
    rw [hneg]
    refine .exs (α₀ := ThetaVNoteD.nadd α (ThetaVNoteD.ofNat (2 * c))) m' (hmem _) ?_
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (hnum' _ _) (hlt _ _ (by omega)) ?_
    · rw [paramsVal_cons, params_neg]
      exact Set.union_subset hpn hP
    · refine d.weaken_seq hH.1 (List.cons_subset.mpr ⟨List.mem_cons_of_mem _ List.mem_cons_self,
        List.cons_subset.mpr ⟨List.mem_cons_self, fun x hx => List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))⟩⟩) ?_
      refine paramsVal_subset fun χ hχ => ?_
      simp only [List.mem_cons] at hχ
      rcases hχ with rfl | rfl | rfl | rfl | hχ
      · exact hqn
      · rw [params_neg]; exact hpn
      · exact hpu
      · exact hpe
      · exact plΓ χ hχ

/-! #### T1-T4 through a formula -/

/-- **The atom pairs of the transfer from level `k` to `Jlev ⊤`** (source: `A_k(t; I_k, Jlev k)`,
target: the embedded `A_{k̄}(t; Jlev ⊤ (k̄,·), j < k̄ ∧ Jlev ⊤ (j,·))`): an arithmetic literal is
its own image, `I_k s ↦ Jlev ⊤ (k̄, s)`, `Jlev k (j,a) ↦ j < k̄ ∧ Jlev ⊤ (j,a)` and
`¬Jlev k (j,a) ↦ ¬(j < k̄ ∧ Jlev ⊤ (j,a))`. (`I_k` occurs only positively: `PositiveP`.) -/
def OkFwd (k : ℕ) (B B' : Proposition LIinfW) : Prop :=
  (IsArithLit B ∧ B' = B) ∨
  (∃ s : SyntacticTerm LIinfW, s.freeVariables = ∅ ∧ B = IOmegaAt k s ∧
    B' = jlevAt ⊤ (numI k) s) ∨
  (∃ j a : SyntacticTerm LIinfW, j.freeVariables = ∅ ∧ a.freeVariables = ∅ ∧
    B = jlevAt (k : WithTop ℕ) j a ∧ B' = qTop k j a) ∨
  (∃ j a : SyntacticTerm LIinfW, j.freeVariables = ∅ ∧ a.freeVariables = ∅ ∧
    B = njlevAt (k : WithTop ℕ) j a ∧ B' = ∼(qTop k j a))

/-- **The atom pairs of the transfer from `Jlev ⊤` back to level `k`** (the converse of `OkFwd`). -/
def OkBwd (k : ℕ) (B B' : Proposition LIinfW) : Prop :=
  (IsArithLit B ∧ B' = B) ∨
  (∃ s : SyntacticTerm LIinfW, s.freeVariables = ∅ ∧ B = jlevAt ⊤ (numI k) s ∧
    B' = IOmegaAt k s) ∨
  (∃ j a : SyntacticTerm LIinfW, j.freeVariables = ∅ ∧ a.freeVariables = ∅ ∧
    B = qTop k j a ∧ B' = jlevAt (k : WithTop ℕ) j a) ∨
  (∃ j a : SyntacticTerm LIinfW, j.freeVariables = ∅ ∧ a.freeVariables = ∅ ∧
    B = ∼(qTop k j a) ∧ B' = njlevAt (k : WithTop ℕ) j a)

/-- An arithmetic literal implies itself, at any height in `H(∅)`. -/
theorem arith_identity {α : ThetaVNoteD} (hα : α ∈ H ∅)
    {Γ : Sequent LIinfW} {B : Proposition LIinfW} (hl : IsArithLit B)
    (hP : paramsVal (∼B :: B :: Γ) ⊆ H ∅) :
    IDwDerivable A ThetaVNoteD.zero H α (∼B :: B :: Γ) := by
  by_cases ht : TrueN B
  · exact .literal hα hP ⟨hl, ht⟩ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact .literal hα hP ⟨hl.neg, (trueN_neg _).mpr ht⟩ List.mem_cons_self

theorem nadd_Omega_le (k : ℕ) {i c : ℕ} (h : i ≤ c) :
    ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat i) ≤
      ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat c) :=
  ThetaVNoteD.nadd_le_nadd_right _ (ThetaVNoteD.ofNat_le_ofNat h)

/-- Every atom pair of `OkFwd k` is derivable at height `Ω_{k+1} ⊕ 4` (T1-T4 and identity). -/
theorem okFwd_derivable (hH : ThetaVNoteD.NiceS H) (k : ℕ) {Γ : Sequent LIinfW}
    (hΓ : paramsVal Γ ⊆ H ∅) (B B' : Proposition LIinfW) (h : OkFwd k B B')
    (hp : Stage.val '' params B ⊆ H ∅) (hp' : Stage.val '' params B' ⊆ H ∅) :
    IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 4)) (∼B :: B' :: Γ) := by
  have hα := nadd_Omega_mem hH k 4
  have hP : paramsVal (∼B :: B' :: Γ) ⊆ H ∅ := by
    rw [paramsVal_cons, paramsVal_cons, params_neg]
    exact Set.union_subset hp (Set.union_subset hp' hΓ)
  rcases h with ⟨hl, rfl⟩ | ⟨s, hs, rfl, rfl⟩ | ⟨j, a, hj, ha, rfl, rfl⟩ | ⟨j, a, hj, ha, rfl, rfl⟩
  · exact arith_identity hα hl hP
  · exact (transfer2 hH k hs).weaken hH.1 (nadd_Omega_le k (by omega))
      (List.cons_subset.mpr ⟨List.mem_cons_self, List.cons_subset.mpr
        ⟨List.mem_cons_of_mem _ List.mem_cons_self, List.nil_subset _⟩⟩) hα hP
  · exact (transfer4 hH k hj ha).weaken hH.1 (nadd_Omega_le k (by omega))
      (List.cons_subset.mpr ⟨List.mem_cons_self, List.cons_subset.mpr
        ⟨List.mem_cons_of_mem _ List.mem_cons_self, List.nil_subset _⟩⟩) hα hP
  · exact (transfer3 hH k hj ha).weaken hH.1 (nadd_Omega_le k (by omega))
      (List.cons_subset.mpr ⟨List.mem_cons_of_mem _ List.mem_cons_self, List.cons_subset.mpr
        ⟨List.mem_cons_self, List.nil_subset _⟩⟩) hα hP

/-- Every atom pair of `OkBwd k` is derivable at height `Ω_{k+1} ⊕ 4` (T1-T4 and identity). -/
theorem okBwd_derivable (hH : ThetaVNoteD.NiceS H) (k : ℕ) {Γ : Sequent LIinfW}
    (hΓ : paramsVal Γ ⊆ H ∅) (B B' : Proposition LIinfW) (h : OkBwd k B B')
    (hp : Stage.val '' params B ⊆ H ∅) (hp' : Stage.val '' params B' ⊆ H ∅) :
    IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 4)) (∼B :: B' :: Γ) := by
  have hα := nadd_Omega_mem hH k 4
  have hP : paramsVal (∼B :: B' :: Γ) ⊆ H ∅ := by
    rw [paramsVal_cons, paramsVal_cons, params_neg]
    exact Set.union_subset hp (Set.union_subset hp' hΓ)
  rcases h with ⟨hl, rfl⟩ | ⟨s, hs, rfl, rfl⟩ | ⟨j, a, hj, ha, rfl, rfl⟩ | ⟨j, a, hj, ha, rfl, rfl⟩
  · exact arith_identity hα hl hP
  · exact (transfer1 hH k hs).weaken hH.1 (nadd_Omega_le k (by omega))
      (List.cons_subset.mpr ⟨List.mem_cons_self, List.cons_subset.mpr
        ⟨List.mem_cons_of_mem _ List.mem_cons_self, List.nil_subset _⟩⟩) hα hP
  · exact (transfer3 hH k hj ha).weaken hH.1 (nadd_Omega_le k (by omega))
      (List.cons_subset.mpr ⟨List.mem_cons_self, List.cons_subset.mpr
        ⟨List.mem_cons_of_mem _ List.mem_cons_self, List.nil_subset _⟩⟩) hα hP
  · exact (transfer4 hH k hj ha).weaken hH.1 (nadd_Omega_le k (by omega))
      (List.cons_subset.mpr ⟨List.mem_cons_of_mem _ List.mem_cons_self, List.cons_subset.mpr
        ⟨List.mem_cons_self, List.nil_subset _⟩⟩) hα hP

theorem cong_numerals (k : ℕ) (m : ℕ) :
    ThetaVNoteD.ofNat m < ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat 4) :=
  lt_of_lt_of_le (ThetaVNoteD.ofNat_lt_prin (ThetaVTerm.isPrin_Omega k) m)
    (ThetaVNoteD.le_nadd_left _ _)

/-- **T5 (forward)**: if `Cong (OkFwd k) c B B'` then `⊢ ¬B, B', Γ` at height `Ω_{k+1} ⊕ (4 + 2c)`,
rank `0`, in every nice `H`.  `c` is the number of connectives and quantifiers of `B` along a
branch, hence independent of `k`. -/
theorem transfer5_fwd (hH : ThetaVNoteD.NiceS H) (k : ℕ) {Γ : Sequent LIinfW}
    (hΓ : paramsVal Γ ⊆ H ∅) {c : ℕ} {B B' : Proposition LIinfW} (hC : Cong (OkFwd k) c B B')
    (hp : Stage.val '' params B ⊆ H ∅) (hp' : Stage.val '' params B' ⊆ H ∅) :
    IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat (4 + 2 * c))) (∼B :: B' :: Γ) := by
  have := cong_derivable (A := A) hH (nadd_Omega_mem hH k 4)
    (lt_of_lt_of_le (one_lt_Omega k) (ThetaVNoteD.le_nadd_left _ _)) (cong_numerals k) hΓ
    (okFwd_derivable hH k hΓ) hC hp hp'
  rwa [nadd_nadd_ofNat] at this

/-- **T5 (backward)**: the same for `OkBwd k`. -/
theorem transfer5_bwd (hH : ThetaVNoteD.NiceS H) (k : ℕ) {Γ : Sequent LIinfW}
    (hΓ : paramsVal Γ ⊆ H ∅) {c : ℕ} {B B' : Proposition LIinfW} (hC : Cong (OkBwd k) c B B')
    (hp : Stage.val '' params B ⊆ H ∅) (hp' : Stage.val '' params B' ⊆ H ∅) :
    IDwDerivable A ThetaVNoteD.zero H
      (ThetaVNoteD.nadd (ThetaVNoteD.Omega k) (ThetaVNoteD.ofNat (4 + 2 * c))) (∼B :: B' :: Γ) := by
  have := cong_derivable (A := A) hH (nadd_Omega_mem hH k 4)
    (lt_of_lt_of_le (one_lt_Omega k) (ThetaVNoteD.le_nadd_left _ _)) (cong_numerals k) hΓ
    (okBwd_derivable hH k hΓ) hC hp hp'
  rwa [nadd_nadd_ofNat] at this

end T5



/-! ### Concrete instances (smoke): the trivial form `⊤`, the nice operator `HopS 0` -/

section Smoke

/-- T1 at `k = 0`: `⊢ ¬Jlev ⊤ (0̄, 0̄), I_0 0̄`. -/
example : IDwDerivable (⊤ : FormJ) ThetaVNoteD.zero (ThetaVNoteD.HopS ThetaVNoteD.zero)
    (ThetaVNoteD.nadd (ThetaVNoteD.Omega 0) (ThetaVNoteD.ofNat 1))
    [njlevAt ⊤ (numI 0) (numI 0), IOmegaAt 0 (numI 0)] :=
  transfer1 (ThetaVNoteD.HopS_nice _) 0 (numI_freeVariables 0)

/-- T2 at `k = 0`. -/
example : IDwDerivable (⊤ : FormJ) ThetaVNoteD.zero (ThetaVNoteD.HopS ThetaVNoteD.zero)
    (ThetaVNoteD.nadd (ThetaVNoteD.Omega 0) (ThetaVNoteD.ofNat 1))
    [∼(IOmegaAt 0 (numI 0)), jlevAt ⊤ (numI 0) (numI 0)] :=
  transfer2 (ThetaVNoteD.HopS_nice _) 0 (numI_freeVariables 0)

/-- T3 at `k = 1`, `j = 0` (the main case `val j < k`). -/
example : IDwDerivable (⊤ : FormJ) ThetaVNoteD.zero (ThetaVNoteD.HopS ThetaVNoteD.zero)
    (ThetaVNoteD.nadd (ThetaVNoteD.Omega 1) (ThetaVNoteD.ofNat 4))
    [∼(qTop 1 (numI 0) (numI 0)), jlevAt ((1 : ℕ) : WithTop ℕ) (numI 0) (numI 0)] :=
  transfer3 (ThetaVNoteD.HopS_nice _) 1 (numI_freeVariables 0) (numI_freeVariables 0)

/-- T4 at `k = 1`, `j = 0`. -/
example : IDwDerivable (⊤ : FormJ) ThetaVNoteD.zero (ThetaVNoteD.HopS ThetaVNoteD.zero)
    (ThetaVNoteD.nadd (ThetaVNoteD.Omega 1) (ThetaVNoteD.ofNat 3))
    [njlevAt ((1 : ℕ) : WithTop ℕ) (numI 0) (numI 0), qTop 1 (numI 0) (numI 0)] :=
  transfer4 (ThetaVNoteD.HopS_nice _) 1 (numI_freeVariables 0) (numI_freeVariables 0)

end Smoke

end Transfer

end IDw

end OrdinalAnalysis
