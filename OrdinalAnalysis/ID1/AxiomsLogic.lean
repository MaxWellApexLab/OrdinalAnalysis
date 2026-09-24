/-
  The tautology lemma and the logical and arithmetical axioms of `ID₁` in the infinitary
  calculus.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §6: Lemma 6.1, and the proof of Theorem 6.5 (the
  axioms of `PA ⊆ ID₁` "treated as in the proof of Theorem 3.7 of the first lecture", and
  the equality axiom for `I_φ`).

  **Lemma 6.1** (`taut`): `H[k(ψ)] ⊢^{ω·rk(ψ)}_0 ψ, ¬ψ` for every closed `ψ` and every nice
  `H`.  By induction on `rk ψ` (well-founded, since the unfolding `A(t, I^{≺γ})` of a stage
  atom is not a subformula).  For the conjunctive `ψ ≃ ⋀_{γ≺δ} ψ_γ` the premise for `γ` is
  obtained by clause (W) on `¬ψ ≃ ⋁_{γ≺δ} ¬ψ_γ` at a height `α(γ)` with `γ ≺ α(γ)` and
  `α(γ) ≺ ω · rk ψ`; the disjunctive shapes are the conjunctive ones read backwards.  The
  closed formulas are those without free variables; the clause `idX` handles the literals
  of the free predicate `X`.  Heights: Freund's `α(γ) = max{ω·rk ψ_γ, γ} + 1`; for the
  finite indices `i ≺ 2` and `n ≺ ω` the equivalent `ω · rk ψ_γ ⊕ (γ + 1)` is used.

  **The arithmetical axioms.**  A closed formula without stage atoms and without `X`
  (`ArithF`) that is true in `ℕ` is derivable at height `ω ⊕ c`, `c` its complexity
  (`omega_complete`; the ω-rule for `∀`, a numeral witness for `∃`).  Through the reading
  of `X` as empty (`trueN_embK`) this gives every axiom of `𝗣𝗔⁻` and every equality axiom
  except the one for `I` (`paMinus_axiom`, `eq_axiom`).  The equality axiom for `I` is
  derived by hand as in Freund: for distinct numerals `p ≠ q` is a true literal, and for
  equal ones Lemma 6.1 applies (`relExtI_derivable`).

  Contents.

    height arithmetic: `succ_max_lt`, `omegaMul_nadd_lt_omegaMul_succ`, …
    `taut_and`, `taut_all`, `taut_stage`, `taut`       **Lemma 6.1**
    `ArithF`, `trueN_all`, `trueN_exs`, `omega_complete`
    `trueN_embK`                                       `X` read as empty
    `allClosure_derivable`                             the universal closure, by the ω-rule
    `IFreeL`, `paMinus_axiom`, `eq_axiom`, `relExtI_derivable`
-/
import OrdinalAnalysis.ID1.NumSubst
import OrdinalAnalysis.ID1.Sound

set_option autoImplicit false

namespace OrdinalAnalysis

/-! ### Height arithmetic -/

namespace ThetaNote

theorem nadd_ofNat_one (a : ThetaNote) : ThetaNote.nadd a (ofNat 1) = succ a := by
  rw [ofNat_one]; rfl

theorem succ_max_lt {p q B : ThetaNote} (hp : succ p < B) (hq : succ q < B) :
    succ (max p q) < B := by
  rcases le_total p q with h | h
  · rw [max_eq_right h]; exact hq
  · rw [max_eq_left h]; exact hp

/-- `ω · x ⊕ k ≺ ω · (m + 1)` for `x ⪯ m`. -/
theorem omegaMul_nadd_lt_omegaMul_succ {x m : ThetaNote} (h : x ≤ m) (k : ℕ) :
    ThetaNote.nadd (omegaMul x) (ofNat k) < omegaMul (succ m) :=
  omegaMul_nadd_ofNat_lt (lt_of_le_of_lt h (lt_succ m)) k

/-- `k ≺ ω · (m + 1)`. -/
theorem ofNat_lt_omegaMul_succ (m : ThetaNote) (k : ℕ) : ofNat k < omegaMul (succ m) := by
  have h := omegaMul_nadd_ofNat_lt (lt_of_le_of_lt (zero_le' m) (lt_succ m)) k
  rwa [omegaMul_zero, zero_nadd] at h

/-- `γ + 1 ≺ ω · ω · δ` for `γ ≺ δ`: the stage weight in Lemma 6.1. -/
theorem succ_lt_omegaMul_omegaMul {g a : ThetaNote} (h : g < a) :
    succ g < omegaMul (omegaMul a) := by
  have h1 : succ g ≤ succ (omegaMul g) := succ_le_succ (InductiveDef.ThetaNote.le_omegaMul g)
  have h2 : succ (omegaMul g) < omegaMul a := by
    rw [← nadd_ofNat_one]; exact omegaMul_nadd_ofNat_lt h 1
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (InductiveDef.ThetaNote.le_omegaMul _))

theorem succ_omegaMul_lt {x y : ThetaNote} (h : x < y) : succ (omegaMul x) < omegaMul y := by
  rw [← nadd_ofNat_one]; exact omegaMul_nadd_ofNat_lt h 1

theorem lt_nadd_ofNat_succ (a : ThetaNote) (k : ℕ) : a < ThetaNote.nadd a (ofNat (k + 1)) :=
  lt_of_lt_of_le (lt_succ a) (by
    rw [← nadd_ofNat_one]
    exact nadd_le_nadd_right a (ofNat_le_ofNat (by omega)))

theorem ofNat_lt_nadd_ofNat_succ (a : ThetaNote) (k : ℕ) : ofNat k < ThetaNote.nadd a (ofNat (k + 1)) :=
  lt_of_lt_of_le (ofNat_lt_ofNat (Nat.lt_succ_self k)) (le_nadd_right _ _)

theorem nadd_ofNat_lt_nadd_ofNat (a : ThetaNote) {j k : ℕ} (h : j < k) :
    ThetaNote.nadd a (ofNat j) < ThetaNote.nadd a (ofNat k) :=
  nadd_lt_nadd_right a (ofNat_lt_ofNat h)

theorem one_lt_nadd_ofNat_two (a : ThetaNote) : one < ThetaNote.nadd a (ofNat 2) := by
  rw [← ofNat_one]; exact ofNat_lt_nadd_ofNat_succ a 1

theorem ofNat_nadd_ofNat (m : ℕ) : ∀ n : ℕ, ThetaNote.nadd (ofNat m) (ofNat n) = ofNat (m + n)
  | 0 => by rw [ofNat_zero, nadd_zero, Nat.add_zero]
  | n + 1 => by
    rw [ofNat_succ, succ, ← nadd_assoc, ofNat_nadd_ofNat m n, ← succ, ← ofNat_succ]; rfl

end ThetaNote

namespace InductiveDef

open LO LO.FirstOrder

/-! ### Structural helpers -/

section Helpers

variable {A : Semisentence LXI 1} {ρ : ThetaNote}

/-- Case analysis on a proposition of `LIinf`, in connective form. -/
theorem cases0 {C : Proposition LIinf → Prop}
    (hverum : C ⊤) (hfalsum : C ⊥)
    (hrel : ∀ (k : ℕ) (r : LIinf.Rel k) (v : Fin k → SyntacticTerm LIinf), C (Semiformula.rel r v))
    (hnrel : ∀ (k : ℕ) (r : LIinf.Rel k) (v : Fin k → SyntacticTerm LIinf),
      C (Semiformula.nrel r v))
    (hand : ∀ φ ψ : Proposition LIinf, C (φ ⋏ ψ))
    (hor : ∀ φ ψ : Proposition LIinf, C (φ ⋎ ψ))
    (hall : ∀ φ : Semiproposition LIinf 1, C (∀¹ φ))
    (hexs : ∀ φ : Semiproposition LIinf 1, C (∃¹ φ)) :
    ∀ φ : Proposition LIinf, C φ
  | Semiformula.verum => hverum
  | Semiformula.falsum => hfalsum
  | Semiformula.rel r v => hrel _ r v
  | Semiformula.nrel r v => hnrel _ r v
  | Semiformula.and φ ψ => hand φ ψ
  | Semiformula.or φ ψ => hor φ ψ
  | Semiformula.all φ => hall φ
  | Semiformula.exs φ => hexs φ

/-- Moving a derivation to a larger operator and a larger sequent. -/
theorem IDerivable.lift {K K' : Set ThetaNote → Set ThetaNote} (hK' : ThetaNote.IsOperator K')
    (hKK : ∀ X, K X ⊆ K' X) {h : ThetaNote} {Δ Δ' : Sequent LIinf}
    (d : IDerivable A ρ K h Δ) (hsub : Δ ⊆ Δ') (hP : paramsList Δ' ⊆ K' ∅) :
    IDerivable A ρ K' h Δ' :=
  (d.mono_op hKK).weaken_seq hK' hsub hP

theorem adjoin_le_adjoin {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.IsOperator H)
    {Z Z' : Set ThetaNote} (h : Z ⊆ Z') (X : Set ThetaNote) :
    ThetaNote.adjoin H Z X ⊆ ThetaNote.adjoin H Z' X :=
  hH.mono (Set.union_subset_union_left X h)

theorem subset_adjoin_empty {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.IsOperator H)
    (Z : Set ThetaNote) : Z ⊆ ThetaNote.adjoin H Z ∅ := by
  intro x hx
  exact hH.subset _ (Or.inl hx)

theorem freeVariables_subst_numI (φ : Semiformula LIinf ℕ 1) (hφ : φ.freeVariables = ∅)
    (n : ℕ) : (φ/[numI n]).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![numI n]) (φ := φ) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ ((Rew.subst ![numI n]) #i : SyntacticTerm LIinf).freeVariables := hi
    cases i using Fin.cases with
    | zero => simp only [Rew.subst_bvar, Matrix.cons_val_zero, numI_freeVariables] at hi'
              exact Finset.notMem_empty x hi'
    | succ i => exact i.elim0
  · have hz' : z ∈ φ.freeVariables := hz
    rw [hφ] at hz'
    exact Finset.notMem_empty z hz'

theorem freeVariables_subst_of_closed (φ : Semiformula LIinf ℕ 1) (hφ : φ.freeVariables = ∅)
    {t : SyntacticTerm LIinf} (ht : t.freeVariables = ∅) : (φ/[t]).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![t]) (φ := φ) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ ((Rew.subst ![t]) #i : SyntacticTerm LIinf).freeVariables := hi
    cases i using Fin.cases with
    | zero => simp only [Rew.subst_bvar, Matrix.cons_val_zero, ht] at hi'
              exact Finset.notMem_empty x hi'
    | succ i => exact i.elim0
  · have hz' : z ∈ φ.freeVariables := hz
    rw [hφ] at hz'
    exact Finset.notMem_empty z hz'

/-- The sequent `ψ, ¬ψ` read backwards. -/
theorem IDerivable.swap {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.IsOperator H)
    {h : ThetaNote} {ψ : Proposition LIinf} (d : IDerivable A ρ H h [∼ψ, ψ]) :
    IDerivable A ρ H h [ψ, ∼ψ] := by
  refine d.weaken_seq (Γ' := [ψ, ∼ψ]) hH (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) ?_
  have := d.params_subset
  simp only [paramsList_cons, paramsList_nil, params_neg, Set.union_empty] at this ⊢
  exact this

end Helpers

/-! ### Lemma 6.1 -/

section Taut

variable {A : Semisentence LXI 1} {H : Set ThetaNote → Set ThetaNote}

theorem params_sub_adjoin (hH : ThetaNote.IsOperator H) {ψ : Proposition LIinf} :
    paramsList [ψ, ∼ψ] ⊆ ThetaNote.adjoin H (params ψ) ∅ := by
  simp only [paramsList_cons, paramsList_nil, params_neg, Set.union_empty, Set.union_self]
  exact subset_adjoin_empty hH _

/-- **Lemma 6.1, conjunction.** -/
theorem taut_and (hH : ThetaNote.Nice H) {φ₀ φ₁ : Proposition LIinf}
    (ih₀ : IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params φ₀))
      (ThetaNote.omegaMul (rk φ₀)) [φ₀, ∼φ₀])
    (ih₁ : IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params φ₁))
      (ThetaNote.omegaMul (rk φ₁)) [φ₁, ∼φ₁]) :
    IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params (φ₀ ⋏ φ₁)))
      (ThetaNote.omegaMul (rk (φ₀ ⋏ φ₁))) [φ₀ ⋏ φ₁, ∼(φ₀ ⋏ φ₁)] := by
  set ψ : Proposition LIinf := φ₀ ⋏ φ₁ with hψ
  have hK := hH.adjoin (params ψ)
  have hKo := hK.isOperator
  have hZ : params ψ ⊆ ThetaNote.adjoin H (params ψ) ∅ := subset_adjoin_empty hH.isOperator _
  have hΓ : paramsList [ψ, ∼ψ] ⊆ ThetaNote.adjoin H (params ψ) ∅ :=
    params_sub_adjoin hH.isOperator
  have hneg : ∼ψ = ∼φ₀ ⋎ ∼φ₁ := by simp [hψ]
  have hrk : rk ψ = ThetaNote.succ (max (rk φ₀) (rk φ₁)) := rk_and φ₀ φ₁
  have hs0 : params φ₀ ⊆ params ψ := Set.subset_union_left
  have hs1 : params φ₁ ⊆ params ψ := Set.subset_union_right
  -- the heights
  have hm0 : ThetaNote.omegaMul (rk φ₀) ∈ ThetaNote.adjoin H (params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_mem (hs0.trans hZ))
  have hm1 : ThetaNote.omegaMul (rk φ₁) ∈ ThetaNote.adjoin H (params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_mem (hs1.trans hZ))
  have hmψ : ThetaNote.omegaMul (rk ψ) ∈ ThetaNote.adjoin H (params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_mem hZ)
  have hP : ∀ φ : Proposition LIinf, params φ ⊆ params ψ →
      paramsList [∼φ, φ, ψ, ∼ψ] ⊆ ThetaNote.adjoin H (params ψ) ∅ := by
    intro φ hφ
    simp only [paramsList_cons, paramsList_nil, params_neg, Set.union_empty]
    exact Set.union_subset (hφ.trans hZ) (Set.union_subset (hφ.trans hZ)
      (Set.union_subset hZ hZ))
  have hP' : ∀ φ : Proposition LIinf, params φ ⊆ params ψ →
      paramsList [φ, ψ, ∼ψ] ⊆ ThetaNote.adjoin H (params ψ) ∅ := by
    intro φ hφ
    simp only [paramsList_cons, paramsList_nil, params_neg, Set.union_empty]
    exact Set.union_subset (hφ.trans hZ) (Set.union_subset hZ hZ)
  have d0 : IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params ψ))
      (ThetaNote.omegaMul (rk φ₀)) [∼φ₀, φ₀, ψ, ∼ψ] :=
    ih₀.lift hKo (adjoin_le_adjoin hH.isOperator hs0)
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) (hP φ₀ hs0)
  have d1 : IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params ψ))
      (ThetaNote.omegaMul (rk φ₁)) [∼φ₁, φ₁, ψ, ∼ψ] :=
    ih₁.lift hKo (adjoin_le_adjoin hH.isOperator hs1)
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) (hP φ₁ hs1)
  have e0 : IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params ψ))
      (ThetaNote.nadd (ThetaNote.omegaMul (rk φ₀)) (ThetaNote.ofNat 2)) [φ₀, ψ, ∼ψ] :=
    .orL (hK.nadd_mem hm0 (hK.ofNat_mem 2)) (hP' φ₀ hs0)
      (by rw [← hneg]; simp) (ThetaNote.lt_nadd_ofNat_succ _ 1) d0
  have e1 : IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params ψ))
      (ThetaNote.nadd (ThetaNote.omegaMul (rk φ₁)) (ThetaNote.ofNat 2)) [φ₁, ψ, ∼ψ] :=
    .orR (hK.nadd_mem hm1 (hK.ofNat_mem 2)) (hP' φ₁ hs1)
      (by rw [← hneg]; simp) (ThetaNote.one_lt_nadd_ofNat_two _)
      (ThetaNote.lt_nadd_ofNat_succ _ 1) d1
  refine .and hmψ hΓ List.mem_cons_self ?_ ?_ e0 e1
  · rw [hrk]; exact ThetaNote.omegaMul_nadd_lt_omegaMul_succ (le_max_left _ _) 2
  · rw [hrk]; exact ThetaNote.omegaMul_nadd_lt_omegaMul_succ (le_max_right _ _) 2

/-- **Lemma 6.1, universal quantifier.** -/
theorem taut_all (hH : ThetaNote.Nice H) {φ : Semiproposition LIinf 1}
    (ih : ∀ n : ℕ, IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params (φ/[numI n])))
      (ThetaNote.omegaMul (rk (φ/[numI n]))) [φ/[numI n], ∼(φ/[numI n])]) :
    IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params (∀¹ φ)))
      (ThetaNote.omegaMul (rk (∀¹ φ))) [∀¹ φ, ∼(∀¹ φ)] := by
  set ψ : Proposition LIinf := ∀¹ φ with hψ
  have hK := hH.adjoin (params ψ)
  have hKo := hK.isOperator
  have hZ : params ψ ⊆ ThetaNote.adjoin H (params ψ) ∅ := subset_adjoin_empty hH.isOperator _
  have hΓ : paramsList [ψ, ∼ψ] ⊆ ThetaNote.adjoin H (params ψ) ∅ :=
    params_sub_adjoin hH.isOperator
  have hneg : ∼ψ = ∃¹ (∼φ) := by simp [hψ]
  have hrk : rk ψ = ThetaNote.succ (rk φ) := rk_all φ
  have hsn : ∀ n, params (φ/[numI n]) = params ψ := fun n => params_subst φ _
  have hmφ : ThetaNote.omegaMul (rk φ) ∈ ThetaNote.adjoin H (params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_mem (by rw [show params ψ = params φ from rfl] at hZ; exact hZ))
  have hmψ : ThetaNote.omegaMul (rk ψ) ∈ ThetaNote.adjoin H (params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_mem hZ)
  refine .all (fun n => ThetaNote.nadd (ThetaNote.omegaMul (rk φ)) (ThetaNote.ofNat (n + 1)))
    hmψ hΓ (φ := φ) List.mem_cons_self (fun n => by
      rw [hrk]; exact ThetaNote.omegaMul_nadd_lt_omegaMul_succ le_rfl _) (fun n => ?_)
  have hP : paramsList [φ/[numI n], ψ, ∼ψ] ⊆ ThetaNote.adjoin H (params ψ) ∅ := by
    simp only [paramsList_cons, paramsList_nil, params_neg, Set.union_empty, hsn n]
    exact Set.union_subset hZ (Set.union_subset hZ hZ)
  have d : IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params ψ))
      (ThetaNote.omegaMul (rk φ)) [(∼φ)/[numI n], φ/[numI n], ψ, ∼ψ] := by
    have e : (∼φ)/[numI n] = ∼(φ/[numI n]) := by simp
    rw [e]
    have ihn := ih n
    rw [rk_subst] at ihn
    refine ihn.lift hKo (fun X => by rw [hsn n]) (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) ?_
    simp only [paramsList_cons, paramsList_nil, params_neg, Set.union_empty, hsn n]
    exact Set.union_subset hZ (Set.union_subset hZ (Set.union_subset hZ hZ))
  exact .exs n (hK.nadd_mem hmφ (hK.ofNat_mem _)) hP (by rw [← hneg]; simp)
    (ThetaNote.ofNat_lt_nadd_ofNat_succ _ n) (ThetaNote.lt_nadd_ofNat_succ _ n) d

/-- **Lemma 6.1, stage atom** `I^{≺δ} t`. -/
theorem taut_stage (hH : ThetaNote.Nice H) (a : Stage) (t : SyntacticTerm LIinf)
    (ih : ∀ g : Stage, g.1 < a.1 →
      IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params (unfold A g t)))
        (ThetaNote.omegaMul (rk (unfold A g t))) [unfold A g t, ∼(unfold A g t)]) :
    IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params (stageAt a t)))
      (ThetaNote.omegaMul (rk (stageAt a t))) [stageAt a t, ∼(stageAt a t)] := by
  set ψ : Proposition LIinf := stageAt a t with hψ
  have hK := hH.adjoin (params ψ)
  have hZ : params ψ ⊆ ThetaNote.adjoin H (params ψ) ∅ := subset_adjoin_empty hH.isOperator _
  have hΓ : paramsList [ψ, ∼ψ] ⊆ ThetaNote.adjoin H (params ψ) ∅ :=
    params_sub_adjoin hH.isOperator
  have hmψ : ThetaNote.omegaMul (rk ψ) ∈ ThetaNote.adjoin H (params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_mem hZ)
  refine .nstage (fun g => ThetaNote.succ (max (ThetaNote.omegaMul (rk (unfold A g t))) g.1))
    hmψ hΓ (a := a) (t := t) (List.mem_cons_of_mem _ List.mem_cons_self) (fun g hg => ?_)
    (fun g hg => ?_)
  · rw [hψ, rk_stageAt]
    refine ThetaNote.succ_max_lt ?_ (ThetaNote.succ_lt_omegaMul_omegaMul hg)
    refine ThetaNote.succ_omegaMul_lt ?_
    have := rk_unfold_lt_stageAt A hg t t
    rwa [rk_stageAt] at this
  · -- the premise for `g`, by clause (W) on `I^{≺δ} t` with the witness `g`
    set K' := ThetaNote.adjoin (ThetaNote.adjoin H (params ψ)) {g.1} with hK'
    have hK'n : ThetaNote.Nice K' := hK.adjoin {g.1}
    have hg' : g.1 ∈ K' ∅ := subset_adjoin_empty hK.isOperator {g.1} rfl
    have hsub : params ψ ⊆ K' ∅ :=
      hZ.trans (hK.isOperator.mono (Set.empty_subset _))
    have hu : params (unfold A g t) ⊆ K' ∅ :=
      (params_unfold A g t).trans (Set.singleton_subset_iff.mpr hg')
    have hmu : ThetaNote.omegaMul (rk (unfold A g t)) ∈ K' ∅ :=
      hK'n.omegaMul_mem (hK'n.rk_mem hu)
    have hmax : max (ThetaNote.omegaMul (rk (unfold A g t))) g.1 ∈ K' ∅ := by
      rcases le_total (ThetaNote.omegaMul (rk (unfold A g t))) g.1 with h | h
      · rw [max_eq_right h]; exact hg'
      · rw [max_eq_left h]; exact hmu
    have hP : paramsList [∼(unfold A g t), ψ, ∼ψ] ⊆ K' ∅ := by
      simp only [paramsList_cons, paramsList_nil, params_neg, Set.union_empty]
      exact Set.union_subset hu (Set.union_subset hsub hsub)
    have hP2 : paramsList [unfold A g t, ∼(unfold A g t), ψ, ∼ψ] ⊆ K' ∅ := by
      simp only [paramsList_cons, paramsList_nil, params_neg, Set.union_empty]
      exact Set.union_subset hu (Set.union_subset hu (Set.union_subset hsub hsub))
    have hop : ∀ X, ThetaNote.adjoin H (params (unfold A g t)) X ⊆ K' X := by
      intro X
      rw [hK', ThetaNote.adjoin_adjoin]
      exact adjoin_le_adjoin hH.isOperator
        ((params_unfold A g t).trans Set.subset_union_right) X
    have d : IDerivable A ThetaNote.zero K' (ThetaNote.omegaMul (rk (unfold A g t)))
        [unfold A g t, ∼(unfold A g t), ψ, ∼ψ] :=
      (ih g hg).lift hK'n.isOperator hop
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) hP2
    exact .stage g (hK'n.succ_mem hmax) hP (a := a) (t := t)
      (List.mem_cons_of_mem _ List.mem_cons_self) hg
      (lt_of_le_of_lt (le_max_right _ _) (ThetaNote.lt_succ _)) hg'
      (lt_of_le_of_lt (le_max_left _ _) (ThetaNote.lt_succ _)) d

/-- A derivation of `¬ψ, ¬¬ψ` is one of `ψ, ¬ψ`. -/
theorem taut_neg (hH : ThetaNote.Nice H) {ψ : Proposition LIinf}
    (d : IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params (∼ψ)))
      (ThetaNote.omegaMul (rk (∼ψ))) [∼ψ, ∼(∼ψ)]) :
    IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params ψ))
      (ThetaNote.omegaMul (rk ψ)) [ψ, ∼ψ] := by
  rw [params_neg, rk_neg] at d
  have e : ∼(∼ψ) = ψ := by simp
  rw [e] at d
  exact d.swap (hH.adjoin _).isOperator

theorem freeVariables_unfold (a : Stage) {t : SyntacticTerm LIinf} (ht : t.freeVariables = ∅) :
    (unfold A a t).freeVariables = ∅ :=
  freeVariables_subst_of_closed _ (Semiformula.freeVariables_emb _) ht

/-- **Freund, Lemma 6.1**: `H[k(ψ)] ⊢^{ω·rk(ψ)}_0 ψ, ¬ψ` for every closed formula `ψ` and
every nice operator `H`. -/
theorem taut (hH : ThetaNote.Nice H) (ψ : Proposition LIinf) (hc : ψ.freeVariables = ∅) :
    IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params ψ))
      (ThetaNote.omegaMul (rk ψ)) [ψ, ∼ψ] := by
  suffices key : ∀ r : ThetaNote, ∀ ψ : Proposition LIinf, rk ψ = r → ψ.freeVariables = ∅ →
      IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params ψ))
        (ThetaNote.omegaMul (rk ψ)) [ψ, ∼ψ] from key _ ψ rfl hc
  intro r
  induction r using WellFoundedLT.induction with
  | _ r ih =>
  intro ψ hr hc
  subst hr
  have IH : ∀ φ : Proposition LIinf, rk φ < rk ψ → φ.freeVariables = ∅ →
      IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params φ))
        (ThetaNote.omegaMul (rk φ)) [φ, ∼φ] := fun φ h hc' => ih _ h φ rfl hc'
  have hK := hH.adjoin (params ψ)
  have hZ : params ψ ⊆ ThetaNote.adjoin H (params ψ) ∅ := subset_adjoin_empty hH.isOperator _
  have hα : ThetaNote.omegaMul (rk ψ) ∈ ThetaNote.adjoin H (params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_mem hZ)
  have hΓ : paramsList [ψ, ∼ψ] ⊆ ThetaNote.adjoin H (params ψ) ∅ :=
    params_sub_adjoin hH.isOperator
  revert IH hc hα hΓ
  cases ψ using cases0 with
  | hverum => intro _ _ hα hΓ; exact .verum hα hΓ List.mem_cons_self
  | hfalsum =>
    intro _ _ hα hΓ; exact .verum hα hΓ (List.mem_cons_of_mem _ List.mem_cons_self)
  | hrel k r v =>
    intro hc IH hα hΓ
    rcases r with r | r
    · have hv : ∀ i, (v i).freeVariables = ∅ := freeVariables_rel_arg hc
      have hl : IsArithLit (Semiformula.rel (Sum.inl r : LIinf.Rel k) v) :=
        ⟨k, r, v, Or.inl rfl, hv⟩
      by_cases ht : TrueN (Semiformula.rel (Sum.inl r : LIinf.Rel k) v)
      · exact .literal hα hΓ ⟨hl, ht⟩ List.mem_cons_self
      · exact .literal hα hΓ ⟨hl.neg, (trueN_neg _).mpr ht⟩
          (List.mem_cons_of_mem _ List.mem_cons_self)
    · cases r with
      | X =>
        have e : Semiformula.rel (Sum.inr IInfRel.X : LIinf.Rel 1) v = XinfAt (v 0) :=
          rel_eq_vec _ v
        have d : IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params (XinfAt (v 0))))
            (ThetaNote.omegaMul (rk (XinfAt (v 0)))) [XinfAt (v 0), ∼(XinfAt (v 0))] := by
          rw [← e]
          exact .idX (v 0) hα hΓ (by rw [e]; exact List.mem_cons_self)
            (by rw [e]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        rw [e]; exact d
      | stage a =>
        have e : Semiformula.rel (Sum.inr (IInfRel.stage a) : LIinf.Rel 1) v = stageAt a (v 0) :=
          rel_eq_vec _ v
        have hv0 : (v 0).freeVariables = ∅ := freeVariables_rel_arg hc 0
        rw [e]
        refine taut_stage hH a (v 0) fun g hg => IH _ ?_ (freeVariables_unfold g hv0)
        rw [e]
        exact rk_unfold_lt_stageAt A hg (v 0) (v 0)
  | hnrel k r v =>
    intro hc IH hα hΓ
    rcases r with r | r
    · have hv : ∀ i, (v i).freeVariables = ∅ := freeVariables_nrel_arg hc
      have hl : IsArithLit (Semiformula.nrel (Sum.inl r : LIinf.Rel k) v) :=
        ⟨k, r, v, Or.inr rfl, hv⟩
      by_cases ht : TrueN (Semiformula.nrel (Sum.inl r : LIinf.Rel k) v)
      · exact .literal hα hΓ ⟨hl, ht⟩ List.mem_cons_self
      · exact .literal hα hΓ ⟨hl.neg, (trueN_neg _).mpr ht⟩
          (List.mem_cons_of_mem _ List.mem_cons_self)
    · cases r with
      | X =>
        have e : Semiformula.nrel (Sum.inr IInfRel.X : LIinf.Rel 1) v = ∼(XinfAt (v 0)) :=
          nrel_eq_vec _ v
        have d : IDerivable A ThetaNote.zero (ThetaNote.adjoin H (params (∼(XinfAt (v 0)))))
            (ThetaNote.omegaMul (rk (∼(XinfAt (v 0))))) [∼(XinfAt (v 0)), ∼(∼(XinfAt (v 0)))] := by
          rw [← e]
          exact .idX (v 0) hα hΓ (by rw [e]; exact List.mem_cons_of_mem _ (by simp))
            (by rw [e]; exact List.mem_cons_self)
        rw [e]; exact d
      | stage a =>
        have e : Semiformula.nrel (Sum.inr (IInfRel.stage a) : LIinf.Rel 1) v =
            ∼(stageAt a (v 0)) := nrel_eq_vec _ v
        have hv0 : (v 0).freeVariables = ∅ := freeVariables_nrel_arg hc 0
        rw [e]
        refine taut_neg hH ?_
        have e2 : ∼(∼(stageAt a (v 0))) = stageAt a (v 0) := by simp
        rw [e2]
        refine taut_stage hH a (v 0) fun g hg => IH _ ?_ (freeVariables_unfold g hv0)
        rw [e, rk_neg]
        exact rk_unfold_lt_stageAt A hg (v 0) (v 0)
  | hand φ₀ φ₁ =>
    intro hc IH _ _
    rw [Semiformula.freeVariables_and, Finset.union_eq_empty] at hc
    exact taut_and hH (IH φ₀ (rk_left_lt_and φ₀ φ₁) hc.1) (IH φ₁ (rk_right_lt_and φ₀ φ₁) hc.2)
  | hor φ₀ φ₁ =>
    intro hc IH _ _
    rw [Semiformula.freeVariables_or, Finset.union_eq_empty] at hc
    refine taut_neg hH ?_
    have e : ∼(φ₀ ⋎ φ₁) = ∼φ₀ ⋏ ∼φ₁ := by simp
    rw [e]
    refine taut_and hH (IH (∼φ₀) ?_ (by rw [Semiformula.freeVariables_not]; exact hc.1))
      (IH (∼φ₁) ?_ (by rw [Semiformula.freeVariables_not]; exact hc.2))
    · rw [rk_neg]; exact rk_left_lt_or φ₀ φ₁
    · rw [rk_neg]; exact rk_right_lt_or φ₀ φ₁
  | hall φ =>
    intro hc IH _ _
    rw [Semiformula.freeVariables_all] at hc
    exact taut_all hH fun n => IH _ (rk_subst_lt_all φ _) (freeVariables_subst_numI φ hc n)
  | hexs φ =>
    intro hc IH _ _
    rw [Semiformula.freeVariables_exs] at hc
    refine taut_neg hH ?_
    have e : ∼(∃¹ φ) = ∀¹ (∼φ) := by simp
    rw [e]
    refine taut_all hH fun n => IH _ ?_ (freeVariables_subst_numI (∼φ)
      (by rw [Semiformula.freeVariables_not]; exact hc) n)
    rw [rk_subst]
    have := rk_lt_exs φ
    rwa [rk_neg]

end Taut

/-! ### ω-completeness for arithmetic -/

section Arith

variable {A : Semisentence LXI 1} {ρ : ThetaNote} {H : Set ThetaNote → Set ThetaNote}

/-- `r` is a relation symbol of arithmetic. -/
def IsArithRel {k : ℕ} (r : LIinf.Rel k) : Prop := ∃ r' : (ℒₒᵣ : Language).Rel k, r = Sum.inl r'

/-- A formula all of whose atoms are atoms of arithmetic. -/
def ArithF {ξ : Type*} : {n : ℕ} → Semiformula LIinf ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel r _ => IsArithRel r
  | _, .nrel r _ => IsArithRel r
  | _, .and φ ψ => ArithF φ ∧ ArithF ψ
  | _, .or φ ψ => ArithF φ ∧ ArithF ψ
  | _, .all φ => ArithF φ
  | _, .exs φ => ArithF φ

theorem arithF_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LIinf ξ₁ n₁ ξ₂ n₂)
    {φ : Semiformula LIinf ξ₁ n₁} (h : ArithF φ) : ArithF (ω ▹ φ) := by
  revert h
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => intro _; simp only [LogicalConnective.HomClass.map_top]; trivial
  | hfalsum => intro _; simp only [LogicalConnective.HomClass.map_bot]; trivial
  | hrel r v => intro h; rw [Semiformula.rew_rel]; exact h
  | hnrel r v => intro h; rw [Semiformula.rew_nrel]; exact h
  | hand φ ψ ihφ ihψ =>
    intro h; rw [LogicalConnective.HomClass.map_and]; exact ⟨ihφ ω h.1, ihψ ω h.2⟩
  | hor φ ψ ihφ ihψ =>
    intro h; rw [LogicalConnective.HomClass.map_or]; exact ⟨ihφ ω h.1, ihψ ω h.2⟩
  | hall φ ih => intro h; rw [Rewriting.app_all]; exact ih ω.q h
  | hexs φ ih => intro h; rw [Rewriting.app_exs]; exact ih ω.q h

theorem params_of_arithF {ξ : Type*} {n : ℕ} {φ : Semiformula LIinf ξ n} (h : ArithF φ) :
    params φ = ∅ := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => obtain ⟨r', rfl⟩ := h; rfl
  | hnrel r v => obtain ⟨r', rfl⟩ := h; rfl
  | hand φ ψ ihφ ihψ => rw [params_and, ihφ h.1, ihψ h.2, Set.union_empty]
  | hor φ ψ ihφ ihψ => rw [params_or, ihφ h.1, ihψ h.2, Set.union_empty]
  | hall φ ih => exact ih h
  | hexs φ ih => exact ih h

theorem trueN_all (φ : Semiproposition LIinf 1) :
    TrueN (∀¹ φ) ↔ ∀ n : ℕ, TrueN (φ/[numI n]) := by
  unfold TrueN
  rw [Semiformula.eval_all]
  refine forall_congr' fun n => ?_
  rw [show φ/[numI n] = φ ⇜ ![numI n] from rfl, Semiformula.eval_substs]
  refine iff_of_eq (congrArg (fun w => Semiformula.Eval (s := stdInf) w (fun _ => 0) φ) ?_)
  funext i
  obtain rfl := Subsingleton.elim i 0
  simp only [Matrix.cons_val_zero, Function.comp_apply]
  exact (val_numI n _ _).symm

theorem trueN_exs (φ : Semiproposition LIinf 1) :
    TrueN (∃¹ φ) ↔ ∃ n : ℕ, TrueN (φ/[numI n]) := by
  unfold TrueN
  rw [Semiformula.eval_ex]
  refine exists_congr fun n => ?_
  rw [show φ/[numI n] = φ ⇜ ![numI n] from rfl, Semiformula.eval_substs]
  refine iff_of_eq (congrArg (fun w => Semiformula.Eval (s := stdInf) w (fun _ => 0) φ) ?_)
  funext i
  obtain rfl := Subsingleton.elim i 0
  simp only [Matrix.cons_val_zero, Function.comp_apply]
  exact (val_numI n _ _).symm

/-- `ω`, as a notation. -/
abbrev omegaT : ThetaNote := ThetaNote.omegaPow ThetaNote.one

theorem omegaT_mem (hH : ThetaNote.Nice H) (X : Set ThetaNote) (c : ℕ) :
    ThetaNote.nadd omegaT (ThetaNote.ofNat c) ∈ H X :=
  hH.nadd_mem (hH.omegaPow_mem hH.one_mem) (hH.ofNat_mem c)

theorem ofNat_lt_omegaT_nadd (n c : ℕ) :
    ThetaNote.ofNat n < ThetaNote.nadd omegaT (ThetaNote.ofNat c) :=
  lt_of_lt_of_le (ThetaNote.ofNat_lt_omega n) (ThetaNote.le_nadd_left _ _)

/-- **ω-completeness**: a closed arithmetic formula true in `ℕ` is derivable, cut-free, at
height `ω ⊕ c` for every bound `c` on its complexity. -/
theorem omega_complete (hH : ThetaNote.Nice H) :
    ∀ (c : ℕ) (φ : Proposition LIinf), φ.complexity ≤ c → ArithF φ → φ.freeVariables = ∅ →
      TrueN φ → IDerivable A ρ H (ThetaNote.nadd omegaT (ThetaNote.ofNat c)) [φ] := by
  intro c
  induction c with
  | zero =>
    intro φ hc hA hf ht
    have hP : paramsList [φ] ⊆ H ∅ := by
      simp only [paramsList_cons, paramsList_nil, params_of_arithF hA, Set.union_empty]
      exact Set.empty_subset _
    revert hc hA hf ht hP
    cases φ using cases0 with
    | hverum => intro _ _ _ _ hP; exact .verum (omegaT_mem hH _ _) hP List.mem_cons_self
    | hfalsum => intro _ _ _ ht _; exact absurd ht (by simp [TrueN])
    | hrel k r v =>
      intro _ hA hf ht hP
      obtain ⟨r', rfl⟩ := hA
      exact .literal (omegaT_mem hH _ _) hP ⟨⟨k, r', v, Or.inl rfl, freeVariables_rel_arg hf⟩, ht⟩
        List.mem_cons_self
    | hnrel k r v =>
      intro _ hA hf ht hP
      obtain ⟨r', rfl⟩ := hA
      exact .literal (omegaT_mem hH _ _) hP ⟨⟨k, r', v, Or.inr rfl, freeVariables_nrel_arg hf⟩, ht⟩
        List.mem_cons_self
    | hand φ ψ => intro hc; simp at hc
    | hor φ ψ => intro hc; simp at hc
    | hall φ => intro hc; simp at hc
    | hexs φ => intro hc; simp at hc
  | succ c ih =>
    intro φ hc hA hf ht
    have hP : paramsList [φ] ⊆ H ∅ := by
      simp only [paramsList_cons, paramsList_nil, params_of_arithF hA, Set.union_empty]
      exact Set.empty_subset _
    have hm : ThetaNote.nadd omegaT (ThetaNote.ofNat (c + 1)) ∈ H ∅ := omegaT_mem hH _ _
    have hlt : ThetaNote.nadd omegaT (ThetaNote.ofNat c) <
        ThetaNote.nadd omegaT (ThetaNote.ofNat (c + 1)) :=
      ThetaNote.nadd_ofNat_lt_nadd_ofNat _ (Nat.lt_succ_self c)
    have lift : ∀ χ : Proposition LIinf, χ.complexity ≤ c → ArithF χ → χ.freeVariables = ∅ →
        TrueN χ → IDerivable A ρ H (ThetaNote.nadd omegaT (ThetaNote.ofNat c)) [χ, φ] := by
      intro χ h1 h2 h3 h4
      refine (ih χ h1 h2 h3 h4).weaken_seq hH.isOperator
        (List.cons_subset_cons _ (List.nil_subset _)) ?_
      simp only [paramsList_cons, paramsList_nil, params_of_arithF hA, params_of_arithF h2,
        Set.union_empty]
      exact Set.empty_subset _
    revert hc hA hf ht hP lift
    cases φ using cases0 with
    | hverum => intro _ _ _ _ hP _; exact .verum hm hP List.mem_cons_self
    | hfalsum => intro _ _ _ ht _ _; exact absurd ht (by simp [TrueN])
    | hrel k r v =>
      intro _ hA hf ht hP _
      obtain ⟨r', rfl⟩ := hA
      exact .literal hm hP ⟨⟨k, r', v, Or.inl rfl, freeVariables_rel_arg hf⟩, ht⟩
        List.mem_cons_self
    | hnrel k r v =>
      intro _ hA hf ht hP _
      obtain ⟨r', rfl⟩ := hA
      exact .literal hm hP ⟨⟨k, r', v, Or.inr rfl, freeVariables_nrel_arg hf⟩, ht⟩
        List.mem_cons_self
    | hand φ ψ =>
      intro hc hA hf ht hP lift
      rw [Semiformula.complexity_and] at hc
      rw [Semiformula.freeVariables_and, Finset.union_eq_empty] at hf
      have ht' : TrueN φ ∧ TrueN ψ := by simpa [TrueN] using ht
      exact .and hm hP List.mem_cons_self hlt hlt
        (lift φ (by omega) hA.1 hf.1 ht'.1) (lift ψ (by omega) hA.2 hf.2 ht'.2)
    | hor φ ψ =>
      intro hc hA hf ht hP lift
      rw [Semiformula.complexity_or] at hc
      rw [Semiformula.freeVariables_or, Finset.union_eq_empty] at hf
      have ht' : TrueN φ ∨ TrueN ψ := by simpa [TrueN] using ht
      rcases ht' with h | h
      · exact .orL hm hP List.mem_cons_self hlt (lift φ (by omega) hA.1 hf.1 h)
      · exact .orR hm hP List.mem_cons_self
          (lt_of_lt_of_le (by rw [← ThetaNote.ofNat_one]; exact ThetaNote.ofNat_lt_omega 1)
            (ThetaNote.le_nadd_left _ _)) hlt (lift ψ (by omega) hA.2 hf.2 h)
    | hall φ =>
      intro hc hA hf ht hP lift
      rw [Semiformula.complexity_all] at hc
      rw [Semiformula.freeVariables_all] at hf
      refine .all (fun _ => ThetaNote.nadd omegaT (ThetaNote.ofNat c)) hm hP List.mem_cons_self
        (fun _ => hlt) fun n => lift _ (by rw [Semiformula.complexity_rew]; omega)
          (arithF_rew _ hA) (freeVariables_subst_numI φ hf n) ((trueN_all φ).mp ht n)
    | hexs φ =>
      intro hc hA hf ht hP lift
      rw [Semiformula.complexity_exs] at hc
      rw [Semiformula.freeVariables_exs] at hf
      obtain ⟨n, hn⟩ := (trueN_exs φ).mp ht
      exact .exs n hm hP List.mem_cons_self (ofNat_lt_omegaT_nadd n _) hlt
        (lift _ (by rw [Semiformula.complexity_rew]; omega) (arithF_rew _ hA)
          (freeVariables_subst_numI φ hf n) hn)

end Arith

/-! ### `X` read as empty: the semantics -/

section Semantics

theorem stdInf_lMap_eq : stdInf.lMap (stageHom Stage.top) = stdI (fun _ => False) ∅ := by
  unfold Structure.lMap
  show Structure.mk _ _ = Structure.mk _ _
  congr 1
  · funext k f v
    rcases f with f | f
    · rfl
    · exact PEmpty.elim f
  · funext k r v
    rcases r with r | r
    · rfl
    · cases r <;> rfl

theorem eval_killX_stdI (S : Set ℕ) {ξ : Type*} {n : ℕ} (φ : Semiformula LXI ξ n)
    (e : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdI (fun _ => False) S) e f (killX φ) ↔
      Semiformula.Eval (s := stdI (fun _ => False) S) e f φ := by
  induction φ using Semiformula.rec' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v =>
    rcases r with r | r
    · exact Iff.rfl
    · cases r
      · show Semiformula.Eval (s := stdI (fun _ => False) S) e f ⊥ ↔ _
        simp only [LogicalConnective.HomClass.map_bot, Prop.bot_eq_false, false_iff]
        exact fun h => h
      · exact Iff.rfl
  | hnrel r v =>
    rcases r with r | r
    · exact Iff.rfl
    · cases r
      · show Semiformula.Eval (s := stdI (fun _ => False) S) e f ⊤ ↔ _
        simp only [LogicalConnective.HomClass.map_top, Prop.top_eq_true, true_iff]
        exact fun h => h
      · exact Iff.rfl
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

/-- **The embedding reads `X` and `I` as empty.** -/
theorem eval_embK {ξ : Type*} {n : ℕ} (φ : Semiformula LXI ξ n) (e : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdInf) e f (embK φ) ↔
      Semiformula.Eval (s := stdI (fun _ => False) ∅) e f φ := by
  rw [embK, embed, Semiformula.eval_lMap, stdInf_lMap_eq]
  exact eval_killX_stdI ∅ φ e f

/-- A sentence true in `stdI` (with `X` and `I` empty) has a true embedding. -/
theorem trueN_emb_embK {σ : Sentence LXI}
    (h : Semiformula.Eval (s := stdI (fun _ => False) ∅) ![] Empty.elim σ) :
    TrueN (Rewriting.emb (embK σ) : Proposition LIinf) := by
  unfold TrueN
  rw [Semiformula.eval_emb]
  exact (eval_embK σ ![] Empty.elim).mpr h

end Semantics

/-! ### The universal closure, by the ω-rule -/

section Closure

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting

variable {A : Semisentence LXI 1} {ρ : ThetaNote} {H : Set ThetaNote → Set ThetaNote}

/-- Composing a lifted `k`-ary substitution with a one-point substitution. -/
theorem subst_q_subst {k : ℕ} (σ : Semiformula LIinf ℕ (k + 1))
    (v : Fin k → SyntacticTerm LIinf) (t : SyntacticTerm LIinf) :
    ((Rew.subst v).q ▹ σ)/[t] = σ ⇜ (t :> v) := by
  have hrew : (Rew.subst ![t]).comp ((Rew.subst v).q) = Rew.subst (t :> v) := by
    rw [Rew.q_subst, Rew.subst_comp_subst]
    congr 1
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  simpa [← comp_app] using smul_ext' (φ := σ) hrew

theorem allClosure_aux (hH : ThetaNote.IsOperator H) (β : ThetaNote)
    (hβ : ∀ j : ℕ, ThetaNote.nadd β (ThetaNote.ofNat j) ∈ H ∅) :
    ∀ (k j : ℕ) (σ : Semiformula LIinf ℕ k), params σ ⊆ H ∅ →
      (∀ w : Fin k → ℕ, IDerivable A ρ H (ThetaNote.nadd β (ThetaNote.ofNat j))
        [σ ⇜ fun i => numI (w i)]) →
      IDerivable A ρ H (ThetaNote.nadd β (ThetaNote.ofNat (j + k))) [∀¹* σ] := by
  intro k
  induction k with
  | zero =>
    intro j σ _ h
    have e : (σ ⇜ fun i : Fin 0 => numI (Fin.elim0 i)) = σ := by simp
    have h0 := h Fin.elim0
    rw [e] at h0
    exact h0
  | succ k ih =>
    intro j σ hP h
    rw [show j + (k + 1) = (j + 1) + k by omega]
    refine ih (j + 1) (∀¹ σ) hP (fun w => ?_)
    have hall : ((∀¹ σ) ⇜ fun i => numI (w i)) =
        ∀¹ ((Rew.subst fun i => numI (w i)).q ▹ σ) := by
      rw [show ((∀¹ σ) ⇜ fun i => numI (w i)) = (Rew.subst fun i => numI (w i)) ▹ (∀¹ σ)
        from rfl, Rewriting.app_all]
    rw [hall]
    have hPs : paramsList [∀¹ ((Rew.subst fun i => numI (w i)).q ▹ σ)] ⊆ H ∅ := by
      simp only [paramsList_cons, paramsList_nil, Set.union_empty, params_all, params_rew]
      exact hP
    refine .all (fun _ => ThetaNote.nadd β (ThetaNote.ofNat j)) (hβ _) hPs List.mem_cons_self
      (fun _ => ThetaNote.nadd_ofNat_lt_nadd_ofNat _ (Nat.lt_succ_self j)) (fun n => ?_)
    rw [subst_q_subst]
    have hv : ((numI n : SyntacticTerm LIinf) :> fun i => numI (w i)) =
        fun i => numI (((n :> w) : Fin (k + 1) → ℕ) i) := by
      funext i
      induction i using Fin.cases with
      | zero => simp
      | succ j => simp
    rw [hv]
    refine (h (n :> w)).weaken_seq hH (List.cons_subset_cons _ (List.nil_subset _)) ?_
    simp only [paramsList_cons, paramsList_nil, Set.union_empty, params_all, params_rew]
    exact Set.union_subset hP hP

/-- **The universal closure**: a `k`-ary matrix whose simultaneous numeral instances are
derivable at height `β` is derivable, closed, at height `β ⊕ k`. -/
theorem allClosure_derivable (hH : ThetaNote.IsOperator H) {k : ℕ}
    (σ : Semiformula LIinf ℕ k) {β : ThetaNote}
    (hβ : ∀ j : ℕ, ThetaNote.nadd β (ThetaNote.ofNat j) ∈ H ∅) (hP : params σ ⊆ H ∅)
    (h : ∀ w : Fin k → ℕ, IDerivable A ρ H β [σ ⇜ fun i => numI (w i)]) :
    IDerivable A ρ H (ThetaNote.nadd β (ThetaNote.ofNat k)) [∀¹* σ] := by
  have key := allClosure_aux (A := A) (ρ := ρ) hH β hβ k 0 σ hP (fun w => by
    rw [ThetaNote.ofNat_zero, ThetaNote.nadd_zero]; exact h w)
  rwa [Nat.zero_add] at key

end Closure

/-! ### The axioms of equality and of `𝗣𝗔⁻` -/

section EqPA

variable {A : Semisentence LXI 1} {H : Set ThetaNote → Set ThetaNote}

/-- `Ω · 2 = Ω ⊕ Ω`. -/
abbrev OmegaTwo : ThetaNote := ThetaNote.nadd ThetaNote.Omega ThetaNote.Omega

/-- **The axiom `σ` is derivable** in the form of Freund, proof of Theorem 6.5: cut-free, at
a height `Ω · 2 + n` independent of the nice operator. -/
def AxDerivable (A : Semisentence LXI 1) (σ : Sentence LXI) : Prop :=
  ∃ n : ℕ, ∀ H : Set ThetaNote → Set ThetaNote, ThetaNote.Nice H →
    IDerivable A ThetaNote.zero H (ThetaNote.nadd OmegaTwo (ThetaNote.ofNat n))
      [(Rewriting.emb (embK σ) : Proposition LIinf)]

theorem OmegaTwo_mem (hH : ThetaNote.Nice H) (X : Set ThetaNote) (n : ℕ) :
    ThetaNote.nadd OmegaTwo (ThetaNote.ofNat n) ∈ H X :=
  hH.nadd_mem (hH.nadd_mem hH.Omega_mem hH.Omega_mem) (hH.ofNat_mem n)

theorem axDerivable_of_le {σ : Sentence LXI} (n : ℕ) (h : ThetaNote)
    (hle : h ≤ ThetaNote.nadd OmegaTwo (ThetaNote.ofNat n))
    (d : ∀ H : Set ThetaNote → Set ThetaNote, ThetaNote.Nice H →
      IDerivable A ThetaNote.zero H h [(Rewriting.emb (embK σ) : Proposition LIinf)]) :
    AxDerivable A σ :=
  ⟨n, fun H hH => (d H hH).mono_height hle (OmegaTwo_mem hH _ n)⟩

theorem Omega_le_OmegaTwo_nadd (n : ℕ) :
    ThetaNote.Omega ≤ ThetaNote.nadd OmegaTwo (ThetaNote.ofNat n) :=
  le_trans (ThetaNote.le_nadd_left _ _) (ThetaNote.le_nadd_left _ _)

theorem omegaT_lt_Omega (c : ℕ) : ThetaNote.nadd omegaT (ThetaNote.ofNat c) < ThetaNote.Omega :=
  ThetaNote.nadd_lt_Omega
    (ThetaNote.omegaPow_lt_Omega (ThetaNote.one_lt_prin (p := ThetaNote.Omega) trivial))
    (ThetaNote.ofNat_lt_prin (p := ThetaNote.Omega) trivial c)

/-- A formula of `LXI` without the predicate `I`. -/
def IFreeL {ξ : Type*} : {n : ℕ} → Semiformula LXI ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel (Sum.inl _) _ => True
  | _, .rel (Sum.inr IXRel.X) _ => True
  | _, .rel (Sum.inr IXRel.I) _ => False
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr IXRel.X) _ => True
  | _, .nrel (Sum.inr IXRel.I) _ => False
  | _, .and φ ψ => IFreeL φ ∧ IFreeL ψ
  | _, .or φ ψ => IFreeL φ ∧ IFreeL ψ
  | _, .all φ => IFreeL φ
  | _, .exs φ => IFreeL φ

/-- Without `I`, the embedding is arithmetic (`X` is read as empty). -/
theorem arithF_embK {ξ : Type*} {n : ℕ} :
    ∀ (φ : Semiformula LXI ξ n), IFreeL φ → ArithF (embK φ)
  | .verum, _ => by show ArithF (embK (⊤ : Semiformula LXI ξ n)); rw [embK_verum]; trivial
  | .falsum, _ => by show ArithF (embK (⊥ : Semiformula LXI ξ n)); rw [embK_falsum]; trivial
  | .rel (Sum.inl r) _, _ => ⟨r, rfl⟩
  | .rel (Sum.inr IXRel.X) _, _ => by
    show ArithF (embK (⊥ : Semiformula LXI ξ n)); rw [embK_falsum]; trivial
  | .rel (Sum.inr IXRel.I) _, h => h.elim
  | .nrel (Sum.inl r) _, _ => ⟨r, rfl⟩
  | .nrel (Sum.inr IXRel.X) _, _ => by
    show ArithF (embK (⊤ : Semiformula LXI ξ n)); rw [embK_verum]; trivial
  | .nrel (Sum.inr IXRel.I) _, h => h.elim
  | .and φ ψ, h => by
    show ArithF (embK (φ ⋏ ψ)); rw [embK_and]; exact ⟨arithF_embK φ h.1, arithF_embK ψ h.2⟩
  | .or φ ψ, h => by
    show ArithF (embK (φ ⋎ ψ)); rw [embK_or]; exact ⟨arithF_embK φ h.1, arithF_embK ψ h.2⟩
  | .all φ, h => by
    show ArithF (embK (∀¹ φ)); rw [embK_all]; exact arithF_embK φ h
  | .exs φ, h => by
    show ArithF (embK (∃¹ φ)); rw [embK_exs]; exact arithF_embK φ h

@[simp] theorem iFreeL_neg {ξ : Type*} {n : ℕ} (φ : Semiformula LXI ξ n) :
    IFreeL (∼φ) ↔ IFreeL φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v => rcases r with r | r; · exact Iff.rfl
                cases r <;> exact Iff.rfl
  | hnrel r v => rcases r with r | r; · exact Iff.rfl
                 cases r <;> exact Iff.rfl
  | hand φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | hor φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | hall φ ih => exact ih
  | hexs φ ih => exact ih

theorem iFreeL_imp {ξ : Type*} {n : ℕ} (φ ψ : Semiformula LXI ξ n) :
    IFreeL (φ 🡒 ψ) ↔ IFreeL φ ∧ IFreeL ψ := by
  have h : (φ 🡒 ψ) = ∼φ ⋎ ψ := rfl
  rw [h]
  exact and_congr (iFreeL_neg φ) Iff.rfl

theorem iFreeL_allClosure {ξ : Type*} :
    ∀ {n : ℕ} (φ : Semiformula LXI ξ n), IFreeL φ → IFreeL (∀¹* φ)
  | 0, _, h => h
  | _ + 1, φ, h => iFreeL_allClosure (∀¹ φ) h

theorem iFreeL_conj {ξ : Type*} {n : ℕ} :
    ∀ {k : ℕ} (v : Fin k → Semiformula LXI ξ n), (∀ i, IFreeL (v i)) → IFreeL (Matrix.conj v)
  | 0, _, _ => trivial
  | _ + 1, v, h => ⟨h 0, iFreeL_conj (Matrix.vecTail v) fun i => h i.succ⟩

theorem iFreeL_eqOp {ξ : Type*} {n : ℕ} (t u : Semiterm LXI ξ n) :
    IFreeL ((Semiformula.Operator.Eq.eq : Semiformula.Operator LXI 2).operator ![t, u]) := by
  rw [Semiformula.Operator.eq_def]
  trivial

theorem iFreeL_eqRefl : IFreeL (Theory.Eq.refl LXI) :=
  iFreeL_eqOp (ξ := Empty) (#0 : Semiterm LXI Empty 1) #0

theorem iFreeL_eqSymm : IFreeL (Theory.Eq.symm LXI) :=
  (iFreeL_imp _ _).mpr ⟨iFreeL_eqOp _ _, iFreeL_eqOp _ _⟩

theorem iFreeL_eqTrans : IFreeL (Theory.Eq.trans LXI) :=
  (iFreeL_imp _ _).mpr ⟨iFreeL_eqOp _ _, (iFreeL_imp _ _).mpr ⟨iFreeL_eqOp _ _, iFreeL_eqOp _ _⟩⟩

theorem iFreeL_funcExt {k : ℕ} (f : LXI.Func k) : IFreeL (Theory.Eq.funcExt f) :=
  iFreeL_allClosure _ ((iFreeL_imp _ _).mpr
    ⟨iFreeL_conj _ (fun _ => iFreeL_eqOp _ _), iFreeL_eqOp _ _⟩)

theorem iFreeL_relExt_inl {k : ℕ} (r : (ℒₒᵣ : Language).Rel k) :
    IFreeL (Theory.Eq.relExt (Sum.inl r : LXI.Rel k)) :=
  iFreeL_allClosure _ ((iFreeL_imp _ _).mpr
    ⟨iFreeL_conj _ (fun _ => iFreeL_eqOp _ _), (iFreeL_imp _ _).mpr ⟨trivial, trivial⟩⟩)

theorem iFreeL_relExt_X : IFreeL (Theory.Eq.relExt (Sum.inr IXRel.X : LXI.Rel 1)) :=
  iFreeL_allClosure _ ((iFreeL_imp _ _).mpr
    ⟨iFreeL_conj _ (fun _ => iFreeL_eqOp _ _), (iFreeL_imp _ _).mpr ⟨trivial, trivial⟩⟩)

theorem iFreeL_lMap_toLXI {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) :
    IFreeL (Semiformula.lMap toLXI φ) := by
  induction φ using Semiformula.rec' with
  | hverum => simp only [LogicalConnective.HomClass.map_top]; trivial
  | hfalsum => simp only [LogicalConnective.HomClass.map_bot]; trivial
  | hrel r v => trivial
  | hnrel r v => trivial
  | hand φ ψ ihφ ihψ => rw [LogicalConnective.HomClass.map_and]; exact ⟨ihφ, ihψ⟩
  | hor φ ψ ihφ ihψ => rw [LogicalConnective.HomClass.map_or]; exact ⟨ihφ, ihψ⟩
  | hall φ ih => rw [Semiformula.lMap_all]; exact ih
  | hexs φ ih => rw [Semiformula.lMap_exs]; exact ih

/-- **An `I`-free sentence true in `ℕ`** (with `X` and `I` read as empty) is an axiom derivable
at height `ω ⊕ c`. -/
theorem axDerivable_of_iFree {σ : Sentence LXI} (hI : IFreeL σ)
    (ht : Semiformula.Eval (s := stdI (fun _ => False) ∅) ![] Empty.elim σ) :
    AxDerivable A σ := by
  refine axDerivable_of_le 0 (ThetaNote.nadd omegaT
    (ThetaNote.ofNat (Rewriting.emb (embK σ) : Proposition LIinf).complexity))
    (le_of_lt (lt_of_lt_of_le (omegaT_lt_Omega _) (Omega_le_OmegaTwo_nadd 0))) (fun H hH => ?_)
  exact omega_complete hH _ _ le_rfl (arithF_rew _ (arithF_embK σ hI))
    (Semiformula.freeVariables_emb _) (trueN_emb_embK ht)

/-- **The axioms of `𝗣𝗔⁻`** (Freund, proof of Theorem 6.5, after Theorem 3.7 of the first
lecture). -/
theorem paMinus_axiom {σ : Sentence LXI} (h : σ ∈ Theory.lMap toLXI 𝗣𝗔⁻) : AxDerivable A σ := by
  obtain ⟨τ, hτ, rfl⟩ := h
  exact axDerivable_of_iFree (iFreeL_lMap_toLXI τ)
    (eval_of_paMinus (fun _ => False) ∅ ⟨τ, hτ, rfl⟩)

/-! #### The equality axiom for `I` -/

/-- `t = u` in `LXI`. -/
def eqX {ξ : Type*} {n : ℕ} (t u : Semiterm LXI ξ n) : Semiformula LXI ξ n :=
  Semiformula.rel (Language.Eq.eq : LXI.Rel 2) ![t, u]

/-- `t = u` in `LIinf`. -/
def eqI {ξ : Type*} {n : ℕ} (t u : Semiterm LIinf ξ n) : Semiformula LIinf ξ n :=
  Semiformula.rel (Language.Eq.eq : LIinf.Rel 2) ![t, u]

/-- The matrix of the equality axiom for `I`. -/
def relI2S : Semisentence LXI 2 :=
  ∼(eqX (#0 : Semiterm LXI Empty 2) #1 ⋏ ⊤) ⋎
    (∼(Iat (#0 : Semiterm LXI Empty 2)) ⋎ Iat (#1 : Semiterm LXI Empty 2))

theorem relExtI_eq :
    (Theory.Eq.relExt (Sum.inr IXRel.I : LXI.Rel 1) : Sentence LXI) = ∀¹ (∀¹ relI2S) := by
  have hv0 : (fun i : Fin 1 ↦ (#(i.addCast 1) : Semiterm LXI Empty 2))
      = ![(#0 : Semiterm LXI Empty 2)] := funext (Fin.forall_fin_one.mpr rfl)
  have hv1 : (fun i : Fin 1 ↦ (#(i.addNat 1) : Semiterm LXI Empty 2))
      = ![(#1 : Semiterm LXI Empty 2)] := funext (Fin.forall_fin_one.mpr rfl)
  have hB : Semiformula.rel (Sum.inr IXRel.I : LXI.Rel 1)
        (fun i : Fin 1 ↦ (#(i.addCast 1) : Semiterm LXI Empty 2))
      = Iat (#0 : Semiterm LXI Empty 2) :=
    congrArg (fun v : Fin 1 → Semiterm LXI Empty 2 =>
        Semiformula.rel (Sum.inr IXRel.I : LXI.Rel 1) v) hv0
  have hC : Semiformula.rel (Sum.inr IXRel.I : LXI.Rel 1)
        (fun i : Fin 1 ↦ (#(i.addNat 1) : Semiterm LXI Empty 2))
      = Iat (#1 : Semiterm LXI Empty 2) :=
    congrArg (fun v : Fin 1 → Semiterm LXI Empty 2 =>
        Semiformula.rel (Sum.inr IXRel.I : LXI.Rel 1) v) hv1
  show (∀¹* ((Matrix.conj fun i : Fin 1 ↦
      (eqX (#(i.addCast 1) : Semiterm LXI Empty 2) (#(i.addNat 1)))) 🡒
      (Semiformula.rel (Sum.inr IXRel.I : LXI.Rel 1)
          (fun i : Fin 1 ↦ (#(i.addCast 1) : Semiterm LXI Empty 2)) 🡒
        Semiformula.rel (Sum.inr IXRel.I : LXI.Rel 1)
          (fun i : Fin 1 ↦ (#(i.addNat 1) : Semiterm LXI Empty 2)))) : Sentence LXI)
      = ∀¹ (∀¹ relI2S)
  rw [hB, hC]
  rfl

theorem embK_eqX {ξ : Type*} {n : ℕ} (t u : Semiterm LXI ξ n) :
    embK (eqX t u) = eqI (embT t) (embT u) :=
  congrArg (Semiformula.rel (Language.Eq.eq : LIinf.Rel 2))
    (funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩))

@[simp] theorem rew_eqI {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LIinf ξ₁ n₁ ξ₂ n₂)
    (t u : Semiterm LIinf ξ₁ n₁) : ω ▹ (eqI t u) = eqI (ω t) (ω u) := Semiformula.rew_rel2 ω

@[simp] theorem rew_IOmegaAt {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LIinf ξ₁ n₁ ξ₂ n₂)
    (t : Semiterm LIinf ξ₁ n₁) : ω ▹ (IOmegaAt t) = IOmegaAt (ω t) := Semiformula.rew_rel1 ω

/-- The matrix of the equality axiom for `I`, embedded. -/
def relI2 : Semiformula LIinf ℕ 2 :=
  ∼(eqI (#0 : Semiterm LIinf ℕ 2) #1 ⋏ ⊤) ⋎
    (∼(IOmegaAt (#0 : Semiterm LIinf ℕ 2)) ⋎ IOmegaAt (#1 : Semiterm LIinf ℕ 2))

/-- The matrix at the numerals `a`, `b`. -/
def relI0 (a b : ℕ) : Proposition LIinf :=
  ∼(eqI (numI a) (numI b) ⋏ ⊤) ⋎ (∼(IOmegaAt (numI a)) ⋎ IOmegaAt (numI b))

theorem emb_embK_relI2S : (Rewriting.emb (embK relI2S) : Semiformula LIinf ℕ 2) = relI2 := by
  simp only [relI2S, embK_or, embK_and, embK_neg, embK_verum, embK_eqX, embK_Iat, relI2,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_top, rew_eqI,
    rew_IOmegaAt, embT, Semiterm.lMap_bvar, Rew.emb_bvar]

theorem emb_embK_relExtI :
    (Rewriting.emb (embK (Theory.Eq.relExt (Sum.inr IXRel.I : LXI.Rel 1))) : Proposition LIinf)
      = ∀¹* relI2 := by
  rw [relExtI_eq, embK_all, embK_all, ← emb_embK_relI2S]
  simp only [Rewriting.app_all, Rew.q_emb]
  rfl

theorem relI2_inst (w : Fin 2 → ℕ) : (relI2 ⇜ fun i => numI (w i)) = relI0 (w 0) (w 1) := by
  simp [relI2, relI0]

theorem trueLit_neqI {a b : ℕ} (h : a ≠ b) : TrueLit (∼(eqI (numI a) (numI b))) := by
  have hl : IsArithLit (eqI (numI a) (numI b)) :=
    ⟨2, Language.Eq.eq, ![numI a, numI b], Or.inl rfl, fun i => by
      match i with
      | ⟨0, _⟩ => exact numI_freeVariables a
      | ⟨1, _⟩ => exact numI_freeVariables b⟩
  refine ⟨hl.neg, (trueN_neg _).mpr ?_⟩
  unfold TrueN eqI
  rw [Semiformula.eval_rel]
  show ¬ (Semiterm.val (s := stdInf) ![] (fun _ => 0) (numI a) =
    Semiterm.val (s := stdInf) ![] (fun _ => 0) (numI b))
  rw [val_numI, val_numI]
  exact h

theorem freeVariables_IOmegaAt_numI (a : ℕ) : (IOmegaAt (numI a)).freeVariables = ∅ := by
  ext x
  simp [IOmegaAt, stageAt, Semiformula.freeVariables, numI_freeVariables]

@[simp] theorem relParams_eq : relParams (Language.Eq.eq : LIinf.Rel 2) = ∅ := rfl

@[simp] theorem params_eqI {ξ : Type*} {n : ℕ} (t u : Semiterm LIinf ξ n) :
    params (eqI t u) = ∅ := rfl

/-- The instance of the equality axiom for `I` at `a`, `b`: `a ≠ b` is a true literal, and for
`a = b` Lemma 6.1 applies (Freund, proof of Theorem 6.5). -/
theorem relI0_derivable (hH : ThetaNote.Nice H) (a b : ℕ) :
    IDerivable A ThetaNote.zero H (ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat 3))
      [relI0 a b] := by
  have hm : ∀ k, ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat k) ∈ H ∅ :=
    fun k => hH.nadd_mem hH.Omega_mem (hH.ofNat_mem k)
  have hΩ : ThetaNote.Omega ∈ H ∅ := hH.Omega_mem
  have hPm : ∀ Γ : Sequent LIinf, (∀ φ ∈ Γ, params φ ⊆ {ThetaNote.Omega}) →
      paramsList Γ ⊆ H ∅ := by
    intro Γ h x ⟨φ, hφ, hx⟩
    rw [Set.mem_singleton_iff.mp (h φ hφ hx)]; exact hΩ
  have pM : params (relI0 a b) ⊆ {ThetaNote.Omega} := by
    intro x hx
    simp [relI0, IOmegaAt] at hx
    exact hx
  have hlt : ∀ j k : ℕ, j < k → ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat j) <
      ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat k) :=
    fun j k h => ThetaNote.nadd_ofNat_lt_nadd_ofNat _ h
  have hone : ∀ k, ThetaNote.one < ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat k) :=
    fun k => lt_of_lt_of_le (ThetaNote.one_lt_prin (p := ThetaNote.Omega) trivial)
      (ThetaNote.le_nadd_left _ _)
  have h0 : ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat 0) = ThetaNote.Omega := by
    rw [ThetaNote.ofNat_zero, ThetaNote.nadd_zero]
  have hlt0 : ThetaNote.Omega < ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat 1) := by
    have := hlt 0 1 (by omega); rwa [h0] at this
  by_cases hab : a = b
  · subst hab
    have d0 := taut (A := A) hH (IOmegaAt (numI a)) (freeVariables_IOmegaAt_numI a)
    rw [params_IOmegaAt, rk_IOmegaAt, ThetaNote.omegaMul_Omega,
      ThetaNote.adjoin_eq_self hH.isOperator (Set.singleton_subset_iff.mpr hΩ)] at d0
    set P : Proposition LIinf := ∼(IOmegaAt (numI a)) with hP
    set Q : Proposition LIinf := IOmegaAt (numI a) with hQ
    set N : Proposition LIinf := ∼(eqI (numI a) (numI a) ⋏ ⊤) with hN
    have eM : relI0 a a = N ⋎ (P ⋎ Q) := rfl
    have pP : params P ⊆ {ThetaNote.Omega} := by rw [hP, params_neg, params_IOmegaAt]
    have pQ : params Q ⊆ {ThetaNote.Omega} := by rw [hQ, params_IOmegaAt]
    have pD : params (P ⋎ Q) ⊆ {ThetaNote.Omega} := by
      rw [params_or]; exact Set.union_subset pP pQ
    have d1 : IDerivable A ThetaNote.zero H ThetaNote.Omega [Q, P, P ⋎ Q, relI0 a a] :=
      d0.weaken_seq hH.isOperator
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto)
        (hPm _ (by
          intro φ hφ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
          rcases hφ with rfl | rfl | rfl | rfl
          · exact pQ
          · exact pP
          · exact pD
          · exact pM))
    have d2 : IDerivable A ThetaNote.zero H (ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat 1))
        [P, P ⋎ Q, relI0 a a] :=
      .orR (hm 1) (hPm _ (by
          intro φ hφ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
          rcases hφ with rfl | rfl | rfl
          · exact pP
          · exact pD
          · exact pM))
        (List.mem_cons_of_mem _ List.mem_cons_self) (hone 1)
        hlt0 d1
    have d3 : IDerivable A ThetaNote.zero H (ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat 2))
        [P ⋎ Q, relI0 a a] :=
      .orL (hm 2) (hPm _ (by
          intro φ hφ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
          rcases hφ with rfl | rfl
          · exact pD
          · exact pM))
        List.mem_cons_self (hlt 1 2 (by omega)) d2
    exact .orR (hm 3) (hPm _ (by
        intro φ hφ
        rw [List.mem_singleton.mp hφ]; exact pM))
      (by rw [eM]; exact List.mem_cons_self) (hone 3) (hlt 2 3 (by omega)) d3
  · set N : Proposition LIinf := ∼(eqI (numI a) (numI b) ⋏ ⊤) with hN
    have eN : N = ∼(eqI (numI a) (numI b)) ⋎ ⊥ := by rw [hN]; simp
    have pN : params N ⊆ {ThetaNote.Omega} := by
      rw [eN]; simp [eqI]
    have pE : params (∼(eqI (numI a) (numI b))) ⊆ {ThetaNote.Omega} := by simp [eqI]
    have e1 : IDerivable A ThetaNote.zero H ThetaNote.Omega
        [∼(eqI (numI a) (numI b)), N, relI0 a b] :=
      .literal hΩ (hPm _ (by
          intro φ hφ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
          rcases hφ with rfl | rfl | rfl
          · exact pE
          · exact pN
          · exact pM))
        (trueLit_neqI hab) List.mem_cons_self
    have e2 : IDerivable A ThetaNote.zero H (ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat 1))
        [N, relI0 a b] :=
      .orL (hm 1) (hPm _ (by
          intro φ hφ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
          rcases hφ with rfl | rfl
          · exact pN
          · exact pM))
        (by rw [← eN]; exact List.mem_cons_self) hlt0 e1
    have e3 : IDerivable A ThetaNote.zero H (ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat 2))
        [relI0 a b] :=
      .orL (hm 2) (hPm _ (by
          intro φ hφ
          rw [List.mem_singleton.mp hφ]; exact pM))
        List.mem_cons_self (hlt 1 2 (by omega)) e2
    exact e3.mono_height (le_of_lt (hlt 2 3 (by omega))) (hm 3)

/-- **The equality axiom for `I`** (Freund, proof of Theorem 6.5). -/
theorem relExtI_axiom : AxDerivable A (Theory.Eq.relExt (Sum.inr IXRel.I : LXI.Rel 1)) := by
  refine axDerivable_of_le 5 (ThetaNote.nadd (ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat 3))
    (ThetaNote.ofNat 2)) ?_ (fun H hH => ?_)
  · rw [ThetaNote.nadd_assoc, ThetaNote.ofNat_nadd_ofNat]
    exact ThetaNote.nadd_le_nadd_left' _ (ThetaNote.le_nadd_left _ _)
  · rw [emb_embK_relExtI]
    refine allClosure_derivable hH.isOperator relI2
      (fun j => hH.nadd_mem (hH.nadd_mem hH.Omega_mem (hH.ofNat_mem 3)) (hH.ofNat_mem j))
      (by intro x hx; simp [relI2, eqI, IOmegaAt] at hx; rw [hx]; exact hH.Omega_mem)
      (fun w => ?_)
    rw [relI2_inst]
    exact relI0_derivable hH _ _

/-- **The equality axioms** (Freund, proof of Theorem 6.5). -/
theorem eq_axiom {σ : Sentence LXI} (h : σ ∈ 𝗘𝗤 LXI) : AxDerivable A σ := by
  have ht := eval_of_eqAxiom (fun _ => False) ∅ h
  cases h with
  | refl => exact axDerivable_of_iFree iFreeL_eqRefl ht
  | symm => exact axDerivable_of_iFree iFreeL_eqSymm ht
  | trans => exact axDerivable_of_iFree iFreeL_eqTrans ht
  | funcExt f => exact axDerivable_of_iFree (iFreeL_funcExt f) ht
  | relExt r =>
    cases r with
    | inl r => exact axDerivable_of_iFree (iFreeL_relExt_inl r) ht
    | inr r =>
      cases r with
      | X => exact axDerivable_of_iFree iFreeL_relExt_X ht
      | I => exact relExtI_axiom

end EqPA

end InductiveDef

end OrdinalAnalysis
