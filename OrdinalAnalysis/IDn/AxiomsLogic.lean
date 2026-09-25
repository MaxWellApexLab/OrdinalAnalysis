/-
  The tautology lemma and the logical and arithmetical axioms of `ID_{<ω}`, `n` simultaneous
  inductive definitions with stage predicates `I_k^{≺α}`, `k : Fin n`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §6: Lemma 6.1, and the proof of Theorem 6.5 (the
  axioms of `PA ⊆ ID₁` "treated as in the proof of Theorem 3.7 of the first lecture", and
  the equality axiom for `I_φ`). As ported by `ID1/AxiomsLogic.lean`, generalised to `n`
  levels: Lemma 6.1 and the arithmetic completeness are level-free (the stage clause of
  Lemma 6.1 now carries an explicit level `k`, unfolding through `A k`); the equality axiom
  for `I` is level-indexed, one instance per `k : Fin n`.

  **Lemma 6.1** (`taut`): `H[k(ψ)] ⊢^{ω·rk(ψ)}_0 ψ, ¬ψ` for every closed `ψ` and every nice
  `H`.  By induction on `rk ψ` (well-founded, since the unfolding `A_k(t, I_k^{≺γ})` of a
  stage atom is not a subformula).  For the conjunctive `ψ ≃ ⋀_{γ≺δ} ψ_γ` the premise for `γ`
  is obtained by clause (W) on `¬ψ ≃ ⋁_{γ≺δ} ¬ψ_γ` at a height `α(γ)` with `γ ≺ α(γ)` and
  `α(γ) ≺ ω · rk ψ`; the disjunctive shapes are the conjunctive ones read backwards.  The
  closed formulas are those without free variables; the clause `idX` handles the literals
  of the free predicate `X`.  Heights: Freund's `α(γ) = max{ω·rk ψ_γ, γ} + 1`; for the
  finite indices `i ≺ 2` and `m ≺ ω` the equivalent `ω · rk ψ_γ ⊕ (γ + 1)` is used.

  **The arithmetical axioms.**  A closed formula without stage atoms and without `X`
  (`ArithF`) that is true in `ℕ` is derivable at height `ω ⊕ c`, `c` its complexity
  (`omega_complete`; the ω-rule for `∀`, a numeral witness for `∃`).  Through the reading
  of `X` and every level's `I` as empty (`trueN_embK`) this gives every axiom of `𝗣𝗔⁻` and
  every equality axiom except the ones for `I_k` (`paMinus_axiom`, `eq_axiom`).  The
  equality axiom for `I_k`, at every level `k`, is derived by hand as in Freund: for
  distinct numerals `p ≠ q` is a true literal, and for equal ones Lemma 6.1 applies
  (`relExtI_derivable`).

  Contents.

    height arithmetic: `succ_max_lt`, `omegaMul_nadd_lt_omegaMul_succ`, …
    `taut_and`, `taut_all`, `taut_stage`, `taut`       **Lemma 6.1**
    `ArithF`, `trueN_all`, `trueN_exs`, `omega_complete`
    `trueN_embK`                                       `X`, every level's `I` read as empty
    `allClosure_derivable`                             the universal closure, by the ω-rule
    `IFreeL`, `paMinus_axiom`, `eq_axiom`, `relExtI_derivable`
-/
import OrdinalAnalysis.IDn.Evaluate
import OrdinalAnalysis.IDn.NumSubst
import OrdinalAnalysis.IDn.Sound

set_option autoImplicit false

namespace OrdinalAnalysis

variable {n : ℕ}

/-! ### Height arithmetic -/

namespace ThetaWNoteD

/-- Convenience projection, matching `Nice.isOperator`'s ergonomics for the level-free `NiceS`
(`Ordinal/ThetaW/HullSingle.lean` does not itself register one; not duplicated elsewhere). -/
theorem NiceS.isOperator {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : NiceS H) : IsOperator H :=
  hH.1

/-- The finite notations lie below `ω = ω^1`. -/
theorem ofNat_lt_omega (p : ℕ) : ofNat p < omegaPow one := by
  rw [lt_omegaPow_iff, entries_ofNat]
  intro e he
  rw [List.eq_of_mem_replicate he]
  exact zero_lt_one

theorem nadd_ofNat_one (a : ThetaWNoteD) : ThetaWNoteD.nadd a (ofNat 1) = succ a := by
  rw [ofNat_one]; rfl

theorem succ_max_lt {p q B : ThetaWNoteD} (hp : succ p < B) (hq : succ q < B) :
    succ (max p q) < B := by
  rcases le_total p q with h | h
  · rw [max_eq_right h]; exact hq
  · rw [max_eq_left h]; exact hp

/-- `ω · x ⊕ p ≺ ω · (m + 1)` for `x ⪯ m`. -/
theorem omegaMul_nadd_lt_omegaMul_succ {x m : ThetaWNoteD} (h : x ≤ m) (p : ℕ) :
    ThetaWNoteD.nadd (omegaMul x) (ofNat p) < omegaMul (succ m) :=
  omegaMul_nadd_ofNat_lt (lt_of_le_of_lt h (lt_succ m)) p

/-- `p ≺ ω · (m + 1)`. -/
theorem ofNat_lt_omegaMul_succ (m : ThetaWNoteD) (p : ℕ) : ofNat p < omegaMul (succ m) := by
  have h := omegaMul_nadd_ofNat_lt (lt_of_le_of_lt (zero_le' m) (lt_succ m)) p
  rwa [omegaMul_zero, zero_nadd] at h

/-- `γ + 1 ≺ ω · ω · δ` for `γ ≺ δ`: the stage weight in Lemma 6.1. -/
theorem succ_lt_omegaMul_omegaMul {g a : ThetaWNoteD} (h : g < a) :
    succ g < omegaMul (omegaMul a) := by
  have h1 : succ g ≤ succ (omegaMul g) := succ_le_succ (ThetaWNoteD.le_omegaMul g)
  have h2 : succ (omegaMul g) < omegaMul a := by
    rw [← nadd_ofNat_one]; exact omegaMul_nadd_ofNat_lt h 1
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (ThetaWNoteD.le_omegaMul _))

theorem succ_omegaMul_lt {x y : ThetaWNoteD} (h : x < y) : succ (omegaMul x) < omegaMul y := by
  rw [← nadd_ofNat_one]; exact omegaMul_nadd_ofNat_lt h 1

theorem lt_nadd_ofNat_succ (a : ThetaWNoteD) (p : ℕ) : a < ThetaWNoteD.nadd a (ofNat (p + 1)) :=
  lt_of_lt_of_le (lt_succ a) (by
    rw [← nadd_ofNat_one]
    exact nadd_le_nadd_right a (ofNat_le_ofNat (by omega)))

theorem ofNat_lt_nadd_ofNat_succ (a : ThetaWNoteD) (p : ℕ) :
    ofNat p < ThetaWNoteD.nadd a (ofNat (p + 1)) :=
  lt_of_lt_of_le (ofNat_lt_ofNat (Nat.lt_succ_self p)) (le_nadd_right _ _)

theorem nadd_ofNat_lt_nadd_ofNat' (a : ThetaWNoteD) {j p : ℕ} (h : j < p) :
    ThetaWNoteD.nadd a (ofNat j) < ThetaWNoteD.nadd a (ofNat p) :=
  nadd_lt_nadd_right a (ofNat_lt_ofNat h)

theorem one_lt_nadd_ofNat_two (a : ThetaWNoteD) : one < ThetaWNoteD.nadd a (ofNat 2) := by
  rw [← ofNat_one]; exact ofNat_lt_nadd_ofNat_succ a 1

theorem ofNat_nadd_ofNat (p : ℕ) : ∀ q : ℕ, ThetaWNoteD.nadd (ofNat p) (ofNat q) = ofNat (p + q)
  | 0 => by rw [ofNat_zero, nadd_zero, Nat.add_zero]
  | q + 1 => by
    rw [ofNat_succ, succ, ← nadd_assoc, ofNat_nadd_ofNat p q, ← succ, ← ofNat_succ]; rfl

end ThetaWNoteD

namespace IDn

open LO LO.FirstOrder

/-! ### Structural helpers -/

section Helpers

variable {A : Fin n → Semisentence (LXIn n) 1} {ρ : ThetaWNoteD}

/-- Case analysis on a proposition of `LIinfN n`, in connective form. -/
theorem cases0 {C : Proposition (LIinfN n) → Prop}
    (hverum : C ⊤) (hfalsum : C ⊥)
    (hrel : ∀ (k : ℕ) (r : (LIinfN n).Rel k) (v : Fin k → SyntacticTerm (LIinfN n)),
      C (Semiformula.rel r v))
    (hnrel : ∀ (k : ℕ) (r : (LIinfN n).Rel k) (v : Fin k → SyntacticTerm (LIinfN n)),
      C (Semiformula.nrel r v))
    (hand : ∀ φ ψ : Proposition (LIinfN n), C (φ ⋏ ψ))
    (hor : ∀ φ ψ : Proposition (LIinfN n), C (φ ⋎ ψ))
    (hall : ∀ φ : Semiproposition (LIinfN n) 1, C (∀¹ φ))
    (hexs : ∀ φ : Semiproposition (LIinfN n) 1, C (∃¹ φ)) :
    ∀ φ : Proposition (LIinfN n), C φ
  | Semiformula.verum => hverum
  | Semiformula.falsum => hfalsum
  | Semiformula.rel r v => hrel _ r v
  | Semiformula.nrel r v => hnrel _ r v
  | Semiformula.and φ ψ => hand φ ψ
  | Semiformula.or φ ψ => hor φ ψ
  | Semiformula.all φ => hall φ
  | Semiformula.exs φ => hexs φ

/-- Moving a derivation to a larger operator and a larger sequent. -/
theorem IDnDerivable.lift {K K' : Set ThetaWNoteD → Set ThetaWNoteD} (hK' : ThetaWNoteD.IsOperator K')
    (hKK : ∀ X, K X ⊆ K' X) {h : ThetaWNoteD} {Δ Δ' : Sequent (LIinfN n)}
    (d : IDnDerivable A ρ K h Δ) (hsub : Δ ⊆ Δ') (hP : paramsVal Δ' ⊆ K' ∅) :
    IDnDerivable A ρ K' h Δ' :=
  (d.mono_op hKK).weaken_seq hK' hsub hP

theorem adjoin_le_adjoin {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.IsOperator H)
    {Z Z' : Set ThetaWNoteD} (h : Z ⊆ Z') (X : Set ThetaWNoteD) :
    ThetaWNoteD.adjoin H Z X ⊆ ThetaWNoteD.adjoin H Z' X :=
  hH.mono (Set.union_subset_union_left X h)

theorem subset_adjoin_empty {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.IsOperator H)
    (Z : Set ThetaWNoteD) : Z ⊆ ThetaWNoteD.adjoin H Z ∅ := by
  intro x hx
  exact hH.subset _ (Or.inl hx)

theorem freeVariables_subst_numI (φ : Semiformula (LIinfN n) ℕ 1) (hφ : φ.freeVariables = ∅)
    (p : ℕ) : (φ/[numI p]).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![numI p]) (φ := φ) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ ((Rew.subst ![numI p]) #i : SyntacticTerm (LIinfN n)).freeVariables := hi
    cases i using Fin.cases with
    | zero => simp only [Rew.subst_bvar, Matrix.cons_val_zero, numI_freeVariables] at hi'
              exact Finset.notMem_empty x hi'
    | succ i => exact i.elim0
  · have hz' : z ∈ φ.freeVariables := hz
    rw [hφ] at hz'
    exact Finset.notMem_empty z hz'

theorem freeVariables_subst_of_closed (φ : Semiformula (LIinfN n) ℕ 1) (hφ : φ.freeVariables = ∅)
    {t : SyntacticTerm (LIinfN n)} (ht : t.freeVariables = ∅) : (φ/[t]).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![t]) (φ := φ) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ ((Rew.subst ![t]) #i : SyntacticTerm (LIinfN n)).freeVariables := hi
    cases i using Fin.cases with
    | zero => simp only [Rew.subst_bvar, Matrix.cons_val_zero, ht] at hi'
              exact Finset.notMem_empty x hi'
    | succ i => exact i.elim0
  · have hz' : z ∈ φ.freeVariables := hz
    rw [hφ] at hz'
    exact Finset.notMem_empty z hz'

/-- The sequent `ψ, ¬ψ` read backwards. -/
theorem IDnDerivable.swap {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.IsOperator H)
    {h : ThetaWNoteD} {ψ : Proposition (LIinfN n)} (d : IDnDerivable A ρ H h [∼ψ, ψ]) :
    IDnDerivable A ρ H h [ψ, ∼ψ] := by
  refine d.weaken_seq (Γ' := [ψ, ∼ψ]) hH (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) ?_
  have := d.params_subset
  simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty] at this ⊢
  exact this

end Helpers

/-! ### Lemma 6.1 -/

section Taut

variable {A : Fin n → Semisentence (LXIn n) 1} {H : Set ThetaWNoteD → Set ThetaWNoteD}

theorem params_sub_adjoin (hH : ThetaWNoteD.IsOperator H) {ψ : Proposition (LIinfN n)} :
    paramsVal [ψ, ∼ψ] ⊆ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ := by
  simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty, Set.union_self]
  exact subset_adjoin_empty hH _

/-- Membership in `H(k(ψ))`, pointwise: the form `NiceS.rk_mem` wants. -/
theorem mem_adjoin_params (hH : ThetaWNoteD.IsOperator H) {ψ : Proposition (LIinfN n)}
    {s : Stage n} (hs : s ∈ params ψ) : s.val ∈ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
  subset_adjoin_empty hH _ ⟨s, hs, rfl⟩

/-- **Lemma 6.1, conjunction.** -/
theorem taut_and (hH : ThetaWNoteD.NiceS H) {φ₀ φ₁ : Proposition (LIinfN n)}
    (ih₀ : IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params φ₀))
      (ThetaWNoteD.omegaMul (rk φ₀)) [φ₀, ∼φ₀])
    (ih₁ : IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params φ₁))
      (ThetaWNoteD.omegaMul (rk φ₁)) [φ₁, ∼φ₁]) :
    IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params (φ₀ ⋏ φ₁)))
      (ThetaWNoteD.omegaMul (rk (φ₀ ⋏ φ₁))) [φ₀ ⋏ φ₁, ∼(φ₀ ⋏ φ₁)] := by
  set ψ : Proposition (LIinfN n) := φ₀ ⋏ φ₁ with hψ
  have hK := hH.adjoin (Stage.val '' params ψ)
  have hKo := hK.isOperator
  have hZ : Stage.val '' params ψ ⊆ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    subset_adjoin_empty hH.isOperator _
  have hΓ : paramsVal [ψ, ∼ψ] ⊆ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    params_sub_adjoin hH.isOperator
  have hneg : ∼ψ = ∼φ₀ ⋎ ∼φ₁ := by simp [hψ]
  have hrk : rk ψ = ThetaWNoteD.succ (max (rk φ₀) (rk φ₁)) := rk_and φ₀ φ₁
  have hs0 : params φ₀ ⊆ params ψ := Set.subset_union_left
  have hs1 : params φ₁ ⊆ params ψ := Set.subset_union_right
  have hs0' : Stage.val '' params φ₀ ⊆ Stage.val '' params ψ := Set.image_mono hs0
  have hs1' : Stage.val '' params φ₁ ⊆ Stage.val '' params ψ := Set.image_mono hs1
  -- the heights
  have hm0 : ThetaWNoteD.omegaMul (rk φ₀) ∈ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_mem (fun s hs => mem_adjoin_params hH.isOperator (hs0 hs)))
  have hm1 : ThetaWNoteD.omegaMul (rk φ₁) ∈ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_mem (fun s hs => mem_adjoin_params hH.isOperator (hs1 hs)))
  have hmψ : ThetaWNoteD.omegaMul (rk ψ) ∈ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_mem (fun s hs => mem_adjoin_params hH.isOperator hs))
  have hP : ∀ φ : Proposition (LIinfN n), params φ ⊆ params ψ →
      paramsVal [∼φ, φ, ψ, ∼ψ] ⊆ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ := by
    intro φ hφ
    simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty]
    exact Set.union_subset ((Set.image_mono hφ).trans hZ)
      (Set.union_subset ((Set.image_mono hφ).trans hZ) (Set.union_subset hZ hZ))
  have hP' : ∀ φ : Proposition (LIinfN n), params φ ⊆ params ψ →
      paramsVal [φ, ψ, ∼ψ] ⊆ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ := by
    intro φ hφ
    simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty]
    exact Set.union_subset ((Set.image_mono hφ).trans hZ) (Set.union_subset hZ hZ)
  have d0 : IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaWNoteD.omegaMul (rk φ₀)) [∼φ₀, φ₀, ψ, ∼ψ] :=
    ih₀.lift hKo (adjoin_le_adjoin hH.isOperator hs0')
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) (hP φ₀ hs0)
  have d1 : IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaWNoteD.omegaMul (rk φ₁)) [∼φ₁, φ₁, ψ, ∼ψ] :=
    ih₁.lift hKo (adjoin_le_adjoin hH.isOperator hs1')
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) (hP φ₁ hs1)
  have e0 : IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaWNoteD.nadd (ThetaWNoteD.omegaMul (rk φ₀)) (ThetaWNoteD.ofNat 2)) [φ₀, ψ, ∼ψ] :=
    .orL (hK.nadd_mem hm0 (hK.ofNat_mem 2)) (hP' φ₀ hs0)
      (by rw [← hneg]; simp) (ThetaWNoteD.lt_nadd_ofNat_succ _ 1) d0
  have e1 : IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaWNoteD.nadd (ThetaWNoteD.omegaMul (rk φ₁)) (ThetaWNoteD.ofNat 2)) [φ₁, ψ, ∼ψ] :=
    .orR (hK.nadd_mem hm1 (hK.ofNat_mem 2)) (hP' φ₁ hs1)
      (by rw [← hneg]; simp) (ThetaWNoteD.one_lt_nadd_ofNat_two _)
      (ThetaWNoteD.lt_nadd_ofNat_succ _ 1) d1
  refine .and hmψ hΓ List.mem_cons_self ?_ ?_ e0 e1
  · rw [hrk]; exact ThetaWNoteD.omegaMul_nadd_lt_omegaMul_succ (le_max_left _ _) 2
  · rw [hrk]; exact ThetaWNoteD.omegaMul_nadd_lt_omegaMul_succ (le_max_right _ _) 2

/-- **Lemma 6.1, universal quantifier.** -/
theorem taut_all (hH : ThetaWNoteD.NiceS H) {φ : Semiproposition (LIinfN n) 1}
    (ih : ∀ p : ℕ, IDnDerivable A ThetaWNoteD.zero
      (ThetaWNoteD.adjoin H (Stage.val '' params (φ/[numI p])))
      (ThetaWNoteD.omegaMul (rk (φ/[numI p]))) [φ/[numI p], ∼(φ/[numI p])]) :
    IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params (∀¹ φ)))
      (ThetaWNoteD.omegaMul (rk (∀¹ φ))) [∀¹ φ, ∼(∀¹ φ)] := by
  set ψ : Proposition (LIinfN n) := ∀¹ φ with hψ
  have hK := hH.adjoin (Stage.val '' params ψ)
  have hKo := hK.isOperator
  have hZ : Stage.val '' params ψ ⊆ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    subset_adjoin_empty hH.isOperator _
  have hΓ : paramsVal [ψ, ∼ψ] ⊆ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    params_sub_adjoin hH.isOperator
  have hneg : ∼ψ = ∃¹ (∼φ) := by simp [hψ]
  have hrk : rk ψ = ThetaWNoteD.succ (rk φ) := rk_all φ
  have hsp : ∀ p, params (φ/[numI p]) = params ψ := fun p => params_subst φ _
  have hmφ : ThetaWNoteD.omegaMul (rk φ) ∈ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_mem (fun s hs => mem_adjoin_params hH.isOperator
      (show s ∈ params φ from hs)))
  have hmψ : ThetaWNoteD.omegaMul (rk ψ) ∈ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_mem (fun s hs => mem_adjoin_params hH.isOperator hs))
  refine .all (fun p => ThetaWNoteD.nadd (ThetaWNoteD.omegaMul (rk φ)) (ThetaWNoteD.ofNat (p + 1)))
    hmψ hΓ (φ := φ) List.mem_cons_self (fun p => by
      rw [hrk]; exact ThetaWNoteD.omegaMul_nadd_lt_omegaMul_succ le_rfl _) (fun p => ?_)
  have hPp : paramsVal [φ/[numI p], ψ, ∼ψ] ⊆ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ := by
    simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty, hsp p]
    exact Set.union_subset hZ (Set.union_subset hZ hZ)
  have d : IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaWNoteD.omegaMul (rk φ)) [(∼φ)/[numI p], φ/[numI p], ψ, ∼ψ] := by
    have e : (∼φ)/[numI p] = ∼(φ/[numI p]) := by simp
    rw [e]
    have ihp := ih p
    rw [rk_subst] at ihp
    refine ihp.lift hKo (fun X => by rw [hsp p]) (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) ?_
    simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty, hsp p]
    exact Set.union_subset hZ (Set.union_subset hZ (Set.union_subset hZ hZ))
  exact .exs p (hK.nadd_mem hmφ (hK.ofNat_mem _)) hPp (by rw [← hneg]; simp)
    (ThetaWNoteD.ofNat_lt_nadd_ofNat_succ _ p) (ThetaWNoteD.lt_nadd_ofNat_succ _ p) d

/-- **Lemma 6.1, stage atom** `I_k^{≺δ} t`, at level `k`. -/
theorem taut_stage (hAb : FamilyLevelBounded A) (hH : ThetaWNoteD.NiceS H) (k : Fin n)
    (a : StageAt k.val) (t : SyntacticTerm (LIinfN n))
    (ih : ∀ g : StageAt k.val, g.1 < a.1 →
      IDnDerivable A ThetaWNoteD.zero
        (ThetaWNoteD.adjoin H (Stage.val '' params (unfold (A k) k g t)))
        (ThetaWNoteD.omegaMul (rk (unfold (A k) k g t)))
        [unfold (A k) k g t, ∼(unfold (A k) k g t)]) :
    IDnDerivable A ThetaWNoteD.zero
      (ThetaWNoteD.adjoin H (Stage.val '' params (stageAt (⟨k, a⟩ : Stage n) t)))
      (ThetaWNoteD.omegaMul (rk (stageAt (⟨k, a⟩ : Stage n) t)))
      [stageAt (⟨k, a⟩ : Stage n) t, ∼(stageAt (⟨k, a⟩ : Stage n) t)] := by
  set ψ : Proposition (LIinfN n) := stageAt (⟨k, a⟩ : Stage n) t with hψ
  have hK := hH.adjoin (Stage.val '' params ψ)
  have hZ : Stage.val '' params ψ ⊆ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    subset_adjoin_empty hH.isOperator _
  have hΓ : paramsVal [ψ, ∼ψ] ⊆ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    params_sub_adjoin hH.isOperator
  have hmψ : ThetaWNoteD.omegaMul (rk ψ) ∈ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_mem (fun s hs => mem_adjoin_params hH.isOperator hs))
  refine .nstage (fun g => ThetaWNoteD.succ (max (ThetaWNoteD.omegaMul (rk (unfold (A k) k g t))) g.1))
    hmψ hΓ (a := a) (t := t) (List.mem_cons_of_mem _ List.mem_cons_self) (fun g hg => ?_)
    (fun g hg => ?_)
  · rw [hψ, rk_stageAt]
    refine ThetaWNoteD.succ_max_lt ?_ (lt_of_lt_of_le (ThetaWNoteD.succ_lt_omegaMul_omegaMul hg)
      (ThetaWNoteD.omegaMul_le_omegaMul (ThetaWNoteD.le_add_left _ _)))
    refine ThetaWNoteD.succ_omegaMul_lt ?_
    have := rk_unfold_lt_stageAt (hAb k) hg t t
    rwa [rk_stageAt] at this
  · -- the premise for `g`, by clause (W) on `I_k^{≺δ} t` with the witness `g`
    set K' := ThetaWNoteD.adjoin (ThetaWNoteD.adjoin H (Stage.val '' params ψ)) {g.1} with hK'
    have hK'n : ThetaWNoteD.NiceS K' := hK.adjoin {g.1}
    have hg' : g.1 ∈ K' ∅ := subset_adjoin_empty hK.isOperator {g.1} rfl
    have hsub : Stage.val '' params ψ ⊆ K' ∅ :=
      hZ.trans (hK.isOperator.mono (Set.empty_subset _))
    -- every parameter of the unfolding is `g` itself or some *lower* level's top, and every
    -- `NiceS` operator already contains every level's top unconditionally (`NiceS.Omega_mem`)
    have huP : ∀ s ∈ params (unfold (A k) k g t), s.val ∈ K' ∅ := by
      intro s hs
      rcases params_unfold_of_levelBounded (hAb k) g t s hs with rfl | ⟨j, -, rfl⟩
      · exact hg'
      · exact hK'n.Omega_mem j.val
    have hu : Stage.val '' params (unfold (A k) k g t) ⊆ K' ∅ :=
      fun _ ⟨s, hs, hx⟩ => hx ▸ huP s hs
    have hmu : ThetaWNoteD.omegaMul (rk (unfold (A k) k g t)) ∈ K' ∅ :=
      hK'n.omegaMul_mem (hK'n.rk_mem huP)
    have hmax : max (ThetaWNoteD.omegaMul (rk (unfold (A k) k g t))) g.1 ∈ K' ∅ := by
      rcases le_total (ThetaWNoteD.omegaMul (rk (unfold (A k) k g t))) g.1 with h | h
      · rw [max_eq_right h]; exact hg'
      · rw [max_eq_left h]; exact hmu
    have hP : paramsVal [∼(unfold (A k) k g t), ψ, ∼ψ] ⊆ K' ∅ := by
      simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty]
      exact Set.union_subset hu (Set.union_subset hsub hsub)
    have hP2 : paramsVal [unfold (A k) k g t, ∼(unfold (A k) k g t), ψ, ∼ψ] ⊆ K' ∅ := by
      simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty]
      exact Set.union_subset hu (Set.union_subset hu (Set.union_subset hsub hsub))
    have hop : ∀ X, ThetaWNoteD.adjoin H (Stage.val '' params (unfold (A k) k g t)) X ⊆ K' X := by
      intro X
      refine hH.isOperator.2 _ _ (Set.union_subset ?_ (hK'n.isOperator.1 X))
      exact fun x hx => (hK'n.isOperator.2 ∅ X (Set.empty_subset _)) (hu hx)
    have d : IDnDerivable A ThetaWNoteD.zero K' (ThetaWNoteD.omegaMul (rk (unfold (A k) k g t)))
        [unfold (A k) k g t, ∼(unfold (A k) k g t), ψ, ∼ψ] :=
      (ih g hg).lift hK'n.isOperator hop
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) hP2
    exact .stage g (hK'n.succ_mem hmax) hP (a := a) (t := t)
      (List.mem_cons_of_mem _ List.mem_cons_self) hg
      (lt_of_le_of_lt (le_max_right _ _) (ThetaWNoteD.lt_succ _)) hg'
      (lt_of_le_of_lt (le_max_left _ _) (ThetaWNoteD.lt_succ _)) d

/-- A derivation of `¬ψ, ¬¬ψ` is one of `ψ, ¬ψ`. -/
theorem taut_neg (hH : ThetaWNoteD.NiceS H) {ψ : Proposition (LIinfN n)}
    (d : IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params (∼ψ)))
      (ThetaWNoteD.omegaMul (rk (∼ψ))) [∼ψ, ∼(∼ψ)]) :
    IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaWNoteD.omegaMul (rk ψ)) [ψ, ∼ψ] := by
  rw [params_neg, rk_neg] at d
  have e : ∼(∼ψ) = ψ := by simp
  rw [e] at d
  exact d.swap (hH.adjoin _).isOperator

theorem freeVariables_unfold {A : Fin n → Semisentence (LXIn n) 1} (k : Fin n) (a : StageAt k.val)
    {t : SyntacticTerm (LIinfN n)} (ht : t.freeVariables = ∅) :
    (unfold (A k) k a t).freeVariables = ∅ :=
  freeVariables_subst_of_closed _ (Semiformula.freeVariables_emb _) ht

/-- **Freund, Lemma 6.1**: `H[k(ψ)] ⊢^{ω·rk(ψ)}_0 ψ, ¬ψ` for every closed formula `ψ` and
every nice operator `H`. -/
theorem taut (hAb : FamilyLevelBounded A) (hH : ThetaWNoteD.NiceS H) (ψ : Proposition (LIinfN n))
    (hc : ψ.freeVariables = ∅) :
    IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaWNoteD.omegaMul (rk ψ)) [ψ, ∼ψ] := by
  suffices key : ∀ r : ThetaWNoteD, ∀ ψ : Proposition (LIinfN n), rk ψ = r → ψ.freeVariables = ∅ →
      IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params ψ))
        (ThetaWNoteD.omegaMul (rk ψ)) [ψ, ∼ψ] from key _ ψ rfl hc
  intro r
  induction r using WellFoundedLT.induction with
  | _ r ih =>
  intro ψ hr hc
  subst hr
  have IH : ∀ φ : Proposition (LIinfN n), rk φ < rk ψ → φ.freeVariables = ∅ →
      IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params φ))
        (ThetaWNoteD.omegaMul (rk φ)) [φ, ∼φ] := fun φ h hc' => ih _ h φ rfl hc'
  have hK := hH.adjoin (Stage.val '' params ψ)
  have hZ : Stage.val '' params ψ ⊆ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    subset_adjoin_empty hH.isOperator _
  have hα : ThetaWNoteD.omegaMul (rk ψ) ∈ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_mem (fun s hs => mem_adjoin_params hH.isOperator hs))
  have hΓ : paramsVal [ψ, ∼ψ] ⊆ ThetaWNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
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
      have hl : IsArithLit (Semiformula.rel (Sum.inl r : (LIinfN n).Rel k) v) :=
        ⟨k, r, v, Or.inl rfl, hv⟩
      by_cases ht : TrueN (Semiformula.rel (Sum.inl r : (LIinfN n).Rel k) v)
      · exact .literal hα hΓ ⟨hl, ht⟩ List.mem_cons_self
      · exact .literal hα hΓ ⟨hl.neg, (trueN_neg _).mpr ht⟩
          (List.mem_cons_of_mem _ List.mem_cons_self)
    · cases r with
      | X =>
        have e : Semiformula.rel (Sum.inr IInfRelN.X : (LIinfN n).Rel 1) v = XinfAt (v 0) :=
          rel_eq_vec _ v
        have d : IDnDerivable A ThetaWNoteD.zero (ThetaWNoteD.adjoin H (Stage.val '' params (XinfAt (v 0))))
            (ThetaWNoteD.omegaMul (rk (XinfAt (v 0)))) [XinfAt (v 0), ∼(XinfAt (v 0))] := by
          rw [← e]
          exact .idX (v 0) hα hΓ (by rw [e]; exact List.mem_cons_self)
            (by rw [e]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        rw [e]; exact d
      | stage s =>
        obtain ⟨k, a⟩ := s
        have e : Semiformula.rel (Sum.inr (IInfRelN.stage ⟨k, a⟩) : (LIinfN n).Rel 1) v =
            stageAt ⟨k, a⟩ (v 0) := rel_eq_vec _ v
        have hv0 : (v 0).freeVariables = ∅ := freeVariables_rel_arg hc 0
        rw [e]
        refine taut_stage hAb hH k a (v 0) fun g hg => IH _ ?_ (freeVariables_unfold k g hv0)
        rw [e]
        have := rk_unfold_lt_stageAt (hAb k) hg (v 0) (v 0)
        simpa using this
  | hnrel k r v =>
    intro hc IH hα hΓ
    rcases r with r | r
    · have hv : ∀ i, (v i).freeVariables = ∅ := freeVariables_nrel_arg hc
      have hl : IsArithLit (Semiformula.nrel (Sum.inl r : (LIinfN n).Rel k) v) :=
        ⟨k, r, v, Or.inr rfl, hv⟩
      by_cases ht : TrueN (Semiformula.nrel (Sum.inl r : (LIinfN n).Rel k) v)
      · exact .literal hα hΓ ⟨hl, ht⟩ List.mem_cons_self
      · exact .literal hα hΓ ⟨hl.neg, (trueN_neg _).mpr ht⟩
          (List.mem_cons_of_mem _ List.mem_cons_self)
    · cases r with
      | X =>
        have e : Semiformula.nrel (Sum.inr IInfRelN.X : (LIinfN n).Rel 1) v = ∼(XinfAt (v 0)) :=
          nrel_eq_vec _ v
        have d : IDnDerivable A ThetaWNoteD.zero
            (ThetaWNoteD.adjoin H (Stage.val '' params (∼(XinfAt (v 0)))))
            (ThetaWNoteD.omegaMul (rk (∼(XinfAt (v 0))))) [∼(XinfAt (v 0)), ∼(∼(XinfAt (v 0)))] := by
          rw [← e]
          exact .idX (v 0) hα hΓ (by rw [e]; exact List.mem_cons_of_mem _ (by simp))
            (by rw [e]; exact List.mem_cons_self)
        rw [e]; exact d
      | stage s =>
        obtain ⟨k, a⟩ := s
        have e : Semiformula.nrel (Sum.inr (IInfRelN.stage ⟨k, a⟩) : (LIinfN n).Rel 1) v =
            ∼(stageAt ⟨k, a⟩ (v 0)) := nrel_eq_vec _ v
        have hv0 : (v 0).freeVariables = ∅ := freeVariables_nrel_arg hc 0
        rw [e]
        refine taut_neg hH ?_
        have e2 : ∼(∼(stageAt ⟨k, a⟩ (v 0))) = stageAt ⟨k, a⟩ (v 0) := by simp
        rw [e2]
        refine taut_stage hAb hH k a (v 0) fun g hg => IH _ ?_ (freeVariables_unfold k g hv0)
        rw [e, rk_neg]
        have := rk_unfold_lt_stageAt (hAb k) hg (v 0) (v 0)
        simpa using this
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
    exact taut_all hH fun p => IH _ (rk_subst_lt_all φ _) (freeVariables_subst_numI φ hc p)
  | hexs φ =>
    intro hc IH _ _
    rw [Semiformula.freeVariables_exs] at hc
    refine taut_neg hH ?_
    have e : ∼(∃¹ φ) = ∀¹ (∼φ) := by simp
    rw [e]
    refine taut_all hH fun p => IH _ ?_ (freeVariables_subst_numI (∼φ)
      (by rw [Semiformula.freeVariables_not]; exact hc) p)
    rw [rk_subst]
    have := rk_lt_exs φ
    rwa [rk_neg]

end Taut

/-! ### `ω`-completeness for arithmetic -/

section Arith

variable {A : Fin n → Semisentence (LXIn n) 1} {ρ : ThetaWNoteD} {H : Set ThetaWNoteD → Set ThetaWNoteD}

/-- `r` is a relation symbol of arithmetic. -/
def IsArithRel {k : ℕ} (r : (LIinfN n).Rel k) : Prop := ∃ r' : (ℒₒᵣ : Language).Rel k, r = Sum.inl r'

/-- A formula all of whose atoms are atoms of arithmetic. -/
def ArithF {ξ : Type*} : {m : ℕ} → Semiformula (LIinfN n) ξ m → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel r _ => IsArithRel r
  | _, .nrel r _ => IsArithRel r
  | _, .and φ ψ => ArithF φ ∧ ArithF ψ
  | _, .or φ ψ => ArithF φ ∧ ArithF ψ
  | _, .all φ => ArithF φ
  | _, .exs φ => ArithF φ

theorem arithF_rew {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfN n) ξ₁ m₁ ξ₂ m₂)
    {φ : Semiformula (LIinfN n) ξ₁ m₁} (h : ArithF φ) : ArithF (ω ▹ φ) := by
  revert h
  induction φ using Semiformula.rec' generalizing m₂ with
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

theorem params_of_arithF {ξ : Type*} {m : ℕ} {φ : Semiformula (LIinfN n) ξ m} (h : ArithF φ) :
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

theorem trueN_all (φ : Semiproposition (LIinfN n) 1) :
    TrueN (∀¹ φ) ↔ ∀ p : ℕ, TrueN (φ/[numI p]) := by
  unfold TrueN
  rw [Semiformula.eval_all]
  refine forall_congr' fun p => ?_
  rw [show φ/[numI p] = φ ⇜ ![numI p] from rfl, Semiformula.eval_substs]
  refine iff_of_eq (congrArg (fun w => Semiformula.Eval (s := stdInfN) w (fun _ => 0) φ) ?_)
  funext i
  obtain rfl := Subsingleton.elim i 0
  simp only [Matrix.cons_val_zero, Function.comp_apply]
  rw [val_numI]

theorem trueN_exs (φ : Semiproposition (LIinfN n) 1) :
    TrueN (∃¹ φ) ↔ ∃ p : ℕ, TrueN (φ/[numI p]) := by
  unfold TrueN
  rw [Semiformula.eval_ex]
  refine exists_congr fun p => ?_
  rw [show φ/[numI p] = φ ⇜ ![numI p] from rfl, Semiformula.eval_substs]
  refine iff_of_eq (congrArg (fun w => Semiformula.Eval (s := stdInfN) w (fun _ => 0) φ) ?_)
  funext i
  obtain rfl := Subsingleton.elim i 0
  simp only [Matrix.cons_val_zero, Function.comp_apply]
  rw [val_numI]

/-- `ω`, as a notation. -/
abbrev omegaT : ThetaWNoteD := ThetaWNoteD.omegaPow ThetaWNoteD.one

theorem omegaT_mem (hH : ThetaWNoteD.NiceS H) (X : Set ThetaWNoteD) (c : ℕ) :
    ThetaWNoteD.nadd omegaT (ThetaWNoteD.ofNat c) ∈ H X :=
  hH.nadd_mem (hH.omegaPow_mem hH.one_mem) (hH.ofNat_mem c)

theorem ofNat_lt_omegaT_nadd (p c : ℕ) :
    ThetaWNoteD.ofNat p < ThetaWNoteD.nadd omegaT (ThetaWNoteD.ofNat c) :=
  lt_of_lt_of_le (ThetaWNoteD.ofNat_lt_omega p) (ThetaWNoteD.le_nadd_left _ _)

/-- **`ω`-completeness**: a closed arithmetic formula true in `ℕ` is derivable, cut-free, at
height `ω ⊕ c` for every bound `c` on its complexity. -/
theorem omega_complete (hH : ThetaWNoteD.NiceS H) :
    ∀ (c : ℕ) (φ : Proposition (LIinfN n)), φ.complexity ≤ c → ArithF φ → φ.freeVariables = ∅ →
      TrueN φ → IDnDerivable A ρ H (ThetaWNoteD.nadd omegaT (ThetaWNoteD.ofNat c)) [φ] := by
  intro c
  induction c with
  | zero =>
    intro φ hc hA hf ht
    have hP : paramsVal [φ] ⊆ H ∅ := by
      simp only [paramsVal_cons, paramsVal_nil, params_of_arithF hA, Set.image_empty,
        Set.union_empty]
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
    have hP : paramsVal [φ] ⊆ H ∅ := by
      simp only [paramsVal_cons, paramsVal_nil, params_of_arithF hA, Set.image_empty,
        Set.union_empty]
      exact Set.empty_subset _
    have hm : ThetaWNoteD.nadd omegaT (ThetaWNoteD.ofNat (c + 1)) ∈ H ∅ := omegaT_mem hH _ _
    have hlt : ThetaWNoteD.nadd omegaT (ThetaWNoteD.ofNat c) <
        ThetaWNoteD.nadd omegaT (ThetaWNoteD.ofNat (c + 1)) :=
      ThetaWNoteD.nadd_ofNat_lt_nadd_ofNat' _ (Nat.lt_succ_self c)
    have lift : ∀ χ : Proposition (LIinfN n), χ.complexity ≤ c → ArithF χ → χ.freeVariables = ∅ →
        TrueN χ → IDnDerivable A ρ H (ThetaWNoteD.nadd omegaT (ThetaWNoteD.ofNat c)) [χ, φ] := by
      intro χ h1 h2 h3 h4
      refine (ih χ h1 h2 h3 h4).weaken_seq hH.isOperator
        (List.cons_subset_cons _ (List.nil_subset _)) ?_
      simp only [paramsVal_cons, paramsVal_nil, params_of_arithF hA, params_of_arithF h2,
        Set.image_empty, Set.union_empty]
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
          (lt_of_lt_of_le (by rw [← ThetaWNoteD.ofNat_one]; exact ThetaWNoteD.ofNat_lt_omega 1)
            (ThetaWNoteD.le_nadd_left _ _)) hlt (lift ψ (by omega) hA.2 hf.2 h)
    | hall φ =>
      intro hc hA hf ht hP lift
      rw [Semiformula.complexity_all] at hc
      rw [Semiformula.freeVariables_all] at hf
      refine .all (fun _ => ThetaWNoteD.nadd omegaT (ThetaWNoteD.ofNat c)) hm hP List.mem_cons_self
        (fun _ => hlt) fun p => lift _ (by rw [Semiformula.complexity_rew]; omega)
          (arithF_rew _ hA) (freeVariables_subst_numI φ hf p) ((trueN_all φ).mp ht p)
    | hexs φ =>
      intro hc hA hf ht hP lift
      rw [Semiformula.complexity_exs] at hc
      rw [Semiformula.freeVariables_exs] at hf
      obtain ⟨p, hp⟩ := (trueN_exs φ).mp ht
      exact .exs p hm hP List.mem_cons_self (ofNat_lt_omegaT_nadd p _) hlt
        (lift _ (by rw [Semiformula.complexity_rew]; omega) (arithF_rew _ hA)
          (freeVariables_subst_numI φ hf p) hp)

end Arith

/-! ### `X` and every level's `I` read as empty: the semantics -/

section Semantics

theorem stdInfN_lMap_eq :
    stdInfN.lMap (embedHom (n := n)) = stdIN (fun _ => False) (fun _ : Fin n => (∅ : Set ℕ)) := by
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

theorem eval_killX_stdIN (S : Fin n → Set ℕ) {ξ : Type*} {m : ℕ} (φ : Semiformula (LXIn n) ξ m)
    (e : Fin m → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdIN (fun _ => False) S) e f (killX φ) ↔
      Semiformula.Eval (s := stdIN (fun _ => False) S) e f φ := by
  induction φ using Semiformula.rec' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v =>
    rcases r with r | r
    · exact Iff.rfl
    · cases r with
      | X =>
        show Semiformula.Eval (s := stdIN (fun _ => False) S) e f ⊥ ↔ _
        simp only [LogicalConnective.HomClass.map_bot, Prop.bot_eq_false, false_iff]
        exact fun h => h
      | I j => exact Iff.rfl
  | hnrel r v =>
    rcases r with r | r
    · exact Iff.rfl
    · cases r with
      | X =>
        show Semiformula.Eval (s := stdIN (fun _ => False) S) e f ⊤ ↔ _
        simp only [LogicalConnective.HomClass.map_top, Prop.top_eq_true, true_iff]
        exact fun h => h
      | I j => exact Iff.rfl
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

/-- **The embedding reads `X` and every level's `I` as empty.** -/
theorem eval_embK {ξ : Type*} {m : ℕ} (φ : Semiformula (LXIn n) ξ m) (e : Fin m → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdInfN) e f (embK φ) ↔
      Semiformula.Eval (s := stdIN (fun _ => False) (fun _ : Fin n => (∅ : Set ℕ))) e f φ := by
  rw [embK, embed, Semiformula.eval_lMap, stdInfN_lMap_eq]
  exact eval_killX_stdIN (fun _ => ∅) φ e f

/-- A sentence true in `stdIN` (with `X` and every level's `I` empty) has a true embedding. -/
theorem trueN_emb_embK {σ : Sentence (LXIn n)}
    (h : Semiformula.Eval (s := stdIN (fun _ => False) (fun _ : Fin n => (∅ : Set ℕ)))
      ![] Empty.elim σ) :
    TrueN (Rewriting.emb (embK σ) : Proposition (LIinfN n)) := by
  unfold TrueN
  rw [Semiformula.eval_emb]
  exact (eval_embK σ ![] Empty.elim).mpr h

end Semantics

/-! ### The universal closure, by the ω-rule -/

section Closure

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting

variable {A : Fin n → Semisentence (LXIn n) 1} {ρ : ThetaWNoteD} {H : Set ThetaWNoteD → Set ThetaWNoteD}

/-- Composing a lifted `k`-ary substitution with a one-point substitution. -/
theorem subst_q_subst {k : ℕ} (σ : Semiformula (LIinfN n) ℕ (k + 1))
    (v : Fin k → SyntacticTerm (LIinfN n)) (t : SyntacticTerm (LIinfN n)) :
    ((Rew.subst v).q ▹ σ)/[t] = σ ⇜ (t :> v) := by
  have hrew : (Rew.subst ![t]).comp ((Rew.subst v).q) = Rew.subst (t :> v) := by
    rw [Rew.q_subst, Rew.subst_comp_subst]
    congr 1
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  simpa [← comp_app] using smul_ext' (φ := σ) hrew

theorem allClosure_aux (hH : ThetaWNoteD.IsOperator H) (β : ThetaWNoteD)
    (hβ : ∀ j : ℕ, ThetaWNoteD.nadd β (ThetaWNoteD.ofNat j) ∈ H ∅) :
    ∀ (k j : ℕ) (σ : Semiformula (LIinfN n) ℕ k), Stage.val '' params σ ⊆ H ∅ →
      (∀ w : Fin k → ℕ, IDnDerivable A ρ H (ThetaWNoteD.nadd β (ThetaWNoteD.ofNat j))
        [σ ⇜ fun i => numI (w i)]) →
      IDnDerivable A ρ H (ThetaWNoteD.nadd β (ThetaWNoteD.ofNat (j + k))) [∀¹* σ] := by
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
    have hPs : paramsVal [∀¹ ((Rew.subst fun i => numI (w i)).q ▹ σ)] ⊆ H ∅ := by
      simp only [paramsVal_cons, paramsVal_nil, Set.union_empty, params_all, params_rew]
      exact hP
    refine .all (fun _ => ThetaWNoteD.nadd β (ThetaWNoteD.ofNat j)) (hβ _) hPs List.mem_cons_self
      (fun _ => ThetaWNoteD.nadd_ofNat_lt_nadd_ofNat' _ (Nat.lt_succ_self j)) (fun p => ?_)
    rw [subst_q_subst]
    have hv : ((numI p : SyntacticTerm (LIinfN n)) :> fun i => numI (w i)) =
        fun i => numI (((p :> w) : Fin (k + 1) → ℕ) i) := by
      funext i
      induction i using Fin.cases with
      | zero => simp
      | succ j => simp
    rw [hv]
    refine (h (p :> w)).weaken_seq hH (List.cons_subset_cons _ (List.nil_subset _)) ?_
    simp only [paramsVal_cons, paramsVal_nil, Set.union_empty, params_all, params_rew]
    exact Set.union_subset hP hP

theorem allClosure_derivable (hH : ThetaWNoteD.IsOperator H) {k : ℕ}
    (σ : Semiformula (LIinfN n) ℕ k) {β : ThetaWNoteD}
    (hβ : ∀ j : ℕ, ThetaWNoteD.nadd β (ThetaWNoteD.ofNat j) ∈ H ∅)
    (hP : Stage.val '' params σ ⊆ H ∅)
    (h : ∀ w : Fin k → ℕ, IDnDerivable A ρ H β [σ ⇜ fun i => numI (w i)]) :
    IDnDerivable A ρ H (ThetaWNoteD.nadd β (ThetaWNoteD.ofNat k)) [∀¹* σ] := by
  have key := allClosure_aux (A := A) (ρ := ρ) hH β hβ k 0 σ hP (fun w => by
    rw [ThetaWNoteD.ofNat_zero, ThetaWNoteD.nadd_zero]; exact h w)
  rwa [Nat.zero_add] at key

end Closure

/-! ### The axioms of equality and of `𝗣𝗔⁻` -/

section EqPA

variable {A : Fin n → Semisentence (LXIn n) 1} {H : Set ThetaWNoteD → Set ThetaWNoteD}

/-- `Ω_n · 2 = Ω_n ⊕ Ω_n`, the top level (matches `IDn.AxiomsPA`'s local copy of the same
quantity, drafted before this file reached this point). -/
abbrev OmegaTwo_al : ThetaWNoteD :=
  ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) (ThetaWNoteD.Omega (n - 1))

/-- **The axiom `σ` is derivable** in the form of Freund, proof of Theorem 6.5: cut-free, at
a height `Ω_n · 2 + m` independent of the nice operator. -/
def AxDerivable_al (A : Fin n → Semisentence (LXIn n) 1) (σ : Sentence (LXIn n)) : Prop :=
  ∃ m : ℕ, ∀ H : Set ThetaWNoteD → Set ThetaWNoteD, ThetaWNoteD.NiceS H →
    IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat m))
      [(Rewriting.emb (embK σ) : Proposition (LIinfN n))]

theorem OmegaTwo_mem_al (hH : ThetaWNoteD.NiceS H) (X : Set ThetaWNoteD) (m : ℕ) :
    ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat m) ∈ H X :=
  hH.nadd_mem (hH.nadd_mem (hH.Omega_mem (n - 1)) (hH.Omega_mem (n - 1))) (hH.ofNat_mem m)

theorem axDerivable_of_le_al {σ : Sentence (LXIn n)} (m : ℕ) (h : ThetaWNoteD)
    (hle : h ≤ ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat m))
    (d : ∀ H : Set ThetaWNoteD → Set ThetaWNoteD, ThetaWNoteD.NiceS H →
      IDnDerivable A ThetaWNoteD.zero H h [(Rewriting.emb (embK σ) : Proposition (LIinfN n))]) :
    AxDerivable_al A σ :=
  ⟨m, fun H hH => (d H hH).mono_height hle (OmegaTwo_mem_al hH _ m)⟩

theorem Omega_le_OmegaTwo_nadd (m : ℕ) :
    ThetaWNoteD.Omega (n - 1) ≤ ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat m) :=
  le_trans (ThetaWNoteD.le_nadd_left _ _) (ThetaWNoteD.le_nadd_left _ _)

/-- `Ω_j ≤ Ω_{n-1}` whenever `j ≤ n - 1` (matches `IDn.AxiomsPA.Omega_le_Omega_of_le`, reproved
locally: that file is not imported here). -/
theorem Omega_le_Omega_of_le {i j : ℕ} (h : i ≤ j) :
    ThetaWNoteD.Omega i ≤ ThetaWNoteD.Omega j := by
  rcases h.lt_or_eq with hlt | rfl
  · exact le_of_lt (ThetaWNoteD.Omega_lt_Omega_iff.mpr hlt)
  · exact le_refl _

theorem omegaT_lt_Omega (c : ℕ) :
    ThetaWNoteD.nadd omegaT (ThetaWNoteD.ofNat c) < ThetaWNoteD.Omega (n - 1) :=
  ThetaWNoteD.nadd_lt_Omega
    (ThetaWNoteD.omegaPow_lt_Omega (ThetaWNoteD.one_lt_prin (p := ThetaWNoteD.Omega (n - 1)) trivial))
    (ThetaWNoteD.ofNat_lt_prin (p := ThetaWNoteD.Omega (n - 1)) trivial c)

/-- A formula of `LXIn n` without any level's predicate `I`. -/
def IFreeL {ξ : Type*} : {m : ℕ} → Semiformula (LXIn n) ξ m → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel (Sum.inl _) _ => True
  | _, .rel (Sum.inr IXRelN.X) _ => True
  | _, .rel (Sum.inr (IXRelN.I _)) _ => False
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr IXRelN.X) _ => True
  | _, .nrel (Sum.inr (IXRelN.I _)) _ => False
  | _, .and φ ψ => IFreeL φ ∧ IFreeL ψ
  | _, .or φ ψ => IFreeL φ ∧ IFreeL ψ
  | _, .all φ => IFreeL φ
  | _, .exs φ => IFreeL φ

/-- Without any level's `I`, the embedding is arithmetic (`X` is read as empty). -/
theorem arithF_embK {ξ : Type*} {m : ℕ} :
    ∀ (φ : Semiformula (LXIn n) ξ m), IFreeL φ → ArithF (embK φ)
  | .verum, _ => by show ArithF (embK (⊤ : Semiformula (LXIn n) ξ m)); rw [embK_verum]; trivial
  | .falsum, _ => by show ArithF (embK (⊥ : Semiformula (LXIn n) ξ m)); rw [embK_falsum]; trivial
  | .rel (Sum.inl r) _, _ => ⟨r, rfl⟩
  | .rel (Sum.inr IXRelN.X) _, _ => by
    show ArithF (embK (⊥ : Semiformula (LXIn n) ξ m)); rw [embK_falsum]; trivial
  | .rel (Sum.inr (IXRelN.I _)) _, h => h.elim
  | .nrel (Sum.inl r) _, _ => ⟨r, rfl⟩
  | .nrel (Sum.inr IXRelN.X) _, _ => by
    show ArithF (embK (⊤ : Semiformula (LXIn n) ξ m)); rw [embK_verum]; trivial
  | .nrel (Sum.inr (IXRelN.I _)) _, h => h.elim
  | .and φ ψ, h => by
    show ArithF (embK (φ ⋏ ψ)); rw [embK_and]; exact ⟨arithF_embK φ h.1, arithF_embK ψ h.2⟩
  | .or φ ψ, h => by
    show ArithF (embK (φ ⋎ ψ)); rw [embK_or]; exact ⟨arithF_embK φ h.1, arithF_embK ψ h.2⟩
  | .all φ, h => by
    show ArithF (embK (∀¹ φ)); rw [embK_all]; exact arithF_embK φ h
  | .exs φ, h => by
    show ArithF (embK (∃¹ φ)); rw [embK_exs]; exact arithF_embK φ h

@[simp] theorem iFreeL_neg {ξ : Type*} {m : ℕ} (φ : Semiformula (LXIn n) ξ m) :
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

theorem iFreeL_imp {ξ : Type*} {m : ℕ} (φ ψ : Semiformula (LXIn n) ξ m) :
    IFreeL (φ 🡒 ψ) ↔ IFreeL φ ∧ IFreeL ψ := by
  have h : (φ 🡒 ψ) = ∼φ ⋎ ψ := rfl
  rw [h]
  exact and_congr (iFreeL_neg φ) Iff.rfl

theorem iFreeL_allClosure {ξ : Type*} :
    ∀ {m : ℕ} (φ : Semiformula (LXIn n) ξ m), IFreeL φ → IFreeL (∀¹* φ)
  | 0, _, h => h
  | _ + 1, φ, h => iFreeL_allClosure (∀¹ φ) h

theorem iFreeL_conj {ξ : Type*} {m : ℕ} :
    ∀ {k : ℕ} (v : Fin k → Semiformula (LXIn n) ξ m), (∀ i, IFreeL (v i)) → IFreeL (Matrix.conj v)
  | 0, _, _ => trivial
  | _ + 1, v, h => ⟨h 0, iFreeL_conj (Matrix.vecTail v) fun i => h i.succ⟩

theorem iFreeL_eqOp {ξ : Type*} {m : ℕ} (t u : Semiterm (LXIn n) ξ m) :
    IFreeL ((Semiformula.Operator.Eq.eq : Semiformula.Operator (LXIn n) 2).operator ![t, u]) := by
  rw [Semiformula.Operator.eq_def]
  trivial

theorem iFreeL_eqRefl : IFreeL (Theory.Eq.refl (LXIn n)) :=
  iFreeL_eqOp (ξ := Empty) (#0 : Semiterm (LXIn n) Empty 1) #0

theorem iFreeL_eqSymm : IFreeL (Theory.Eq.symm (LXIn n)) :=
  (iFreeL_imp _ _).mpr ⟨iFreeL_eqOp _ _, iFreeL_eqOp _ _⟩

theorem iFreeL_eqTrans : IFreeL (Theory.Eq.trans (LXIn n)) :=
  (iFreeL_imp _ _).mpr ⟨iFreeL_eqOp _ _, (iFreeL_imp _ _).mpr ⟨iFreeL_eqOp _ _, iFreeL_eqOp _ _⟩⟩

theorem iFreeL_funcExt {k : ℕ} (f : (LXIn n).Func k) : IFreeL (Theory.Eq.funcExt f) :=
  iFreeL_allClosure _ ((iFreeL_imp _ _).mpr
    ⟨iFreeL_conj _ (fun _ => iFreeL_eqOp _ _), iFreeL_eqOp _ _⟩)

theorem iFreeL_relExt_inl {k : ℕ} (r : (ℒₒᵣ : Language).Rel k) :
    IFreeL (Theory.Eq.relExt (Sum.inl r : (LXIn n).Rel k)) :=
  iFreeL_allClosure _ ((iFreeL_imp _ _).mpr
    ⟨iFreeL_conj _ (fun _ => iFreeL_eqOp _ _), (iFreeL_imp _ _).mpr ⟨trivial, trivial⟩⟩)

theorem iFreeL_relExt_X : IFreeL (Theory.Eq.relExt (Sum.inr IXRelN.X : (LXIn n).Rel 1)) :=
  iFreeL_allClosure _ ((iFreeL_imp _ _).mpr
    ⟨iFreeL_conj _ (fun _ => iFreeL_eqOp _ _), (iFreeL_imp _ _).mpr ⟨trivial, trivial⟩⟩)

theorem iFreeL_lMap_toLXIN {ξ : Type*} {m : ℕ} (φ : Semiformula ℒₒᵣ ξ m) :
    IFreeL (Semiformula.lMap (toLXIN (Fin n)) φ) := by
  induction φ using Semiformula.rec' with
  | hverum => simp only [LogicalConnective.HomClass.map_top]; trivial
  | hfalsum => simp only [LogicalConnective.HomClass.map_bot]; trivial
  | hrel r v => trivial
  | hnrel r v => trivial
  | hand φ ψ ihφ ihψ => rw [LogicalConnective.HomClass.map_and]; exact ⟨ihφ, ihψ⟩
  | hor φ ψ ihφ ihψ => rw [LogicalConnective.HomClass.map_or]; exact ⟨ihφ, ihψ⟩
  | hall φ ih => rw [Semiformula.lMap_all]; exact ih
  | hexs φ ih => rw [Semiformula.lMap_exs]; exact ih

/-- **An `I`-free sentence true in `ℕ`** (with `X` and every level's `I` read as empty) is an
axiom derivable at height `ω ⊕ c`. -/
theorem axDerivable_of_iFree {σ : Sentence (LXIn n)} (hI : IFreeL σ)
    (ht : Semiformula.Eval (s := stdIN (fun _ => False) (fun _ : Fin n => (∅ : Set ℕ))) ![]
      Empty.elim σ) :
    AxDerivable_al A σ := by
  refine axDerivable_of_le_al 0 (ThetaWNoteD.nadd omegaT
    (ThetaWNoteD.ofNat (Rewriting.emb (embK σ) : Proposition (LIinfN n)).complexity))
    (le_of_lt (lt_of_lt_of_le (omegaT_lt_Omega _) (Omega_le_OmegaTwo_nadd 0))) (fun H hH => ?_)
  exact omega_complete hH _ _ le_rfl (arithF_rew _ (arithF_embK σ hI))
    (Semiformula.freeVariables_emb _) (trueN_emb_embK ht)

/-- **The axioms of `𝗣𝗔⁻`** (Freund, proof of Theorem 6.5, after Theorem 3.7 of the first
lecture). -/
theorem paMinus_axiom {σ : Sentence (LXIn n)}
    (h : σ ∈ Theory.lMap (toLXIN (Fin n)) 𝗣𝗔⁻) : AxDerivable_al A σ := by
  obtain ⟨τ, hτ, rfl⟩ := h
  exact axDerivable_of_iFree (iFreeL_lMap_toLXIN τ)
    (eval_of_paMinus (fun _ => False) (fun _ : Fin n => (∅ : Set ℕ)) ⟨τ, hτ, rfl⟩)

/-! #### The equality axiom for `I_k`, one instance per level -/

section RelExtI

variable (k : Fin n)

/-- `t = u` in `LXIn n`. -/
def eqX {ξ : Type*} {m : ℕ} (t u : Semiterm (LXIn n) ξ m) : Semiformula (LXIn n) ξ m :=
  Semiformula.rel (Language.Eq.eq : (LXIn n).Rel 2) ![t, u]

/-- `t = u` in `LIinfN n`. -/
def eqI {ξ : Type*} {m : ℕ} (t u : Semiterm (LIinfN n) ξ m) : Semiformula (LIinfN n) ξ m :=
  Semiformula.rel (Language.Eq.eq : (LIinfN n).Rel 2) ![t, u]

/-- `embT` at any level agrees with the plain embedding of terms (`stageHom_top`). -/
theorem embT_eq_lMap_embedHom {ξ : Type*} {m : ℕ} (t : Semiterm (LXIn n) ξ m) :
    embT k t = Semiterm.lMap (embedHom (n := n)) t := by
  rw [embT, stageHom_top]

/-- The matrix of the equality axiom for `I_k`. -/
def relI2S : Semisentence (LXIn n) 2 :=
  ∼(eqX (#0 : Semiterm (LXIn n) Empty 2) #1 ⋏ ⊤) ⋎
    (∼(Iat k (#0 : Semiterm (LXIn n) Empty 2)) ⋎ Iat k (#1 : Semiterm (LXIn n) Empty 2))

theorem relExtI_eq :
    (Theory.Eq.relExt (Sum.inr (IXRelN.I k) : (LXIn n).Rel 1) : Sentence (LXIn n)) =
      ∀¹ (∀¹ (relI2S k)) := by
  have hv0 : (fun i : Fin 1 ↦ (#(i.addCast 1) : Semiterm (LXIn n) Empty 2))
      = ![(#0 : Semiterm (LXIn n) Empty 2)] := funext (Fin.forall_fin_one.mpr rfl)
  have hv1 : (fun i : Fin 1 ↦ (#(i.addNat 1) : Semiterm (LXIn n) Empty 2))
      = ![(#1 : Semiterm (LXIn n) Empty 2)] := funext (Fin.forall_fin_one.mpr rfl)
  have hB : Semiformula.rel (Sum.inr (IXRelN.I k) : (LXIn n).Rel 1)
        (fun i : Fin 1 ↦ (#(i.addCast 1) : Semiterm (LXIn n) Empty 2))
      = Iat k (#0 : Semiterm (LXIn n) Empty 2) :=
    congrArg (fun v : Fin 1 → Semiterm (LXIn n) Empty 2 =>
        Semiformula.rel (Sum.inr (IXRelN.I k) : (LXIn n).Rel 1) v) hv0
  have hC : Semiformula.rel (Sum.inr (IXRelN.I k) : (LXIn n).Rel 1)
        (fun i : Fin 1 ↦ (#(i.addNat 1) : Semiterm (LXIn n) Empty 2))
      = Iat k (#1 : Semiterm (LXIn n) Empty 2) :=
    congrArg (fun v : Fin 1 → Semiterm (LXIn n) Empty 2 =>
        Semiformula.rel (Sum.inr (IXRelN.I k) : (LXIn n).Rel 1) v) hv1
  show (∀¹* ((Matrix.conj fun i : Fin 1 ↦
      (eqX (#(i.addCast 1) : Semiterm (LXIn n) Empty 2) (#(i.addNat 1)))) 🡒
      (Semiformula.rel (Sum.inr (IXRelN.I k) : (LXIn n).Rel 1)
          (fun i : Fin 1 ↦ (#(i.addCast 1) : Semiterm (LXIn n) Empty 2)) 🡒
        Semiformula.rel (Sum.inr (IXRelN.I k) : (LXIn n).Rel 1)
          (fun i : Fin 1 ↦ (#(i.addNat 1) : Semiterm (LXIn n) Empty 2)))) : Sentence (LXIn n))
      = ∀¹ (∀¹ (relI2S k))
  rw [hB, hC]
  rfl

/-- Level-free on purpose (no `k` in the statement): as a `simp` lemma its LHS must determine
every variable on the RHS, and `embT k` (any `k`) is only *propositionally* `Semiterm.lMap
embedHom` (`embT_eq_lMap_embedHom`, via `stageHom_top`, not `rfl`), so a `k`-parametrised
statement here would leave `simp` unable to pick a `k` for the RHS. -/
theorem embK_eqX {ξ : Type*} {m : ℕ} (t u : Semiterm (LXIn n) ξ m) :
    embK (eqX t u) = eqI (Semiterm.lMap (embedHom (n := n)) t) (Semiterm.lMap (embedHom (n := n)) u) :=
  congrArg (Semiformula.rel (Language.Eq.eq : (LIinfN n).Rel 2))
    (funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩))

@[simp] theorem rew_eqI {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfN n) ξ₁ m₁ ξ₂ m₂)
    (t u : Semiterm (LIinfN n) ξ₁ m₁) : ω ▹ (eqI t u) = eqI (ω t) (ω u) := Semiformula.rew_rel2 ω

@[simp] theorem rew_IOmegaAt {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfN n) ξ₁ m₁ ξ₂ m₂)
    (t : Semiterm (LIinfN n) ξ₁ m₁) : ω ▹ (IOmegaAt k t) = IOmegaAt k (ω t) :=
  Semiformula.rew_rel1 ω

/-- The matrix of the equality axiom for `I_k`, embedded. -/
def relI2 : Semiformula (LIinfN n) ℕ 2 :=
  ∼(eqI (#0 : Semiterm (LIinfN n) ℕ 2) #1 ⋏ ⊤) ⋎
    (∼(IOmegaAt k (#0 : Semiterm (LIinfN n) ℕ 2)) ⋎ IOmegaAt k (#1 : Semiterm (LIinfN n) ℕ 2))

/-- The matrix at the numerals `a`, `b`. -/
def relI0 (a b : ℕ) : Proposition (LIinfN n) :=
  ∼(eqI (numI a) (numI b) ⋏ ⊤) ⋎ (∼(IOmegaAt k (numI a)) ⋎ IOmegaAt k (numI b))

theorem emb_embK_relI2S :
    (Rewriting.emb (embK (relI2S k)) : Semiformula (LIinfN n) ℕ 2) = relI2 k := by
  simp only [relI2S, embK_or, embK_and, embK_neg, embK_verum, embK_eqX, embK_Iat, relI2,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_top, rew_eqI,
    rew_IOmegaAt, Semiterm.lMap_bvar, Rew.emb_bvar]

theorem emb_embK_relExtI :
    (Rewriting.emb (embK (Theory.Eq.relExt (Sum.inr (IXRelN.I k) : (LXIn n).Rel 1))) :
        Proposition (LIinfN n)) = ∀¹* (relI2 k) := by
  rw [relExtI_eq, embK_all, embK_all, ← emb_embK_relI2S]
  simp only [Rewriting.app_all, Rew.q_emb]
  rfl

theorem relI2_inst (w : Fin 2 → ℕ) : ((relI2 k) ⇜ fun i => numI (w i)) = relI0 k (w 0) (w 1) := by
  simp [relI2, relI0]

theorem trueLit_neqI {a b : ℕ} (h : a ≠ b) :
    TrueLit (∼(eqI (numI a) (numI b) : Proposition (LIinfN n))) := by
  have hl : IsArithLit (eqI (numI a) (numI b)) :=
    ⟨2, Language.Eq.eq, ![numI a, numI b], Or.inl rfl, fun i => by
      match i with
      | ⟨0, h⟩ =>
        have h0 : (![numI a, numI b] : Fin 2 → SyntacticTerm (LIinfN n)) ⟨0, h⟩ = numI a := rfl
        rw [h0]; exact numI_freeVariables a
      | ⟨1, h⟩ =>
        have h1 : (![numI a, numI b] : Fin 2 → SyntacticTerm (LIinfN n)) ⟨1, h⟩ = numI b := rfl
        rw [h1]; exact numI_freeVariables b⟩
  refine ⟨hl.neg, (trueN_neg _).mpr ?_⟩
  unfold TrueN eqI
  rw [Semiformula.eval_rel]
  show ¬ (Semiterm.val (s := stdInfN) ![] (fun _ => 0) (numI a) =
    Semiterm.val (s := stdInfN) ![] (fun _ => 0) (numI b))
  rw [val_numI, val_numI]
  exact h

theorem freeVariables_IOmegaAt_numI (a : ℕ) : (IOmegaAt k (numI a)).freeVariables = ∅ := by
  ext x
  simp [IOmegaAt, stageAt, Semiformula.freeVariables, numI_freeVariables]

@[simp] theorem params_eqI {ξ : Type*} {m : ℕ} (t u : Semiterm (LIinfN n) ξ m) :
    params (eqI t u) = ∅ := rfl

/-- **The instance of the equality axiom for `I_k` at `a`, `b`**: `a ≠ b` is a true literal, and
for `a = b` Lemma 6.1 applies (Freund, proof of Theorem 6.5). -/
theorem relI0_derivable (hAb : FamilyLevelBounded A)
    (hH : ThetaWNoteD.NiceS H) (a b : ℕ) :
    IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.nadd (ThetaWNoteD.Omega k.val) (ThetaWNoteD.ofNat 3))
      [relI0 k a b] := by
  have hΩ : ThetaWNoteD.Omega k.val ∈ H ∅ := hH.Omega_mem k.val
  have hm : ∀ j, ThetaWNoteD.nadd (ThetaWNoteD.Omega k.val) (ThetaWNoteD.ofNat j) ∈ H ∅ :=
    fun j => hH.nadd_mem hΩ (hH.ofNat_mem j)
  have hSk : ∀ {φ : Proposition (LIinfN n)}, params φ ⊆ {Stage.top k} →
      Stage.val '' params φ ⊆ H ∅ := by
    rintro φ hφ x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff.mp (hφ hs)]
    simpa using hΩ
  have hPm : ∀ Γ : Sequent (LIinfN n), (∀ φ ∈ Γ, params φ ⊆ {Stage.top k}) →
      paramsVal Γ ⊆ H ∅ := by
    intro Γ
    induction Γ with
    | nil => intro _; simp
    | cons φ Γ ih =>
      intro h
      rw [paramsVal_cons]
      exact Set.union_subset (hSk (h φ List.mem_cons_self))
        (ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))
  have pM : params (relI0 k a b) ⊆ {Stage.top k} := by
    intro x hx
    simp [relI0, IOmegaAt] at hx
    exact hx
  have hlt : ∀ i j : ℕ, i < j → ThetaWNoteD.nadd (ThetaWNoteD.Omega k.val) (ThetaWNoteD.ofNat i) <
      ThetaWNoteD.nadd (ThetaWNoteD.Omega k.val) (ThetaWNoteD.ofNat j) :=
    fun i j h => ThetaWNoteD.nadd_ofNat_lt_nadd_ofNat' _ h
  have hone : ∀ j, ThetaWNoteD.one < ThetaWNoteD.nadd (ThetaWNoteD.Omega k.val) (ThetaWNoteD.ofNat j) :=
    fun j => lt_of_lt_of_le
      (ThetaWNoteD.one_lt_prin (p := ThetaWNoteD.Omega k.val) trivial) (ThetaWNoteD.le_nadd_left _ _)
  have h0 : ThetaWNoteD.nadd (ThetaWNoteD.Omega k.val) (ThetaWNoteD.ofNat 0) = ThetaWNoteD.Omega k.val := by
    rw [ThetaWNoteD.ofNat_zero, ThetaWNoteD.nadd_zero]
  have hlt0 : ThetaWNoteD.Omega k.val < ThetaWNoteD.nadd (ThetaWNoteD.Omega k.val) (ThetaWNoteD.ofNat 1) := by
    have := hlt 0 1 (by omega); rwa [h0] at this
  by_cases hab : a = b
  · subst hab
    have d0 := taut hAb hH (IOmegaAt k (numI a)) (freeVariables_IOmegaAt_numI k a)
    rw [params_IOmegaAt, Set.image_singleton, Stage.val_top, rk_IOmegaAt, ThetaWNoteD.omegaMul_Omega,
      ThetaWNoteD.adjoin_eq_self hH.isOperator (Set.singleton_subset_iff.mpr hΩ)] at d0
    set P : Proposition (LIinfN n) := ∼(IOmegaAt k (numI a)) with hP
    set Q : Proposition (LIinfN n) := IOmegaAt k (numI a) with hQ
    set N : Proposition (LIinfN n) := ∼(eqI (numI a) (numI a) ⋏ ⊤) with hN
    have eM : relI0 k a a = N ⋎ (P ⋎ Q) := rfl
    have pP : params P ⊆ {Stage.top k} := by rw [hP, params_neg, params_IOmegaAt]
    have pQ : params Q ⊆ {Stage.top k} := by rw [hQ, params_IOmegaAt]
    have pD : params (P ⋎ Q) ⊆ {Stage.top k} := by
      rw [params_or]; exact Set.union_subset pP pQ
    have d1 : IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.Omega k.val) [Q, P, P ⋎ Q, relI0 k a a] :=
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
    have d2 : IDnDerivable A ThetaWNoteD.zero H
        (ThetaWNoteD.nadd (ThetaWNoteD.Omega k.val) (ThetaWNoteD.ofNat 1)) [P, P ⋎ Q, relI0 k a a] :=
      .orR (hm 1) (hPm _ (by
          intro φ hφ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
          rcases hφ with rfl | rfl | rfl
          · exact pP
          · exact pD
          · exact pM))
        (List.mem_cons_of_mem _ List.mem_cons_self) (hone 1)
        hlt0 d1
    have d3 : IDnDerivable A ThetaWNoteD.zero H
        (ThetaWNoteD.nadd (ThetaWNoteD.Omega k.val) (ThetaWNoteD.ofNat 2)) [P ⋎ Q, relI0 k a a] :=
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
  · set N : Proposition (LIinfN n) := ∼(eqI (numI a) (numI b) ⋏ ⊤) with hN
    have eN : N = ∼(eqI (numI a) (numI b)) ⋎ ⊥ := by rw [hN]; simp
    have pN : params N ⊆ {Stage.top k} := by
      rw [eN]; simp
    have pE : params (∼(eqI (numI a) (numI b)) : Proposition (LIinfN n)) ⊆ {Stage.top k} := by
      simp
    have e1 : IDnDerivable A ThetaWNoteD.zero H (ThetaWNoteD.Omega k.val)
        [∼(eqI (numI a) (numI b)), N, relI0 k a b] :=
      .literal hΩ (hPm _ (by
          intro φ hφ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
          rcases hφ with rfl | rfl | rfl
          · exact pE
          · exact pN
          · exact pM))
        (trueLit_neqI hab) List.mem_cons_self
    have e2 : IDnDerivable A ThetaWNoteD.zero H
        (ThetaWNoteD.nadd (ThetaWNoteD.Omega k.val) (ThetaWNoteD.ofNat 1)) [N, relI0 k a b] :=
      .orL (hm 1) (hPm _ (by
          intro φ hφ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
          rcases hφ with rfl | rfl
          · exact pN
          · exact pM))
        (by rw [← eN]; exact List.mem_cons_self) hlt0 e1
    have e3 : IDnDerivable A ThetaWNoteD.zero H
        (ThetaWNoteD.nadd (ThetaWNoteD.Omega k.val) (ThetaWNoteD.ofNat 2)) [relI0 k a b] :=
      .orL (hm 2) (hPm _ (by
          intro φ hφ
          rw [List.mem_singleton.mp hφ]; exact pM))
        List.mem_cons_self (hlt 1 2 (by omega)) e2
    exact e3.mono_height (le_of_lt (hlt 2 3 (by omega))) (hm 3)

/-- `params (relI2 k) ⊆ {Stage.top k}` (`Set (Stage n)` level, matches `relI0_derivable`'s `pM`). -/
theorem params_relI2_subset : params (relI2 k) ⊆ {Stage.top k} := by
  intro x hx
  simp [relI2, IOmegaAt] at hx
  exact hx

/-- Converts a `Set (Stage n)` bound `params φ ⊆ {Stage.top k}` into the `Set ThetaWNoteD`
membership the calculus's operators actually control. -/
theorem stageValImage_subset_of_subset_singleton {φ : Proposition (LIinfN n)}
    (h : params φ ⊆ {Stage.top k}) {X : Set ThetaWNoteD} (hΩ : ThetaWNoteD.Omega k.val ∈ X) :
    Stage.val '' params φ ⊆ X := by
  rintro x ⟨s, hs, rfl⟩
  rw [Set.mem_singleton_iff.mp (h hs)]
  simpa using hΩ

/-- **The equality axiom for `I_k`** (Freund, proof of Theorem 6.5), at level `k`. -/
theorem relExtI_axiom (hAb : FamilyLevelBounded A) :
    AxDerivable_al A (Theory.Eq.relExt (Sum.inr (IXRelN.I k) : (LXIn n).Rel 1)) := by
  have hkn : k.val ≤ n - 1 := by have := k.isLt; omega
  refine axDerivable_of_le_al 5 (ThetaWNoteD.nadd
    (ThetaWNoteD.nadd (ThetaWNoteD.Omega k.val) (ThetaWNoteD.ofNat 3)) (ThetaWNoteD.ofNat 2))
    ?_ (fun H hH => ?_)
  · rw [ThetaWNoteD.nadd_assoc, ThetaWNoteD.ofNat_nadd_ofNat]
    exact le_trans (ThetaWNoteD.nadd_le_nadd_left' _ (Omega_le_Omega_of_le hkn))
      (ThetaWNoteD.nadd_le_nadd_left' _ (ThetaWNoteD.le_nadd_left _ _))
  · rw [emb_embK_relExtI]
    refine allClosure_derivable hH.isOperator (relI2 k)
      (fun j => hH.nadd_mem (hH.nadd_mem (hH.Omega_mem k.val) (hH.ofNat_mem 3)) (hH.ofNat_mem j))
      (by
        intro x hx
        obtain ⟨s, hs, rfl⟩ := hx
        rw [Set.mem_singleton_iff.mp (params_relI2_subset k hs)]
        simpa using hH.Omega_mem k.val)
      (fun w => ?_)
    rw [relI2_inst]
    exact relI0_derivable k hAb hH _ _

end RelExtI

/-- **The equality axioms** (Freund, proof of Theorem 6.5). -/
theorem eq_axiom (hAb : FamilyLevelBounded A) {σ : Sentence (LXIn n)}
    (h : σ ∈ 𝗘𝗤 (LXIn n)) : AxDerivable_al A σ := by
  have ht := eval_of_eqAxiom (fun _ => False) (fun _ : Fin n => (∅ : Set ℕ)) h
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
      | I j => exact relExtI_axiom j hAb

end EqPA

end IDn

end OrdinalAnalysis
