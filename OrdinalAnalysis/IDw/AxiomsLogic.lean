/- Source: OrdinalAnalysis\IDn\AxiomsLogic.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.Evaluate
import OrdinalAnalysis.IDw.NumSubst
import OrdinalAnalysis.IDw.Sound
/-
  The tautology lemma and the logical and arithmetical axioms of `ID_ω`, the uniform theory
  `IDw A` with stage predicates `I_k^{≺α}`, `k : ℕ`, and the binary level atoms `Jlev ℓ`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §6: Lemma 6.1, and the proof of Theorem 6.5 (the
  axioms of `PA ⊆ ID₁` "treated as in the proof of Theorem 3.7 of the first lecture", and
  the equality axiom for `I_φ`). As ported by `IDn/AxiomsLogic.lean` (`ID1/AxiomsLogic.lean`
  with levels): Lemma 6.1 and the arithmetic completeness are level-free (the stage clause of
  Lemma 6.1 carries an explicit level `k`, unfolding through `unfoldW A k`, which needs no
  boundedness hypothesis on `A`).  New in `IDw`: the closed level atoms `Jlev ℓ (s,t)` and their
  negations are tautologies via the rules `(jlev)`/`(njlev)` (`taut_jlev`: the premise is the
  tautology of the stage atom `I_{val s} t`, of strictly smaller rank,
  `rk_IOmegaAt_lt_jlevAt`), and the theory's one binary predicate `J` (embedded as
  `Jlev ⊤`) replaces the level-indexed `I_k`: its equality axiom is *one* sentence
  (`relExtJ_axiom`) instead of one per level.

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
  of `X` and `J` as empty (`trueN_emb_embK`) this gives every axiom of `𝗣𝗔⁻` and
  every equality axiom except the one for `J` (`paMinus_axiom`, `eq_axiom`).  The
  equality axiom for `J` is derived by hand as in Freund: for unequal numeral arguments
  a true literal, and for equal ones Lemma 6.1 applies (`relJ0_derivable`, `relExtJ_axiom`).
  The top height is `Ω_ω · 2 + m` (`AxDerivable_al`).

  Contents.

    height arithmetic: `succ_max_lt`, `omegaMul_nadd_lt_omegaMul_succ`, …
    `NiceS.rk_memL`                                    `rk φ ∈ H(X)` (with `Jlev` atoms)
    `taut_and`, `taut_all`, `taut_stage`, `taut_jlev`, `taut`   **Lemma 6.1**
    `ArithF`, `trueN_all`, `trueN_exs`, `omega_complete`
    `eval_embK`, `trueN_emb_embK`                      `X` and `J` read as empty
    `allClosure_derivable`                             the universal closure, by the ω-rule
    `IFreeL`, `paMinus_axiom`, `eq_axiom`, `relJ0_derivable`, `relExtJ_axiom`
-/

set_option autoImplicit false

namespace OrdinalAnalysis


/-! ### Height arithmetic -/

namespace ThetaVNoteD

/-- Convenience projection, matching `Nice.isOperator`'s ergonomics for the level-free `NiceS`
(`Ordinal/ThetaW/HullSingle.lean` does not itself register one; not duplicated elsewhere). -/
theorem NiceS.isOperator {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : NiceS H) : IsOperator H :=
  hH.1

/-- The finite notations lie below `ω = ω^1`. -/
theorem ofNat_lt_omega (p : ℕ) : ofNat p < omegaPow one := by
  rw [lt_omegaPow_iff, entries_ofNat]
  intro e he
  rw [List.eq_of_mem_replicate he]
  exact zero_lt_one

theorem nadd_ofNat_one (a : ThetaVNoteD) : ThetaVNoteD.nadd a (ofNat 1) = succ a := by
  rw [ofNat_one]; rfl

theorem succ_max_lt {p q B : ThetaVNoteD} (hp : succ p < B) (hq : succ q < B) :
    succ (max p q) < B := by
  rcases le_total p q with h | h
  · rw [max_eq_right h]; exact hq
  · rw [max_eq_left h]; exact hp

/-- `ω · x ⊕ p ≺ ω · (m + 1)` for `x ⪯ m`. -/
theorem omegaMul_nadd_lt_omegaMul_succ {x m : ThetaVNoteD} (h : x ≤ m) (p : ℕ) :
    ThetaVNoteD.nadd (omegaMul x) (ofNat p) < omegaMul (succ m) :=
  omegaMul_nadd_ofNat_lt (lt_of_le_of_lt h (lt_succ m)) p

/-- `p ≺ ω · (m + 1)`. -/
theorem ofNat_lt_omegaMul_succ (m : ThetaVNoteD) (p : ℕ) : ofNat p < omegaMul (succ m) := by
  have h := omegaMul_nadd_ofNat_lt (lt_of_le_of_lt (zero_le' m) (lt_succ m)) p
  rwa [omegaMul_zero, zero_nadd] at h

/-- `γ + 1 ≺ ω · ω · δ` for `γ ≺ δ`: the stage weight in Lemma 6.1. -/
theorem succ_lt_omegaMul_omegaMul {g a : ThetaVNoteD} (h : g < a) :
    succ g < omegaMul (omegaMul a) := by
  have h1 : succ g ≤ succ (omegaMul g) := succ_le_succ (ThetaVNoteD.le_omegaMul g)
  have h2 : succ (omegaMul g) < omegaMul a := by
    rw [← nadd_ofNat_one]; exact omegaMul_nadd_ofNat_lt h 1
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (ThetaVNoteD.le_omegaMul _))

theorem succ_omegaMul_lt {x y : ThetaVNoteD} (h : x < y) : succ (omegaMul x) < omegaMul y := by
  rw [← nadd_ofNat_one]; exact omegaMul_nadd_ofNat_lt h 1

theorem lt_nadd_ofNat_succ (a : ThetaVNoteD) (p : ℕ) : a < ThetaVNoteD.nadd a (ofNat (p + 1)) :=
  lt_of_lt_of_le (lt_succ a) (by
    rw [← nadd_ofNat_one]
    exact nadd_le_nadd_right a (ofNat_le_ofNat (by omega)))

theorem ofNat_lt_nadd_ofNat_succ (a : ThetaVNoteD) (p : ℕ) :
    ofNat p < ThetaVNoteD.nadd a (ofNat (p + 1)) :=
  lt_of_lt_of_le (ofNat_lt_ofNat (Nat.lt_succ_self p)) (le_nadd_right _ _)

theorem nadd_ofNat_lt_nadd_ofNat' (a : ThetaVNoteD) {j p : ℕ} (h : j < p) :
    ThetaVNoteD.nadd a (ofNat j) < ThetaVNoteD.nadd a (ofNat p) :=
  nadd_lt_nadd_right a (ofNat_lt_ofNat h)

theorem one_lt_nadd_ofNat_two (a : ThetaVNoteD) : one < ThetaVNoteD.nadd a (ofNat 2) := by
  rw [← ofNat_one]; exact ofNat_lt_nadd_ofNat_succ a 1

theorem ofNat_nadd_ofNat (p : ℕ) : ∀ q : ℕ, ThetaVNoteD.nadd (ofNat p) (ofNat q) = ofNat (p + q)
  | 0 => by rw [ofNat_zero, nadd_zero, Nat.add_zero]
  | q + 1 => by
    rw [ofNat_succ, succ, ← nadd_assoc, ofNat_nadd_ofNat p q, ← succ, ← ofNat_succ]; rfl

end ThetaVNoteD

namespace IDw

open LO LO.FirstOrder

/-- **`rk φ ∈ H(X)`** once every stage parameter of `φ` is in `H(X)`: `Jlev` atoms (`Ω_k + 1`,
`Ω_ω`) and arithmetic (`0`) never obstruct, since they lie in every nice hull.  (The bare-`S`
form `IDn.rk_mem_of_closed` is false with `Jlev` atoms, see `IDw/CalculusAux.lean`.) -/
theorem _root_.OrdinalAnalysis.ThetaVNoteD.NiceS.rk_memL {K : Set ThetaVNoteD → Set ThetaVNoteD}
    (hK : ThetaVNoteD.NiceS K) {X : Set ThetaVNoteD} {ξ : Type*} {m : ℕ}
    {φ : Semiformula (LIinfW) ξ m} (h : ∀ s ∈ params φ, s.val ∈ K X) : rk φ ∈ K X :=
  hK.rk_mem' h

/-! ### Structural helpers -/

section Helpers

variable {A : Semisentence LForm 2} {ρ : ThetaVNoteD}

/-- Case analysis on a proposition of `LIinfW`, in connective form. -/
theorem cases0 {C : Proposition (LIinfW) → Prop}
    (hverum : C ⊤) (hfalsum : C ⊥)
    (hrel : ∀ (k : ℕ) (r : (LIinfW).Rel k) (v : Fin k → SyntacticTerm (LIinfW)),
      C (Semiformula.rel r v))
    (hnrel : ∀ (k : ℕ) (r : (LIinfW).Rel k) (v : Fin k → SyntacticTerm (LIinfW)),
      C (Semiformula.nrel r v))
    (hand : ∀ φ ψ : Proposition (LIinfW), C (φ ⋏ ψ))
    (hor : ∀ φ ψ : Proposition (LIinfW), C (φ ⋎ ψ))
    (hall : ∀ φ : Semiproposition (LIinfW) 1, C (∀¹ φ))
    (hexs : ∀ φ : Semiproposition (LIinfW) 1, C (∃¹ φ)) :
    ∀ φ : Proposition (LIinfW), C φ
  | Semiformula.verum => hverum
  | Semiformula.falsum => hfalsum
  | Semiformula.rel r v => hrel _ r v
  | Semiformula.nrel r v => hnrel _ r v
  | Semiformula.and φ ψ => hand φ ψ
  | Semiformula.or φ ψ => hor φ ψ
  | Semiformula.all φ => hall φ
  | Semiformula.exs φ => hexs φ

/-- Moving a derivation to a larger operator and a larger sequent. -/
theorem IDwDerivable.lift {K K' : Set ThetaVNoteD → Set ThetaVNoteD} (hK' : ThetaVNoteD.IsOperator K')
    (hKK : ∀ X, K X ⊆ K' X) {h : ThetaVNoteD} {Δ Δ' : Sequent (LIinfW)}
    (d : IDwDerivable A ρ K h Δ) (hsub : Δ ⊆ Δ') (hP : paramsVal Δ' ⊆ K' ∅) :
    IDwDerivable A ρ K' h Δ' :=
  (d.mono_op hKK).weaken_seq hK' hsub hP

theorem adjoin_le_adjoin {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.IsOperator H)
    {Z Z' : Set ThetaVNoteD} (h : Z ⊆ Z') (X : Set ThetaVNoteD) :
    ThetaVNoteD.adjoin H Z X ⊆ ThetaVNoteD.adjoin H Z' X :=
  hH.mono (Set.union_subset_union_left X h)

theorem subset_adjoin_empty {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.IsOperator H)
    (Z : Set ThetaVNoteD) : Z ⊆ ThetaVNoteD.adjoin H Z ∅ := by
  intro x hx
  exact hH.subset _ (Or.inl hx)

theorem freeVariables_subst_numI (φ : Semiformula (LIinfW) ℕ 1) (hφ : φ.freeVariables = ∅)
    (p : ℕ) : (φ/[numI p]).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![numI p]) (φ := φ) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ ((Rew.subst ![numI p]) #i : SyntacticTerm (LIinfW)).freeVariables := hi
    cases i using Fin.cases with
    | zero => simp only [Rew.subst_bvar, Matrix.cons_val_zero, numI_freeVariables] at hi'
              exact Finset.notMem_empty x hi'
    | succ i => exact i.elim0
  · have hz' : z ∈ φ.freeVariables := hz
    rw [hφ] at hz'
    exact Finset.notMem_empty z hz'

theorem freeVariables_subst_of_closed (φ : Semiformula (LIinfW) ℕ 1) (hφ : φ.freeVariables = ∅)
    {t : SyntacticTerm (LIinfW)} (ht : t.freeVariables = ∅) : (φ/[t]).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![t]) (φ := φ) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ ((Rew.subst ![t]) #i : SyntacticTerm (LIinfW)).freeVariables := hi
    cases i using Fin.cases with
    | zero => simp only [Rew.subst_bvar, Matrix.cons_val_zero, ht] at hi'
              exact Finset.notMem_empty x hi'
    | succ i => exact i.elim0
  · have hz' : z ∈ φ.freeVariables := hz
    rw [hφ] at hz'
    exact Finset.notMem_empty z hz'

/-- The sequent `ψ, ¬ψ` read backwards. -/
theorem IDwDerivable.swap {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.IsOperator H)
    {h : ThetaVNoteD} {ψ : Proposition (LIinfW)} (d : IDwDerivable A ρ H h [∼ψ, ψ]) :
    IDwDerivable A ρ H h [ψ, ∼ψ] := by
  refine d.weaken_seq (Γ' := [ψ, ∼ψ]) hH (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) ?_
  have := d.params_subset
  simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty] at this ⊢
  exact this

end Helpers

/-! ### Lemma 6.1 -/

section Taut

variable {A : Semisentence LForm 2} {H : Set ThetaVNoteD → Set ThetaVNoteD}

theorem params_sub_adjoin (hH : ThetaVNoteD.IsOperator H) {ψ : Proposition (LIinfW)} :
    paramsVal [ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ := by
  simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty, Set.union_self]
  exact subset_adjoin_empty hH _

/-- Membership in `H(k(ψ))`, pointwise: the form `NiceS.rk_mem` wants. -/
theorem mem_adjoin_params (hH : ThetaVNoteD.IsOperator H) {ψ : Proposition (LIinfW)}
    {s : Stage} (hs : s ∈ params ψ) : s.val ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
  subset_adjoin_empty hH _ ⟨s, hs, rfl⟩

/-- **Lemma 6.1, conjunction.** -/
theorem taut_and (hH : ThetaVNoteD.NiceS H) {φ₀ φ₁ : Proposition (LIinfW)}
    (ih₀ : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params φ₀))
      (ThetaVNoteD.omegaMul (rk φ₀)) [φ₀, ∼φ₀])
    (ih₁ : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params φ₁))
      (ThetaVNoteD.omegaMul (rk φ₁)) [φ₁, ∼φ₁]) :
    IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params (φ₀ ⋏ φ₁)))
      (ThetaVNoteD.omegaMul (rk (φ₀ ⋏ φ₁))) [φ₀ ⋏ φ₁, ∼(φ₀ ⋏ φ₁)] := by
  set ψ : Proposition (LIinfW) := φ₀ ⋏ φ₁ with hψ
  have hK := hH.adjoin (Stage.val '' params ψ)
  have hKo := hK.isOperator
  have hZ : Stage.val '' params ψ ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    subset_adjoin_empty hH.isOperator _
  have hΓ : paramsVal [ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    params_sub_adjoin hH.isOperator
  have hneg : ∼ψ = ∼φ₀ ⋎ ∼φ₁ := by simp [hψ]
  have hrk : rk ψ = ThetaVNoteD.succ (max (rk φ₀) (rk φ₁)) := rk_and φ₀ φ₁
  have hs0 : params φ₀ ⊆ params ψ := Set.subset_union_left
  have hs1 : params φ₁ ⊆ params ψ := Set.subset_union_right
  have hs0' : Stage.val '' params φ₀ ⊆ Stage.val '' params ψ := Set.image_mono hs0
  have hs1' : Stage.val '' params φ₁ ⊆ Stage.val '' params ψ := Set.image_mono hs1
  -- the heights
  have hm0 : ThetaVNoteD.omegaMul (rk φ₀) ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_memL (fun s hs => mem_adjoin_params hH.isOperator (hs0 hs)))
  have hm1 : ThetaVNoteD.omegaMul (rk φ₁) ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_memL (fun s hs => mem_adjoin_params hH.isOperator (hs1 hs)))
  have hmψ : ThetaVNoteD.omegaMul (rk ψ) ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_memL (fun s hs => mem_adjoin_params hH.isOperator hs))
  have hP : ∀ φ : Proposition (LIinfW), params φ ⊆ params ψ →
      paramsVal [∼φ, φ, ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ := by
    intro φ hφ
    simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty]
    exact Set.union_subset ((Set.image_mono hφ).trans hZ)
      (Set.union_subset ((Set.image_mono hφ).trans hZ) (Set.union_subset hZ hZ))
  have hP' : ∀ φ : Proposition (LIinfW), params φ ⊆ params ψ →
      paramsVal [φ, ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ := by
    intro φ hφ
    simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty]
    exact Set.union_subset ((Set.image_mono hφ).trans hZ) (Set.union_subset hZ hZ)
  have d0 : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.omegaMul (rk φ₀)) [∼φ₀, φ₀, ψ, ∼ψ] :=
    ih₀.lift hKo (adjoin_le_adjoin hH.isOperator hs0')
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) (hP φ₀ hs0)
  have d1 : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.omegaMul (rk φ₁)) [∼φ₁, φ₁, ψ, ∼ψ] :=
    ih₁.lift hKo (adjoin_le_adjoin hH.isOperator hs1')
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) (hP φ₁ hs1)
  have e0 : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk φ₀)) (ThetaVNoteD.ofNat 2)) [φ₀, ψ, ∼ψ] :=
    .orL (hK.nadd_mem hm0 (hK.ofNat_mem 2)) (hP' φ₀ hs0)
      (by rw [← hneg]; simp) (ThetaVNoteD.lt_nadd_ofNat_succ _ 1) d0
  have e1 : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk φ₁)) (ThetaVNoteD.ofNat 2)) [φ₁, ψ, ∼ψ] :=
    .orR (hK.nadd_mem hm1 (hK.ofNat_mem 2)) (hP' φ₁ hs1)
      (by rw [← hneg]; simp) (ThetaVNoteD.one_lt_nadd_ofNat_two _)
      (ThetaVNoteD.lt_nadd_ofNat_succ _ 1) d1
  refine .and hmψ hΓ List.mem_cons_self ?_ ?_ e0 e1
  · rw [hrk]; exact ThetaVNoteD.omegaMul_nadd_lt_omegaMul_succ (le_max_left _ _) 2
  · rw [hrk]; exact ThetaVNoteD.omegaMul_nadd_lt_omegaMul_succ (le_max_right _ _) 2

/-- **Lemma 6.1, universal quantifier.** -/
theorem taut_all (hH : ThetaVNoteD.NiceS H) {φ : Semiproposition (LIinfW) 1}
    (ih : ∀ p : ℕ, IDwDerivable A ThetaVNoteD.zero
      (ThetaVNoteD.adjoin H (Stage.val '' params (φ/[numI p])))
      (ThetaVNoteD.omegaMul (rk (φ/[numI p]))) [φ/[numI p], ∼(φ/[numI p])]) :
    IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params (∀¹ φ)))
      (ThetaVNoteD.omegaMul (rk (∀¹ φ))) [∀¹ φ, ∼(∀¹ φ)] := by
  set ψ : Proposition (LIinfW) := ∀¹ φ with hψ
  have hK := hH.adjoin (Stage.val '' params ψ)
  have hKo := hK.isOperator
  have hZ : Stage.val '' params ψ ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    subset_adjoin_empty hH.isOperator _
  have hΓ : paramsVal [ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    params_sub_adjoin hH.isOperator
  have hneg : ∼ψ = ∃¹ (∼φ) := by simp [hψ]
  have hrk : rk ψ = ThetaVNoteD.succ (rk φ) := rk_all φ
  have hsp : ∀ p, params (φ/[numI p]) = params ψ := fun p => params_subst1 φ _
  have hmφ : ThetaVNoteD.omegaMul (rk φ) ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_memL (fun s hs => mem_adjoin_params hH.isOperator
      (show s ∈ params φ from hs)))
  have hmψ : ThetaVNoteD.omegaMul (rk ψ) ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_memL (fun s hs => mem_adjoin_params hH.isOperator hs))
  refine .all (fun p => ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk φ)) (ThetaVNoteD.ofNat (p + 1)))
    hmψ hΓ (φ := φ) List.mem_cons_self (fun p => by
      rw [hrk]; exact ThetaVNoteD.omegaMul_nadd_lt_omegaMul_succ le_rfl _) (fun p => ?_)
  have hPp : paramsVal [φ/[numI p], ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ := by
    simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty, hsp p]
    exact Set.union_subset hZ (Set.union_subset hZ hZ)
  have d : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.omegaMul (rk φ)) [(∼φ)/[numI p], φ/[numI p], ψ, ∼ψ] := by
    have e : (∼φ)/[numI p] = ∼(φ/[numI p]) := by simp
    rw [e]
    have ihp := ih p
    rw [rk_subst] at ihp
    refine ihp.lift hKo (fun X => by rw [hsp p]) (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) ?_
    simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty, hsp p]
    exact Set.union_subset hZ (Set.union_subset hZ (Set.union_subset hZ hZ))
  exact .exs p (hK.nadd_mem hmφ (hK.ofNat_mem _)) hPp (by rw [← hneg]; simp)
    (ThetaVNoteD.ofNat_lt_nadd_ofNat_succ _ p) (ThetaVNoteD.lt_nadd_ofNat_succ _ p) d

/-- **Lemma 6.1, stage atom** `I_k^{≺δ} t`, at level `k`. -/
theorem taut_stage (hH : ThetaVNoteD.NiceS H) (k : ℕ)
    (a : StageAt k) (t : SyntacticTerm (LIinfW))
    (ih : ∀ g : StageAt k, g.1 < a.1 →
      IDwDerivable A ThetaVNoteD.zero
        (ThetaVNoteD.adjoin H (Stage.val '' params (unfoldW A k g t)))
        (ThetaVNoteD.omegaMul (rk (unfoldW A k g t)))
        [unfoldW A k g t, ∼(unfoldW A k g t)]) :
    IDwDerivable A ThetaVNoteD.zero
      (ThetaVNoteD.adjoin H (Stage.val '' params (stageAt (⟨k, a⟩ : Stage) t)))
      (ThetaVNoteD.omegaMul (rk (stageAt (⟨k, a⟩ : Stage) t)))
      [stageAt (⟨k, a⟩ : Stage) t, ∼(stageAt (⟨k, a⟩ : Stage) t)] := by
  set ψ : Proposition (LIinfW) := stageAt (⟨k, a⟩ : Stage) t with hψ
  have hK := hH.adjoin (Stage.val '' params ψ)
  have hZ : Stage.val '' params ψ ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    subset_adjoin_empty hH.isOperator _
  have hΓ : paramsVal [ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    params_sub_adjoin hH.isOperator
  have hmψ : ThetaVNoteD.omegaMul (rk ψ) ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_memL (fun s hs => mem_adjoin_params hH.isOperator hs))
  refine .nstage (fun g => ThetaVNoteD.succ (max (ThetaVNoteD.omegaMul (rk (unfoldW A k g t))) g.1))
    hmψ hΓ (a := a) (t := t) (List.mem_cons_of_mem _ List.mem_cons_self) (fun g hg => ?_)
    (fun g hg => ?_)
  · rw [hψ, rk_stageAt]
    refine ThetaVNoteD.succ_max_lt ?_ (lt_of_lt_of_le (ThetaVNoteD.succ_lt_omegaMul_omegaMul hg)
      (ThetaVNoteD.omegaMul_le_omegaMul (ThetaVNoteD.le_add_left _ _)))
    refine ThetaVNoteD.succ_omegaMul_lt ?_
    have := rk_unfold_lt_stageAt A hg t t
    rwa [rk_stageAt] at this
  · -- the premise for `g`, by clause (W) on `I_k^{≺δ} t` with the witness `g`
    set K' := ThetaVNoteD.adjoin (ThetaVNoteD.adjoin H (Stage.val '' params ψ)) {g.1} with hK'
    have hK'n : ThetaVNoteD.NiceS K' := hK.adjoin {g.1}
    have hg' : g.1 ∈ K' ∅ := subset_adjoin_empty hK.isOperator {g.1} rfl
    have hsub : Stage.val '' params ψ ⊆ K' ∅ :=
      hZ.trans (hK.isOperator.mono (Set.empty_subset _))
    -- every parameter of the unfolding is `g` itself or some *lower* level's top, and every
    -- `NiceS` operator already contains every level's top unconditionally (`NiceS.Omega_mem`)
    have huP : ∀ s ∈ params (unfoldW A k g t), s.val ∈ K' ∅ := by
      intro s hs
      have h1 := params_unfoldW A k g t hs
      rw [Set.mem_singleton_iff] at h1
      subst h1
      exact hg'
    have hu : Stage.val '' params (unfoldW A k g t) ⊆ K' ∅ :=
      fun _ ⟨s, hs, hx⟩ => hx ▸ huP s hs
    have hmu : ThetaVNoteD.omegaMul (rk (unfoldW A k g t)) ∈ K' ∅ :=
      hK'n.omegaMul_mem (hK'n.rk_memL huP)
    have hmax : max (ThetaVNoteD.omegaMul (rk (unfoldW A k g t))) g.1 ∈ K' ∅ := by
      rcases le_total (ThetaVNoteD.omegaMul (rk (unfoldW A k g t))) g.1 with h | h
      · rw [max_eq_right h]; exact hg'
      · rw [max_eq_left h]; exact hmu
    have hP : paramsVal [∼(unfoldW A k g t), ψ, ∼ψ] ⊆ K' ∅ := by
      simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty]
      exact Set.union_subset hu (Set.union_subset hsub hsub)
    have hP2 : paramsVal [unfoldW A k g t, ∼(unfoldW A k g t), ψ, ∼ψ] ⊆ K' ∅ := by
      simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty]
      exact Set.union_subset hu (Set.union_subset hu (Set.union_subset hsub hsub))
    have hop : ∀ X, ThetaVNoteD.adjoin H (Stage.val '' params (unfoldW A k g t)) X ⊆ K' X := by
      intro X
      refine hH.isOperator.2 _ _ (Set.union_subset ?_ (hK'n.isOperator.1 X))
      exact fun x hx => (hK'n.isOperator.2 ∅ X (Set.empty_subset _)) (hu hx)
    have d : IDwDerivable A ThetaVNoteD.zero K' (ThetaVNoteD.omegaMul (rk (unfoldW A k g t)))
        [unfoldW A k g t, ∼(unfoldW A k g t), ψ, ∼ψ] :=
      (ih g hg).lift hK'n.isOperator hop
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) hP2
    exact .stage g (hK'n.succ_mem hmax) hP (a := a) (t := t)
      (List.mem_cons_of_mem _ List.mem_cons_self) hg
      (lt_of_le_of_lt (le_max_right _ _) (ThetaVNoteD.lt_succ _)) hg'
      (lt_of_le_of_lt (le_max_left _ _) (ThetaVNoteD.lt_succ _)) d

/-- A derivation of `¬ψ, ¬¬ψ` is one of `ψ, ¬ψ`. -/
theorem taut_neg (hH : ThetaVNoteD.NiceS H) {ψ : Proposition (LIinfW)}
    (d : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params (∼ψ)))
      (ThetaVNoteD.omegaMul (rk (∼ψ))) [∼ψ, ∼(∼ψ)]) :
    IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.omegaMul (rk ψ)) [ψ, ∼ψ] := by
  rw [params_neg, rk_neg] at d
  have e : ∼(∼ψ) = ψ := by simp
  rw [e] at d
  exact d.swap (hH.adjoin _).isOperator

theorem freeVariables_rel_closed {k : ℕ} (r : (LIinfW).Rel k) (v : Fin k → SyntacticTerm (LIinfW))
    (hv : ∀ i, (v i).freeVariables = ∅) : (Semiformula.rel r v).freeVariables = ∅ := by
  rw [Semiformula.freeVariables_rel]
  ext x
  simp [hv]

/-- `I_k t` with `t` closed is closed. -/
theorem freeVariables_IOmegaAt {t : SyntacticTerm (LIinfW)} (ht : t.freeVariables = ∅) (k : ℕ) :
    (IOmegaAt k t).freeVariables = ∅ := by
  unfold IOmegaAt stageAt
  refine freeVariables_rel_closed _ _ fun i => ?_
  obtain rfl := Subsingleton.elim i 0
  exact ht

/-- **The unfolding of a closed term is closed.** -/
theorem freeVariables_unfold {A : Semisentence LForm 2} (k : ℕ) (a : StageAt k)
    {t : SyntacticTerm (LIinfW)} (ht : t.freeVariables = ∅) :
    (unfoldW A k a t).freeVariables = ∅ := by
  unfold unfoldW
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![t, Semiterm.numeral k])
    (φ := (Rewriting.emb (formAtW A k a) : Semiformula LIinfW ℕ 2)) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · cases i using Fin.cases with
    | zero =>
      have hi' : x ∈ ((Rew.subst ![t, Semiterm.numeral k] : Rew LIinfW ℕ 2 ℕ 0) #0 :
          SyntacticTerm LIinfW).freeVariables := hi
      simp only [Rew.subst_bvar, Matrix.cons_val_zero, ht] at hi'
      exact Finset.notMem_empty x hi'
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        have hi' : x ∈ ((Rew.subst ![t, Semiterm.numeral k] : Rew LIinfW ℕ 2 ℕ 0) #1 :
            SyntacticTerm LIinfW).freeVariables := hi
        simp only [Rew.subst_bvar, Matrix.cons_val_one, Matrix.cons_val_zero,
          numeral_freeVariables] at hi'
        exact Finset.notMem_empty x hi'
      | succ i => exact i.elim0
  · have hz' : z ∈ (Rewriting.emb (formAtW A k a) : Semiformula LIinfW ℕ 2).freeVariables := hz
    rw [Semiformula.freeVariables_emb] at hz'
    exact Finset.notMem_empty z hz'

/-- **Lemma 6.1, level atom** `Jlev ℓ (s,t)`, `s`, `t` closed.  If `val s < ℓ` the rule (jlev) on
`Jlev ℓ (s,t)` and (njlev) on `¬Jlev ℓ (s,t)` reduce to the tautology for the stage atom
`I_{val s} t`, of strictly smaller rank; otherwise `¬Jlev ℓ (s,t)` is an empty conjunction. -/
theorem taut_jlev (hH : ThetaVNoteD.NiceS H) (ℓ : WithTop ℕ) {s t : SyntacticTerm LIinfW}
    (hs : s.freeVariables = ∅) (ht : t.freeVariables = ∅)
    (ih : ((termVal s : ℕ) : WithTop ℕ) < ℓ →
      IDwDerivable A ThetaVNoteD.zero
        (ThetaVNoteD.adjoin H (Stage.val '' params (IOmegaAt (termVal s) t)))
        (ThetaVNoteD.omegaMul (rk (IOmegaAt (termVal s) t)))
        [IOmegaAt (termVal s) t, ∼(IOmegaAt (termVal s) t)]) :
    IDwDerivable A ThetaVNoteD.zero
      (ThetaVNoteD.adjoin H (Stage.val '' params (jlevAt ℓ s t)))
      (ThetaVNoteD.omegaMul (rk (jlevAt ℓ s t))) [jlevAt ℓ s t, ∼(jlevAt ℓ s t)] := by
  have hp : Stage.val '' params (jlevAt ℓ s t) = ∅ := by
    rw [params_jlevAt, Set.image_empty]
  rw [hp]
  have hK := hH.adjoin ∅
  have hmψ : ThetaVNoteD.omegaMul (rk (jlevAt ℓ s t)) ∈ ThetaVNoteD.adjoin H ∅ ∅ :=
    hK.omegaMul_mem (hK.rk_memL (fun x hx => by rw [params_jlevAt] at hx; exact hx.elim))
  have hp1 : paramsVal [jlevAt ℓ s t, ∼(jlevAt ℓ s t)] ⊆ ThetaVNoteD.adjoin H ∅ ∅ := by
    simp [paramsVal_cons, paramsVal_nil, params_jlevAt]
  by_cases hv : ((termVal s : ℕ) : WithTop ℕ) < ℓ
  · set v := termVal s with hvdef
    have hIp : Stage.val '' params (IOmegaAt v t) = {ThetaVNoteD.Omega v} := by
      rw [params_IOmegaAt, Set.image_singleton]; rfl
    have hΩ : ThetaVNoteD.Omega v ∈ ThetaVNoteD.adjoin H ∅ ∅ := hK.Omega_mem v
    have hop : ∀ X, ThetaVNoteD.adjoin H (Stage.val '' params (IOmegaAt v t)) X ⊆
        ThetaVNoteD.adjoin H ∅ X := by
      intro X
      rw [hIp]
      refine hH.isOperator.2 _ _ (Set.union_subset ?_ (fun x hx => hH.isOperator.1 _ (Or.inr hx)))
      exact Set.singleton_subset_iff.mpr (hK.Omega_mem v)
    have hpI : paramsVal (∼(IOmegaAt v t) :: [jlevAt ℓ s t, ∼(jlevAt ℓ s t)]) ⊆
        ThetaVNoteD.adjoin H ∅ ∅ := by
      rw [paramsVal_cons, params_neg, params_IOmegaAt, Set.image_singleton]
      exact Set.union_subset (Set.singleton_subset_iff.mpr hΩ) hp1
    have hpI2 : paramsVal (IOmegaAt v t :: ∼(IOmegaAt v t) :: [jlevAt ℓ s t, ∼(jlevAt ℓ s t)]) ⊆
        ThetaVNoteD.adjoin H ∅ ∅ := by
      rw [paramsVal_cons, params_IOmegaAt, Set.image_singleton]
      exact Set.union_subset (Set.singleton_subset_iff.mpr hΩ) hpI
    have d0 := (ih hv).lift hK.isOperator hop
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) hpI2
    have hβ : ThetaVNoteD.succ (ThetaVNoteD.omegaMul (rk (IOmegaAt v t))) ∈
        ThetaVNoteD.adjoin H ∅ ∅ := by
      rw [rk_IOmegaAt]
      exact hK.succ_mem (hK.omegaMul_mem hΩ)
    have e1 : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H ∅)
        (ThetaVNoteD.succ (ThetaVNoteD.omegaMul (rk (IOmegaAt v t))))
        (∼(IOmegaAt v t) :: [jlevAt ℓ s t, ∼(jlevAt ℓ s t)]) :=
      .jlev hβ hpI (List.mem_cons_of_mem _ List.mem_cons_self) hs ht hv
        (ThetaVNoteD.lt_succ _) d0
    exact .njlev hmψ hp1 (List.mem_cons_of_mem _ List.mem_cons_self) hs ht
      (fun _ => ThetaVNoteD.succ_omegaMul_lt (rk_IOmegaAt_lt_jlevAt hv t s t)) (fun _ => e1)
  · exact .njlev (α₀ := ThetaVNoteD.zero) hmψ hp1 (List.mem_cons_of_mem _ List.mem_cons_self) hs ht
      (fun h => absurd h hv) (fun h => absurd h hv)

/-- **Freund, Lemma 6.1**: `H[k(ψ)] ⊢^{ω·rk(ψ)}_0 ψ, ¬ψ` for every closed formula `ψ` and
every nice operator `H`. -/
theorem taut (hH : ThetaVNoteD.NiceS H) (ψ : Proposition (LIinfW))
    (hc : ψ.freeVariables = ∅) :
    IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.omegaMul (rk ψ)) [ψ, ∼ψ] := by
  suffices key : ∀ r : ThetaVNoteD, ∀ ψ : Proposition (LIinfW), rk ψ = r → ψ.freeVariables = ∅ →
      IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
        (ThetaVNoteD.omegaMul (rk ψ)) [ψ, ∼ψ] from key _ ψ rfl hc
  intro r
  induction r using WellFoundedLT.induction with
  | _ r ih =>
  intro ψ hr hc
  subst hr
  have IH : ∀ φ : Proposition (LIinfW), rk φ < rk ψ → φ.freeVariables = ∅ →
      IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params φ))
        (ThetaVNoteD.omegaMul (rk φ)) [φ, ∼φ] := fun φ h hc' => ih _ h φ rfl hc'
  have hK := hH.adjoin (Stage.val '' params ψ)
  have hZ : Stage.val '' params ψ ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    subset_adjoin_empty hH.isOperator _
  have hα : ThetaVNoteD.omegaMul (rk ψ) ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (hK.rk_memL (fun s hs => mem_adjoin_params hH.isOperator hs))
  have hΓ : paramsVal [ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
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
      have hl : IsArithLit (Semiformula.rel (Sum.inl r : (LIinfW).Rel k) v) :=
        ⟨k, r, v, Or.inl rfl, hv⟩
      by_cases ht : TrueN (Semiformula.rel (Sum.inl r : (LIinfW).Rel k) v)
      · exact .literal hα hΓ ⟨hl, ht⟩ List.mem_cons_self
      · exact .literal hα hΓ ⟨hl.neg, (trueN_neg _).mpr ht⟩
          (List.mem_cons_of_mem _ List.mem_cons_self)
    · cases r with
      | X =>
        have e : Semiformula.rel (Sum.inr IInfRelW.X : (LIinfW).Rel 1) v = XinfAt (v 0) :=
          rel_eq_vec _ v
        have d : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params (XinfAt (v 0))))
            (ThetaVNoteD.omegaMul (rk (XinfAt (v 0)))) [XinfAt (v 0), ∼(XinfAt (v 0))] := by
          rw [← e]
          exact .idX (v 0) hα hΓ (by rw [e]; exact List.mem_cons_self)
            (by rw [e]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        rw [e]; exact d
      | stage s =>
        obtain ⟨k, a⟩ := s
        have e : Semiformula.rel (Sum.inr (IInfRelW.stage ⟨k, a⟩) : (LIinfW).Rel 1) v =
            stageAt ⟨k, a⟩ (v 0) := rel_eq_vec _ v
        have hv0 : (v 0).freeVariables = ∅ := freeVariables_rel_arg hc 0
        rw [e]
        refine taut_stage hH k a (v 0) fun g hg => IH _ ?_ (freeVariables_unfold k g hv0)
        rw [e]
        have := rk_unfold_lt_stageAt A hg (v 0) (v 0)
        simpa using this
      | jlev ℓ =>
        have e : Semiformula.rel (Sum.inr (IInfRelW.jlev ℓ) : (LIinfW).Rel 2) v =
            jlevAt ℓ (v 0) (v 1) := rel_eq_vec2 _ v
        have hv0 : (v 0).freeVariables = ∅ := freeVariables_rel_arg hc 0
        have hv1 : (v 1).freeVariables = ∅ := freeVariables_rel_arg hc 1
        rw [e]
        refine taut_jlev hH ℓ hv0 hv1 fun hl => IH _ ?_ (freeVariables_IOmegaAt hv1 _)
        rw [e]
        exact rk_IOmegaAt_lt_jlevAt hl (v 1) (v 0) (v 1)
  | hnrel k r v =>
    intro hc IH hα hΓ
    rcases r with r | r
    · have hv : ∀ i, (v i).freeVariables = ∅ := freeVariables_nrel_arg hc
      have hl : IsArithLit (Semiformula.nrel (Sum.inl r : (LIinfW).Rel k) v) :=
        ⟨k, r, v, Or.inr rfl, hv⟩
      by_cases ht : TrueN (Semiformula.nrel (Sum.inl r : (LIinfW).Rel k) v)
      · exact .literal hα hΓ ⟨hl, ht⟩ List.mem_cons_self
      · exact .literal hα hΓ ⟨hl.neg, (trueN_neg _).mpr ht⟩
          (List.mem_cons_of_mem _ List.mem_cons_self)
    · cases r with
      | X =>
        have e : Semiformula.nrel (Sum.inr IInfRelW.X : (LIinfW).Rel 1) v = ∼(XinfAt (v 0)) :=
          nrel_eq_vec _ v
        have d : IDwDerivable A ThetaVNoteD.zero
            (ThetaVNoteD.adjoin H (Stage.val '' params (∼(XinfAt (v 0)))))
            (ThetaVNoteD.omegaMul (rk (∼(XinfAt (v 0))))) [∼(XinfAt (v 0)), ∼(∼(XinfAt (v 0)))] := by
          rw [← e]
          exact .idX (v 0) hα hΓ (by rw [e]; exact List.mem_cons_of_mem _ (by simp))
            (by rw [e]; exact List.mem_cons_self)
        rw [e]; exact d
      | stage s =>
        obtain ⟨k, a⟩ := s
        have e : Semiformula.nrel (Sum.inr (IInfRelW.stage ⟨k, a⟩) : (LIinfW).Rel 1) v =
            ∼(stageAt ⟨k, a⟩ (v 0)) := nrel_eq_vec _ v
        have hv0 : (v 0).freeVariables = ∅ := freeVariables_nrel_arg hc 0
        rw [e]
        refine taut_neg hH ?_
        have e2 : ∼(∼(stageAt ⟨k, a⟩ (v 0))) = stageAt ⟨k, a⟩ (v 0) := by simp
        rw [e2]
        refine taut_stage hH k a (v 0) fun g hg => IH _ ?_ (freeVariables_unfold k g hv0)
        rw [e, rk_neg]
        have := rk_unfold_lt_stageAt A hg (v 0) (v 0)
        simpa using this
      | jlev ℓ =>
        have e : Semiformula.nrel (Sum.inr (IInfRelW.jlev ℓ) : (LIinfW).Rel 2) v =
            ∼(jlevAt ℓ (v 0) (v 1)) := nrel_eq_vec2 _ v
        have hv0 : (v 0).freeVariables = ∅ := freeVariables_nrel_arg hc 0
        have hv1 : (v 1).freeVariables = ∅ := freeVariables_nrel_arg hc 1
        rw [e]
        refine taut_neg hH ?_
        have e2 : ∼(∼(jlevAt ℓ (v 0) (v 1))) = jlevAt ℓ (v 0) (v 1) := by simp
        rw [e2]
        refine taut_jlev hH ℓ hv0 hv1 fun hl => IH _ ?_ (freeVariables_IOmegaAt hv1 _)
        rw [e, rk_neg]
        exact rk_IOmegaAt_lt_jlevAt hl (v 1) (v 0) (v 1)
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

variable {A : Semisentence LForm 2} {ρ : ThetaVNoteD} {H : Set ThetaVNoteD → Set ThetaVNoteD}

/-- `r` is a relation symbol of arithmetic. -/
def IsArithRel {k : ℕ} (r : (LIinfW).Rel k) : Prop := ∃ r' : (ℒₒᵣ : Language).Rel k, r = Sum.inl r'

/-- A formula all of whose atoms are atoms of arithmetic. -/
def ArithF {ξ : Type*} : {m : ℕ} → Semiformula (LIinfW) ξ m → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel r _ => IsArithRel r
  | _, .nrel r _ => IsArithRel r
  | _, .and φ ψ => ArithF φ ∧ ArithF ψ
  | _, .or φ ψ => ArithF φ ∧ ArithF ψ
  | _, .all φ => ArithF φ
  | _, .exs φ => ArithF φ

theorem arithF_rew {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfW) ξ₁ m₁ ξ₂ m₂)
    {φ : Semiformula (LIinfW) ξ₁ m₁} (h : ArithF φ) : ArithF (ω ▹ φ) := by
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

theorem params_of_arithF {ξ : Type*} {m : ℕ} {φ : Semiformula (LIinfW) ξ m} (h : ArithF φ) :
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

theorem trueN_all (φ : Semiproposition (LIinfW) 1) :
    TrueN (∀¹ φ) ↔ ∀ p : ℕ, TrueN (φ/[numI p]) := by
  unfold TrueN
  rw [Semiformula.eval_all]
  refine forall_congr' fun p => ?_
  rw [show φ/[numI p] = φ ⇜ ![numI p] from rfl, Semiformula.eval_substs]
  refine iff_of_eq (congrArg (fun w => Semiformula.Eval (s := stdW) w (fun _ => 0) φ) ?_)
  funext i
  obtain rfl := Subsingleton.elim i 0
  simp only [Matrix.cons_val_zero, Function.comp_apply]
  rw [val_numI]

theorem trueN_exs (φ : Semiproposition (LIinfW) 1) :
    TrueN (∃¹ φ) ↔ ∃ p : ℕ, TrueN (φ/[numI p]) := by
  unfold TrueN
  rw [Semiformula.eval_ex]
  refine exists_congr fun p => ?_
  rw [show φ/[numI p] = φ ⇜ ![numI p] from rfl, Semiformula.eval_substs]
  refine iff_of_eq (congrArg (fun w => Semiformula.Eval (s := stdW) w (fun _ => 0) φ) ?_)
  funext i
  obtain rfl := Subsingleton.elim i 0
  simp only [Matrix.cons_val_zero, Function.comp_apply]
  rw [val_numI]

/-- `ω`, as a notation. -/
abbrev omegaT : ThetaVNoteD := ThetaVNoteD.omegaPow ThetaVNoteD.one

theorem omegaT_mem (hH : ThetaVNoteD.NiceS H) (X : Set ThetaVNoteD) (c : ℕ) :
    ThetaVNoteD.nadd omegaT (ThetaVNoteD.ofNat c) ∈ H X :=
  hH.nadd_mem (hH.omegaPow_mem hH.one_mem) (hH.ofNat_mem c)

theorem ofNat_lt_omegaT_nadd (p c : ℕ) :
    ThetaVNoteD.ofNat p < ThetaVNoteD.nadd omegaT (ThetaVNoteD.ofNat c) :=
  lt_of_lt_of_le (ThetaVNoteD.ofNat_lt_omega p) (ThetaVNoteD.le_nadd_left _ _)

/-- **`ω`-completeness**: a closed arithmetic formula true in `ℕ` is derivable, cut-free, at
height `ω ⊕ c` for every bound `c` on its complexity. -/
theorem omega_complete (hH : ThetaVNoteD.NiceS H) :
    ∀ (c : ℕ) (φ : Proposition (LIinfW)), φ.complexity ≤ c → ArithF φ → φ.freeVariables = ∅ →
      TrueN φ → IDwDerivable A ρ H (ThetaVNoteD.nadd omegaT (ThetaVNoteD.ofNat c)) [φ] := by
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
    have hm : ThetaVNoteD.nadd omegaT (ThetaVNoteD.ofNat (c + 1)) ∈ H ∅ := omegaT_mem hH _ _
    have hlt : ThetaVNoteD.nadd omegaT (ThetaVNoteD.ofNat c) <
        ThetaVNoteD.nadd omegaT (ThetaVNoteD.ofNat (c + 1)) :=
      ThetaVNoteD.nadd_ofNat_lt_nadd_ofNat' _ (Nat.lt_succ_self c)
    have lift : ∀ χ : Proposition (LIinfW), χ.complexity ≤ c → ArithF χ → χ.freeVariables = ∅ →
        TrueN χ → IDwDerivable A ρ H (ThetaVNoteD.nadd omegaT (ThetaVNoteD.ofNat c)) [χ, φ] := by
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
          (lt_of_lt_of_le (by rw [← ThetaVNoteD.ofNat_one]; exact ThetaVNoteD.ofNat_lt_omega 1)
            (ThetaVNoteD.le_nadd_left _ _)) hlt (lift ψ (by omega) hA.2 hf.2 h)
    | hall φ =>
      intro hc hA hf ht hP lift
      rw [Semiformula.complexity_all] at hc
      rw [Semiformula.freeVariables_all] at hf
      refine .all (fun _ => ThetaVNoteD.nadd omegaT (ThetaVNoteD.ofNat c)) hm hP List.mem_cons_self
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

theorem stdW_lMap_eq :
    stdW.lMap embedW = stdJ (fun _ => False) (fun _ : ℕ => (∅ : Set ℕ)) := by
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

theorem eval_killX_stdJ (S : ℕ → Set ℕ) {ξ : Type*} {m : ℕ} (φ : Semiformula (LXJ) ξ m)
    (e : Fin m → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdJ (fun _ => False) S) e f (killX φ) ↔
      Semiformula.Eval (s := stdJ (fun _ => False) S) e f φ := by
  induction φ using Semiformula.rec' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v =>
    rcases r with r | r
    · exact Iff.rfl
    · cases r with
      | X =>
        show Semiformula.Eval (s := stdJ (fun _ => False) S) e f ⊥ ↔ _
        simp only [LogicalConnective.HomClass.map_bot, Prop.bot_eq_false, false_iff]
        exact fun h => h
      | J => exact Iff.rfl
  | hnrel r v =>
    rcases r with r | r
    · exact Iff.rfl
    · cases r with
      | X =>
        show Semiformula.Eval (s := stdJ (fun _ => False) S) e f ⊤ ↔ _
        simp only [LogicalConnective.HomClass.map_top, Prop.top_eq_true, true_iff]
        exact fun h => h
      | J => exact Iff.rfl
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

/-- **The embedding reads `X` and `J` as empty.** -/
theorem eval_embK {ξ : Type*} {m : ℕ} (φ : Semiformula (LXJ) ξ m) (e : Fin m → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdW) e f (embK φ) ↔
      Semiformula.Eval (s := stdJ (fun _ => False) (fun _ : ℕ => (∅ : Set ℕ))) e f φ := by
  rw [embK, embed, Semiformula.eval_lMap, stdW_lMap_eq]
  exact eval_killX_stdJ (fun _ => ∅) φ e f

/-- A sentence true in `stdJ` (with `X` and `J` empty) has a true embedding. -/
theorem trueN_emb_embK {σ : Sentence (LXJ)}
    (h : Semiformula.Eval (s := stdJ (fun _ => False) (fun _ : ℕ => (∅ : Set ℕ)))
      ![] Empty.elim σ) :
    TrueN (Rewriting.emb (embK σ) : Proposition (LIinfW)) := by
  unfold TrueN
  rw [Semiformula.eval_emb]
  exact (eval_embK σ ![] Empty.elim).mpr h

end Semantics

/-! ### The universal closure, by the ω-rule -/

section Closure

open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting

variable {A : Semisentence LForm 2} {ρ : ThetaVNoteD} {H : Set ThetaVNoteD → Set ThetaVNoteD}

/-- Composing a lifted `k`-ary substitution with a one-point substitution. -/
theorem subst_q_subst {k : ℕ} (σ : Semiformula (LIinfW) ℕ (k + 1))
    (v : Fin k → SyntacticTerm (LIinfW)) (t : SyntacticTerm (LIinfW)) :
    ((Rew.subst v).q ▹ σ)/[t] = σ ⇜ (t :> v) := by
  have hrew : (Rew.subst ![t]).comp ((Rew.subst v).q) = Rew.subst (t :> v) := by
    rw [Rew.q_subst, Rew.subst_comp_subst]
    congr 1
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  simpa [← comp_app] using smul_ext' (φ := σ) hrew

theorem allClosure_aux (hH : ThetaVNoteD.IsOperator H) (β : ThetaVNoteD)
    (hβ : ∀ j : ℕ, ThetaVNoteD.nadd β (ThetaVNoteD.ofNat j) ∈ H ∅) :
    ∀ (k j : ℕ) (σ : Semiformula (LIinfW) ℕ k), Stage.val '' params σ ⊆ H ∅ →
      (∀ w : Fin k → ℕ, IDwDerivable A ρ H (ThetaVNoteD.nadd β (ThetaVNoteD.ofNat j))
        [σ ⇜ fun i => numI (w i)]) →
      IDwDerivable A ρ H (ThetaVNoteD.nadd β (ThetaVNoteD.ofNat (j + k))) [∀¹* σ] := by
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
    refine .all (fun _ => ThetaVNoteD.nadd β (ThetaVNoteD.ofNat j)) (hβ _) hPs List.mem_cons_self
      (fun _ => ThetaVNoteD.nadd_ofNat_lt_nadd_ofNat' _ (Nat.lt_succ_self j)) (fun p => ?_)
    rw [subst_q_subst]
    have hv : ((numI p : SyntacticTerm (LIinfW)) :> fun i => numI (w i)) =
        fun i => numI (((p :> w) : Fin (k + 1) → ℕ) i) := by
      funext i
      induction i using Fin.cases with
      | zero => simp
      | succ j => simp
    rw [hv]
    refine (h (p :> w)).weaken_seq hH (List.cons_subset_cons _ (List.nil_subset _)) ?_
    simp only [paramsVal_cons, paramsVal_nil, Set.union_empty, params_all, params_rew]
    exact Set.union_subset hP hP

theorem allClosure_derivable (hH : ThetaVNoteD.IsOperator H) {k : ℕ}
    (σ : Semiformula (LIinfW) ℕ k) {β : ThetaVNoteD}
    (hβ : ∀ j : ℕ, ThetaVNoteD.nadd β (ThetaVNoteD.ofNat j) ∈ H ∅)
    (hP : Stage.val '' params σ ⊆ H ∅)
    (h : ∀ w : Fin k → ℕ, IDwDerivable A ρ H β [σ ⇜ fun i => numI (w i)]) :
    IDwDerivable A ρ H (ThetaVNoteD.nadd β (ThetaVNoteD.ofNat k)) [∀¹* σ] := by
  have key := allClosure_aux (A := A) (ρ := ρ) hH β hβ k 0 σ hP (fun w => by
    rw [ThetaVNoteD.ofNat_zero, ThetaVNoteD.nadd_zero]; exact h w)
  rwa [Nat.zero_add] at key

end Closure

/-! ### The axioms of equality and of `𝗣𝗔⁻` -/

section EqPA

variable {A : Semisentence LForm 2} {H : Set ThetaVNoteD → Set ThetaVNoteD}

/-- `Ω_ω · 2 = Ω_ω ⊕ Ω_ω`, the top level (matches `IDw.AxiomsPA`'s local copy of the same
quantity). -/
abbrev OmegaTwo_al : ThetaVNoteD :=
  ThetaVNoteD.nadd ThetaVNoteD.OmegaW ThetaVNoteD.OmegaW

/-- **The axiom `σ` is derivable** in the form of Freund, proof of Theorem 6.5: cut-free, at
a height `Ω_ω · 2 + m` independent of the nice operator. -/
def AxDerivable_al (A : Semisentence LForm 2) (σ : Sentence (LXJ)) : Prop :=
  ∃ m : ℕ, ∀ H : Set ThetaVNoteD → Set ThetaVNoteD, ThetaVNoteD.NiceS H →
    IDwDerivable A ThetaVNoteD.zero H (ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat m))
      [(Rewriting.emb (embK σ) : Proposition (LIinfW))]

theorem OmegaTwo_mem_al (hH : ThetaVNoteD.NiceS H) (X : Set ThetaVNoteD) (m : ℕ) :
    ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat m) ∈ H X :=
  hH.nadd_mem (hH.nadd_mem hH.OmegaW_mem hH.OmegaW_mem) (hH.ofNat_mem m)

theorem axDerivable_of_le_al {σ : Sentence (LXJ)} (m : ℕ) (h : ThetaVNoteD)
    (hle : h ≤ ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat m))
    (d : ∀ H : Set ThetaVNoteD → Set ThetaVNoteD, ThetaVNoteD.NiceS H →
      IDwDerivable A ThetaVNoteD.zero H h [(Rewriting.emb (embK σ) : Proposition (LIinfW))]) :
    AxDerivable_al A σ :=
  ⟨m, fun H hH => (d H hH).mono_height hle (OmegaTwo_mem_al hH _ m)⟩

theorem Omega_le_OmegaTwo_nadd (m : ℕ) :
    ThetaVNoteD.OmegaW ≤ ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat m) :=
  le_trans (ThetaVNoteD.le_nadd_left _ _) (ThetaVNoteD.le_nadd_left _ _)

theorem omegaT_lt_Omega (c : ℕ) :
    ThetaVNoteD.nadd omegaT (ThetaVNoteD.ofNat c) < ThetaVNoteD.OmegaW :=
  ThetaVNoteD.nadd_lt_prin ThetaVTerm.isPrin_OmegaW
    (ThetaVNoteD.omegaPow_lt_prin ThetaVTerm.isPrin_OmegaW
      (ThetaVNoteD.one_lt_prin ThetaVTerm.isPrin_OmegaW))
    (ThetaVNoteD.ofNat_lt_prin ThetaVTerm.isPrin_OmegaW c)

/-- A formula of `LXJ` without the level predicate `J`. -/
def IFreeL {ξ : Type*} : {m : ℕ} → Semiformula (LXJ) ξ m → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel (Sum.inl _) _ => True
  | _, .rel (Sum.inr XJRel.X) _ => True
  | _, .rel (Sum.inr XJRel.J) _ => False
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr XJRel.X) _ => True
  | _, .nrel (Sum.inr XJRel.J) _ => False
  | _, .and φ ψ => IFreeL φ ∧ IFreeL ψ
  | _, .or φ ψ => IFreeL φ ∧ IFreeL ψ
  | _, .all φ => IFreeL φ
  | _, .exs φ => IFreeL φ

/-- Without `J`, the embedding is arithmetic (`X` is read as empty). -/
theorem arithF_embK {ξ : Type*} {m : ℕ} :
    ∀ (φ : Semiformula (LXJ) ξ m), IFreeL φ → ArithF (embK φ)
  | .verum, _ => by show ArithF (embK (⊤ : Semiformula (LXJ) ξ m)); rw [embK_verum]; trivial
  | .falsum, _ => by show ArithF (embK (⊥ : Semiformula (LXJ) ξ m)); rw [embK_falsum]; trivial
  | .rel (Sum.inl r) _, _ => ⟨r, rfl⟩
  | .rel (Sum.inr XJRel.X) _, _ => by
    show ArithF (embK (⊥ : Semiformula (LXJ) ξ m)); rw [embK_falsum]; trivial
  | .rel (Sum.inr XJRel.J) _, h => h.elim
  | .nrel (Sum.inl r) _, _ => ⟨r, rfl⟩
  | .nrel (Sum.inr XJRel.X) _, _ => by
    show ArithF (embK (⊤ : Semiformula (LXJ) ξ m)); rw [embK_verum]; trivial
  | .nrel (Sum.inr XJRel.J) _, h => h.elim
  | .and φ ψ, h => by
    show ArithF (embK (φ ⋏ ψ)); rw [embK_and]; exact ⟨arithF_embK φ h.1, arithF_embK ψ h.2⟩
  | .or φ ψ, h => by
    show ArithF (embK (φ ⋎ ψ)); rw [embK_or]; exact ⟨arithF_embK φ h.1, arithF_embK ψ h.2⟩
  | .all φ, h => by
    show ArithF (embK (∀¹ φ)); rw [embK_all]; exact arithF_embK φ h
  | .exs φ, h => by
    show ArithF (embK (∃¹ φ)); rw [embK_exs]; exact arithF_embK φ h

@[simp] theorem iFreeL_neg {ξ : Type*} {m : ℕ} (φ : Semiformula (LXJ) ξ m) :
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

theorem iFreeL_imp {ξ : Type*} {m : ℕ} (φ ψ : Semiformula (LXJ) ξ m) :
    IFreeL (φ 🡒 ψ) ↔ IFreeL φ ∧ IFreeL ψ := by
  have h : (φ 🡒 ψ) = ∼φ ⋎ ψ := rfl
  rw [h]
  exact and_congr (iFreeL_neg φ) Iff.rfl

theorem iFreeL_allClosure {ξ : Type*} :
    ∀ {m : ℕ} (φ : Semiformula (LXJ) ξ m), IFreeL φ → IFreeL (∀¹* φ)
  | 0, _, h => h
  | _ + 1, φ, h => iFreeL_allClosure (∀¹ φ) h

theorem iFreeL_conj {ξ : Type*} {m : ℕ} :
    ∀ {k : ℕ} (v : Fin k → Semiformula (LXJ) ξ m), (∀ i, IFreeL (v i)) → IFreeL (Matrix.conj v)
  | 0, _, _ => trivial
  | _ + 1, v, h => ⟨h 0, iFreeL_conj (Matrix.vecTail v) fun i => h i.succ⟩

theorem iFreeL_eqOp {ξ : Type*} {m : ℕ} (t u : Semiterm (LXJ) ξ m) :
    IFreeL ((Semiformula.Operator.Eq.eq : Semiformula.Operator (LXJ) 2).operator ![t, u]) := by
  rw [Semiformula.Operator.eq_def]
  trivial

theorem iFreeL_eqRefl : IFreeL (Theory.Eq.refl (LXJ)) :=
  iFreeL_eqOp (ξ := Empty) (#0 : Semiterm (LXJ) Empty 1) #0

theorem iFreeL_eqSymm : IFreeL (Theory.Eq.symm (LXJ)) :=
  (iFreeL_imp _ _).mpr ⟨iFreeL_eqOp _ _, iFreeL_eqOp _ _⟩

theorem iFreeL_eqTrans : IFreeL (Theory.Eq.trans (LXJ)) :=
  (iFreeL_imp _ _).mpr ⟨iFreeL_eqOp _ _, (iFreeL_imp _ _).mpr ⟨iFreeL_eqOp _ _, iFreeL_eqOp _ _⟩⟩

theorem iFreeL_funcExt {k : ℕ} (f : (LXJ).Func k) : IFreeL (Theory.Eq.funcExt f) :=
  iFreeL_allClosure _ ((iFreeL_imp _ _).mpr
    ⟨iFreeL_conj _ (fun _ => iFreeL_eqOp _ _), iFreeL_eqOp _ _⟩)

theorem iFreeL_relExt_inl {k : ℕ} (r : (ℒₒᵣ : Language).Rel k) :
    IFreeL (Theory.Eq.relExt (Sum.inl r : (LXJ).Rel k)) :=
  iFreeL_allClosure _ ((iFreeL_imp _ _).mpr
    ⟨iFreeL_conj _ (fun _ => iFreeL_eqOp _ _), (iFreeL_imp _ _).mpr ⟨trivial, trivial⟩⟩)

theorem iFreeL_relExt_X : IFreeL (Theory.Eq.relExt (Sum.inr XJRel.X : (LXJ).Rel 1)) :=
  iFreeL_allClosure _ ((iFreeL_imp _ _).mpr
    ⟨iFreeL_conj _ (fun _ => iFreeL_eqOp _ _), (iFreeL_imp _ _).mpr ⟨trivial, trivial⟩⟩)

theorem iFreeL_lMap_toLXJ {ξ : Type*} {m : ℕ} (φ : Semiformula ℒₒᵣ ξ m) :
    IFreeL (Semiformula.lMap toLXJ φ) := by
  induction φ using Semiformula.rec' with
  | hverum => simp only [LogicalConnective.HomClass.map_top]; trivial
  | hfalsum => simp only [LogicalConnective.HomClass.map_bot]; trivial
  | hrel r v => trivial
  | hnrel r v => trivial
  | hand φ ψ ihφ ihψ => rw [LogicalConnective.HomClass.map_and]; exact ⟨ihφ, ihψ⟩
  | hor φ ψ ihφ ihψ => rw [LogicalConnective.HomClass.map_or]; exact ⟨ihφ, ihψ⟩
  | hall φ ih => rw [Semiformula.lMap_all]; exact ih
  | hexs φ ih => rw [Semiformula.lMap_exs]; exact ih

/-- **A `J`-free sentence true in `ℕ`** (with `X` and `J` read as empty) is an axiom derivable
at height `ω ⊕ c`. -/
theorem axDerivable_of_iFree {σ : Sentence (LXJ)} (hI : IFreeL σ)
    (ht : Semiformula.Eval (s := stdJ (fun _ => False) (fun _ : ℕ => (∅ : Set ℕ))) ![]
      Empty.elim σ) :
    AxDerivable_al A σ := by
  refine axDerivable_of_le_al 0 (ThetaVNoteD.nadd omegaT
    (ThetaVNoteD.ofNat (Rewriting.emb (embK σ) : Proposition (LIinfW)).complexity))
    (le_of_lt (lt_of_lt_of_le (omegaT_lt_Omega _) (Omega_le_OmegaTwo_nadd 0))) (fun H hH => ?_)
  exact omega_complete hH _ _ le_rfl (arithF_rew _ (arithF_embK σ hI))
    (Semiformula.freeVariables_emb _) (trueN_emb_embK ht)

/-- **The axioms of `𝗣𝗔⁻`** (Freund, proof of Theorem 6.5, after Theorem 3.7 of the first
lecture). -/
theorem paMinus_axiom {σ : Sentence (LXJ)}
    (h : σ ∈ Theory.lMap toLXJ 𝗣𝗔⁻) : AxDerivable_al A σ := by
  obtain ⟨τ, hτ, rfl⟩ := h
  exact axDerivable_of_iFree (iFreeL_lMap_toLXJ τ)
    (eval_of_paMinus (fun _ => False) (fun _ : ℕ => (∅ : Set ℕ)) ⟨τ, hτ, rfl⟩)

/-! #### The equality axiom for `J` -/

section RelExtJ

/-- `t = u` in `LXJ`. -/
def eqX {ξ : Type*} {m : ℕ} (t u : Semiterm (LXJ) ξ m) : Semiformula (LXJ) ξ m :=
  Semiformula.rel (Language.Eq.eq : (LXJ).Rel 2) ![t, u]

/-- `t = u` in `LIinfW`. -/
def eqI {ξ : Type*} {m : ℕ} (t u : Semiterm (LIinfW) ξ m) : Semiformula (LIinfW) ξ m :=
  Semiformula.rel (Language.Eq.eq : (LIinfW).Rel 2) ![t, u]

/-- The matrix of the equality axiom for `J`: `x₀ = y₀ ∧ x₁ = y₁ → J x₀ x₁ → J y₀ y₁`. -/
def relJ4S : Semisentence (LXJ) 4 :=
  ∼(eqX (#0 : Semiterm (LXJ) Empty 4) #2 ⋏ (eqX (#1 : Semiterm (LXJ) Empty 4) #3 ⋏ ⊤)) ⋎
    (∼(Jat (#0 : Semiterm (LXJ) Empty 4) #1) ⋎ Jat (#2 : Semiterm (LXJ) Empty 4) #3)

theorem relExtJ_eq :
    (Theory.Eq.relExt (Sum.inr XJRel.J : (LXJ).Rel 2) : Sentence (LXJ)) = ∀¹* relJ4S := by
  have hv0 : (fun i : Fin 2 ↦ (#(i.addCast 2) : Semiterm (LXJ) Empty 4))
      = ![(#0 : Semiterm (LXJ) Empty 4), #1] := funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)
  have hv1 : (fun i : Fin 2 ↦ (#(i.addNat 2) : Semiterm (LXJ) Empty 4))
      = ![(#2 : Semiterm (LXJ) Empty 4), #3] := funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)
  show (∀¹* ((Matrix.conj fun i : Fin 2 ↦
      (eqX (#(i.addCast 2) : Semiterm (LXJ) Empty 4) (#(i.addNat 2)))) 🡒
      (Semiformula.rel (Sum.inr XJRel.J : (LXJ).Rel 2)
          (fun i : Fin 2 ↦ (#(i.addCast 2) : Semiterm (LXJ) Empty 4)) 🡒
        Semiformula.rel (Sum.inr XJRel.J : (LXJ).Rel 2)
          (fun i : Fin 2 ↦ (#(i.addNat 2) : Semiterm (LXJ) Empty 4)))) : Sentence (LXJ))
      = ∀¹* relJ4S
  rw [hv0, hv1]
  rfl

/-- `embK (t = u)` is the equality of the embedded terms. -/
theorem embK_eqX {ξ : Type*} {m : ℕ} (t u : Semiterm (LXJ) ξ m) :
    embK (eqX t u) = eqI (Semiterm.lMap embedW t) (Semiterm.lMap embedW u) :=
  congrArg (Semiformula.rel (Language.Eq.eq : (LIinfW).Rel 2))
    (funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩))

@[simp] theorem rew_eqI {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfW) ξ₁ m₁ ξ₂ m₂)
    (t u : Semiterm (LIinfW) ξ₁ m₁) : ω ▹ (eqI t u) = eqI (ω t) (ω u) := Semiformula.rew_rel2 ω

@[simp] theorem rew_njlevAt_al {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfW) ξ₁ m₁ ξ₂ m₂)
    (ℓ : WithTop ℕ) (s t : Semiterm (LIinfW) ξ₁ m₁) :
    ω ▹ (njlevAt ℓ s t) = njlevAt ℓ (ω s) (ω t) :=
  Semiformula.rew_nrel2 ω

@[simp] theorem rew_jlevAt_al {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfW) ξ₁ m₁ ξ₂ m₂)
    (ℓ : WithTop ℕ) (s t : Semiterm (LIinfW) ξ₁ m₁) :
    ω ▹ (jlevAt ℓ s t) = jlevAt ℓ (ω s) (ω t) :=
  Semiformula.rew_rel2 ω

/-- The matrix of the equality axiom for `J`, embedded. -/
def relJ4 : Semiformula (LIinfW) ℕ 4 :=
  ∼(eqI (#0 : Semiterm (LIinfW) ℕ 4) #2 ⋏ (eqI (#1 : Semiterm (LIinfW) ℕ 4) #3 ⋏ ⊤)) ⋎
    (∼(jlevAt ⊤ (#0 : Semiterm (LIinfW) ℕ 4) #1) ⋎ jlevAt ⊤ (#2 : Semiterm (LIinfW) ℕ 4) #3)

/-- The matrix at the numerals. -/
def relJ0 (a₀ a₁ b₀ b₁ : ℕ) : Proposition (LIinfW) :=
  ∼(eqI (numI a₀) (numI b₀) ⋏ (eqI (numI a₁) (numI b₁) ⋏ ⊤)) ⋎
    (∼(jlevAt ⊤ (numI a₀) (numI a₁)) ⋎ jlevAt ⊤ (numI b₀) (numI b₁))

theorem emb_embK_relJ4S :
    (Rewriting.emb (embK relJ4S) : Semiformula (LIinfW) ℕ 4) = relJ4 := by
  simp only [relJ4S, embK_or, embK_and, embK_neg, embK_verum, embK_eqX, embK_Jat, relJ4,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_top, rew_eqI,
    rew_jlevAt_al, Semiterm.lMap_bvar, Rew.emb_bvar]

theorem emb_allClosure_al : ∀ {n : ℕ} (φ : Semiformula (LIinfW) Empty n),
    (Rewriting.emb (∀¹* φ) : Proposition (LIinfW)) =
      ∀¹* (Rewriting.emb φ : Semiformula (LIinfW) ℕ n)
  | 0, φ => rfl
  | n + 1, φ => by
    rw [allClosure_succ, allClosure_succ, emb_allClosure_al (∀¹ φ)]
    simp only [Rewriting.app_all, Rew.q_emb]

theorem emb_embK_relExtJ :
    (Rewriting.emb (embK (Theory.Eq.relExt (Sum.inr XJRel.J : (LXJ).Rel 2))) :
        Proposition (LIinfW)) = ∀¹* relJ4 := by
  rw [relExtJ_eq, embK_allClosure, emb_allClosure_al, emb_embK_relJ4S]

theorem relJ4_inst (w : Fin 4 → ℕ) :
    (relJ4 ⇜ fun i => numI (w i)) = relJ0 (w 0) (w 1) (w 2) (w 3) := by
  simp [relJ4, relJ0]

theorem trueLit_neqI {a b : ℕ} (h : a ≠ b) :
    TrueLit (∼(eqI (numI a) (numI b) : Proposition (LIinfW))) := by
  have hl : IsArithLit (eqI (numI a) (numI b)) :=
    ⟨2, Language.Eq.eq, ![numI a, numI b], Or.inl rfl, fun i => by
      match i with
      | ⟨0, h⟩ =>
        have h0 : (![numI a, numI b] : Fin 2 → SyntacticTerm (LIinfW)) ⟨0, h⟩ = numI a := rfl
        rw [h0]; exact numI_freeVariables a
      | ⟨1, h⟩ =>
        have h1 : (![numI a, numI b] : Fin 2 → SyntacticTerm (LIinfW)) ⟨1, h⟩ = numI b := rfl
        rw [h1]; exact numI_freeVariables b⟩
  refine ⟨hl.neg, (trueN_neg _).mpr ?_⟩
  unfold TrueN eqI
  rw [Semiformula.eval_rel]
  show ¬ (Semiterm.val (s := stdW) ![] (fun _ => 0) (numI a) =
    Semiterm.val (s := stdW) ![] (fun _ => 0) (numI b))
  rw [val_numI, val_numI]
  exact h

theorem freeVariables_jlevAt_numI (a b : ℕ) :
    (jlevAt ⊤ (numI a) (numI b) : Proposition (LIinfW)).freeVariables = ∅ := by
  ext x
  simp [jlevAt, Semiformula.freeVariables, numI_freeVariables]

@[simp] theorem params_eqI {ξ : Type*} {m : ℕ} (t u : Semiterm (LIinfW) ξ m) :
    params (eqI t u) = ∅ := rfl

theorem params_relJ0 (a₀ a₁ b₀ b₁ : ℕ) : params (relJ0 a₀ a₁ b₀ b₁) = ∅ := by
  simp [relJ0]

theorem paramsVal_eq_empty {Γ : Sequent (LIinfW)} (h : ∀ φ ∈ Γ, params φ = ∅) :
    paramsVal Γ = ∅ := by
  induction Γ with
  | nil => simp
  | cons φ Γ ih =>
    rw [paramsVal_cons, h φ List.mem_cons_self, ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)]
    simp

/-- **The instance of the equality axiom for `J` at `a₀ a₁ b₀ b₁`**: an unequal pair of arguments
is a true literal, and for equal ones Lemma 6.1 applies (Freund, proof of Theorem 6.5). -/
theorem relJ0_derivable
    (hH : ThetaVNoteD.NiceS H) (a₀ a₁ b₀ b₁ : ℕ) :
    IDwDerivable A ThetaVNoteD.zero H (ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat 3))
      [relJ0 a₀ a₁ b₀ b₁] := by
  have hΩ : ThetaVNoteD.OmegaW ∈ H ∅ := hH.OmegaW_mem
  have hm : ∀ j, ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat j) ∈ H ∅ :=
    fun j => hH.nadd_mem hΩ (hH.ofNat_mem j)
  have hlt : ∀ i j : ℕ, i < j → ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat i) <
      ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat j) :=
    fun i j h => ThetaVNoteD.nadd_ofNat_lt_nadd_ofNat' _ h
  have hone : ∀ j, ThetaVNoteD.one < ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat j) :=
    fun j => lt_of_lt_of_le (ThetaVNoteD.one_lt_prin ThetaVTerm.isPrin_OmegaW)
      (ThetaVNoteD.le_nadd_left _ _)
  have h0 : ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat 0) = ThetaVNoteD.OmegaW := by
    rw [ThetaVNoteD.ofNat_zero, ThetaVNoteD.nadd_zero]
  have hlt0 : ThetaVNoteD.OmegaW <
      ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat 1) := by
    have := hlt 0 1 (by omega); rwa [h0] at this
  have pM : params (relJ0 a₀ a₁ b₀ b₁) = ∅ := params_relJ0 _ _ _ _
  by_cases hab : a₀ = b₀ ∧ a₁ = b₁
  · obtain ⟨rfl, rfl⟩ := hab
    have d0 := taut (A := A) hH (jlevAt ⊤ (numI a₀) (numI a₁)) (freeVariables_jlevAt_numI a₀ a₁)
    rw [params_jlevAt, Set.image_empty, rk_jlevAt_top,
      ThetaVNoteD.omegaMul_prin ThetaVTerm.isPrin_OmegaW,
      ThetaVNoteD.adjoin_eq_self hH.isOperator (Set.empty_subset _)] at d0
    set P : Proposition (LIinfW) := ∼(jlevAt ⊤ (numI a₀) (numI a₁)) with hP
    set Q : Proposition (LIinfW) := jlevAt ⊤ (numI a₀) (numI a₁) with hQ
    set N : Proposition (LIinfW) :=
      ∼(eqI (numI a₀) (numI a₀) ⋏ (eqI (numI a₁) (numI a₁) ⋏ ⊤)) with hN
    have eM : relJ0 a₀ a₁ a₀ a₁ = N ⋎ (P ⋎ Q) := rfl
    have pQ : params Q = ∅ := by rw [hQ]; simp
    have pP : params P = ∅ := by rw [hP, params_neg]; exact pQ
    have pN : params N = ∅ := by rw [hN]; simp
    have d1 : IDwDerivable A ThetaVNoteD.zero H ThetaVNoteD.OmegaW
        [Q, P, P ⋎ Q, relJ0 a₀ a₁ a₀ a₁] :=
      d0.weaken_seq hH.isOperator
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto)
        (by simp only [paramsVal_cons, paramsVal_nil, params_or, pQ, pP, pM, Set.image_empty,
              Set.union_empty]; exact Set.empty_subset _)
    have d2 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat 1))
        [P, P ⋎ Q, relJ0 a₀ a₁ a₀ a₁] :=
      .orR (hm 1)
        (by simp only [paramsVal_cons, paramsVal_nil, params_or, pQ, pP, pM, Set.image_empty,
              Set.union_empty]; exact Set.empty_subset _)
        (List.mem_cons_of_mem _ List.mem_cons_self) (hone 1) hlt0 d1
    have d3 : IDwDerivable A ThetaVNoteD.zero H
        (ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat 2))
        [P ⋎ Q, relJ0 a₀ a₁ a₀ a₁] :=
      .orL (hm 2)
        (by simp only [paramsVal_cons, paramsVal_nil, params_or, pQ, pP, pM, Set.image_empty,
              Set.union_empty]; exact Set.empty_subset _)
        List.mem_cons_self (hlt 1 2 (by omega)) d2
    exact .orR (hm 3)
      (by simp only [paramsVal_cons, paramsVal_nil, pM, Set.image_empty, Set.union_empty]
          exact Set.empty_subset _)
      (by rw [eM]; exact List.mem_cons_self) (hone 3) (hlt 2 3 (by omega)) d3
  · set N : Proposition (LIinfW) :=
      ∼(eqI (numI a₀) (numI b₀) ⋏ (eqI (numI a₁) (numI b₁) ⋏ ⊤)) with hN
    have eM : relJ0 a₀ a₁ b₀ b₁ =
        N ⋎ (∼(jlevAt ⊤ (numI a₀) (numI a₁)) ⋎ jlevAt ⊤ (numI b₀) (numI b₁)) := rfl
    have pN : params N = ∅ := by rw [hN]; simp
    by_cases h0' : a₀ = b₀
    · have h1' : a₁ ≠ b₁ := fun h => hab ⟨h0', h⟩
      have eN : N = ∼(eqI (numI a₀) (numI b₀)) ⋎ (∼(eqI (numI a₁) (numI b₁)) ⋎ ⊥) := by
        rw [hN]; simp
      have pM' : params (∼(eqI (numI a₁) (numI b₁)) ⋎ (⊥ : Proposition (LIinfW))) = ∅ := by simp
      have pE : params (∼(eqI (numI a₁) (numI b₁)) : Proposition (LIinfW)) = ∅ := by simp
      have e1 : IDwDerivable A ThetaVNoteD.zero H ThetaVNoteD.OmegaW
          [∼(eqI (numI a₁) (numI b₁)), ∼(eqI (numI a₁) (numI b₁)) ⋎ ⊥, N,
            relJ0 a₀ a₁ b₀ b₁] :=
        .literal hΩ
          (by simp only [paramsVal_cons, paramsVal_nil, pE, pM', pN, pM, Set.image_empty,
                Set.union_empty]; exact Set.empty_subset _)
          (trueLit_neqI h1') List.mem_cons_self
      have e2 : IDwDerivable A ThetaVNoteD.zero H
          (ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat 1))
          [∼(eqI (numI a₁) (numI b₁)) ⋎ ⊥, N, relJ0 a₀ a₁ b₀ b₁] :=
        .orL (hm 1)
          (by simp only [paramsVal_cons, paramsVal_nil, pM', pN, pM, Set.image_empty,
                Set.union_empty]; exact Set.empty_subset _)
          List.mem_cons_self hlt0 e1
      have e3 : IDwDerivable A ThetaVNoteD.zero H
          (ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat 2))
          [N, relJ0 a₀ a₁ b₀ b₁] :=
        .orR (hm 2)
          (by simp only [paramsVal_cons, paramsVal_nil, pN, pM, Set.image_empty,
                Set.union_empty]; exact Set.empty_subset _)
          (by rw [← eN]; exact List.mem_cons_self) (hone 2) (hlt 1 2 (by omega)) e2
      exact .orL (hm 3)
        (by simp only [paramsVal_cons, paramsVal_nil, pM, Set.image_empty, Set.union_empty]
            exact Set.empty_subset _)
        (by rw [eM]; exact List.mem_cons_self) (hlt 2 3 (by omega)) e3
    · have eN : N = ∼(eqI (numI a₀) (numI b₀)) ⋎ (∼(eqI (numI a₁) (numI b₁)) ⋎ ⊥) := by
        rw [hN]; simp
      have pE : params (∼(eqI (numI a₀) (numI b₀)) : Proposition (LIinfW)) = ∅ := by simp
      have e1 : IDwDerivable A ThetaVNoteD.zero H ThetaVNoteD.OmegaW
          [∼(eqI (numI a₀) (numI b₀)), N, relJ0 a₀ a₁ b₀ b₁] :=
        .literal hΩ
          (by simp only [paramsVal_cons, paramsVal_nil, pE, pN, pM, Set.image_empty,
                Set.union_empty]; exact Set.empty_subset _)
          (trueLit_neqI h0') List.mem_cons_self
      have e2 : IDwDerivable A ThetaVNoteD.zero H
          (ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat 1))
          [N, relJ0 a₀ a₁ b₀ b₁] :=
        .orL (hm 1)
          (by simp only [paramsVal_cons, paramsVal_nil, pN, pM, Set.image_empty,
                Set.union_empty]; exact Set.empty_subset _)
          (by rw [← eN]; exact List.mem_cons_self) hlt0 e1
      have e3 : IDwDerivable A ThetaVNoteD.zero H
          (ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat 2))
          [relJ0 a₀ a₁ b₀ b₁] :=
        .orL (hm 2)
          (by simp only [paramsVal_cons, paramsVal_nil, pM, Set.image_empty, Set.union_empty]
              exact Set.empty_subset _)
          (by rw [eM]; exact List.mem_cons_self) (hlt 1 2 (by omega)) e2
      exact e3.mono_height (le_of_lt (hlt 2 3 (by omega))) (hm 3)

/-- **The equality axiom for `J`** (Freund, proof of Theorem 6.5). -/
theorem relExtJ_axiom :
    AxDerivable_al A (Theory.Eq.relExt (Sum.inr XJRel.J : (LXJ).Rel 2)) := by
  refine axDerivable_of_le_al 7 (ThetaVNoteD.nadd
    (ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat 3)) (ThetaVNoteD.ofNat 4))
    ?_ (fun H hH => ?_)
  · rw [ThetaVNoteD.nadd_assoc, ThetaVNoteD.ofNat_nadd_ofNat]
    have key : ThetaVNoteD.nadd ThetaVNoteD.OmegaW (ThetaVNoteD.ofNat 7) ≤
        ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat 7) := by
      rw [ThetaVNoteD.nadd_comm ThetaVNoteD.OmegaW, ThetaVNoteD.nadd_comm OmegaTwo_al]
      exact ThetaVNoteD.nadd_le_nadd_right _ (ThetaVNoteD.le_nadd_left _ _)
    exact key
  · rw [emb_embK_relExtJ]
    refine allClosure_derivable hH.isOperator relJ4
      (fun j => hH.nadd_mem (hH.nadd_mem hH.OmegaW_mem (hH.ofNat_mem 3)) (hH.ofNat_mem j))
      (by
        intro x hx
        obtain ⟨s, hs, rfl⟩ := hx
        simp [relJ4] at hs)
      (fun w => ?_)
    rw [relJ4_inst]
    exact relJ0_derivable hH _ _ _ _

end RelExtJ

/-- **The equality axioms** (Freund, proof of Theorem 6.5). -/
theorem eq_axiom {σ : Sentence (LXJ)}
    (h : σ ∈ 𝗘𝗤 (LXJ)) : AxDerivable_al A σ := by
  have ht := eval_of_eqAxiom (fun _ => False) (fun _ : ℕ => (∅ : Set ℕ)) h
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
      | J => exact relExtJ_axiom

end EqPA

end IDw

end OrdinalAnalysis
