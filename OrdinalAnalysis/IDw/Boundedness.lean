/- Source: OrdinalAnalysis\IDn\Boundedness.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.Calculus
/-
  Boundedness in the multi-level operator-controlled calculus `ID_{<ω}^∞`, at every level.

  Sources: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Theorem 5.9 and Exercise 6.6 (one level, ported as
  `ID1/Boundedness.lean`); W. Buchholz, *A simplified version of local predicativity* (1992),
  Lemma 3.17 (Boundedness, any regular `κ`) and Lemma 3.9 c); W. Pohlers, *Subsystems of set
  theory and second order number theory* (Handbook of Proof Theory, 1998), Theorem 3.4.3.7
  (Boundedness Theorem, any regular `κ`).

  **Theorem (boundedness at level `k`).**  `H ⊢^α_ρ Γ, ψ` gives `H ⊢^α_ρ Γ, ψ^{(k,b)}` for every
  `b ∈ H(∅)` with `α ⪯ b ≺ Ω_{k+1}`, where `ψ^{(k,b)} = capAt k b ψ` replaces every literal
  `I_k t = I_k^{≺Ω_{k+1}} t`, `¬I_k t` by `I_k^{≺b} t`, `¬I_k^{≺b} t` and leaves every other
  literal (other levels, and level `k` below the top) untouched.  No hypothesis on `ψ`, `Γ` or
  the operator family `A` is needed: the operator forms `A_j` of *higher* levels `j > k` may
  mention `I_k` (as `LevelBounded j (A j)` allows).

  **Why the higher levels do no harm.**  The one-level proof closes the (W)/(V) cases of a
  principal stage literal with the premise *bounded* and then uses
  `cap (A(t, I^{≺γ})) = A(t, I^{≺γ})` (`γ ≺ Ω`).  With several levels that identity fails for
  the unfolding of a level `j > k` whose form mentions `I_k`
  (see the closing remark of this file), and a mechanical port gets stuck there.  But the generalised claim (`bound_aux`, as in `ID1`) bounds only a chosen list `Θ` of
  formulas and leaves the rest `Γ` alone, and the minor formula `A_j(t, I_j^{≺γ})` of a stage
  literal can simply be put into the *unbounded* part: that premise is exactly the premise the
  rule needs, whatever level the literal has and whether or not the literal itself was bounded.
  This is the shape of the print: Buchholz (proof of 3.17) and Pohlers (proof of 3.4.3.7) bound
  only the distinguished formula and apply the induction hypothesis with the rest of the
  sequent untouched.  Only the conjunctive/disjunctive connectives and quantifiers, whose minor
  formulas are subformulas of a bounded formula, use the bounded premise.

  Clause (Fix_j) at level `j = k` cannot occur below `Ω_{k+1}`; at `j ≠ k` its principal
  literal `I_j t` is untouched by bounding at level `k`.

  **Exercise 6.6 at level `k`.**  `H ⊢^α_ρ Γ, ¬I_k t` gives `H ⊢^α_ρ Γ, ¬I_k^{≺δ} t` for every
  `δ ⪯ Ω_{k+1}` with `δ ∈ H(∅)`: restrict the premises of (V).

  Both results need of the operator only that it is an operator (monotone).
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder


/-! ### Bounding of single literals -/

section CapLit

variable (k : ℕ) (b : StageAt k) {ξ : Type*} {m : ℕ}

theorem capAt_XinfAt (t : Semiterm (LIinfW) ξ m) : capAt k b (XinfAt t) = XinfAt t := rfl

theorem capAt_neg_XinfAt (t : Semiterm (LIinfW) ξ m) :
    capAt k b (∼(XinfAt t)) = ∼(XinfAt t) := rfl

/-- `(¬I_k t)^β = ¬I_k^{≺β} t`. -/
theorem capAt_nstageAt_top (t : Semiterm (LIinfW) ξ m) :
    capAt k b (nstageAt (Stage.top k) t) = nstageAt ⟨k, b⟩ t := by
  show Semiformula.nrel (capRelAt k b (Sum.inr (IInfRelW.stage (Stage.top k)))) ![t] = _
  rw [capRelAt_stage, dif_pos rfl]
  rfl

/-- The full predicate of a level other than `k` is untouched by bounding at level `k`. -/
theorem capAt_IOmegaAt_of_ne {j : ℕ} (h : j ≠ k) (t : Semiterm (LIinfW) ξ m) :
    capAt k b (IOmegaAt j t) = IOmegaAt j t :=
  capAt_stageAt_of_ne_top k b (fun e => h (Stage.top_injective e)) t

/-- The negated full predicate of a level other than `k` is untouched as well. -/
theorem capAt_nstageAt_of_ne_top {s : Stage} (hs : s ≠ Stage.top k) (t : Semiterm (LIinfW) ξ m) :
    capAt k b (nstageAt s t) = nstageAt s t := by
  show Semiformula.nrel (capRelAt k b (Sum.inr (IInfRelW.stage s))) ![t] = _
  rw [capRelAt_stage, dif_neg hs]
  rfl

/-- **Bounding commutes with every rewriting.** -/
theorem capAt_rew {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfW) ξ₁ m₁ ξ₂ m₂)
    (φ : Semiformula (LIinfW) ξ₁ m₁) : capAt k b (ω ▹ φ) = ω ▹ capAt k b φ := by
  induction φ using Semiformula.rec' generalizing m₂ with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [Semiformula.rew_rel, capAt_rel, capAt_rel, Semiformula.rew_rel]
  | hnrel r v => rw [Semiformula.rew_nrel, capAt_nrel, capAt_nrel, Semiformula.rew_nrel]
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

theorem capAt_subst (φ : Semiformula (LIinfW) ξ 1) (t : Semiterm (LIinfW) ξ m) :
    capAt k b (φ/[t]) = (capAt k b φ)/[t] := capAt_rew k b _ φ

/-- The terms do not see the stage. -/
theorem lMap_formHomAt_term {ξ' : Type*} {m' : ℕ} (a a' : StageAt k) (t : Semiterm LForm ξ' m') :
    Semiterm.lMap (formHomAt k a) t = Semiterm.lMap (formHomAt k a') t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih =>
    simp only [Semiterm.lMap_func]
    congr 1
    funext i
    exact ih i

/-- **Interaction of `capAt k b` with `formHomAt k a`**: `A` with `P ↦ I_k^{≺a}`, `Q ↦ Jlev k`,
bounded at level `k`, is `A` with `P ↦ I_k^{≺a'}`, `a' = b` if `a` was the top of level `k` and
`a' = a` otherwise (`Q ↦ Jlev k` is untouched: `capRelAt` fixes every `Jlev`). -/
theorem capAt_lMap_formHomAt (a : StageAt k) {ξ' : Type*} {m' : ℕ}
    (φ : Semiformula LForm ξ' m') :
    capAt k b (Semiformula.lMap (formHomAt k a) φ) =
      Semiformula.lMap (formHomAt k (if a = StageAt.top k then b else a)) φ := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
    show capAt k b (Semiformula.rel (formRelAt k a r) (Semiterm.lMap (formHomAt k a) ∘ v)) =
      Semiformula.rel (formRelAt k (if a = StageAt.top k then b else a) r)
        (Semiterm.lMap (formHomAt k (if a = StageAt.top k then b else a)) ∘ v)
    rw [capAt_rel]
    congr 1
    · rcases r with r | r
      · rfl
      · cases r with
        | P =>
          show capRelAt k b (Sum.inr (IInfRelW.stage ⟨k, a⟩)) = _
          rw [capRelAt_stage]
          show Sum.inr (IInfRelW.stage _) = Sum.inr (IInfRelW.stage _)
          congr 2
          by_cases h' : a = StageAt.top k
          · rw [dif_pos (Stage.mk_eq_top_iff.mpr h'), if_pos h']
          · rw [dif_neg (fun e => h' (Stage.mk_eq_top_iff.mp e)), if_neg h']
        | Q => rfl
    · funext i; exact lMap_formHomAt_term k a _ (v i)
  | hnrel r v =>
    show capAt k b (Semiformula.nrel (formRelAt k a r) (Semiterm.lMap (formHomAt k a) ∘ v)) =
      Semiformula.nrel (formRelAt k (if a = StageAt.top k then b else a) r)
        (Semiterm.lMap (formHomAt k (if a = StageAt.top k then b else a)) ∘ v)
    rw [capAt_nrel]
    congr 1
    · rcases r with r | r
      · rfl
      · cases r with
        | P =>
          show capRelAt k b (Sum.inr (IInfRelW.stage ⟨k, a⟩)) = _
          rw [capRelAt_stage]
          show Sum.inr (IInfRelW.stage _) = Sum.inr (IInfRelW.stage _)
          congr 2
          by_cases h' : a = StageAt.top k
          · rw [dif_pos (Stage.mk_eq_top_iff.mpr h'), if_pos h']
          · rw [dif_neg (fun e => h' (Stage.mk_eq_top_iff.mp e)), if_neg h']
        | Q => rfl
    · funext i; exact lMap_formHomAt_term k a _ (v i)
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and, capAt_and,
      ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or, capAt_or,
      ihφ, ihψ]
  | hall φ ih => rw [Semiformula.lMap_all, Semiformula.lMap_all, capAt_all, ih]
  | hexs φ ih => rw [Semiformula.lMap_exs, Semiformula.lMap_exs, capAt_exs, ih]

/-- The unfolding at level `k` commutes with bounding at level `k`. -/
theorem capAt_unfoldW (A : FormJ) (a : StageAt k) (t : Semiterm (LIinfW) ξ m) :
    capAt k b (unfoldW A k a t) = unfoldW A k (if a = StageAt.top k then b else a) t := by
  unfold unfoldW
  refine (capAt_rew k b _ _).trans ?_
  congr 1
  rw [capAt_rew, formAtW, formAtW, capAt_lMap_formHomAt]

/-- **`A_k(t, I_k^{≺Ω_{k+1}})^β = A_k(t, I_k^{≺β})`** -- the (Fix) case of boundedness, at
level `k`. -/
theorem capAt_unfoldW_top (A : FormJ) (t : Semiterm (LIinfW) ξ m) :
    capAt k b (unfoldW A k (StageAt.top k) t) = unfoldW A k b t := by
  rw [capAt_unfoldW, if_pos rfl]

end CapLit

/-- `k(Θ^β) ⊆ k(Θ) ∪ {β}`, bounded at level `k`, through `paramsVal`. -/
theorem paramsVal_capSeq {k : ℕ} {b : StageAt k} {H : Set ThetaVNoteD → Set ThetaVNoteD}
    {Θ Γ : Sequent (LIinfW)} (hb : b.1 ∈ H ∅) (hP : paramsVal (Θ ++ Γ) ⊆ H ∅) :
    paramsVal (Θ.map (capAt k b) ++ Γ) ⊆ H ∅ := by
  rw [paramsVal_append] at hP ⊢
  refine Set.union_subset ((paramsVal_map_capAt k b Θ).trans (Set.union_subset ?_ ?_)) ?_
  · exact Set.subset_union_left.trans hP
  · exact Set.singleton_subset_iff.mpr hb
  · exact Set.subset_union_right.trans hP

theorem mem_capSeq_of_mem_left {k : ℕ} {b : StageAt k} {Θ Γ : Sequent (LIinfW)}
    {χ : Proposition (LIinfW)} (h : χ ∈ Θ) : capAt k b χ ∈ Θ.map (capAt k b) ++ Γ :=
  List.mem_append_left _ (List.mem_map_of_mem h)

theorem mem_capSeq_of_mem_right {k : ℕ} {b : StageAt k} {Θ Γ : Sequent (LIinfW)}
    {χ : Proposition (LIinfW)} (h : χ ∈ Γ) : χ ∈ Θ.map (capAt k b) ++ Γ :=
  List.mem_append_right _ h

/-- A formula fixed by bounding stays in the sequent. -/
theorem mem_capSeq_of_capAt_eq {k : ℕ} {b : StageAt k} {Δ Θ Γ : Sequent (LIinfW)}
    {χ : Proposition (LIinfW)} (hχ : χ ∈ Δ) (hΔ : Δ ⊆ Θ ++ Γ) (he : capAt k b χ = χ) :
    χ ∈ Θ.map (capAt k b) ++ Γ := by
  rcases List.mem_append.mp (hΔ hχ) with h | h
  · exact he ▸ mem_capSeq_of_mem_left h
  · exact mem_capSeq_of_mem_right h

/-! ### Theorem 5.9 / Lemma 3.17 at level `k` -/

section Bound

variable {A : Semisentence LForm 2} {ρ : ThetaVNoteD}

/-- The statement of boundedness at level `k` for a derivation of `Δ`, bounding a list `Θ` of
formulas at the stage `b` and leaving the list `Γ` alone. -/
def BoundClaim (A : Semisentence LForm 2) (ρ : ThetaVNoteD) (k : ℕ)
    (b : StageAt k) (H : Set ThetaVNoteD → Set ThetaVNoteD) (α : ThetaVNoteD)
    (Δ : Sequent (LIinfW)) : Prop :=
  ThetaVNoteD.IsOperator H → b.1 ∈ H ∅ → α ≤ b.1 →
    ∀ Θ Γ : Sequent (LIinfW), Δ ⊆ Θ ++ Γ → paramsVal (Θ ++ Γ) ⊆ H ∅ →
      IDwDerivable A ρ H α (Θ.map (capAt k b) ++ Γ)

/-- The premises: from the claim for a premise `φ :: Δ`, the premise with `φ` unbounded (put
into the untouched part) and with `φ` bounded. -/
theorem bound_prem {k : ℕ} {b : StageAt k} {H : Set ThetaVNoteD → Set ThetaVNoteD}
    {α₀ : ThetaVNoteD} {φ : Proposition (LIinfW)} {Δ Θ Γ : Sequent (LIinfW)}
    (hH : ThetaVNoteD.IsOperator H) (hb : b.1 ∈ H ∅) (hα₀ : α₀ ≤ b.1)
    (d₀ : IDwDerivable A ρ H α₀ (φ :: Δ)) (ih₀ : BoundClaim A ρ k b H α₀ (φ :: Δ))
    (hΔ : Δ ⊆ Θ ++ Γ) (hP : paramsVal (Θ ++ Γ) ⊆ H ∅) :
    IDwDerivable A ρ H α₀ (φ :: (Θ.map (capAt k b) ++ Γ)) ∧
      IDwDerivable A ρ H α₀ (capAt k b φ :: (Θ.map (capAt k b) ++ Γ)) := by
  have hφ : Stage.val '' params φ ⊆ H ∅ := d₀.params_head_subset
  constructor
  · have h1 := ih₀ hH hb hα₀ Θ (φ :: Γ)
      (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_append_right _ List.mem_cons_self
        · rcases List.mem_append.mp (hΔ hx) with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))
      (by
        rw [paramsVal_append, paramsVal_cons]
        rw [paramsVal_append] at hP
        exact Set.union_subset (Set.subset_union_left.trans hP)
          (Set.union_subset hφ (Set.subset_union_right.trans hP)))
    refine h1.weaken_seq hH ?_ ?_
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)
    · rw [paramsVal_cons]
      exact Set.union_subset hφ (paramsVal_capSeq hb hP)
  · exact ih₀ hH hb hα₀ (φ :: Θ) Γ
      (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hΔ hx))
      (by
        show paramsVal (φ :: (Θ ++ Γ)) ⊆ H ∅
        rw [paramsVal_cons]
        exact Set.union_subset hφ hP)

/-- **Boundedness at level `k`, generalised to a list `Θ` of bounded formulas.**  The stage
clauses of every level use the unbounded premise. -/
theorem bound_aux {k : ℕ} {b : StageAt k} (hbΩ : b.1 < ThetaVNoteD.Omega k)
    {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Δ : Sequent (LIinfW)}
    (d : IDwDerivable A ρ H α Δ) : BoundClaim A ρ k b H α Δ := by
  induction d with
  | literal hα _ hφ hm =>
    intro hH hb hαb Θ Γ hΔ hP
    exact .literal hα (paramsVal_capSeq hb hP) hφ
      (mem_capSeq_of_capAt_eq hm hΔ (hφ.1.capAt_eq b))
  | verum hα _ hm =>
    intro hH hb hαb Θ Γ hΔ hP
    exact .verum hα (paramsVal_capSeq hb hP) (mem_capSeq_of_capAt_eq hm hΔ rfl)
  | idX t hα _ h1 h2 =>
    intro hH hb hαb Θ Γ hΔ hP
    exact .idX t hα (paramsVal_capSeq hb hP) (mem_capSeq_of_capAt_eq h1 hΔ (capAt_XinfAt k b t))
      (mem_capSeq_of_capAt_eq h2 hΔ (capAt_neg_XinfAt k b t))
  | and hα _ hm h0 h1 d0 d1 ih0 ih1 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    have p1 := bound_prem hH hb (le_trans (le_of_lt h1) hαb) d1 ih1 hΔ hP
    rcases List.mem_append.mp (hΔ hm) with h | h
    · exact .and hα (paramsVal_capSeq hb hP)
        (mem_capSeq_of_mem_left (k := k) (b := b) (Γ := Γ) h) h0 h1 p0.2 p1.2
    · exact .and hα (paramsVal_capSeq hb hP) (mem_capSeq_of_mem_right h) h0 h1 p0.1 p1.1
  | orL hα _ hm h0 d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    rcases List.mem_append.mp (hΔ hm) with h | h
    · exact .orL hα (paramsVal_capSeq hb hP)
        (mem_capSeq_of_mem_left (k := k) (b := b) (Γ := Γ) h) h0 p0.2
    · exact .orL hα (paramsVal_capSeq hb hP) (mem_capSeq_of_mem_right h) h0 p0.1
  | orR hα _ hm h1 h0 d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    rcases List.mem_append.mp (hΔ hm) with h | h
    · exact .orR hα (paramsVal_capSeq hb hP)
        (mem_capSeq_of_mem_left (k := k) (b := b) (Γ := Γ) h) h1 h0 p0.2
    · exact .orR hα (paramsVal_capSeq hb hP) (mem_capSeq_of_mem_right h) h1 h0 p0.1
  | @all H α Δ φ f hα _ hm hf d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := fun i => bound_prem hH hb (le_trans (le_of_lt (hf i)) hαb) (d0 i) (ih0 i) hΔ hP
    rcases List.mem_append.mp (hΔ hm) with h | h
    · refine .all (φ := capAt k b φ) f hα (paramsVal_capSeq hb hP)
        (mem_capSeq_of_mem_left (k := k) (b := b) (Γ := Γ) h) hf fun i => ?_
      have := (p0 i).2
      rwa [capAt_subst] at this
    · exact .all f hα (paramsVal_capSeq hb hP) (mem_capSeq_of_mem_right h) hf fun i => (p0 i).1
  | @exs H α Δ φ i α₀ hα _ hm hn h0 d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    rcases List.mem_append.mp (hΔ hm) with h | h
    · refine .exs (φ := capAt k b φ) i hα (paramsVal_capSeq hb hP)
        (mem_capSeq_of_mem_left (k := k) (b := b) (Γ := Γ) h) hn h0 ?_
      have := p0.2
      rwa [capAt_subst] at this
    · exact .exs i hα (paramsVal_capSeq hb hP) (mem_capSeq_of_mem_right h) hn h0 p0.1
  | @stage H α Δ j a t g α₀ hα _ hm hga hgα hgH h0 d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    by_cases hs : (⟨j, a⟩ : Stage) = Stage.top k
    · -- the full level-`k` predicate: if it lies in `Θ` it becomes `I_k^{≺b} t`
      have hjk : j = k := congrArg Stage.lvl hs
      subst hjk
      have ha : a = StageAt.top j := Stage.mk_eq_top_iff.mp hs
      subst ha
      rcases List.mem_append.mp (hΔ hm) with h | h
      · have hm' := mem_capSeq_of_mem_left (k := j) (b := b) (Γ := Γ) h
        rw [show capAt j b (stageAt (⟨j, StageAt.top j⟩ : Stage) t) =
            stageAt (⟨j, b⟩ : Stage) t from capAt_IOmegaAt j b t] at hm'
        exact .stage g hα (paramsVal_capSeq hb hP) hm' (lt_of_lt_of_le hgα hαb) hgα hgH h0
          p0.1
      · exact .stage g hα (paramsVal_capSeq hb hP) (mem_capSeq_of_mem_right h) hga hgα hgH h0
          p0.1
    · -- any other stage literal, of any level, is untouched
      exact .stage g hα (paramsVal_capSeq hb hP)
        (mem_capSeq_of_capAt_eq hm hΔ (capAt_stageAt_of_ne_top k b hs t)) hga hgα hgH h0 p0.1
  | @nstage H α Δ j a t f hα _ hm hf d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 : ∀ g : StageAt j, g.1 < a.1 →
        IDwDerivable A ρ (ThetaVNoteD.adjoin H {g.1}) (f g)
          (∼(unfoldW A j g t) :: (Θ.map (capAt k b) ++ Γ)) := by
      intro g hg
      have hsub : H ∅ ⊆ ThetaVNoteD.adjoin H {g.1} ∅ := hH.mono (Set.empty_subset _)
      exact (bound_prem (hH.adjoin {g.1}) (hsub hb) (le_trans (le_of_lt (hf g hg)) hαb)
        (d0 g hg) (ih0 g hg) hΔ (hP.trans hsub)).1
    by_cases hs : (⟨j, a⟩ : Stage) = Stage.top k
    · have hjk : j = k := congrArg Stage.lvl hs
      subst hjk
      have ha : a = StageAt.top j := Stage.mk_eq_top_iff.mp hs
      subst ha
      rcases List.mem_append.mp (hΔ hm) with h | h
      · -- `¬I_k t` in `Θ` becomes `¬I_k^{≺b} t`: a conjunction over fewer premises
        have hm' := mem_capSeq_of_mem_left (k := j) (b := b) (Γ := Γ) h
        rw [show capAt j b (nstageAt (⟨j, StageAt.top j⟩ : Stage) t) =
            nstageAt (⟨j, b⟩ : Stage) t from capAt_nstageAt_top j b t] at hm'
        exact .nstage f hα (paramsVal_capSeq hb hP) hm'
          (fun g hg => hf g (lt_of_lt_of_le hg b.2)) fun g hg => p0 g (lt_of_lt_of_le hg b.2)
      · exact .nstage f hα (paramsVal_capSeq hb hP) (mem_capSeq_of_mem_right h) hf p0
    · exact .nstage f hα (paramsVal_capSeq hb hP)
        (mem_capSeq_of_capAt_eq hm hΔ (capAt_nstageAt_of_ne_top k b hs t)) hf p0
  | @fix H α Δ j t α₀ hα _ hm hΩ h0 d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    -- (Fix_k) cannot occur below `Ω_{k+1}`; (Fix_j), `j ≠ k`, keeps its principal literal
    have hjk : j ≠ k := by
      rintro rfl
      exact absurd (lt_of_le_of_lt (le_trans hΩ hαb) hbΩ) (lt_irrefl _)
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    exact .fix hα (paramsVal_capSeq hb hP)
      (mem_capSeq_of_capAt_eq hm hΔ (capAt_IOmegaAt_of_ne k b hjk t)) hΩ h0 p0.1
  | jlev hα _ hm hs ht hl h0 d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    -- `Jlev` is fixed by bounding; the premise `I_{val s} t` (level `val s < ℓ`, whatever it
    -- is relative to `k`) is taken from the unbounded part, as for any stage clause
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    exact .jlev hα (paramsVal_capSeq hb hP) (mem_capSeq_of_capAt_eq hm hΔ (capAt_jlevAt k b _ _ _))
      hs ht hl h0 p0.1
  | njlev hα _ hm hs ht h0 d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    exact .njlev hα (paramsVal_capSeq hb hP)
      (mem_capSeq_of_capAt_eq hm hΔ (capAt_njlevAt k b _ _ _)) hs ht h0 fun hl =>
        (bound_prem hH hb (le_trans (le_of_lt (h0 hl)) hαb) (d0 hl) (ih0 hl) hΔ hP).1
  | cut hα _ hr h0 d0 d1 ih0 ih1 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    have p1 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d1 ih1 hΔ hP
    exact .cut hα (paramsVal_capSeq hb hP) hr h0 p0.1 p1.1

variable {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent (LIinfW)}
  {k : ℕ}

/-- **Boundedness at level `k`** (Freund Theorem 5.9 read at level `k`; Buchholz Lemma 3.17 and
Pohlers Theorem 3.4.3.7 at `κ = Ω_{k+1}`): `H ⊢^α_ρ Γ, ψ` gives `H ⊢^α_ρ Γ, ψ^{(k,b)}` for every
`b ∈ H(∅)` with `α ⪯ b ≺ Ω_{k+1}`.  No hypothesis on `ψ`, `Γ` or the forms `A`.  (`H` an
operator.)  This is the field `CollapseHyps.bound` of `IDw/Collapsing/Statement.lean`. -/
theorem boundedness (hH : ThetaVNoteD.IsOperator H) {ψ : Proposition (LIinfW)}
    {b : StageAt k} (hbH : b.1 ∈ H ∅) (hαb : α ≤ b.1)
    (hbΩ : b.1 < ThetaVNoteD.Omega k) (d : IDwDerivable A ρ H α (ψ :: Γ)) :
    IDwDerivable A ρ H α (capAt k b ψ :: Γ) :=
  bound_aux hbΩ d hH hbH hαb [ψ] Γ (List.Subset.refl _) d.params_subset

/-- Boundedness at level `k` of the whole sequent: `H ⊢^α_ρ Γ` gives `H ⊢^α_ρ Γ^{(k,b)}`. -/
theorem boundedness_seq (hH : ThetaVNoteD.IsOperator H) {b : StageAt k} (hbH : b.1 ∈ H ∅)
    (hαb : α ≤ b.1) (hbΩ : b.1 < ThetaVNoteD.Omega k) (d : IDwDerivable A ρ H α Γ) :
    IDwDerivable A ρ H α (Γ.map (capAt k b)) := by
  have h := bound_aux hbΩ d hH hbH hαb Γ [] (List.subset_append_left _ _)
    (by rw [List.append_nil]; exact d.params_subset)
  rwa [List.append_nil] at h

/-- **Buchholz's form of Lemma 3.17** (height `b` in the conclusion): `H ⊢^α_ρ Γ, ψ`,
`α ⪯ b ≺ Ω_{k+1}`, `b ∈ H(∅)` give `H ⊢^b_ρ Γ, ψ^{(k,b)}`. -/
theorem boundedness_height (hH : ThetaVNoteD.IsOperator H) {ψ : Proposition (LIinfW)}
    {b : StageAt k} (hbH : b.1 ∈ H ∅) (hαb : α ≤ b.1)
    (hbΩ : b.1 < ThetaVNoteD.Omega k) (d : IDwDerivable A ρ H α (ψ :: Γ)) :
    IDwDerivable A ρ H b.1 (capAt k b ψ :: Γ) :=
  (boundedness hH hbH hαb hbΩ d).mono_height hαb hbH

/-- **Boundedness at the height itself**: a derivation of height `α ≺ Ω_{k+1}` bounds its whole
end sequent at level `k` to the stage `α` (the form used at level `0` in the last step of the
lower bound, design note §2.7 step 5). -/
theorem boundedness_self (hH : ThetaVNoteD.IsOperator H) (hαΩ : α < ThetaVNoteD.Omega k)
    (d : IDwDerivable A ρ H α Γ) :
    IDwDerivable A ρ H α (Γ.map (capAt k (StageAt.ofLt k α hαΩ))) :=
  boundedness_seq hH d.height_mem le_rfl hαΩ d

/-- Boundedness for the formula `A_k(t, I_k^{≺Ω_{k+1}})`: it bounds to `A_k(t, I_k^{≺b})`. -/
theorem boundedness_unfold (hH : ThetaVNoteD.IsOperator H) {t : SyntacticTerm (LIinfW)}
    {b : StageAt k} (hbH : b.1 ∈ H ∅) (hαb : α ≤ b.1)
    (hbΩ : b.1 < ThetaVNoteD.Omega k)
    (d : IDwDerivable A ρ H α (unfoldW A k (StageAt.top k) t :: Γ)) :
    IDwDerivable A ρ H α (unfoldW A k b t :: Γ) := by
  have h := boundedness hH hbH hαb hbΩ d
  rwa [capAt_unfoldW_top] at h

/-- Boundedness for the formula `I_k t = I_k^{≺Ω_{k+1}} t`: it bounds to `I_k^{≺b} t` (the case
used for a cut on `I_k t` in the collapsing theorem). -/
theorem boundedness_IOmegaAt (hH : ThetaVNoteD.IsOperator H) {t : SyntacticTerm (LIinfW)}
    {b : StageAt k} (hbH : b.1 ∈ H ∅) (hαb : α ≤ b.1)
    (hbΩ : b.1 < ThetaVNoteD.Omega k) (d : IDwDerivable A ρ H α (IOmegaAt k t :: Γ)) :
    IDwDerivable A ρ H α (stageAt (⟨k, b⟩ : Stage) t :: Γ) := by
  have h := boundedness hH hbH hαb hbΩ d
  rwa [capAt_IOmegaAt] at h

end Bound

/-! ### Exercise 6.6 at level `k` -/

section NegStage

variable {A : Semisentence LForm 2} {ρ : ThetaVNoteD}

/-- The statement of Exercise 6.6 at level `k` for a derivation of `Δ`: the occurrence of
`¬I_k t` is replaced by `¬I_k^{≺δ} t`. -/
def NegClaim (A : Semisentence LForm 2) (ρ : ThetaVNoteD) (k : ℕ)
    (δ : StageAt k) (t : SyntacticTerm (LIinfW)) (H : Set ThetaVNoteD → Set ThetaVNoteD)
    (α : ThetaVNoteD) (Δ : Sequent (LIinfW)) : Prop :=
  ThetaVNoteD.IsOperator H → δ.1 ∈ H ∅ →
    ∀ Γ : Sequent (LIinfW), Δ ⊆ nstageAt (Stage.top k) t :: Γ → paramsVal Γ ⊆ H ∅ →
      IDwDerivable A ρ H α (nstageAt (⟨k, δ⟩ : Stage) t :: Γ)

theorem paramsVal_negSeq {k : ℕ} {δ : StageAt k} {t : SyntacticTerm (LIinfW)}
    {H : Set ThetaVNoteD → Set ThetaVNoteD} {Γ : Sequent (LIinfW)} (hδ : δ.1 ∈ H ∅)
    (hP : paramsVal Γ ⊆ H ∅) : paramsVal (nstageAt (⟨k, δ⟩ : Stage) t :: Γ) ⊆ H ∅ := by
  rw [paramsVal_cons, params_nstageAt, Set.image_singleton]
  exact Set.union_subset (Set.singleton_subset_iff.mpr hδ) hP

theorem neg_prem {k : ℕ} {δ : StageAt k} {t : SyntacticTerm (LIinfW)}
    {H : Set ThetaVNoteD → Set ThetaVNoteD} {α₀ : ThetaVNoteD} {φ : Proposition (LIinfW)}
    {Δ Γ : Sequent (LIinfW)} (hH : ThetaVNoteD.IsOperator H) (hδ : δ.1 ∈ H ∅)
    (d₀ : IDwDerivable A ρ H α₀ (φ :: Δ)) (ih₀ : NegClaim A ρ k δ t H α₀ (φ :: Δ))
    (hΔ : Δ ⊆ nstageAt (Stage.top k) t :: Γ) (hP : paramsVal Γ ⊆ H ∅) :
    IDwDerivable A ρ H α₀ (φ :: nstageAt (⟨k, δ⟩ : Stage) t :: Γ) := by
  have hφ : Stage.val '' params φ ⊆ H ∅ := d₀.params_head_subset
  have h1 := ih₀ hH hδ (φ :: Γ)
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · rcases List.mem_cons.mp (hΔ hx) with h | h
        · exact h ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    (by rw [paramsVal_cons]; exact Set.union_subset hφ hP)
  refine h1.weaken_seq hH ?_ ?_
  · intro x hx
    simp only [List.mem_cons] at hx ⊢
    tauto
  · rw [paramsVal_cons]
    exact Set.union_subset hφ (paramsVal_negSeq hδ hP)

/-- A principal formula other than `¬I_k t` stays in the sequent. -/
theorem mem_negSeq {k : ℕ} {δ : StageAt k} {t : SyntacticTerm (LIinfW)}
    {Δ Γ : Sequent (LIinfW)} {χ : Proposition (LIinfW)} (hχ : χ ∈ Δ)
    (hΔ : Δ ⊆ nstageAt (Stage.top k) t :: Γ) (hne : negHeadStage χ = none) :
    χ ∈ nstageAt (⟨k, δ⟩ : Stage) t :: Γ := by
  rcases List.mem_cons.mp (hΔ hχ) with h | h
  · rw [h, negHeadStage_nstageAt] at hne
    exact absurd hne (by simp)
  · exact List.mem_cons_of_mem _ h

theorem neg_aux {k : ℕ} {δ : StageAt k} {t : SyntacticTerm (LIinfW)}
    {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Δ : Sequent (LIinfW)}
    (d : IDwDerivable A ρ H α Δ) : NegClaim A ρ k δ t H α Δ := by
  induction d with
  | literal hα _ hφ hm =>
    intro hH hδ Γ hΔ hP
    exact .literal hα (paramsVal_negSeq hδ hP) hφ (mem_negSeq hm hΔ hφ.1.negHeadStage)
  | verum hα _ hm =>
    intro hH hδ Γ hΔ hP
    exact .verum hα (paramsVal_negSeq hδ hP) (mem_negSeq hm hΔ rfl)
  | idX s hα _ h1 h2 =>
    intro hH hδ Γ hΔ hP
    exact .idX s hα (paramsVal_negSeq hδ hP) (mem_negSeq h1 hΔ rfl) (mem_negSeq h2 hΔ rfl)
  | and hα _ hm h0 h1 d0 d1 ih0 ih1 =>
    intro hH hδ Γ hΔ hP
    exact .and hα (paramsVal_negSeq hδ hP) (mem_negSeq hm hΔ rfl) h0 h1
      (neg_prem hH hδ d0 ih0 hΔ hP) (neg_prem hH hδ d1 ih1 hΔ hP)
  | orL hα _ hm h0 d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .orL hα (paramsVal_negSeq hδ hP) (mem_negSeq hm hΔ rfl) h0
      (neg_prem hH hδ d0 ih0 hΔ hP)
  | orR hα _ hm h1 h0 d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .orR hα (paramsVal_negSeq hδ hP) (mem_negSeq hm hΔ rfl) h1 h0
      (neg_prem hH hδ d0 ih0 hΔ hP)
  | all f hα _ hm hf d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .all f hα (paramsVal_negSeq hδ hP) (mem_negSeq hm hΔ rfl) hf
      fun i => neg_prem hH hδ (d0 i) (ih0 i) hΔ hP
  | exs i hα _ hm hn h0 d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .exs i hα (paramsVal_negSeq hδ hP) (mem_negSeq hm hΔ rfl) hn h0
      (neg_prem hH hδ d0 ih0 hΔ hP)
  | stage g hα _ hm hga hgα hgH h0 d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .stage g hα (paramsVal_negSeq hδ hP) (mem_negSeq hm hΔ rfl) hga hgα hgH h0
      (neg_prem hH hδ d0 ih0 hΔ hP)
  | @nstage H α Δ j a s f hα _ hm hf d0 ih0 =>
    intro hH hδ Γ hΔ hP
    have p0 : ∀ g : StageAt j, g.1 < a.1 →
        IDwDerivable A ρ (ThetaVNoteD.adjoin H {g.1}) (f g)
          (∼(unfoldW A j g s) :: nstageAt (⟨k, δ⟩ : Stage) t :: Γ) := by
      intro g hg
      have hsub : H ∅ ⊆ ThetaVNoteD.adjoin H {g.1} ∅ := hH.mono (Set.empty_subset _)
      exact neg_prem (hH.adjoin {g.1}) (hsub hδ) (d0 g hg) (ih0 g hg) hΔ (hP.trans hsub)
    rcases List.mem_cons.mp (hΔ hm) with h | h
    · obtain ⟨hka, rfl⟩ := nstageAt_inj h
      have hjk : j = k := congrArg Stage.lvl hka
      subst hjk
      have ha : a = StageAt.top j := Stage.mk_eq_top_iff.mp hka
      subst ha
      exact .nstage f hα (paramsVal_negSeq hδ hP) List.mem_cons_self
        (fun g hg => hf g (lt_of_lt_of_le hg δ.2)) fun g hg => p0 g (lt_of_lt_of_le hg δ.2)
    · exact .nstage f hα (paramsVal_negSeq hδ hP) (List.mem_cons_of_mem _ h) hf p0
  | fix hα _ hm hΩ h0 d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .fix hα (paramsVal_negSeq hδ hP) (mem_negSeq hm hΔ rfl) hΩ h0
      (neg_prem hH hδ d0 ih0 hΔ hP)
  | jlev hα _ hm hs ht hl h0 d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .jlev hα (paramsVal_negSeq hδ hP) (mem_negSeq hm hΔ rfl) hs ht
      hl h0 (neg_prem hH hδ d0 ih0 hΔ hP)
  | njlev hα _ hm hs ht h0 d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .njlev hα (paramsVal_negSeq hδ hP) (mem_negSeq hm hΔ rfl) hs ht
      h0 fun hl => neg_prem hH hδ (d0 hl) (ih0 hl) hΔ hP
  | cut hα _ hr h0 d0 d1 ih0 ih1 =>
    intro hH hδ Γ hΔ hP
    exact .cut hα (paramsVal_negSeq hδ hP) hr h0 (neg_prem hH hδ d0 ih0 hΔ hP)
      (neg_prem hH hδ d1 ih1 hΔ hP)

/-- **Exercise 6.6 at level `k`** (Buchholz Lemma 3.9 c)): `H ⊢^α_ρ Γ, ¬I_k t` gives
`H ⊢^α_ρ Γ, ¬I_k^{≺δ} t` for every stage `δ ⪯ Ω_{k+1}` with `δ ∈ H(∅)`.  (`H` an operator.)
This is the field `CollapseHyps.negStage` of `IDw/Collapsing/Statement.lean`. -/
theorem neg_stage_bound {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.IsOperator H)
    {α : ThetaVNoteD} {k : ℕ} {t : SyntacticTerm (LIinfW)} {Γ : Sequent (LIinfW)}
    {δ : StageAt k} (hδ : δ.1 ∈ H ∅) (d : IDwDerivable A ρ H α (∼(IOmegaAt k t) :: Γ)) :
    IDwDerivable A ρ H α (nstageAt (⟨k, δ⟩ : Stage) t :: Γ) :=
  neg_aux d hH hδ Γ (List.Subset.refl _)
    ((paramsVal_mono (List.subset_cons_self _ _)).trans d.params_subset)

end NegStage

/-! ### Why the one-level proof does not port verbatim

If the form `A` mentions `I_0` at level `1` (say `A_1(t, I_1^{≺γ}) = I_0 t`), bounding at level
`0` changes the premise `A_1(t, I_1^{≺γ})` of level `1`'s stage clause into `I_0^{≺b} t`, which
is not of the form `A_1(t, I_1^{≺γ'})` for any `γ'`.  So the one-level step "bound the premise, then
`cap (A(t, I^{≺γ})) = A(t, I^{≺γ})`" is false with several levels; `bound_aux` uses the
unbounded premise instead and does not need it. -/

end IDw

end OrdinalAnalysis
