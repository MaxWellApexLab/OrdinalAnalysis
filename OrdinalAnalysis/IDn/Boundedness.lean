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
  (`capAt_unfold_smokeA_one_ne` below is a concrete instance), and a mechanical port gets stuck
  there.  But the generalised claim (`bound_aux`, as in `ID1`) bounds only a chosen list `Θ` of
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
import OrdinalAnalysis.IDn.Calculus

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder

variable {n : ℕ}

/-! ### Bounding of single literals -/

section CapLit

variable (k : Fin n) (b : StageAt k.val) {ξ : Type*} {m : ℕ}

theorem capAt_XinfAt (t : Semiterm (LIinfN n) ξ m) : capAt k b (XinfAt t) = XinfAt t := rfl

theorem capAt_neg_XinfAt (t : Semiterm (LIinfN n) ξ m) :
    capAt k b (∼(XinfAt t)) = ∼(XinfAt t) := rfl

/-- `(¬I_k t)^β = ¬I_k^{≺β} t`. -/
theorem capAt_nstageAt_top (t : Semiterm (LIinfN n) ξ m) :
    capAt k b (nstageAt (Stage.top k) t) = nstageAt ⟨k, b⟩ t := by
  show Semiformula.nrel (capRelAt k b (Sum.inr (IInfRelN.stage (Stage.top k)))) ![t] = _
  rw [capRelAt_stage, dif_pos rfl]
  rfl

/-- The full predicate of a level other than `k` is untouched by bounding at level `k`. -/
theorem capAt_IOmegaAt_of_ne {j : Fin n} (h : j ≠ k) (t : Semiterm (LIinfN n) ξ m) :
    capAt k b (IOmegaAt j t) = IOmegaAt j t :=
  capAt_stageAt_of_ne_top k b (fun e => h (Stage.top_injective e)) t

end CapLit

/-- `k(Θ^β) ⊆ k(Θ) ∪ {β}`, bounded at level `k`, through `paramsVal`. -/
theorem paramsVal_capSeq {k : Fin n} {b : StageAt k.val} {H : Set ThetaWNoteD → Set ThetaWNoteD}
    {Θ Γ : Sequent (LIinfN n)} (hb : b.1 ∈ H ∅) (hP : paramsVal (Θ ++ Γ) ⊆ H ∅) :
    paramsVal (Θ.map (capAt k b) ++ Γ) ⊆ H ∅ := by
  rw [paramsVal_append] at hP ⊢
  refine Set.union_subset ((paramsVal_map_capAt k b Θ).trans (Set.union_subset ?_ ?_)) ?_
  · exact Set.subset_union_left.trans hP
  · exact Set.singleton_subset_iff.mpr hb
  · exact Set.subset_union_right.trans hP

theorem mem_capSeq_of_mem_left {k : Fin n} {b : StageAt k.val} {Θ Γ : Sequent (LIinfN n)}
    {χ : Proposition (LIinfN n)} (h : χ ∈ Θ) : capAt k b χ ∈ Θ.map (capAt k b) ++ Γ :=
  List.mem_append_left _ (List.mem_map_of_mem h)

theorem mem_capSeq_of_mem_right {k : Fin n} {b : StageAt k.val} {Θ Γ : Sequent (LIinfN n)}
    {χ : Proposition (LIinfN n)} (h : χ ∈ Γ) : χ ∈ Θ.map (capAt k b) ++ Γ :=
  List.mem_append_right _ h

/-- A formula fixed by bounding stays in the sequent. -/
theorem mem_capSeq_of_capAt_eq {k : Fin n} {b : StageAt k.val} {Δ Θ Γ : Sequent (LIinfN n)}
    {χ : Proposition (LIinfN n)} (hχ : χ ∈ Δ) (hΔ : Δ ⊆ Θ ++ Γ) (he : capAt k b χ = χ) :
    χ ∈ Θ.map (capAt k b) ++ Γ := by
  rcases List.mem_append.mp (hΔ hχ) with h | h
  · exact he ▸ mem_capSeq_of_mem_left h
  · exact mem_capSeq_of_mem_right h

/-! ### Theorem 5.9 / Lemma 3.17 at level `k` -/

section Bound

variable {A : Fin n → Semisentence (LXIn n) 1} {ρ : ThetaWNoteD}

/-- The statement of boundedness at level `k` for a derivation of `Δ`, bounding a list `Θ` of
formulas at the stage `b` and leaving the list `Γ` alone. -/
def BoundClaim (A : Fin n → Semisentence (LXIn n) 1) (ρ : ThetaWNoteD) (k : Fin n)
    (b : StageAt k.val) (H : Set ThetaWNoteD → Set ThetaWNoteD) (α : ThetaWNoteD)
    (Δ : Sequent (LIinfN n)) : Prop :=
  ThetaWNoteD.IsOperator H → b.1 ∈ H ∅ → α ≤ b.1 →
    ∀ Θ Γ : Sequent (LIinfN n), Δ ⊆ Θ ++ Γ → paramsVal (Θ ++ Γ) ⊆ H ∅ →
      IDnDerivable A ρ H α (Θ.map (capAt k b) ++ Γ)

/-- The premises: from the claim for a premise `φ :: Δ`, the premise with `φ` unbounded (put
into the untouched part) and with `φ` bounded. -/
theorem bound_prem {k : Fin n} {b : StageAt k.val} {H : Set ThetaWNoteD → Set ThetaWNoteD}
    {α₀ : ThetaWNoteD} {φ : Proposition (LIinfN n)} {Δ Θ Γ : Sequent (LIinfN n)}
    (hH : ThetaWNoteD.IsOperator H) (hb : b.1 ∈ H ∅) (hα₀ : α₀ ≤ b.1)
    (d₀ : IDnDerivable A ρ H α₀ (φ :: Δ)) (ih₀ : BoundClaim A ρ k b H α₀ (φ :: Δ))
    (hΔ : Δ ⊆ Θ ++ Γ) (hP : paramsVal (Θ ++ Γ) ⊆ H ∅) :
    IDnDerivable A ρ H α₀ (φ :: (Θ.map (capAt k b) ++ Γ)) ∧
      IDnDerivable A ρ H α₀ (capAt k b φ :: (Θ.map (capAt k b) ++ Γ)) := by
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
theorem bound_aux {k : Fin n} {b : StageAt k.val} (hbΩ : b.1 < ThetaWNoteD.Omega k.val)
    {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Δ : Sequent (LIinfN n)}
    (d : IDnDerivable A ρ H α Δ) : BoundClaim A ρ k b H α Δ := by
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
    by_cases hs : (⟨j, a⟩ : Stage n) = Stage.top k
    · -- the full level-`k` predicate: if it lies in `Θ` it becomes `I_k^{≺b} t`
      have hjk : j = k := congrArg Stage.lvl hs
      subst hjk
      have ha : a = StageAt.top j.val := stage_mk_eq_top_iff.mp hs
      subst ha
      rcases List.mem_append.mp (hΔ hm) with h | h
      · have hm' := mem_capSeq_of_mem_left (k := j) (b := b) (Γ := Γ) h
        rw [show capAt j b (stageAt (⟨j, StageAt.top j.val⟩ : Stage n) t) =
            stageAt (⟨j, b⟩ : Stage n) t from capAt_IOmegaAt j b t] at hm'
        exact .stage g hα (paramsVal_capSeq hb hP) hm' (lt_of_lt_of_le hgα hαb) hgα hgH h0
          p0.1
      · exact .stage g hα (paramsVal_capSeq hb hP) (mem_capSeq_of_mem_right h) hga hgα hgH h0
          p0.1
    · -- any other stage literal, of any level, is untouched
      exact .stage g hα (paramsVal_capSeq hb hP)
        (mem_capSeq_of_capAt_eq hm hΔ (capAt_stageAt_of_ne_top k b hs t)) hga hgα hgH h0 p0.1
  | @nstage H α Δ j a t f hα _ hm hf d0 ih0 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 : ∀ g : StageAt j.val, g.1 < a.1 →
        IDnDerivable A ρ (ThetaWNoteD.adjoin H {g.1}) (f g)
          (∼(unfold (A j) j g t) :: (Θ.map (capAt k b) ++ Γ)) := by
      intro g hg
      have hsub : H ∅ ⊆ ThetaWNoteD.adjoin H {g.1} ∅ := hH.mono (Set.empty_subset _)
      exact (bound_prem (hH.adjoin {g.1}) (hsub hb) (le_trans (le_of_lt (hf g hg)) hαb)
        (d0 g hg) (ih0 g hg) hΔ (hP.trans hsub)).1
    by_cases hs : (⟨j, a⟩ : Stage n) = Stage.top k
    · have hjk : j = k := congrArg Stage.lvl hs
      subst hjk
      have ha : a = StageAt.top j.val := stage_mk_eq_top_iff.mp hs
      subst ha
      rcases List.mem_append.mp (hΔ hm) with h | h
      · -- `¬I_k t` in `Θ` becomes `¬I_k^{≺b} t`: a conjunction over fewer premises
        have hm' := mem_capSeq_of_mem_left (k := j) (b := b) (Γ := Γ) h
        rw [show capAt j b (nstageAt (⟨j, StageAt.top j.val⟩ : Stage n) t) =
            nstageAt (⟨j, b⟩ : Stage n) t from capAt_nstageAt_top j b t] at hm'
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
  | cut hα _ hr h0 d0 d1 ih0 ih1 =>
    intro hH hb hαb Θ Γ hΔ hP
    have p0 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d0 ih0 hΔ hP
    have p1 := bound_prem hH hb (le_trans (le_of_lt h0) hαb) d1 ih1 hΔ hP
    exact .cut hα (paramsVal_capSeq hb hP) hr h0 p0.1 p1.1

variable {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
  {k : Fin n}

/-- **Boundedness at level `k`** (Freund Theorem 5.9 read at level `k`; Buchholz Lemma 3.17 and
Pohlers Theorem 3.4.3.7 at `κ = Ω_{k+1}`): `H ⊢^α_ρ Γ, ψ` gives `H ⊢^α_ρ Γ, ψ^{(k,b)}` for every
`b ∈ H(∅)` with `α ⪯ b ≺ Ω_{k+1}`.  No hypothesis on `ψ`, `Γ` or the forms `A`.  (`H` an
operator.)  This is the field `CollapseHyps.bound` of `IDn/Collapsing/Statement.lean`. -/
theorem boundedness (hH : ThetaWNoteD.IsOperator H) {ψ : Proposition (LIinfN n)}
    {b : StageAt k.val} (hbH : b.1 ∈ H ∅) (hαb : α ≤ b.1)
    (hbΩ : b.1 < ThetaWNoteD.Omega k.val) (d : IDnDerivable A ρ H α (ψ :: Γ)) :
    IDnDerivable A ρ H α (capAt k b ψ :: Γ) :=
  bound_aux hbΩ d hH hbH hαb [ψ] Γ (List.Subset.refl _) d.params_subset

/-- Boundedness at level `k` of the whole sequent: `H ⊢^α_ρ Γ` gives `H ⊢^α_ρ Γ^{(k,b)}`. -/
theorem boundedness_seq (hH : ThetaWNoteD.IsOperator H) {b : StageAt k.val} (hbH : b.1 ∈ H ∅)
    (hαb : α ≤ b.1) (hbΩ : b.1 < ThetaWNoteD.Omega k.val) (d : IDnDerivable A ρ H α Γ) :
    IDnDerivable A ρ H α (Γ.map (capAt k b)) := by
  have h := bound_aux hbΩ d hH hbH hαb Γ [] (List.subset_append_left _ _)
    (by rw [List.append_nil]; exact d.params_subset)
  rwa [List.append_nil] at h

/-- **Buchholz's form of Lemma 3.17** (height `b` in the conclusion): `H ⊢^α_ρ Γ, ψ`,
`α ⪯ b ≺ Ω_{k+1}`, `b ∈ H(∅)` give `H ⊢^b_ρ Γ, ψ^{(k,b)}`. -/
theorem boundedness_height (hH : ThetaWNoteD.IsOperator H) {ψ : Proposition (LIinfN n)}
    {b : StageAt k.val} (hbH : b.1 ∈ H ∅) (hαb : α ≤ b.1)
    (hbΩ : b.1 < ThetaWNoteD.Omega k.val) (d : IDnDerivable A ρ H α (ψ :: Γ)) :
    IDnDerivable A ρ H b.1 (capAt k b ψ :: Γ) :=
  (boundedness hH hbH hαb hbΩ d).mono_height hαb hbH

/-- **Boundedness at the height itself**: a derivation of height `α ≺ Ω_{k+1}` bounds its whole
end sequent at level `k` to the stage `α` (the form used at level `0` in the last step of the
lower bound, design note §2.7 step 5). -/
theorem boundedness_self (hH : ThetaWNoteD.IsOperator H) (hαΩ : α < ThetaWNoteD.Omega k.val)
    (d : IDnDerivable A ρ H α Γ) :
    IDnDerivable A ρ H α (Γ.map (capAt k (StageAt.ofLt k.val α hαΩ))) :=
  boundedness_seq hH d.height_mem le_rfl hαΩ d

/-- Boundedness for the formula `A_k(t, I_k^{≺Ω_{k+1}})`: it bounds to `A_k(t, I_k^{≺b})`. -/
theorem boundedness_unfold (hH : ThetaWNoteD.IsOperator H) {t : SyntacticTerm (LIinfN n)}
    {b : StageAt k.val} (hbH : b.1 ∈ H ∅) (hαb : α ≤ b.1)
    (hbΩ : b.1 < ThetaWNoteD.Omega k.val)
    (d : IDnDerivable A ρ H α (unfold (A k) k (StageAt.top k.val) t :: Γ)) :
    IDnDerivable A ρ H α (unfold (A k) k b t :: Γ) := by
  have h := boundedness hH hbH hαb hbΩ d
  rwa [capAt_unfold_top] at h

/-- Boundedness for the formula `I_k t = I_k^{≺Ω_{k+1}} t`: it bounds to `I_k^{≺b} t` (the case
used for a cut on `I_k t` in the collapsing theorem). -/
theorem boundedness_IOmegaAt (hH : ThetaWNoteD.IsOperator H) {t : SyntacticTerm (LIinfN n)}
    {b : StageAt k.val} (hbH : b.1 ∈ H ∅) (hαb : α ≤ b.1)
    (hbΩ : b.1 < ThetaWNoteD.Omega k.val) (d : IDnDerivable A ρ H α (IOmegaAt k t :: Γ)) :
    IDnDerivable A ρ H α (stageAt (⟨k, b⟩ : Stage n) t :: Γ) := by
  have h := boundedness hH hbH hαb hbΩ d
  rwa [capAt_IOmegaAt] at h

end Bound

/-! ### Exercise 6.6 at level `k` -/

section NegStage

variable {A : Fin n → Semisentence (LXIn n) 1} {ρ : ThetaWNoteD}

/-- The statement of Exercise 6.6 at level `k` for a derivation of `Δ`: the occurrence of
`¬I_k t` is replaced by `¬I_k^{≺δ} t`. -/
def NegClaim (A : Fin n → Semisentence (LXIn n) 1) (ρ : ThetaWNoteD) (k : Fin n)
    (δ : StageAt k.val) (t : SyntacticTerm (LIinfN n)) (H : Set ThetaWNoteD → Set ThetaWNoteD)
    (α : ThetaWNoteD) (Δ : Sequent (LIinfN n)) : Prop :=
  ThetaWNoteD.IsOperator H → δ.1 ∈ H ∅ →
    ∀ Γ : Sequent (LIinfN n), Δ ⊆ nstageAt (Stage.top k) t :: Γ → paramsVal Γ ⊆ H ∅ →
      IDnDerivable A ρ H α (nstageAt (⟨k, δ⟩ : Stage n) t :: Γ)

theorem paramsVal_negSeq {k : Fin n} {δ : StageAt k.val} {t : SyntacticTerm (LIinfN n)}
    {H : Set ThetaWNoteD → Set ThetaWNoteD} {Γ : Sequent (LIinfN n)} (hδ : δ.1 ∈ H ∅)
    (hP : paramsVal Γ ⊆ H ∅) : paramsVal (nstageAt (⟨k, δ⟩ : Stage n) t :: Γ) ⊆ H ∅ := by
  rw [paramsVal_cons, params_nstageAt, Set.image_singleton]
  exact Set.union_subset (Set.singleton_subset_iff.mpr hδ) hP

theorem neg_prem {k : Fin n} {δ : StageAt k.val} {t : SyntacticTerm (LIinfN n)}
    {H : Set ThetaWNoteD → Set ThetaWNoteD} {α₀ : ThetaWNoteD} {φ : Proposition (LIinfN n)}
    {Δ Γ : Sequent (LIinfN n)} (hH : ThetaWNoteD.IsOperator H) (hδ : δ.1 ∈ H ∅)
    (d₀ : IDnDerivable A ρ H α₀ (φ :: Δ)) (ih₀ : NegClaim A ρ k δ t H α₀ (φ :: Δ))
    (hΔ : Δ ⊆ nstageAt (Stage.top k) t :: Γ) (hP : paramsVal Γ ⊆ H ∅) :
    IDnDerivable A ρ H α₀ (φ :: nstageAt (⟨k, δ⟩ : Stage n) t :: Γ) := by
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
theorem mem_negSeq {k : Fin n} {δ : StageAt k.val} {t : SyntacticTerm (LIinfN n)}
    {Δ Γ : Sequent (LIinfN n)} {χ : Proposition (LIinfN n)} (hχ : χ ∈ Δ)
    (hΔ : Δ ⊆ nstageAt (Stage.top k) t :: Γ) (hne : negHeadStage χ = none) :
    χ ∈ nstageAt (⟨k, δ⟩ : Stage n) t :: Γ := by
  rcases List.mem_cons.mp (hΔ hχ) with h | h
  · rw [h, negHeadStage_nstageAt] at hne
    exact absurd hne (by simp)
  · exact List.mem_cons_of_mem _ h

theorem neg_aux {k : Fin n} {δ : StageAt k.val} {t : SyntacticTerm (LIinfN n)}
    {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Δ : Sequent (LIinfN n)}
    (d : IDnDerivable A ρ H α Δ) : NegClaim A ρ k δ t H α Δ := by
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
    have p0 : ∀ g : StageAt j.val, g.1 < a.1 →
        IDnDerivable A ρ (ThetaWNoteD.adjoin H {g.1}) (f g)
          (∼(unfold (A j) j g s) :: nstageAt (⟨k, δ⟩ : Stage n) t :: Γ) := by
      intro g hg
      have hsub : H ∅ ⊆ ThetaWNoteD.adjoin H {g.1} ∅ := hH.mono (Set.empty_subset _)
      exact neg_prem (hH.adjoin {g.1}) (hsub hδ) (d0 g hg) (ih0 g hg) hΔ (hP.trans hsub)
    rcases List.mem_cons.mp (hΔ hm) with h | h
    · obtain ⟨hka, rfl⟩ := nstageAt_inj h
      have hjk : j = k := congrArg Stage.lvl hka
      subst hjk
      have ha : a = StageAt.top j.val := stage_mk_eq_top_iff.mp hka
      subst ha
      exact .nstage f hα (paramsVal_negSeq hδ hP) List.mem_cons_self
        (fun g hg => hf g (lt_of_lt_of_le hg δ.2)) fun g hg => p0 g (lt_of_lt_of_le hg δ.2)
    · exact .nstage f hα (paramsVal_negSeq hδ hP) (List.mem_cons_of_mem _ h) hf p0
  | fix hα _ hm hΩ h0 d0 ih0 =>
    intro hH hδ Γ hΔ hP
    exact .fix hα (paramsVal_negSeq hδ hP) (mem_negSeq hm hΔ rfl) hΩ h0
      (neg_prem hH hδ d0 ih0 hΔ hP)
  | cut hα _ hr h0 d0 d1 ih0 ih1 =>
    intro hH hδ Γ hΔ hP
    exact .cut hα (paramsVal_negSeq hδ hP) hr h0 (neg_prem hH hδ d0 ih0 hΔ hP)
      (neg_prem hH hδ d1 ih1 hΔ hP)

/-- **Exercise 6.6 at level `k`** (Buchholz Lemma 3.9 c)): `H ⊢^α_ρ Γ, ¬I_k t` gives
`H ⊢^α_ρ Γ, ¬I_k^{≺δ} t` for every stage `δ ⪯ Ω_{k+1}` with `δ ∈ H(∅)`.  (`H` an operator.)
This is the field `CollapseHyps.negStage` of `IDn/Collapsing/Statement.lean`. -/
theorem neg_stage_bound {H : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ThetaWNoteD.IsOperator H)
    {α : ThetaWNoteD} {k : Fin n} {t : SyntacticTerm (LIinfN n)} {Γ : Sequent (LIinfN n)}
    {δ : StageAt k.val} (hδ : δ.1 ∈ H ∅) (d : IDnDerivable A ρ H α (∼(IOmegaAt k t) :: Γ)) :
    IDnDerivable A ρ H α (nstageAt (⟨k, δ⟩ : Stage n) t :: Γ) :=
  neg_aux d hH hδ Γ (List.Subset.refl _)
    ((paramsVal_mono (List.subset_cons_self _ _)).trans d.params_subset)

end NegStage

/-! ### Why the one-level proof does not port verbatim

With `A_1(x) := I_0(x)` (`smokeA` of `IDn/Calculus.lean`), bounding at level `0` changes the
premise `A_1(t, I_1^{≺γ}) = I_0 t` of level `1`'s stage clause into `I_0^{≺b} t`, which is not
of the form `A_1(t, I_1^{≺γ'})` for any `γ'`.  So the one-level step "bound the premise, then
`cap (A(t, I^{≺γ})) = A(t, I^{≺γ})`" is false with several levels; `bound_aux` uses the
unbounded premise instead and does not need it. -/

theorem capAt_unfold_smokeA_one_ne (b : StageAt (0 : Fin 2).val)
    (hb : b ≠ StageAt.top (0 : Fin 2).val) (g : StageAt (1 : Fin 2).val)
    (t : SyntacticTerm (LIinfN 2)) :
    capAt (0 : Fin 2) b (unfold (smokeA 1) 1 g t) ≠ unfold (smokeA 1) 1 g t := by
  rw [unfold_smokeA_one, capAt_IOmegaAt, IOmegaAt_eq]
  intro h
  exact hb (stage_mk_eq_top_iff.mp (stageAt_inj h).1)

end IDn

end OrdinalAnalysis
