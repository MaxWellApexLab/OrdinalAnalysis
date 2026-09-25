/-
  The operator-controlled infinitary calculus `ID_{<ω}^∞`, for `n` simultaneous inductive
  definitions with stage predicates `I_k^{≺α}`, `k : Fin n`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §5 (as ported by `ID1/Calculus.lean`). After Buchholz, *A simplified
  version of local predicativity* (1992), §4 (several simultaneous predicates).

  **The relation.**  `IDnDerivable A ρ H α Γ` is the multi-level form of `ID1.IDerivable`: one
  operator family `A : Fin n → Semisentence (LXIn n) 1` (`A k` is the defining form of level
  `k`; it may mention `X` and any `I_j`, per level, exactly as `IDn/Theory.lean`'s `ID` axioms
  do), one *level-free* operator `H` (Freund's operators are already level-free; the multi-level
  hull `Ordinal.ThetaW.HullSingle`/`HullDom` gives `ThetaWNoteD.HopS`/`NiceS`/`HullHypS`/
  `HullHypGe` as the level-free operator this calculus's side conditions are phrased against,
  **not** the per-level `Hop k`/
  `Nice k` of `Ordinal/ThetaW/Hull.lean`), and a single height/rank pair `α`, `ρ : ThetaWNoteD`
  shared by every level (a sequent can mix stage atoms of any level).

  The clauses are `ID1.IDerivable`'s, unchanged except: (i) the stage clauses `stage`/`nstage`/
  `fix` each carry an explicit level `k : Fin n`, their local stage variables have type
  `IDn.StageAt k.val` (**not** the packaged `IDn.Stage n`, which only appears wrapped as
  `⟨k, ·⟩` where an actual `LIinfN n`-atom or its parameter is formed — this is the one
  systematic fix the mechanical `id1_to_idn.py` rewrite cannot make on its own, see
  `tools/README_id1_to_idn.md`'s measured residue for `Boundedness.lean`); (ii) the unfolding
  `unfold A g t` of `ID1` becomes `unfold (A k) k g t`; (iii) the control condition
  `paramsList Γ ⊆ H ∅` becomes `IDn.paramsVal Γ ⊆ H ∅` (`IDn/CalculusAux.lean`), since
  `paramsList` returns a set of `Stage n` (level and bound together) but the level-free operator
  acts on sets of bare `ThetaWNoteD` values.

  Every other deviation from `ID1.IDerivable` noted there (lists instead of finite sets, the
  `X`-clause `idX`, formulas with free variables, the true literals of arithmetic) carries over
  unchanged; see `IDn/CalculusAux.lean`'s docstring for the multi-level statement of those
  pieces.

  Contents.

    `IDnDerivable`                                   the calculus, with levels
    `IDnDerivable.control`, `mono_rank`, `mono_height`, `weaken`   Exercise 5.7 (b)
    `IDnDerivable.mono_op`                           Exercise 5.7 (a)
    `IDnDerivable.adjoin`, `weaken_adjoin`            `H ⊢ Γ` gives `H[k(Δ)] ⊢ Γ, Δ`
    `IDnDerivable.inv_and_left`, `inv_and_right`,
    `IDnDerivable.inv_all`, `inv_nstage`              Exercise 7.1 (a), inversion
    §Smoke test                                      `n = 2`: closure of `I_1`, the Ω₂-rule
-/
import OrdinalAnalysis.IDn.CalculusAux
import OrdinalAnalysis.Tactic.Order

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder

variable {n : ℕ}

/-! ### The calculus -/

/-- **The multi-level operator-controlled calculus**: `IDnDerivable A ρ H α Γ` is
`H ⊢^α_ρ Γ` for the operator family `A` (one form `A k` per level). Every clause carries the
initial condition `α ∈ H(∅)` and `k(Γ) ⊆ H(∅)` (read through `paramsVal`). -/
inductive IDnDerivable (A : Fin n → Semisentence (LXIn n) 1) (ρ : ThetaWNoteD) :
    (Set ThetaWNoteD → Set ThetaWNoteD) → ThetaWNoteD → Sequent (LIinfN n) → Prop
  /-- (V) for a true literal of arithmetic, the empty conjunction. -/
  | literal {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
      {φ : Proposition (LIinfN n)} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → TrueLit φ → φ ∈ Γ → IDnDerivable A ρ H α Γ
  /-- (V) for `⊤`, the empty conjunction. -/
  | verum {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → ⊤ ∈ Γ → IDnDerivable A ρ H α Γ
  /-- The identity axiom of the free predicate `X`. -/
  | idX {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
      (t : SyntacticTerm (LIinfN n)) :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → XinfAt t ∈ Γ → ∼(XinfAt t) ∈ Γ → IDnDerivable A ρ H α Γ
  /-- (V) for `ψ₀ ∧ ψ₁ ≃ ⋀_{i≺2} ψ_i`. -/
  | and {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
      {φ ψ : Proposition (LIinfN n)} {α₀ α₁ : ThetaWNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → φ ⋏ ψ ∈ Γ → α₀ < α → α₁ < α →
      IDnDerivable A ρ H α₀ (φ :: Γ) → IDnDerivable A ρ H α₁ (ψ :: Γ) → IDnDerivable A ρ H α Γ
  /-- (W) for `ψ₀ ∨ ψ₁ ≃ ⋁_{i≺2} ψ_i`, index `0`. -/
  | orL {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
      {φ ψ : Proposition (LIinfN n)} {α₀ : ThetaWNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → φ ⋎ ψ ∈ Γ → α₀ < α →
      IDnDerivable A ρ H α₀ (φ :: Γ) → IDnDerivable A ρ H α Γ
  /-- (W) for `ψ₀ ∨ ψ₁ ≃ ⋁_{i≺2} ψ_i`, index `1` (so `1 ≺ α`). -/
  | orR {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
      {φ ψ : Proposition (LIinfN n)} {α₀ : ThetaWNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → φ ⋎ ψ ∈ Γ → ThetaWNoteD.one < α → α₀ < α →
      IDnDerivable A ρ H α₀ (ψ :: Γ) → IDnDerivable A ρ H α Γ
  /-- (V) for `∀x ψ(x) ≃ ⋀_{m≺ω} ψ(m̄)`: the ω-rule. -/
  | all {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
      {φ : Semiproposition (LIinfN n) 1} (f : ℕ → ThetaWNoteD) :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → (∀¹ φ) ∈ Γ → (∀ m, f m < α) →
      (∀ m, IDnDerivable A ρ H (f m) (φ/[numI m] :: Γ)) → IDnDerivable A ρ H α Γ
  /-- (W) for `∃x ψ(x) ≃ ⋁_{m≺ω} ψ(m̄)`, with the witness `m ≺ α`. -/
  | exs {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
      {φ : Semiproposition (LIinfN n) 1} (m : ℕ) {α₀ : ThetaWNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → (∃¹ φ) ∈ Γ → ThetaWNoteD.ofNat m < α → α₀ < α →
      IDnDerivable A ρ H α₀ (φ/[numI m] :: Γ) → IDnDerivable A ρ H α Γ
  /-- (W) for `I_k^{≺δ} t ≃ ⋁_{γ≺δ} A_k(t, I_k^{≺γ})`, at level `k`, with `γ ≺ α` and
  `γ ∈ H(∅)`. -/
  | stage {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
      {k : Fin n} {a : StageAt k.val} {t : SyntacticTerm (LIinfN n)} (g : StageAt k.val)
      {α₀ : ThetaWNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → stageAt (⟨k, a⟩ : Stage n) t ∈ Γ → g.1 < a.1 → g.1 < α →
      g.1 ∈ H ∅ → α₀ < α → IDnDerivable A ρ H α₀ (unfold (A k) k g t :: Γ) →
      IDnDerivable A ρ H α Γ
  /-- (V) for `¬I_k^{≺δ} t ≃ ⋀_{γ≺δ} ¬A_k(t, I_k^{≺γ})`, at level `k`, the premise for `γ` with
  `H[{γ}]`. -/
  | nstage {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
      {k : Fin n} {a : StageAt k.val} {t : SyntacticTerm (LIinfN n)}
      (f : StageAt k.val → ThetaWNoteD) :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → nstageAt (⟨k, a⟩ : Stage n) t ∈ Γ →
      (∀ g : StageAt k.val, g.1 < a.1 → f g < α) →
      (∀ g : StageAt k.val, g.1 < a.1 →
        IDnDerivable A ρ (ThetaWNoteD.adjoin H {g.1}) (f g) (∼(unfold (A k) k g t) :: Γ)) →
      IDnDerivable A ρ H α Γ
  /-- (Fix) at level `k`: `Ω_{k+1} ⪯ α`, `I_k t = I_k^{≺Ω_{k+1}} t ∈ Γ`, premise
  `Γ, A_k(t, I_k^{≺Ω_{k+1}})`. -/
  | fix {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
      {k : Fin n} {t : SyntacticTerm (LIinfN n)} {α₀ : ThetaWNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → IOmegaAt k t ∈ Γ → ThetaWNoteD.Omega k.val ≤ α → α₀ < α →
      IDnDerivable A ρ H α₀ (unfold (A k) k (StageAt.top k.val) t :: Γ) →
      IDnDerivable A ρ H α Γ
  /-- (Cut): a cut formula of rank `≺ ρ`, both premises of the same height. -/
  | cut {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}
      {ψ : Proposition (LIinfN n)} {α₀ : ThetaWNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → rk ψ < ρ → α₀ < α →
      IDnDerivable A ρ H α₀ (ψ :: Γ) → IDnDerivable A ρ H α₀ (∼ψ :: Γ) →
      IDnDerivable A ρ H α Γ

namespace IDnDerivable

variable {A : Fin n → Semisentence (LXIn n) 1} {ρ : ThetaWNoteD}
  {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}

/-- **The initial condition**: `{α} ∪ k(Γ) ⊆ H(∅)`. -/
theorem control (d : IDnDerivable A ρ H α Γ) : α ∈ H ∅ ∧ paramsVal Γ ⊆ H ∅ := by
  cases d <;> exact ⟨by assumption, by assumption⟩

theorem height_mem (d : IDnDerivable A ρ H α Γ) : α ∈ H ∅ := d.control.1

theorem params_subset (d : IDnDerivable A ρ H α Γ) : paramsVal Γ ⊆ H ∅ := d.control.2

/-- The head formula of a derivable sequent has its parameters' values in `H(∅)`. -/
theorem params_head_subset {φ : Proposition (LIinfN n)} (d : IDnDerivable A ρ H α (φ :: Γ)) :
    Stage.val '' params φ ⊆ H ∅ :=
  (params_val_subset_paramsVal List.mem_cons_self).trans d.params_subset

/-- **Exercise 5.7 (b), cut rank**: `ρ ⪯ ρ'` gives `H ⊢^α_{ρ'} Γ`. -/
theorem mono_rank {ρ' : ThetaWNoteD} (hρ : ρ ≤ ρ') (d : IDnDerivable A ρ H α Γ) :
    IDnDerivable A ρ' H α Γ := by
  induction d with
  | literal hα hΓ hφ hm => exact .literal hα hΓ hφ hm
  | verum hα hΓ hm => exact .verum hα hΓ hm
  | idX t hα hΓ h1 h2 => exact .idX t hα hΓ h1 h2
  | and hα hΓ hm h0 h1 _ _ ih0 ih1 => exact .and hα hΓ hm h0 h1 ih0 ih1
  | orL hα hΓ hm h0 _ ih => exact .orL hα hΓ hm h0 ih
  | orR hα hΓ hm h1 h0 _ ih => exact .orR hα hΓ hm h1 h0 ih
  | all f hα hΓ hm hf _ ih => exact .all f hα hΓ hm hf ih
  | exs m hα hΓ hm hn h0 _ ih => exact .exs m hα hΓ hm hn h0 ih
  | stage g hα hΓ hm hga hgα hgH h0 _ ih => exact .stage g hα hΓ hm hga hgα hgH h0 ih
  | nstage f hα hΓ hm hf _ ih => exact .nstage f hα hΓ hm hf ih
  | fix hα hΓ hm hΩ h0 _ ih => exact .fix hα hΓ hm hΩ h0 ih
  | cut hα hΓ hr h0 _ _ ih0 ih1 => exact .cut hα hΓ (lt_of_lt_of_le hr hρ) h0 ih0 ih1

/-- **Exercise 5.7 (b), height**: `α ⪯ α'` and `α' ∈ H(∅)` give `H ⊢^{α'}_ρ Γ`. Only the last
inference changes. -/
theorem mono_height {α' : ThetaWNoteD} (hα : α ≤ α') (hα' : α' ∈ H ∅)
    (d : IDnDerivable A ρ H α Γ) : IDnDerivable A ρ H α' Γ := by
  cases d with
  | literal _ hΓ hφ hm => exact .literal hα' hΓ hφ hm
  | verum _ hΓ hm => exact .verum hα' hΓ hm
  | idX t _ hΓ h1 h2 => exact .idX t hα' hΓ h1 h2
  | and _ hΓ hm h0 h1 d0 d1 =>
    exact .and hα' hΓ hm (lt_of_lt_of_le h0 hα) (lt_of_lt_of_le h1 hα) d0 d1
  | orL _ hΓ hm h0 d0 => exact .orL hα' hΓ hm (lt_of_lt_of_le h0 hα) d0
  | orR _ hΓ hm h1 h0 d0 =>
    exact .orR hα' hΓ hm (lt_of_lt_of_le h1 hα) (lt_of_lt_of_le h0 hα) d0
  | all f _ hΓ hm hf d0 => exact .all f hα' hΓ hm (fun m => lt_of_lt_of_le (hf m) hα) d0
  | exs m _ hΓ hm hn h0 d0 =>
    exact .exs m hα' hΓ hm (lt_of_lt_of_le hn hα) (lt_of_lt_of_le h0 hα) d0
  | stage g _ hΓ hm hga hgα hgH h0 d0 =>
    exact .stage g hα' hΓ hm hga (lt_of_lt_of_le hgα hα) hgH (lt_of_lt_of_le h0 hα) d0
  | nstage f _ hΓ hm hf d0 =>
    exact .nstage f hα' hΓ hm (fun g hg => lt_of_lt_of_le (hf g hg) hα) d0
  | fix _ hΓ hm hΩ h0 d0 => exact .fix hα' hΓ hm (le_trans hΩ hα) (lt_of_lt_of_le h0 hα) d0
  | cut _ hΓ hr h0 d0 d1 => exact .cut hα' hΓ hr (lt_of_lt_of_le h0 hα) d0 d1

/-- **Exercise 5.7 (a)**: `H(X) ⊆ H'(X)` for all `X` gives `H' ⊢^α_ρ Γ`. -/
theorem mono_op {H' : Set ThetaWNoteD → Set ThetaWNoteD} (hH : ∀ X, H X ⊆ H' X)
    (d : IDnDerivable A ρ H α Γ) : IDnDerivable A ρ H' α Γ := by
  induction d generalizing H' with
  | literal hα hΓ hφ hm => exact .literal (hH _ hα) (hΓ.trans (hH _)) hφ hm
  | verum hα hΓ hm => exact .verum (hH _ hα) (hΓ.trans (hH _)) hm
  | idX t hα hΓ h1 h2 => exact .idX t (hH _ hα) (hΓ.trans (hH _)) h1 h2
  | and hα hΓ hm h0 h1 _ _ ih0 ih1 =>
    exact .and (hH _ hα) (hΓ.trans (hH _)) hm h0 h1 (ih0 hH) (ih1 hH)
  | orL hα hΓ hm h0 _ ih => exact .orL (hH _ hα) (hΓ.trans (hH _)) hm h0 (ih hH)
  | orR hα hΓ hm h1 h0 _ ih => exact .orR (hH _ hα) (hΓ.trans (hH _)) hm h1 h0 (ih hH)
  | all f hα hΓ hm hf _ ih => exact .all f (hH _ hα) (hΓ.trans (hH _)) hm hf (fun m => ih m hH)
  | exs m hα hΓ hm hn h0 _ ih => exact .exs m (hH _ hα) (hΓ.trans (hH _)) hm hn h0 (ih hH)
  | stage g hα hΓ hm hga hgα hgH h0 _ ih =>
    exact .stage g (hH _ hα) (hΓ.trans (hH _)) hm hga hgα (hH _ hgH) h0 (ih hH)
  | nstage f hα hΓ hm hf _ ih =>
    exact .nstage f (hH _ hα) (hΓ.trans (hH _)) hm hf
      (fun g hg => ih g hg (H' := ThetaWNoteD.adjoin H' {g.1}) (fun X => hH _))
  | fix hα hΓ hm hΩ h0 _ ih => exact .fix (hH _ hα) (hΓ.trans (hH _)) hm hΩ h0 (ih hH)
  | cut hα hΓ hr h0 _ _ ih0 ih1 =>
    exact .cut (hH _ hα) (hΓ.trans (hH _)) hr h0 (ih0 hH) (ih1 hH)

/-- **Exercise 5.7 (b)**: `H ⊢^α_ρ Γ` gives `H ⊢^{α'}_ρ Γ'` for `α ⪯ α'`, `Γ ⊆ Γ'` and
`{α'} ∪ k(Γ') ⊆ H(∅)`. Together with `mono_rank` this is the full exercise; it also covers the
reordering and the duplication of formulas. -/
theorem weaken (hH : ThetaWNoteD.IsOperator H) (d : IDnDerivable A ρ H α Γ) {α' : ThetaWNoteD}
    {Γ' : Sequent (LIinfN n)} (hα : α ≤ α') (hΓ : Γ ⊆ Γ') (hα' : α' ∈ H ∅)
    (hΓ' : paramsVal Γ' ⊆ H ∅) : IDnDerivable A ρ H α' Γ' := by
  induction d generalizing α' Γ' with
  | literal _ _ hφ hm => exact .literal hα' hΓ' hφ (hΓ hm)
  | verum _ _ hm => exact .verum hα' hΓ' (hΓ hm)
  | idX t _ _ h1 h2 => exact .idX t hα' hΓ' (hΓ h1) (hΓ h2)
  | and _ _ hm h0 h1 d0 d1 ih0 ih1 =>
    exact .and hα' hΓ' (hΓ hm) (lt_of_lt_of_le h0 hα) (lt_of_lt_of_le h1 hα)
      (ih0 hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsVal_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
      (ih1 hH le_rfl (List.cons_subset_cons _ hΓ) d1.height_mem
        (by rw [paramsVal_cons]; exact Set.union_subset d1.params_head_subset hΓ'))
  | orL _ _ hm h0 d0 ih =>
    exact .orL hα' hΓ' (hΓ hm) (lt_of_lt_of_le h0 hα)
      (ih hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsVal_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
  | orR _ _ hm h1 h0 d0 ih =>
    exact .orR hα' hΓ' (hΓ hm) (lt_of_lt_of_le h1 hα) (lt_of_lt_of_le h0 hα)
      (ih hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsVal_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
  | all f _ _ hm hf d0 ih =>
    exact .all f hα' hΓ' (hΓ hm) (fun m => lt_of_lt_of_le (hf m) hα) fun m =>
      ih m hH le_rfl (List.cons_subset_cons _ hΓ) (d0 m).height_mem
        (by rw [paramsVal_cons]; exact Set.union_subset (d0 m).params_head_subset hΓ')
  | exs m _ _ hm hn h0 d0 ih =>
    exact .exs m hα' hΓ' (hΓ hm) (lt_of_lt_of_le hn hα) (lt_of_lt_of_le h0 hα)
      (ih hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsVal_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
  | stage g _ _ hm hga hgα hgH h0 d0 ih =>
    exact .stage g hα' hΓ' (hΓ hm) hga (lt_of_lt_of_le hgα hα) hgH (lt_of_lt_of_le h0 hα)
      (ih hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsVal_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
  | nstage f _ _ hm hf d0 ih =>
    refine .nstage f hα' hΓ' (hΓ hm) (fun g hg => lt_of_lt_of_le (hf g hg) hα) fun g hg => ?_
    have hH' := hH.adjoin {g.1}
    exact ih g hg hH' le_rfl (List.cons_subset_cons _ hΓ) (d0 g hg).height_mem
      (by
        rw [paramsVal_cons]
        exact Set.union_subset (d0 g hg).params_head_subset
          (hΓ'.trans (hH.mono (Set.empty_subset _))))
  | fix _ _ hm hΩ h0 d0 ih =>
    exact .fix hα' hΓ' (hΓ hm) (le_trans hΩ hα) (lt_of_lt_of_le h0 hα)
      (ih hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsVal_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
  | cut _ _ hr h0 d0 d1 ih0 ih1 =>
    exact .cut hα' hΓ' hr (lt_of_lt_of_le h0 hα)
      (ih0 hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsVal_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
      (ih1 hH le_rfl (List.cons_subset_cons _ hΓ) d1.height_mem
        (by rw [paramsVal_cons]; exact Set.union_subset d1.params_head_subset hΓ'))

/-- Weakening of the sequent alone. -/
theorem weaken_seq (hH : ThetaWNoteD.IsOperator H) (d : IDnDerivable A ρ H α Γ)
    {Γ' : Sequent (LIinfN n)} (hΓ : Γ ⊆ Γ') (hΓ' : paramsVal Γ' ⊆ H ∅) :
    IDnDerivable A ρ H α Γ' :=
  d.weaken hH le_rfl hΓ d.height_mem hΓ'

/-- `H ⊢ Γ` gives `H[Z] ⊢ Γ` (Exercise 5.7 (a) with `H(X) ⊆ H(Z ∪ X)`). -/
theorem adjoin (hH : ThetaWNoteD.IsOperator H) (Z : Set ThetaWNoteD) (d : IDnDerivable A ρ H α Γ) :
    IDnDerivable A ρ (ThetaWNoteD.adjoin H Z) α Γ :=
  d.mono_op fun _ => hH.mono Set.subset_union_right

/-- **`H ⊢^α_ρ Γ` weakens to `H[k(Δ)] ⊢^α_ρ Γ, Δ`** (Freund, after Definition 5.6). -/
theorem weaken_adjoin (hH : ThetaWNoteD.IsOperator H) (d : IDnDerivable A ρ H α Γ)
    (Δ : Sequent (LIinfN n)) :
    IDnDerivable A ρ (ThetaWNoteD.adjoin H (paramsVal Δ)) α (Γ ++ Δ) := by
  have hH' := hH.adjoin (paramsVal Δ)
  have hsub : H ∅ ⊆ ThetaWNoteD.adjoin H (paramsVal Δ) ∅ := hH.mono (Set.empty_subset _)
  refine (d.adjoin hH (paramsVal Δ)).weaken_seq hH' (List.subset_append_left _ _) ?_
  rw [paramsVal_append]
  exact Set.union_subset (d.params_subset.trans hsub)
    (Set.subset_union_left.trans (hH.subset _))

end IDnDerivable

/-! ### Inversion (Exercise 7.1 (a))

For a conjunctive formula `ψ ≃ ⋀_{γ≺δ} ψ_γ`, `H ⊢^α_ρ Γ, ψ` gives `H ⊢^α_ρ Γ, ψ_γ` for every
`γ ≺ δ` with `γ ∈ H(∅)` (Freund, Exercise 7.1 (a)). The conjunctive formulas with premises are
`ψ₀ ∧ ψ₁`, `∀x ψ(x)` and `¬I_k^{≺δ} t`; none of them is the principal formula of a disjunctive
clause or of (Fix), whose principal formula `I_k^{≺Ω_{k+1}} t` is disjunctive. For `¬I_k^{≺δ} t`
the premise for `γ` carries `H[{γ}]`, which is `H` when `γ ∈ H(∅)` (Exercise 5.5 (c)).

The three cases share one induction (`inv_aux`): `InvShape A G ψ χ` says that `χ` is a component
of the conjunctive formula `ψ`, that `ψ` has no other shape, and, for `¬I_k^{≺δ} t`, that the
index of the component satisfies `G` (the index is not determined by the component when `A`
does not mention `I_k`). -/

/-- `χ` is a component `ψ_γ` of the conjunctive formula `ψ`, and `ψ` is not the principal
formula of any other clause; a stage index of the component satisfies `G`. -/
structure InvShape (A : Fin n → Semisentence (LXIn n) 1) (G : Stage n → Prop)
    (ψ χ : Proposition (LIinfN n)) : Prop where
  not_lit : ¬TrueLit ψ
  ne_verum : ψ ≠ ⊤
  ne_X : ∀ t : SyntacticTerm (LIinfN n), ψ ≠ XinfAt t
  ne_nX : ∀ t : SyntacticTerm (LIinfN n), ψ ≠ ∼(XinfAt t)
  ne_or : ∀ φ₀ φ₁ : Proposition (LIinfN n), ψ ≠ φ₀ ⋎ φ₁
  ne_exs : ∀ φ : Semiproposition (LIinfN n) 1, ψ ≠ ∃¹ φ
  ne_stage : ∀ (s : Stage n) (t : SyntacticTerm (LIinfN n)), ψ ≠ stageAt s t
  of_and : ∀ φ₀ φ₁ : Proposition (LIinfN n), ψ = φ₀ ⋏ φ₁ → χ = φ₀ ∨ χ = φ₁
  of_all : ∀ φ : Semiproposition (LIinfN n) 1, ψ = ∀¹ φ → ∃ m : ℕ, χ = φ/[numI m]
  of_nstage : ∀ (k : Fin n) (a : StageAt k.val) (t : SyntacticTerm (LIinfN n)),
    ψ = nstageAt (⟨k, a⟩ : Stage n) t →
    ∃ g : StageAt k.val, g.1 < a.1 ∧ χ = ∼(unfold (A k) k g t) ∧ G ⟨k, g⟩

namespace IDnDerivable

variable {A : Fin n → Semisentence (LXIn n) 1} {ρ : ThetaWNoteD}

/-- The statement of inversion for a derivation of `Δ`. -/
def InvClaim (A : Fin n → Semisentence (LXIn n) 1) (ρ : ThetaWNoteD) (G : Stage n → Prop)
    (ψ χ : Proposition (LIinfN n)) (H : Set ThetaWNoteD → Set ThetaWNoteD) (α : ThetaWNoteD)
    (Δ : Sequent (LIinfN n)) : Prop :=
  ThetaWNoteD.IsOperator H → (∀ s : Stage n, G s → s.val ∈ H ∅) →
    ∀ Γ : Sequent (LIinfN n), Δ ⊆ ψ :: Γ → paramsVal (χ :: Γ) ⊆ H ∅ →
      IDnDerivable A ρ H α (χ :: Γ)

theorem mem_inv {ψ χ θ : Proposition (LIinfN n)} {Δ Γ : Sequent (LIinfN n)} (hθ : θ ∈ Δ)
    (hΔ : Δ ⊆ ψ :: Γ) (hne : θ ≠ ψ) : θ ∈ χ :: Γ := by
  rcases List.mem_cons.mp (hΔ hθ) with h | h
  · exact absurd h hne
  · exact List.mem_cons_of_mem _ h

theorem inv_prem {G : Stage n → Prop} {ψ χ φ : Proposition (LIinfN n)}
    {H : Set ThetaWNoteD → Set ThetaWNoteD} {α₀ : ThetaWNoteD} {Δ Γ : Sequent (LIinfN n)}
    (hH : ThetaWNoteD.IsOperator H) (hγ : ∀ s : Stage n, G s → s.val ∈ H ∅)
    (d₀ : IDnDerivable A ρ H α₀ (φ :: Δ)) (ih₀ : InvClaim A ρ G ψ χ H α₀ (φ :: Δ))
    (hΔ : Δ ⊆ ψ :: Γ) (hP : paramsVal (χ :: Γ) ⊆ H ∅) :
    IDnDerivable A ρ H α₀ (φ :: χ :: Γ) := by
  have hφ : Stage.val '' params φ ⊆ H ∅ := d₀.params_head_subset
  rw [paramsVal_cons] at hP
  have h1 := ih₀ hH hγ (φ :: Γ)
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · rcases List.mem_cons.mp (hΔ hx) with h | h
        · exact h ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    (by
      rw [paramsVal_cons, paramsVal_cons]
      exact Set.union_subset (Set.subset_union_left.trans hP)
        (Set.union_subset hφ (Set.subset_union_right.trans hP)))
  refine h1.weaken_seq hH ?_ ?_
  · intro x hx
    simp only [List.mem_cons] at hx ⊢
    tauto
  · rw [paramsVal_cons, paramsVal_cons]
    exact Set.union_subset hφ hP

/-- The principal case: the component was derived, as the head of `χ :: χ :: Γ`, at a height
below `α`. -/
theorem inv_principal {χ : Proposition (LIinfN n)} {H : Set ThetaWNoteD → Set ThetaWNoteD}
    {α α₀ : ThetaWNoteD} {Γ : Sequent (LIinfN n)} (hH : ThetaWNoteD.IsOperator H) (hα : α ∈ H ∅)
    (h0 : α₀ < α) (d : IDnDerivable A ρ H α₀ (χ :: χ :: Γ)) (hP : paramsVal (χ :: Γ) ⊆ H ∅) :
    IDnDerivable A ρ H α (χ :: Γ) :=
  d.weaken hH (le_of_lt h0)
    (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hα hP

theorem inv_aux {G : Stage n → Prop} {ψ χ : Proposition (LIinfN n)} (hs : InvShape A G ψ χ)
    {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Δ : Sequent (LIinfN n)}
    (d : IDnDerivable A ρ H α Δ) : InvClaim A ρ G ψ χ H α Δ := by
  induction d with
  | literal hα _ hφ hm =>
    intro hH hγ Γ hΔ hP
    exact .literal hα hP hφ (mem_inv hm hΔ fun h => hs.not_lit (h ▸ hφ))
  | verum hα _ hm =>
    intro hH hγ Γ hΔ hP
    exact .verum hα hP (mem_inv hm hΔ fun h => hs.ne_verum h.symm)
  | idX t hα _ h1 h2 =>
    intro hH hγ Γ hΔ hP
    exact .idX t hα hP (mem_inv h1 hΔ fun h => hs.ne_X t h.symm)
      (mem_inv h2 hΔ fun h => hs.ne_nX t h.symm)
  | @and H α Δ φ₀ φ₁ α₀ α₁ hα _ hm h0 h1 d0 d1 ih0 ih1 =>
    intro hH hγ Γ hΔ hP
    have p0 := inv_prem hH hγ d0 ih0 hΔ hP
    have p1 := inv_prem hH hγ d1 ih1 hΔ hP
    by_cases he : φ₀ ⋏ φ₁ = ψ
    · rcases hs.of_and φ₀ φ₁ he.symm with rfl | rfl
      · exact inv_principal hH hα h0 p0 hP
      · exact inv_principal hH hα h1 p1 hP
    · exact .and hα hP (mem_inv hm hΔ he) h0 h1 p0 p1
  | orL hα _ hm h0 d0 ih0 =>
    intro hH hγ Γ hΔ hP
    exact .orL hα hP (mem_inv hm hΔ fun h => hs.ne_or _ _ h.symm) h0
      (inv_prem hH hγ d0 ih0 hΔ hP)
  | orR hα _ hm h1 h0 d0 ih0 =>
    intro hH hγ Γ hΔ hP
    exact .orR hα hP (mem_inv hm hΔ fun h => hs.ne_or _ _ h.symm) h1 h0
      (inv_prem hH hγ d0 ih0 hΔ hP)
  | @all H α Δ φ f hα _ hm hf d0 ih0 =>
    intro hH hγ Γ hΔ hP
    have p0 := fun m => inv_prem hH hγ (d0 m) (ih0 m) hΔ hP
    by_cases he : (∀¹ φ) = ψ
    · obtain ⟨m, rfl⟩ := hs.of_all φ he.symm
      exact inv_principal hH hα (hf m) (p0 m) hP
    · exact .all f hα hP (mem_inv hm hΔ he) hf p0
  | exs m hα _ hm hn h0 d0 ih0 =>
    intro hH hγ Γ hΔ hP
    exact .exs m hα hP (mem_inv hm hΔ fun h => hs.ne_exs _ h.symm) hn h0
      (inv_prem hH hγ d0 ih0 hΔ hP)
  | stage g hα _ hm hga hgα hgH h0 d0 ih0 =>
    intro hH hγ Γ hΔ hP
    exact .stage g hα hP (mem_inv hm hΔ fun h => hs.ne_stage _ _ h.symm) hga hgα hgH h0
      (inv_prem hH hγ d0 ih0 hΔ hP)
  | @nstage H α Δ k a t f hα _ hm hf d0 ih0 =>
    intro hH hγ Γ hΔ hP
    have p0 : ∀ g : StageAt k.val, g.1 < a.1 →
        IDnDerivable A ρ (ThetaWNoteD.adjoin H {g.1}) (f g)
          (∼(unfold (A k) k g t) :: χ :: Γ) := by
      intro g hg
      have hsub : H ∅ ⊆ ThetaWNoteD.adjoin H {g.1} ∅ := hH.mono (Set.empty_subset _)
      exact inv_prem (hH.adjoin {g.1}) (fun g' hg' => hsub (hγ g' hg'))
        (d0 g hg) (ih0 g hg) hΔ (hP.trans hsub)
    by_cases he : nstageAt (⟨k, a⟩ : Stage n) t = ψ
    · obtain ⟨g, hg, rfl, hG⟩ := hs.of_nstage k a t he.symm
      have e : ThetaWNoteD.adjoin H {g.1} = H :=
        ThetaWNoteD.adjoin_eq_self hH (Set.singleton_subset_iff.mpr (hγ ⟨k, g⟩ hG))
      have p := p0 g hg
      rw [e] at p
      exact inv_principal hH hα (hf g hg) p hP
    · exact .nstage f hα hP (mem_inv hm hΔ he) hf p0
  | fix hα _ hm hΩ h0 d0 ih0 =>
    intro hH hγ Γ hΔ hP
    exact .fix hα hP (mem_inv hm hΔ fun h => hs.ne_stage _ _ h.symm) hΩ h0
      (inv_prem hH hγ d0 ih0 hΔ hP)
  | cut hα _ hr h0 d0 d1 ih0 ih1 =>
    intro hH hγ Γ hΔ hP
    exact .cut hα hP hr h0 (inv_prem hH hγ d0 ih0 hΔ hP) (inv_prem hH hγ d1 ih1 hΔ hP)

variable {H : Set ThetaWNoteD → Set ThetaWNoteD} {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)}

theorem inv_of_shape {G : Stage n → Prop} {ψ χ : Proposition (LIinfN n)} (hs : InvShape A G ψ χ)
    (hH : ThetaWNoteD.IsOperator H) (hγ : ∀ s : Stage n, G s → s.val ∈ H ∅)
    (hχ : Stage.val '' params χ ⊆ H ∅) (d : IDnDerivable A ρ H α (ψ :: Γ)) :
    IDnDerivable A ρ H α (χ :: Γ) := by
  refine inv_aux hs d hH hγ Γ (List.Subset.refl _) ?_
  have h := d.params_subset
  rw [paramsVal_cons] at h ⊢
  exact Set.union_subset hχ (Set.subset_union_right.trans h)

/-- **Exercise 7.1 (a) for `∧`**, left component. -/
theorem inv_and_left (hH : ThetaWNoteD.IsOperator H) {φ₀ φ₁ : Proposition (LIinfN n)}
    (d : IDnDerivable A ρ H α (φ₀ ⋏ φ₁ :: Γ)) : IDnDerivable A ρ H α (φ₀ :: Γ) :=
  inv_of_shape (G := fun _ => False) (ψ := φ₀ ⋏ φ₁)
    ⟨(fun h => by obtain ⟨⟨j, r, v, (h | h), -⟩, -⟩ := h <;> exact nomatch h),
      (fun h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ h => by cases h; exact Or.inl rfl), (fun _ h => nomatch h),
      (fun _ _ _ h => nomatch h)⟩
    hH (fun _ h => h.elim)
    (by
      have h := d.params_head_subset
      rw [params_and] at h
      exact fun x ⟨s, hs, hx⟩ => h ⟨s, Or.inl hs, hx⟩)
    d

/-- **Exercise 7.1 (a) for `∧`**, right component. -/
theorem inv_and_right (hH : ThetaWNoteD.IsOperator H) {φ₀ φ₁ : Proposition (LIinfN n)}
    (d : IDnDerivable A ρ H α (φ₀ ⋏ φ₁ :: Γ)) : IDnDerivable A ρ H α (φ₁ :: Γ) :=
  inv_of_shape (G := fun _ => False) (ψ := φ₀ ⋏ φ₁)
    ⟨(fun h => by obtain ⟨⟨j, r, v, (h | h), -⟩, -⟩ := h <;> exact nomatch h),
      (fun h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ h => by cases h; exact Or.inr rfl), (fun _ h => nomatch h),
      (fun _ _ _ h => nomatch h)⟩
    hH (fun _ h => h.elim)
    (by
      have h := d.params_head_subset
      rw [params_and] at h
      exact fun x ⟨s, hs, hx⟩ => h ⟨s, Or.inr hs, hx⟩)
    d

/-- **Exercise 7.1 (a) for `∀`**: `H ⊢^α_ρ Γ, ∀x φ(x)` gives `H ⊢^α_ρ Γ, φ(m̄)`. -/
theorem inv_all (hH : ThetaWNoteD.IsOperator H) {φ : Semiproposition (LIinfN n) 1} (m : ℕ)
    (d : IDnDerivable A ρ H α ((∀¹ φ) :: Γ)) : IDnDerivable A ρ H α (φ/[numI m] :: Γ) :=
  inv_of_shape (G := fun _ => False) (ψ := ∀¹ φ)
    ⟨(fun h => by obtain ⟨⟨j, r, v, (h | h), -⟩, -⟩ := h <;> exact nomatch h),
      (fun h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => by cases h; exact ⟨m, rfl⟩),
      (fun _ _ _ h => nomatch h)⟩
    hH (fun _ h => h.elim)
    (by
      have h := d.params_head_subset
      rw [params_all] at h
      rw [params_subst]
      exact h)
    d

/-- **Exercise 7.1 (a) for `¬I_k^{≺δ} t`**: `H ⊢^α_ρ Γ, ¬I_k^{≺δ} t` gives
`H ⊢^α_ρ Γ, ¬A_k(t, I_k^{≺γ})` for `γ ≺ δ` with `γ ∈ H(∅)`. This needs `H` **nice**: unlike the
single-level case, `A_k`'s unfolding may mention every other level's own `I_j`, so `k(¬A_k(t,
I_k^{≺γ}))` also contains those levels' tops (`params_unfold`), automatically in `H(∅)` for a
nice `H` (`ThetaWNoteD.NiceS.Omega_mem`). -/
theorem inv_nstage (hH : ThetaWNoteD.NiceS H) {k : Fin n} {a g : StageAt k.val}
    {t : SyntacticTerm (LIinfN n)} (hg : g.1 < a.1) (hgH : g.1 ∈ H ∅)
    (d : IDnDerivable A ρ H α (nstageAt (⟨k, a⟩ : Stage n) t :: Γ)) :
    IDnDerivable A ρ H α (∼(unfold (A k) k g t) :: Γ) :=
  inv_of_shape (G := fun s => s = (⟨k, g⟩ : Stage n)) (ψ := nstageAt (⟨k, a⟩ : Stage n) t)
    ⟨(fun h => by
        obtain ⟨⟨j, r, v, (h | h), -⟩, -⟩ := h
        · exact nomatch h
        · have := congrArg negHeadStage h
          exact nomatch this),
      (fun h => nomatch h), (fun _ h => nomatch h),
      (fun _ h => by have := congrArg negHeadStage h; exact nomatch this),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h),
      fun k' a' t' h => by
        obtain ⟨hka, rfl⟩ := nstageAt_inj h
        have hkk' : k = k' := congrArg Stage.lvl hka
        subst hkk'
        have haa' : a = a' := Subtype.ext (congrArg Stage.val hka)
        subst haa'
        exact ⟨g, hg, rfl, rfl⟩⟩
    hH.1 (fun s h => h ▸ hgH)
    (by
      rw [params_neg]
      rintro x ⟨s, hs, rfl⟩
      rcases params_unfold (A k) k g t hs with h | ⟨j, hj⟩
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact hgH
      · rw [hj, Stage.val_top]
        exact hH.Omega_mem j.val)
    d

end IDnDerivable

/-! ### Smoke test (design §4.3): `n = 2`

`I_0`'s closure form is `⊤` (so `I_0` holds of everything trivially); `I_1`'s closure form is
`I_1(x) ↔ I_0(x)`, a positive reference to the lower level. With the trivial operator
`Htriv X := Set.univ` (nice, so every control condition holds for free), `smoke_I0_zero` derives
the trivial level-0 fact `⊢ I_0 0̄`; `smoke_I1_stage_zero` then applies level `1`'s closure to it
through the `stage` rule (**not** `fix`) to get `⊢ I_1^{≺a} 0̄}` at a finite stage `a`;
`smoke_I1_omega2` applies the same level-0 fact through the `fix` rule at level `1`, i.e.
**the Ω₂-rule**, to get the full `⊢ I_1 0̄`. -/

section SmokeTest

/-- The trivial operator: every control condition holds for free. It is nice (`Ahull a ⊆ univ`
always holds), so it is a legitimate operator for every clause of the calculus. -/
def Htriv : Set ThetaWNoteD → Set ThetaWNoteD := fun _ => Set.univ

theorem Htriv_isOperator : ThetaWNoteD.IsOperator Htriv :=
  ⟨fun _ => Set.subset_univ _, fun _ _ _ => Set.subset_univ _⟩

theorem Htriv_niceS : ThetaWNoteD.NiceS Htriv :=
  ⟨Htriv_isOperator, fun _ _ => ⟨fun _ => Set.subset_univ _, fun _ => Set.mem_univ _⟩⟩

/-- `n = 2`. Level `0`: `A_0(x) := ⊤`. Level `1`: `A_1(x) := I_0(x)`. -/
def smokeA (k : Fin 2) : Semisentence (LXIn 2) 1 :=
  if k = 0 then ⊤ else Iat (0 : Fin 2) (#0 : Semiterm (LXIn 2) Empty 1)

@[simp] theorem smokeA_zero : smokeA 0 = (⊤ : Semisentence (LXIn 2) 1) := rfl

@[simp] theorem smokeA_one : smokeA 1 = Iat (0 : Fin 2) (#0 : Semiterm (LXIn 2) Empty 1) := rfl

theorem unfold_smokeA_zero_top {ξ : Type*} {m : ℕ} (t : Semiterm (LIinfN 2) ξ m) :
    unfold (smokeA 0) 0 (StageAt.top (0 : Fin 2).val) t = ⊤ := by
  simp [unfold, formAt, smokeA]

/-- `A_1`'s unfolding at any level-`1` stage is `I_0`'s own full predicate, since `A_1` does not
mention `I_1` at all: `stageHom 1 a` agrees with `embedHom` on every atom of a level other than
`1`. -/
theorem unfold_smokeA_one {ξ : Type*} {m : ℕ} (a : StageAt (1 : Fin 2).val)
    (t : Semiterm (LIinfN 2) ξ m) :
    unfold (smokeA 1) 1 a t = IOmegaAt (0 : Fin 2) t := by
  have hne : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  have hform : formAt (smokeA 1) (1 : Fin 2) a =
      stageAt (Stage.top (0 : Fin 2)) (#0 : Semiterm (LIinfN 2) Empty 1) := by
    show Semiformula.rel (stageRel (1 : Fin 2) a (Sum.inr (IXRelN.I 0)))
        (Semiterm.lMap (stageHom (1 : Fin 2) a) ∘ ![(#0 : Semiterm (LXIn 2) Empty 1)]) = _
    rw [stageRel_I, dif_neg hne]
    congr 1
    funext i
    obtain rfl := Subsingleton.elim i (0 : Fin 1)
    rfl
  rw [unfold, hform, IOmegaAt_eq, stageAt]
  unfold Rewriting.emb Rewriting.subst
  rw [← TransitiveRewriting.comp_app]
  refine (Semiformula.rew_rel _ _ _).trans ?_
  simp only [Rew.comp_app, stageAt]
  congr 1
  funext i
  obtain rfl := Subsingleton.elim i (0 : Fin 1)
  rfl

/-- **The trivial level-0 fact `⊢ I_0 0̄`.** -/
theorem smoke_I0_zero :
    IDnDerivable smokeA ThetaWNoteD.zero Htriv (ThetaWNoteD.Omega (0 : Fin 2).val)
      (IOmegaAt (0 : Fin 2) (numI 0) :: []) := by
  have hpremise : IDnDerivable smokeA ThetaWNoteD.zero Htriv ThetaWNoteD.zero
      (unfold (smokeA 0) 0 (StageAt.top (0 : Fin 2).val) (numI 0) ::
        (IOmegaAt (0 : Fin 2) (numI 0) :: [])) := by
    rw [unfold_smokeA_zero_top]
    exact .verum (Set.mem_univ _) (Set.subset_univ _) List.mem_cons_self
  exact .fix (Set.mem_univ _) (Set.subset_univ _) List.mem_cons_self (le_refl _)
    (ThetaWNoteD.zero_lt_Omega _) hpremise

/-- **Level `1`'s closure applied to the trivial level-0 fact, via the `stage` rule**: a finite
stage of `I_1` at `0̄`, not going through `fix`. The witness `g := 0` unfolds (independently of
`g`, since `A_1` does not mention `I_1`) to `I_0`'s own full predicate, which
`smoke_I0_zero` already derives; weakening moves it into the wider sequent. -/
theorem smoke_I1_stage_zero :
    IDnDerivable smokeA ThetaWNoteD.zero Htriv
      (ThetaWNoteD.succ (ThetaWNoteD.Omega (0 : Fin 2).val))
      (stageAt (⟨(1 : Fin 2), StageAt.ofLt (1 : Fin 2).val (ThetaWNoteD.ofNat 1)
        (by theta_order)⟩ : Stage 2) (numI 0) :: []) := by
  have hgtop : (ThetaWNoteD.ofNat 0 : ThetaWNoteD) < ThetaWNoteD.Omega (1 : Fin 2).val := by
    theta_order
  have hsub : ([IOmegaAt (0 : Fin 2) (numI 0)] : Sequent (LIinfN 2)) ⊆
      [IOmegaAt (0 : Fin 2) (numI 0),
        stageAt (⟨(1 : Fin 2), StageAt.ofLt (1 : Fin 2).val (ThetaWNoteD.ofNat 1)
          (by theta_order)⟩ : Stage 2) (numI 0)] := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self
    · nomatch hx
  have hpremise : IDnDerivable smokeA ThetaWNoteD.zero Htriv (ThetaWNoteD.Omega (0 : Fin 2).val)
      (unfold (smokeA 1) 1 (StageAt.ofLt (1 : Fin 2).val (ThetaWNoteD.ofNat 0) hgtop) (numI 0) ::
        (stageAt (⟨(1 : Fin 2), StageAt.ofLt (1 : Fin 2).val (ThetaWNoteD.ofNat 1)
          (by theta_order)⟩ : Stage 2) (numI 0) :: [])) := by
    rw [unfold_smokeA_one]
    exact smoke_I0_zero.weaken_seq Htriv_isOperator hsub (Set.subset_univ _)
  refine .stage (StageAt.ofLt (1 : Fin 2).val (ThetaWNoteD.ofNat 0) hgtop) (Set.mem_univ _)
    (Set.subset_univ _) List.mem_cons_self (by theta_order) ?_ (Set.mem_univ _)
    (by theta_order) hpremise
  exact lt_trans (by theta_order : (ThetaWNoteD.ofNat 0 : ThetaWNoteD) <
    ThetaWNoteD.Omega (0 : Fin 2).val) (ThetaWNoteD.lt_succ _)

/-- **The full `⊢ I_1 0̄`, via `fix` at level `1` — the Ω₂-rule.** -/
theorem smoke_I1_omega2 :
    IDnDerivable smokeA ThetaWNoteD.zero Htriv (ThetaWNoteD.Omega (1 : Fin 2).val)
      (IOmegaAt (1 : Fin 2) (numI 0) :: []) := by
  have hsub : ([IOmegaAt (0 : Fin 2) (numI 0)] : Sequent (LIinfN 2)) ⊆
      [IOmegaAt (0 : Fin 2) (numI 0), IOmegaAt (1 : Fin 2) (numI 0)] := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self
    · nomatch hx
  have hpremise : IDnDerivable smokeA ThetaWNoteD.zero Htriv (ThetaWNoteD.Omega (0 : Fin 2).val)
      (unfold (smokeA 1) 1 (StageAt.top (1 : Fin 2).val) (numI 0) ::
        (IOmegaAt (1 : Fin 2) (numI 0) :: [])) := by
    rw [unfold_smokeA_one]
    exact smoke_I0_zero.weaken_seq Htriv_isOperator hsub (Set.subset_univ _)
  exact .fix (Set.mem_univ _) (Set.subset_univ _) List.mem_cons_self (le_refl _)
    (by theta_order) hpremise

end SmokeTest

end IDn

end OrdinalAnalysis
