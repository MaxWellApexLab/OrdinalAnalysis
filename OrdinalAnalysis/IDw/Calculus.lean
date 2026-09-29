import OrdinalAnalysis.IDw.CalculusAux
/-
  The operator-controlled infinitary calculus `ID_ω^∞`, for the uniform theory `IDw A` with
  stage predicates `I_k^{≺α}`, `k : ℕ`, and the binary level atoms `Jlev ℓ`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §5 (as ported by `ID1/Calculus.lean`). After Buchholz, *A simplified
  version of local predicativity* (1992), §4 (several simultaneous predicates).

  **The relation.**  `IDwDerivable A ρ H α Γ` is the multi-level form of `ID1.IDerivable`: one
  operator family `A : Semisentence LForm 2` (`A k` is the defining form of level
  `k`; it may mention `X` and any `I_j`, per level, exactly as `IDw/Theory.lean`'s `ID` axioms
  do), one *level-free* operator `H` (Freund's operators are already level-free; the multi-level
  hull `Ordinal.ThetaW.HullSingle`/`HullDom` gives `ThetaVNoteD.HopS`/`NiceS`/`HullHypS`/
  `HullHypGe` as the level-free operator this calculus's side conditions are phrased against,
  **not** the per-level `Hop k`/
  `Nice k` of `Ordinal/ThetaW/Hull.lean`), and a single height/rank pair `α`, `ρ : ThetaVNoteD`
  shared by every level (a sequent can mix stage atoms of any level).

  The clauses are `IDn.IDnDerivable`'s twelve (`ID1.IDerivable`'s, with levels), plus **two new
  evaluation rules for the binary atoms** (design `idomega_design.md` §3.2):

      (jlev)   Jlev ℓ (s,t) ∈ Γ, s,t closed, val s < ℓ, α₀ < α;  Γ, I_{val s} t at α₀  ⇒  Γ at α
      (njlev)  ¬Jlev ℓ (s,t) ∈ Γ, s,t closed; if val s < ℓ then Γ, ¬I_{val s} t at α₀ < α
                                                                                  ⇒  Γ at α

  (`njlev` is a conjunction with at most one conjunct: an empty `⋀` when `val s ≥ ℓ`, like
  `literal`; `val s` is the standard value `termVal s` of the closed term `s`, so `s` need not be a
  numeral.)  The twelve are unchanged except: (i) the stage clauses `stage`/`nstage`/
  `fix` each carry an explicit level `k : ℕ`, their local stage variables have type
  `IDw.StageAt k` (**not** the packaged `IDw.Stage`, which only appears wrapped as
  `⟨k, ·⟩` where an actual `LIinfW`-atom or its parameter is formed — this is the one
  systematic fix the mechanical `id1_to_idn.py` rewrite cannot make on its own, see
  `tools/README_id1_to_idn.md`'s measured residue for `Boundedness.lean`); (ii) the unfolding
  `unfold A g t` of `ID1` becomes `unfoldW A k g t`; (iii) the control condition
  `paramsList Γ ⊆ H ∅` becomes `IDw.paramsVal Γ ⊆ H ∅` (`IDw/CalculusAux.lean`), since
  `paramsList` returns a set of `Stage` (level and bound together) but the level-free operator
  acts on sets of bare `ThetaVNoteD` values.

  Every other deviation from `ID1.IDerivable` noted there (lists instead of finite sets, the
  `X`-clause `idX`, formulas with free variables, the true literals of arithmetic) carries over
  unchanged; see `IDw/CalculusAux.lean`'s docstring for the multi-level statement of those
  pieces.

  Contents.

    `IDwDerivable`                                   the calculus, with levels
    `IDwDerivable.control`, `mono_rank`, `mono_height`, `weaken`   Exercise 5.7 (b)
    `IDwDerivable.mono_op`                           Exercise 5.7 (a)
    `IDwDerivable.adjoin`, `weaken_adjoin`            `H ⊢ Γ` gives `H[k(Δ)] ⊢ Γ, Δ`
    `IDwDerivable.inv_and_left`, `inv_and_right`,
    `IDwDerivable.inv_all`, `inv_nstage`,
    `IDwDerivable.inv_njlev`                          Exercise 7.1 (a), inversion
  (the smoke tests live in `IDw/CalculusSmoke.lean`)
-/

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder


/-! ### The calculus -/

/-- **The multi-level operator-controlled calculus**: `IDwDerivable A ρ H α Γ` is
`H ⊢^α_ρ Γ` for the uniform form `A : Semisentence LForm 2`. Every clause carries the initial
condition `α ∈ H(∅)` and `k(Γ) ⊆ H(∅)` (read through `paramsVal`). -/
inductive IDwDerivable (A : Semisentence LForm 2) (ρ : ThetaVNoteD) :
    (Set ThetaVNoteD → Set ThetaVNoteD) → ThetaVNoteD → Sequent LIinfW → Prop
  /-- (V) for a true literal of arithmetic, the empty conjunction. -/
  | literal {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent LIinfW}
      {φ : Proposition LIinfW} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → TrueLit φ → φ ∈ Γ → IDwDerivable A ρ H α Γ
  /-- (V) for `⊤`, the empty conjunction. -/
  | verum {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent LIinfW} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → ⊤ ∈ Γ → IDwDerivable A ρ H α Γ
  /-- The identity axiom of the free predicate `X`. -/
  | idX {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent LIinfW}
      (t : SyntacticTerm LIinfW) :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → XinfAt t ∈ Γ → ∼(XinfAt t) ∈ Γ → IDwDerivable A ρ H α Γ
  /-- (V) for `ψ₀ ∧ ψ₁ ≃ ⋀_{i≺2} ψ_i`. -/
  | and {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent LIinfW}
      {φ ψ : Proposition LIinfW} {α₀ α₁ : ThetaVNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → φ ⋏ ψ ∈ Γ → α₀ < α → α₁ < α →
      IDwDerivable A ρ H α₀ (φ :: Γ) → IDwDerivable A ρ H α₁ (ψ :: Γ) → IDwDerivable A ρ H α Γ
  /-- (W) for `ψ₀ ∨ ψ₁ ≃ ⋁_{i≺2} ψ_i`, index `0`. -/
  | orL {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent LIinfW}
      {φ ψ : Proposition LIinfW} {α₀ : ThetaVNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → φ ⋎ ψ ∈ Γ → α₀ < α →
      IDwDerivable A ρ H α₀ (φ :: Γ) → IDwDerivable A ρ H α Γ
  /-- (W) for `ψ₀ ∨ ψ₁ ≃ ⋁_{i≺2} ψ_i`, index `1` (so `1 ≺ α`). -/
  | orR {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent LIinfW}
      {φ ψ : Proposition LIinfW} {α₀ : ThetaVNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → φ ⋎ ψ ∈ Γ → ThetaVNoteD.one < α → α₀ < α →
      IDwDerivable A ρ H α₀ (ψ :: Γ) → IDwDerivable A ρ H α Γ
  /-- (V) for `∀x ψ(x) ≃ ⋀_{m≺ω} ψ(m̄)`: the ω-rule. -/
  | all {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent LIinfW}
      {φ : Semiproposition LIinfW 1} (f : ℕ → ThetaVNoteD) :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → (∀¹ φ) ∈ Γ → (∀ m, f m < α) →
      (∀ m, IDwDerivable A ρ H (f m) (φ/[numI m] :: Γ)) → IDwDerivable A ρ H α Γ
  /-- (W) for `∃x ψ(x) ≃ ⋁_{m≺ω} ψ(m̄)`, with the witness `m ≺ α`. -/
  | exs {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent LIinfW}
      {φ : Semiproposition LIinfW 1} (m : ℕ) {α₀ : ThetaVNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → (∃¹ φ) ∈ Γ → ThetaVNoteD.ofNat m < α → α₀ < α →
      IDwDerivable A ρ H α₀ (φ/[numI m] :: Γ) → IDwDerivable A ρ H α Γ
  /-- (W) for `I_k^{≺δ} t ≃ ⋁_{γ≺δ} A(k̄, t; I_k^{≺γ}, Jlev k)`, at level `k`, with `γ ≺ α`
  and `γ ∈ H(∅)`. -/
  | stage {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent LIinfW}
      {k : ℕ} {a : StageAt k} {t : SyntacticTerm LIinfW} (g : StageAt k)
      {α₀ : ThetaVNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → stageAt (⟨k, a⟩ : Stage) t ∈ Γ → g.1 < a.1 → g.1 < α →
      g.1 ∈ H ∅ → α₀ < α → IDwDerivable A ρ H α₀ (unfoldW A k g t :: Γ) →
      IDwDerivable A ρ H α Γ
  /-- (V) for `¬I_k^{≺δ} t ≃ ⋀_{γ≺δ} ¬A(k̄, t; I_k^{≺γ}, Jlev k)`, at level `k`, the premise for
  `γ` with `H[{γ}]`. -/
  | nstage {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent LIinfW}
      {k : ℕ} {a : StageAt k} {t : SyntacticTerm LIinfW}
      (f : StageAt k → ThetaVNoteD) :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → nstageAt (⟨k, a⟩ : Stage) t ∈ Γ →
      (∀ g : StageAt k, g.1 < a.1 → f g < α) →
      (∀ g : StageAt k, g.1 < a.1 →
        IDwDerivable A ρ (ThetaVNoteD.adjoin H {g.1}) (f g) (∼(unfoldW A k g t) :: Γ)) →
      IDwDerivable A ρ H α Γ
  /-- (Fix) at level `k`: `Ω_{k+1} ⪯ α`, `I_k t = I_k^{≺Ω_{k+1}} t ∈ Γ`, premise
  `Γ, A(k̄, t; I_k^{≺Ω_{k+1}}, Jlev k)`. -/
  | fix {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent LIinfW}
      {k : ℕ} {t : SyntacticTerm LIinfW} {α₀ : ThetaVNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → IOmegaAt k t ∈ Γ → ThetaVNoteD.Omega k ≤ α → α₀ < α →
      IDwDerivable A ρ H α₀ (unfoldW A k (StageAt.top k) t :: Γ) →
      IDwDerivable A ρ H α Γ
  /-- **(jlev)** (W) for `Jlev ℓ (s,t)`, a disjunction over the levels `j < ℓ`: for closed `s`,
  `t` with `val s < ℓ` (the standard value `termVal s`), the one relevant disjunct
  `I_{val s} t`, at `α₀ ≺ α`. -/
  | jlev {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent LIinfW}
      {ℓ : WithTop ℕ} {s t : SyntacticTerm LIinfW} {α₀ : ThetaVNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → jlevAt ℓ s t ∈ Γ → s.freeVariables = ∅ →
      t.freeVariables = ∅ → ((termVal s : ℕ) : WithTop ℕ) < ℓ → α₀ < α →
      IDwDerivable A ρ H α₀ (IOmegaAt (termVal s) t :: Γ) → IDwDerivable A ρ H α Γ
  /-- **(njlev)** (V) for `¬Jlev ℓ (s,t)`: a conjunction with at most one conjunct. For closed
  `s`, `t`: if `val s < ℓ` the single premise `Γ, ¬I_{val s} t` at `α₀ ≺ α`; if `val s ≥ ℓ` the
  conjunction is empty and there is no premise (like `literal`). -/
  | njlev {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent LIinfW}
      {ℓ : WithTop ℕ} {s t : SyntacticTerm LIinfW} {α₀ : ThetaVNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → njlevAt ℓ s t ∈ Γ → s.freeVariables = ∅ →
      t.freeVariables = ∅ → (((termVal s : ℕ) : WithTop ℕ) < ℓ → α₀ < α) →
      (((termVal s : ℕ) : WithTop ℕ) < ℓ →
        IDwDerivable A ρ H α₀ (∼(IOmegaAt (termVal s) t) :: Γ)) →
      IDwDerivable A ρ H α Γ
  /-- (Cut): a cut formula of rank `≺ ρ`, both premises of the same height. -/
  | cut {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent LIinfW}
      {ψ : Proposition LIinfW} {α₀ : ThetaVNoteD} :
      α ∈ H ∅ → paramsVal Γ ⊆ H ∅ → rk ψ < ρ → α₀ < α →
      IDwDerivable A ρ H α₀ (ψ :: Γ) → IDwDerivable A ρ H α₀ (∼ψ :: Γ) →
      IDwDerivable A ρ H α Γ

namespace IDwDerivable

variable {A : Semisentence LForm 2} {ρ : ThetaVNoteD}
  {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent (LIinfW)}

/-- **The initial condition**: `{α} ∪ k(Γ) ⊆ H(∅)`. -/
theorem control (d : IDwDerivable A ρ H α Γ) : α ∈ H ∅ ∧ paramsVal Γ ⊆ H ∅ := by
  cases d <;> exact ⟨by assumption, by assumption⟩

theorem height_mem (d : IDwDerivable A ρ H α Γ) : α ∈ H ∅ := d.control.1

theorem params_subset (d : IDwDerivable A ρ H α Γ) : paramsVal Γ ⊆ H ∅ := d.control.2

/-- The head formula of a derivable sequent has its parameters' values in `H(∅)`. -/
theorem params_head_subset {φ : Proposition (LIinfW)} (d : IDwDerivable A ρ H α (φ :: Γ)) :
    Stage.val '' params φ ⊆ H ∅ :=
  (params_val_subset_paramsVal List.mem_cons_self).trans d.params_subset

/-- **Exercise 5.7 (b), cut rank**: `ρ ⪯ ρ'` gives `H ⊢^α_{ρ'} Γ`. -/
theorem mono_rank {ρ' : ThetaVNoteD} (hρ : ρ ≤ ρ') (d : IDwDerivable A ρ H α Γ) :
    IDwDerivable A ρ' H α Γ := by
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
  | jlev hα hΓ hm hs ht hl h0 _ ih => exact .jlev hα hΓ hm hs ht hl h0 ih
  | njlev hα hΓ hm hs ht h0 _ ih => exact .njlev hα hΓ hm hs ht h0 ih
  | cut hα hΓ hr h0 _ _ ih0 ih1 => exact .cut hα hΓ (lt_of_lt_of_le hr hρ) h0 ih0 ih1

/-- **Exercise 5.7 (b), height**: `α ⪯ α'` and `α' ∈ H(∅)` give `H ⊢^{α'}_ρ Γ`. Only the last
inference changes. -/
theorem mono_height {α' : ThetaVNoteD} (hα : α ≤ α') (hα' : α' ∈ H ∅)
    (d : IDwDerivable A ρ H α Γ) : IDwDerivable A ρ H α' Γ := by
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
  | jlev _ hΓ hm hs ht hl h0 d0 =>
    exact .jlev hα' hΓ hm hs ht hl (lt_of_lt_of_le h0 hα) d0
  | njlev _ hΓ hm hs ht h0 d0 =>
    exact .njlev hα' hΓ hm hs ht (fun h => lt_of_lt_of_le (h0 h) hα) d0
  | cut _ hΓ hr h0 d0 d1 => exact .cut hα' hΓ hr (lt_of_lt_of_le h0 hα) d0 d1

/-- **Exercise 5.7 (a)**: `H(X) ⊆ H'(X)` for all `X` gives `H' ⊢^α_ρ Γ`. -/
theorem mono_op {H' : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ∀ X, H X ⊆ H' X)
    (d : IDwDerivable A ρ H α Γ) : IDwDerivable A ρ H' α Γ := by
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
      (fun g hg => ih g hg (H' := ThetaVNoteD.adjoin H' {g.1}) (fun X => hH _))
  | fix hα hΓ hm hΩ h0 _ ih => exact .fix (hH _ hα) (hΓ.trans (hH _)) hm hΩ h0 (ih hH)
  | jlev hα hΓ hm hs ht hl h0 _ ih =>
    exact .jlev (hH _ hα) (hΓ.trans (hH _)) hm hs ht hl h0 (ih hH)
  | njlev hα hΓ hm hs ht h0 _ ih =>
    exact .njlev (hH _ hα) (hΓ.trans (hH _)) hm hs ht h0 (fun h => ih h hH)
  | cut hα hΓ hr h0 _ _ ih0 ih1 =>
    exact .cut (hH _ hα) (hΓ.trans (hH _)) hr h0 (ih0 hH) (ih1 hH)

/-- **Exercise 5.7 (b)**: `H ⊢^α_ρ Γ` gives `H ⊢^{α'}_ρ Γ'` for `α ⪯ α'`, `Γ ⊆ Γ'` and
`{α'} ∪ k(Γ') ⊆ H(∅)`. Together with `mono_rank` this is the full exercise; it also covers the
reordering and the duplication of formulas. -/
theorem weaken (hH : ThetaVNoteD.IsOperator H) (d : IDwDerivable A ρ H α Γ) {α' : ThetaVNoteD}
    {Γ' : Sequent (LIinfW)} (hα : α ≤ α') (hΓ : Γ ⊆ Γ') (hα' : α' ∈ H ∅)
    (hΓ' : paramsVal Γ' ⊆ H ∅) : IDwDerivable A ρ H α' Γ' := by
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
  | jlev _ _ hm hs ht hl h0 d0 ih =>
    exact .jlev hα' hΓ' (hΓ hm) hs ht hl (lt_of_lt_of_le h0 hα)
      (ih hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsVal_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
  | njlev _ _ hm hs ht h0 d0 ih =>
    exact .njlev hα' hΓ' (hΓ hm) hs ht (fun h => lt_of_lt_of_le (h0 h) hα) fun h =>
      ih h hH le_rfl (List.cons_subset_cons _ hΓ) (d0 h).height_mem
        (by rw [paramsVal_cons]; exact Set.union_subset (d0 h).params_head_subset hΓ')
  | cut _ _ hr h0 d0 d1 ih0 ih1 =>
    exact .cut hα' hΓ' hr (lt_of_lt_of_le h0 hα)
      (ih0 hH le_rfl (List.cons_subset_cons _ hΓ) d0.height_mem
        (by rw [paramsVal_cons]; exact Set.union_subset d0.params_head_subset hΓ'))
      (ih1 hH le_rfl (List.cons_subset_cons _ hΓ) d1.height_mem
        (by rw [paramsVal_cons]; exact Set.union_subset d1.params_head_subset hΓ'))

/-- Weakening of the sequent alone. -/
theorem weaken_seq (hH : ThetaVNoteD.IsOperator H) (d : IDwDerivable A ρ H α Γ)
    {Γ' : Sequent (LIinfW)} (hΓ : Γ ⊆ Γ') (hΓ' : paramsVal Γ' ⊆ H ∅) :
    IDwDerivable A ρ H α Γ' :=
  d.weaken hH le_rfl hΓ d.height_mem hΓ'

/-- `H ⊢ Γ` gives `H[Z] ⊢ Γ` (Exercise 5.7 (a) with `H(X) ⊆ H(Z ∪ X)`). -/
theorem adjoin (hH : ThetaVNoteD.IsOperator H) (Z : Set ThetaVNoteD) (d : IDwDerivable A ρ H α Γ) :
    IDwDerivable A ρ (ThetaVNoteD.adjoin H Z) α Γ :=
  d.mono_op fun _ => hH.mono Set.subset_union_right

/-- **`H ⊢^α_ρ Γ` weakens to `H[k(Δ)] ⊢^α_ρ Γ, Δ`** (Freund, after Definition 5.6). -/
theorem weaken_adjoin (hH : ThetaVNoteD.IsOperator H) (d : IDwDerivable A ρ H α Γ)
    (Δ : Sequent (LIinfW)) :
    IDwDerivable A ρ (ThetaVNoteD.adjoin H (paramsVal Δ)) α (Γ ++ Δ) := by
  have hH' := hH.adjoin (paramsVal Δ)
  have hsub : H ∅ ⊆ ThetaVNoteD.adjoin H (paramsVal Δ) ∅ := hH.mono (Set.empty_subset _)
  refine (d.adjoin hH (paramsVal Δ)).weaken_seq hH' (List.subset_append_left _ _) ?_
  rw [paramsVal_append]
  exact Set.union_subset (d.params_subset.trans hsub)
    (Set.subset_union_left.trans (hH.subset _))

end IDwDerivable

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
structure InvShape (A : Semisentence LForm 2) (G : Stage → Prop)
    (ψ χ : Proposition (LIinfW)) : Prop where
  not_lit : ¬TrueLit ψ
  ne_verum : ψ ≠ ⊤
  ne_X : ∀ t : SyntacticTerm (LIinfW), ψ ≠ XinfAt t
  ne_nX : ∀ t : SyntacticTerm (LIinfW), ψ ≠ ∼(XinfAt t)
  ne_or : ∀ φ₀ φ₁ : Proposition (LIinfW), ψ ≠ φ₀ ⋎ φ₁
  ne_exs : ∀ φ : Semiproposition (LIinfW) 1, ψ ≠ ∃¹ φ
  ne_stage : ∀ (s : Stage) (t : SyntacticTerm (LIinfW)), ψ ≠ stageAt s t
  ne_jlev : ∀ (ℓ : WithTop ℕ) (s t : SyntacticTerm (LIinfW)), ψ ≠ jlevAt ℓ s t
  of_and : ∀ φ₀ φ₁ : Proposition (LIinfW), ψ = φ₀ ⋏ φ₁ → χ = φ₀ ∨ χ = φ₁
  of_all : ∀ φ : Semiproposition (LIinfW) 1, ψ = ∀¹ φ → ∃ m : ℕ, χ = φ/[numI m]
  of_nstage : ∀ (k : ℕ) (a : StageAt k) (t : SyntacticTerm (LIinfW)),
    ψ = nstageAt (⟨k, a⟩ : Stage) t →
    ∃ g : StageAt k, g.1 < a.1 ∧ χ = ∼(unfoldW A k g t) ∧ G ⟨k, g⟩
  of_njlev : ∀ (ℓ : WithTop ℕ) (s t : SyntacticTerm (LIinfW)), ψ = njlevAt ℓ s t →
    ∃ _ : ((termVal s : ℕ) : WithTop ℕ) < ℓ, χ = ∼(IOmegaAt (termVal s) t)

namespace IDwDerivable

variable {A : Semisentence LForm 2} {ρ : ThetaVNoteD}

/-- The statement of inversion for a derivation of `Δ`. -/
def InvClaim (A : Semisentence LForm 2) (ρ : ThetaVNoteD) (G : Stage → Prop)
    (ψ χ : Proposition (LIinfW)) (H : Set ThetaVNoteD → Set ThetaVNoteD) (α : ThetaVNoteD)
    (Δ : Sequent (LIinfW)) : Prop :=
  ThetaVNoteD.IsOperator H → (∀ s : Stage, G s → s.val ∈ H ∅) →
    ∀ Γ : Sequent (LIinfW), Δ ⊆ ψ :: Γ → paramsVal (χ :: Γ) ⊆ H ∅ →
      IDwDerivable A ρ H α (χ :: Γ)

theorem mem_inv {ψ χ θ : Proposition (LIinfW)} {Δ Γ : Sequent (LIinfW)} (hθ : θ ∈ Δ)
    (hΔ : Δ ⊆ ψ :: Γ) (hne : θ ≠ ψ) : θ ∈ χ :: Γ := by
  rcases List.mem_cons.mp (hΔ hθ) with h | h
  · exact absurd h hne
  · exact List.mem_cons_of_mem _ h

theorem inv_prem {G : Stage → Prop} {ψ χ φ : Proposition (LIinfW)}
    {H : Set ThetaVNoteD → Set ThetaVNoteD} {α₀ : ThetaVNoteD} {Δ Γ : Sequent (LIinfW)}
    (hH : ThetaVNoteD.IsOperator H) (hγ : ∀ s : Stage, G s → s.val ∈ H ∅)
    (d₀ : IDwDerivable A ρ H α₀ (φ :: Δ)) (ih₀ : InvClaim A ρ G ψ χ H α₀ (φ :: Δ))
    (hΔ : Δ ⊆ ψ :: Γ) (hP : paramsVal (χ :: Γ) ⊆ H ∅) :
    IDwDerivable A ρ H α₀ (φ :: χ :: Γ) := by
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
theorem inv_principal {χ : Proposition (LIinfW)} {H : Set ThetaVNoteD → Set ThetaVNoteD}
    {α α₀ : ThetaVNoteD} {Γ : Sequent (LIinfW)} (hH : ThetaVNoteD.IsOperator H) (hα : α ∈ H ∅)
    (h0 : α₀ < α) (d : IDwDerivable A ρ H α₀ (χ :: χ :: Γ)) (hP : paramsVal (χ :: Γ) ⊆ H ∅) :
    IDwDerivable A ρ H α (χ :: Γ) :=
  d.weaken hH (le_of_lt h0)
    (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hα hP

theorem inv_aux {G : Stage → Prop} {ψ χ : Proposition (LIinfW)} (hs : InvShape A G ψ χ)
    {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Δ : Sequent (LIinfW)}
    (d : IDwDerivable A ρ H α Δ) : InvClaim A ρ G ψ χ H α Δ := by
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
    have p0 : ∀ g : StageAt k, g.1 < a.1 →
        IDwDerivable A ρ (ThetaVNoteD.adjoin H {g.1}) (f g)
          (∼(unfoldW A k g t) :: χ :: Γ) := by
      intro g hg
      have hsub : H ∅ ⊆ ThetaVNoteD.adjoin H {g.1} ∅ := hH.mono (Set.empty_subset _)
      exact inv_prem (hH.adjoin {g.1}) (fun g' hg' => hsub (hγ g' hg'))
        (d0 g hg) (ih0 g hg) hΔ (hP.trans hsub)
    by_cases he : nstageAt (⟨k, a⟩ : Stage) t = ψ
    · obtain ⟨g, hg, rfl, hG⟩ := hs.of_nstage k a t he.symm
      have e : ThetaVNoteD.adjoin H {g.1} = H :=
        ThetaVNoteD.adjoin_eq_self hH (Set.singleton_subset_iff.mpr (hγ ⟨k, g⟩ hG))
      have p := p0 g hg
      rw [e] at p
      exact inv_principal hH hα (hf g hg) p hP
    · exact .nstage f hα hP (mem_inv hm hΔ he) hf p0
  | fix hα _ hm hΩ h0 d0 ih0 =>
    intro hH hγ Γ hΔ hP
    exact .fix hα hP (mem_inv hm hΔ fun h => hs.ne_stage _ _ h.symm) hΩ h0
      (inv_prem hH hγ d0 ih0 hΔ hP)
  | jlev hα _ hm hs' ht hl h0 d0 ih0 =>
    intro hH hγ Γ hΔ hP
    exact .jlev hα hP (mem_inv hm hΔ fun h => hs.ne_jlev _ _ _ h.symm) hs' ht hl h0
      (inv_prem hH hγ d0 ih0 hΔ hP)
  | @njlev H α Δ ℓ s t α₀ hα _ hm hs' ht h0 d0 ih0 =>
    intro hH hγ Γ hΔ hP
    have p0 : ((termVal s : ℕ) : WithTop ℕ) < ℓ →
        IDwDerivable A ρ H α₀ (∼(IOmegaAt (termVal s) t) :: χ :: Γ) :=
      fun h => inv_prem hH hγ (d0 h) (ih0 h) hΔ hP
    by_cases he : njlevAt ℓ s t = ψ
    · obtain ⟨hl, rfl⟩ := hs.of_njlev ℓ s t he.symm
      exact inv_principal hH hα (h0 hl) (p0 hl) hP
    · exact .njlev hα hP (mem_inv hm hΔ he) hs' ht h0 p0
  | cut hα _ hr h0 d0 d1 ih0 ih1 =>
    intro hH hγ Γ hΔ hP
    exact .cut hα hP hr h0 (inv_prem hH hγ d0 ih0 hΔ hP) (inv_prem hH hγ d1 ih1 hΔ hP)

variable {H : Set ThetaVNoteD → Set ThetaVNoteD} {α : ThetaVNoteD} {Γ : Sequent (LIinfW)}

theorem inv_of_shape {G : Stage → Prop} {ψ χ : Proposition (LIinfW)} (hs : InvShape A G ψ χ)
    (hH : ThetaVNoteD.IsOperator H) (hγ : ∀ s : Stage, G s → s.val ∈ H ∅)
    (hχ : Stage.val '' params χ ⊆ H ∅) (d : IDwDerivable A ρ H α (ψ :: Γ)) :
    IDwDerivable A ρ H α (χ :: Γ) := by
  refine inv_aux hs d hH hγ Γ (List.Subset.refl _) ?_
  have h := d.params_subset
  rw [paramsVal_cons] at h ⊢
  exact Set.union_subset hχ (Set.subset_union_right.trans h)

/-- **Exercise 7.1 (a) for `∧`**, left component. -/
theorem inv_and_left (hH : ThetaVNoteD.IsOperator H) {φ₀ φ₁ : Proposition (LIinfW)}
    (d : IDwDerivable A ρ H α (φ₀ ⋏ φ₁ :: Γ)) : IDwDerivable A ρ H α (φ₀ :: Γ) :=
  inv_of_shape (G := fun _ => False) (ψ := φ₀ ⋏ φ₁)
    ⟨(fun h => by obtain ⟨⟨j, r, v, (h | h), -⟩, -⟩ := h <;> exact nomatch h),
      (fun h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ _ h => nomatch h),
      (fun _ _ h => by cases h; exact Or.inl rfl), (fun _ h => nomatch h),
      (fun _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
    hH (fun _ h => h.elim)
    (by
      have h := d.params_head_subset
      rw [params_and] at h
      exact fun x ⟨s, hs, hx⟩ => h ⟨s, Or.inl hs, hx⟩)
    d

/-- **Exercise 7.1 (a) for `∧`**, right component. -/
theorem inv_and_right (hH : ThetaVNoteD.IsOperator H) {φ₀ φ₁ : Proposition (LIinfW)}
    (d : IDwDerivable A ρ H α (φ₀ ⋏ φ₁ :: Γ)) : IDwDerivable A ρ H α (φ₁ :: Γ) :=
  inv_of_shape (G := fun _ => False) (ψ := φ₀ ⋏ φ₁)
    ⟨(fun h => by obtain ⟨⟨j, r, v, (h | h), -⟩, -⟩ := h <;> exact nomatch h),
      (fun h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ _ h => nomatch h),
      (fun _ _ h => by cases h; exact Or.inr rfl), (fun _ h => nomatch h),
      (fun _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
    hH (fun _ h => h.elim)
    (by
      have h := d.params_head_subset
      rw [params_and] at h
      exact fun x ⟨s, hs, hx⟩ => h ⟨s, Or.inr hs, hx⟩)
    d

/-- **Exercise 7.1 (a) for `∀`**: `H ⊢^α_ρ Γ, ∀x φ(x)` gives `H ⊢^α_ρ Γ, φ(m̄)`. -/
theorem inv_all (hH : ThetaVNoteD.IsOperator H) {φ : Semiproposition (LIinfW) 1} (m : ℕ)
    (d : IDwDerivable A ρ H α ((∀¹ φ) :: Γ)) : IDwDerivable A ρ H α (φ/[numI m] :: Γ) :=
  inv_of_shape (G := fun _ => False) (ψ := ∀¹ φ)
    ⟨(fun h => by obtain ⟨⟨j, r, v, (h | h), -⟩, -⟩ := h <;> exact nomatch h),
      (fun h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => by cases h; exact ⟨m, rfl⟩),
      (fun _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
    hH (fun _ h => h.elim)
    (by
      have h := d.params_head_subset
      rw [params_all] at h
      rw [params_subst1]
      exact h)
    d

/-- **Exercise 7.1 (a) for `¬I_k^{≺δ} t`**: `H ⊢^α_ρ Γ, ¬I_k^{≺δ} t` gives
`H ⊢^α_ρ Γ, ¬A(k̄, t; I_k^{≺γ}, Jlev k)` for `γ ≺ δ` with `γ ∈ H(∅)`. Unlike `IDn`, the
unfolding's only parameter is `⟨k, γ⟩` itself (`params_unfoldW`: `Q ↦ Jlev k` carries none), so
`IsOperator H` would suffice; `NiceS` is kept so that the `IDn`-shaped call sites port unchanged. -/
theorem inv_nstage (hH : ThetaVNoteD.NiceS H) {k : ℕ} {a g : StageAt k}
    {t : SyntacticTerm (LIinfW)} (hg : g.1 < a.1) (hgH : g.1 ∈ H ∅)
    (d : IDwDerivable A ρ H α (nstageAt (⟨k, a⟩ : Stage) t :: Γ)) :
    IDwDerivable A ρ H α (∼(unfoldW A k g t) :: Γ) :=
  inv_of_shape (G := fun s => s = (⟨k, g⟩ : Stage)) (ψ := nstageAt (⟨k, a⟩ : Stage) t)
    ⟨(fun h => by
        obtain ⟨⟨j, r, v, (h | h), -⟩, -⟩ := h
        · exact nomatch h
        · have := congrArg negHeadStage h
          exact nomatch this),
      (fun h => nomatch h), (fun _ h => nomatch h),
      (fun _ h => by have := congrArg negHeadStage h; exact nomatch this),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h),
      (fun k' a' t' h => by
        obtain ⟨hka, rfl⟩ := nstageAt_inj h
        have hkk' : k = k' := congrArg Stage.lvl hka
        subst hkk'
        have haa' : a = a' := Subtype.ext (congrArg Stage.val hka)
        subst haa'
        exact ⟨g, hg, rfl, rfl⟩),
      fun _ _ _ h => by have := congrArg negHeadStage h; exact nomatch this⟩
    hH.1 (fun s h => h ▸ hgH)
    (by
      rw [params_neg]
      rintro x ⟨s, hs, rfl⟩
      have h := params_unfoldW A k g t hs
      rw [Set.mem_singleton_iff] at h
      rw [h]
      exact hgH)
    d

/-- **Exercise 7.1 (a) for `¬Jlev ℓ (s,t)`** (with `val s < ℓ`): `H ⊢^α_ρ Γ, ¬Jlev ℓ (s,t)` gives
`H ⊢^α_ρ Γ, ¬I_{val s} t`. `H` nice, so the parameter `Ω_{val s+1}` of the new head is in `H(∅)`. -/
theorem inv_njlev (hH : ThetaVNoteD.NiceS H) {ℓ : WithTop ℕ} {s t : SyntacticTerm (LIinfW)}
    (hl : ((termVal s : ℕ) : WithTop ℕ) < ℓ)
    (d : IDwDerivable A ρ H α (njlevAt ℓ s t :: Γ)) :
    IDwDerivable A ρ H α (∼(IOmegaAt (termVal s) t) :: Γ) :=
  inv_of_shape (G := fun _ => False) (ψ := njlevAt ℓ s t)
    ⟨(fun h => not_trueLit_njlevAt _ _ _ h),
      (fun h => nomatch h), (fun _ h => nomatch h),
      (fun _ h => by have := congrArg atomShape h; simp at this),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h),
      (fun _ _ h => nomatch h), (fun _ h => nomatch h),
      (fun _ _ _ h => by have := congrArg negHeadStage h; exact nomatch this),
      fun ℓ' s' t' h => by
        obtain ⟨rfl, rfl, rfl⟩ := njlevAt_inj h
        exact ⟨hl, rfl⟩⟩
    hH.1 (fun _ h => h.elim)
    (by
      rw [params_neg, params_IOmegaAt]
      rintro x ⟨s', hs', rfl⟩
      rw [Set.mem_singleton_iff] at hs'
      rw [hs', Stage.val_top]
      exact hH.Omega_mem _)
    d

end IDwDerivable

end IDw

end OrdinalAnalysis
