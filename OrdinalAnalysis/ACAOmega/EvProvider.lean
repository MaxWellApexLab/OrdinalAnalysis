/-
  The substitution provider of the evaluating instantiation.

  `Reduction.lean` needs, for every arithmetical `ψ`, a depth-indexed family of
  formula maps that performs `X₀ ↦ ψ` — turning a `(∀₂)` eigenvariable premise
  `φ.free₁ :: shift₁ Γ` into `inst₂ φ ψ :: Γ` — and respects every rule of the
  calculus.  For the raw instantiation the family is Foundation's `Rew.app` at
  every depth.  For the evaluating one it cannot be: `Rew.app` composed with
  `ev₂` would normalise the *context* as well, and `ctx` demands that the
  context come back untouched.

  The family here is `evApp (liftN (subAt ψ m) N)` — substitute, and normalise
  exactly the instances `ψ/[t]` that the substitution creates.  That is the same
  operation `evInst₂.inst₂` is, so `head` holds by the composition law
  `evApp Ω (R.app φ) = evApp (Ω.comp R) φ` for a renaming `R`, and `ctx` holds
  because `(subAt ψ 0).comp shift = Rew.id` and `evApp Rew.id` is the identity —
  nothing is created, so nothing is normalised.

  The one law that needs real work is `SubstFamily.inst₂`,

      S m (inst₂ φ ψ') = inst₂ (S m φ) (S m ψ'),

  a composition of two `evApp`s on each side.  It goes through a genuine
  composition calculus for `evApp`: `ecomp`, whose components are the `evApp`
  images of the inner rewriting's, together with the congruence `evApp_congr`
  ("`evApp` sees a rewriting only through `evSub`"), because the two composites
  are equal only up to one extra `evSub … #0`.
-/
import OrdinalAnalysis.ACAOmega.Evaluate
import OrdinalAnalysis.ACAOmega.Reduction

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA

namespace OmegaDerivable₂

/-! ### `evApp` does not create bare set atoms out of nothing -/

theorem isSetAtom_evApp_of_not {N₁ N₂ : ℕ} (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ)
    {χ : Semiformula ℒₒᵣ ℕ ℕ N₁ 1} (h : isSetAtom χ = false) :
    isSetAtom (evApp Ω χ) = false := by
  cases χ using Semiformula.cases' with
  | hRel r v => simp
  | hNrel r v => simp
  | hBvar X t => exact isSetAtom_evSub_of_not_bvar _ (by simpa using h)
  | hNbvar X t =>
      rw [evApp_nbvar, isSetAtom_neg]
      exact isSetAtom_evSub_of_not_bvar _ (by simpa using h)
  | hFvar X t => exact isSetAtom_evSub_of_not_bvar _ (by simpa using h)
  | hNfvar X t =>
      rw [evApp_nfvar, isSetAtom_neg]
      exact isSetAtom_evSub_of_not_bvar _ (by simpa using h)
  | hVerum => simp
  | hFalsum => simp
  | hAnd φ ψ => simp
  | hOr φ ψ => simp
  | hAll₁ φ => simp
  | hExs₁ φ => simp
  | hAll₂ φ => simp
  | hExs₂ φ => simp

/-- **`evApp` commutes with `evSub`.**  This is the atomic step of the
composition law: substituting into a component and then applying `Ω` is
applying `Ω` to the component and then substituting. -/
theorem evApp_evSub {N₁ N₂ n : ℕ} (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ)
    (χ : Semiformula ℒₒᵣ ℕ ℕ N₁ 1) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    evApp Ω (evSub χ t) = evSub (evApp Ω χ) t := by
  by_cases h : isSetAtom χ = true
  · rw [evSub_of_atom h]
    rcases eq_of_isSetAtom h with ⟨Y, rfl⟩ | ⟨Y, rfl⟩ | ⟨Y, rfl⟩ | ⟨Y, rfl⟩ <;>
      simp [evSub_evSub_bvar]
  · have h' : isSetAtom χ = false := by simpa using h
    rw [evSub_of_not_atom h', evApp_ev₂ _ N₂ Ω,
      evSub_of_not_atom (isSetAtom_evApp_of_not Ω h'),
      SecondOrder.Rew.app_comm_subst]
    rw [← ev₂_rew_ev₂ (evApp Ω χ) n (FirstOrder.Rew.subst ![t]), ev₂_evApp χ N₂ Ω,
      ev₂_rew_ev₂ (Ω.app χ) n (FirstOrder.Rew.subst ![t])]

/-! ### `evApp` and the renaming of bound set variables -/

theorem evApp_bLeft : ∀ {N₁ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) (N₂ N₃ : ℕ)
    (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ) (f : Fin N₂ → Fin N₃),
    (evApp Ω φ).bmap f = evApp (Ω.bLeft f) φ := by
  intro N₁ n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₂ N₃ Ω f; simp
  | hNrel r v => intro N₂ N₃ Ω f; simp
  | hBvar X t => intro N₂ N₃ Ω f; simpa using evSub_bmap f (Ω.bv X) t
  | hNbvar X t =>
      intro N₂ N₃ Ω f
      simpa using congrArg (fun χ => ∼χ) (evSub_bmap f (Ω.bv X) t)
  | hFvar X t => intro N₂ N₃ Ω f; simpa using evSub_bmap f (Ω.fv X) t
  | hNfvar X t =>
      intro N₂ N₃ Ω f
      simpa using congrArg (fun χ => ∼χ) (evSub_bmap f (Ω.fv X) t)
  | hVerum => intro N₂ N₃ Ω f; simp
  | hFalsum => intro N₂ N₃ Ω f; simp
  | hAnd φ ψ ihφ ihψ => intro N₂ N₃ Ω f; simp [ihφ N₂ N₃ Ω f, ihψ N₂ N₃ Ω f]
  | hOr φ ψ ihφ ihψ => intro N₂ N₃ Ω f; simp [ihφ N₂ N₃ Ω f, ihψ N₂ N₃ Ω f]
  | hAll₁ φ ih => intro N₂ N₃ Ω f; simp [ih N₂ N₃ Ω f]
  | hExs₁ φ ih => intro N₂ N₃ Ω f; simp [ih N₂ N₃ Ω f]
  | hAll₂ φ ih =>
      intro N₂ N₃ Ω f
      simp only [evApp_all₂, Semiformula.bmap_all₁, SecondOrder.Rew.bLeft_q]
      exact congrArg (fun χ => ∀² χ) (ih (N₂ + 1) (N₃ + 1) Ω.q (Fin.retrusion f))
  | hExs₂ φ ih =>
      intro N₂ N₃ Ω f
      simp only [evApp_exs₂, Semiformula.bmap_exs₁, SecondOrder.Rew.bLeft_q]
      exact congrArg (fun χ => ∃² χ) (ih (N₂ + 1) (N₃ + 1) Ω.q (Fin.retrusion f))

theorem evApp_bRight : ∀ {N₀ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₀ n) (N₁ N₂ : ℕ)
    (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ) (f : Fin N₀ → Fin N₁),
    evApp Ω (φ.bmap f) = evApp (Ω.bRight f) φ := by
  intro N₀ n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₁ N₂ Ω f; simp
  | hNrel r v => intro N₁ N₂ Ω f; simp
  | hBvar X t => intro N₁ N₂ Ω f; simp
  | hNbvar X t => intro N₁ N₂ Ω f; simp
  | hFvar X t => intro N₁ N₂ Ω f; simp
  | hNfvar X t => intro N₁ N₂ Ω f; simp
  | hVerum => intro N₁ N₂ Ω f; simp
  | hFalsum => intro N₁ N₂ Ω f; simp
  | hAnd φ ψ ihφ ihψ => intro N₁ N₂ Ω f; simp [ihφ N₁ N₂ Ω f, ihψ N₁ N₂ Ω f]
  | hOr φ ψ ihφ ihψ => intro N₁ N₂ Ω f; simp [ihφ N₁ N₂ Ω f, ihψ N₁ N₂ Ω f]
  | hAll₁ φ ih => intro N₁ N₂ Ω f; simp [ih N₁ N₂ Ω f]
  | hExs₁ φ ih => intro N₁ N₂ Ω f; simp [ih N₁ N₂ Ω f]
  | hAll₂ φ ih =>
      intro N₁ N₂ Ω f
      simp only [Semiformula.bmap_all₁, evApp_all₂, SecondOrder.Rew.bRight_q]
      exact congrArg (fun χ => ∀² χ) (ih (N₁ + 1) (N₂ + 1) Ω.q (Fin.retrusion f))
  | hExs₂ φ ih =>
      intro N₁ N₂ Ω f
      simp only [Semiformula.bmap_exs₁, evApp_exs₂, SecondOrder.Rew.bRight_q]
      exact congrArg (fun χ => ∃² χ) (ih (N₁ + 1) (N₂ + 1) Ω.q (Fin.retrusion f))

/-! ### The composition calculus of `evApp` -/

/-- The composition of two evaluating rewritings. -/
def ecomp {N₁ N₂ N₃ : ℕ} (Ω₂₃ : SecondOrder.Rew ℒₒᵣ ℕ N₂ ℕ N₃ ℕ)
    (Ω₁₂ : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ) : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₃ ℕ where
  bv X := evApp Ω₂₃ (Ω₁₂.bv X)
  fv X := evApp Ω₂₃ (Ω₁₂.fv X)

@[simp] theorem ecomp_bv {N₁ N₂ N₃ : ℕ} (Ω₂₃ : SecondOrder.Rew ℒₒᵣ ℕ N₂ ℕ N₃ ℕ)
    (Ω₁₂ : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ) (X : Fin N₁) :
    (ecomp Ω₂₃ Ω₁₂).bv X = evApp Ω₂₃ (Ω₁₂.bv X) := rfl

@[simp] theorem ecomp_fv {N₁ N₂ N₃ : ℕ} (Ω₂₃ : SecondOrder.Rew ℒₒᵣ ℕ N₂ ℕ N₃ ℕ)
    (Ω₁₂ : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ) (X : ℕ) :
    (ecomp Ω₂₃ Ω₁₂).fv X = evApp Ω₂₃ (Ω₁₂.fv X) := rfl

theorem ecomp_q {N₁ N₂ N₃ : ℕ} (Ω₂₃ : SecondOrder.Rew ℒₒᵣ ℕ N₂ ℕ N₃ ℕ)
    (Ω₁₂ : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ) :
    (ecomp Ω₂₃ Ω₁₂).q = ecomp Ω₂₃.q Ω₁₂.q := by
  have key : ∀ (χ : Semiformula ℒₒᵣ ℕ ℕ N₂ 1),
      evApp Ω₂₃.q (χ.bmap Fin.succ) = (evApp Ω₂₃ χ).bmap Fin.succ := by
    intro χ
    rw [evApp_bRight χ (N₂ + 1) (N₃ + 1) Ω₂₃.q Fin.succ, SecondOrder.Rew.q_bRight_succ,
      evApp_bLeft χ N₃ (N₃ + 1) Ω₂₃ Fin.succ]
  ext X
  · cases X using Fin.cases with
    | zero =>
        show ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin (N₃ + 1))) =
          evApp Ω₂₃.q (Ω₁₂.q.bv 0)
        rw [SecondOrder.Rew.q_bv_zero, evApp_bvar, SecondOrder.Rew.q_bv_zero, evSub_bv]
    | succ X =>
        show (evApp Ω₂₃ (Ω₁₂.bv X)).bmap Fin.succ = evApp Ω₂₃.q (Ω₁₂.q.bv X.succ)
        rw [SecondOrder.Rew.q_bv_succ, key]
  · show (evApp Ω₂₃ (Ω₁₂.fv X)).bmap Fin.succ = evApp Ω₂₃.q (Ω₁₂.q.fv X)
    rw [SecondOrder.Rew.q_fv, key]

/-- **The composition law.** -/
theorem evApp_comp : ∀ {N₁ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) (N₂ N₃ : ℕ)
    (Ω₂₃ : SecondOrder.Rew ℒₒᵣ ℕ N₂ ℕ N₃ ℕ) (Ω₁₂ : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ),
    evApp Ω₂₃ (evApp Ω₁₂ φ) = evApp (ecomp Ω₂₃ Ω₁₂) φ := by
  intro N₁ n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₂ N₃ Ω₂₃ Ω₁₂; simp
  | hNrel r v => intro N₂ N₃ Ω₂₃ Ω₁₂; simp
  | hBvar X t => intro N₂ N₃ Ω₂₃ Ω₁₂; simpa using evApp_evSub Ω₂₃ (Ω₁₂.bv X) t
  | hNbvar X t =>
      intro N₂ N₃ Ω₂₃ Ω₁₂
      simpa using congrArg (fun χ => ∼χ) (evApp_evSub Ω₂₃ (Ω₁₂.bv X) t)
  | hFvar X t => intro N₂ N₃ Ω₂₃ Ω₁₂; simpa using evApp_evSub Ω₂₃ (Ω₁₂.fv X) t
  | hNfvar X t =>
      intro N₂ N₃ Ω₂₃ Ω₁₂
      simpa using congrArg (fun χ => ∼χ) (evApp_evSub Ω₂₃ (Ω₁₂.fv X) t)
  | hVerum => intro N₂ N₃ Ω₂₃ Ω₁₂; simp
  | hFalsum => intro N₂ N₃ Ω₂₃ Ω₁₂; simp
  | hAnd φ ψ ihφ ihψ =>
      intro N₂ N₃ Ω₂₃ Ω₁₂; simp [ihφ N₂ N₃ Ω₂₃ Ω₁₂, ihψ N₂ N₃ Ω₂₃ Ω₁₂]
  | hOr φ ψ ihφ ihψ =>
      intro N₂ N₃ Ω₂₃ Ω₁₂; simp [ihφ N₂ N₃ Ω₂₃ Ω₁₂, ihψ N₂ N₃ Ω₂₃ Ω₁₂]
  | hAll₁ φ ih => intro N₂ N₃ Ω₂₃ Ω₁₂; simp [ih N₂ N₃ Ω₂₃ Ω₁₂]
  | hExs₁ φ ih => intro N₂ N₃ Ω₂₃ Ω₁₂; simp [ih N₂ N₃ Ω₂₃ Ω₁₂]
  | hAll₂ φ ih =>
      intro N₂ N₃ Ω₂₃ Ω₁₂
      simp only [evApp_all₂, ecomp_q]
      exact congrArg (fun χ => ∀² χ) (ih (N₂ + 1) (N₃ + 1) Ω₂₃.q Ω₁₂.q)
  | hExs₂ φ ih =>
      intro N₂ N₃ Ω₂₃ Ω₁₂
      simp only [evApp_exs₂, ecomp_q]
      exact congrArg (fun χ => ∃² χ) (ih (N₂ + 1) (N₃ + 1) Ω₂₃.q Ω₁₂.q)

/-- **`evApp` sees a rewriting only through `evSub`.** -/
def ESubEq {N₁ N₂ : ℕ} (Ω Ω' : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ) : Prop :=
  (∀ (X : Fin N₁) (n : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n),
      evSub (Ω.bv X) t = evSub (Ω'.bv X) t) ∧
    ∀ (X : ℕ) (n : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n),
      evSub (Ω.fv X) t = evSub (Ω'.fv X) t

theorem ESubEq.q {N₁ N₂ : ℕ} {Ω Ω' : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ} (h : ESubEq Ω Ω') :
    ESubEq Ω.q Ω'.q := by
  constructor
  · intro X n t
    cases X using Fin.cases with
    | zero => rw [SecondOrder.Rew.q_bv_zero, SecondOrder.Rew.q_bv_zero]
    | succ X =>
        rw [SecondOrder.Rew.q_bv_succ, SecondOrder.Rew.q_bv_succ,
          ← evSub_bmap, ← evSub_bmap, h.1 X n t]
  · intro X n t
    rw [SecondOrder.Rew.q_fv, SecondOrder.Rew.q_fv, ← evSub_bmap, ← evSub_bmap, h.2 X n t]

theorem evApp_congr : ∀ {N₁ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) (N₂ : ℕ)
    (Ω Ω' : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ), ESubEq Ω Ω' → evApp Ω φ = evApp Ω' φ := by
  intro N₁ n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₂ Ω Ω' _; simp
  | hNrel r v => intro N₂ Ω Ω' _; simp
  | hBvar X t => intro N₂ Ω Ω' h; simpa using h.1 X _ t
  | hNbvar X t => intro N₂ Ω Ω' h; simpa using congrArg (fun χ => ∼χ) (h.1 X _ t)
  | hFvar X t => intro N₂ Ω Ω' h; simpa using h.2 X _ t
  | hNfvar X t => intro N₂ Ω Ω' h; simpa using congrArg (fun χ => ∼χ) (h.2 X _ t)
  | hVerum => intro N₂ Ω Ω' _; simp
  | hFalsum => intro N₂ Ω Ω' _; simp
  | hAnd φ ψ ihφ ihψ => intro N₂ Ω Ω' h; simp [ihφ N₂ Ω Ω' h, ihψ N₂ Ω Ω' h]
  | hOr φ ψ ihφ ihψ => intro N₂ Ω Ω' h; simp [ihφ N₂ Ω Ω' h, ihψ N₂ Ω Ω' h]
  | hAll₁ φ ih => intro N₂ Ω Ω' h; simp [ih N₂ Ω Ω' h]
  | hExs₁ φ ih => intro N₂ Ω Ω' h; simp [ih N₂ Ω Ω' h]
  | hAll₂ φ ih =>
      intro N₂ Ω Ω' h
      exact congrArg (fun χ => ∀² χ) (ih (N₂ + 1) Ω.q Ω'.q h.q)
  | hExs₂ φ ih =>
      intro N₂ Ω Ω' h
      exact congrArg (fun χ => ∃² χ) (ih (N₂ + 1) Ω.q Ω'.q h.q)

/-! ### The substitution family of the evaluating instantiation -/

variable {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1}

/-- The key instance of `evApp_comp` + `evApp_congr`: the `(∃₂)`-instance law of
the family.  Both sides are a two-step evaluating substitution, and the two
composites differ only by an `evSub … #0`, which `evSub_evSub_bvar` absorbs. -/
theorem evApp_subst₂_comm (Ω : SecondOrder.Rew ℒₒᵣ ℕ 0 ℕ 0 ℕ)
    (φ : Semiformula ℒₒᵣ ℕ ℕ 1 0) (σ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    evApp Ω (evApp (SecondOrder.Rew.subst ![σ]) φ)
      = evApp (SecondOrder.Rew.subst ![evApp Ω σ]) (evApp Ω.q φ) := by
  rw [evApp_comp φ 0 0 Ω (SecondOrder.Rew.subst ![σ]),
    evApp_comp φ 1 0 (SecondOrder.Rew.subst ![evApp Ω σ]) Ω.q]
  refine evApp_congr φ 0 _ _ ⟨fun X n t => ?_, fun X n t => ?_⟩
  · have hX : X = 0 := Subsingleton.elim X 0
    subst hX
    show evSub (evApp Ω ((SecondOrder.Rew.subst ![σ]).bv 0)) t
      = evSub (evApp (SecondOrder.Rew.subst ![evApp Ω σ]) (Ω.q.bv 0)) t
    rw [SecondOrder.Rew.subst_bv, SecondOrder.Rew.q_bv_zero, evApp_bvar,
      SecondOrder.Rew.subst_bv]
    simp only [Matrix.cons_val_zero]
    exact (evSub_evSub_bvar _ t).symm
  · show evSub (evApp Ω ((SecondOrder.Rew.subst ![σ]).fv X)) t
      = evSub (evApp (SecondOrder.Rew.subst ![evApp Ω σ]) (Ω.q.fv X)) t
    rw [SecondOrder.Rew.subst_fv, SecondOrder.Rew.q_fv, evApp_fvar,
      evApp_bRight (Ω.fv X) 1 0 (SecondOrder.Rew.subst ![evApp Ω σ]) Fin.succ,
      subst_bRight_succ, evApp_id]
    exact evSub_evSub_bvar _ t

/-- **The substitution family of `X₀ ↦ ψ` for the evaluating instantiation.** -/
def evFam (hψ : Arith ψ) : SubstFamily trueArithLits₂ evInst₂ where
  S m {N} {_} φ := evApp (liftN (subAt ψ m) N) φ
  neg m {N} {n} φ := evApp_neg φ N (liftN (subAt ψ m) N)
  verum := by intros; rfl
  or := by intros; rfl
  and := by intros; rfl
  all₁ := by intros; rfl
  exs₁ := by intros; rfl
  all₂ := by intros; rfl
  exs₂ := by intros; rfl
  inst m φ n := by
    show evApp (subAt ψ m) (ev₂ (φ/[(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)]))
      = ev₂ ((evApp (subAt ψ m) φ)/[(numAt n : FirstOrder.SyntacticTerm ℒₒᵣ)])
    rw [evApp_ev₂ _ 0 (subAt ψ m), SecondOrder.Rew.app_comm_subst,
      ← ev₂_rew_ev₂ (evApp (subAt ψ m) φ) 0 (FirstOrder.Rew.subst ![_]),
      ev₂_evApp φ 0 (subAt ψ m),
      ev₂_rew_ev₂ ((subAt ψ m).app φ) 0 (FirstOrder.Rew.subst ![_])]
  arith m σ hσ := by
    show Arith (evApp (subAt ψ m) σ)
    rw [arith_evApp σ 0 (subAt ψ m)]
    exact arith_app σ hσ (subAt ψ m) (fun X => X.elim0) (fun X => arith_fvAt hψ m X)
  inst₂ m φ σ := evApp_subst₂_comm (subAt ψ m) φ σ
  free m φ := by
    show evApp (subAt ψ (m + 1)) (SecondOrder.Rew.free.app φ)
      = SecondOrder.Rew.free.app (evApp (subAt ψ m).q φ)
    have hc : (subAt ψ (m + 1)).comp SecondOrder.Rew.free
        = SecondOrder.Rew.free.comp (subAt ψ m).q :=
      (subAtFamily (fun k => (numAt k : FirstOrder.SyntacticTerm ℒₒᵣ)) hψ).free_comp m
    rw [evApp_comp_atomRew φ 0 0 (subAt ψ (m + 1)) SecondOrder.Rew.free atomRew_free,
      evApp_atomRew_comp φ 1 0 SecondOrder.Rew.free (subAt ψ m).q atomRew_free, hc]
  shift m γ := by
    show evApp (subAt ψ (m + 1)) (SecondOrder.Rew.shift.app γ)
      = SecondOrder.Rew.shift.app (evApp (subAt ψ m) γ)
    have hc : (subAt ψ (m + 1)).comp SecondOrder.Rew.shift
        = SecondOrder.Rew.shift.comp (subAt ψ m) :=
      (subAtFamily (fun k => (numAt k : FirstOrder.SyntacticTerm ℒₒᵣ)) hψ).shift_comp m
    rw [evApp_comp_atomRew γ 0 0 (subAt ψ (m + 1)) SecondOrder.Rew.shift atomRew_shift,
      evApp_atomRew_comp γ 0 0 SecondOrder.Rew.shift (subAt ψ m) atomRew_shift, hc]
  atom m φ hφ := by
    obtain ⟨k, rl, v, rfl | rfl⟩ := trueArithLits₂.literal φ hφ <;> rfl
  Ok ρ := omegaN ≤ ρ
  rank_ctrl m φ ρ hok h := by
    show rank (evApp (subAt ψ m) φ) < ρ
    rw [rank_evApp φ 0 (subAt ψ m)]
    rcases lt_or_ge (rank φ) omegaN with h' | h'
    · exact lt_of_lt_of_le (rank_app_lt_omegaN _ (fun X => X.elim0)
        (fun X => rank_lt_omega_of_arith (arith_fvAt hψ m X)) h') hok
    · rw [rank_app_eq_of_omegaN_le _ (fun X => X.elim0)
        (fun X => rank_lt_omega_of_arith (arith_fvAt hψ m X)) h']
      exact h

/-- **The substitution provider of the evaluating instantiation.** -/
def evProvider : SubstProvider trueArithLits₂ evInst₂ where
  fam _ hψ := evFam hψ
  ok _ _ _ h := h
  head σ hσ φ := by
    show evApp (subAt σ 0) (SecondOrder.Rew.free.app φ)
      = evApp (SecondOrder.Rew.subst ![σ]) φ
    rw [evApp_comp_atomRew φ 0 0 (subAt σ 0) SecondOrder.Rew.free atomRew_free,
      subAt_zero_comp_free]
  ctx σ hσ γ := by
    show evApp (subAt σ 0) (SecondOrder.Rew.shift.app γ) = γ
    rw [evApp_comp_atomRew γ 0 0 (subAt σ 0) SecondOrder.Rew.shift atomRew_shift,
      subAt_zero_comp_shift, evApp_id]

end OmegaDerivable₂

end OrdinalAnalysis.ACAOmega
