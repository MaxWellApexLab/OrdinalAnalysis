/-
  **The internal ω-tower induction (⋆⋆)**.

      `ACA ⊢ ∀c ∀n ∀u (Tower(u,n,c) → (∀²X TI(≺₁,c,X)) → (∀²X TI(≺₁,u,X)))`

  This is the single use of the full second-order induction scheme in the
  upper-bound argument, and the one place where `ACA` outruns `ACA₀`: the
  induction formula

      `θ(n) :≡ ∀c ∀u (Tower(u,n,c) → (∀²X TI(c,X)) → (∀²X TI(u,X)))`

  is `Π¹₁`, not arithmetical, so `ACA₀`'s set-induction axiom cannot reach it.

  Three layers.

  * **Layer 0** (`namespace TowerSyntax`) — the first-order syntax of
    `Gentzen/Jump.lean`'s `formulaAt`/`belowAt`/`progAt`/`tiUptoAt` family under
    rewriting, and their closedness.  `Gentzen/LowerSyntax.lean` has the
    analogous facts for `Setup.lean`'s `below`/`Prog`/`TI`; the generic family
    of `Jump.lean` had none, and every step below needs them.
  * **Layer 1** — the second-order vocabulary (`allTI`, `stepBody`, `thetaAt`)
    together with the *uniform* rewriting lemma `rew_thetaAt`, which is what
    makes `free₀`/`shift₀`/`Rew.subst` computable on the induction formula, and
    the two membership conditions `NoSetFvar θ`, `shift₀ θ = θ` that
    `indScheme₂ θ ∈ ACA` demands.
  * **Layer 2** — the derivation: base case from `towerZero_SO` plus a Leibniz
    step (`Congruence.congrPSeq`), step case from `towerSucc_SO`, `spec₂` at
    `jumpWitness` (this *is* arithmetical comprehension — the `exs₂` rule) and
    `jumpB_SO`, and the `gen₁`/`gen₂` bookkeeping around them.

  The comprehension step uses **route 2** of the design note: `Toolkit.spec₂` is
  applied raw and both sides are normalised with `Lifted.lean`'s
  `toSOAtB_tiUptoAt`/`toSOAtB_liftCode`/`toSOAtB_Xat_bvar`, so no `Empty`-version
  of the jump formula is ever needed (`specSO` could not take one).
-/
import OrdinalAnalysis.ACA.Lifted
import OrdinalAnalysis.ACA.Congruence

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Layer 0: the first-order `tiUptoAt` family under rewriting -/

namespace OrdinalAnalysis.ACA.TowerSyntax

open LO LO.FirstOrder
open OrdinalAnalysis OrdinalAnalysis.Gentzen

/-- A rewriting passes through a substitution instance of a **closed** formula:
only the substituted terms are seen. -/
theorem rew_subst_closed {m n₁ n₂ : ℕ} {θ : Semiformula LX ℕ m} (hθ : θ.freeVariables = ∅)
    (ω : Rew LX ℕ n₁ ℕ n₂) (v : Fin m → Semiterm LX ℕ n₁) :
    ω ▹ (Rew.subst v ▹ θ) = Rew.subst (fun i => ω (v i)) ▹ θ := by
  rw [← TransitiveRewriting.comp_app]
  refine Semiformula.rew_eq_of_funEqOn ?_ ?_
  · intro x
    simp [Rew.comp_app]
  · intro x hx
    have hx' : x ∈ θ.freeVariables := hx
    rw [hθ] at hx'
    exact absurd hx' (by simp)

theorem q_bShift {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) (t : Semiterm LX ℕ n₁) :
    ω.q (Rew.bShift t) = Rew.bShift (ω t) := by
  simp [← Rew.comp_app]

/-- An operator applied to closed terms is a closed term.  (`LowerSyntax` has
only the `0`-ary case, `freeVariables_const`.) -/
theorem freeVariables_operator {k n : ℕ} (o : Semiterm.Operator LX k)
    {v : Fin k → Semiterm LX ℕ n} (hv : ∀ i, (v i).freeVariables = ∅) :
    (o.operator v).freeVariables = ∅ :=
  LowerSyntax.freeVariables_rew_term_eq_empty _ Semiterm.freeVariables_emb hv

@[simp] theorem freeVariables_succ_three :
    (‘(#1 + 1)’ : Semiterm LX ℕ 3).freeVariables = ∅ :=
  freeVariables_operator _ (fun j => by
    fin_cases j
    · rfl
    · exact freeVariables_operator _ (fun l => l.elim0))

variable {prec : Semiformula LX ℕ 2} {φ : Semiformula LX ℕ 1}

/-! ### Rewriting -/

theorem rew_formulaAt (hφ : φ.freeVariables = ∅) {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂)
    (t : Semiterm LX ℕ n₁) : ω ▹ (formulaAt φ t) = formulaAt φ (ω t) := by
  have hv : (fun i => ω ((![t] : Fin 1 → Semiterm LX ℕ n₁) i)) = ![ω t] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  show ω ▹ (Rew.subst ![t] ▹ φ) = Rew.subst ![ω t] ▹ φ
  rw [rew_subst_closed hφ ω ![t], hv]

theorem rew_precAt' (hprec : prec.freeVariables = ∅) {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂)
    (y x : Semiterm LX ℕ n₁) : ω ▹ (precAt prec y x) = precAt prec (ω y) (ω x) := by
  have hv : (fun i => ω ((![y, x] : Fin 2 → Semiterm LX ℕ n₁) i)) = ![ω y, ω x] := by
    funext i
    fin_cases i <;> rfl
  show ω ▹ (Rew.subst ![y, x] ▹ prec) = Rew.subst ![ω y, ω x] ▹ prec
  rw [rew_subst_closed hprec ω ![y, x], hv]

theorem rew_belowAt (hprec : prec.freeVariables = ∅) (hφ : φ.freeVariables = ∅)
    {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) (b : Semiterm LX ℕ n₁) :
    ω ▹ (belowAt prec φ b) = belowAt prec φ (ω b) := by
  have hq0 : ω.q (#0 : Semiterm LX ℕ (n₁ + 1)) = #0 := by simp
  show ω ▹ (∀¹ (∼(precAt prec (#0 : Semiterm LX ℕ (n₁ + 1)) (Rew.bShift b)) ⋎
      formulaAt φ #0)) = _
  rw [Rewriting.app_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, rew_precAt' hprec, rew_formulaAt hφ,
    q_bShift, hq0]
  rfl

theorem rew_progAt (hprec : prec.freeVariables = ∅) (hφ : φ.freeVariables = ∅)
    {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) :
    ω ▹ (progAt prec φ : Semiformula LX ℕ n₁) = (progAt prec φ : Semiformula LX ℕ n₂) := by
  have hq0 : ω.q (#0 : Semiterm LX ℕ (n₁ + 1)) = #0 := by simp
  show ω ▹ (∀¹ (∼(belowAt prec φ (#0 : Semiterm LX ℕ (n₁ + 1))) ⋎ formulaAt φ #0)) = _
  rw [Rewriting.app_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, rew_belowAt hprec hφ, rew_formulaAt hφ, hq0]
  rfl

theorem rew_tiUptoAt (hprec : prec.freeVariables = ∅) (hφ : φ.freeVariables = ∅)
    {n₁ n₂ : ℕ} (ω : Rew LX ℕ n₁ ℕ n₂) (a : Semiterm LX ℕ n₁) :
    ω ▹ (tiUptoAt prec φ a) = tiUptoAt prec φ (ω a) := by
  show ω ▹ (∼(progAt prec φ) ⋎ belowAt prec φ a) = _
  rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    rew_progAt hprec hφ, rew_belowAt hprec hφ]
  rfl

/-! ### Closedness -/

@[simp] theorem freeVariables_bvar {n : ℕ} (i : Fin n) :
    (#i : Semiterm LX ℕ n).freeVariables = ∅ := rfl

theorem freeVariables_formulaAt (hφ : φ.freeVariables = ∅) {n : ℕ} {t : Semiterm LX ℕ n}
    (ht : t.freeVariables = ∅) : (formulaAt φ t).freeVariables = ∅ :=
  LowerSyntax.freeVariables_rew_eq_empty _ hφ (fun i => by
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simpa using ht)

theorem freeVariables_belowAt (hprec : prec.freeVariables = ∅) (hφ : φ.freeVariables = ∅)
    {n : ℕ} {b : Semiterm LX ℕ n} (hb : b.freeVariables = ∅) :
    (belowAt prec φ b).freeVariables = ∅ := by
  have h1 : (precAt prec (#0 : Semiterm LX ℕ (n + 1)) (Rew.bShift b)).freeVariables = ∅ :=
    LowerSyntax.freeVariables_precAt_eq_empty hprec (by simp) (by simpa using hb)
  have h2 : (formulaAt φ (#0 : Semiterm LX ℕ (n + 1))).freeVariables = ∅ :=
    freeVariables_formulaAt hφ (by simp)
  show (∀¹ (∼(precAt prec (#0 : Semiterm LX ℕ (n + 1)) (Rew.bShift b)) ⋎
      formulaAt φ #0)).freeVariables = ∅
  simp [h1, h2]

theorem freeVariables_progAt (hprec : prec.freeVariables = ∅) (hφ : φ.freeVariables = ∅)
    {n : ℕ} : (progAt prec φ : Semiformula LX ℕ n).freeVariables = ∅ := by
  have h1 : (belowAt prec φ (#0 : Semiterm LX ℕ (n + 1))).freeVariables = ∅ :=
    freeVariables_belowAt hprec hφ (by simp)
  have h2 : (formulaAt φ (#0 : Semiterm LX ℕ (n + 1))).freeVariables = ∅ :=
    freeVariables_formulaAt hφ (by simp)
  show (∀¹ (∼(belowAt prec φ (#0 : Semiterm LX ℕ (n + 1))) ⋎ formulaAt φ #0)).freeVariables = ∅
  simp [h1, h2]

theorem freeVariables_tiUptoAt (hprec : prec.freeVariables = ∅) (hφ : φ.freeVariables = ∅)
    {n : ℕ} {a : Semiterm LX ℕ n} (ha : a.freeVariables = ∅) :
    (tiUptoAt prec φ a).freeVariables = ∅ := by
  have h1 : (progAt prec φ : Semiformula LX ℕ n).freeVariables = ∅ :=
    freeVariables_progAt hprec hφ
  have h2 : (belowAt prec φ a).freeVariables = ∅ := freeVariables_belowAt hprec hφ ha
  show (∼(progAt prec φ) ⋎ belowAt prec φ a).freeVariables = ∅
  simp [h1, h2]

/-! ### The jump formula is closed -/

open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁ freeVariables_precCode₁)
open OrdinalAnalysis.Gentzen.CodedVeblenJump (addCode₁ omegaPowCode₁)

@[simp] theorem freeVariables_addCode₁ : addCode₁.freeVariables = ∅ := by
  simp [addCode₁, CodedNotation.liftCode]

@[simp] theorem freeVariables_omegaPowCode₁ : omegaPowCode₁.freeVariables = ∅ := by
  simp [omegaPowCode₁, CodedNotation.liftCode]

@[simp] theorem freeVariables_towerCode₁ : VeblenTower.towerCode₁.freeVariables = ∅ := by
  simp [VeblenTower.towerCode₁, CodedNotation.liftCode]

theorem freeVariables_addAt {n : ℕ} {z x y : Semiterm LX ℕ n}
    (hz : z.freeVariables = ∅) (hx : x.freeVariables = ∅) (hy : y.freeVariables = ∅) :
    (addAt addCode₁ z x y).freeVariables = ∅ :=
  LowerSyntax.freeVariables_rew_eq_empty _ freeVariables_addCode₁ (fun i => by
    fin_cases i
    · simpa using hz
    · simpa using hx
    · simpa using hy)

theorem freeVariables_omegaPowAt {n : ℕ} {z x : Semiterm LX ℕ n}
    (hz : z.freeVariables = ∅) (hx : x.freeVariables = ∅) :
    (omegaPowAt omegaPowCode₁ z x).freeVariables = ∅ :=
  LowerSyntax.freeVariables_rew_eq_empty _ freeVariables_omegaPowCode₁ (fun i => by
    fin_cases i
    · simpa using hz
    · simpa using hx)

theorem freeVariables_towerAt {n : ℕ} {u k c : Semiterm LX ℕ n}
    (hu : u.freeVariables = ∅) (hk : k.freeVariables = ∅) (hc : c.freeVariables = ∅) :
    (VeblenTower.towerAt VeblenTower.towerCode₁ u k c).freeVariables = ∅ :=
  LowerSyntax.freeVariables_rew_eq_empty _ freeVariables_towerCode₁ (fun i => by
    fin_cases i
    · simpa using hu
    · simpa using hk
    · simpa using hc)

/-- `X(#0)` is closed. -/
@[simp] theorem freeVariables_XatZero {n : ℕ} :
    (Xat (#0 : Semiterm LX ℕ (n + 1))).freeVariables = ∅ := by simp

/-- **The jump of `X` is a closed formula.**  Needed both for `rew_tiUptoAt` at
the jump and for the `univCl`-unwrapping of `jumpBStatement`. -/
@[simp] theorem freeVariables_jumpX :
    (jump precCode₁ addCode₁ omegaPowCode₁
      (Xat (#0 : Semiterm LX ℕ 1))).freeVariables = ∅ := by
  have hX : (Xat (#0 : Semiterm LX ℕ 1)).freeVariables = ∅ := by simp
  have h1 : (omegaPowAt omegaPowCode₁ (#1 : Semiterm LX ℕ 4)
      (#3 : Semiterm LX ℕ 4)).freeVariables = ∅ :=
    freeVariables_omegaPowAt (by simp) (by simp)
  have h2 : (addAt addCode₁ (#0 : Semiterm LX ℕ 4) #2 #1).freeVariables = ∅ :=
    freeVariables_addAt (by simp) (by simp) (by simp)
  have h3 : (belowAt precCode₁ (Xat (#0 : Semiterm LX ℕ 1))
      (#2 : Semiterm LX ℕ 4)).freeVariables = ∅ :=
    freeVariables_belowAt freeVariables_precCode₁ hX (by simp)
  have h4 : (belowAt precCode₁ (Xat (#0 : Semiterm LX ℕ 1))
      (#0 : Semiterm LX ℕ 4)).freeVariables = ∅ :=
    freeVariables_belowAt freeVariables_precCode₁ hX (by simp)
  show (∀¹ ∀¹ ∀¹
    (∼(omegaPowAt omegaPowCode₁ (#1 : Semiterm LX ℕ 4)
        (Rew.bShift (Rew.bShift (Rew.bShift (#0 : Semiterm LX ℕ 1))))) ⋎
      (∼(addAt addCode₁ #0 #2 #1) ⋎
        (∼(belowAt precCode₁ (Xat (#0 : Semiterm LX ℕ 1)) #2) ⋎
          belowAt precCode₁ (Xat (#0 : Semiterm LX ℕ 1)) #0)))).freeVariables = ∅
  simp [h1, h2, h3, h4]

/-! ### `univCl` is a typing wrapper -/

/-- Embedding a `univCl`-closed **closed** formula back into `Semiformula LX ℕ 0`
returns it on the nose. -/
theorem emb_univCl_of_closed {χ : Semiformula LX ℕ 0} (h : χ.freeVariables = ∅) :
    (Rewriting.emb χ.univCl : Semiformula LX ℕ 0) = χ := by
  have h1 : ((χ.univCl : Sentence LX) : Semiformula LX ℕ 0) = χ.univCl' :=
    Semiformula.coe_univCl_eq_univCl' _
  rw [show (Rewriting.emb (χ.univCl) : Semiformula LX ℕ 0)
        = ((χ.univCl : Sentence LX) : Semiformula LX ℕ 0) from rfl, h1,
    Semiformula.univCl'_eq_self_of _ h]

/-! ### Two `paLX` theorems packaging the tower steps with transfinite induction

The two-layer discipline at work.  `towerZeroTIStatement` packages the zero
step `Tower(u,0,c) → u = c` *together with* the transport of `TI` across that
equality, so the second-order layer never has to perform a Leibniz step;
`towerStepTIStatement` packages the successor step of the tower *together with*
Gentzen's Lemma B, so the second-order layer never has to eliminate the internal
`∃v` (which would shift the eigenvariables of the whole context).

What is left for the second-order layer is then exactly the three genuinely
second-order moves: `gen₂`, `spec₂` at the jump, and the induction axiom. -/

/-- `Jump(X)` — the first-order source of the arithmetical witness `jumpWitness`. -/
abbrev jumpXF : Semiformula LX ℕ 1 :=
  jump precCode₁ addCode₁ omegaPowCode₁ (Xat (#0 : Semiterm LX ℕ 1))

/-- The matrix of the zero step. -/
def towerZeroTIBody : Semiformula LX ℕ 2 :=
  ∼(VeblenTower.towerAt VeblenTower.towerCode₁ (#0 : Semiterm LX ℕ 2)
      ((0 : ℕ) : Semiterm LX ℕ 2) #1) ⋎
    (∼(tiUptoAt precCode₁ (Xat (#0 : Semiterm LX ℕ 1)) (#1 : Semiterm LX ℕ 2)) ⋎
      tiUptoAt precCode₁ (Xat (#0 : Semiterm LX ℕ 1)) (#0 : Semiterm LX ℕ 2))

/-- **The zero step**: `∀c∀u (Tower(u,0,c) → TI(≺₁,c,X) → TI(≺₁,u,X))`. -/
def towerZeroTIStatement : Sentence LX := (∀¹ ∀¹ towerZeroTIBody).univCl

/-- The matrix of the successor step. -/
def towerStepTIBody : Semiformula LX ℕ 3 :=
  ∼(VeblenTower.towerAt VeblenTower.towerCode₁ (#0 : Semiterm LX ℕ 3)
      (‘(#1 + 1)’ : Semiterm LX ℕ 3) #2) ⋎
    (∼(∀¹ (∼(VeblenTower.towerAt VeblenTower.towerCode₁ (#0 : Semiterm LX ℕ 4) #2 #3) ⋎
          tiUptoAt precCode₁ jumpXF (#0 : Semiterm LX ℕ 4))) ⋎
      tiUptoAt precCode₁ (Xat (#0 : Semiterm LX ℕ 1)) (#0 : Semiterm LX ℕ 3))

/-- **The successor step**, with Gentzen's Lemma B already folded in:
`∀c∀k∀u (Tower(u,k+1,c) → (∀v (Tower(v,k,c) → TI(≺₁,Jump X,v))) → TI(≺₁,X,u))`.

The hypothesis is a *universal* statement about `v`, not an existential one —
that is the whole point: the internal `∃v` of the tower's successor step is
consumed here, inside `paLX`. -/
def towerStepTIStatement : Sentence LX := (∀¹ ∀¹ ∀¹ towerStepTIBody).univCl

@[simp] theorem freeVariables_towerZeroTIBody : towerZeroTIBody.freeVariables = ∅ := by
  have hX : (Xat (#0 : Semiterm LX ℕ 1)).freeVariables = ∅ := by simp
  have h1 : (VeblenTower.towerAt VeblenTower.towerCode₁ (#0 : Semiterm LX ℕ 2)
      ((0 : ℕ) : Semiterm LX ℕ 2) #1).freeVariables = ∅ :=
    freeVariables_towerAt (by simp) (by simp) (by simp)
  have h2 : (tiUptoAt precCode₁ (Xat (#0 : Semiterm LX ℕ 1))
      (#1 : Semiterm LX ℕ 2)).freeVariables = ∅ :=
    freeVariables_tiUptoAt freeVariables_precCode₁ hX (by simp)
  have h3 : (tiUptoAt precCode₁ (Xat (#0 : Semiterm LX ℕ 1))
      (#0 : Semiterm LX ℕ 2)).freeVariables = ∅ :=
    freeVariables_tiUptoAt freeVariables_precCode₁ hX (by simp)
  simp [towerZeroTIBody, h1, h2, h3]

@[simp] theorem freeVariables_towerStepTIBody : towerStepTIBody.freeVariables = ∅ := by
  have hX : (Xat (#0 : Semiterm LX ℕ 1)).freeVariables = ∅ := by simp
  have h1 : (VeblenTower.towerAt VeblenTower.towerCode₁ (#0 : Semiterm LX ℕ 3)
      (‘(#1 + 1)’ : Semiterm LX ℕ 3) #2).freeVariables = ∅ :=
    freeVariables_towerAt (by simp) (by simp) (by simp)
  have h2 : (VeblenTower.towerAt VeblenTower.towerCode₁ (#0 : Semiterm LX ℕ 4)
      #2 #3).freeVariables = ∅ :=
    freeVariables_towerAt (by simp) (by simp) (by simp)
  have h3 : (tiUptoAt precCode₁ jumpXF (#0 : Semiterm LX ℕ 4)).freeVariables = ∅ :=
    freeVariables_tiUptoAt freeVariables_precCode₁ freeVariables_jumpX (by simp)
  have h4 : (tiUptoAt precCode₁ (Xat (#0 : Semiterm LX ℕ 1))
      (#0 : Semiterm LX ℕ 3)).freeVariables = ∅ :=
    freeVariables_tiUptoAt freeVariables_precCode₁ hX (by simp)
  simp [towerStepTIBody, h1, h2, h3, h4]

/-- **The zero step, in `paLX`.**  `Tower(u,0,c)` forces `u = c`
(`VeblenTower.concrete_towerZero`), and then the two transfinite-induction
statements are the same statement. -/
theorem concrete_towerZeroTI : paLX ⊢ towerZeroTIStatement := by
  classical
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  have h0 : M↓[LX] ⊧ VeblenTower.towerZeroStatement VeblenTower.towerCode₁ :=
    consequence_iff_eq'.mp (Theory.Proof.sound VeblenTower.concrete_towerZero) M
  have h0' := (VeblenTower.models_towerZeroStatement VeblenTower.towerCode₁).mp h0
  show M↓[LX] ⊧ (∀¹ ∀¹ towerZeroTIBody).univCl
  rw [models_iff_proposition]
  intro f
  simp only [Semiformula.eval_all, towerZeroTIBody, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq, VeblenTower.eval_towerAt, eval_tiUptoAt,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  intro c u
  by_cases htw : VeblenTower.towerCode₁.Eval
      ![u, ((0 : ℕ) : Semiterm LX ℕ 2).val ![u, c] f, c] f
  · have huc : u = c := by
      refine h0' f c u ?_
      have he : ((0 : ℕ) : Semiterm LX ℕ 0).val ![] f =
          ((0 : ℕ) : Semiterm LX ℕ 2).val ![u, c] f := by simp
      rw [he]
      exact htw
    subst huc
    exact Or.inr (Classical.em _).symm
  · exact Or.inl htw

/-- **The successor step, in `paLX`.**  The tower's successor step supplies the
unique `v` with `Tower(v,k,c)` and `OmegaPow(u,v)`; the universal hypothesis is
used at that `v`, and Gentzen's Lemma B (`CodedVeblenJump.jumpB₁`) converts
`TI(Jump X, v)` into `TI(X, u)`. -/
theorem concrete_towerStepTI : paLX ⊢ towerStepTIStatement := by
  classical
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ _ _ hM
  have hS : M↓[LX] ⊧ VeblenTower.towerSuccStatement omegaPowCode₁ VeblenTower.towerCode₁ :=
    consequence_iff_eq'.mp (Theory.Proof.sound VeblenTower.concrete_towerSucc) M
  have hS' := (VeblenTower.models_towerSuccStatement omegaPowCode₁
    VeblenTower.towerCode₁).mp hS
  have hB : M↓[LX] ⊧ jumpBStatement precCode₁ addCode₁ omegaPowCode₁
      (Xat (#0 : Semiterm LX ℕ 1)) :=
    consequence_iff_eq'.mp (Theory.Proof.sound
      (CodedVeblenJump.jumpB₁ (Xat (#0 : Semiterm LX ℕ 1)))) M
  rw [models_iff] at hB
  simp only [jumpBStatement, Semiformula.eval_univCl, Semiformula.eval_all,
    LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq,
    eval_omegaPowAt, eval_tiUptoAt, Semiterm.val_bvar, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hB
  show M↓[LX] ⊧ (∀¹ ∀¹ ∀¹ towerStepTIBody).univCl
  rw [models_iff_proposition]
  intro f
  simp only [Semiformula.eval_all, towerStepTIBody, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.neg_eq, VeblenTower.eval_towerAt, eval_tiUptoAt,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  intro c k u
  by_cases htw : VeblenTower.towerCode₁.Eval
      ![u, (‘(#1 + 1)’ : Semiterm LX ℕ 3).val ![u, k, c] f, c] f
  · obtain ⟨v, hv, hom⟩ := hS' f c k u (by
      have he : (‘(#0 + 1)’ : Semiterm LX ℕ 1).val ![k] f =
          (‘(#1 + 1)’ : Semiterm LX ℕ 3).val ![u, k, c] f := by simp
      rw [he]
      exact htw)
    refine Or.inr ?_
    rw [or_iff_not_imp_left]
    intro hall
    have hW := not_not.mp hall
    have hWv := (hW v).resolve_left (not_not_intro hv)
    exact ((hB f v u).resolve_left (not_not_intro hom)).resolve_left (not_not_intro hWv)
  · exact Or.inl htw

end OrdinalAnalysis.ACA.TowerSyntax

/-! ## Layer 1: the second-order vocabulary -/

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX Xat paLX)
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁ freeVariables_precCode₁)
open OrdinalAnalysis.Gentzen.CodedVeblenJump (addCode₁ omegaPowCode₁)
open OrdinalAnalysis.ACA.TowerSyntax

/-- `TI(≺₁, X, a)` as a first-order `LX`-formula: the statement whose lifting at
a parameter `Ψ` is transfinite induction below `a` *for `Ψ`*. -/
def tiX {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) : FirstOrder.Semiformula LX ℕ n :=
  Gentzen.tiUptoAt precCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) a

/-- `TI(≺₁, Jump(X), a)`: the same for the jump of `X`. -/
def tiJumpX {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) : FirstOrder.Semiformula LX ℕ n :=
  Gentzen.tiUptoAt precCode₁
    (Gentzen.jump precCode₁ addCode₁ omegaPowCode₁
      (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))) a

@[simp] theorem freeVariables_tiX {n : ℕ} {a : FirstOrder.Semiterm LX ℕ n}
    (ha : a.freeVariables = ∅) : (tiX a).freeVariables = ∅ :=
  freeVariables_tiUptoAt freeVariables_precCode₁ (by simp) ha

@[simp] theorem freeVariables_tiJumpX {n : ℕ} {a : FirstOrder.Semiterm LX ℕ n}
    (ha : a.freeVariables = ∅) : (tiJumpX a).freeVariables = ∅ :=
  freeVariables_tiUptoAt freeVariables_precCode₁ (by simp) ha

theorem rew_tiX {n₁ n₂ : ℕ} (ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂)
    (a : FirstOrder.Semiterm LX ℕ n₁) : ω ▹ (tiX a) = tiX (ω a) :=
  rew_tiUptoAt freeVariables_precCode₁ (by simp) ω a

theorem rew_tiJumpX {n₁ n₂ : ℕ} (ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂)
    (a : FirstOrder.Semiterm LX ℕ n₁) : ω ▹ (tiJumpX a) = tiJumpX (ω a) :=
  rew_tiUptoAt freeVariables_precCode₁ freeVariables_jumpX ω a

/-- **`∀²X TI(≺₁, a, X)`** — the `Π¹₁` statement the tower induction carries. -/
def allTI {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  ∀² (toSOAtB boundWitness (tiX a))

/-- `Tower(u, k, c)`, lifted. -/
def towerSO {n : ℕ} (u k c : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  toSOAt segWitness (Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁ u k c)

/-- `OmegaPow(z, a)`, lifted. -/
def omegaPowSO {n : ℕ} (z a : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  toSOAt segWitness (Gentzen.omegaPowAt omegaPowCode₁ z a)

/-- The matrix of the induction formula:
`Tower(u,k,c) → (∀²X TI(c,X)) → (∀²X TI(u,X))`. -/
def stepBody {n : ℕ} (u k c : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  ∼(towerSO u k c) ⋎ (∼(allTI c) ⋎ allTI u)

/-- `∀u (Tower(u,k,c) → …)`. -/
def thetaInner {n : ℕ} (k c : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  ∀¹ (stepBody (#0 : FirstOrder.Semiterm LX ℕ (n + 1))
    (FirstOrder.Rew.bShift k) (FirstOrder.Rew.bShift c))

/-- **The induction formula `θ`, at an arbitrary term for the tower height.** -/
def thetaAt {n : ℕ} (k : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  ∀¹ (thetaInner (FirstOrder.Rew.bShift k) (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))

/-- `θ` itself, with the induction variable in the innermost bound slot. -/
def theta : Semiproposition ℒₒᵣ 0 1 := thetaAt (#0 : FirstOrder.Semiterm LX ℕ 1)

/-! ### The uniform rewriting lemma

`free₀`, `shift₀` and every `Rew.subst` that `LK.lean`'s `indBody` applies to
`θ` are instances of this one lemma; nothing below ever computes a rewriting of
`θ` by hand. -/

section Rew

variable {n₁ n₂ : ℕ} {ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂} {ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂}

theorem rew_towerSO (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (u k c : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (towerSO u k c) = towerSO (ω u) (ω k) (ω c) := by
  have hv : (fun i => ω ((![u, k, c] : Fin 3 → FirstOrder.Semiterm LX ℕ n₁) i)) =
      ![ω u, ω k, ω c] := by
    funext i; fin_cases i <;> rfl
  show ω' ▹ (toSOAt segWitness (FirstOrder.Rew.subst ![u, k, c] ▹
    Gentzen.VeblenTower.towerCode₁)) = _
  rw [← toSOAtB_rew hb hf, rew_subst_closed freeVariables_towerCode₁ ω ![u, k, c], hv]
  rfl

theorem rew_omegaPowSO (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (z a : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (omegaPowSO z a) = omegaPowSO (ω z) (ω a) := by
  have hv : (fun i => ω ((![z, a] : Fin 2 → FirstOrder.Semiterm LX ℕ n₁) i)) =
      ![ω z, ω a] := by
    funext i; fin_cases i <;> rfl
  show ω' ▹ (toSOAt segWitness (FirstOrder.Rew.subst ![z, a] ▹ omegaPowCode₁)) = _
  rw [← toSOAtB_rew hb hf, rew_subst_closed freeVariables_omegaPowCode₁ ω ![z, a], hv]
  rfl

theorem rew_allTI (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (a : FirstOrder.Semiterm LX ℕ n₁) : ω' ▹ (allTI a) = allTI (ω a) := by
  show ω' ▹ (∀² (toSOAtB boundWitness (tiX a))) = _
  rw [Semiformula.rew_all₁, ← toSOAtB_rew hb hf, rew_tiX]
  rfl

theorem rew_stepBody (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (u k c : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (stepBody u k c) = stepBody (ω u) (ω k) (ω c) := by
  show ω' ▹ (∼(towerSO u k c) ⋎ (∼(allTI c) ⋎ allTI u)) = _
  rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_neg,
    rew_towerSO hb hf, rew_allTI hb hf, rew_allTI hb hf]
  rfl

theorem rew_thetaInner (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (k c : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (thetaInner k c) = thetaInner (ω k) (ω c) := by
  show ω' ▹ (∀¹ (stepBody (#0 : FirstOrder.Semiterm LX ℕ (n₁ + 1))
    (FirstOrder.Rew.bShift k) (FirstOrder.Rew.bShift c))) = _
  rw [Semiformula.rew_all₀, rew_stepBody (q_hb hb) (q_hf hf), q_bShift, q_bShift]
  show ∀¹ (stepBody (ω.q #0) (FirstOrder.Rew.bShift (ω k)) (FirstOrder.Rew.bShift (ω c))) = _
  simp only [FirstOrder.Rew.q_bvar_zero]
  rfl

theorem rew_thetaAt (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (k : FirstOrder.Semiterm LX ℕ n₁) : ω' ▹ (thetaAt k) = thetaAt (ω k) := by
  show ω' ▹ (∀¹ (thetaInner (FirstOrder.Rew.bShift k)
    (#0 : FirstOrder.Semiterm LX ℕ (n₁ + 1)))) = _
  rw [Semiformula.rew_all₀, rew_thetaInner (q_hb hb) (q_hf hf), q_bShift]
  show ∀¹ (thetaInner (FirstOrder.Rew.bShift (ω k)) (ω.q #0)) = _
  simp only [FirstOrder.Rew.q_bvar_zero]
  rfl

end Rew

/-! ### The two membership conditions for `indScheme₂ θ ∈ ACA` -/

theorem noSetFvar_allTI {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) : NoSetFvar (allTI a) :=
  noSetFvar_toSOAtB noSetFvar_emb_boundWitness _

/-- **The lifted tower graph is a `lift`**, parameter-independent (it mentions no
`X`).  This is what makes it `NoSetFvar` and `shift₁`-fixed. -/
theorem towerSO_eq {n : ℕ} (u k c : FirstOrder.Semiterm LX ℕ n) :
    towerSO u k c =
      FirstOrder.Rew.subst ![unTerm u, unTerm k, unTerm c] ▹
        (lift (FirstOrder.Rewriting.emb Gentzen.VeblenTower.towerDef₁.val) :
          Semiproposition ℒₒᵣ 0 3) := by
  show toSOAtB segWitness (FirstOrder.Rew.subst ![u, k, c] ▹
    (Gentzen.CodedNotation.liftCode Gentzen.VeblenTower.towerDef₁)) = _
  rw [toSOAtB_rew (ω := FirstOrder.Rew.subst ![u, k, c])
      (ω' := FirstOrder.Rew.subst ![unTerm u, unTerm k, unTerm c])
      (fun i => by fin_cases i <;> simp) (fun _ => by simp),
    toSOAtB_liftCode]

theorem omegaPowSO_eq {n : ℕ} (z a : FirstOrder.Semiterm LX ℕ n) :
    omegaPowSO z a =
      FirstOrder.Rew.subst ![unTerm z, unTerm a] ▹
        (lift (FirstOrder.Rewriting.emb
          Gentzen.CodedVeblenJump.omegaPowDef₁.val) : Semiproposition ℒₒᵣ 0 2) := by
  show toSOAtB segWitness (FirstOrder.Rew.subst ![z, a] ▹
    (Gentzen.CodedNotation.liftCode Gentzen.CodedVeblenJump.omegaPowDef₁)) = _
  rw [toSOAtB_rew (ω := FirstOrder.Rew.subst ![z, a])
      (ω' := FirstOrder.Rew.subst ![unTerm z, unTerm a])
      (fun i => by fin_cases i <;> simp) (fun _ => by simp),
    toSOAtB_liftCode]

theorem noSetFvar_towerSO {n : ℕ} (u k c : FirstOrder.Semiterm LX ℕ n) :
    NoSetFvar (towerSO u k c) := by
  rw [towerSO_eq]
  exact (noSetFvar_rew _ _).mpr (noSetFvar_lift _)

theorem noSetFvar_omegaPowSO {n : ℕ} (z a : FirstOrder.Semiterm LX ℕ n) :
    NoSetFvar (omegaPowSO z a) := by
  rw [omegaPowSO_eq]
  exact (noSetFvar_rew _ _).mpr (noSetFvar_lift _)

theorem noSetFvar_stepBody {n : ℕ} (u k c : FirstOrder.Semiterm LX ℕ n) :
    NoSetFvar (stepBody u k c) := by
  show NoSetFvar (∼(towerSO u k c) ⋎ (∼(allTI c) ⋎ allTI u))
  simp [noSetFvar_towerSO, noSetFvar_allTI]

theorem noSetFvar_theta : NoSetFvar theta := by
  show NoSetFvar (∀¹ (∀¹ (stepBody _ _ _)))
  simpa using noSetFvar_stepBody (n := 3) _ _ _

theorem shift₀_theta : Semiproposition.shift₀ theta = theta := by
  show (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1) ▹ theta = theta
  show (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1) ▹
    (thetaAt (#0 : FirstOrder.Semiterm LX ℕ 1)) = _
  rw [rew_thetaAt (ω := (FirstOrder.Rew.shift : FirstOrder.Rew LX ℕ 1 ℕ 1))
    (fun i => by simp) (fun x => by simp)]
  rfl

theorem noSetFvar_thetaInner {n : ℕ} (k c : FirstOrder.Semiterm LX ℕ n) :
    NoSetFvar (thetaInner k c) := by
  show NoSetFvar (∀¹ (stepBody (#0 : FirstOrder.Semiterm LX ℕ (n + 1)) _ _))
  simpa using noSetFvar_stepBody (n := n + 1) _ _ _

theorem noSetFvar_thetaAt {n : ℕ} (k : FirstOrder.Semiterm LX ℕ n) :
    NoSetFvar (thetaAt k) := by
  show NoSetFvar (∀¹ (thetaInner _ (#0 : FirstOrder.Semiterm LX ℕ (n + 1))))
  simpa using noSetFvar_thetaInner (n := n + 1) _ _

/-! ## Layer 2: the derivation -/

/-! ### The three rewriting packages used below -/

theorem hb_shift {n : ℕ} : ∀ i,
    unTerm ((FirstOrder.Rew.shift : FirstOrder.Rew LX ℕ n ℕ n) #i) =
      (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) #i := fun _ => by simp

theorem hf_shift {n : ℕ} : ∀ x,
    unTerm ((FirstOrder.Rew.shift : FirstOrder.Rew LX ℕ n ℕ n) &x) =
      (FirstOrder.Rew.shift : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) &x := fun _ => by simp

theorem hb_free {n : ℕ} : ∀ i,
    unTerm ((FirstOrder.Rew.free : FirstOrder.Rew LX ℕ (n + 1) ℕ n) #i) =
      (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ (n + 1) ℕ n) #i := fun i => by
  cases i using Fin.lastCases <;> simp

theorem hf_free {n : ℕ} : ∀ x,
    unTerm ((FirstOrder.Rew.free : FirstOrder.Rew LX ℕ (n + 1) ℕ n) &x) =
      (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ (n + 1) ℕ n) &x := fun _ => by simp

theorem hb_subst {m n : ℕ} (w : Fin m → FirstOrder.Semiterm LX ℕ n) : ∀ i,
    unTerm ((FirstOrder.Rew.subst w) #i) =
      (FirstOrder.Rew.subst (fun j => unTerm (w j))) #i := fun _ => by simp

theorem hf_subst {m n : ℕ} (w : Fin m → FirstOrder.Semiterm LX ℕ n) : ∀ x,
    unTerm ((FirstOrder.Rew.subst w) &x) =
      (FirstOrder.Rew.subst (fun j => unTerm (w j))) &x := fun _ => by simp

/-! ### `TI` at the free set variable, and at the jump -/

/-- `TI(≺₁, X₀, a)` — the `∀²`-eliminated form of `allTI a`. -/
def tiSO {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  toSOAt segWitness (tiX a)

/-- `TI(≺₁, Jump(X₀), a)` — the `spec₂`-instance at `jumpWitness`. -/
def tiJSO {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  toSOAt segWitness (tiJumpX a)

section RewTI

variable {n₁ n₂ : ℕ} {ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂} {ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂}

theorem rew_tiSO (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (a : FirstOrder.Semiterm LX ℕ n₁) : ω' ▹ (tiSO a) = tiSO (ω a) := by
  show ω' ▹ (toSOAt segWitness (tiX a)) = _
  rw [← toSOAtB_rew hb hf, rew_tiX]
  rfl

theorem rew_tiJSO (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (a : FirstOrder.Semiterm LX ℕ n₁) : ω' ▹ (tiJSO a) = tiJSO (ω a) := by
  show ω' ▹ (toSOAt segWitness (tiJumpX a)) = _
  rw [← toSOAtB_rew hb hf, rew_tiJumpX]
  rfl

end RewTI

/-! ### Route 2: `spec₂` at the jump, normalised

`specSO` cannot be used: it wants a witness over `ξ = Empty`, and `jumpWitness`
— being the image of a `Gentzen` code, which lives over `ξ = ℕ` — is not one.
Instead `Toolkit.spec₂` is applied raw and both sides are normalised through
`Lifted.lean`'s `tiUptoAtLift`. -/

/-- A second-order substitution fixes a lifted first-order formula. -/
theorem subst₁_lift {N M n : ℕ} (Φ : Fin N → Semiformula ℒₒᵣ ℕ ℕ M 1)
    (χ : FirstOrder.Semiformula ℒₒᵣ ℕ n) :
    Semiproposition.subst₁ (lift χ : Semiproposition ℒₒᵣ N n) Φ = lift χ := by
  induction χ using FirstOrder.Semiformula.rec' <;> simp [lift, *]

/-- Substituting for the bound slot of the embedded `boundWitness`. -/
theorem subst₁_emb_boundWitness {M : ℕ} (Ψ : Semiformula ℒₒᵣ ℕ ℕ M 1) :
    Semiproposition.subst₁
        (FirstOrder.Rewriting.emb boundWitness : Semiproposition ℒₒᵣ 1 1) ![Ψ] = Ψ := by
  show (SecondOrder.Rew.subst ![Ψ]).app
    (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# (0 : Fin 1)) : Semiproposition ℒₒᵣ 1 1) = _
  simp only [SecondOrder.Rew.app_bvar, SecondOrder.Rew.subst_bv, Matrix.cons_val_fin_one]
  exact FirstOrder.Rewriting.subst1_bvar0_eq _

section SubstLift

variable {N M n : ℕ} (Φ : Fin N → Semiformula ℒₒᵣ ℕ ℕ M 1)

theorem subst₁_precAtLift (P : Semiformula ℒₒᵣ ℕ ℕ N 2)
    (y x : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    (SecondOrder.Rew.subst Φ).app (precAtLift P y x) =
      precAtLift ((SecondOrder.Rew.subst Φ).app P) y x :=
  SecondOrder.Rew.app_comm_subst _ _ _

theorem subst₁_formulaAtLift (Ψ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (x : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    (SecondOrder.Rew.subst Φ).app (formulaAtLift Ψ x) =
      formulaAtLift ((SecondOrder.Rew.subst Φ).app Ψ) x :=
  SecondOrder.Rew.app_comm_subst _ _ _

theorem subst₁_belowAtLift (P : Semiformula ℒₒᵣ ℕ ℕ N 2) (Ψ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (b : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    (SecondOrder.Rew.subst Φ).app (belowAtLift P Ψ b) =
      belowAtLift ((SecondOrder.Rew.subst Φ).app P) ((SecondOrder.Rew.subst Φ).app Ψ) b := by
  show (SecondOrder.Rew.subst Φ).app
    (∀¹ (∼(precAtLift P (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1))
        (FirstOrder.Rew.bShift b)) ⋎ formulaAtLift Ψ #0)) = _
  rw [SecondOrder.Rew.app_all₀, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, subst₁_precAtLift, subst₁_formulaAtLift]
  rfl

theorem subst₁_progAtLift (P : Semiformula ℒₒᵣ ℕ ℕ N 2) (Ψ : Semiformula ℒₒᵣ ℕ ℕ N 1) :
    (SecondOrder.Rew.subst Φ).app (progAtLift (n := n) P Ψ) =
      progAtLift ((SecondOrder.Rew.subst Φ).app P) ((SecondOrder.Rew.subst Φ).app Ψ) := by
  show (SecondOrder.Rew.subst Φ).app
    (∀¹ (∼(belowAtLift P Ψ (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1))) ⋎
      formulaAtLift Ψ #0)) = _
  rw [SecondOrder.Rew.app_all₀, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, subst₁_belowAtLift, subst₁_formulaAtLift]
  rfl

/-- **The owed lemma of design-note route 2.** -/
theorem subst₁_tiUptoAtLift (P : Semiformula ℒₒᵣ ℕ ℕ N 2) (Ψ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (a : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    Semiproposition.subst₁ (tiUptoAtLift P Ψ a) Φ =
      tiUptoAtLift (Semiproposition.subst₁ P Φ) (Semiproposition.subst₁ Ψ Φ) a := by
  show (SecondOrder.Rew.subst Φ).app (∼(progAtLift P Ψ) ⋎ belowAtLift P Ψ a) = _
  rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    subst₁_progAtLift, subst₁_belowAtLift]
  rfl

end SubstLift

@[simp] theorem toSOAtB_precCode₁ {N : ℕ} {ψ : Semiformula ℒₒᵣ ℕ Empty N 1} :
    toSOAtB ψ precCode₁ =
      lift (FirstOrder.Rewriting.emb Gentzen.InternalVNote.precDef₁.val) :=
  toSOAtB_liftCode _

/-- The image of `TI(≺₁, X, a)` in the bound-slot presentation, normalised. -/
theorem tiBody_eq {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) :
    toSOAtB boundWitness (tiX a) =
      tiUptoAtLift (lift (FirstOrder.Rewriting.emb Gentzen.InternalVNote.precDef₁.val))
        (FirstOrder.Rewriting.emb boundWitness) (unTerm a) := by
  show toSOAtB boundWitness (Gentzen.tiUptoAt precCode₁
    (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) a) = _
  rw [toSOAtB_tiUptoAt, toSOAtB_precCode₁, toSOAtB_Xat_bvar]

/-- The image of `TI(≺₁, Jump X, a)` at the free set variable, normalised. -/
theorem tiJSO_eq {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) :
    tiJSO a =
      tiUptoAtLift (lift (FirstOrder.Rewriting.emb Gentzen.InternalVNote.precDef₁.val))
        jumpWitness (unTerm a) := by
  show toSOAtB segWitness (Gentzen.tiUptoAt precCode₁
    (Gentzen.jump precCode₁ addCode₁ omegaPowCode₁
      (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))) a) = _
  rw [toSOAtB_tiUptoAt, toSOAtB_precCode₁]
  rfl

/-- **`spec₂` at `jumpWitness`, computed.**  The `∀²X TI(≺₁,a,X)` hypothesis,
instantiated at the arithmetical witness `Jump(X₀)`, *is* transfinite induction
below `a` for the jump — which is the hypothesis of Gentzen's Lemma B. -/
theorem subst₁_tiBody_jump {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.subst₁ (toSOAtB boundWitness (tiX a)) ![jumpWitness] = tiJSO a := by
  rw [tiBody_eq, subst₁_tiUptoAtLift, subst₁_lift, subst₁_emb_boundWitness, tiJSO_eq]

/-- `spec₂` at the *free set variable* witness. -/
theorem subst₁_tiBody_free {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.subst₁ (toSOAtB boundWitness (tiX a)) ![freeWitness] = tiSO a := by
  have h := subst₁_toSOAtB (ψ := boundWitness) ![segWitness] (tiX a)
  rw [emb_cons_witness, emb_segWitness, subst₁_boundWitness] at h
  exact h

/-- **`free₁` of the bound-slot presentation** — the `gen₂` premise. -/
theorem free₁_tiBody (a : FirstOrder.Semiterm LX ℕ 0) :
    Semiproposition.free₁ (toSOAtB boundWitness (tiX a)) = tiSO a :=
  free₁_toSOAtB (tiX a)

/-- The negated form of the free-variable instantiation (what `exs₂` produces). -/
theorem neg_subst₁_tiBody_free {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.subst₁ (∼(toSOAtB boundWitness (tiX a))) ![freeWitness] = ∼(tiSO a) := by
  have h0 : Semiproposition.subst₁ (∼(toSOAtB boundWitness (tiX a))) ![freeWitness] =
      ∼(Semiproposition.subst₁ (toSOAtB boundWitness (tiX a)) ![freeWitness]) := by
    simp [Semiproposition.subst₁]
  rw [h0, subst₁_tiBody_free]

/-- The negated form of the jump instantiation. -/
theorem neg_subst₁_tiBody_jump {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.subst₁ (∼(toSOAtB boundWitness (tiX a))) ![jumpWitness] = ∼(tiJSO a) := by
  have h0 : Semiproposition.subst₁ (∼(toSOAtB boundWitness (tiX a))) ![jumpWitness] =
      ∼(Semiproposition.subst₁ (toSOAtB boundWitness (tiX a)) ![jumpWitness]) := by
    simp [Semiproposition.subst₁]
  rw [h0, subst₁_tiBody_jump]

/-! ### The two lifted tower statements -/

/-- The matrix of the lifted zero step (`#0 = u`, `#1 = c`). -/
def zeroMatrixSO : Semiproposition ℒₒᵣ 0 2 :=
  ∼(towerSO (#0 : FirstOrder.Semiterm LX ℕ 2)
      ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2) #1) ⋎
    (∼(tiSO (#1 : FirstOrder.Semiterm LX ℕ 2)) ⋎ tiSO (#0 : FirstOrder.Semiterm LX ℕ 2))

/-- The matrix of the lifted successor step (`#0 = u`, `#1 = k`, `#2 = c`). -/
def stepMatrixSO : Semiproposition ℒₒᵣ 0 3 :=
  ∼(towerSO (#0 : FirstOrder.Semiterm LX ℕ 3) (‘(#1 + 1)’) #2) ⋎
    (∼(∀¹ (∼(towerSO (#0 : FirstOrder.Semiterm LX ℕ 4) #2 #3) ⋎
          tiJSO (#0 : FirstOrder.Semiterm LX ℕ 4))) ⋎
      tiSO (#0 : FirstOrder.Semiterm LX ℕ 3))

theorem towerZeroTI_SO : Provable ACA (∀¹ (∀¹ zeroMatrixSO)) := by
  have h : Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      ((∀¹ (∀¹ TowerSyntax.towerZeroTIBody)).univCl))) :=
    lift_paLX_seg TowerSyntax.concrete_towerZeroTI
  rw [TowerSyntax.emb_univCl_of_closed (by simp)] at h
  have e : toSOAt segWitness ((∀¹ (∀¹ TowerSyntax.towerZeroTIBody)) :
      FirstOrder.Semiformula LX ℕ 0) = ∀¹ (∀¹ zeroMatrixSO) := by
    show ∀¹ (∀¹ (toSOAtB segWitness TowerSyntax.towerZeroTIBody)) = _
    show ∀¹ (∀¹ (toSOAtB segWitness
      (∼(Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
          (#0 : FirstOrder.Semiterm LX ℕ 2) ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2) #1) ⋎
        (∼(Gentzen.tiUptoAt precCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
            (#1 : FirstOrder.Semiterm LX ℕ 2)) ⋎
          Gentzen.tiUptoAt precCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
            (#0 : FirstOrder.Semiterm LX ℕ 2))))) = _
    rw [toSOAtB_or, toSOAtB_neg, toSOAtB_or, toSOAtB_neg]
    rfl
  rwa [e] at h

theorem towerStepTI_SO : Provable ACA (∀¹ (∀¹ (∀¹ stepMatrixSO))) := by
  have h : Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb
      ((∀¹ (∀¹ (∀¹ TowerSyntax.towerStepTIBody))).univCl))) :=
    lift_paLX_seg TowerSyntax.concrete_towerStepTI
  rw [TowerSyntax.emb_univCl_of_closed (by simp)] at h
  have e : toSOAt segWitness ((∀¹ (∀¹ (∀¹ TowerSyntax.towerStepTIBody))) :
      FirstOrder.Semiformula LX ℕ 0) = ∀¹ (∀¹ (∀¹ stepMatrixSO)) := by
    show ∀¹ (∀¹ (∀¹ (toSOAtB segWitness TowerSyntax.towerStepTIBody))) = _
    show ∀¹ (∀¹ (∀¹ (toSOAtB segWitness
      (∼(Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
          (#0 : FirstOrder.Semiterm LX ℕ 3) (‘(#1 + 1)’ : FirstOrder.Semiterm LX ℕ 3) #2) ⋎
        (∼(∀¹ (∼(Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
                (#0 : FirstOrder.Semiterm LX ℕ 4) #2 #3) ⋎
              Gentzen.tiUptoAt precCode₁ TowerSyntax.jumpXF
                (#0 : FirstOrder.Semiterm LX ℕ 4))) ⋎
          Gentzen.tiUptoAt precCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
            (#0 : FirstOrder.Semiterm LX ℕ 3)))))) = _
    rw [toSOAtB_or, toSOAtB_neg, toSOAtB_or, toSOAtB_neg, toSOAtB_all, toSOAtB_or,
      toSOAtB_neg]
    rfl
  rwa [e] at h

/-! ### Instances -/

/-- `0̄`, as an `LX`-term. -/
abbrev zeroLX : FirstOrder.Semiterm LX ℕ 0 := ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 0)

/-- `#0 + 1`, as an `LX`-term. -/
abbrev succLX : FirstOrder.Semiterm LX ℕ 1 := ‘(#0 + 1)’

theorem towerZeroTI_inst (tu tc : FirstOrder.Semiterm LX ℕ 0) :
    Provable ACA (∼(towerSO tu zeroLX tc) ⋎ (∼(tiSO tc) ⋎ tiSO tu)) := by
  have h := specNums zeroMatrixSO
    (fun j => unTerm ((![tu, tc] : Fin 2 → FirstOrder.Semiterm LX ℕ 0) j)) towerZeroTI_SO
  have e : (FirstOrder.Rew.subst
        (fun j => unTerm ((![tu, tc] : Fin 2 → FirstOrder.Semiterm LX ℕ 0) j))) ▹
      zeroMatrixSO = ∼(towerSO tu zeroLX tc) ⋎ (∼(tiSO tc) ⋎ tiSO tu) := by
    show (FirstOrder.Rew.subst _) ▹
      (∼(towerSO (#0 : FirstOrder.Semiterm LX ℕ 2)
          ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2) #1) ⋎
        (∼(tiSO (#1 : FirstOrder.Semiterm LX ℕ 2)) ⋎
          tiSO (#0 : FirstOrder.Semiterm LX ℕ 2))) = _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or,
      LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_neg,
      rew_towerSO (hb_subst _) (hf_subst _), rew_tiSO (hb_subst _) (hf_subst _),
      rew_tiSO (hb_subst _) (hf_subst _)]
    simp
  rwa [e] at h

theorem towerStepTI_inst (tu tk tc : FirstOrder.Semiterm LX ℕ 0) :
    Provable ACA
      (∼(towerSO tu (FirstOrder.Rew.subst ![tu, tk, tc]
          (‘(#1 + 1)’ : FirstOrder.Semiterm LX ℕ 3)) tc) ⋎
        (∼(∀¹ (∼(towerSO (#0 : FirstOrder.Semiterm LX ℕ 1)
              (FirstOrder.Rew.bShift tk) (FirstOrder.Rew.bShift tc)) ⋎
            tiJSO (#0 : FirstOrder.Semiterm LX ℕ 1))) ⋎
          tiSO tu)) := by
  have h := specNums stepMatrixSO
    (fun j => unTerm ((![tu, tk, tc] : Fin 3 → FirstOrder.Semiterm LX ℕ 0) j))
    towerStepTI_SO
  have e : (FirstOrder.Rew.subst
        (fun j => unTerm ((![tu, tk, tc] : Fin 3 → FirstOrder.Semiterm LX ℕ 0) j))) ▹
      stepMatrixSO =
      ∼(towerSO tu (FirstOrder.Rew.subst ![tu, tk, tc]
          (‘(#1 + 1)’ : FirstOrder.Semiterm LX ℕ 3)) tc) ⋎
        (∼(∀¹ (∼(towerSO (#0 : FirstOrder.Semiterm LX ℕ 1)
              (FirstOrder.Rew.bShift tk) (FirstOrder.Rew.bShift tc)) ⋎
            tiJSO (#0 : FirstOrder.Semiterm LX ℕ 1))) ⋎ tiSO tu) := by
    show (FirstOrder.Rew.subst _) ▹
      (∼(towerSO (#0 : FirstOrder.Semiterm LX ℕ 3)
          (‘(#1 + 1)’ : FirstOrder.Semiterm LX ℕ 3) #2) ⋎
        (∼(∀¹ (∼(towerSO (#0 : FirstOrder.Semiterm LX ℕ 4) #2 #3) ⋎
              tiJSO (#0 : FirstOrder.Semiterm LX ℕ 4))) ⋎
          tiSO (#0 : FirstOrder.Semiterm LX ℕ 3))) = _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or,
      LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_neg,
      rew_towerSO (hb_subst _) (hf_subst _), rew_tiSO (hb_subst _) (hf_subst _),
      Semiformula.rew_all₀, LogicalConnective.HomClass.map_or,
      LogicalConnective.HomClass.map_neg,
      rew_towerSO (ω := (FirstOrder.Rew.subst ![tu, tk, tc]).q) (q_hb (hb_subst _))
        (q_hf (hf_subst _)),
      rew_tiJSO (ω := (FirstOrder.Rew.subst ![tu, tk, tc]).q) (q_hb (hb_subst _))
        (q_hf (hf_subst _))]
    simp [FirstOrder.Rew.q_subst]
  rwa [e] at h

/-! ### The base case -/

theorem towerBase : Provable ACA (thetaAt zeroLX) := by
  show Provable ACA (∀¹ (thetaInner (FirstOrder.Rew.bShift zeroLX)
    (#0 : FirstOrder.Semiterm LX ℕ 1)))
  refine gen₁ ACA_shift₀_invariant ?_
  have e1 : Semiproposition.free₀ (thetaInner (FirstOrder.Rew.bShift zeroLX)
      (#0 : FirstOrder.Semiterm LX ℕ 1)) =
      thetaInner zeroLX (&0 : FirstOrder.Semiterm LX ℕ 0) := by
    show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹
      (thetaInner (FirstOrder.Rew.bShift zeroLX) (#0 : FirstOrder.Semiterm LX ℕ 1)) = _
    rw [rew_thetaInner (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
      hb_free hf_free]
    simp
  rw [e1]
  show Provable ACA (∀¹ (stepBody (#0 : FirstOrder.Semiterm LX ℕ 1)
    (FirstOrder.Rew.bShift zeroLX)
    (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))))
  refine gen₁ ACA_shift₀_invariant ?_
  have e2 : Semiproposition.free₀ (stepBody (#0 : FirstOrder.Semiterm LX ℕ 1)
      (FirstOrder.Rew.bShift zeroLX)
      (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))) =
      stepBody (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX (&1) := by
    show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹
      (stepBody (#0 : FirstOrder.Semiterm LX ℕ 1) (FirstOrder.Rew.bShift zeroLX)
        (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))) = _
    rw [rew_stepBody (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
      hb_free hf_free]
    simp
  rw [e2]
  -- the sequent derivation
  have hT := towerZeroTI_inst (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)
  have h1 : PSeq ACA [∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX (&1)),
      (∼(tiSO (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋎
        tiSO (&0 : FirstOrder.Semiterm LX ℕ 0))] :=
    PSeq.orInv (PSeq.of_provable hT)
  have h2 : PSeq ACA [(∼(tiSO (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋎
        tiSO (&0 : FirstOrder.Semiterm LX ℕ 0)),
      ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX (&1))] :=
    PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h1
  have h3 : PSeq ACA [∼(tiSO (&1 : FirstOrder.Semiterm LX ℕ 0)),
      tiSO (&0 : FirstOrder.Semiterm LX ℕ 0),
      ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX (&1))] :=
    PSeq.orInv h2
  have h4 : PSeq ACA [∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)),
      tiSO (&0 : FirstOrder.Semiterm LX ℕ 0),
      ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX (&1))] := by
    have key : PSeq ACA
        [Semiproposition.subst₁ (∼(toSOAtB boundWitness
            (tiX (&1 : FirstOrder.Semiterm LX ℕ 0)))) ![freeWitness],
          tiSO (&0 : FirstOrder.Semiterm LX ℕ 0),
          ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX (&1))] := by
      rw [neg_subst₁_tiBody_free]
      exact h3
    exact PSeq.exs₂ arith_freeWitness key
  have hshift : SecondOrder.Sequent.shift₁
      [∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)),
        ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX (&1))] =
      [∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)),
        ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX (&1))] := by
    simp only [SecondOrder.Sequent.shift₁, List.map_cons, List.map_nil,
      LogicalConnective.HomClass.map_neg,
      shift₁_eq_self_of_noSetFvar (noSetFvar_allTI (&1 : FirstOrder.Semiterm LX ℕ 0)),
      shift₁_eq_self_of_noSetFvar
        (noSetFvar_towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX (&1))]
  have h5 : PSeq ACA [allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
      ∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)),
      ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX (&1))] := by
    refine PSeq.all₂ ACA_shift₁_invariant ?_
    rw [hshift, free₁_tiBody]
    exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h4
  have h6 : PSeq ACA [∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)),
      allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
      ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX (&1))] :=
    PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h5
  have h7 : PSeq ACA [(∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋎
        allTI (&0 : FirstOrder.Semiterm LX ℕ 0)),
      ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX (&1))] := PSeq.or h6
  have h8 : PSeq ACA [∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX (&1)),
      (∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋎
        allTI (&0 : FirstOrder.Semiterm LX ℕ 0))] :=
    PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h7
  exact PSeq.to_provable (PSeq.or h8)

/-! ### `shift₀` on the vocabulary -/

theorem shift₀_tiSO {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.shift₀ (tiSO a) = tiSO (FirstOrder.Rew.shift a) :=
  rew_tiSO hb_shift hf_shift a

theorem shift₀_tiJSO {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.shift₀ (tiJSO a) = tiJSO (FirstOrder.Rew.shift a) :=
  rew_tiJSO hb_shift hf_shift a

theorem shift₀_allTI {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.shift₀ (allTI a) = allTI (FirstOrder.Rew.shift a) :=
  rew_allTI hb_shift hf_shift a

theorem shift₀_towerSO {n : ℕ} (u k c : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.shift₀ (towerSO u k c) =
      towerSO (FirstOrder.Rew.shift u) (FirstOrder.Rew.shift k) (FirstOrder.Rew.shift c) :=
  rew_towerSO hb_shift hf_shift u k c

theorem shift₀_thetaAt {n : ℕ} (k : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.shift₀ (thetaAt k) = thetaAt (FirstOrder.Rew.shift k) :=
  rew_thetaAt hb_shift hf_shift k

/-! ### The step case -/

/-- `&0 + 1` — the successor of the induction eigenvariable. -/
abbrev succFree : FirstOrder.Semiterm LX ℕ 0 := FirstOrder.Rew.free succLX

theorem succ_term_eq :
    FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm LX ℕ 0), &2, &1]
        (‘(#1 + 1)’ : FirstOrder.Semiterm LX ℕ 3) =
      FirstOrder.Rew.shift (FirstOrder.Rew.shift succFree) := by
  simp

theorem towerStep : Provable ACA (∀¹ (theta 🡒 thetaAt succLX)) := by
  refine gen₁ ACA_shift₀_invariant ?_
  have e0 : Semiproposition.free₀ (theta 🡒 thetaAt succLX) =
      (thetaAt (&0 : FirstOrder.Semiterm LX ℕ 0) 🡒 thetaAt succFree) := by
    show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹
      (thetaAt (#0 : FirstOrder.Semiterm LX ℕ 1) 🡒 thetaAt succLX) = _
    rw [LogicalConnective.HomClass.map_imply,
      rew_thetaAt (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0)) hb_free hf_free,
      rew_thetaAt (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0)) hb_free hf_free]
    simp
  rw [e0]
  -- abbreviations
  set K : FirstOrder.Semiterm LX ℕ 0 :=
    FirstOrder.Rew.shift (FirstOrder.Rew.shift succFree) with hK
  set W : Proposition ℒₒᵣ :=
    ∀¹ (∼(towerSO (#0 : FirstOrder.Semiterm LX ℕ 1)
        (FirstOrder.Rew.bShift (&2 : FirstOrder.Semiterm LX ℕ 0))
        (FirstOrder.Rew.bShift (&1 : FirstOrder.Semiterm LX ℕ 0))) ⋎
      tiJSO (#0 : FirstOrder.Semiterm LX ℕ 1)) with hW
  -- the sequent after the two eigenvariable steps
  have main : PSeq ACA [stepBody (&0 : FirstOrder.Semiterm LX ℕ 0) K (&1),
      ∼(thetaAt (&2 : FirstOrder.Semiterm LX ℕ 0))] := by
    -- S : the sequent after `all₂` on the conclusion
    have hS := towerStepTI_inst (&0 : FirstOrder.Semiterm LX ℕ 0) (&2) (&1)
    rw [succ_term_eq] at hS
    -- the four-element sequent `S`
    have hshift₁ : SecondOrder.Sequent.shift₁
        [∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)),
          ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) K (&1)),
          ∼(thetaAt (&2 : FirstOrder.Semiterm LX ℕ 0))] =
        [∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)),
          ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) K (&1)),
          ∼(thetaAt (&2 : FirstOrder.Semiterm LX ℕ 0))] := by
      simp only [SecondOrder.Sequent.shift₁, List.map_cons, List.map_nil,
        LogicalConnective.HomClass.map_neg,
        shift₁_eq_self_of_noSetFvar (noSetFvar_allTI (&1 : FirstOrder.Semiterm LX ℕ 0)),
        shift₁_eq_self_of_noSetFvar
          (noSetFvar_towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) K (&1)),
        shift₁_eq_self_of_noSetFvar
          (noSetFvar_thetaAt (&2 : FirstOrder.Semiterm LX ℕ 0))]
    have hcut : PSeq ACA [tiSO (&0 : FirstOrder.Semiterm LX ℕ 0),
        ∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)),
        ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) K (&1)),
        ∼(thetaAt (&2 : FirstOrder.Semiterm LX ℕ 0))] := by
      refine PSeq.cut W ?_ ?_
      · -- positive branch: prove `W`
        refine PSeq.all₁ ACA_shift₀_invariant ?_
        have hfree : Semiproposition.free₀
            (∼(towerSO (#0 : FirstOrder.Semiterm LX ℕ 1)
                (FirstOrder.Rew.bShift (&2 : FirstOrder.Semiterm LX ℕ 0))
                (FirstOrder.Rew.bShift (&1 : FirstOrder.Semiterm LX ℕ 0))) ⋎
              tiJSO (#0 : FirstOrder.Semiterm LX ℕ 1)) =
            (∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&3) (&2)) ⋎
              tiJSO (&0 : FirstOrder.Semiterm LX ℕ 0)) := by
          show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹ _ = _
          rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
            rew_towerSO (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
              hb_free hf_free,
            rew_tiJSO (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
              hb_free hf_free]
          simp
        have hsh : SecondOrder.Sequent.shift₀
            [tiSO (&0 : FirstOrder.Semiterm LX ℕ 0),
              ∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)),
              ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) K (&1)),
              ∼(thetaAt (&2 : FirstOrder.Semiterm LX ℕ 0))] =
            [tiSO (&1 : FirstOrder.Semiterm LX ℕ 0),
              ∼(allTI (&2 : FirstOrder.Semiterm LX ℕ 0)),
              ∼(towerSO (&1 : FirstOrder.Semiterm LX ℕ 0)
                (FirstOrder.Rew.shift K) (&2)),
              ∼(thetaAt (&3 : FirstOrder.Semiterm LX ℕ 0))] := by
          simp only [SecondOrder.Sequent.shift₀, List.map_cons, List.map_nil,
            LogicalConnective.HomClass.map_neg, shift₀_tiSO, shift₀_allTI,
            shift₀_towerSO, shift₀_thetaAt]
          norm_num
        rw [hfree, hsh]
        refine PSeq.or ?_
        -- the working sequent
        refine PSeq.wk (Γ := [∼(thetaAt (&3 : FirstOrder.Semiterm LX ℕ 0)),
          ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&3) (&2)),
          tiJSO (&0 : FirstOrder.Semiterm LX ℕ 0),
          tiSO (&1 : FirstOrder.Semiterm LX ℕ 0),
          ∼(allTI (&2 : FirstOrder.Semiterm LX ℕ 0)),
          ∼(towerSO (&1 : FirstOrder.Semiterm LX ℕ 0) (FirstOrder.Rew.shift K) (&2))])
          (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) ?_
        -- instantiate the induction hypothesis
        refine PSeq.exs₁ (&2 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) ?_
        have e3 : (FirstOrder.Rew.subst ![(&2 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)] ▹
            (∼(thetaInner (FirstOrder.Rew.bShift (&3 : FirstOrder.Semiterm LX ℕ 0))
              (#0 : FirstOrder.Semiterm LX ℕ 1))) : Proposition ℒₒᵣ) =
            ∼(thetaInner (&3 : FirstOrder.Semiterm LX ℕ 0) (&2)) := by
          show (FirstOrder.Rew.subst ![(&2 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)]) ▹
            (∼(thetaInner _ _)) = _
          rw [LogicalConnective.HomClass.map_neg,
            rew_thetaInner (ω := FirstOrder.Rew.subst
              ![(&2 : FirstOrder.Semiterm LX ℕ 0)]) (fun i => by simp) (fun x => by simp)]
          simp
        show PSeq ACA ((FirstOrder.Rew.subst ![(&2 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)] ▹
          (∼(thetaInner (FirstOrder.Rew.bShift (&3 : FirstOrder.Semiterm LX ℕ 0))
            (#0 : FirstOrder.Semiterm LX ℕ 1))) : Proposition ℒₒᵣ) :: _)
        rw [e3]
        refine PSeq.exs₁ (&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) ?_
        have e4 : (FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)] ▹
            (∼(stepBody (#0 : FirstOrder.Semiterm LX ℕ 1)
              (FirstOrder.Rew.bShift (&3 : FirstOrder.Semiterm LX ℕ 0))
              (FirstOrder.Rew.bShift (&2 : FirstOrder.Semiterm LX ℕ 0)))) :
              Proposition ℒₒᵣ) =
            (towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&3) (&2) ⋏
              (allTI (&2 : FirstOrder.Semiterm LX ℕ 0) ⋏
                ∼(allTI (&0 : FirstOrder.Semiterm LX ℕ 0)))) := by
          show (FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)]) ▹
            (∼(stepBody _ _ _)) = _
          rw [LogicalConnective.HomClass.map_neg,
            rew_stepBody (ω := FirstOrder.Rew.subst
              ![(&0 : FirstOrder.Semiterm LX ℕ 0)]) (fun i => by simp) (fun x => by simp)]
          show ∼(∼(towerSO _ _ _) ⋎ (∼(allTI _) ⋎ allTI _)) = _
          show (∼(∼(towerSO _ _ _))) ⋏ ((∼(∼(allTI _))) ⋏ ∼(allTI _)) = _
          rw [Semiformula.neg_neg, Semiformula.neg_neg]
          simp
        show PSeq ACA ((FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)] ▹
          (∼(stepBody (#0 : FirstOrder.Semiterm LX ℕ 1)
            (FirstOrder.Rew.bShift (&3 : FirstOrder.Semiterm LX ℕ 0))
            (FirstOrder.Rew.bShift (&2 : FirstOrder.Semiterm LX ℕ 0)))) :
            Proposition ℒₒᵣ) :: _)
        rw [e4]
        refine PSeq.and (PSeq.id (φ := towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&3) (&2))
          (by simp) (by simp)) (PSeq.and
            (PSeq.id (φ := allTI (&2 : FirstOrder.Semiterm LX ℕ 0)) (by simp) (by simp)) ?_)
        -- arithmetical comprehension: instantiate `∀²X TI(v,X)` at `Jump(X₀)`
        have key : PSeq ACA
            (Semiproposition.subst₁ (∼(toSOAtB boundWitness
                (tiX (&0 : FirstOrder.Semiterm LX ℕ 0)))) ![jumpWitness] ::
              [∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&3) (&2)),
                tiJSO (&0 : FirstOrder.Semiterm LX ℕ 0),
                tiSO (&1 : FirstOrder.Semiterm LX ℕ 0),
                ∼(allTI (&2 : FirstOrder.Semiterm LX ℕ 0)),
                ∼(towerSO (&1 : FirstOrder.Semiterm LX ℕ 0)
                  (FirstOrder.Rew.shift K) (&2))]) := by
          rw [neg_subst₁_tiBody_jump]
          exact PSeq.id (φ := tiJSO (&0 : FirstOrder.Semiterm LX ℕ 0)) (by simp) (by simp)
        exact PSeq.exs₂ arith_jumpWitness key
      · -- negative branch: `∼W` from the lifted successor step
        have g1 : PSeq ACA [∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) K (&1)),
            (∼W ⋎ tiSO (&0 : FirstOrder.Semiterm LX ℕ 0))] :=
          PSeq.orInv (PSeq.of_provable hS)
        have g2 : PSeq ACA [(∼W ⋎ tiSO (&0 : FirstOrder.Semiterm LX ℕ 0)),
            ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) K (&1))] :=
          PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) g1
        have g3 : PSeq ACA [∼W, tiSO (&0 : FirstOrder.Semiterm LX ℕ 0),
            ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) K (&1))] := PSeq.orInv g2
        exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) g3
    -- close the `∀²`
    have h5 : PSeq ACA [allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
        ∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)),
        ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) K (&1)),
        ∼(thetaAt (&2 : FirstOrder.Semiterm LX ℕ 0))] := by
      refine PSeq.all₂ ACA_shift₁_invariant ?_
      rw [hshift₁, free₁_tiBody]
      exact hcut
    have h6 : PSeq ACA [∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)),
        allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
        ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) K (&1)),
        ∼(thetaAt (&2 : FirstOrder.Semiterm LX ℕ 0))] :=
      PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h5
    have h7 : PSeq ACA [(∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋎
          allTI (&0 : FirstOrder.Semiterm LX ℕ 0)),
        ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) K (&1)),
        ∼(thetaAt (&2 : FirstOrder.Semiterm LX ℕ 0))] := PSeq.or h6
    have h8 : PSeq ACA [∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) K (&1)),
        (∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋎
          allTI (&0 : FirstOrder.Semiterm LX ℕ 0)),
        ∼(thetaAt (&2 : FirstOrder.Semiterm LX ℕ 0))] :=
      PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h7
    exact PSeq.or h8
  -- wrap the two eigenvariables back up
  have step2 : PSeq ACA [thetaInner (FirstOrder.Rew.shift succFree)
      (&0 : FirstOrder.Semiterm LX ℕ 0),
      ∼(thetaAt (&1 : FirstOrder.Semiterm LX ℕ 0))] := by
    refine PSeq.all₁ ACA_shift₀_invariant ?_
    have hfree : Semiproposition.free₀ (stepBody (#0 : FirstOrder.Semiterm LX ℕ 1)
        (FirstOrder.Rew.bShift (FirstOrder.Rew.shift succFree))
        (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))) =
        stepBody (&0 : FirstOrder.Semiterm LX ℕ 0) K (&1) := by
      show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹ (stepBody _ _ _) = _
      rw [rew_stepBody (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
        hb_free hf_free]
      simp [hK]
    have hsh : SecondOrder.Sequent.shift₀
        [∼(thetaAt (&1 : FirstOrder.Semiterm LX ℕ 0))] =
        [∼(thetaAt (&2 : FirstOrder.Semiterm LX ℕ 0))] := by
      simp only [SecondOrder.Sequent.shift₀, List.map_cons, List.map_nil,
        LogicalConnective.HomClass.map_neg, shift₀_thetaAt]
      norm_num
    show PSeq ACA (Semiproposition.free₀ (stepBody (#0 : FirstOrder.Semiterm LX ℕ 1)
      (FirstOrder.Rew.bShift (FirstOrder.Rew.shift succFree))
      (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))) ::
        SecondOrder.Sequent.shift₀ [∼(thetaAt (&1 : FirstOrder.Semiterm LX ℕ 0))])
    rw [hfree, hsh]
    exact main
  have step3 : PSeq ACA [thetaAt succFree,
      ∼(thetaAt (&0 : FirstOrder.Semiterm LX ℕ 0))] := by
    refine PSeq.all₁ ACA_shift₀_invariant ?_
    have hfree : Semiproposition.free₀ (thetaInner
        (FirstOrder.Rew.bShift succFree) (#0 : FirstOrder.Semiterm LX ℕ 1)) =
        thetaInner (FirstOrder.Rew.shift succFree) (&0 : FirstOrder.Semiterm LX ℕ 0) := by
      show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹ (thetaInner _ _) = _
      rw [rew_thetaInner (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
        hb_free hf_free]
      simp
    have hsh : SecondOrder.Sequent.shift₀
        [∼(thetaAt (&0 : FirstOrder.Semiterm LX ℕ 0))] =
        [∼(thetaAt (&1 : FirstOrder.Semiterm LX ℕ 0))] := by
      simp only [SecondOrder.Sequent.shift₀, List.map_cons, List.map_nil,
        LogicalConnective.HomClass.map_neg, shift₀_thetaAt]
      norm_num
    show PSeq ACA (Semiproposition.free₀ (thetaInner
      (FirstOrder.Rew.bShift succFree) (#0 : FirstOrder.Semiterm LX ℕ 1)) ::
        SecondOrder.Sequent.shift₀ [∼(thetaAt (&0 : FirstOrder.Semiterm LX ℕ 0))])
    rw [hfree, hsh]
    exact step2
  exact PSeq.to_provable (PSeq.or
    (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) step3))

/-! ### (⋆⋆) -/

/-- **The internal ω-tower induction.**

    `ACA ⊢ ∀k ∀c ∀u (Tower(u,k,c) → (∀²X TI(≺₁,c,X)) → (∀²X TI(≺₁,u,X)))`

This is the *only* use of the full second-order induction scheme in the upper
bound, and the exact point at which `ACA` outruns `ACA₀`: the induction formula
`θ` is `Π¹₁`, and `ACA₀`'s `setInduction` is induction for sets only.  Inside
the step, the instantiation of `∀²X TI(≺₁,v,X)` at the arithmetical witness
`Jump(X₀)` *is* arithmetical comprehension — the `exs₂` rule of `ACA/LK.lean`,
with no appeal to a comprehension axiom. -/
theorem towerInduction : Provable ACA (∀¹ theta) := by
  have hax : Provable ACA (indBody theta) :=
    ofAxiom (indScheme₂_mem_ACA (N := 0) (n := 0) noSetFvar_theta shift₀_theta)
  have hbase : Provable ACA
      (FirstOrder.Rew.subst (indZeroSub 0) ▹ theta) := by
    have e : (FirstOrder.Rew.subst (indZeroSub 0) ▹ theta : Proposition ℒₒᵣ) =
        thetaAt zeroLX := by
      have hv : (fun j => unTerm ((![zeroLX] : Fin 1 → FirstOrder.Semiterm LX ℕ 0) j)) =
          indZeroSub 0 := by
        funext j
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        simp [indZeroSub]
      rw [← hv]
      show (FirstOrder.Rew.subst _) ▹ (thetaAt (#0 : FirstOrder.Semiterm LX ℕ 1)) = _
      rw [rew_thetaAt (ω := FirstOrder.Rew.subst ![zeroLX]) (hb_subst _) (hf_subst _)]
      simp
    rw [e]
    exact towerBase
  have hstep : Provable ACA
      (∀¹ (theta 🡒 FirstOrder.Rew.subst (indSuccSub 0) ▹ theta)) := by
    have e : (FirstOrder.Rew.subst (indSuccSub 0) ▹ theta : Semiproposition ℒₒᵣ 0 1) =
        thetaAt succLX := by
      have hv : (fun j => unTerm ((![succLX] : Fin 1 → FirstOrder.Semiterm LX ℕ 1) j)) =
          indSuccSub 0 := by
        funext j
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        simp [indSuccSub]
      rw [← hv]
      show (FirstOrder.Rew.subst _) ▹ (thetaAt (#0 : FirstOrder.Semiterm LX ℕ 1)) = _
      rw [rew_thetaAt (ω := FirstOrder.Rew.subst ![succLX]) (hb_subst _) (hf_subst _)]
      simp
    rw [e]
    exact towerStep
  exact mp hax (andIntro hbase hstep)

end OrdinalAnalysis.ACA
