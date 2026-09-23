/-
  **The ε-progressiveness (Prog), the transfinite
  induction for it (TIψ), and the conclusion (Final)** —

      `ACA ⊢ ∀²X TI(≺₁, ε̄_c, X)` for every external `c < ε₀`,

  which is the single remaining hypothesis of
  `ACA/UpperBound.lean`'s `aca_theorem_of_ti_epsilon`.

  The `Π¹₁` induction formula is

      `ψ₀(g) :≡ ∀u (Eps(u, g) → ∀²X TI(≺₁, u, X))`,

  the ε-value of `g` being named by the internal graph `Eps` of
  `Gentzen/InternalEpsMonoCode.lean` rather than by a term (there is no
  ε-function symbol in `ℒₒᵣ`).

  Three layers, as in `ACA/TowerInduction.lean`.

  * **Layer 0** is `Gentzen/ProgStep.lean`: the cover with its case split
    (`Good`), presented as an implication whose hypothesis is *universal*, and
    the successor step of the ordering packaged with transfinite induction.
  * **Layer 1** here is the second-order vocabulary (`psiAt`, `belowPsi`,
    `progPsi`), its rewriting lemmas, and the `ξ = Empty` presentation `psiE`
    that `ACA/Lift.lean`'s `lift_paLX` demands of a parameter with set
    quantifiers (`lift_paLX₀` cannot take one: it wants `Arith`).
  * **Layer 2** is the derivation: three *closed* `ACA`-theorems
    (`succAllTI`, `goodAllTI`, and `TowerInduction.towerInduction`), and then
    (Prog) itself, whose second-order moves are one `gen₂`, one `exs₂` and a
    handful of `all₁`/`exs₁`/`cut`.
-/
import OrdinalAnalysis.ACA.TowerInduction
import OrdinalAnalysis.Gentzen.ProgStep

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open OrdinalAnalysis.Gentzen (LX Xat paLX)
open OrdinalAnalysis.Gentzen.CodedVeblen (precCode₁ freeVariables_precCode₁)
open OrdinalAnalysis.Gentzen.CodedVeblenJump (addCode₁)
open OrdinalAnalysis.Gentzen.InternalEpsMonoCode (epsCode₁ epsAt epsDef₁)
open OrdinalAnalysis.Gentzen.VeblenSuccStep (baseCode₁)
open OrdinalAnalysis.Gentzen.ProgStep
open OrdinalAnalysis.ACA.TowerSyntax

/-! ## Layer 1a: closedness of the new first-order codes -/

@[simp] theorem freeVariables_epsCode₁ : epsCode₁.freeVariables = ∅ := by
  simp [epsCode₁, Gentzen.CodedNotation.liftCode]

@[simp] theorem freeVariables_baseCode₁ : baseCode₁.freeVariables = ∅ := by
  simp [baseCode₁, Gentzen.CodedNotation.liftCode]

theorem freeVariables_epsAt {n : ℕ} {y g : FirstOrder.Semiterm LX ℕ n}
    (hy : y.freeVariables = ∅) (hg : g.freeVariables = ∅) :
    (epsAt epsCode₁ y g).freeVariables = ∅ :=
  Gentzen.LowerSyntax.freeVariables_rew_eq_empty _ freeVariables_epsCode₁ (fun i => by
    fin_cases i
    · simpa using hy
    · simpa using hg)

theorem freeVariables_goodBody : goodBody.freeVariables = ∅ := by
  have h1 : (Gentzen.formulaAt baseCode₁
      ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2)).freeVariables = ∅ :=
    freeVariables_formulaAt freeVariables_baseCode₁ (by simp)
  have h2 : (Gentzen.addAt addCode₁ (#0 : FirstOrder.Semiterm LX ℕ 2)
      ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2)
      ((Gentzen.VNoteBridge.gamma0Code 1 : ℕ) :
        FirstOrder.Semiterm LX ℕ 2)).freeVariables = ∅ :=
    freeVariables_addAt (by simp) (by simp) (by simp)
  have h3 : (Gentzen.precAt precCode₁ (#1 : FirstOrder.Semiterm LX ℕ 4) #3).freeVariables = ∅ :=
    Gentzen.LowerSyntax.freeVariables_precAt_eq_empty freeVariables_precCode₁ (by simp) (by simp)
  have h4 : (Gentzen.formulaAt baseCode₁
      (#0 : FirstOrder.Semiterm LX ℕ 4)).freeVariables = ∅ :=
    freeVariables_formulaAt freeVariables_baseCode₁ (by simp)
  have h5 : (epsAt epsCode₁ (#0 : FirstOrder.Semiterm LX ℕ 4) #1).freeVariables = ∅ :=
    freeVariables_epsAt (by simp) (by simp)
  have h6 : (Gentzen.addAt addCode₁ (#2 : FirstOrder.Semiterm LX ℕ 4) #0
      ((Gentzen.VNoteBridge.gamma0Code 1 : ℕ) :
        FirstOrder.Semiterm LX ℕ 4)).freeVariables = ∅ :=
    freeVariables_addAt (by simp) (by simp) (by simp)
  show ((Gentzen.formulaAt baseCode₁ ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2) ⋏
      Gentzen.addAt addCode₁ (#0 : FirstOrder.Semiterm LX ℕ 2)
        ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2)
        ((Gentzen.VNoteBridge.gamma0Code 1 : ℕ) : FirstOrder.Semiterm LX ℕ 2)) ⋎
    (∃¹ ∃¹
      (Gentzen.precAt precCode₁ (#1 : FirstOrder.Semiterm LX ℕ 4) #3 ⋏
        (Gentzen.formulaAt baseCode₁ (#0 : FirstOrder.Semiterm LX ℕ 4) ⋏
          (epsAt epsCode₁ (#0 : FirstOrder.Semiterm LX ℕ 4) #1 ⋏
            Gentzen.addAt addCode₁ (#2 : FirstOrder.Semiterm LX ℕ 4) #0
              ((Gentzen.VNoteBridge.gamma0Code 1 : ℕ) :
                FirstOrder.Semiterm LX ℕ 4)))))).freeVariables = ∅
  simp [h1, h2, h3, h4, h5, h6]

/-! ## Layer 1b: the second-order vocabulary -/

/-- `Eps(u, g)`, lifted. -/
def epsSO {n : ℕ} (u g : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  toSOAt segWitness (epsAt epsCode₁ u g)

/-- `Add(z, x, y)`, lifted. -/
def addSO {n : ℕ} (z x y : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  toSOAt segWitness (Gentzen.addAt addCode₁ z x y)

/-- `Base(e)`, lifted. -/
def baseSO {n : ℕ} (e : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  toSOAt segWitness (Gentzen.formulaAt baseCode₁ e)

/-- `y ≺₁ x`, lifted. -/
def precSOv {n : ℕ} (y x : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  toSOAt segWitness (Gentzen.precAt precCode₁ y x)

/-- `Good(s, g)`, lifted. -/
noncomputable def goodSO {n : ℕ} (s g : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  toSOAt segWitness (goodAt s g)

/-- `X(t)`, lifted at the free set variable. -/
def xSO {n : ℕ} (t : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  toSOAt segWitness (Xat t)

/-- `Prog(≺₁, X)`, lifted. -/
def progSOX {n : ℕ} : Semiproposition ℒₒᵣ 0 n :=
  toSOAt segWitness (Gentzen.progAt (n := n) precCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)))

/-- `Below(X, b)`, lifted. -/
def belowSOX {n : ℕ} (b : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  toSOAt segWitness
    (Gentzen.belowAt precCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) b)

/-- **`ψ₀(g)`** — the `Π¹₁` induction formula. -/
def psiAt {n : ℕ} (g : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  ∀¹ (∼(epsSO (#0 : FirstOrder.Semiterm LX ℕ (n + 1)) (FirstOrder.Rew.bShift g)) ⋎
      allTI (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))

/-- `Below(ψ₀, b)`. -/
def belowPsi {n : ℕ} (b : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  ∀¹ (∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ (n + 1)) (FirstOrder.Rew.bShift b)) ⋎
      psiAt (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))

/-- `Prog(≺₁, ψ₀)` — the goal of (Prog). -/
def progPsi {n : ℕ} : Semiproposition ℒₒᵣ 0 n :=
  ∀¹ (∼(belowPsi (#0 : FirstOrder.Semiterm LX ℕ (n + 1))) ⋎
      psiAt (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))

/-! ### Rewriting -/

section Rew

variable {n₁ n₂ : ℕ} {ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂} {ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂}

theorem rew_epsSO (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (u g : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (epsSO u g) = epsSO (ω u) (ω g) := by
  have hv : (fun i => ω ((![u, g] : Fin 2 → FirstOrder.Semiterm LX ℕ n₁) i)) = ![ω u, ω g] := by
    funext i; fin_cases i <;> rfl
  show ω' ▹ (toSOAt segWitness (FirstOrder.Rew.subst ![u, g] ▹ epsCode₁)) = _
  rw [← toSOAtB_rew hb hf, rew_subst_closed freeVariables_epsCode₁ ω ![u, g], hv]
  rfl

theorem rew_addSO (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (z x y : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (addSO z x y) = addSO (ω z) (ω x) (ω y) := by
  have hv : (fun i => ω ((![z, x, y] : Fin 3 → FirstOrder.Semiterm LX ℕ n₁) i)) =
      ![ω z, ω x, ω y] := by
    funext i; fin_cases i <;> rfl
  show ω' ▹ (toSOAt segWitness (FirstOrder.Rew.subst ![z, x, y] ▹ addCode₁)) = _
  rw [← toSOAtB_rew hb hf, rew_subst_closed freeVariables_addCode₁ ω ![z, x, y], hv]
  rfl

theorem rew_baseSO (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (e : FirstOrder.Semiterm LX ℕ n₁) : ω' ▹ (baseSO e) = baseSO (ω e) := by
  show ω' ▹ (toSOAt segWitness (Gentzen.formulaAt baseCode₁ e)) = _
  rw [← toSOAtB_rew hb hf, rew_formulaAt freeVariables_baseCode₁]
  rfl

theorem rew_precSOv (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (y x : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (precSOv y x) = precSOv (ω y) (ω x) := by
  show ω' ▹ (toSOAt segWitness (Gentzen.precAt precCode₁ y x)) = _
  rw [← toSOAtB_rew hb hf, rew_precAt' freeVariables_precCode₁]
  rfl

theorem rew_goodSO (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (s g : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (goodSO s g) = goodSO (ω s) (ω g) := by
  have hv : (fun i => ω ((![s, g] : Fin 2 → FirstOrder.Semiterm LX ℕ n₁) i)) = ![ω s, ω g] := by
    funext i; fin_cases i <;> rfl
  show ω' ▹ (toSOAt segWitness (FirstOrder.Rew.subst ![s, g] ▹ goodBody)) = _
  rw [← toSOAtB_rew hb hf, rew_subst_closed freeVariables_goodBody ω ![s, g], hv]
  rfl

theorem rew_xSO (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (t : FirstOrder.Semiterm LX ℕ n₁) : ω' ▹ (xSO t) = xSO (ω t) := by
  show ω' ▹ (toSOAt segWitness (Xat t)) = _
  rw [← toSOAtB_rew hb hf]
  rfl

theorem rew_progSOX (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x) :
    ω' ▹ (progSOX : Semiproposition ℒₒᵣ 0 n₁) = (progSOX : Semiproposition ℒₒᵣ 0 n₂) := by
  show ω' ▹ (toSOAt segWitness (Gentzen.progAt (n := n₁) precCode₁
    (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)))) = _
  rw [← toSOAtB_rew hb hf, rew_progAt freeVariables_precCode₁ (by simp)]
  rfl

theorem rew_belowSOX (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (b : FirstOrder.Semiterm LX ℕ n₁) : ω' ▹ (belowSOX b) = belowSOX (ω b) := by
  show ω' ▹ (toSOAt segWitness (Gentzen.belowAt precCode₁
    (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) b)) = _
  rw [← toSOAtB_rew hb hf, rew_belowAt freeVariables_precCode₁ (by simp)]
  rfl

theorem rew_psiAt (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (g : FirstOrder.Semiterm LX ℕ n₁) : ω' ▹ (psiAt g) = psiAt (ω g) := by
  show ω' ▹ (∀¹ (∼(epsSO (#0 : FirstOrder.Semiterm LX ℕ (n₁ + 1))
    (FirstOrder.Rew.bShift g)) ⋎ allTI (#0 : FirstOrder.Semiterm LX ℕ (n₁ + 1)))) = _
  rw [Semiformula.rew_all₀, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, rew_epsSO (q_hb hb) (q_hf hf),
    rew_allTI (q_hb hb) (q_hf hf), q_bShift]
  show ∀¹ (∼(epsSO (ω.q #0) (FirstOrder.Rew.bShift (ω g))) ⋎ allTI (ω.q #0)) = _
  simp only [FirstOrder.Rew.q_bvar_zero]
  rfl

theorem rew_belowPsi (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (b : FirstOrder.Semiterm LX ℕ n₁) : ω' ▹ (belowPsi b) = belowPsi (ω b) := by
  show ω' ▹ (∀¹ (∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ (n₁ + 1))
    (FirstOrder.Rew.bShift b)) ⋎ psiAt (#0 : FirstOrder.Semiterm LX ℕ (n₁ + 1)))) = _
  rw [Semiformula.rew_all₀, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, rew_precSOv (q_hb hb) (q_hf hf),
    rew_psiAt (q_hb hb) (q_hf hf), q_bShift]
  show ∀¹ (∼(precSOv (ω.q #0) (FirstOrder.Rew.bShift (ω b))) ⋎ psiAt (ω.q #0)) = _
  simp only [FirstOrder.Rew.q_bvar_zero]
  rfl

theorem rew_progPsi (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x) :
    ω' ▹ (progPsi : Semiproposition ℒₒᵣ 0 n₁) = (progPsi : Semiproposition ℒₒᵣ 0 n₂) := by
  show ω' ▹ (∀¹ (∼(belowPsi (#0 : FirstOrder.Semiterm LX ℕ (n₁ + 1))) ⋎
    psiAt (#0 : FirstOrder.Semiterm LX ℕ (n₁ + 1)))) = _
  rw [Semiformula.rew_all₀, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, rew_belowPsi (q_hb hb) (q_hf hf),
    rew_psiAt (q_hb hb) (q_hf hf)]
  show ∀¹ (∼(belowPsi (ω.q #0)) ⋎ psiAt (ω.q #0)) = _
  simp only [FirstOrder.Rew.q_bvar_zero]
  rfl

end Rew

/-! ### `NoSetFvar` -/

theorem epsSO_eq {n : ℕ} (u g : FirstOrder.Semiterm LX ℕ n) :
    epsSO u g =
      FirstOrder.Rew.subst ![unTerm u, unTerm g] ▹
        (lift (FirstOrder.Rewriting.emb epsDef₁.val) : Semiproposition ℒₒᵣ 0 2) := by
  show toSOAtB segWitness (FirstOrder.Rew.subst ![u, g] ▹
    (Gentzen.CodedNotation.liftCode epsDef₁)) = _
  rw [toSOAtB_rew (ω := FirstOrder.Rew.subst ![u, g])
      (ω' := FirstOrder.Rew.subst ![unTerm u, unTerm g])
      (fun i => by fin_cases i <;> simp) (fun _ => by simp),
    toSOAtB_liftCode]

theorem addSO_eq {n : ℕ} (z x y : FirstOrder.Semiterm LX ℕ n) :
    addSO z x y =
      FirstOrder.Rew.subst ![unTerm z, unTerm x, unTerm y] ▹
        (lift (FirstOrder.Rewriting.emb
          Gentzen.InternalVNoteJump.safeIadd₁Def.val) : Semiproposition ℒₒᵣ 0 3) := by
  show toSOAtB segWitness (FirstOrder.Rew.subst ![z, x, y] ▹
    (Gentzen.CodedNotation.liftCode Gentzen.InternalVNoteJump.safeIadd₁Def)) = _
  rw [toSOAtB_rew (ω := FirstOrder.Rew.subst ![z, x, y])
      (ω' := FirstOrder.Rew.subst ![unTerm z, unTerm x, unTerm y])
      (fun i => by fin_cases i <;> simp) (fun _ => by simp),
    toSOAtB_liftCode]

theorem baseSO_eq {n : ℕ} (e : FirstOrder.Semiterm LX ℕ n) :
    baseSO e =
      FirstOrder.Rew.subst ![unTerm e] ▹
        (lift (FirstOrder.Rewriting.emb
          Gentzen.VeblenSuccStep.baseDef₁.val) : Semiproposition ℒₒᵣ 0 1) := by
  show toSOAtB segWitness (FirstOrder.Rew.subst ![e] ▹
    (Gentzen.CodedNotation.liftCode Gentzen.VeblenSuccStep.baseDef₁)) = _
  rw [toSOAtB_rew (ω := FirstOrder.Rew.subst ![e])
      (ω' := FirstOrder.Rew.subst ![unTerm e])
      (fun i => by fin_cases i; simp) (fun _ => by simp),
    toSOAtB_liftCode]

theorem precSOv_eq {n : ℕ} (y x : FirstOrder.Semiterm LX ℕ n) :
    precSOv y x =
      FirstOrder.Rew.subst ![unTerm y, unTerm x] ▹
        (lift (FirstOrder.Rewriting.emb
          Gentzen.InternalVNote.precDef₁.val) : Semiproposition ℒₒᵣ 0 2) := by
  show toSOAtB segWitness (FirstOrder.Rew.subst ![y, x] ▹
    (Gentzen.CodedNotation.liftCode Gentzen.InternalVNote.precDef₁)) = _
  rw [toSOAtB_rew (ω := FirstOrder.Rew.subst ![y, x])
      (ω' := FirstOrder.Rew.subst ![unTerm y, unTerm x])
      (fun i => by fin_cases i <;> simp) (fun _ => by simp),
    toSOAtB_liftCode]

theorem goodSO_eq {n : ℕ} (s g : FirstOrder.Semiterm LX ℕ n) :
    goodSO s g =
      FirstOrder.Rew.subst ![unTerm s, unTerm g] ▹
        (lift arithGoodBody : Semiproposition ℒₒᵣ 0 2) := by
  show toSOAtB segWitness (FirstOrder.Rew.subst ![s, g] ▹ goodBody) = _
  rw [toSOAtB_rew (ω := FirstOrder.Rew.subst ![s, g])
      (ω' := FirstOrder.Rew.subst ![unTerm s, unTerm g])
      (fun i => by fin_cases i <;> simp) (fun _ => by simp),
    ← goodBody_eq_lMap, toSOAtB_lMap]

theorem noSetFvar_epsSO {n : ℕ} (u g : FirstOrder.Semiterm LX ℕ n) :
    NoSetFvar (epsSO u g) := by
  rw [epsSO_eq]; exact (noSetFvar_rew _ _).mpr (noSetFvar_lift _)

theorem noSetFvar_addSO {n : ℕ} (z x y : FirstOrder.Semiterm LX ℕ n) :
    NoSetFvar (addSO z x y) := by
  rw [addSO_eq]; exact (noSetFvar_rew _ _).mpr (noSetFvar_lift _)

theorem noSetFvar_baseSO {n : ℕ} (e : FirstOrder.Semiterm LX ℕ n) :
    NoSetFvar (baseSO e) := by
  rw [baseSO_eq]; exact (noSetFvar_rew _ _).mpr (noSetFvar_lift _)

theorem noSetFvar_precSOv {n : ℕ} (y x : FirstOrder.Semiterm LX ℕ n) :
    NoSetFvar (precSOv y x) := by
  rw [precSOv_eq]; exact (noSetFvar_rew _ _).mpr (noSetFvar_lift _)

theorem noSetFvar_goodSO {n : ℕ} (s g : FirstOrder.Semiterm LX ℕ n) :
    NoSetFvar (goodSO s g) := by
  rw [goodSO_eq]; exact (noSetFvar_rew _ _).mpr (noSetFvar_lift _)

theorem noSetFvar_psiAt {n : ℕ} (g : FirstOrder.Semiterm LX ℕ n) : NoSetFvar (psiAt g) := by
  show NoSetFvar (∀¹ (∼(epsSO _ _) ⋎ allTI _))
  simp [noSetFvar_epsSO, noSetFvar_allTI]

theorem noSetFvar_belowPsi {n : ℕ} (b : FirstOrder.Semiterm LX ℕ n) :
    NoSetFvar (belowPsi b) := by
  show NoSetFvar (∀¹ (∼(precSOv _ _) ⋎ psiAt _))
  simp [noSetFvar_precSOv, noSetFvar_psiAt]

/-! ### `shift₀` on the vocabulary -/

theorem shift₀_epsSO {n : ℕ} (u g : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.shift₀ (epsSO u g) =
      epsSO (FirstOrder.Rew.shift u) (FirstOrder.Rew.shift g) :=
  rew_epsSO hb_shift hf_shift u g

theorem shift₀_addSO {n : ℕ} (z x y : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.shift₀ (addSO z x y) =
      addSO (FirstOrder.Rew.shift z) (FirstOrder.Rew.shift x) (FirstOrder.Rew.shift y) :=
  rew_addSO hb_shift hf_shift z x y

theorem shift₀_baseSO {n : ℕ} (e : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.shift₀ (baseSO e) = baseSO (FirstOrder.Rew.shift e) :=
  rew_baseSO hb_shift hf_shift e

theorem shift₀_precSOv {n : ℕ} (y x : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.shift₀ (precSOv y x) =
      precSOv (FirstOrder.Rew.shift y) (FirstOrder.Rew.shift x) :=
  rew_precSOv hb_shift hf_shift y x

theorem shift₀_goodSO {n : ℕ} (s g : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.shift₀ (goodSO s g) =
      goodSO (FirstOrder.Rew.shift s) (FirstOrder.Rew.shift g) :=
  rew_goodSO hb_shift hf_shift s g

theorem shift₀_xSO {n : ℕ} (t : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.shift₀ (xSO t) = xSO (FirstOrder.Rew.shift t) :=
  rew_xSO hb_shift hf_shift t

theorem shift₀_progSOX {n : ℕ} :
    Semiproposition.shift₀ (progSOX : Semiproposition ℒₒᵣ 0 n) = progSOX :=
  rew_progSOX hb_shift hf_shift

theorem shift₀_psiAt {n : ℕ} (g : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.shift₀ (psiAt g) = psiAt (FirstOrder.Rew.shift g) :=
  rew_psiAt hb_shift hf_shift g

theorem shift₀_belowPsi {n : ℕ} (b : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition.shift₀ (belowPsi b) = belowPsi (FirstOrder.Rew.shift b) :=
  rew_belowPsi hb_shift hf_shift b

/-! ### The shape of `tiSO` -/

theorem tiSO_eq {n : ℕ} (a : FirstOrder.Semiterm LX ℕ n) :
    tiSO a = ∼(progSOX : Semiproposition ℒₒᵣ 0 n) ⋎ belowSOX a := by
  show toSOAtB segWitness (Gentzen.tiUptoAt precCode₁
    (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) a) = _
  show toSOAtB segWitness (∼(Gentzen.progAt precCode₁
    (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))) ⋎
      Gentzen.belowAt precCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) a) = _
  rw [toSOAtB_or, toSOAtB_neg]
  rfl

theorem belowSOX_eq {n : ℕ} (b : FirstOrder.Semiterm LX ℕ n) :
    belowSOX b =
      ∀¹ (∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ (n + 1)) (FirstOrder.Rew.bShift b)) ⋎
        xSO (#0 : FirstOrder.Semiterm LX ℕ (n + 1))) := by
  show toSOAtB segWitness (∀¹ (∼(Gentzen.precAt precCode₁
    (#0 : FirstOrder.Semiterm LX ℕ (n + 1)) (FirstOrder.Rew.bShift b)) ⋎
      Gentzen.formulaAt (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) #0)) = _
  rw [toSOAtB_all, toSOAtB_or, toSOAtB_neg]
  have h : Gentzen.formulaAt (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
      (#0 : FirstOrder.Semiterm LX ℕ (n + 1)) = Xat (#0 : FirstOrder.Semiterm LX ℕ (n + 1)) := by
    unfold Gentzen.formulaAt Gentzen.Xat
    change FirstOrder.Semiformula.rel (Sum.inr Gentzen.XRel.X)
        ((FirstOrder.Rew.subst ![(#0 : FirstOrder.Semiterm LX ℕ (n + 1))]) ∘
          ![(#0 : FirstOrder.Semiterm LX ℕ 1)]) =
      FirstOrder.Semiformula.rel (Sum.inr Gentzen.XRel.X)
        ![(#0 : FirstOrder.Semiterm LX ℕ (n + 1))]
    congr 1
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp
  rw [h]
  rfl

/-! ## Layer 1c: the `ξ = Empty` presentation of `ψ₀`

`Lift.lean`'s `lift_paLX` insists that the lifting parameter carry no free
*number* variable of its own (`ξ := Empty`), because `Rew.free`/`Rew.shift`
would otherwise renumber them; `lift_paLX₀`, the convenient `ξ = ℕ` form, is not
available here because it demands `Arith`, and `ψ₀` has a set quantifier.  So
`ψ₀` is built over `Empty`, and `emb_psiE` identifies its embedding with the
`ℕ`-side vocabulary above. -/

section EmptySide

/-- Two rewritings out of `Empty` agree as soon as they agree on bound
variables; this is the only fact the `Empty`-side bookkeeping needs. -/
private theorem emb_comm_subst {M m n : ℕ} (χ : Semiformula ℒₒᵣ ℕ Empty M m)
    (v : Fin m → FirstOrder.Semiterm ℒₒᵣ Empty n) :
    (FirstOrder.Rew.subst (fun i => (FirstOrder.Rew.emb (v i) :
        FirstOrder.Semiterm ℒₒᵣ ℕ n))) ▹
        (FirstOrder.Rewriting.emb χ : Semiformula ℒₒᵣ ℕ ℕ M m) =
      (FirstOrder.Rewriting.emb (FirstOrder.Rew.subst v ▹ χ) : Semiformula ℒₒᵣ ℕ ℕ M n) := by
  have he : ((FirstOrder.Rew.subst (fun i => (FirstOrder.Rew.emb (v i) :
        FirstOrder.Semiterm ℒₒᵣ ℕ n))).comp FirstOrder.Rew.emb :
        FirstOrder.Rew ℒₒᵣ Empty m ℕ n) =
      FirstOrder.Rew.emb.comp (FirstOrder.Rew.subst v) := by
    ext x
    · simp [FirstOrder.Rew.comp_app]
    · exact x.elim
  show FirstOrder.Rew.subst _ ▹ (FirstOrder.Rew.emb ▹ χ) =
    FirstOrder.Rew.emb ▹ (FirstOrder.Rew.subst v ▹ χ)
  rw [← FirstOrder.TransitiveRewriting.comp_app, ← FirstOrder.TransitiveRewriting.comp_app, he]

variable {N n : ℕ}

/-- `y ≺ x`, over `Empty`. -/
def precAtE (P : Semiformula ℒₒᵣ ℕ Empty N 2)
    (y x : FirstOrder.Semiterm ℒₒᵣ Empty n) : Semiformula ℒₒᵣ ℕ Empty N n :=
  FirstOrder.Rew.subst ![y, x] ▹ P

/-- `Ψ(x)`, over `Empty`. -/
def formulaAtE (Ψ : Semiformula ℒₒᵣ ℕ Empty N 1)
    (x : FirstOrder.Semiterm ℒₒᵣ Empty n) : Semiformula ℒₒᵣ ℕ Empty N n := Ψ/[x]

/-- `Below(Ψ, b)`, over `Empty`. -/
def belowAtE (P : Semiformula ℒₒᵣ ℕ Empty N 2) (Ψ : Semiformula ℒₒᵣ ℕ Empty N 1)
    (b : FirstOrder.Semiterm ℒₒᵣ Empty n) : Semiformula ℒₒᵣ ℕ Empty N n :=
  ∀¹ (∼(precAtE P (#0 : FirstOrder.Semiterm ℒₒᵣ Empty (n + 1))
      (FirstOrder.Rew.bShift b)) ⋎ formulaAtE Ψ #0)

/-- `Prog(Ψ)`, over `Empty`. -/
def progAtE (P : Semiformula ℒₒᵣ ℕ Empty N 2) (Ψ : Semiformula ℒₒᵣ ℕ Empty N 1) :
    Semiformula ℒₒᵣ ℕ Empty N n :=
  ∀¹ (∼(belowAtE P Ψ (#0 : FirstOrder.Semiterm ℒₒᵣ Empty (n + 1))) ⋎ formulaAtE Ψ #0)

/-- `TI(Ψ, a)`, over `Empty`. -/
def tiUptoAtE (P : Semiformula ℒₒᵣ ℕ Empty N 2) (Ψ : Semiformula ℒₒᵣ ℕ Empty N 1)
    (a : FirstOrder.Semiterm ℒₒᵣ Empty n) : Semiformula ℒₒᵣ ℕ Empty N n :=
  ∼(progAtE P Ψ) ⋎ belowAtE P Ψ a

theorem emb_precAtE (P : Semiformula ℒₒᵣ ℕ Empty N 2)
    (y x : FirstOrder.Semiterm ℒₒᵣ Empty n) :
    (FirstOrder.Rewriting.emb (precAtE P y x) : Semiformula ℒₒᵣ ℕ ℕ N n) =
      precAtLift (FirstOrder.Rewriting.emb P) (FirstOrder.Rew.emb y)
        (FirstOrder.Rew.emb x) := by
  have hv : (fun i => (FirstOrder.Rew.emb ((![y, x] : Fin 2 →
      FirstOrder.Semiterm ℒₒᵣ Empty n) i) : FirstOrder.Semiterm ℒₒᵣ ℕ n)) =
      ![FirstOrder.Rew.emb y, FirstOrder.Rew.emb x] := by
    funext i; fin_cases i <;> rfl
  show _ = FirstOrder.Rew.subst ![FirstOrder.Rew.emb y, FirstOrder.Rew.emb x] ▹
    (FirstOrder.Rewriting.emb P)
  rw [← hv, emb_comm_subst]
  rfl

theorem emb_formulaAtE (Ψ : Semiformula ℒₒᵣ ℕ Empty N 1)
    (x : FirstOrder.Semiterm ℒₒᵣ Empty n) :
    (FirstOrder.Rewriting.emb (formulaAtE Ψ x) : Semiformula ℒₒᵣ ℕ ℕ N n) =
      formulaAtLift (FirstOrder.Rewriting.emb Ψ) (FirstOrder.Rew.emb x) := by
  have hv : (fun i => (FirstOrder.Rew.emb ((![x] : Fin 1 →
      FirstOrder.Semiterm ℒₒᵣ Empty n) i) : FirstOrder.Semiterm ℒₒᵣ ℕ n)) =
      ![FirstOrder.Rew.emb x] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi; rfl
  show _ = FirstOrder.Rew.subst ![FirstOrder.Rew.emb x] ▹ (FirstOrder.Rewriting.emb Ψ)
  rw [← hv, emb_comm_subst]
  rfl

theorem emb_belowAtE (P : Semiformula ℒₒᵣ ℕ Empty N 2) (Ψ : Semiformula ℒₒᵣ ℕ Empty N 1)
    (b : FirstOrder.Semiterm ℒₒᵣ Empty n) :
    (FirstOrder.Rewriting.emb (belowAtE P Ψ b) : Semiformula ℒₒᵣ ℕ ℕ N n) =
      belowAtLift (FirstOrder.Rewriting.emb P) (FirstOrder.Rewriting.emb Ψ)
        (FirstOrder.Rew.emb b) := by
  show (FirstOrder.Rew.emb : FirstOrder.Rew ℒₒᵣ Empty n ℕ n) ▹
    (∀¹ (∼(precAtE P (#0 : FirstOrder.Semiterm ℒₒᵣ Empty (n + 1))
      (FirstOrder.Rew.bShift b)) ⋎ formulaAtE Ψ #0)) = _
  rw [Semiformula.rew_all₀, FirstOrder.Rew.q_emb,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    emb_precAtE, emb_formulaAtE]
  have hcomp : ((FirstOrder.Rew.emb : FirstOrder.Rew ℒₒᵣ Empty (n + 1) ℕ (n + 1)).comp
        FirstOrder.Rew.bShift : FirstOrder.Rew ℒₒᵣ Empty n ℕ (n + 1)) =
      FirstOrder.Rew.bShift.comp (FirstOrder.Rew.emb : FirstOrder.Rew ℒₒᵣ Empty n ℕ n) := by
    ext x
    · simp [FirstOrder.Rew.comp_app]
    · exact x.elim
  have hb : (FirstOrder.Rew.emb (FirstOrder.Rew.bShift b) :
      FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1)) =
      FirstOrder.Rew.bShift (FirstOrder.Rew.emb b) := by
    rw [← FirstOrder.Rew.comp_app, ← FirstOrder.Rew.comp_app, hcomp]
  rw [hb]
  rfl

theorem emb_progAtE (P : Semiformula ℒₒᵣ ℕ Empty N 2) (Ψ : Semiformula ℒₒᵣ ℕ Empty N 1) :
    (FirstOrder.Rewriting.emb (progAtE (n := n) P Ψ) : Semiformula ℒₒᵣ ℕ ℕ N n) =
      progAtLift (FirstOrder.Rewriting.emb P) (FirstOrder.Rewriting.emb Ψ) := by
  show (FirstOrder.Rew.emb : FirstOrder.Rew ℒₒᵣ Empty n ℕ n) ▹
    (∀¹ (∼(belowAtE P Ψ (#0 : FirstOrder.Semiterm ℒₒᵣ Empty (n + 1))) ⋎
      formulaAtE Ψ #0)) = _
  rw [Semiformula.rew_all₀, FirstOrder.Rew.q_emb,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    emb_belowAtE, emb_formulaAtE]
  rfl

theorem emb_tiUptoAtE (P : Semiformula ℒₒᵣ ℕ Empty N 2) (Ψ : Semiformula ℒₒᵣ ℕ Empty N 1)
    (a : FirstOrder.Semiterm ℒₒᵣ Empty n) :
    (FirstOrder.Rewriting.emb (tiUptoAtE P Ψ a) : Semiformula ℒₒᵣ ℕ ℕ N n) =
      tiUptoAtLift (FirstOrder.Rewriting.emb P) (FirstOrder.Rewriting.emb Ψ)
        (FirstOrder.Rew.emb a) := by
  show (FirstOrder.Rew.emb : FirstOrder.Rew ℒₒᵣ Empty n ℕ n) ▹
    (∼(progAtE P Ψ) ⋎ belowAtE P Ψ a) = _
  rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    emb_progAtE, emb_belowAtE]
  rfl

theorem emb_lift_eq {M m : ℕ} (χ : FirstOrder.Semiformula ℒₒᵣ Empty m) :
    (FirstOrder.Rewriting.emb (lift χ : Semiformula ℒₒᵣ ℕ Empty M m) :
        Semiformula ℒₒᵣ ℕ ℕ M m) =
      lift (FirstOrder.Rewriting.emb χ) := by
  show (FirstOrder.Rew.emb : FirstOrder.Rew ℒₒᵣ Empty m ℕ m) ▹ (lift χ) = _
  rw [← lift_rew]

end EmptySide

/-- **`ψ₀`, over `ξ = Empty`** — the parameter `lift_paLX` is applied at. -/
noncomputable def psiE : Semiformula ℒₒᵣ ℕ Empty 0 1 :=
  ∀¹ (∼(FirstOrder.Rew.subst ![(#0 : FirstOrder.Semiterm ℒₒᵣ Empty 2), #1] ▹
        (lift epsDef₁.val : Semiformula ℒₒᵣ ℕ Empty 0 2)) ⋎
      (∀² (tiUptoAtE (lift Gentzen.InternalVNote.precDef₁.val) boundWitness
        (#0 : FirstOrder.Semiterm ℒₒᵣ Empty 2))))

/-- **The image of `tiX` at an arbitrary parameter**, normalised
(`TowerInduction.tiBody_eq` is the instance at `boundWitness`). -/
theorem tiX_image {M : ℕ} {ψ : Semiformula ℒₒᵣ ℕ Empty M 1} {n : ℕ}
    (a : FirstOrder.Semiterm LX ℕ n) :
    toSOAtB ψ (tiX a) =
      tiUptoAtLift (lift (FirstOrder.Rewriting.emb Gentzen.InternalVNote.precDef₁.val))
        (FirstOrder.Rewriting.emb ψ) (unTerm a) := by
  show toSOAtB ψ (Gentzen.tiUptoAt precCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)) a) = _
  rw [toSOAtB_tiUptoAt, toSOAtB_precCode₁, toSOAtB_Xat_bvar]

/-- **`emb psiE` is the `ℕ`-side `ψ₀`.** -/
theorem emb_psiE :
    (FirstOrder.Rewriting.emb psiE : Semiproposition ℒₒᵣ 0 1) =
      psiAt (#0 : FirstOrder.Semiterm LX ℕ 1) := by
  have hv : (fun i => (FirstOrder.Rew.emb ((![(#0 : FirstOrder.Semiterm ℒₒᵣ Empty 2), #1] :
      Fin 2 → FirstOrder.Semiterm ℒₒᵣ Empty 2) i) : FirstOrder.Semiterm ℒₒᵣ ℕ 2)) =
      ![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2), #1] := by
    funext i; fin_cases i <;> rfl
  have heps : (FirstOrder.Rewriting.emb (FirstOrder.Rew.subst
        ![(#0 : FirstOrder.Semiterm ℒₒᵣ Empty 2), #1] ▹
        (lift epsDef₁.val : Semiformula ℒₒᵣ ℕ Empty 0 2)) : Semiproposition ℒₒᵣ 0 2) =
      epsSO (#0 : FirstOrder.Semiterm LX ℕ 2) #1 := by
    rw [← emb_comm_subst, hv, epsSO_eq, emb_lift_eq]
    rfl
  have hti : (FirstOrder.Rewriting.emb (tiUptoAtE
        (lift Gentzen.InternalVNote.precDef₁.val) boundWitness
        (#0 : FirstOrder.Semiterm ℒₒᵣ Empty 2)) : Semiformula ℒₒᵣ ℕ ℕ 1 2) =
      toSOAtB boundWitness (tiX (#0 : FirstOrder.Semiterm LX ℕ 2)) := by
    rw [emb_tiUptoAtE, tiX_image, emb_lift_eq]
    rfl
  show (FirstOrder.Rew.emb : FirstOrder.Rew ℒₒᵣ Empty 1 ℕ 1) ▹
    (∀¹ (∼(FirstOrder.Rew.subst ![(#0 : FirstOrder.Semiterm ℒₒᵣ Empty 2), #1] ▹
          (lift epsDef₁.val : Semiformula ℒₒᵣ ℕ Empty 0 2)) ⋎
        (∀² (tiUptoAtE (lift Gentzen.InternalVNote.precDef₁.val) boundWitness
          (#0 : FirstOrder.Semiterm ℒₒᵣ Empty 2))))) = _
  rw [Semiformula.rew_all₀, FirstOrder.Rew.q_emb,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    Semiformula.rew_all₁]
  show ∀¹ (∼(FirstOrder.Rewriting.emb (FirstOrder.Rew.subst
      ![(#0 : FirstOrder.Semiterm ℒₒᵣ Empty 2), #1] ▹
      (lift epsDef₁.val : Semiformula ℒₒᵣ ℕ Empty 0 2))) ⋎
    (∀² (FirstOrder.Rewriting.emb (tiUptoAtE
      (lift Gentzen.InternalVNote.precDef₁.val) boundWitness
      (#0 : FirstOrder.Semiterm ℒₒᵣ Empty 2))))) = _
  rw [heps, hti]
  rfl

/-! ## Layer 1d: the lifting at `ψ₀`, and (TIψ) -/

theorem noSetFvar_emb_psiE :
    NoSetFvar (FirstOrder.Rewriting.emb psiE : Semiproposition ℒₒᵣ 0 1) := by
  rw [emb_psiE]
  exact noSetFvar_psiAt _

/-- **The lifting at the parameter `ψ₀`.**  `lift_paLX` with `N = 0`: the set
quantifier of `ψ₀` is *bound*, so there are no witnesses to supply and the
`hΦ`-obligation is vacuous. -/
theorem lift_paLX_psi {σ : FirstOrder.Sentence LX} (h : paLX ⊢ σ) :
    Provable ACA (toSOAt psiE (FirstOrder.Rewriting.emb σ)) := by
  have h2 := lift_paLX (N := 0) psiE noSetFvar_emb_psiE
    (![] : Fin 0 → Semiformula ℒₒᵣ ℕ Empty 0 1) (fun i => i.elim0) h
  have e : Semiproposition.subst₁ psiE (![] : Fin 0 → Semiformula ℒₒᵣ ℕ Empty 0 1) = psiE := by
    have hid : (SecondOrder.Rew.subst (![] : Fin 0 → Semiformula ℒₒᵣ ℕ Empty 0 1) :
        SecondOrder.Rew ℒₒᵣ ℕ 0 ℕ 0 Empty) = SecondOrder.Rew.id := by
      ext X
      · exact X.elim0
      · simp
    show (SecondOrder.Rew.subst _).app psiE = _
    rw [hid]
    simp
  rwa [e] at h2

/-! ### Normalising the `tiUptoAtLift`-image at `ψ₀` -/

theorem precAtLift_bvar_eq {n : ℕ} (x : FirstOrder.Semiterm LX ℕ n) :
    precAtLift (lift (FirstOrder.Rewriting.emb Gentzen.InternalVNote.precDef₁.val))
      (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1)) (FirstOrder.Rew.bShift (unTerm x)) =
      precSOv (#0 : FirstOrder.Semiterm LX ℕ (n + 1)) (FirstOrder.Rew.bShift x) := by
  rw [precSOv_eq, unTerm_bShift]
  rfl

theorem formulaAtLift_psi {n : ℕ} (t : FirstOrder.Semiterm LX ℕ n) :
    formulaAtLift (psiAt (#0 : FirstOrder.Semiterm LX ℕ 1)) (unTerm t) = psiAt t := by
  have hv : (fun j => unTerm ((![t] : Fin 1 → FirstOrder.Semiterm LX ℕ n) j)) =
      ![unTerm t] := by
    funext j
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj; rfl
  show FirstOrder.Rew.subst ![unTerm t] ▹ (psiAt (#0 : FirstOrder.Semiterm LX ℕ 1)) = _
  rw [← hv, rew_psiAt (ω := FirstOrder.Rew.subst ![t]) (hb_subst _) (hf_subst _)]
  simp

theorem formulaAtLift_psi_bvar {n : ℕ} :
    formulaAtLift (psiAt (#0 : FirstOrder.Semiterm LX ℕ 1))
        (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1)) =
      psiAt (#0 : FirstOrder.Semiterm LX ℕ (n + 1)) :=
  formulaAtLift_psi (#0 : FirstOrder.Semiterm LX ℕ (n + 1))

theorem belowAtLift_psi {n : ℕ} (b : FirstOrder.Semiterm LX ℕ n) :
    belowAtLift (lift (FirstOrder.Rewriting.emb Gentzen.InternalVNote.precDef₁.val))
      (psiAt (#0 : FirstOrder.Semiterm LX ℕ 1)) (unTerm b) = belowPsi b := by
  show ∀¹ (∼(precAtLift (lift (FirstOrder.Rewriting.emb
      Gentzen.InternalVNote.precDef₁.val))
      (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1))
      (FirstOrder.Rew.bShift (unTerm b))) ⋎
    formulaAtLift (psiAt (#0 : FirstOrder.Semiterm LX ℕ 1))
      (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1))) = _
  rw [precAtLift_bvar_eq, formulaAtLift_psi_bvar]
  rfl

theorem belowAtLift_psi_bvar {n : ℕ} :
    belowAtLift (lift (FirstOrder.Rewriting.emb Gentzen.InternalVNote.precDef₁.val))
        (psiAt (#0 : FirstOrder.Semiterm LX ℕ 1))
        (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1)) =
      belowPsi (#0 : FirstOrder.Semiterm LX ℕ (n + 1)) :=
  belowAtLift_psi (#0 : FirstOrder.Semiterm LX ℕ (n + 1))

theorem progAtLift_psi {n : ℕ} :
    progAtLift (lift (FirstOrder.Rewriting.emb Gentzen.InternalVNote.precDef₁.val))
      (psiAt (#0 : FirstOrder.Semiterm LX ℕ 1)) = (progPsi : Semiproposition ℒₒᵣ 0 n) := by
  show ∀¹ (∼(belowAtLift (lift (FirstOrder.Rewriting.emb
      Gentzen.InternalVNote.precDef₁.val))
      (psiAt (#0 : FirstOrder.Semiterm LX ℕ 1))
      (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1))) ⋎
    formulaAtLift (psiAt (#0 : FirstOrder.Semiterm LX ℕ 1))
      (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ (n + 1))) = _
  rw [belowAtLift_psi_bvar, formulaAtLift_psi_bvar]
  rfl

theorem tiUptoAtLift_psi {n : ℕ} (b : FirstOrder.Semiterm LX ℕ n) :
    tiUptoAtLift (lift (FirstOrder.Rewriting.emb Gentzen.InternalVNote.precDef₁.val))
        (psiAt (#0 : FirstOrder.Semiterm LX ℕ 1)) (unTerm b) =
      ∼(progPsi : Semiproposition ℒₒᵣ 0 n) ⋎ belowPsi b := by
  show ∼(progAtLift (lift (FirstOrder.Rewriting.emb
      Gentzen.InternalVNote.precDef₁.val)) (psiAt (#0 : FirstOrder.Semiterm LX ℕ 1))) ⋎
    belowAtLift (lift (FirstOrder.Rewriting.emb
      Gentzen.InternalVNote.precDef₁.val)) (psiAt (#0 : FirstOrder.Semiterm LX ℕ 1))
      (unTerm b) = _
  rw [progAtLift_psi, belowAtLift_psi]

/-- **(TIψ).**  Gentzen's `ε₀` bound, lifted at `ψ₀`: for every external
`c < ε₀`, `ACA` proves transfinite induction along `≺₁` below `c̄` *for the
`Π¹₁` formula `ψ₀`*.  This is the one place the parametric lifting of
`ACA/Lift.lean` is used at a non-arithmetical parameter. -/
theorem tiPsi (c : Gamma0Note) (hc : c < Gamma0Note.epsilonNote 0) :
    Provable ACA (∼(progPsi : Proposition ℒₒᵣ) ⋎
      belowPsi (Gentzen.Epsilon1UpperBound.gamma0Term c)) := by
  have h := lift_paLX_psi (Gentzen.VeblenEpsilon0UpperBound.concrete_eps0_ti c hc
    (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)))
  have hcl : (tiX (Gentzen.Epsilon1UpperBound.gamma0Term c)).freeVariables = ∅ :=
    freeVariables_tiX (by simp [Gentzen.Epsilon1UpperBound.gamma0Term])
  have he : (FirstOrder.Rewriting.emb (Gentzen.Epsilon1UpperBound.closedTI₁
      (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
      (Gentzen.Epsilon1UpperBound.gamma0Term c)) : FirstOrder.Semiformula LX ℕ 0) =
      tiX (Gentzen.Epsilon1UpperBound.gamma0Term c) :=
    TowerSyntax.emb_univCl_of_closed hcl
  rw [he] at h
  show Provable ACA (∼(progPsi : Proposition ℒₒᵣ) ⋎
    belowPsi (Gentzen.Epsilon1UpperBound.gamma0Term c))
  rw [← tiUptoAtLift_psi, ← emb_psiE, ← tiX_image]
  exact h

/-! ## Layer 2a: the successor step as a closed `ACA`-theorem

    `ACA ⊢ ∀e ∀s (Base(e) → Add(s,e,1̄) → (∀²X TI(e,X)) → (∀²X TI(s,X)))`

One `all₂`, one `exs₂` (at the *free* set variable — this instance of
comprehension is trivial, it merely undoes the `∀²`), and the lifted
`ProgStep.succTIStatement`. -/

/-- The code of `1`, as an `LX` numeral. -/
abbrev oneLX {n : ℕ} : FirstOrder.Semiterm LX ℕ n :=
  ((Gentzen.VNoteBridge.gamma0Code 1 : ℕ) : FirstOrder.Semiterm LX ℕ n)

/-- The matrix of the lifted successor step (`#1 = e`, `#0 = s`). -/
def succMatrixSO : Semiproposition ℒₒᵣ 0 2 :=
  ∼(baseSO (#1 : FirstOrder.Semiterm LX ℕ 2)) ⋎
    (∼(addSO (#0 : FirstOrder.Semiterm LX ℕ 2) #1 oneLX) ⋎
      (∼(tiSO (#1 : FirstOrder.Semiterm LX ℕ 2)) ⋎ tiSO (#0 : FirstOrder.Semiterm LX ℕ 2)))

@[simp] theorem freeVariables_succTIBody : succTIBody.freeVariables = ∅ := by
  have hX : (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)).freeVariables = ∅ := by simp
  have h1 : (Gentzen.formulaAt baseCode₁
      (#1 : FirstOrder.Semiterm LX ℕ 2)).freeVariables = ∅ :=
    freeVariables_formulaAt freeVariables_baseCode₁ (by simp)
  have h2 : (Gentzen.addAt addCode₁ (#0 : FirstOrder.Semiterm LX ℕ 2) #1
      oneLX).freeVariables = ∅ :=
    freeVariables_addAt (by simp) (by simp) (by simp)
  have h3 : (Gentzen.tiUptoAt precCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
      (#1 : FirstOrder.Semiterm LX ℕ 2)).freeVariables = ∅ :=
    freeVariables_tiUptoAt freeVariables_precCode₁ hX (by simp)
  have h4 : (Gentzen.tiUptoAt precCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
      (#0 : FirstOrder.Semiterm LX ℕ 2)).freeVariables = ∅ :=
    freeVariables_tiUptoAt freeVariables_precCode₁ hX (by simp)
  show (∼(Gentzen.formulaAt baseCode₁ (#1 : FirstOrder.Semiterm LX ℕ 2)) ⋎
    (∼(Gentzen.addAt addCode₁ (#0 : FirstOrder.Semiterm LX ℕ 2) #1 oneLX) ⋎
      (∼(Gentzen.tiUptoAt precCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
          (#1 : FirstOrder.Semiterm LX ℕ 2)) ⋎
        Gentzen.tiUptoAt precCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
          (#0 : FirstOrder.Semiterm LX ℕ 2)))).freeVariables = ∅
  simp [h1, h2, h3, h4]

theorem succTI_SO : Provable ACA (∀¹ (∀¹ succMatrixSO)) := by
  have h : Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb succTIStatement)) :=
    lift_paLX_seg concrete_succTI
  rw [show succTIStatement = (∀¹ ∀¹ succTIBody).univCl from rfl,
    TowerSyntax.emb_univCl_of_closed (by simp)] at h
  have e : toSOAt segWitness ((∀¹ (∀¹ succTIBody)) : FirstOrder.Semiformula LX ℕ 0) =
      ∀¹ (∀¹ succMatrixSO) := by
    show ∀¹ (∀¹ (toSOAtB segWitness succTIBody)) = _
    show ∀¹ (∀¹ (toSOAtB segWitness
      (∼(Gentzen.formulaAt baseCode₁ (#1 : FirstOrder.Semiterm LX ℕ 2)) ⋎
        (∼(Gentzen.addAt addCode₁ (#0 : FirstOrder.Semiterm LX ℕ 2) #1 oneLX) ⋎
          (∼(Gentzen.tiUptoAt precCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
              (#1 : FirstOrder.Semiterm LX ℕ 2)) ⋎
            Gentzen.tiUptoAt precCode₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
              (#0 : FirstOrder.Semiterm LX ℕ 2)))))) = _
    rw [toSOAtB_or, toSOAtB_neg, toSOAtB_or, toSOAtB_neg, toSOAtB_or, toSOAtB_neg]
    rfl
  rwa [e] at h

theorem succTI_inst (te ts : FirstOrder.Semiterm LX ℕ 0) :
    Provable ACA (∼(baseSO te) ⋎ (∼(addSO ts te oneLX) ⋎ (∼(tiSO te) ⋎ tiSO ts))) := by
  have h := specNums succMatrixSO
    (fun j => unTerm ((![ts, te] : Fin 2 → FirstOrder.Semiterm LX ℕ 0) j)) succTI_SO
  have e : (FirstOrder.Rew.subst
        (fun j => unTerm ((![ts, te] : Fin 2 → FirstOrder.Semiterm LX ℕ 0) j))) ▹
      succMatrixSO = ∼(baseSO te) ⋎ (∼(addSO ts te oneLX) ⋎ (∼(tiSO te) ⋎ tiSO ts)) := by
    show (FirstOrder.Rew.subst _) ▹
      (∼(baseSO (#1 : FirstOrder.Semiterm LX ℕ 2)) ⋎
        (∼(addSO (#0 : FirstOrder.Semiterm LX ℕ 2) #1 oneLX) ⋎
          (∼(tiSO (#1 : FirstOrder.Semiterm LX ℕ 2)) ⋎
            tiSO (#0 : FirstOrder.Semiterm LX ℕ 2)))) = _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
      LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
      LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
      rew_baseSO (hb_subst _) (hf_subst _), rew_addSO (hb_subst _) (hf_subst _),
      rew_tiSO (hb_subst _) (hf_subst _), rew_tiSO (hb_subst _) (hf_subst _)]
    simp
  rwa [e] at h

/-- The matrix of the closed successor theorem. -/
def succBody {n : ℕ} (e s : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  ∼(baseSO e) ⋎ (∼(addSO s e oneLX) ⋎ (∼(allTI e) ⋎ allTI s))

def succInner {n : ℕ} (e : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  ∀¹ (succBody (FirstOrder.Rew.bShift e) (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))

/-- `∀e ∀s (Base(e) → Add(s,e,1̄) → (∀²X TI(e,X)) → (∀²X TI(s,X)))`. -/
def succAll : Proposition ℒₒᵣ := ∀¹ (succInner (#0 : FirstOrder.Semiterm LX ℕ 1))

section RewSucc

variable {n₁ n₂ : ℕ} {ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂} {ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂}

theorem rew_succBody (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (e s : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (succBody e s) = succBody (ω e) (ω s) := by
  show ω' ▹ (∼(baseSO e) ⋎ (∼(addSO s e oneLX) ⋎ (∼(allTI e) ⋎ allTI s))) = _
  rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    rew_baseSO hb hf, rew_addSO hb hf, rew_allTI hb hf, rew_allTI hb hf]
  show ∼(baseSO (ω e)) ⋎ (∼(addSO (ω s) (ω e) (ω oneLX)) ⋎
    (∼(allTI (ω e)) ⋎ allTI (ω s))) = _
  have hone : ω (oneLX : FirstOrder.Semiterm LX ℕ n₁) =
      (oneLX : FirstOrder.Semiterm LX ℕ n₂) := by simp
  rw [hone]
  rfl

theorem rew_succInner (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (e : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (succInner e) = succInner (ω e) := by
  show ω' ▹ (∀¹ (succBody (FirstOrder.Rew.bShift e)
    (#0 : FirstOrder.Semiterm LX ℕ (n₁ + 1)))) = _
  rw [Semiformula.rew_all₀, rew_succBody (q_hb hb) (q_hf hf), q_bShift]
  show ∀¹ (succBody (FirstOrder.Rew.bShift (ω e)) (ω.q #0)) = _
  simp only [FirstOrder.Rew.q_bvar_zero]
  rfl

end RewSucc

theorem noSetFvar_succBody {n : ℕ} (e s : FirstOrder.Semiterm LX ℕ n) :
    NoSetFvar (succBody e s) := by
  show NoSetFvar (∼(baseSO e) ⋎ (∼(addSO s e oneLX) ⋎ (∼(allTI e) ⋎ allTI s)))
  simp [noSetFvar_baseSO, noSetFvar_addSO, noSetFvar_allTI]

/-- **The successor step, `∀²`-closed.** -/
theorem succAllTI : Provable ACA succAll := by
  show Provable ACA (∀¹ (succInner (#0 : FirstOrder.Semiterm LX ℕ 1)))
  refine gen₁ ACA_shift₀_invariant ?_
  have e1 : Semiproposition.free₀ (succInner (#0 : FirstOrder.Semiterm LX ℕ 1)) =
      succInner (&0 : FirstOrder.Semiterm LX ℕ 0) := by
    show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹
      (succInner (#0 : FirstOrder.Semiterm LX ℕ 1)) = _
    rw [rew_succInner (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
      hb_free hf_free]
    simp
  rw [e1]
  show Provable ACA (∀¹ (succBody (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))
    (#0 : FirstOrder.Semiterm LX ℕ 1)))
  refine gen₁ ACA_shift₀_invariant ?_
  have e2 : Semiproposition.free₀ (succBody
      (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))
      (#0 : FirstOrder.Semiterm LX ℕ 1)) =
      succBody (&1 : FirstOrder.Semiterm LX ℕ 0) (&0) := by
    show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹ (succBody _ _) = _
    rw [rew_succBody (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
      hb_free hf_free]
    simp
  rw [e2]
  -- the sequent derivation, with `e = &1`, `s = &0`
  have hcore : PSeq ACA [∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)),
      allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
      ∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) oneLX),
      ∼(baseSO (&1 : FirstOrder.Semiterm LX ℕ 0))] := by
    have hs := succTI_inst (&1 : FirstOrder.Semiterm LX ℕ 0) (&0)
    have g0 : PSeq ACA [∼(baseSO (&1 : FirstOrder.Semiterm LX ℕ 0)),
        (∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) oneLX) ⋎
          (∼(tiSO (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋎
            tiSO (&0 : FirstOrder.Semiterm LX ℕ 0)))] :=
      PSeq.orInv (PSeq.of_provable hs)
    have g0' : PSeq ACA [(∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) oneLX) ⋎
          (∼(tiSO (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋎
            tiSO (&0 : FirstOrder.Semiterm LX ℕ 0))),
        ∼(baseSO (&1 : FirstOrder.Semiterm LX ℕ 0))] :=
      PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) g0
    have g1a : PSeq ACA [∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) oneLX),
        (∼(tiSO (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋎
          tiSO (&0 : FirstOrder.Semiterm LX ℕ 0)),
        ∼(baseSO (&1 : FirstOrder.Semiterm LX ℕ 0))] := PSeq.orInv g0'
    have g1b : PSeq ACA [(∼(tiSO (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋎
          tiSO (&0 : FirstOrder.Semiterm LX ℕ 0)),
        ∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) oneLX),
        ∼(baseSO (&1 : FirstOrder.Semiterm LX ℕ 0))] :=
      PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) g1a
    have g1 : PSeq ACA [∼(tiSO (&1 : FirstOrder.Semiterm LX ℕ 0)),
        tiSO (&0 : FirstOrder.Semiterm LX ℕ 0),
        ∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) oneLX),
        ∼(baseSO (&1 : FirstOrder.Semiterm LX ℕ 0))] := PSeq.orInv g1b
    have hshift₁ : SecondOrder.Sequent.shift₁
        [∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) oneLX),
          ∼(baseSO (&1 : FirstOrder.Semiterm LX ℕ 0)),
          ∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0))] =
        [∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) oneLX),
          ∼(baseSO (&1 : FirstOrder.Semiterm LX ℕ 0)),
          ∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0))] := by
      simp only [SecondOrder.Sequent.shift₁, List.map_cons, List.map_nil,
        LogicalConnective.HomClass.map_neg,
        shift₁_eq_self_of_noSetFvar
          (noSetFvar_addSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) oneLX),
        shift₁_eq_self_of_noSetFvar (noSetFvar_baseSO (&1 : FirstOrder.Semiterm LX ℕ 0)),
        shift₁_eq_self_of_noSetFvar (noSetFvar_allTI (&1 : FirstOrder.Semiterm LX ℕ 0))]
    have h5 : PSeq ACA [allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
        ∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) oneLX),
        ∼(baseSO (&1 : FirstOrder.Semiterm LX ℕ 0)),
        ∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0))] := by
      refine PSeq.all₂ ACA_shift₁_invariant ?_
      rw [hshift₁, free₁_tiBody]
      have key : PSeq ACA
          (Semiproposition.subst₁ (∼(toSOAtB boundWitness
              (tiX (&1 : FirstOrder.Semiterm LX ℕ 0)))) ![freeWitness] ::
            [tiSO (&0 : FirstOrder.Semiterm LX ℕ 0),
              ∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) oneLX),
              ∼(baseSO (&1 : FirstOrder.Semiterm LX ℕ 0))]) := by
        rw [neg_subst₁_tiBody_free]
        exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) g1
      exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
        (PSeq.exs₂ arith_freeWitness key)
    exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h5
  have h2 : PSeq ACA [(∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋎
        allTI (&0 : FirstOrder.Semiterm LX ℕ 0)),
      ∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) oneLX),
      ∼(baseSO (&1 : FirstOrder.Semiterm LX ℕ 0))] := PSeq.or hcore
  have h3 : PSeq ACA [∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) oneLX),
      (∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋎
        allTI (&0 : FirstOrder.Semiterm LX ℕ 0)),
      ∼(baseSO (&1 : FirstOrder.Semiterm LX ℕ 0))] :=
    PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h2
  have h4 : PSeq ACA [(∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) oneLX) ⋎
        (∼(allTI (&1 : FirstOrder.Semiterm LX ℕ 0)) ⋎
          allTI (&0 : FirstOrder.Semiterm LX ℕ 0))),
      ∼(baseSO (&1 : FirstOrder.Semiterm LX ℕ 0))] := PSeq.or h3
  exact PSeq.to_provable (PSeq.or
    (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h4))

/-- **`ACA ⊢ ∀²X TI(≺₁, 0̄, X)`** — the base of the case split. -/
theorem allTI_zero : Provable ACA (allTI zeroLX) := by
  have h := allSetsOfPaLX (Gentzen.VeblenEpsilon0UpperBound.concrete_ti_zero₁
    (Xat (#0 : FirstOrder.Semiterm LX ℕ 1)))
  have hcl : (tiX (zeroLX : FirstOrder.Semiterm LX ℕ 0)).freeVariables = ∅ :=
    freeVariables_tiX (by simp)
  rw [show Gentzen.Epsilon1UpperBound.closedTI₁ (Xat (#0 : FirstOrder.Semiterm LX ℕ 1))
      ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 0) = (tiX (zeroLX : FirstOrder.Semiterm LX ℕ 0)).univCl
    from rfl, TowerSyntax.emb_univCl_of_closed hcl] at h
  exact h

/-! ### Instances of the two closed theorems -/

theorem succ_inst (te ts : FirstOrder.Semiterm LX ℕ 0) : Provable ACA (succBody te ts) := by
  have h1 := spec₁ succAllTI (unTerm te)
  have e1 : (succInner (#0 : FirstOrder.Semiterm LX ℕ 1))/[unTerm te] = succInner te := by
    have hv : (fun j => unTerm ((![te] : Fin 1 → FirstOrder.Semiterm LX ℕ 0) j)) =
        ![unTerm te] := by
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj; rfl
    show FirstOrder.Rew.subst ![unTerm te] ▹ (succInner (#0 : FirstOrder.Semiterm LX ℕ 1)) = _
    rw [← hv, rew_succInner (ω := FirstOrder.Rew.subst ![te]) (hb_subst _) (hf_subst _)]
    simp
  rw [e1] at h1
  have h1' : Provable ACA (∀¹ (succBody (FirstOrder.Rew.bShift te)
      (#0 : FirstOrder.Semiterm LX ℕ 1))) := h1
  have h2 := spec₁ h1' (unTerm ts)
  have e2 : (succBody (FirstOrder.Rew.bShift te) (#0 : FirstOrder.Semiterm LX ℕ 1))/[unTerm ts] =
      succBody te ts := by
    have hv : (fun j => unTerm ((![ts] : Fin 1 → FirstOrder.Semiterm LX ℕ 0) j)) =
        ![unTerm ts] := by
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj; rfl
    show FirstOrder.Rew.subst ![unTerm ts] ▹ (succBody (FirstOrder.Rew.bShift te)
      (#0 : FirstOrder.Semiterm LX ℕ 1)) = _
    rw [← hv, rew_succBody (ω := FirstOrder.Rew.subst ![ts]) (hb_subst _) (hf_subst _)]
    simp
  rwa [e2] at h2

theorem towerInd_inst (tu tk tc : FirstOrder.Semiterm LX ℕ 0) :
    Provable ACA (stepBody tu tk tc) := by
  have h1 := spec₁ towerInduction (unTerm tk)
  have e1 : (theta : Semiproposition ℒₒᵣ 0 1)/[unTerm tk] = thetaAt tk := by
    have hv : (fun j => unTerm ((![tk] : Fin 1 → FirstOrder.Semiterm LX ℕ 0) j)) =
        ![unTerm tk] := by
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj; rfl
    show FirstOrder.Rew.subst ![unTerm tk] ▹ (thetaAt (#0 : FirstOrder.Semiterm LX ℕ 1)) = _
    rw [← hv, rew_thetaAt (ω := FirstOrder.Rew.subst ![tk]) (hb_subst _) (hf_subst _)]
    simp
  rw [e1] at h1
  have h1' : Provable ACA (∀¹ (thetaInner (FirstOrder.Rew.bShift tk)
      (#0 : FirstOrder.Semiterm LX ℕ 1))) := h1
  have h2 := spec₁ h1' (unTerm tc)
  have e2 : (thetaInner (FirstOrder.Rew.bShift tk)
      (#0 : FirstOrder.Semiterm LX ℕ 1))/[unTerm tc] = thetaInner tk tc := by
    have hv : (fun j => unTerm ((![tc] : Fin 1 → FirstOrder.Semiterm LX ℕ 0) j)) =
        ![unTerm tc] := by
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj; rfl
    show FirstOrder.Rew.subst ![unTerm tc] ▹ (thetaInner (FirstOrder.Rew.bShift tk)
      (#0 : FirstOrder.Semiterm LX ℕ 1)) = _
    rw [← hv, rew_thetaInner (ω := FirstOrder.Rew.subst ![tc]) (hb_subst _) (hf_subst _)]
    simp
  rw [e2] at h2
  have h2' : Provable ACA (∀¹ (stepBody (#0 : FirstOrder.Semiterm LX ℕ 1)
      (FirstOrder.Rew.bShift tk) (FirstOrder.Rew.bShift tc))) := h2
  have h3 := spec₁ h2' (unTerm tu)
  have e3 : (stepBody (#0 : FirstOrder.Semiterm LX ℕ 1) (FirstOrder.Rew.bShift tk)
      (FirstOrder.Rew.bShift tc))/[unTerm tu] = stepBody tu tk tc := by
    have hv : (fun j => unTerm ((![tu] : Fin 1 → FirstOrder.Semiterm LX ℕ 0) j)) =
        ![unTerm tu] := by
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj; rfl
    show FirstOrder.Rew.subst ![unTerm tu] ▹ (stepBody (#0 : FirstOrder.Semiterm LX ℕ 1)
      (FirstOrder.Rew.bShift tk) (FirstOrder.Rew.bShift tc)) = _
    rw [← hv, rew_stepBody (ω := FirstOrder.Rew.subst ![tu]) (hb_subst _) (hf_subst _)]
    simp
  rwa [e3] at h3

/-! ## Layer 2b: `Good` gives `∀²X TI` -/

/-- The first branch of `Good`: `s` is the coded successor of `0`. -/
def goodASO {n : ℕ} (s : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  baseSO ((0 : ℕ) : FirstOrder.Semiterm LX ℕ n) ⋏
    addSO s ((0 : ℕ) : FirstOrder.Semiterm LX ℕ n) oneLX

/-- The second branch of `Good`: `s` is the coded successor of an ε-number
`ε_h` with `h ≺₁ g`. -/
def goodBSO {n : ℕ} (s g : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  ∃¹ ∃¹
    (precSOv (#1 : FirstOrder.Semiterm LX ℕ (n + 2))
        (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift g)) ⋏
      (baseSO (#0 : FirstOrder.Semiterm LX ℕ (n + 2)) ⋏
        (epsSO (#0 : FirstOrder.Semiterm LX ℕ (n + 2)) #1 ⋏
          addSO (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift s))
            (#0 : FirstOrder.Semiterm LX ℕ (n + 2)) oneLX)))

/-- The first-order `Good`, at arbitrary terms. -/
noncomputable def goodBodyAt {n : ℕ} (s g : FirstOrder.Semiterm LX ℕ n) :
    FirstOrder.Semiformula LX ℕ n :=
  (Gentzen.formulaAt baseCode₁ ((0 : ℕ) : FirstOrder.Semiterm LX ℕ n) ⋏
      Gentzen.addAt addCode₁ s ((0 : ℕ) : FirstOrder.Semiterm LX ℕ n) oneLX) ⋎
    (∃¹ ∃¹
      (Gentzen.precAt precCode₁ (#1 : FirstOrder.Semiterm LX ℕ (n + 2))
          (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift g)) ⋏
        (Gentzen.formulaAt baseCode₁ (#0 : FirstOrder.Semiterm LX ℕ (n + 2)) ⋏
          (epsAt epsCode₁ (#0 : FirstOrder.Semiterm LX ℕ (n + 2)) #1 ⋏
            Gentzen.addAt addCode₁ (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift s))
              (#0 : FirstOrder.Semiterm LX ℕ (n + 2)) oneLX))))

theorem rew_epsAt' {n₁ n₂ : ℕ} (ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂)
    (y g : FirstOrder.Semiterm LX ℕ n₁) :
    ω ▹ (epsAt epsCode₁ y g) = epsAt epsCode₁ (ω y) (ω g) := by
  have hv : (fun i => ω ((![y, g] : Fin 2 → FirstOrder.Semiterm LX ℕ n₁) i)) = ![ω y, ω g] := by
    funext i; fin_cases i <;> rfl
  show ω ▹ (FirstOrder.Rew.subst ![y, g] ▹ epsCode₁) = _
  rw [rew_subst_closed freeVariables_epsCode₁ ω ![y, g], hv]
  rfl

theorem rew_addAt' {n₁ n₂ : ℕ} (ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂)
    (z x y : FirstOrder.Semiterm LX ℕ n₁) :
    ω ▹ (Gentzen.addAt addCode₁ z x y) = Gentzen.addAt addCode₁ (ω z) (ω x) (ω y) := by
  have hv : (fun i => ω ((![z, x, y] : Fin 3 → FirstOrder.Semiterm LX ℕ n₁) i)) =
      ![ω z, ω x, ω y] := by
    funext i; fin_cases i <;> rfl
  show ω ▹ (FirstOrder.Rew.subst ![z, x, y] ▹ addCode₁) = _
  rw [rew_subst_closed freeVariables_addCode₁ ω ![z, x, y], hv]
  rfl

theorem goodAt_eq {n : ℕ} (s g : FirstOrder.Semiterm LX ℕ n) :
    goodAt s g = goodBodyAt s g := by
  show FirstOrder.Rew.subst ![s, g] ▹
    ((Gentzen.formulaAt baseCode₁ ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2) ⋏
        Gentzen.addAt addCode₁ (#0 : FirstOrder.Semiterm LX ℕ 2)
          ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2) oneLX) ⋎
      (∃¹ ∃¹
        (Gentzen.precAt precCode₁ (#1 : FirstOrder.Semiterm LX ℕ 4) #3 ⋏
          (Gentzen.formulaAt baseCode₁ (#0 : FirstOrder.Semiterm LX ℕ 4) ⋏
            (epsAt epsCode₁ (#0 : FirstOrder.Semiterm LX ℕ 4) #1 ⋏
              Gentzen.addAt addCode₁ (#2 : FirstOrder.Semiterm LX ℕ 4) #0 oneLX))))) = _
  rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and,
    rew_formulaAt freeVariables_baseCode₁, rew_addAt',
    FirstOrder.Rewriting.app_exs, FirstOrder.Rewriting.app_exs,
    LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_and,
    rew_precAt' freeVariables_precCode₁, rew_formulaAt freeVariables_baseCode₁,
    rew_epsAt', rew_addAt']
  show (Gentzen.formulaAt baseCode₁ (FirstOrder.Rew.subst ![s, g]
      ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2)) ⋏
      Gentzen.addAt addCode₁ (FirstOrder.Rew.subst ![s, g] (#0 : FirstOrder.Semiterm LX ℕ 2))
        (FirstOrder.Rew.subst ![s, g] ((0 : ℕ) : FirstOrder.Semiterm LX ℕ 2))
        (FirstOrder.Rew.subst ![s, g] oneLX)) ⋎
    (∃¹ ∃¹
      (Gentzen.precAt precCode₁ ((FirstOrder.Rew.subst ![s, g]).q.q
            (#1 : FirstOrder.Semiterm LX ℕ 4))
          ((FirstOrder.Rew.subst ![s, g]).q.q #3) ⋏
        (Gentzen.formulaAt baseCode₁ ((FirstOrder.Rew.subst ![s, g]).q.q
            (#0 : FirstOrder.Semiterm LX ℕ 4)) ⋏
          (epsAt epsCode₁ ((FirstOrder.Rew.subst ![s, g]).q.q
              (#0 : FirstOrder.Semiterm LX ℕ 4))
              ((FirstOrder.Rew.subst ![s, g]).q.q #1) ⋏
            Gentzen.addAt addCode₁ ((FirstOrder.Rew.subst ![s, g]).q.q
                (#2 : FirstOrder.Semiterm LX ℕ 4))
              ((FirstOrder.Rew.subst ![s, g]).q.q #0)
              ((FirstOrder.Rew.subst ![s, g]).q.q oneLX))))) = _
  simp [FirstOrder.Rew.q_subst, goodBodyAt]

theorem goodSO_split {n : ℕ} (s g : FirstOrder.Semiterm LX ℕ n) :
    goodSO s g = goodASO s ⋎ goodBSO s g := by
  show toSOAtB segWitness (goodAt s g) = _
  rw [goodAt_eq]
  show toSOAtB segWitness
    ((Gentzen.formulaAt baseCode₁ ((0 : ℕ) : FirstOrder.Semiterm LX ℕ n) ⋏
        Gentzen.addAt addCode₁ s ((0 : ℕ) : FirstOrder.Semiterm LX ℕ n) oneLX) ⋎
      (∃¹ ∃¹
        (Gentzen.precAt precCode₁ (#1 : FirstOrder.Semiterm LX ℕ (n + 2))
            (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift g)) ⋏
          (Gentzen.formulaAt baseCode₁ (#0 : FirstOrder.Semiterm LX ℕ (n + 2)) ⋏
            (epsAt epsCode₁ (#0 : FirstOrder.Semiterm LX ℕ (n + 2)) #1 ⋏
              Gentzen.addAt addCode₁ (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift s))
                (#0 : FirstOrder.Semiterm LX ℕ (n + 2)) oneLX))))) = _
  rw [toSOAtB_or, toSOAtB_and, toSOAtB_exs, toSOAtB_exs, toSOAtB_and, toSOAtB_and,
    toSOAtB_and]
  rfl

theorem noSetFvar_goodASO {n : ℕ} (s : FirstOrder.Semiterm LX ℕ n) :
    NoSetFvar (goodASO s) := by
  show NoSetFvar (baseSO _ ⋏ addSO _ _ _)
  simp [noSetFvar_baseSO, noSetFvar_addSO]

theorem noSetFvar_goodBSO {n : ℕ} (s g : FirstOrder.Semiterm LX ℕ n) :
    NoSetFvar (goodBSO s g) := by
  show NoSetFvar (∃¹ ∃¹ (precSOv _ _ ⋏ (baseSO _ ⋏ (epsSO _ _ ⋏ addSO _ _ _))))
  simp [noSetFvar_precSOv, noSetFvar_baseSO, noSetFvar_epsSO, noSetFvar_addSO]

/-- The negated matrix of the second branch of `Good`. -/
def goodBNegBody {n : ℕ} (s g v h : FirstOrder.Semiterm LX ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  ∼(precSOv h g) ⋎ (∼(baseSO v) ⋎ (∼(epsSO v h) ⋎ ∼(addSO s v oneLX)))

theorem rew_goodBNegBody {n₁ n₂ : ℕ} {ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂}
    {ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂}
    (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (s g v h : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (goodBNegBody s g v h) = goodBNegBody (ω s) (ω g) (ω v) (ω h) := by
  show ω' ▹ (∼(precSOv h g) ⋎ (∼(baseSO v) ⋎ (∼(epsSO v h) ⋎ ∼(addSO s v oneLX)))) = _
  rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.HomClass.map_neg,
    rew_precSOv hb hf, rew_baseSO hb hf, rew_epsSO hb hf, rew_addSO hb hf]
  show ∼(precSOv (ω h) (ω g)) ⋎ (∼(baseSO (ω v)) ⋎ (∼(epsSO (ω v) (ω h)) ⋎
    ∼(addSO (ω s) (ω v) (ω oneLX)))) = _
  have hone : ω (oneLX : FirstOrder.Semiterm LX ℕ n₁) =
      (oneLX : FirstOrder.Semiterm LX ℕ n₂) := by simp
  rw [hone]
  rfl

/-- The matrix of `goodAllTI` (`g` then `s`). -/
noncomputable def goodBodySO {n : ℕ} (g s : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition ℒₒᵣ 0 n :=
  ∼(belowPsi g) ⋎ (∼(goodSO s g) ⋎ allTI s)

noncomputable def goodInner {n : ℕ} (g : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition ℒₒᵣ 0 n :=
  ∀¹ (goodBodySO (FirstOrder.Rew.bShift g) (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))

/-- `∀g ∀s (Below(ψ₀, g) → Good(s,g) → (∀²X TI(s,X)))`. -/
noncomputable def goodAll : Proposition ℒₒᵣ :=
  ∀¹ (goodInner (#0 : FirstOrder.Semiterm LX ℕ 1))

section RewGood

variable {n₁ n₂ : ℕ} {ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂} {ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂}

theorem rew_goodBodySO (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (g s : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (goodBodySO g s) = goodBodySO (ω g) (ω s) := by
  show ω' ▹ (∼(belowPsi g) ⋎ (∼(goodSO s g) ⋎ allTI s)) = _
  rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    rew_belowPsi hb hf, rew_goodSO hb hf, rew_allTI hb hf]
  rfl

theorem rew_goodInner (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (g : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (goodInner g) = goodInner (ω g) := by
  show ω' ▹ (∀¹ (goodBodySO (FirstOrder.Rew.bShift g)
    (#0 : FirstOrder.Semiterm LX ℕ (n₁ + 1)))) = _
  rw [Semiformula.rew_all₀, rew_goodBodySO (q_hb hb) (q_hf hf), q_bShift]
  show ∀¹ (goodBodySO (FirstOrder.Rew.bShift (ω g)) (ω.q #0)) = _
  simp only [FirstOrder.Rew.q_bvar_zero]
  rfl

end RewGood

/-- **`Good(s,g)` and `Below(ψ₀,g)` give `∀²X TI(≺₁,s,X)`.**  This is the whole
case split of the cover, and the only place `Below(ψ₀, g)` is consumed. -/
theorem goodAllTI : Provable ACA goodAll := by
  show Provable ACA (∀¹ (goodInner (#0 : FirstOrder.Semiterm LX ℕ 1)))
  refine gen₁ ACA_shift₀_invariant ?_
  have e1 : Semiproposition.free₀ (goodInner (#0 : FirstOrder.Semiterm LX ℕ 1)) =
      goodInner (&0 : FirstOrder.Semiterm LX ℕ 0) := by
    show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹
      (goodInner (#0 : FirstOrder.Semiterm LX ℕ 1)) = _
    rw [rew_goodInner (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
      hb_free hf_free]
    simp
  rw [e1]
  show Provable ACA (∀¹ (goodBodySO (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))
    (#0 : FirstOrder.Semiterm LX ℕ 1)))
  refine gen₁ ACA_shift₀_invariant ?_
  have e2 : Semiproposition.free₀ (goodBodySO
      (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))
      (#0 : FirstOrder.Semiterm LX ℕ 1)) =
      goodBodySO (&1 : FirstOrder.Semiterm LX ℕ 0) (&0) := by
    show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹ (goodBodySO _ _) = _
    rw [rew_goodBodySO (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
      hb_free hf_free]
    simp
  rw [e2]
  -- `g = &1`, `s = &0`
  have hbranchA : PSeq ACA [∼(goodASO (&0 : FirstOrder.Semiterm LX ℕ 0)),
      allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
      ∼(belowPsi (&1 : FirstOrder.Semiterm LX ℕ 0))] := by
    have hs := succ_inst (zeroLX : FirstOrder.Semiterm LX ℕ 0) (&0)
    have g0 : PSeq ACA [∼(baseSO (zeroLX : FirstOrder.Semiterm LX ℕ 0)),
        (∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX oneLX) ⋎
          (∼(allTI (zeroLX : FirstOrder.Semiterm LX ℕ 0)) ⋎
            allTI (&0 : FirstOrder.Semiterm LX ℕ 0)))] :=
      PSeq.orInv (PSeq.of_provable hs)
    have g1 : PSeq ACA [∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX oneLX),
        (∼(allTI (zeroLX : FirstOrder.Semiterm LX ℕ 0)) ⋎
          allTI (&0 : FirstOrder.Semiterm LX ℕ 0)),
        ∼(baseSO (zeroLX : FirstOrder.Semiterm LX ℕ 0))] :=
      PSeq.orInv (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) g0)
    have g2 : PSeq ACA [∼(allTI (zeroLX : FirstOrder.Semiterm LX ℕ 0)),
        allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
        ∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX oneLX),
        ∼(baseSO (zeroLX : FirstOrder.Semiterm LX ℕ 0))] :=
      PSeq.orInv (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) g1)
    have hcore : PSeq ACA [∼(baseSO (zeroLX : FirstOrder.Semiterm LX ℕ 0)),
        ∼(addSO (&0 : FirstOrder.Semiterm LX ℕ 0) zeroLX oneLX),
        allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
        ∼(belowPsi (&1 : FirstOrder.Semiterm LX ℕ 0))] := by
      refine PSeq.cut (allTI (zeroLX : FirstOrder.Semiterm LX ℕ 0)) ?_ ?_
      · exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
          (PSeq.of_provable allTI_zero)
      · exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) g2
    exact PSeq.or hcore
  have hbranchB : PSeq ACA [∼(goodBSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)),
      allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
      ∼(belowPsi (&1 : FirstOrder.Semiterm LX ℕ 0))] := by
    -- innermost: `v = &0`, `h = &1`, `s = &2`, `g = &3`
    have hmain : PSeq ACA [∼(precSOv (&1 : FirstOrder.Semiterm LX ℕ 0) (&3)),
        ∼(baseSO (&0 : FirstOrder.Semiterm LX ℕ 0)),
        ∼(epsSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)),
        ∼(addSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&0) oneLX),
        allTI (&2 : FirstOrder.Semiterm LX ℕ 0),
        ∼(belowPsi (&3 : FirstOrder.Semiterm LX ℕ 0))] := by
      refine PSeq.cut (allTI (&0 : FirstOrder.Semiterm LX ℕ 0)) ?_ ?_
      · -- `allTI &0` from `Below(ψ₀, &3)` at `h := &1` and `u := &0`
        refine PSeq.wk (Γ := [∼(belowPsi (&3 : FirstOrder.Semiterm LX ℕ 0)),
          ∼(precSOv (&1 : FirstOrder.Semiterm LX ℕ 0) (&3)),
          ∼(epsSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)),
          allTI (&0 : FirstOrder.Semiterm LX ℕ 0)])
          (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) ?_
        refine PSeq.exs₁ (&1 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) ?_
        have e3 : (FirstOrder.Rew.subst ![(&1 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)] ▹
            (∼(∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ 1)
                (FirstOrder.Rew.bShift (&3 : FirstOrder.Semiterm LX ℕ 0))) ⋎
              psiAt (#0 : FirstOrder.Semiterm LX ℕ 1))) : Proposition ℒₒᵣ) =
            precSOv (&1 : FirstOrder.Semiterm LX ℕ 0) (&3) ⋏
              ∼(psiAt (&1 : FirstOrder.Semiterm LX ℕ 0)) := by
          show (FirstOrder.Rew.subst ![(&1 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)]) ▹
            (∼(∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ 1)
                (FirstOrder.Rew.bShift (&3 : FirstOrder.Semiterm LX ℕ 0))) ⋎
              psiAt (#0 : FirstOrder.Semiterm LX ℕ 1))) = _
          show (FirstOrder.Rew.subst ![(&1 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)]) ▹
            ((∼(∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ 1)
                (FirstOrder.Rew.bShift (&3 : FirstOrder.Semiterm LX ℕ 0)))) ⋏
              ∼(psiAt (#0 : FirstOrder.Semiterm LX ℕ 1))) : Semiproposition ℒₒᵣ 0 1) = _
          rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg,
            LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_neg,
            rew_precSOv (ω := FirstOrder.Rew.subst
              ![(&1 : FirstOrder.Semiterm LX ℕ 0)]) (fun i => by simp) (fun x => by simp),
            rew_psiAt (ω := FirstOrder.Rew.subst
              ![(&1 : FirstOrder.Semiterm LX ℕ 0)]) (fun i => by simp) (fun x => by simp),
            Semiformula.neg_neg]
          simp
        show PSeq ACA ((FirstOrder.Rew.subst ![(&1 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)] ▹
          (∼(∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ 1)
              (FirstOrder.Rew.bShift (&3 : FirstOrder.Semiterm LX ℕ 0))) ⋎
            psiAt (#0 : FirstOrder.Semiterm LX ℕ 1))) : Proposition ℒₒᵣ) :: _)
        rw [e3]
        refine PSeq.and (PSeq.id (φ := precSOv (&1 : FirstOrder.Semiterm LX ℕ 0) (&3))
          (by simp) (by simp)) ?_
        refine PSeq.exs₁ (&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) ?_
        have e4 : (FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)] ▹
            (∼(∼(epsSO (#0 : FirstOrder.Semiterm LX ℕ 1)
                (FirstOrder.Rew.bShift (&1 : FirstOrder.Semiterm LX ℕ 0))) ⋎
              allTI (#0 : FirstOrder.Semiterm LX ℕ 1))) : Proposition ℒₒᵣ) =
            epsSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) ⋏
              ∼(allTI (&0 : FirstOrder.Semiterm LX ℕ 0)) := by
          show (FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)]) ▹
            ((∼(∼(epsSO (#0 : FirstOrder.Semiterm LX ℕ 1)
                (FirstOrder.Rew.bShift (&1 : FirstOrder.Semiterm LX ℕ 0)))) ⋏
              ∼(allTI (#0 : FirstOrder.Semiterm LX ℕ 1))) : Semiproposition ℒₒᵣ 0 1) = _
          rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg,
            LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_neg,
            rew_epsSO (ω := FirstOrder.Rew.subst
              ![(&0 : FirstOrder.Semiterm LX ℕ 0)]) (fun i => by simp) (fun x => by simp),
            rew_allTI (ω := FirstOrder.Rew.subst
              ![(&0 : FirstOrder.Semiterm LX ℕ 0)]) (fun i => by simp) (fun x => by simp),
            Semiformula.neg_neg]
          simp
        show PSeq ACA ((FirstOrder.Rew.subst ![(&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)] ▹
          (∼(∼(epsSO (#0 : FirstOrder.Semiterm LX ℕ 1)
              (FirstOrder.Rew.bShift (&1 : FirstOrder.Semiterm LX ℕ 0))) ⋎
            allTI (#0 : FirstOrder.Semiterm LX ℕ 1))) : Proposition ℒₒᵣ) :: _)
        rw [e4]
        exact PSeq.and (PSeq.id (φ := epsSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1))
          (by simp) (by simp))
          (PSeq.id (φ := allTI (&0 : FirstOrder.Semiterm LX ℕ 0)) (by simp) (by simp))
      · -- the successor step at `e := &0`, `s := &2`
        have hs := succ_inst (&0 : FirstOrder.Semiterm LX ℕ 0) (&2)
        have g0 : PSeq ACA [∼(baseSO (&0 : FirstOrder.Semiterm LX ℕ 0)),
            (∼(addSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&0) oneLX) ⋎
              (∼(allTI (&0 : FirstOrder.Semiterm LX ℕ 0)) ⋎
                allTI (&2 : FirstOrder.Semiterm LX ℕ 0)))] :=
          PSeq.orInv (PSeq.of_provable hs)
        have g1 : PSeq ACA [∼(addSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&0) oneLX),
            (∼(allTI (&0 : FirstOrder.Semiterm LX ℕ 0)) ⋎
              allTI (&2 : FirstOrder.Semiterm LX ℕ 0)),
            ∼(baseSO (&0 : FirstOrder.Semiterm LX ℕ 0))] :=
          PSeq.orInv (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) g0)
        have g2 : PSeq ACA [∼(allTI (&0 : FirstOrder.Semiterm LX ℕ 0)),
            allTI (&2 : FirstOrder.Semiterm LX ℕ 0),
            ∼(addSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&0) oneLX),
            ∼(baseSO (&0 : FirstOrder.Semiterm LX ℕ 0))] :=
          PSeq.orInv (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) g1)
        exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) g2
    -- fold the four literals into the matrix
    have hor1 : PSeq ACA [(∼(epsSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)) ⋎
          ∼(addSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&0) oneLX)),
        ∼(precSOv (&1 : FirstOrder.Semiterm LX ℕ 0) (&3)),
        ∼(baseSO (&0 : FirstOrder.Semiterm LX ℕ 0)),
        allTI (&2 : FirstOrder.Semiterm LX ℕ 0),
        ∼(belowPsi (&3 : FirstOrder.Semiterm LX ℕ 0))] :=
      PSeq.or (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hmain)
    have hor2 : PSeq ACA [(∼(baseSO (&0 : FirstOrder.Semiterm LX ℕ 0)) ⋎
          (∼(epsSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)) ⋎
            ∼(addSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&0) oneLX))),
        ∼(precSOv (&1 : FirstOrder.Semiterm LX ℕ 0) (&3)),
        allTI (&2 : FirstOrder.Semiterm LX ℕ 0),
        ∼(belowPsi (&3 : FirstOrder.Semiterm LX ℕ 0))] :=
      PSeq.or (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hor1)
    have hor3 : PSeq ACA [goodBNegBody (&2 : FirstOrder.Semiterm LX ℕ 0) (&3) (&0) (&1),
        allTI (&2 : FirstOrder.Semiterm LX ℕ 0),
        ∼(belowPsi (&3 : FirstOrder.Semiterm LX ℕ 0))] :=
      PSeq.or (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hor2)
    -- two eigenvariable steps
    have hall1 : PSeq ACA [∀¹ (goodBNegBody (&1 : FirstOrder.Semiterm LX ℕ 1) (&2)
        (#0 : FirstOrder.Semiterm LX ℕ 1) (&0)),
        allTI (&1 : FirstOrder.Semiterm LX ℕ 0),
        ∼(belowPsi (&2 : FirstOrder.Semiterm LX ℕ 0))] := by
      refine PSeq.all₁ ACA_shift₀_invariant ?_
      have hfree : Semiproposition.free₀ (goodBNegBody (&1 : FirstOrder.Semiterm LX ℕ 1) (&2)
          (#0 : FirstOrder.Semiterm LX ℕ 1) (&0)) =
          goodBNegBody (&2 : FirstOrder.Semiterm LX ℕ 0) (&3) (&0) (&1) := by
        show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹ (goodBNegBody _ _ _ _) = _
        rw [rew_goodBNegBody (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
          hb_free hf_free]
        simp
      have hsh : SecondOrder.Sequent.shift₀
          [allTI (&1 : FirstOrder.Semiterm LX ℕ 0),
            ∼(belowPsi (&2 : FirstOrder.Semiterm LX ℕ 0))] =
          [allTI (&2 : FirstOrder.Semiterm LX ℕ 0),
            ∼(belowPsi (&3 : FirstOrder.Semiterm LX ℕ 0))] := by
        simp only [SecondOrder.Sequent.shift₀, List.map_cons, List.map_nil,
          LogicalConnective.HomClass.map_neg, shift₀_allTI, shift₀_belowPsi]
        norm_num
      rw [hfree, hsh]
      exact hor3
    have hall2 : PSeq ACA [∀¹ (∀¹ (goodBNegBody
          (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0)))
          (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift (&1 : FirstOrder.Semiterm LX ℕ 0)))
          (#0 : FirstOrder.Semiterm LX ℕ 2) (#1))),
        allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
        ∼(belowPsi (&1 : FirstOrder.Semiterm LX ℕ 0))] := by
      refine PSeq.all₁ ACA_shift₀_invariant ?_
      have hfree : Semiproposition.free₀ (∀¹ (goodBNegBody
          (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0)))
          (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift (&1 : FirstOrder.Semiterm LX ℕ 0)))
          (#0 : FirstOrder.Semiterm LX ℕ 2) (#1))) =
          ∀¹ (goodBNegBody (&1 : FirstOrder.Semiterm LX ℕ 1) (&2)
            (#0 : FirstOrder.Semiterm LX ℕ 1) (&0)) := by
        show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹
          (∀¹ (goodBNegBody _ _ _ _)) = _
        have hfr : (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 2 ℕ 1)
            (#1 : FirstOrder.Semiterm LX ℕ 2) = (&0 : FirstOrder.Semiterm LX ℕ 1) := by
          have hl : (1 : Fin 2) = Fin.last 1 := rfl
          show (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 2 ℕ 1)
            (#(1 : Fin 2) : FirstOrder.Semiterm LX ℕ 2) = _
          rw [hl]
          exact FirstOrder.Rew.free_bvar_last
        rw [Semiformula.rew_all₀,
          rew_goodBNegBody (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0).q)
            (q_hb hb_free) (q_hf hf_free)]
        simp [hfr]
      have hsh : SecondOrder.Sequent.shift₀
          [allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
            ∼(belowPsi (&1 : FirstOrder.Semiterm LX ℕ 0))] =
          [allTI (&1 : FirstOrder.Semiterm LX ℕ 0),
            ∼(belowPsi (&2 : FirstOrder.Semiterm LX ℕ 0))] := by
        simp only [SecondOrder.Sequent.shift₀, List.map_cons, List.map_nil,
          LogicalConnective.HomClass.map_neg, shift₀_allTI, shift₀_belowPsi]
        norm_num
      rw [hfree, hsh]
      exact hall1
    exact hall2
  have hsplit : PSeq ACA [∼(goodSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)),
      allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
      ∼(belowPsi (&1 : FirstOrder.Semiterm LX ℕ 0))] := by
    rw [goodSO_split]
    exact PSeq.and hbranchA hbranchB
  have h2 : PSeq ACA [(∼(goodSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)) ⋎
        allTI (&0 : FirstOrder.Semiterm LX ℕ 0)),
      ∼(belowPsi (&1 : FirstOrder.Semiterm LX ℕ 0))] := PSeq.or hsplit
  exact PSeq.to_provable (PSeq.or
    (PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h2))

/-! ## Layer 2c: (Prog) -/

theorem good_inst (tg ts : FirstOrder.Semiterm LX ℕ 0) :
    Provable ACA (goodBodySO tg ts) := by
  have h1 := spec₁ goodAllTI (unTerm tg)
  have e1 : (goodInner (#0 : FirstOrder.Semiterm LX ℕ 1))/[unTerm tg] = goodInner tg := by
    have hv : (fun j => unTerm ((![tg] : Fin 1 → FirstOrder.Semiterm LX ℕ 0) j)) =
        ![unTerm tg] := by
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj; rfl
    show FirstOrder.Rew.subst ![unTerm tg] ▹ (goodInner (#0 : FirstOrder.Semiterm LX ℕ 1)) = _
    rw [← hv, rew_goodInner (ω := FirstOrder.Rew.subst ![tg]) (hb_subst _) (hf_subst _)]
    simp
  rw [e1] at h1
  have h1' : Provable ACA (∀¹ (goodBodySO (FirstOrder.Rew.bShift tg)
      (#0 : FirstOrder.Semiterm LX ℕ 1))) := h1
  have h2 := spec₁ h1' (unTerm ts)
  have e2 : (goodBodySO (FirstOrder.Rew.bShift tg)
      (#0 : FirstOrder.Semiterm LX ℕ 1))/[unTerm ts] = goodBodySO tg ts := by
    have hv : (fun j => unTerm ((![ts] : Fin 1 → FirstOrder.Semiterm LX ℕ 0) j)) =
        ![unTerm ts] := by
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj; rfl
    show FirstOrder.Rew.subst ![unTerm ts] ▹ (goodBodySO (FirstOrder.Rew.bShift tg)
      (#0 : FirstOrder.Semiterm LX ℕ 1)) = _
    rw [← hv, rew_goodBodySO (ω := FirstOrder.Rew.subst ![ts]) (hb_subst _) (hf_subst _)]
    simp
  rwa [e2] at h2

/-! ### The lifted universal hypothesis of the cover -/

noncomputable def hypMatrix {n : ℕ} (g x s k w : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition ℒₒᵣ 0 n :=
  ∼(goodSO s g) ⋎ (∼(towerSO w k s) ⋎ (∼(precSOv x w) ⋎ xSO x))

noncomputable def hypInner₁ {n : ℕ} (g x s k : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition ℒₒᵣ 0 n :=
  ∀¹ (hypMatrix (FirstOrder.Rew.bShift g) (FirstOrder.Rew.bShift x)
    (FirstOrder.Rew.bShift s) (FirstOrder.Rew.bShift k)
    (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))

noncomputable def hypInner₂ {n : ℕ} (g x s : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition ℒₒᵣ 0 n :=
  ∀¹ (hypInner₁ (FirstOrder.Rew.bShift g) (FirstOrder.Rew.bShift x)
    (FirstOrder.Rew.bShift s) (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))

noncomputable def hypSO {n : ℕ} (g x : FirstOrder.Semiterm LX ℕ n) :
    Semiproposition ℒₒᵣ 0 n :=
  ∀¹ (hypInner₂ (FirstOrder.Rew.bShift g) (FirstOrder.Rew.bShift x)
    (#0 : FirstOrder.Semiterm LX ℕ (n + 1)))

section RewHyp

variable {n₁ n₂ : ℕ} {ω : FirstOrder.Rew LX ℕ n₁ ℕ n₂} {ω' : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂}

theorem rew_hypMatrix (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (g x s k w : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (hypMatrix g x s k w) = hypMatrix (ω g) (ω x) (ω s) (ω k) (ω w) := by
  show ω' ▹ (∼(goodSO s g) ⋎ (∼(towerSO w k s) ⋎ (∼(precSOv x w) ⋎ xSO x))) = _
  rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    rew_goodSO hb hf, rew_towerSO hb hf, rew_precSOv hb hf, rew_xSO hb hf]
  rfl

theorem rew_hypInner₁ (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (g x s k : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (hypInner₁ g x s k) = hypInner₁ (ω g) (ω x) (ω s) (ω k) := by
  show ω' ▹ (∀¹ (hypMatrix (FirstOrder.Rew.bShift g) (FirstOrder.Rew.bShift x)
    (FirstOrder.Rew.bShift s) (FirstOrder.Rew.bShift k)
    (#0 : FirstOrder.Semiterm LX ℕ (n₁ + 1)))) = _
  rw [Semiformula.rew_all₀, rew_hypMatrix (q_hb hb) (q_hf hf),
    q_bShift, q_bShift, q_bShift, q_bShift]
  show ∀¹ (hypMatrix (FirstOrder.Rew.bShift (ω g)) (FirstOrder.Rew.bShift (ω x))
    (FirstOrder.Rew.bShift (ω s)) (FirstOrder.Rew.bShift (ω k)) (ω.q #0)) = _
  simp only [FirstOrder.Rew.q_bvar_zero]
  rfl

theorem rew_hypInner₂ (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (g x s : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (hypInner₂ g x s) = hypInner₂ (ω g) (ω x) (ω s) := by
  show ω' ▹ (∀¹ (hypInner₁ (FirstOrder.Rew.bShift g) (FirstOrder.Rew.bShift x)
    (FirstOrder.Rew.bShift s) (#0 : FirstOrder.Semiterm LX ℕ (n₁ + 1)))) = _
  rw [Semiformula.rew_all₀, rew_hypInner₁ (q_hb hb) (q_hf hf),
    q_bShift, q_bShift, q_bShift]
  show ∀¹ (hypInner₁ (FirstOrder.Rew.bShift (ω g)) (FirstOrder.Rew.bShift (ω x))
    (FirstOrder.Rew.bShift (ω s)) (ω.q #0)) = _
  simp only [FirstOrder.Rew.q_bvar_zero]
  rfl

theorem rew_hypSO (hb : ∀ i, unTerm (ω #i) = ω' #i) (hf : ∀ x, unTerm (ω &x) = ω' &x)
    (g x : FirstOrder.Semiterm LX ℕ n₁) :
    ω' ▹ (hypSO g x) = hypSO (ω g) (ω x) := by
  show ω' ▹ (∀¹ (hypInner₂ (FirstOrder.Rew.bShift g) (FirstOrder.Rew.bShift x)
    (#0 : FirstOrder.Semiterm LX ℕ (n₁ + 1)))) = _
  rw [Semiformula.rew_all₀, rew_hypInner₂ (q_hb hb) (q_hf hf), q_bShift, q_bShift]
  show ∀¹ (hypInner₂ (FirstOrder.Rew.bShift (ω g)) (FirstOrder.Rew.bShift (ω x))
    (ω.q #0)) = _
  simp only [FirstOrder.Rew.q_bvar_zero]
  rfl

end RewHyp

theorem toSOAtB_hypBodyAt {n : ℕ} (g x : FirstOrder.Semiterm LX ℕ n) :
    toSOAtB segWitness (hypBodyAt g x) = hypSO g x := by
  show toSOAtB segWitness (∀¹ ∀¹ ∀¹
    (∼(goodAt (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
          (#0 : FirstOrder.Semiterm LX ℕ (n + 1))))
        (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift g)))) ⋎
      (∼(Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
          (#0 : FirstOrder.Semiterm LX ℕ (n + 3))
          (FirstOrder.Rew.bShift (#0 : FirstOrder.Semiterm LX ℕ (n + 2)))
          (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
            (#0 : FirstOrder.Semiterm LX ℕ (n + 1))))) ⋎
        (∼(Gentzen.precAt precCode₁ (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
            (FirstOrder.Rew.bShift x))) (#0 : FirstOrder.Semiterm LX ℕ (n + 3))) ⋎
          Xat (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
            (FirstOrder.Rew.bShift x))))))) = _
  rw [toSOAtB_all, toSOAtB_all, toSOAtB_all, toSOAtB_or, toSOAtB_neg, toSOAtB_or,
    toSOAtB_neg, toSOAtB_or, toSOAtB_neg]
  rfl

/-! ### The lifted cover -/

theorem freeVariables_goodAt {n : ℕ} {s g : FirstOrder.Semiterm LX ℕ n}
    (hs : s.freeVariables = ∅) (hg : g.freeVariables = ∅) :
    (goodAt s g).freeVariables = ∅ :=
  Gentzen.LowerSyntax.freeVariables_rew_eq_empty _ freeVariables_goodBody (fun i => by
    fin_cases i
    · simpa using hs
    · simpa using hg)

theorem freeVariables_hypBodyAt {n : ℕ} {g x : FirstOrder.Semiterm LX ℕ n}
    (hg : g.freeVariables = ∅) (hx : x.freeVariables = ∅) :
    (hypBodyAt g x).freeVariables = ∅ := by
  have hbx : (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
      (FirstOrder.Rew.bShift x)) : FirstOrder.Semiterm LX ℕ (n + 3)).freeVariables = ∅ := by
    simpa using hx
  have hbg : (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
      (FirstOrder.Rew.bShift g)) : FirstOrder.Semiterm LX ℕ (n + 3)).freeVariables = ∅ := by
    simpa using hg
  have h1 : (goodAt (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
      (#0 : FirstOrder.Semiterm LX ℕ (n + 1))))
      (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
        (FirstOrder.Rew.bShift g)))).freeVariables = ∅ :=
    freeVariables_goodAt (by simp) hbg
  have h2 : (Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
      (#0 : FirstOrder.Semiterm LX ℕ (n + 3))
      (FirstOrder.Rew.bShift (#0 : FirstOrder.Semiterm LX ℕ (n + 2)))
      (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
        (#0 : FirstOrder.Semiterm LX ℕ (n + 1))))).freeVariables = ∅ :=
    freeVariables_towerAt (by simp) (by simp) (by simp)
  have h3 : (Gentzen.precAt precCode₁ (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
      (FirstOrder.Rew.bShift x))) (#0 : FirstOrder.Semiterm LX ℕ (n + 3))).freeVariables = ∅ :=
    Gentzen.LowerSyntax.freeVariables_precAt_eq_empty freeVariables_precCode₁ hbx (by simp)
  have h4 : (Xat (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
      (FirstOrder.Rew.bShift x)) : FirstOrder.Semiterm LX ℕ (n + 3))).freeVariables = ∅ := by
    simpa using hx
  show (∀¹ ∀¹ ∀¹ (∼(goodAt (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
      (#0 : FirstOrder.Semiterm LX ℕ (n + 1))))
      (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift g)))) ⋎
    (∼(Gentzen.VeblenTower.towerAt Gentzen.VeblenTower.towerCode₁
        (#0 : FirstOrder.Semiterm LX ℕ (n + 3))
        (FirstOrder.Rew.bShift (#0 : FirstOrder.Semiterm LX ℕ (n + 2)))
        (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
          (#0 : FirstOrder.Semiterm LX ℕ (n + 1))))) ⋎
      (∼(Gentzen.precAt precCode₁ (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
          (FirstOrder.Rew.bShift x))) (#0 : FirstOrder.Semiterm LX ℕ (n + 3))) ⋎
        Xat (FirstOrder.Rew.bShift (FirstOrder.Rew.bShift
          (FirstOrder.Rew.bShift x))))))).freeVariables = ∅
  simp only [FirstOrder.Semiformula.freeVariables_all, FirstOrder.Semiformula.freeVariables_or,
    FirstOrder.Semiformula.freeVariables_not, h1, h2, h3, h4, Finset.union_empty]

@[simp] theorem freeVariables_progCoverBody : progCoverBody.freeVariables = ∅ := by
  have h1 : (epsAt epsCode₁ (#1 : FirstOrder.Semiterm LX ℕ 3) #2).freeVariables = ∅ :=
    freeVariables_epsAt (by simp) (by simp)
  have h2 : (Gentzen.precAt precCode₁ (#0 : FirstOrder.Semiterm LX ℕ 3) #1).freeVariables = ∅ :=
    Gentzen.LowerSyntax.freeVariables_precAt_eq_empty freeVariables_precCode₁ (by simp) (by simp)
  have h3 : (progHypBody).freeVariables = ∅ :=
    freeVariables_hypBodyAt (by simp) (by simp)
  have h4 : (Xat (#0 : FirstOrder.Semiterm LX ℕ 3)).freeVariables = ∅ := by simp
  show (∼(epsAt epsCode₁ (#1 : FirstOrder.Semiterm LX ℕ 3) #2) ⋎
    (∼(Gentzen.precAt precCode₁ (#0 : FirstOrder.Semiterm LX ℕ 3) #1) ⋎
      (∼progHypBody ⋎ Xat (#0 : FirstOrder.Semiterm LX ℕ 3)))).freeVariables = ∅
  simp [h1, h2, h3, h4]

/-- The matrix of the lifted cover (`#2 = g`, `#1 = u`, `#0 = x`). -/
noncomputable def progCoverMatrixSO : Semiproposition ℒₒᵣ 0 3 :=
  ∼(epsSO (#1 : FirstOrder.Semiterm LX ℕ 3) #2) ⋎
    (∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ 3) #1) ⋎
      (∼(hypSO (#2 : FirstOrder.Semiterm LX ℕ 3) (#0)) ⋎
        xSO (#0 : FirstOrder.Semiterm LX ℕ 3)))

theorem progCover_SO : Provable ACA (∀¹ (∀¹ (∀¹ progCoverMatrixSO))) := by
  have h : Provable ACA (toSOAt segWitness (FirstOrder.Rewriting.emb progCoverStatement)) :=
    lift_paLX_seg concrete_progCover
  rw [show progCoverStatement = (∀¹ ∀¹ ∀¹ progCoverBody).univCl from rfl,
    TowerSyntax.emb_univCl_of_closed (by simp)] at h
  have e : toSOAt segWitness ((∀¹ (∀¹ (∀¹ progCoverBody))) :
      FirstOrder.Semiformula LX ℕ 0) = ∀¹ (∀¹ (∀¹ progCoverMatrixSO)) := by
    show ∀¹ (∀¹ (∀¹ (toSOAtB segWitness progCoverBody))) = _
    show ∀¹ (∀¹ (∀¹ (toSOAtB segWitness
      (∼(epsAt epsCode₁ (#1 : FirstOrder.Semiterm LX ℕ 3) #2) ⋎
        (∼(Gentzen.precAt precCode₁ (#0 : FirstOrder.Semiterm LX ℕ 3) #1) ⋎
          (∼(hypBodyAt (#2 : FirstOrder.Semiterm LX ℕ 3) (#0)) ⋎
            Xat (#0 : FirstOrder.Semiterm LX ℕ 3))))))) = _
    rw [toSOAtB_or, toSOAtB_neg, toSOAtB_or, toSOAtB_neg, toSOAtB_or, toSOAtB_neg,
      toSOAtB_hypBodyAt]
    rfl
  rwa [e] at h

theorem progCover_inst (tg tu tx : FirstOrder.Semiterm LX ℕ 0) :
    Provable ACA (∼(epsSO tu tg) ⋎ (∼(precSOv tx tu) ⋎ (∼(hypSO tg tx) ⋎ xSO tx))) := by
  have h := specNums progCoverMatrixSO
    (fun j => unTerm ((![tx, tu, tg] : Fin 3 → FirstOrder.Semiterm LX ℕ 0) j)) progCover_SO
  have e : (FirstOrder.Rew.subst
        (fun j => unTerm ((![tx, tu, tg] : Fin 3 → FirstOrder.Semiterm LX ℕ 0) j))) ▹
      progCoverMatrixSO =
      ∼(epsSO tu tg) ⋎ (∼(precSOv tx tu) ⋎ (∼(hypSO tg tx) ⋎ xSO tx)) := by
    show (FirstOrder.Rew.subst _) ▹
      (∼(epsSO (#1 : FirstOrder.Semiterm LX ℕ 3) #2) ⋎
        (∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ 3) #1) ⋎
          (∼(hypSO (#2 : FirstOrder.Semiterm LX ℕ 3) (#0)) ⋎
            xSO (#0 : FirstOrder.Semiterm LX ℕ 3)))) = _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
      LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
      LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
      rew_epsSO (hb_subst _) (hf_subst _), rew_precSOv (hb_subst _) (hf_subst _),
      rew_hypSO (hb_subst _) (hf_subst _), rew_xSO (hb_subst _) (hf_subst _)]
    simp
  rwa [e] at h

/-! ### (Prog) -/

/-- **(Prog).**  `ACA ⊢ Prog(≺₁, ψ₀)`: the `Π¹₁` formula
`ψ₀(g) :≡ ∀u (Eps(u,g) → ∀²X TI(≺₁,u,X))` is `≺₁`-progressive.

The second-order moves are exactly: one `∀²`-introduction (`all₂`), one
comprehension step (`exs₂` at the *free* set variable), four eigenvariable
introductions, and three `cut`s against the closed theorems `goodAllTI`,
`towerInduction` and the lifted cover. -/
theorem epsProg : Provable ACA (progPsi : Proposition ℒₒᵣ) := by
  -- `x = &0`, `u = &1`, `g = &2`
  have hΓ₀ : PSeq ACA [∼(precSOv (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)),
      xSO (&0 : FirstOrder.Semiterm LX ℕ 0),
      ∼(progSOX : Proposition ℒₒᵣ),
      ∼(epsSO (&1 : FirstOrder.Semiterm LX ℕ 0) (&2)),
      ∼(belowPsi (&2 : FirstOrder.Semiterm LX ℕ 0))] := by
    refine PSeq.cut (hypSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&0)) ?_ ?_
    · -- prove the universal hypothesis
      refine PSeq.all₁ ACA_shift₀_invariant ?_
      have hf1 : Semiproposition.free₀ (hypInner₂
          (FirstOrder.Rew.bShift (&2 : FirstOrder.Semiterm LX ℕ 0))
          (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))
          (#0 : FirstOrder.Semiterm LX ℕ 1)) =
          hypInner₂ (&3 : FirstOrder.Semiterm LX ℕ 0) (&1) (&0) := by
        show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹ (hypInner₂ _ _ _) = _
        rw [rew_hypInner₂ (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
          hb_free hf_free]
        simp
      have hs1 : SecondOrder.Sequent.shift₀
          [∼(precSOv (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)),
            xSO (&0 : FirstOrder.Semiterm LX ℕ 0),
            ∼(progSOX : Proposition ℒₒᵣ),
            ∼(epsSO (&1 : FirstOrder.Semiterm LX ℕ 0) (&2)),
            ∼(belowPsi (&2 : FirstOrder.Semiterm LX ℕ 0))] =
          [∼(precSOv (&1 : FirstOrder.Semiterm LX ℕ 0) (&2)),
            xSO (&1 : FirstOrder.Semiterm LX ℕ 0),
            ∼(progSOX : Proposition ℒₒᵣ),
            ∼(epsSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&3)),
            ∼(belowPsi (&3 : FirstOrder.Semiterm LX ℕ 0))] := by
        simp only [SecondOrder.Sequent.shift₀, List.map_cons, List.map_nil,
          LogicalConnective.HomClass.map_neg, shift₀_precSOv, shift₀_xSO,
          shift₀_progSOX, shift₀_epsSO, shift₀_belowPsi]
        norm_num
      rw [hf1, hs1]
      refine PSeq.all₁ ACA_shift₀_invariant ?_
      have hf2 : Semiproposition.free₀ (hypInner₁
          (FirstOrder.Rew.bShift (&3 : FirstOrder.Semiterm LX ℕ 0))
          (FirstOrder.Rew.bShift (&1 : FirstOrder.Semiterm LX ℕ 0))
          (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))
          (#0 : FirstOrder.Semiterm LX ℕ 1)) =
          hypInner₁ (&4 : FirstOrder.Semiterm LX ℕ 0) (&2) (&1) (&0) := by
        show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹ (hypInner₁ _ _ _ _) = _
        rw [rew_hypInner₁ (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
          hb_free hf_free]
        simp
      have hs2 : SecondOrder.Sequent.shift₀
          [∼(precSOv (&1 : FirstOrder.Semiterm LX ℕ 0) (&2)),
            xSO (&1 : FirstOrder.Semiterm LX ℕ 0),
            ∼(progSOX : Proposition ℒₒᵣ),
            ∼(epsSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&3)),
            ∼(belowPsi (&3 : FirstOrder.Semiterm LX ℕ 0))] =
          [∼(precSOv (&2 : FirstOrder.Semiterm LX ℕ 0) (&3)),
            xSO (&2 : FirstOrder.Semiterm LX ℕ 0),
            ∼(progSOX : Proposition ℒₒᵣ),
            ∼(epsSO (&3 : FirstOrder.Semiterm LX ℕ 0) (&4)),
            ∼(belowPsi (&4 : FirstOrder.Semiterm LX ℕ 0))] := by
        simp only [SecondOrder.Sequent.shift₀, List.map_cons, List.map_nil,
          LogicalConnective.HomClass.map_neg, shift₀_precSOv, shift₀_xSO,
          shift₀_progSOX, shift₀_epsSO, shift₀_belowPsi]
        norm_num
      rw [hf2, hs2]
      refine PSeq.all₁ ACA_shift₀_invariant ?_
      have hf3 : Semiproposition.free₀ (hypMatrix
          (FirstOrder.Rew.bShift (&4 : FirstOrder.Semiterm LX ℕ 0))
          (FirstOrder.Rew.bShift (&2 : FirstOrder.Semiterm LX ℕ 0))
          (FirstOrder.Rew.bShift (&1 : FirstOrder.Semiterm LX ℕ 0))
          (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))
          (#0 : FirstOrder.Semiterm LX ℕ 1)) =
          hypMatrix (&5 : FirstOrder.Semiterm LX ℕ 0) (&3) (&2) (&1) (&0) := by
        show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹ (hypMatrix _ _ _ _ _) = _
        rw [rew_hypMatrix (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
          hb_free hf_free]
        simp
      have hs3 : SecondOrder.Sequent.shift₀
          [∼(precSOv (&2 : FirstOrder.Semiterm LX ℕ 0) (&3)),
            xSO (&2 : FirstOrder.Semiterm LX ℕ 0),
            ∼(progSOX : Proposition ℒₒᵣ),
            ∼(epsSO (&3 : FirstOrder.Semiterm LX ℕ 0) (&4)),
            ∼(belowPsi (&4 : FirstOrder.Semiterm LX ℕ 0))] =
          [∼(precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&4)),
            xSO (&3 : FirstOrder.Semiterm LX ℕ 0),
            ∼(progSOX : Proposition ℒₒᵣ),
            ∼(epsSO (&4 : FirstOrder.Semiterm LX ℕ 0) (&5)),
            ∼(belowPsi (&5 : FirstOrder.Semiterm LX ℕ 0))] := by
        simp only [SecondOrder.Sequent.shift₀, List.map_cons, List.map_nil,
          LogicalConnective.HomClass.map_neg, shift₀_precSOv, shift₀_xSO,
          shift₀_progSOX, shift₀_epsSO, shift₀_belowPsi]
        norm_num
      rw [hf3, hs3]
      -- `w = &0`, `k = &1`, `s = &2`, `x = &3`, `u = &4`, `g = &5`
      have hcore : PSeq ACA [∼(precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&0)),
          xSO (&3 : FirstOrder.Semiterm LX ℕ 0),
          ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) (&2)),
          ∼(goodSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&5)),
          ∼(precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&4)),
          xSO (&3 : FirstOrder.Semiterm LX ℕ 0),
          ∼(progSOX : Proposition ℒₒᵣ),
          ∼(epsSO (&4 : FirstOrder.Semiterm LX ℕ 0) (&5)),
          ∼(belowPsi (&5 : FirstOrder.Semiterm LX ℕ 0))] := by
        refine PSeq.cut (allTI (&2 : FirstOrder.Semiterm LX ℕ 0)) ?_ ?_
        · -- `allTI &2` from `goodAllTI`
          have hg := good_inst (&5 : FirstOrder.Semiterm LX ℕ 0) (&2)
          have g0 : PSeq ACA [∼(belowPsi (&5 : FirstOrder.Semiterm LX ℕ 0)),
              (∼(goodSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&5)) ⋎
                allTI (&2 : FirstOrder.Semiterm LX ℕ 0))] :=
            PSeq.orInv (PSeq.of_provable hg)
          have g1 : PSeq ACA [∼(goodSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&5)),
              allTI (&2 : FirstOrder.Semiterm LX ℕ 0),
              ∼(belowPsi (&5 : FirstOrder.Semiterm LX ℕ 0))] :=
            PSeq.orInv (PSeq.wk (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto) g0)
          exact PSeq.wk (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto) g1
        · refine PSeq.cut (allTI (&0 : FirstOrder.Semiterm LX ℕ 0)) ?_ ?_
          · -- `allTI &0` from the tower induction
            have ht := towerInd_inst (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) (&2)
            have g0 : PSeq ACA [∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) (&2)),
                (∼(allTI (&2 : FirstOrder.Semiterm LX ℕ 0)) ⋎
                  allTI (&0 : FirstOrder.Semiterm LX ℕ 0))] :=
              PSeq.orInv (PSeq.of_provable ht)
            have g1 : PSeq ACA [∼(allTI (&2 : FirstOrder.Semiterm LX ℕ 0)),
                allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
                ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) (&2))] :=
              PSeq.orInv (PSeq.wk (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto) g0)
            exact PSeq.wk (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto) g1
          · -- comprehension: instantiate the `∀²` at the free set variable
            have key : PSeq ACA
                (Semiproposition.subst₁ (∼(toSOAtB boundWitness
                    (tiX (&0 : FirstOrder.Semiterm LX ℕ 0)))) ![freeWitness] ::
                  [∼(allTI (&2 : FirstOrder.Semiterm LX ℕ 0)),
                    ∼(precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&0)),
                    xSO (&3 : FirstOrder.Semiterm LX ℕ 0),
                    ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) (&2)),
                    ∼(goodSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&5)),
                    ∼(precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&4)),
                    ∼(progSOX : Proposition ℒₒᵣ),
                    ∼(epsSO (&4 : FirstOrder.Semiterm LX ℕ 0) (&5)),
                    ∼(belowPsi (&5 : FirstOrder.Semiterm LX ℕ 0))]) := by
              rw [neg_subst₁_tiBody_free]
              have hneg : ∼(tiSO (&0 : FirstOrder.Semiterm LX ℕ 0)) =
                  (progSOX : Proposition ℒₒᵣ) ⋏
                    ∼(belowSOX (&0 : FirstOrder.Semiterm LX ℕ 0)) := by
                rw [tiSO_eq]
                show (∼(∼(progSOX : Proposition ℒₒᵣ))) ⋏
                  ∼(belowSOX (&0 : FirstOrder.Semiterm LX ℕ 0)) = _
                rw [Semiformula.neg_neg]
              rw [hneg]
              refine PSeq.and (PSeq.id (φ := (progSOX : Proposition ℒₒᵣ))
                (by simp) (by simp)) ?_
              have hb : ∼(belowSOX (&0 : FirstOrder.Semiterm LX ℕ 0)) =
                  ∃¹ (∼(∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ 1)
                      (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))) ⋎
                    xSO (#0 : FirstOrder.Semiterm LX ℕ 1))) := by
                rw [belowSOX_eq]
                rfl
              rw [hb]
              refine PSeq.exs₁ (&3 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) ?_
              have e5 : (FirstOrder.Rew.subst ![(&3 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)] ▹
                  (∼(∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ 1)
                      (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))) ⋎
                    xSO (#0 : FirstOrder.Semiterm LX ℕ 1))) : Proposition ℒₒᵣ) =
                  precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&0) ⋏
                    ∼(xSO (&3 : FirstOrder.Semiterm LX ℕ 0)) := by
                show (FirstOrder.Rew.subst ![(&3 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)]) ▹
                  ((∼(∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ 1)
                      (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0)))) ⋏
                    ∼(xSO (#0 : FirstOrder.Semiterm LX ℕ 1))) :
                      Semiproposition ℒₒᵣ 0 1) = _
                rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg,
                  LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_neg,
                  rew_precSOv (ω := FirstOrder.Rew.subst
                    ![(&3 : FirstOrder.Semiterm LX ℕ 0)]) (fun i => by simp)
                    (fun y => by simp),
                  rew_xSO (ω := FirstOrder.Rew.subst
                    ![(&3 : FirstOrder.Semiterm LX ℕ 0)]) (fun i => by simp)
                    (fun y => by simp),
                  Semiformula.neg_neg]
                simp
              show PSeq ACA ((FirstOrder.Rew.subst ![(&3 : FirstOrder.Semiterm ℒₒᵣ ℕ 0)] ▹
                (∼(∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ 1)
                    (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))) ⋎
                  xSO (#0 : FirstOrder.Semiterm LX ℕ 1))) : Proposition ℒₒᵣ) :: _)
              rw [e5]
              exact PSeq.and
                (PSeq.id (φ := precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&0))
                  (by simp) (by simp))
                (PSeq.id (φ := xSO (&3 : FirstOrder.Semiterm LX ℕ 0)) (by simp) (by simp))
            exact PSeq.wk (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto)
              (PSeq.exs₂ arith_freeWitness key)
      have o1 : PSeq ACA [(∼(precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&0)) ⋎
            xSO (&3 : FirstOrder.Semiterm LX ℕ 0)),
          ∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) (&2)),
          ∼(goodSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&5)),
          ∼(precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&4)),
          xSO (&3 : FirstOrder.Semiterm LX ℕ 0),
          ∼(progSOX : Proposition ℒₒᵣ),
          ∼(epsSO (&4 : FirstOrder.Semiterm LX ℕ 0) (&5)),
          ∼(belowPsi (&5 : FirstOrder.Semiterm LX ℕ 0))] := PSeq.or hcore
      have o2 : PSeq ACA [∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) (&2)),
          (∼(precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&0)) ⋎
            xSO (&3 : FirstOrder.Semiterm LX ℕ 0)),
          ∼(goodSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&5)),
          ∼(precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&4)),
          xSO (&3 : FirstOrder.Semiterm LX ℕ 0),
          ∼(progSOX : Proposition ℒₒᵣ),
          ∼(epsSO (&4 : FirstOrder.Semiterm LX ℕ 0) (&5)),
          ∼(belowPsi (&5 : FirstOrder.Semiterm LX ℕ 0))] :=
        PSeq.wk (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto) o1
      have o3 : PSeq ACA [(∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) (&2)) ⋎
            (∼(precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&0)) ⋎
              xSO (&3 : FirstOrder.Semiterm LX ℕ 0))),
          ∼(goodSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&5)),
          ∼(precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&4)),
          xSO (&3 : FirstOrder.Semiterm LX ℕ 0),
          ∼(progSOX : Proposition ℒₒᵣ),
          ∼(epsSO (&4 : FirstOrder.Semiterm LX ℕ 0) (&5)),
          ∼(belowPsi (&5 : FirstOrder.Semiterm LX ℕ 0))] := PSeq.or o2
      have o4 : PSeq ACA [∼(goodSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&5)),
          (∼(towerSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1) (&2)) ⋎
            (∼(precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&0)) ⋎
              xSO (&3 : FirstOrder.Semiterm LX ℕ 0))),
          ∼(precSOv (&3 : FirstOrder.Semiterm LX ℕ 0) (&4)),
          xSO (&3 : FirstOrder.Semiterm LX ℕ 0),
          ∼(progSOX : Proposition ℒₒᵣ),
          ∼(epsSO (&4 : FirstOrder.Semiterm LX ℕ 0) (&5)),
          ∼(belowPsi (&5 : FirstOrder.Semiterm LX ℕ 0))] :=
        PSeq.wk (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto) o3
      exact PSeq.or o4
    · -- the lifted cover supplies `∼W`
      have hc := progCover_inst (&2 : FirstOrder.Semiterm LX ℕ 0) (&1) (&0)
      have g0 : PSeq ACA [∼(epsSO (&1 : FirstOrder.Semiterm LX ℕ 0) (&2)),
          (∼(precSOv (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)) ⋎
            (∼(hypSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&0)) ⋎
              xSO (&0 : FirstOrder.Semiterm LX ℕ 0)))] :=
        PSeq.orInv (PSeq.of_provable hc)
      have g1 : PSeq ACA [∼(precSOv (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)),
          (∼(hypSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&0)) ⋎
            xSO (&0 : FirstOrder.Semiterm LX ℕ 0)),
          ∼(epsSO (&1 : FirstOrder.Semiterm LX ℕ 0) (&2))] :=
        PSeq.orInv (PSeq.wk (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto) g0)
      have g2 : PSeq ACA [∼(hypSO (&2 : FirstOrder.Semiterm LX ℕ 0) (&0)),
          xSO (&0 : FirstOrder.Semiterm LX ℕ 0),
          ∼(precSOv (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)),
          ∼(epsSO (&1 : FirstOrder.Semiterm LX ℕ 0) (&2))] :=
        PSeq.orInv (PSeq.wk (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto) g1)
      exact PSeq.wk (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto) g2
  -- wrap up: `∀x`, `∀²X`, `∀u`, `∀g`
  have hStepC : PSeq ACA [belowSOX (&0 : FirstOrder.Semiterm LX ℕ 0),
      ∼(progSOX : Proposition ℒₒᵣ),
      ∼(epsSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)),
      ∼(belowPsi (&1 : FirstOrder.Semiterm LX ℕ 0))] := by
    rw [belowSOX_eq]
    refine PSeq.all₁ ACA_shift₀_invariant ?_
    have hfree : Semiproposition.free₀ (∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ 1)
        (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))) ⋎
      xSO (#0 : FirstOrder.Semiterm LX ℕ 1)) =
        ∼(precSOv (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)) ⋎
          xSO (&0 : FirstOrder.Semiterm LX ℕ 0) := by
      show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹ _ = _
      rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
        rew_precSOv (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0))
          hb_free hf_free,
        rew_xSO (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0)) hb_free hf_free]
      simp
    have hsh : SecondOrder.Sequent.shift₀
        [∼(progSOX : Proposition ℒₒᵣ),
          ∼(epsSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)),
          ∼(belowPsi (&1 : FirstOrder.Semiterm LX ℕ 0))] =
        [∼(progSOX : Proposition ℒₒᵣ),
          ∼(epsSO (&1 : FirstOrder.Semiterm LX ℕ 0) (&2)),
          ∼(belowPsi (&2 : FirstOrder.Semiterm LX ℕ 0))] := by
      simp only [SecondOrder.Sequent.shift₀, List.map_cons, List.map_nil,
        LogicalConnective.HomClass.map_neg, shift₀_progSOX, shift₀_epsSO, shift₀_belowPsi]
      norm_num
    rw [hfree, hsh]
    exact PSeq.or hΓ₀
  have hStepE : PSeq ACA [allTI (&0 : FirstOrder.Semiterm LX ℕ 0),
      ∼(epsSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)),
      ∼(belowPsi (&1 : FirstOrder.Semiterm LX ℕ 0))] := by
    refine PSeq.all₂ ACA_shift₁_invariant ?_
    have hshift₁ : SecondOrder.Sequent.shift₁
        [∼(epsSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)),
          ∼(belowPsi (&1 : FirstOrder.Semiterm LX ℕ 0))] =
        [∼(epsSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)),
          ∼(belowPsi (&1 : FirstOrder.Semiterm LX ℕ 0))] := by
      simp only [SecondOrder.Sequent.shift₁, List.map_cons, List.map_nil,
        LogicalConnective.HomClass.map_neg,
        shift₁_eq_self_of_noSetFvar
          (noSetFvar_epsSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)),
        shift₁_eq_self_of_noSetFvar
          (noSetFvar_belowPsi (&1 : FirstOrder.Semiterm LX ℕ 0))]
    rw [hshift₁, free₁_tiBody, tiSO_eq]
    exact PSeq.or (PSeq.wk (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto) hStepC)
  have hStepG : PSeq ACA [psiAt (&0 : FirstOrder.Semiterm LX ℕ 0),
      ∼(belowPsi (&0 : FirstOrder.Semiterm LX ℕ 0))] := by
    refine PSeq.all₁ ACA_shift₀_invariant ?_
    have hfree : Semiproposition.free₀ (∼(epsSO (#0 : FirstOrder.Semiterm LX ℕ 1)
        (FirstOrder.Rew.bShift (&0 : FirstOrder.Semiterm LX ℕ 0))) ⋎
      allTI (#0 : FirstOrder.Semiterm LX ℕ 1)) =
        ∼(epsSO (&0 : FirstOrder.Semiterm LX ℕ 0) (&1)) ⋎
          allTI (&0 : FirstOrder.Semiterm LX ℕ 0) := by
      show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹ _ = _
      rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
        rew_epsSO (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0)) hb_free hf_free,
        rew_allTI (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0)) hb_free hf_free]
      simp
    have hsh : SecondOrder.Sequent.shift₀
        [∼(belowPsi (&0 : FirstOrder.Semiterm LX ℕ 0))] =
        [∼(belowPsi (&1 : FirstOrder.Semiterm LX ℕ 0))] := by
      simp only [SecondOrder.Sequent.shift₀, List.map_cons, List.map_nil,
        LogicalConnective.HomClass.map_neg, shift₀_belowPsi]
      norm_num
    rw [hfree, hsh]
    exact PSeq.or (PSeq.wk (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto) hStepE)
  show Provable ACA (∀¹ (∼(belowPsi (#0 : FirstOrder.Semiterm LX ℕ 1)) ⋎
    psiAt (#0 : FirstOrder.Semiterm LX ℕ 1)))
  refine gen₁ ACA_shift₀_invariant ?_
  have e0 : Semiproposition.free₀ (∼(belowPsi (#0 : FirstOrder.Semiterm LX ℕ 1)) ⋎
      psiAt (#0 : FirstOrder.Semiterm LX ℕ 1)) =
      ∼(belowPsi (&0 : FirstOrder.Semiterm LX ℕ 0)) ⋎
        psiAt (&0 : FirstOrder.Semiterm LX ℕ 0) := by
    show (FirstOrder.Rew.free : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 0) ▹ _ = _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
      rew_belowPsi (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0)) hb_free hf_free,
      rew_psiAt (ω := (FirstOrder.Rew.free : FirstOrder.Rew LX ℕ 1 ℕ 0)) hb_free hf_free]
    simp
  rw [e0]
  exact PSeq.to_provable (PSeq.or
    (PSeq.wk (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto) hStepG))

/-! ## (Final): `ACA ⊢ ∀²X TI(≺₁, ε̄_c, X)` -/

open Ordinal in
private theorem vtower_lt_eps0 (n : ℕ) :
    Gentzen.VeblenEpsilon0UpperBound.vtower n < Gamma0Note.epsilonNote 0 := by
  rw [Gamma0Note.lt_def, Gamma0Note.epsilonNote_zero_repr,
    Gentzen.VeblenEpsilon0UpperBound.repr_vtower]
  exact Ordinal.iterate_omega0_opow_lt_epsilon_zero n

/-- **The remaining hypothesis of `aca_theorem_of_ti_epsilon`.**

For every Veblen notation `c < ε₀`, `ACA` proves `∀²X TI(≺₁, ε̄_c, X)`. -/
theorem ti_epsilon_all (c : Gamma0Note) (hc : c < Gamma0Note.epsilonNote 0) :
    Provable ACA (allTI (Gentzen.Epsilon1UpperBound.gamma0Term
      (Gamma0Note.epsilonNote c))) := by
  obtain ⟨n, hcn⟩ := Gentzen.VeblenEpsilon0UpperBound.exists_lt_vtower c hc
  set c' : Gamma0Note := Gentzen.VeblenEpsilon0UpperBound.vtower n with hc'
  -- (TIψ) + (Prog)
  have h1 : Provable ACA (belowPsi (Gentzen.Epsilon1UpperBound.gamma0Term c')) :=
    cutP epsProg (tiPsi c' (vtower_lt_eps0 n))
  -- instantiate at `g := c̄`
  have h2 := spec₁ h1 (unTerm (Gentzen.Epsilon1UpperBound.gamma0Term c))
  have e2 : (∼(precSOv (#0 : FirstOrder.Semiterm LX ℕ 1)
        (FirstOrder.Rew.bShift (Gentzen.Epsilon1UpperBound.gamma0Term c'))) ⋎
      psiAt (#0 : FirstOrder.Semiterm LX ℕ 1))/[unTerm
        (Gentzen.Epsilon1UpperBound.gamma0Term c)] =
      ∼(precSOv (Gentzen.Epsilon1UpperBound.gamma0Term c)
          (Gentzen.Epsilon1UpperBound.gamma0Term c')) ⋎
        psiAt (Gentzen.Epsilon1UpperBound.gamma0Term c) := by
    have hv : (fun j => unTerm ((![Gentzen.Epsilon1UpperBound.gamma0Term c] :
        Fin 1 → FirstOrder.Semiterm LX ℕ 0) j)) =
        ![unTerm (Gentzen.Epsilon1UpperBound.gamma0Term c)] := by
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj; rfl
    show FirstOrder.Rew.subst ![unTerm (Gentzen.Epsilon1UpperBound.gamma0Term c)] ▹ _ = _
    rw [← hv, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
      rew_precSOv (ω := FirstOrder.Rew.subst
        ![Gentzen.Epsilon1UpperBound.gamma0Term c]) (hb_subst _) (hf_subst _),
      rew_psiAt (ω := FirstOrder.Rew.subst
        ![Gentzen.Epsilon1UpperBound.gamma0Term c]) (hb_subst _) (hf_subst _)]
    simp
  rw [e2] at h2
  -- `c̄ ≺₁ c̄'`
  have hprec : Provable ACA (precSOv (Gentzen.Epsilon1UpperBound.gamma0Term c)
      (Gentzen.Epsilon1UpperBound.gamma0Term c')) := by
    have h := lift_paLX_seg (Gentzen.Epsilon1UpperBound.concrete_gamma0_prec hcn)
    have hcl : (Gentzen.precAt precCode₁ (Gentzen.Epsilon1UpperBound.gamma0Term c)
        (Gentzen.Epsilon1UpperBound.gamma0Term c')).freeVariables = ∅ :=
      Gentzen.LowerSyntax.freeVariables_precAt_eq_empty freeVariables_precCode₁
        (by simp [Gentzen.Epsilon1UpperBound.gamma0Term])
        (by simp [Gentzen.Epsilon1UpperBound.gamma0Term])
    rw [show Gentzen.Epsilon1UpperBound.closedPrec₁
        (Gentzen.Epsilon1UpperBound.gamma0Term c)
        (Gentzen.Epsilon1UpperBound.gamma0Term c') =
        (Gentzen.precAt precCode₁ (Gentzen.Epsilon1UpperBound.gamma0Term c)
          (Gentzen.Epsilon1UpperBound.gamma0Term c')).univCl from rfl,
      TowerSyntax.emb_univCl_of_closed hcl] at h
    exact h
  have h3 : Provable ACA (psiAt (Gentzen.Epsilon1UpperBound.gamma0Term c)) :=
    cutP hprec h2
  -- instantiate at `u := ε̄_c`
  have h4 := spec₁ h3 (unTerm (Gentzen.Epsilon1UpperBound.gamma0Term
    (Gamma0Note.epsilonNote c)))
  have e4 : (∼(epsSO (#0 : FirstOrder.Semiterm LX ℕ 1)
        (FirstOrder.Rew.bShift (Gentzen.Epsilon1UpperBound.gamma0Term c))) ⋎
      allTI (#0 : FirstOrder.Semiterm LX ℕ 1))/[unTerm
        (Gentzen.Epsilon1UpperBound.gamma0Term (Gamma0Note.epsilonNote c))] =
      ∼(epsSO (Gentzen.Epsilon1UpperBound.gamma0Term (Gamma0Note.epsilonNote c))
          (Gentzen.Epsilon1UpperBound.gamma0Term c)) ⋎
        allTI (Gentzen.Epsilon1UpperBound.gamma0Term (Gamma0Note.epsilonNote c)) := by
    have hv : (fun j => unTerm ((![Gentzen.Epsilon1UpperBound.gamma0Term
        (Gamma0Note.epsilonNote c)] : Fin 1 → FirstOrder.Semiterm LX ℕ 0) j)) =
        ![unTerm (Gentzen.Epsilon1UpperBound.gamma0Term (Gamma0Note.epsilonNote c))] := by
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj; rfl
    show FirstOrder.Rew.subst ![unTerm (Gentzen.Epsilon1UpperBound.gamma0Term
      (Gamma0Note.epsilonNote c))] ▹ _ = _
    rw [← hv, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
      rew_epsSO (ω := FirstOrder.Rew.subst
        ![Gentzen.Epsilon1UpperBound.gamma0Term (Gamma0Note.epsilonNote c)])
        (hb_subst _) (hf_subst _),
      rew_allTI (ω := FirstOrder.Rew.subst
        ![Gentzen.Epsilon1UpperBound.gamma0Term (Gamma0Note.epsilonNote c)])
        (hb_subst _) (hf_subst _)]
    simp
  rw [e4] at h4
  -- `Eps(ε̄_c, c̄)`
  have heps : Provable ACA (epsSO (Gentzen.Epsilon1UpperBound.gamma0Term
      (Gamma0Note.epsilonNote c)) (Gentzen.Epsilon1UpperBound.gamma0Term c)) := by
    have h := lift_paLX_seg (concrete_epsValue c)
    have hcl : (epsAt epsCode₁ (Gentzen.Epsilon1UpperBound.gamma0Term
        (Gamma0Note.epsilonNote c))
        (Gentzen.Epsilon1UpperBound.gamma0Term c)).freeVariables = ∅ :=
      freeVariables_epsAt (by simp [Gentzen.Epsilon1UpperBound.gamma0Term])
        (by simp [Gentzen.Epsilon1UpperBound.gamma0Term])
    rw [show epsValueStatement c = (epsAt epsCode₁
        (Gentzen.Epsilon1UpperBound.gamma0Term (Gamma0Note.epsilonNote c))
        (Gentzen.Epsilon1UpperBound.gamma0Term c)).univCl from rfl,
      TowerSyntax.emb_univCl_of_closed hcl] at h
    exact h
  exact cutP heps h4

end OrdinalAnalysis.ACA
