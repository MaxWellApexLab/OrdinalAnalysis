/-
  The formulas of the generalised descent at numerals: their meaning in an
  arbitrary `LRA`-structure, their truth in `ℕ`, their free variables, levels and
  ranks.

  * `precA x v`: `x ≺₁ v`;  `vebA u a g`: `u = φ_a(g)`;  `epsA u g`: `u = ε_g`
    (the arithmetical graphs of the Veblen notation system, at numerals).
  * `memA μ x z`: `x ∈̇_μ z`;  `progA μ z`: `Prog(≺₁, λy. y ∈̇_μ z)`.
  * `accA μ v`: `Acc_μ(v) :≡ ∀z TI(≺₁, v, λx. x ∈̇_μ z)` at the numeral `v`, which is
    `∀¹ accBody μ v`; the instance of `accBody μ v` at a numeral `z` says
    `TI(≺₁, v, λx. x ∈̇_μ z)` (`eval_accBody_inst`).

  In `ℕ` the order and the graphs are decided on the notations: a numeral
  satisfies the normal-form recogniser exactly when it is the code of a notation
  (`VNoteBridge.isNF₁_surj`), the internal comparison is the order of the
  notations, and the internal Veblen function computes `veblenNote` on codes.
-/
import OrdinalAnalysis.Ramified.DescentBetaAux2
import OrdinalAnalysis.Ramified.CopyR
import OrdinalAnalysis.Ramified.EffLevel
import OrdinalAnalysis.Gentzen.InternalVeblenCode
import OrdinalAnalysis.Gentzen.ProgStep

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalVNote (precDef₁ eval_precDef₁ isNF₁)
open OrdinalAnalysis.Gentzen.InternalVeblenCode (vebDef₁ eval_vebDef₁)
open OrdinalAnalysis.Gentzen.InternalEpsMonoCode (epsDef₁ eval_epsDef₁)
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)

/-! ### The formulas -/

/-- `x ≺₁ v`. -/
def precA (x v : ℕ) : Proposition LRA := arAt precDef₁.val ![numAtR x, numAtR v]

/-- `u = φ_a(g)`. -/
def vebA (u a g : ℕ) : Proposition LRA := arAt vebDef₁.val ![numAtR u, numAtR a, numAtR g]

/-- `u = ε_g`. -/
def epsA (u g : ℕ) : Proposition LRA := arAt epsDef₁.val ![numAtR u, numAtR g]

/-- `x ∈̇_μ z`. -/
def memA (μ : Lv) (x z : ℕ) : Proposition LRA := memAt μ (numAtR x) (numAtR z)

/-- `Prog(≺₁, λy. y ∈̇_μ z)`. -/
def progA (μ : Lv) (z : ℕ) : Proposition LRA :=
  progR (memAt μ (#0 : Semiterm LRA ℕ 1) (numAtR z))

/-- The body of `Acc_μ(v)`: `TI(≺₁, v, λx. x ∈̇_μ z)`, in the set variable. -/
def accBody (μ : Lv) (v : ℕ) : Semiformula LRA ℕ 1 :=
  (Rew.subst ![(numAtR v : Semiterm LRA ℕ 0)]).q ▹
    (Rew.bind ![(#1 : Semiterm LRA ℕ 2)] (fun _ => #0) ▹ xMem μ tiXF)

/-- `Acc_μ(v) :≡ ∀z TI(≺₁, v, λx. x ∈̇_μ z)`. -/
def accA (μ : Lv) (v : ℕ) : Proposition LRA := (tiMuR μ)/[(numAtR v : Semiterm LRA ℕ 0)]

theorem accA_eq (μ : Lv) (v : ℕ) : accA μ v = ∀¹ accBody μ v := by
  simp [accA, tiMuR, accBody]

theorem evR_accA (μ : Lv) (v : ℕ) : evR (accA μ v) = ∀¹ evR (accBody μ v) := by
  rw [accA_eq, evR_all]

/-- Truth in `ℕ`. -/
def TrueN (φ : Proposition LRA) : Prop := Semiformula.Eval (s := stdLRA) ![] (fun _ => 0) φ

theorem trueN_neg (φ : Proposition LRA) : TrueN (∼φ) ↔ ¬TrueN φ := by
  simp [TrueN]

/-! ### Meaning in an arbitrary structure -/

section Eval

variable {M : Type} [s : Structure LRA M]

theorem vec2_numAtR (x v : ℕ) :
    (![numAtR x, numAtR v] : Fin 2 → Semiterm LRA ℕ 0) = fun i => numAtR (![x, v] i) := by
  funext i; fin_cases i <;> rfl

theorem vec3_numAtR (x y z : ℕ) :
    (![numAtR x, numAtR y, numAtR z] : Fin 3 → Semiterm LRA ℕ 0) =
      fun i => numAtR (![x, y, z] i) := by
  funext i; fin_cases i <;> rfl

theorem eval_arAt_num {k : ℕ} (σ : ArithmeticSemisentence k) (w : Fin k → ℕ) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (arAt σ (fun i => numAtR (w i))) ↔
      arEval σ (fun i => numVal M (w i)) := by
  rw [eval_arAt]
  have h : (fun i => Semiterm.val (s := s) ![] f (numAtR (w i) : Semiterm LRA ℕ 0)) =
      fun i => numVal M (w i) := by
    funext i; exact val_numAtR_model _ _ _
  rw [h]

theorem eval_precA (x v : ℕ) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (precA x v) ↔ precM (numVal M x) (numVal M v) := by
  rw [precA, vec2_numAtR, eval_arAt_num]
  have h : (fun i => numVal M (![x, v] i)) = ![numVal M x, numVal M v] := by
    funext i; fin_cases i <;> rfl
  rw [h]
  rfl

theorem eval_vebA (u a g : ℕ) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (vebA u a g) ↔
      arEval vebDef₁.val ![numVal M u, numVal M a, numVal M g] := by
  rw [vebA, vec3_numAtR, eval_arAt_num]
  have h : (fun i => numVal M (![u, a, g] i)) = ![numVal M u, numVal M a, numVal M g] := by
    funext i; fin_cases i <;> rfl
  rw [h]

theorem eval_epsA (u g : ℕ) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (epsA u g) ↔ epsM (numVal M u) (numVal M g) := by
  rw [epsA, vec2_numAtR, eval_arAt_num]
  have h : (fun i => numVal M (![u, g] i)) = ![numVal M u, numVal M g] := by
    funext i; fin_cases i <;> rfl
  rw [h]
  rfl

theorem eval_memA (μ : Lv) (x z : ℕ) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (memA μ x z) ↔ memM μ (numVal M x) (numVal M z) := by
  rw [memA, eval_memAt, val_numAtR_model, val_numAtR_model]

theorem eval_memAt_bvar (μ : Lv) (z : ℕ) (y : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![y] f (memAt μ (#0 : Semiterm LRA ℕ 1) (numAtR z)) ↔
      memM μ y (numVal M z) := by
  rw [eval_memAt, val_numAtR_model]
  rfl

theorem eval_progA (μ : Lv) (z : ℕ) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (progA μ z) ↔ ProgM (fun y => memM μ y (numVal M z)) := by
  rw [progA, eval_progR]
  have h : (fun x => Semiformula.Eval (s := s) ![x] f
      (memAt μ (#0 : Semiterm LRA ℕ 1) (numAtR z))) = fun y => memM μ y (numVal M z) := by
    funext y; exact propext (eval_memAt_bvar μ z y f)
  rw [h]

theorem eval_accA (μ : Lv) (v : ℕ) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (accA μ v) ↔ TImu μ (numVal M v) := by
  rw [accA, eval_tiMuR_subst, val_numAtR_model]

theorem eval_accBody_inst (μ : Lv) (v z : ℕ) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f ((accBody μ v)/[(num z : SyntacticTerm LRA)]) ↔
      TIupM (fun x => memM μ x (numVal M z)) (numVal M v) := by
  simp only [accBody, Semiformula.eval_rew]
  have key : ∀ (e : Fin 1 → M) (g : ℕ → M), e = ![numVal M v] → g = (fun _ => numVal M z) →
      (Semiformula.Eval (s := s) e g (xMem μ tiXF) ↔
        TIupM (fun x => memM μ x (numVal M z)) (numVal M v)) := by
    rintro e g rfl rfl
    rw [eval_xMem, tiXF, eval_tiUptoAt_Xat_lxStr]
    rfl
  apply key
  · funext i
    fin_cases i
    simp only [Function.comp_apply, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      Rew.bind_bvar, Semiterm.val_bvar]
    rw [show (#1 : Semiterm LRA ℕ 2) = #(Fin.succ (0 : Fin 1)) from rfl, Rew.q_bvar_succ,
      Rew.subst_bvar, Matrix.cons_val_zero, rew_numAtR, val_numAtR_model]
  · funext x
    simp only [Function.comp_apply, Rew.bind_fvar, Semiterm.val_bvar, Rew.q_bvar_zero,
      Semiterm.val_bvar, Rew.subst_bvar, Matrix.cons_val_zero]
    exact val_numAtR_model _ _ z

end Eval

/-! ### Truth in `ℕ` -/

theorem eval_arAt_std {k : ℕ} (σ : ArithmeticSemisentence k) (w : Fin k → ℕ) :
    TrueN (arAt σ (fun i => numAtR (w i))) ↔ Semiformula.Evalb (M := ℕ) w σ := by
  rw [TrueN, arAt, Semiformula.eval_rew, arR, stdLRA_eq_raStd, eval_lMap_toLRA,
    Semiformula.eval_emb]
  have h : (Semiterm.val (s := raStd raStruc) ![] (fun _ => 0) ∘
      ⇑(Rew.subst fun i => (numAtR (w i) : Semiterm LRA ℕ 0)) ∘ Semiterm.bvar) = w := by
    funext i
    simp only [Function.comp_apply, Rew.subst_bvar]
    exact val_numAtR_stdLRA _ _ _
  rw [h]

theorem isNF₁_code (o : Gamma0Note) : isNF₁ (V := ℕ) (gamma0Code o) := by
  have h := Gentzen.VNoteBridge.isNF₁_gamma0ModelCode (V := ℕ) o
  rwa [Gentzen.VNoteBridge.gamma0ModelCode_nat] at h

theorem lt_iff_icmp_code (a b : Gamma0Note) :
    a < b ↔ Gentzen.InternalVNote.icmp₁ (V := ℕ) (gamma0Code a) (gamma0Code b) = 0 := by
  have h := Gentzen.VNoteBridge.gamma0_lt_iff_icmp₁_eq_zero (V := ℕ) a b
  rwa [Gentzen.VNoteBridge.gamma0ModelCode_nat, Gentzen.VNoteBridge.gamma0ModelCode_nat] at h

/-- **`x ≺₁ v` holds in `ℕ` exactly between codes of notations in order.** -/
theorem precA_true_iff (x v : ℕ) :
    TrueN (precA x v) ↔
      ∃ ξ η : Gamma0Note, gamma0Code ξ = x ∧ gamma0Code η = v ∧ ξ < η := by
  rw [precA, vec2_numAtR, eval_arAt_std]
  rw [eval_precDef₁]
  constructor
  · rintro ⟨hx, hv, hc⟩
    obtain ⟨ξ, rfl⟩ := Gentzen.VNoteBridge.isNF₁_surj x hx
    obtain ⟨η, rfl⟩ := Gentzen.VNoteBridge.isNF₁_surj v hv
    exact ⟨ξ, η, rfl, rfl, (lt_iff_icmp_code ξ η).mpr hc⟩
  · rintro ⟨ξ, η, rfl, rfl, hlt⟩
    exact ⟨isNF₁_code ξ, isNF₁_code η, (lt_iff_icmp_code ξ η).mp hlt⟩

theorem precA_true_code {ξ η : Gamma0Note} (h : ξ < η) :
    TrueN (precA (gamma0Code ξ) (gamma0Code η)) :=
  (precA_true_iff _ _).mpr ⟨ξ, η, rfl, rfl, h⟩

/-- **`u = φ_a(g)` holds in `ℕ` exactly at codes of notations.** -/
theorem vebA_true_iff (u a g : ℕ) :
    TrueN (vebA u a g) ↔
      ∃ α γ : Gamma0Note, gamma0Code α = a ∧ gamma0Code γ = g ∧
        u = gamma0Code (Gamma0Note.veblenNote α γ) := by
  rw [vebA, vec3_numAtR, eval_arAt_std]
  rw [eval_vebDef₁]
  constructor
  · rintro ⟨ha, hg, hu⟩
    obtain ⟨α, rfl⟩ := Gentzen.VNoteBridge.isNF₁_surj a ha
    obtain ⟨γ, rfl⟩ := Gentzen.VNoteBridge.isNF₁_surj g hg
    refine ⟨α, γ, rfl, rfl, ?_⟩
    rw [hu]
    have e := Gentzen.InternalVeblen.iveblen_gamma0ModelCode (V := ℕ) α γ
    simpa only [Gentzen.VNoteBridge.gamma0ModelCode_nat] using e
  · rintro ⟨α, γ, rfl, rfl, rfl⟩
    refine ⟨isNF₁_code α, isNF₁_code γ, ?_⟩
    have e := Gentzen.InternalVeblen.iveblen_gamma0ModelCode (V := ℕ) α γ
    simpa only [Gentzen.VNoteBridge.gamma0ModelCode_nat] using e.symm

/-- `ε_c = φ_1(c)` holds in `ℕ` at the codes. -/
theorem epsA_true_code (c : Gamma0Note) :
    TrueN (epsA (gamma0Code (Gamma0Note.epsilonNote c)) (gamma0Code c)) := by
  rw [epsA, vec2_numAtR, eval_arAt_std]
  rw [eval_epsDef₁]
  refine ⟨isNF₁_code c, ?_⟩
  have e := Gentzen.ProgStep.iepsilon_gamma0ModelCode (V := ℕ) c
  simpa only [Gentzen.VNoteBridge.gamma0ModelCode_nat] using e.symm

/-! ### Free variables -/

theorem freeVariables_arR {k : ℕ} (σ : ArithmeticSemisentence k) :
    (arR σ).freeVariables = ∅ := by
  simp [arR]

theorem freeVariables_arAt {k : ℕ} (σ : ArithmeticSemisentence k) (v : Fin k → Semiterm LRA ℕ 0)
    (hv : ∀ i, (v i).freeVariables = ∅) : (arAt σ v).freeVariables = ∅ :=
  freeVariables_rewR_eq_empty (Rew.subst v) (freeVariables_arR σ)
    (fun i => by rw [Rew.subst_bvar]; exact hv i)

theorem freeVariables_precA (x v : ℕ) : (precA x v).freeVariables = ∅ :=
  freeVariables_arAt _ _ (fun i => by fin_cases i <;> exact freeVariables_numAtR)

theorem freeVariables_vebA (u a g : ℕ) : (vebA u a g).freeVariables = ∅ :=
  freeVariables_arAt _ _ (fun i => by fin_cases i <;> exact freeVariables_numAtR)

theorem freeVariables_epsA (u g : ℕ) : (epsA u g).freeVariables = ∅ :=
  freeVariables_arAt _ _ (fun i => by fin_cases i <;> exact freeVariables_numAtR)

theorem freeVariables_memA (μ : Lv) (x z : ℕ) : (memA μ x z).freeVariables = ∅ := by
  rw [memA, freeVariables_memAt]
  simp

theorem freeVariables_tiMuR (μ : Lv) : (tiMuR μ).freeVariables = ∅ := by
  rw [tiMuR, Semiformula.freeVariables_all]
  exact freeVariables_rew_eq_empty_of _ _ (fun i => by rw [Subsingleton.elim i 0]; simp) (fun x => by simp)

theorem freeVariables_accA (μ : Lv) (v : ℕ) : (accA μ v).freeVariables = ∅ :=
  freeVariables_rewR_eq_empty _ (freeVariables_tiMuR μ)
    (fun i => by rw [Subsingleton.elim i 0, Rew.subst_bvar]; exact freeVariables_numAtR)

theorem freeVariables_progA (μ : Lv) (z : ℕ) : (progA μ z).freeVariables = ∅ := by
  have hm : (memAt μ (#0 : Semiterm LRA ℕ 1) (numAtR z)).freeVariables = ∅ := by
    rw [freeVariables_memAt]; simp
  have h1 : ((memAt μ (#0 : Semiterm LRA ℕ 1) (numAtR z))/[(#0 : Semiterm LRA ℕ 2)]).freeVariables
      = ∅ := freeVariables_rewR_eq_empty _ hm (fun i => by rw [Subsingleton.elim i 0]; simp)
  have h3 : (arAt precDef₁.val ![(#0 : Semiterm LRA ℕ 2), #1]).freeVariables = ∅ :=
    freeVariables_rewR_eq_empty _ (freeVariables_arR _) (fun i => by fin_cases i <;> rfl)
  simp [progA, progR, h1, hm, h3]

/-! ### `R`-freeness of the arithmetical formulas -/

theorem rFree_arAt {k : ℕ} (σ : ArithmeticSemisentence k) (v : Fin k → Semiterm LRA ℕ 0) :
    RFree (arAt σ v) :=
  rFree_rew _ (rFree_lMap_toLRA _)

/-! ### Levels and ranks -/

theorem lvlOf_precA (x v : ℕ) : lvlOf (precA x v) = 0 := lvlOf_arAt _ _

theorem lvlOf_vebA (u a g : ℕ) : lvlOf (vebA u a g) = 0 := lvlOf_arAt _ _

theorem lvlOf_epsA (u g : ℕ) : lvlOf (epsA u g) = 0 := lvlOf_arAt _ _

theorem lvlOf_memA (μ : Lv) (x z : ℕ) : lvlOf (memA μ x z) = μ := lvlOf_memAt _ _ _

theorem lvlOf_progA (μ : Lv) (z : ℕ) : lvlOf (progA μ z) = μ := by
  rw [progA, lvlOf_progR, lvlOf_memAt]

theorem lvlOf_accA_le (μ : Lv) (v : ℕ) : lvlOf (accA μ v) ≤ μ := by
  rw [accA, lvlOf_subst₁]
  exact lvlOf_tiMuR_le μ

/-- **Every formula of level at most `L` is a legitimate cut formula below
`blkTop (L ⊕ 1)`.** -/
theorem rank_lt_of_lvlOf_le {n : ℕ} {L : Lv} {φ : Semiformula LRA ℕ n} (h : lvlOf φ ≤ L) :
    rank φ < Gamma0Note.blkTop (Gamma0Note.nadd L 1) :=
  lt_of_lt_of_le (rank_lt_blkTop_succ φ)
    (Gamma0Note.blkTop_mono (Gamma0Note.nadd_le_nadd_left 1 h))

end Ramified

end OrdinalAnalysis
