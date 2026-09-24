/-
  The standard models of `ID₁`, and its consistency.

  `stdI P S` is the `LXI`-structure on `ℕ` with standard arithmetic, `X` read
  by `P` and `I` read by `S`.  For an operator form `A`, the operator

      opA P A S  :=  { x | A(S, x) holds in ℕ, with X read by P }

  is monotone in `S` as soon as `A` is positive (`positive_monotone`,
  `opA_mono`), so its least fixed point exists; it is taken as the
  intersection of all closed sets (`lfpA`), which is by definition mathlib's
  `OrderHom.lfp` of the operator (`lfpA_eq_lfp`).

  **Soundness** (`models_ID1`): for every positive `A` and every `P`, every
  axiom of `ID1 A` is true in `stdI P (lfpA P A)`.

    * Equality: `=` is read as equality.
    * `𝗣𝗔⁻`: the arithmetic reduct is Foundation's standard model of `ℕ`.
    * Induction for every `LXI`-formula: induction on `ℕ`.
    * Closure `∀x (A(I, x) → I x)`: the least fixed point is closed under the
      operator; this is where positivity is used.
    * The induction scheme at `F`: under an assignment `f` of the free
      variables, let `S_F := {x | F(x)}`.  By `eval_substI`, `A(F, x)` holds
      exactly when `x ∈ opA P A S_F`, so the premise says that `S_F` is closed
      under the operator, and the least fixed point is contained in every
      closed set.  No positivity is needed here, and none is used.

  With Foundation's soundness theorem this gives `ID1_consistent`.  The same
  holds for `ID1Acc prec`, for every arithmetic `prec`; in its standard model
  `I` is the accessible part of `prec` (`lfpA_accForm`).

  Contents.

    `ixStruc`, `stdI`                     the standard structures
    `eval_lMap_toLXI`                     arithmetic is read standardly
    `val_stdI_congr`                      term values see neither `P` nor `S`
    `eval_Iat`, `eval_Xat`                the two atoms
    `positive_monotone`                   positivity gives monotonicity in `S`
    `eval_substI`                         `A(F, ·)` reads `I` as the set defined by `F`
    `opA`, `opA_mono`, `lfpA`             the operator and its least fixed point
    `opA_lfpA_subset`, `lfpA_subset`, `opA_lfpA`, `lfpA_eq_lfp`
    `eval_closureAx`, `eval_indAx`        the axioms of the inductive definition
    `eval_of_eqAxiom`, `eval_of_paMinus`, `eval_of_succInd`, `models_paLXI`
    `models_ID1`                          **soundness**
    `ID1_consistent`                      **consistency**
    `lfpA_accForm`, `models_ID1Acc`, `ID1Acc_consistent`
-/
import OrdinalAnalysis.ID1.Theory
import Mathlib.Order.FixedPoints

set_option autoImplicit false
set_option warn.classDefReducibility false

namespace OrdinalAnalysis

namespace InductiveDef

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### The standard structures -/

/-- The fresh predicates read by `P` and `S`.  `IXLang` has no function
symbols. -/
def ixStruc (P : ℕ → Prop) (S : Set ℕ) : Structure IXLang ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ r v => match r with
    | IXRel.X => P (v 0)
    | IXRel.I => v 0 ∈ S

/-- **The standard structure of `LXI`**: arithmetic standard, `X` read by `P`,
`I` read by `S`. -/
def stdI (P : ℕ → Prop) (S : Set ℕ) : Structure LXI ℕ :=
  Structure.add ℒₒᵣ IXLang ℕ (str₂ := ixStruc P S)

section Std

variable (P : ℕ → Prop) (S : Set ℕ)

/-- The arithmetic reduct of `stdI P S` is Foundation's standard model. -/
theorem stdI_lMap_toLXI : (stdI P S).lMap toLXI = Arithmetic.standardModel ℕ := rfl

/-- An arithmetic formula says in `stdI P S` what it says in `ℕ`. -/
@[simp] theorem eval_lMap_toLXI {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) (e : Fin n → ℕ)
    (f : ξ → ℕ) :
    Semiformula.Eval (s := stdI P S) e f (Semiformula.lMap toLXI φ)
      ↔ Semiformula.Eval (M := ℕ) e f φ :=
  Structure.eval_lMap_add₁ (str₂ := ixStruc P S) φ e f

/-- Term values do not depend on the readings of `X` and `I`. -/
theorem val_stdI_congr (Q : ℕ → Prop) (T : Set ℕ) {ξ : Type*} {n : ℕ} (e : Fin n → ℕ)
    (f : ξ → ℕ) (t : Semiterm LXI ξ n) :
    Semiterm.val (s := stdI P S) e f t = Semiterm.val (s := stdI Q T) e f t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func fn v ih =>
      simp only [Semiterm.val_func, Function.comp_def, ih]
      rcases fn with fn | fn
      · rfl
      · exact PEmpty.elim fn

/-- `I(t)` holds when the value of `t` lies in `S`. -/
theorem eval_Iat {ξ : Type*} {n : ℕ} (t : Semiterm LXI ξ n) (e : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdI P S) e f (Iat t) ↔ Semiterm.val (s := stdI P S) e f t ∈ S := by
  have h : (Semiterm.val (s := stdI P S) e f ∘ ![t] : Fin 1 → ℕ)
      = ![Semiterm.val (s := stdI P S) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg ((stdI P S).rel (Sum.inr IXRel.I)) h)

/-- `X(t)` holds when `P` holds at the value of `t`. -/
theorem eval_Xat {ξ : Type*} {n : ℕ} (t : Semiterm LXI ξ n) (e : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdI P S) e f (Xat t) ↔ P (Semiterm.val (s := stdI P S) e f t) := by
  have h : (Semiterm.val (s := stdI P S) e f ∘ ![t] : Fin 1 → ℕ)
      = ![Semiterm.val (s := stdI P S) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg ((stdI P S).rel (Sum.inr IXRel.X)) h)

end Std

/-! ### Positivity gives monotonicity -/

/-- **Positive formulas are monotone in the reading of `I`.** -/
theorem positive_monotone {ξ : Type*} (P : ℕ → Prop) {S S' : Set ℕ} (hS : S ⊆ S') {n : ℕ}
    (φ : Semiformula LXI ξ n) (hφ : Positive φ) (e : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdI P S) e f φ → Semiformula.Eval (s := stdI P S') e f φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact id
  | hfalsum => exact id
  | hrel r v =>
    have hv : (fun i => Semiterm.val (s := stdI P S) e f (v i))
        = (fun i => Semiterm.val (s := stdI P S') e f (v i)) :=
      funext fun i => val_stdI_congr P S P S' e f (v i)
    rcases r with r | r
    · show Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdI P S) e f (v i)) →
        Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdI P S') e f (v i))
      rw [hv]
      exact id
    · cases r with
      | X =>
        show P (Semiterm.val (s := stdI P S) e f (v 0)) →
          P (Semiterm.val (s := stdI P S') e f (v 0))
        rw [val_stdI_congr P S P S']
        exact id
      | I =>
        show Semiterm.val (s := stdI P S) e f (v 0) ∈ S →
          Semiterm.val (s := stdI P S') e f (v 0) ∈ S'
        rw [val_stdI_congr P S P S']
        exact fun h => hS h
  | hnrel r v =>
    have hv : (fun i => Semiterm.val (s := stdI P S) e f (v i))
        = (fun i => Semiterm.val (s := stdI P S') e f (v i)) :=
      funext fun i => val_stdI_congr P S P S' e f (v i)
    rcases r with r | r
    · show ¬Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdI P S) e f (v i)) →
        ¬Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdI P S') e f (v i))
      rw [hv]
      exact id
    · cases r with
      | X =>
        show ¬P (Semiterm.val (s := stdI P S) e f (v 0)) →
          ¬P (Semiterm.val (s := stdI P S') e f (v 0))
        rw [val_stdI_congr P S P S']
        exact id
      | I => exact (hφ : False).elim
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact fun h => ⟨ihφ hφ.1 e h.1, ihψ hφ.2 e h.2⟩
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact fun h => h.imp (ihφ hφ.1 e) (ihψ hφ.2 e)
  | hall φ ih =>
    rw [Semiformula.eval_all, Semiformula.eval_all]
    exact fun h x => ih hφ (x :> e) (h x)
  | hexs φ ih =>
    rw [Semiformula.eval_ex, Semiformula.eval_ex]
    exact fun ⟨x, hx⟩ => ⟨x, ih hφ (x :> e) hx⟩

/-! ### Substitution of a formula for `I` -/

/-- **`substI F φ` reads `I` as the set defined by `F`**, under the same
assignment of the free variables. -/
theorem eval_substI {ξ : Type*} (P : ℕ → Prop) (S : Set ℕ) (F : Semiformula LXI ξ 1)
    (f : ξ → ℕ) {n : ℕ} (φ : Semiformula LXI ξ n) (e : Fin n → ℕ) :
    Semiformula.Eval (s := stdI P S) e f (substI F φ) ↔
      Semiformula.Eval (s := stdI P {x | Semiformula.Eval (s := stdI P S) ![x] f F}) e f φ := by
  set SF : Set ℕ := {x | Semiformula.Eval (s := stdI P S) ![x] f F} with hSF
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v =>
    have hv : (fun i => Semiterm.val (s := stdI P S) e f (v i))
        = (fun i => Semiterm.val (s := stdI P SF) e f (v i)) :=
      funext fun i => val_stdI_congr P S P SF e f (v i)
    rcases r with r | r
    · show Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdI P S) e f (v i)) ↔
        Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdI P SF) e f (v i))
      rw [hv]
    · cases r with
      | X =>
        show P (Semiterm.val (s := stdI P S) e f (v 0)) ↔
          P (Semiterm.val (s := stdI P SF) e f (v 0))
        rw [val_stdI_congr P S P SF]
      | I =>
        show Semiformula.Eval (s := stdI P S) e f (F/[v 0]) ↔
          Semiterm.val (s := stdI P SF) e f (v 0) ∈ SF
        rw [Semiformula.eval_substs, Matrix.comp₁, hSF, Set.mem_ofPred_eq,
          val_stdI_congr P S P SF]
  | hnrel r v =>
    have hv : (fun i => Semiterm.val (s := stdI P S) e f (v i))
        = (fun i => Semiterm.val (s := stdI P SF) e f (v i)) :=
      funext fun i => val_stdI_congr P S P SF e f (v i)
    rcases r with r | r
    · show ¬Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdI P S) e f (v i)) ↔
        ¬Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdI P SF) e f (v i))
      rw [hv]
    · cases r with
      | X =>
        show ¬P (Semiterm.val (s := stdI P S) e f (v 0)) ↔
          ¬P (Semiterm.val (s := stdI P SF) e f (v 0))
        rw [val_stdI_congr P S P SF]
      | I =>
        show Semiformula.Eval (s := stdI P S) e f (∼(F/[v 0])) ↔
          Semiterm.val (s := stdI P SF) e f (v 0) ∉ SF
        rw [LogicalConnective.HomClass.map_neg, Semiformula.eval_substs, Matrix.comp₁, hSF,
          Set.mem_ofPred_eq, val_stdI_congr P S P SF]
        rfl
  | hand φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := stdI P S) e f (substI F φ ⋏ substI F ψ) ↔ _
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact and_congr (ihφ e) (ihψ e)
  | hor φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := stdI P S) e f (substI F φ ⋎ substI F ψ) ↔ _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact or_congr (ihφ e) (ihψ e)
  | hall φ ih =>
    show Semiformula.Eval (s := stdI P S) e f (∀¹ substI F φ) ↔ _
    rw [Semiformula.eval_all, Semiformula.eval_all]
    exact forall_congr' fun x => ih (x :> e)
  | hexs φ ih =>
    show Semiformula.Eval (s := stdI P S) e f (∃¹ substI F φ) ↔ _
    rw [Semiformula.eval_ex, Semiformula.eval_ex]
    exact exists_congr fun x => ih (x :> e)

/-! ### The operator and its least fixed point -/

section Operator

variable (P : ℕ → Prop) (A : Semisentence LXI 1)

/-- **The operator of `A`**: `S ↦ {x | A(S, x)}`, with `X` read by `P`. -/
def opA (S : Set ℕ) : Set ℕ :=
  {x | Semiformula.Eval (s := stdI P S) ![x] Empty.elim A}

/-- A positive operator form defines a monotone operator. -/
theorem opA_mono (hA : Positive A) : Monotone (opA P A) :=
  fun _ _ hS x hx => positive_monotone P hS A hA ![x] Empty.elim hx

/-- **The least fixed point**: the intersection of all sets closed under the
operator. -/
def lfpA : Set ℕ :=
  sInf {S | opA P A S ⊆ S}

/-- The least fixed point is contained in every closed set. -/
theorem lfpA_subset {S : Set ℕ} (h : opA P A S ⊆ S) : lfpA P A ⊆ S :=
  sInf_le h

/-- The least fixed point is closed under the operator, when `A` is positive. -/
theorem opA_lfpA_subset (hA : Positive A) : opA P A (lfpA P A) ⊆ lfpA P A :=
  le_sInf fun _ hS => (opA_mono P A hA (lfpA_subset P A hS)).trans hS

/-- It is a fixed point. -/
theorem opA_lfpA (hA : Positive A) : opA P A (lfpA P A) = lfpA P A :=
  le_antisymm (opA_lfpA_subset P A hA)
    (lfpA_subset P A (opA_mono P A hA (opA_lfpA_subset P A hA)))

/-- `lfpA` is mathlib's least fixed point of the operator. -/
theorem lfpA_eq_lfp (hA : Positive A) : lfpA P A = OrderHom.lfp ⟨opA P A, opA_mono P A hA⟩ :=
  rfl

end Operator

/-! ### The axioms of the inductive definition -/

section Axioms

variable (P : ℕ → Prop) (A : Semisentence LXI 1)

/-- `A(F, x)` holds exactly when `x` is in the operator applied to the set
defined by `F`. -/
theorem eval_opAt (S : Set ℕ) (F : Semiformula LXI ℕ 1) (f : ℕ → ℕ) (x : ℕ) :
    Semiformula.Eval (s := stdI P S) ![x] f (opAt A F) ↔
      x ∈ opA P A {y | Semiformula.Eval (s := stdI P S) ![y] f F} := by
  rw [opAt, eval_substI, Semiformula.eval_emb]
  rfl

/-- **The closure axiom is true** in `stdI P (lfpA P A)`. -/
theorem eval_closureAx (hA : Positive A) :
    Semiformula.Eval (s := stdI P (lfpA P A)) ![] Empty.elim (closureAx A) := by
  rw [closureAx, Semiformula.eval_all]
  intro x
  rw [LogicalConnective.HomClass.map_imply, eval_Iat]
  intro hx
  exact opA_lfpA_subset P A hA hx

/-- **Every instance of the induction scheme for `I` is true** in
`stdI P (lfpA P A)`.  Positivity is not needed. -/
theorem eval_indAx (F : Semiformula LXI ℕ 1) :
    Semiformula.Eval (s := stdI P (lfpA P A)) ![] Empty.elim (indAx A F) := by
  rw [indAx]
  refine (Semiformula.eval_univCl (s := stdI P (lfpA P A)) _).mpr ?_
  intro f
  simp only [Semiformula.Evalf, LogicalConnective.HomClass.map_imply, Semiformula.eval_all]
  intro hcl x hx
  rw [eval_Iat] at hx
  have hsub := lfpA_subset P A (S := {y | Semiformula.Eval (s := stdI P (lfpA P A)) ![y] f F})
    (fun y hy => hcl y ((eval_opAt P A _ F f y).mpr hy))
  exact hsub hx

end Axioms

/-! ### The axioms of `paLXI` -/

section PA

variable (P : ℕ → Prop) (S : Set ℕ)

set_option linter.style.haveILetI false in
/-- Every equality axiom is true in `stdI P S`: `=` is read as equality. -/
theorem eval_of_eqAxiom {σ : Sentence LXI} (h : σ ∈ 𝗘𝗤 LXI) :
    Semiformula.Eval (s := stdI P S) ![] Empty.elim σ := by
  letI : Structure LXI ℕ := stdI P S
  haveI : Structure.Eq LXI ℕ := ⟨fun _ _ => iff_of_eq rfl⟩
  haveI : ℕ↓[LXI] ⊧* 𝗘𝗤 LXI := Structure.Eq.models_eq LXI ℕ
  exact Theory.models ℕ (𝗘𝗤 LXI) h

/-- Every transported axiom of `𝗣𝗔⁻` is true in `stdI P S`. -/
theorem eval_of_paMinus {σ : Sentence LXI} (h : σ ∈ Theory.lMap toLXI 𝗣𝗔⁻) :
    Semiformula.Eval (s := stdI P S) ![] Empty.elim σ := by
  obtain ⟨τ, hτ, rfl⟩ := h
  rw [eval_lMap_toLXI]
  exact Theory.models ℕ 𝗣𝗔⁻ hτ

/-- The two terms of `succInd` have their standard values. -/
theorem val_zero_stdI (f : ℕ → ℕ) :
    Semiterm.val (s := stdI P S) ![] f ((0 : ℕ) : Semiterm LXI ℕ 0) = 0 := rfl

theorem val_succ_stdI (f : ℕ → ℕ) (x : ℕ) :
    Semiterm.val (s := stdI P S) ![x] f (‘(#0 + 1)’ : Semiterm LXI ℕ 1) = x + 1 := rfl

/-- Every induction axiom is true in `stdI P S`: induction on `ℕ`. -/
theorem eval_of_succInd {σ : Sentence LXI} (h : σ ∈ InductionScheme LXI Set.univ) :
    Semiformula.Eval (s := stdI P S) ![] Empty.elim σ := by
  obtain ⟨φ, -, rfl⟩ := h
  refine (Semiformula.eval_univCl (s := stdI P S) _).mpr ?_
  intro f
  show Semiformula.Eval (s := stdI P S) ![] f ((φ/[((0 : ℕ) : Semiterm LXI ℕ 0)]) 🡒
      (∀¹ (φ/[(#0 : Semiterm LXI ℕ 1)] 🡒 φ/[(‘(#0 + 1)’ : Semiterm LXI ℕ 1)])) 🡒
      ∀¹ (φ/[(#0 : Semiterm LXI ℕ 1)]))
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_all,
    Semiformula.eval_substs, Matrix.comp₁]
  intro h0 hs x
  induction x with
  | zero => exact h0
  | succ k ih => exact hs k ih

/-- `stdI P S` is a model of `paLXI`, for every `P` and `S`. -/
theorem models_paLXI :
    letI := stdI P S; ℕ↓[LXI] ⊧* paLXI := by
  let _ : Structure LXI ℕ := stdI P S
  refine Semantics.modelsSet_iff.mpr fun σ hσ => models_iff.mpr ?_
  rcases hσ with h | h | h
  · exact eval_of_eqAxiom P S h
  · exact eval_of_paMinus P S h
  · exact eval_of_succInd P S h

end PA

/-! ### Soundness and consistency -/

section Soundness

variable (A : Semisentence LXI 1)

/-- Every axiom of `ID1 A` is true in `stdI P (lfpA P A)`. -/
theorem eval_of_mem_ID1 (hA : Positive A) (P : ℕ → Prop) {σ : Sentence LXI} (h : σ ∈ ID1 A) :
    Semiformula.Eval (s := stdI P (lfpA P A)) ![] Empty.elim σ := by
  rcases (mem_ID1 A).mp h with h | h | h | rfl | ⟨F, rfl⟩
  · exact eval_of_eqAxiom P _ h
  · exact eval_of_paMinus P _ h
  · exact eval_of_succInd P _ h
  · exact eval_closureAx P A hA
  · exact eval_indAx P A F

/-- **Soundness of `ID₁`**: for a positive operator form `A` and every reading
`P` of `X`, the standard structure with `I` read as the least fixed point of
the operator is a model of `ID1 A`. -/
theorem models_ID1 (hA : Positive A) (P : ℕ → Prop) :
    letI := stdI P (lfpA P A); ℕ↓[LXI] ⊧* ID1 A := by
  let _ : Structure LXI ℕ := stdI P (lfpA P A)
  exact Semantics.modelsSet_iff.mpr fun σ hσ => models_iff.mpr (eval_of_mem_ID1 A hA P hσ)

/-- **Every theorem of `ID1 A` is true in the standard model.** -/
theorem eval_of_provable_ID1 (hA : Positive A) (P : ℕ → Prop) {σ : Sentence LXI}
    (h : ID1 A ⊢ σ) :
    Semiformula.Eval (s := stdI P (lfpA P A)) ![] Empty.elim σ := by
  let _ : Structure LXI ℕ := stdI P (lfpA P A)
  exact models_iff.mp (models_of_provable (models_ID1 A hA P) h)

/-- **`ID₁` is consistent** for every positive operator form. -/
theorem ID1_consistent (hA : Positive A) : ID1 A ⊬ (⊥ : Sentence LXI) := by
  intro h
  have := eval_of_provable_ID1 A hA (fun _ => False) h
  simp at this

end Soundness

/-! ### The accessible part -/

section Acc

variable (prec : Semisentence ℒₒᵣ 2)

/-- The operator of the accessibility form: `x` enters once every `y ≺ x` is
in `S`. -/
theorem opA_accForm (P : ℕ → Prop) (S : Set ℕ) (x : ℕ) :
    x ∈ opA P (accForm prec) S ↔ ∀ y, Semiformula.Eval (M := ℕ) ![y, x] Empty.elim prec → y ∈ S := by
  show Semiformula.Eval (s := stdI P S) ![x] Empty.elim
      (∀¹ (Semiformula.lMap toLXI prec 🡒 Iat #0)) ↔ _
  rw [Semiformula.eval_all]
  refine forall_congr' fun y => ?_
  rw [LogicalConnective.HomClass.map_imply, eval_lMap_toLXI, eval_Iat]
  have e : (y :> ![x] : Fin 2 → ℕ) = ![y, x] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    rfl
  rw [e]
  rfl

/-- **In the standard model, `I` is the accessible part of `≺`**: the least
set `S` such that `x ∈ S` whenever every `y ≺ x` is in `S`. -/
theorem lfpA_accForm (P : ℕ → Prop) :
    lfpA P (accForm prec) =
      sInf {S : Set ℕ | ∀ x, (∀ y, Semiformula.Eval (M := ℕ) ![y, x] Empty.elim prec → y ∈ S) →
        x ∈ S} := by
  unfold lfpA
  congr 1
  ext S
  simp only [Set.mem_ofPred_eq, Set.subset_def, opA_accForm]

/-- Soundness of `ID1Acc prec`. -/
theorem models_ID1Acc (P : ℕ → Prop) :
    letI := stdI P (lfpA P (accForm prec)); ℕ↓[LXI] ⊧* ID1Acc prec :=
  models_ID1 (accForm prec) (ID1Acc_positive prec) P

/-- **`ID1Acc prec` is consistent**, for every arithmetic `prec`. -/
theorem ID1Acc_consistent : ID1Acc prec ⊬ (⊥ : Sentence LXI) :=
  ID1_consistent (accForm prec) (ID1Acc_positive prec)

end Acc

end InductiveDef

end OrdinalAnalysis
