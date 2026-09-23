/-
  **Congruence** — `ACA` proves
  `∀x∀y (x = y → ψ(x) → ψ(y))` for an arbitrary second-order formula `ψ`.

  This is the one axiom of `paLX` whose `toSOAt`-image is not already an axiom
  of `ACA` (`Lift.lean`, `CongruenceStatement`).  The proof is a strong
  induction on `complexity ψ`, generalised to arbitrary pairs of number
  substitutions:

      congrOf χ : ∀ ω₁ ω₂, (∀ x, ω₁ &x = ω₂ &x) →
        PSeq ACA (∼(ω₁ ▹ χ) :: (ω₂ ▹ χ) :: eqHyps ω₁ ω₂)

  with `eqHyps ω₁ ω₂` the list of negated equalities `∼(ω₁ #i = ω₂ #i)`.  The
  generalisation is forced by the quantifier cases: opening a `∀¹` with an
  eigenvariable replaces `ω_j` by `Rew.free.comp ω_j.q`, which is not a
  substitution and does not fix the free variables, and shifts the whole
  context — exactly what the list form absorbs.  The `∀²`/`∃²` cases replace the
  subformula by its `free₁`, whose *complexity* (not size) is smaller, which is
  why the recursion is on `complexity`.

  The atomic cases are the genuine content:
  * an `ℒₒᵣ`-atom needs `𝗘𝗤 ℒₒᵣ`'s `relExt`, lifted (`eqAxioms ⊆ ACA₀`), and
    term congruence, which needs `refl` and `funcExt`;
  * a set atom `t ∈& X` needs `setExt`, which `LK.lean` put into `ACA₀`
    precisely for this purpose.
-/
import OrdinalAnalysis.ACA.Combinators

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder

/-! ### The equality atom -/

/-- The equality atom of the second-order syntax, as the primitive
`Semiformula.rel` (the shape `LK.lean`'s `setExt` uses). -/
abbrev eqA {n : ℕ} (s t : FirstOrder.Semiterm ℒₒᵣ ℕ n) : Semiproposition ℒₒᵣ 0 n :=
  Semiformula.rel FirstOrder.Language.Eq.eq ![s, t]

/-! ### Sequent-level plumbing -/

variable {𝓢 : Set (Proposition ℒₒᵣ)}

/-- **Modus ponens inside a sequent.** -/
theorem cutImpSeq {Γ : SecondOrder.Sequent ℒₒᵣ} {φ χ : Proposition ℒₒᵣ}
    (himp : PSeq 𝓢 ((φ 🡒 χ) :: Γ)) (hφ : PSeq 𝓢 (φ :: Γ)) : PSeq 𝓢 (χ :: Γ) := by
  have h1 : PSeq 𝓢 ((∼φ) :: χ :: Γ) :=
    PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) (PSeq.orInv himp)
  have h2 : PSeq 𝓢 (φ :: χ :: Γ) :=
    PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hφ
  exact PSeq.cut φ h2 h1

/-- **A `⊥` in a sequent may be dropped.** -/
theorem dropFalsum {Γ : SecondOrder.Sequent ℒₒᵣ} (h : PSeq 𝓢 ((⊥ : Proposition ℒₒᵣ) :: Γ)) :
    PSeq 𝓢 Γ :=
  PSeq.cut ⊥ h (PSeq.verum (Γ := (∼(⊥ : Proposition ℒₒᵣ)) :: Γ) List.mem_cons_self)

/-- **Uncurrying Foundation's `Matrix.conj`-shaped binary hypothesis.**  The
antecedent of `Eq.funcExt`/`Eq.relExt` at arity 2 is `A ⋏ (B ⋏ ⊤)`. -/
theorem impOfConj2 {A B C : Proposition ℒₒᵣ} (h : Provable 𝓢 ((A ⋏ (B ⋏ ⊤)) 🡒 C)) :
    Provable 𝓢 (A 🡒 (B 🡒 C)) := by
  have hneg : (∼(A ⋏ (B ⋏ ⊤)) : Proposition ℒₒᵣ) = (∼A) ⋎ ((∼B) ⋎ ⊥) := rfl
  have h0 : PSeq 𝓢 (((A ⋏ (B ⋏ ⊤)) 🡒 C) :: [(∼A : Proposition ℒₒᵣ), ∼B, C]) :=
    PSeq.ofProvable h _
  have h1 : PSeq 𝓢 ((∼(A ⋏ (B ⋏ ⊤))) :: C :: [(∼A : Proposition ℒₒᵣ), ∼B, C]) :=
    PSeq.orInv h0
  rw [hneg] at h1
  have h2 : PSeq 𝓢 ((∼A) :: ((∼B) ⋎ ⊥) :: C :: [(∼A : Proposition ℒₒᵣ), ∼B, C]) :=
    PSeq.orInv h1
  have h3 : PSeq 𝓢 (((∼B) ⋎ ⊥) :: (∼A) :: C :: [(∼A : Proposition ℒₒᵣ), ∼B, C]) :=
    PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h2
  have h4 : PSeq 𝓢 ((∼B) :: (⊥ : Proposition ℒₒᵣ) :: (∼A) :: C ::
      [(∼A : Proposition ℒₒᵣ), ∼B, C]) := PSeq.orInv h3
  have h5 : PSeq 𝓢 ((⊥ : Proposition ℒₒᵣ) :: [(∼A : Proposition ℒₒᵣ), ∼B, C]) :=
    PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h4
  have h6 : PSeq 𝓢 [(∼A : Proposition ℒₒᵣ), ∼B, C] := dropFalsum h5
  have h7 : PSeq 𝓢 [(∼B : Proposition ℒₒᵣ), C, ∼A] :=
    PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h6
  have h8 : PSeq 𝓢 [((∼B) ⋎ C : Proposition ℒₒᵣ), ∼A] := PSeq.or h7
  have h9 : PSeq 𝓢 [(∼A : Proposition ℒₒᵣ), (∼B) ⋎ C] :=
    PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h8
  exact PSeq.to_provable (PSeq.or h9)

/-! ### The lifted equality axioms

`liftSentence '' (𝗘𝗤 ℒₒᵣ) = eqAxioms ⊆ ACA₀`, so every equality axiom is an
`ACA₀`-axiom once its lift is computed. -/

theorem lift_allNums : ∀ {n : ℕ} (φ : FirstOrder.Semiformula ℒₒᵣ ℕ n),
    (lift (∀¹* φ) : Proposition ℒₒᵣ) = allNums (lift φ)
  |       0, _ => rfl
  | (_ + 1), φ => lift_allNums (∀¹ φ)

private theorem eqAxiom_provable {σ : FirstOrder.Sentence ℒₒᵣ}
    (h : σ ∈ 𝗘𝗤 ℒₒᵣ) : Provable ACA₀ (liftSentence σ) :=
  ofAxiom (eqAxioms_subset_ACA₀ ⟨σ, h, rfl⟩)

private theorem vec4_cast {α : Type _} (w : Fin 4 → α) :
    (fun x : Fin 2 => w (Fin.addCast 2 x)) = ![w 0, w 1] := by
  funext x
  cases x using Fin.cases with
  | zero => rfl
  | succ j =>
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj; rfl

private theorem vec4_nat {α : Type _} (w : Fin 4 → α) :
    (fun x : Fin 2 => w (Fin.addNat x 2)) = ![w 2, w 3] := by
  funext x
  cases x using Fin.cases with
  | zero => rfl
  | succ j =>
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj; rfl

private theorem allNums_two {ρ : Semiproposition ℒₒᵣ 0 2} : allNums ρ = ∀¹ (∀¹ ρ) := rfl

private theorem addCast2_zero : Fin.addCast 2 (0 : Fin 2) = (0 : Fin 4) := rfl
private theorem addCast2_one : Fin.addCast 2 (1 : Fin 2) = (1 : Fin 4) := rfl

/-- **Reflexivity.** -/
theorem eqRefl (t : FirstOrder.Semiterm ℒₒᵣ ℕ 0) : Provable ACA₀ (eqA t t) := by
  have h := eqAxiom_provable (σ := FirstOrder.Theory.Eq.refl ℒₒᵣ) FirstOrder.Theory.eqAxiom.refl
  have e : liftSentence (FirstOrder.Theory.Eq.refl ℒₒᵣ) =
      ∀¹ (eqA (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) #0) := by
    simp [liftSentence, FirstOrder.Theory.Eq.refl, FirstOrder.Semiformula.Operator.eq_def,
      Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [e] at h
  have h2 := spec₁ h t
  simpa [Semiformula.rew_rel, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton] using h2

/-- **Symmetry.** -/
theorem eqSymm (s t : FirstOrder.Semiterm ℒₒᵣ ℕ 0) : Provable ACA₀ (eqA s t 🡒 eqA t s) := by
  have h := eqAxiom_provable (σ := FirstOrder.Theory.Eq.symm ℒₒᵣ) FirstOrder.Theory.eqAxiom.symm
  have e : liftSentence (FirstOrder.Theory.Eq.symm ℒₒᵣ) =
      allNums ((eqA (#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) #0) 🡒
        (eqA (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) #1)) := by
    simp [allNums_two, liftSentence, FirstOrder.Theory.Eq.symm,
      FirstOrder.Semiformula.Operator.eq_def,
      Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [e] at h
  have h2 := specNums _ ![t, s] h
  simpa [Semiformula.rew_rel, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton] using h2

/-- **Function extensionality**, at arity 2 (the only nonzero arity of `ℒₒᵣ`). -/
theorem funcExt2 (f : (ℒₒᵣ).Func 2) (a₀ a₁ b₀ b₁ : FirstOrder.Semiterm ℒₒᵣ ℕ 0) :
    Provable ACA₀ (eqA a₀ b₀ 🡒 (eqA a₁ b₁ 🡒
      eqA (FirstOrder.Semiterm.func f ![a₀, a₁]) (FirstOrder.Semiterm.func f ![b₀, b₁]))) := by
  have h := eqAxiom_provable (σ := FirstOrder.Theory.Eq.funcExt f)
    (FirstOrder.Theory.eqAxiom.funcExt f)
  have e : liftSentence (FirstOrder.Theory.Eq.funcExt f) =
      allNums
        ((((eqA (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 4) #2) ⋏
            ((eqA (#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 4) #3) ⋏ ⊤)) 🡒
          eqA (FirstOrder.Semiterm.func f ![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 4), #1])
            (FirstOrder.Semiterm.func f ![(#2 : FirstOrder.Semiterm ℒₒᵣ ℕ 4), #3]))) := by
    simp [addCast2_zero, addCast2_one, liftSentence, FirstOrder.Theory.Eq.funcExt,
      FirstOrder.Semiformula.Operator.eq_def, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton, Matrix.conj, Matrix.vecTail, lift_allNums,
      vec4_cast (fun i : Fin 4 => (#i : FirstOrder.Semiterm ℒₒᵣ ℕ 4)),
      vec4_nat (fun i : Fin 4 => (#i : FirstOrder.Semiterm ℒₒᵣ ℕ 4))]
  rw [e] at h
  have h2 := specNums _ ![a₀, a₁, b₀, b₁] h
  refine impOfConj2 ?_
  simpa [Semiformula.rew_rel, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton, FirstOrder.Rew.func] using h2

/-- **Relation extensionality**, at arity 2 (the only arity of `ℒₒᵣ`). -/
theorem relExt2 (r : (ℒₒᵣ).Rel 2) (a₀ a₁ b₀ b₁ : FirstOrder.Semiterm ℒₒᵣ ℕ 0) :
    Provable ACA₀ (eqA a₀ b₀ 🡒 (eqA a₁ b₁ 🡒
      ((Semiformula.rel r ![a₀, a₁] : Proposition ℒₒᵣ) 🡒 Semiformula.rel r ![b₀, b₁]))) := by
  have h := eqAxiom_provable (σ := FirstOrder.Theory.Eq.relExt r)
    (FirstOrder.Theory.eqAxiom.relExt r)
  have e : liftSentence (FirstOrder.Theory.Eq.relExt r) =
      allNums
        ((((eqA (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 4) #2) ⋏
            ((eqA (#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 4) #3) ⋏ ⊤)) 🡒
          ((Semiformula.rel r ![(#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 4), #1] :
              Semiproposition ℒₒᵣ 0 4) 🡒
            Semiformula.rel r ![(#2 : FirstOrder.Semiterm ℒₒᵣ ℕ 4), #3]))) := by
    simp [addCast2_zero, addCast2_one, liftSentence, FirstOrder.Theory.Eq.relExt,
      FirstOrder.Semiformula.Operator.eq_def, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton, Matrix.conj, Matrix.vecTail, lift_allNums,
      vec4_cast (fun i : Fin 4 => (#i : FirstOrder.Semiterm ℒₒᵣ ℕ 4)),
      vec4_nat (fun i : Fin 4 => (#i : FirstOrder.Semiterm ℒₒᵣ ℕ 4))]
  rw [e] at h
  have h2 := specNums _ ![a₀, a₁, b₀, b₁] h
  refine impOfConj2 ?_
  simpa [Semiformula.rew_rel, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton] using h2

/-- **Set extensionality at an arbitrary free set variable.** -/
theorem setExtAt (X : ℕ) (s t : FirstOrder.Semiterm ℒₒᵣ ℕ 0) :
    Provable ACA₀ (eqA s t 🡒 ((s ∈& X : Proposition ℒₒᵣ) 🡒 (t ∈& X))) := by
  have h := spec₂ (𝓢 := ACA₀) (ofAxiom setExt_mem_ACA₀)
    (ψ := ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& X)) trivial
  have e : Provable ACA₀
      (allNums ((eqA (#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) #1) 🡒
        (((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) ∈& X) 🡒
          ((#1 : FirstOrder.Semiterm ℒₒᵣ ℕ 2) ∈& X)))) := by
    simpa [allNums_two, setExt, Semiproposition.subst₁,
      FirstOrder.Rewriting.subst1_bvar0_eq] using h
  have h2 := specNums _ ![s, t] e
  simpa [Semiformula.rew_rel, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton] using h2

/-! ### Vector and rewriting normalisations

`ℒₒᵣ` has function symbols of arity `0` and `2` only, and relation symbols of
arity `2` only, so every atom is handled by one of the three lemmas below. -/

private theorem vec2_eq {α : Type _} (g : Fin 2 → α) : g = ![g 0, g 1] := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j =>
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj; rfl

private theorem rew_rel2 {n : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0) (r : (ℒₒᵣ).Rel 2)
    (v : Fin 2 → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    (ω ▹ (Semiformula.rel r v : Semiproposition ℒₒᵣ 0 n)) =
      Semiformula.rel r ![ω (v 0), ω (v 1)] := by
  rw [Semiformula.rew_rel]
  exact congrArg _ (vec2_eq (fun i => ω (v i)))

private theorem rew_nrel2 {n : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0) (r : (ℒₒᵣ).Rel 2)
    (v : Fin 2 → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    (ω ▹ (Semiformula.nrel r v : Semiproposition ℒₒᵣ 0 n)) =
      Semiformula.nrel r ![ω (v 0), ω (v 1)] := by
  rw [Semiformula.rew_nrel]
  exact congrArg _ (vec2_eq (fun i => ω (v i)))

private theorem rew_func2 {n : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0) (f : (ℒₒᵣ).Func 2)
    (v : Fin 2 → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ω (FirstOrder.Semiterm.func f v) = FirstOrder.Semiterm.func f ![ω (v 0), ω (v 1)] := by
  rw [FirstOrder.Rew.func]
  exact congrArg _ (vec2_eq (fun i => ω (v i)))

private theorem rew_func0 {n : ℕ} (ω₁ ω₂ : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0) (f : (ℒₒᵣ).Func 0)
    (v : Fin 0 → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    ω₁ (FirstOrder.Semiterm.func f v) = ω₂ (FirstOrder.Semiterm.func f v) := by
  rw [FirstOrder.Rew.func, FirstOrder.Rew.func]
  exact congrArg _ (funext (fun i => i.elim0))

/-! ### The equality hypotheses -/

/-- The list of *negated* equalities `∼(ω₁ #i = ω₂ #i)`: the hypotheses under
which `ω₁` and `ω₂` agree. -/
def eqHyps {n : ℕ} (ω₁ ω₂ : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0) : SecondOrder.Sequent ℒₒᵣ :=
  List.ofFn (fun i : Fin n => ∼(eqA (ω₁ #i) (ω₂ #i)))

theorem mem_eqHyps {n : ℕ} (ω₁ ω₂ : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0) (i : Fin n) :
    (∼(eqA (ω₁ #i) (ω₂ #i)) : Proposition ℒₒᵣ) ∈ eqHyps ω₁ ω₂ :=
  List.mem_ofFn.mpr ⟨i, rfl⟩

private theorem shift₀_negEq (s t : FirstOrder.Semiterm ℒₒᵣ ℕ 0) :
    Semiproposition.shift₀ (∼(eqA s t)) =
      ∼(eqA (FirstOrder.Rew.shift s) (FirstOrder.Rew.shift t)) := by
  show FirstOrder.Rew.shift ▹ (Semiformula.nrel FirstOrder.Language.Eq.eq ![s, t]) = _
  rw [Semiformula.rew_nrel]
  exact congrArg _ (by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj; rfl)

private theorem free_comp_bShift :
    (FirstOrder.Rew.free.comp (FirstOrder.Rew.bShift) : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) =
      FirstOrder.Rew.shift := by
  ext x
  · exact x.elim0
  · simp [FirstOrder.Rew.comp_app]

private theorem freeq_bvar_zero {n : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0) :
    (FirstOrder.Rew.free.comp ω.q) (#0) = (&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) := by
  simp [FirstOrder.Rew.comp_app]

private theorem freeq_bvar_succ {n : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0) (i : Fin n) :
    (FirstOrder.Rew.free.comp ω.q) (#(i.succ)) = FirstOrder.Rew.shift (ω (#i)) := by
  have e : (FirstOrder.Rew.free.comp ω.q) (#(i.succ)) =
      FirstOrder.Rew.free (FirstOrder.Rew.bShift (ω (#i))) := by
    simp [FirstOrder.Rew.comp_app]
  rw [e, ← FirstOrder.Rew.comp_app, free_comp_bShift]

private theorem freeq_fvar {n : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0) (x : ℕ) :
    (FirstOrder.Rew.free.comp ω.q) (&x) = FirstOrder.Rew.shift (ω (&x)) := by
  have e : (FirstOrder.Rew.free.comp ω.q) (&x) =
      FirstOrder.Rew.free (FirstOrder.Rew.bShift (ω (&x))) := by
    simp [FirstOrder.Rew.comp_app]
  rw [e, ← FirstOrder.Rew.comp_app, free_comp_bShift]

/-- **The eigenvariable step's bookkeeping.**  Opening a `∀¹` adds one trivial
equality `&0 = &0` and shifts all the others. -/
theorem eqHyps_free {n : ℕ} (ω₁ ω₂ : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0) :
    eqHyps (FirstOrder.Rew.free.comp ω₁.q) (FirstOrder.Rew.free.comp ω₂.q) =
      (∼(eqA (&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) &0)) ::
        SecondOrder.Sequent.shift₀ (eqHyps ω₁ ω₂) := by
  have key : ∀ i : Fin n,
      (∼(eqA ((FirstOrder.Rew.free.comp ω₁.q) (#(i.succ)))
        ((FirstOrder.Rew.free.comp ω₂.q) (#(i.succ)))) : Proposition ℒₒᵣ) =
      Semiproposition.shift₀ (∼(eqA (ω₁ (#i)) (ω₂ (#i)))) := by
    intro i
    rw [freeq_bvar_succ, freeq_bvar_succ, shift₀_negEq]
  show List.ofFn (fun i : Fin (n + 1) =>
      ∼(eqA ((FirstOrder.Rew.free.comp ω₁.q) (#i))
        ((FirstOrder.Rew.free.comp ω₂.q) (#i)))) = _
  rw [List.ofFn_succ, freeq_bvar_zero, freeq_bvar_zero]
  simp only [key, SecondOrder.Sequent.shift₀, eqHyps, List.map_ofFn, Function.comp_def]

theorem shift₁_eqHyps {n : ℕ} (ω₁ ω₂ : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0) :
    SecondOrder.Sequent.shift₁ (eqHyps ω₁ ω₂) = eqHyps ω₁ ω₂ := by
  show List.map Semiproposition.shift₁ (eqHyps ω₁ ω₂) = _
  rw [eqHyps, List.map_ofFn]
  rfl

/-! ### Term congruence -/

/-- **Terms are congruent.**  Under the hypotheses `ω₁ #i = ω₂ #i` (and given
that `ω₁`, `ω₂` agree on free variables), `ω₁ t = ω₂ t` for every term `t`. -/
theorem term_congr {n : ℕ} {ω₁ ω₂ : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0}
    (hf : ∀ x, ω₁ (&x) = ω₂ (&x)) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    PSeq ACA (eqA (ω₁ t) (ω₂ t) :: eqHyps ω₁ ω₂) := by
  induction t with
  | bvar i =>
      exact PSeq.id (φ := eqA (ω₁ (#i)) (ω₂ (#i))) List.mem_cons_self
        (List.mem_cons_of_mem _ (mem_eqHyps ω₁ ω₂ i))
  | fvar x =>
      rw [hf x]
      exact PSeq.ofProvable (aca_provable_mono (eqRefl _)) _
  | func f v ih =>
      cases f with
      | zero =>
          rw [rew_func0 ω₁ ω₂ _ v]
          exact PSeq.ofProvable (aca_provable_mono (eqRefl _)) _
      | one =>
          rw [rew_func0 ω₁ ω₂ _ v]
          exact PSeq.ofProvable (aca_provable_mono (eqRefl _)) _
      | add =>
          rw [rew_func2 ω₁ _ v, rew_func2 ω₂ _ v]
          exact cutImpSeq (cutImpSeq
            (PSeq.ofProvable (aca_provable_mono
              (funcExt2 _ (ω₁ (v 0)) (ω₁ (v 1)) (ω₂ (v 0)) (ω₂ (v 1)))) _) (ih 0)) (ih 1)
      | mul =>
          rw [rew_func2 ω₁ _ v, rew_func2 ω₂ _ v]
          exact cutImpSeq (cutImpSeq
            (PSeq.ofProvable (aca_provable_mono
              (funcExt2 _ (ω₁ (v 0)) (ω₁ (v 1)) (ω₂ (v 0)) (ω₂ (v 1)))) _) (ih 0)) (ih 1)

/-- Term congruence, read backwards. -/
theorem term_congr_symm {n : ℕ} {ω₁ ω₂ : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0}
    (hf : ∀ x, ω₁ (&x) = ω₂ (&x)) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    PSeq ACA (eqA (ω₂ t) (ω₁ t) :: eqHyps ω₁ ω₂) :=
  cutImpSeq (PSeq.ofProvable (aca_provable_mono (eqSymm (ω₁ t) (ω₂ t))) _) (term_congr hf t)

/-! ### Atomic set substitutions

`SecondOrder.Rew.free` — the eigenvariable substitution for `∀²` — replaces
every set slot by a bare membership *atom*.  Two facts about such substitutions
are needed: they do not change a formula's complexity (so the induction on
`complexity` goes through the `∀²` case), and they commute with first-order
rewriting (which `Rew.app_comm_subst` gives only for `Rew.subst`). -/

/-- A one-slot formula that is a bare membership atom. -/
def AtomicIm {M : ℕ} (χ : Semiproposition ℒₒᵣ M 1) : Prop :=
  (∃ Y : Fin M, χ = ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈# Y)) ∨
    (∃ Y : ℕ, χ = ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∈& Y))

/-- A set substitution all of whose images are membership atoms. -/
def AtomicSO {N M : ℕ} (Ω : SecondOrder.Rew ℒₒᵣ ℕ N ℕ M ℕ) : Prop :=
  (∀ X, AtomicIm (Ω.bv X)) ∧ (∀ X, AtomicIm (Ω.fv X))

theorem AtomicSO.q {N M : ℕ} {Ω : SecondOrder.Rew ℒₒᵣ ℕ N ℕ M ℕ} (h : AtomicSO Ω) :
    AtomicSO Ω.q := by
  constructor
  · intro X
    cases X using Fin.cases with
    | zero => exact Or.inl ⟨0, rfl⟩
    | succ Y =>
        rcases h.1 Y with ⟨Z, hZ⟩ | ⟨Z, hZ⟩
        · exact Or.inl ⟨Z.succ, by simp [SecondOrder.Rew.q, hZ]⟩
        · exact Or.inr ⟨Z, by simp [SecondOrder.Rew.q, hZ]⟩
  · intro X
    rcases h.2 X with ⟨Z, hZ⟩ | ⟨Z, hZ⟩
    · exact Or.inl ⟨Z.succ, by simp [SecondOrder.Rew.q, hZ]⟩
    · exact Or.inr ⟨Z, by simp [SecondOrder.Rew.q, hZ]⟩

theorem atomicSO_free {N : ℕ} :
    AtomicSO (SecondOrder.Rew.free : SecondOrder.Rew ℒₒᵣ ℕ (N + 1) ℕ N ℕ) := by
  constructor
  · intro X
    cases X using Fin.lastCases with
    | last => exact Or.inr ⟨0, by simp⟩
    | cast Y => exact Or.inl ⟨Y, by simp⟩
  · intro X
    exact Or.inr ⟨X + 1, rfl⟩

private theorem atomicIm_complexity {M n : ℕ} {χ : Semiproposition ℒₒᵣ M 1}
    (h : AtomicIm χ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    (χ/[t] : Semiproposition ℒₒᵣ M n).complexity = 0 := by
  rcases h with ⟨Y, rfl⟩ | ⟨Y, rfl⟩ <;> simp

private theorem atomicIm_comm {M n₁ n₂ : ℕ} {χ : Semiproposition ℒₒᵣ M 1}
    (h : AtomicIm χ) (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n₁) :
    (ω ▹ (χ/[t] : Semiproposition ℒₒᵣ M n₁)) = χ/[ω t] := by
  rcases h with ⟨Y, rfl⟩ | ⟨Y, rfl⟩ <;> simp

/-- **Negation does not change a formula's complexity.** -/
@[simp] theorem complexity_neg : ∀ {N n : ℕ} (φ : Semiproposition ℒₒᵣ N n),
    (∼φ).complexity = φ.complexity := by
  intro N n φ
  induction φ using Semiformula.rec' <;> simp [*]

/-- **A first-order rewriting does not change a formula's complexity.** -/
theorem complexity_rew : ∀ {N n₁ : ℕ} (φ : Semiproposition ℒₒᵣ N n₁) (n₂ : ℕ)
    (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂), (ω ▹ φ).complexity = φ.complexity := by
  intro N n₁ φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro n₂ ω; simp [Semiformula.rew_rel]
  | hNrel r v => intro n₂ ω; simp [Semiformula.rew_nrel]
  | hBvar X t => intro n₂ ω; simp
  | hNbvar X t => intro n₂ ω; simp
  | hFvar X t => intro n₂ ω; simp
  | hNfvar X t => intro n₂ ω; simp
  | hVerum => intro n₂ ω; simp
  | hFalsum => intro n₂ ω; simp
  | hAnd φ ψ ihφ ihψ => intro n₂ ω; simp [ihφ, ihψ]
  | hOr φ ψ ihφ ihψ => intro n₂ ω; simp [ihφ, ihψ]
  | hAll₁ φ ih => intro n₂ ω; simp [ih]
  | hExs₁ φ ih => intro n₂ ω; simp [ih]
  | hAll₂ φ ih => intro n₂ ω; simp [ih]
  | hExs₂ φ ih => intro n₂ ω; simp [ih]

/-- **An atomic set substitution does not change a formula's complexity.** -/
theorem complexity_app : ∀ {N n : ℕ} (φ : Semiproposition ℒₒᵣ N n) (M : ℕ)
    (Ω : SecondOrder.Rew ℒₒᵣ ℕ N ℕ M ℕ), AtomicSO Ω → (Ω.app φ).complexity = φ.complexity := by
  intro N n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro M Ω _; rfl
  | hNrel r v => intro M Ω _; rfl
  | hBvar X t => intro M Ω hΩ; exact atomicIm_complexity (hΩ.1 X) t
  | hNbvar X t =>
      intro M Ω hΩ
      show (∼((Ω.bv X)/[t])).complexity = 0
      rw [complexity_neg]
      exact atomicIm_complexity (hΩ.1 X) t
  | hFvar X t => intro M Ω hΩ; exact atomicIm_complexity (hΩ.2 X) t
  | hNfvar X t =>
      intro M Ω hΩ
      show (∼((Ω.fv X)/[t])).complexity = 0
      rw [complexity_neg]
      exact atomicIm_complexity (hΩ.2 X) t
  | hVerum => intro M Ω _; rfl
  | hFalsum => intro M Ω _; rfl
  | hAnd φ ψ ihφ ihψ => intro M Ω hΩ; simp [ihφ M Ω hΩ, ihψ M Ω hΩ]
  | hOr φ ψ ihφ ihψ => intro M Ω hΩ; simp [ihφ M Ω hΩ, ihψ M Ω hΩ]
  | hAll₁ φ ih => intro M Ω hΩ; simp [ih M Ω hΩ]
  | hExs₁ φ ih => intro M Ω hΩ; simp [ih M Ω hΩ]
  | hAll₂ φ ih => intro M Ω hΩ; simp [ih (M + 1) Ω.q hΩ.q]
  | hExs₂ φ ih => intro M Ω hΩ; simp [ih (M + 1) Ω.q hΩ.q]

/-- **An atomic set substitution commutes with first-order rewriting.** -/
theorem app_comm_rew : ∀ {N n₁ : ℕ} (φ : Semiproposition ℒₒᵣ N n₁) (M n₂ : ℕ)
    (Ω : SecondOrder.Rew ℒₒᵣ ℕ N ℕ M ℕ) (_ : AtomicSO Ω) (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂),
    Ω.app (ω ▹ φ) = ω ▹ Ω.app φ := by
  intro N n₁ φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro M n₂ Ω _ ω; simp [Semiformula.rew_rel]
  | hNrel r v => intro M n₂ Ω _ ω; simp [Semiformula.rew_nrel]
  | hBvar X t => intro M n₂ Ω hΩ ω; exact (atomicIm_comm (hΩ.1 X) ω t).symm
  | hNbvar X t =>
      intro M n₂ Ω hΩ ω
      show ∼((Ω.bv X)/[ω t]) = ω ▹ (∼((Ω.bv X)/[t]))
      rw [LogicalConnective.HomClass.map_neg, atomicIm_comm (hΩ.1 X) ω t]
  | hFvar X t => intro M n₂ Ω hΩ ω; exact (atomicIm_comm (hΩ.2 X) ω t).symm
  | hNfvar X t =>
      intro M n₂ Ω hΩ ω
      show ∼((Ω.fv X)/[ω t]) = ω ▹ (∼((Ω.fv X)/[t]))
      rw [LogicalConnective.HomClass.map_neg, atomicIm_comm (hΩ.2 X) ω t]
  | hVerum => intro M n₂ Ω _ ω; rfl
  | hFalsum => intro M n₂ Ω _ ω; rfl
  | hAnd φ ψ ihφ ihψ =>
      intro M n₂ Ω hΩ ω
      simp only [LogicalConnective.HomClass.map_and, ihφ M n₂ Ω hΩ ω, ihψ M n₂ Ω hΩ ω]
  | hOr φ ψ ihφ ihψ =>
      intro M n₂ Ω hΩ ω
      simp only [LogicalConnective.HomClass.map_or, ihφ M n₂ Ω hΩ ω, ihψ M n₂ Ω hΩ ω]
  | hAll₁ φ ih =>
      intro M n₂ Ω hΩ ω
      simp only [Semiformula.rew_all₀, SecondOrder.Rew.app_all₀, ih M (n₂ + 1) Ω hΩ ω.q]
  | hExs₁ φ ih =>
      intro M n₂ Ω hΩ ω
      simp only [Semiformula.rew_exs₀, SecondOrder.Rew.app_exs₀, ih M (n₂ + 1) Ω hΩ ω.q]
  | hAll₂ φ ih =>
      intro M n₂ Ω hΩ ω
      simp only [Semiformula.rew_all₁, SecondOrder.Rew.app_all₁,
        ih (M + 1) n₂ Ω.q hΩ.q ω]
  | hExs₂ φ ih =>
      intro M n₂ Ω hΩ ω
      simp only [Semiformula.rew_exs₁, SecondOrder.Rew.app_exs₁,
        ih (M + 1) n₂ Ω.q hΩ.q ω]

theorem complexity_free₁ {N n : ℕ} (φ : Semiproposition ℒₒᵣ (N + 1) n) :
    (Semiproposition.free₁ φ).complexity = φ.complexity :=
  complexity_app φ N SecondOrder.Rew.free atomicSO_free

theorem rew_free₁ {N n₁ n₂ : ℕ} (φ : Semiproposition ℒₒᵣ (N + 1) n₁)
    (ω : FirstOrder.Rew ℒₒᵣ ℕ n₁ ℕ n₂) :
    Semiproposition.free₁ (ω ▹ φ) = ω ▹ (Semiproposition.free₁ φ) :=
  app_comm_rew φ N n₂ SecondOrder.Rew.free atomicSO_free ω


/-! ### The atomic cases -/

private theorem closeAtom2 {Γ : SecondOrder.Sequent ℒₒᵣ} {A B C D : Proposition ℒₒᵣ}
    (h : Provable ACA (A 🡒 (B 🡒 (C 🡒 D))))
    (hA : PSeq ACA (A :: ((∼C) :: D :: Γ))) (hB : PSeq ACA (B :: ((∼C) :: D :: Γ))) :
    PSeq ACA ((∼C) :: D :: Γ) := by
  have s0 := PSeq.ofProvable h ((∼C) :: D :: Γ)
  have s2 := cutImpSeq (cutImpSeq s0 hA) hB
  exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) (PSeq.orInv s2)

private theorem closeAtom1 {Γ : SecondOrder.Sequent ℒₒᵣ} {A C D : Proposition ℒₒᵣ}
    (h : Provable ACA (A 🡒 (C 🡒 D))) (hA : PSeq ACA (A :: ((∼C) :: D :: Γ))) :
    PSeq ACA ((∼C) :: D :: Γ) := by
  have s0 := PSeq.ofProvable h ((∼C) :: D :: Γ)
  have s1 := cutImpSeq s0 hA
  exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) (PSeq.orInv s1)

private theorem congrRel {n : ℕ} {ω₁ ω₂ : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0}
    (hf : ∀ x, ω₁ (&x) = ω₂ (&x)) (r : (ℒₒᵣ).Rel 2)
    (v : Fin 2 → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    PSeq ACA ((∼(ω₁ ▹ (Semiformula.rel r v : Semiproposition ℒₒᵣ 0 n))) ::
      (ω₂ ▹ (Semiformula.rel r v : Semiproposition ℒₒᵣ 0 n)) :: eqHyps ω₁ ω₂) := by
  rw [rew_rel2, rew_rel2]
  refine closeAtom2 (aca_provable_mono (relExt2 r (ω₁ (v 0)) (ω₁ (v 1)) (ω₂ (v 0)) (ω₂ (v 1))))
    (PSeq.wk ?_ (term_congr hf (v 0))) (PSeq.wk ?_ (term_congr hf (v 1))) <;>
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))

private theorem congrNrel {n : ℕ} {ω₁ ω₂ : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0}
    (hf : ∀ x, ω₁ (&x) = ω₂ (&x)) (r : (ℒₒᵣ).Rel 2)
    (v : Fin 2 → FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    PSeq ACA ((∼(ω₁ ▹ (Semiformula.nrel r v : Semiproposition ℒₒᵣ 0 n))) ::
      (ω₂ ▹ (Semiformula.nrel r v : Semiproposition ℒₒᵣ 0 n)) :: eqHyps ω₁ ω₂) := by
  rw [rew_nrel2, rew_nrel2]
  have key : PSeq ACA
      ((∼(Semiformula.rel r ![ω₂ (v 0), ω₂ (v 1)] : Proposition ℒₒᵣ)) ::
        (Semiformula.rel r ![ω₁ (v 0), ω₁ (v 1)] : Proposition ℒₒᵣ) :: eqHyps ω₁ ω₂) := by
    refine closeAtom2 (aca_provable_mono (relExt2 r (ω₂ (v 0)) (ω₂ (v 1)) (ω₁ (v 0)) (ω₁ (v 1))))
      (PSeq.wk ?_ (term_congr_symm hf (v 0))) (PSeq.wk ?_ (term_congr_symm hf (v 1))) <;>
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) key

private theorem congrFvar {n : ℕ} {ω₁ ω₂ : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0}
    (hf : ∀ x, ω₁ (&x) = ω₂ (&x)) (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    PSeq ACA ((∼(ω₁ ▹ ((t ∈& X) : Semiproposition ℒₒᵣ 0 n))) ::
      (ω₂ ▹ ((t ∈& X) : Semiproposition ℒₒᵣ 0 n)) :: eqHyps ω₁ ω₂) := by
  show PSeq ACA ((∼(((ω₁ t) ∈& X) : Proposition ℒₒᵣ)) ::
    (((ω₂ t) ∈& X) : Proposition ℒₒᵣ) :: eqHyps ω₁ ω₂)
  refine closeAtom1 (aca_provable_mono (setExtAt X (ω₁ t) (ω₂ t))) (PSeq.wk ?_ (term_congr hf t))
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))

private theorem congrNfvar {n : ℕ} {ω₁ ω₂ : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0}
    (hf : ∀ x, ω₁ (&x) = ω₂ (&x)) (X : ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    PSeq ACA ((∼(ω₁ ▹ ((t ∉& X) : Semiproposition ℒₒᵣ 0 n))) ::
      (ω₂ ▹ ((t ∉& X) : Semiproposition ℒₒᵣ 0 n)) :: eqHyps ω₁ ω₂) := by
  have key : PSeq ACA ((∼(((ω₂ t) ∈& X) : Proposition ℒₒᵣ)) ::
      (((ω₁ t) ∈& X) : Proposition ℒₒᵣ) :: eqHyps ω₁ ω₂) := by
    refine closeAtom1 (aca_provable_mono (setExtAt X (ω₂ t) (ω₁ t)))
      (PSeq.wk ?_ (term_congr_symm hf t))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  show PSeq ACA ((((ω₁ t) ∈& X) : Proposition ℒₒᵣ) ::
    (∼(((ω₂ t) ∈& X) : Proposition ℒₒᵣ)) :: eqHyps ω₁ ω₂)
  exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) key

/-! ### The induction -/

/-- The statement proved by induction on `complexity`: **`ω₁` and `ω₂` agreeing
on every bound slot (as hypotheses of the sequent) and on the free variables
makes `χ` transfer from `ω₁` to `ω₂`.** -/
def CongP {n : ℕ} (χ : Semiproposition ℒₒᵣ 0 n) : Prop :=
  ∀ (ω₁ ω₂ : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0), (∀ x, ω₁ (&x) = ω₂ (&x)) →
    PSeq ACA ((∼(ω₁ ▹ χ)) :: (ω₂ ▹ χ) :: eqHyps ω₁ ω₂)

private theorem free_comp_q {n : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0)
    (φ : Semiproposition ℒₒᵣ 0 (n + 1)) :
    ((FirstOrder.Rew.free.comp ω.q) ▹ φ : Proposition ℒₒᵣ) =
      FirstOrder.Rewriting.free (ω.q ▹ φ) := by
  show FirstOrder.Rew.free.comp ω.q ▹ φ = FirstOrder.Rew.free ▹ (ω.q ▹ φ)
  rw [FirstOrder.TransitiveRewriting.comp_app]

/-- The eigenvariable premiss shared by the four quantifier cases. -/
private theorem quantPremiss {n : ℕ} {c : ℕ}
    (ih : ∀ {m : ℕ} (φ : Semiproposition ℒₒᵣ 0 m), φ.complexity < c → CongP φ)
    {ω₁ ω₂ : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0} (hf : ∀ x, ω₁ (&x) = ω₂ (&x))
    (φ : Semiproposition ℒₒᵣ 0 (n + 1)) (hlt : φ.complexity < c) :
    PSeq ACA ((∼(FirstOrder.Rewriting.free (ω₁.q ▹ φ))) ::
      (FirstOrder.Rewriting.free (ω₂.q ▹ φ)) ::
        SecondOrder.Sequent.shift₀ (eqHyps ω₁ ω₂)) := by
  have hf' : ∀ x, (FirstOrder.Rew.free.comp ω₁.q) (&x) =
      (FirstOrder.Rew.free.comp ω₂.q) (&x) := by
    intro x; rw [freeq_fvar, freeq_fvar, hf x]
  have hih := ih φ hlt (FirstOrder.Rew.free.comp ω₁.q) (FirstOrder.Rew.free.comp ω₂.q) hf'
  rw [eqHyps_free, free_comp_q, free_comp_q] at hih
  refine PSeq.cut (eqA (&0 : FirstOrder.Semiterm ℒₒᵣ ℕ 0) &0) ?_ ?_
  · exact PSeq.ofProvable (aca_provable_mono (eqRefl _)) _
  · exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hih

private theorem congrStep (c : ℕ)
    (ih : ∀ {m : ℕ} (φ : Semiproposition ℒₒᵣ 0 m), φ.complexity < c → CongP φ)
    {n : ℕ} (χ : Semiproposition ℒₒᵣ 0 n) (hc : χ.complexity ≤ c) : CongP χ := by
  intro ω₁ ω₂ hf
  cases χ with
  | rel r v => cases r with
      | eq => exact congrRel hf _ v
      | lt => exact congrRel hf _ v
  | nrel r v => cases r with
      | eq => exact congrNrel hf _ v
      | lt => exact congrNrel hf _ v
  | bvar X t => exact X.elim0
  | nbvar X t => exact X.elim0
  | fvar X t => exact congrFvar hf X t
  | nfvar X t => exact congrNfvar hf X t
  | verum =>
      show PSeq ACA ((⊥ : Proposition ℒₒᵣ) :: (⊤ : Proposition ℒₒᵣ) :: eqHyps ω₁ ω₂)
      exact PSeq.verum (List.mem_cons_of_mem _ List.mem_cons_self)
  | falsum =>
      show PSeq ACA ((⊤ : Proposition ℒₒᵣ) :: (⊥ : Proposition ℒₒᵣ) :: eqHyps ω₁ ω₂)
      exact PSeq.verum List.mem_cons_self
  | and φ ψ =>
      have hcφ : φ.complexity < c := Nat.lt_of_succ_le (le_trans (by simp) hc)
      have hcψ : ψ.complexity < c := Nat.lt_of_succ_le (le_trans (by simp) hc)
      have hp := ih φ hcφ ω₁ ω₂ hf
      have hq := ih ψ hcψ ω₁ ω₂ hf
      have hp' : PSeq ACA ((ω₂ ▹ φ) ::
          ((∼(ω₁ ▹ φ)) :: (∼(ω₁ ▹ ψ)) :: eqHyps ω₁ ω₂)) :=
        PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hp
      have hq' : PSeq ACA ((ω₂ ▹ ψ) ::
          ((∼(ω₁ ▹ φ)) :: (∼(ω₁ ▹ ψ)) :: eqHyps ω₁ ω₂)) :=
        PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hq
      have hand := PSeq.and hp' hq'
      have hand' : PSeq ACA ((∼(ω₁ ▹ φ)) :: (∼(ω₁ ▹ ψ)) ::
          ((ω₂ ▹ φ) ⋏ (ω₂ ▹ ψ)) :: eqHyps ω₁ ω₂) :=
        PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hand
      show PSeq ACA (((∼(ω₁ ▹ φ)) ⋎ (∼(ω₁ ▹ ψ))) ::
        ((ω₂ ▹ φ) ⋏ (ω₂ ▹ ψ)) :: eqHyps ω₁ ω₂)
      exact PSeq.or hand'
  | or φ ψ =>
      have hcφ : φ.complexity < c := Nat.lt_of_succ_le (le_trans (by simp) hc)
      have hcψ : ψ.complexity < c := Nat.lt_of_succ_le (le_trans (by simp) hc)
      have hp := ih φ hcφ ω₁ ω₂ hf
      have hq := ih ψ hcψ ω₁ ω₂ hf
      have hp' : PSeq ACA ((ω₂ ▹ φ) :: (ω₂ ▹ ψ) ::
          (∼(ω₁ ▹ φ)) :: eqHyps ω₁ ω₂) :=
        PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hp
      have hq' : PSeq ACA ((ω₂ ▹ φ) :: (ω₂ ▹ ψ) ::
          (∼(ω₁ ▹ ψ)) :: eqHyps ω₁ ω₂) :=
        PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hq
      have hp'' : PSeq ACA ((∼(ω₁ ▹ φ)) ::
          ((ω₂ ▹ φ) ⋎ (ω₂ ▹ ψ)) :: eqHyps ω₁ ω₂) :=
        PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) (PSeq.or hp')
      have hq'' : PSeq ACA ((∼(ω₁ ▹ ψ)) ::
          ((ω₂ ▹ φ) ⋎ (ω₂ ▹ ψ)) :: eqHyps ω₁ ω₂) :=
        PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) (PSeq.or hq')
      show PSeq ACA (((∼(ω₁ ▹ φ)) ⋏ (∼(ω₁ ▹ ψ))) ::
        ((ω₂ ▹ φ) ⋎ (ω₂ ▹ ψ)) :: eqHyps ω₁ ω₂)
      exact PSeq.and hp'' hq''
  | all₁ φ =>
      have hlt : φ.complexity < c := Nat.lt_of_succ_le hc
      have hP := quantPremiss ih hf φ hlt
      have hsubst : (Semiproposition.shift₀ (∼(ω₁.q ▹ φ)))/[(&0 :
          FirstOrder.Semiterm ℒₒᵣ ℕ 0)] = ∼(FirstOrder.Rewriting.free (ω₁.q ▹ φ)) := by
        rw [subst_bar_shift₀]
        exact LogicalConnective.HomClass.map_neg _ _
      have h2 : PSeq ACA ((∃¹ (Semiproposition.shift₀ (∼(ω₁.q ▹ φ)))) ::
          (FirstOrder.Rewriting.free (ω₂.q ▹ φ)) ::
            SecondOrder.Sequent.shift₀ (eqHyps ω₁ ω₂)) := by
        refine PSeq.exs₁ (&0) ?_
        rw [hsubst]
        exact hP
      have hsh : Semiproposition.shift₀ (∃¹ (∼(ω₁.q ▹ φ))) =
          ∃¹ (Semiproposition.shift₀ (∼(ω₁.q ▹ φ))) := by
        show FirstOrder.Rew.shift ▹ (∃¹ (∼(ω₁.q ▹ φ))) = _
        rw [Semiformula.rew_exs₀, FirstOrder.Rew.q_shift]
      have h3 : PSeq ACA ((FirstOrder.Rewriting.free (ω₂.q ▹ φ)) ::
          SecondOrder.Sequent.shift₀ ((∃¹ (∼(ω₁.q ▹ φ))) :: eqHyps ω₁ ω₂)) := by
        show PSeq ACA (_ :: (Semiproposition.shift₀ (∃¹ (∼(ω₁.q ▹ φ)))) ::
          SecondOrder.Sequent.shift₀ (eqHyps ω₁ ω₂))
        rw [hsh]
        exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h2
      have h4 : PSeq ACA ((∀¹ (ω₂.q ▹ φ)) :: (∃¹ (∼(ω₁.q ▹ φ))) :: eqHyps ω₁ ω₂) :=
        PSeq.all₁ ACA_shift₀_invariant h3
      show PSeq ACA ((∃¹ (∼(ω₁.q ▹ φ))) :: (∀¹ (ω₂.q ▹ φ)) :: eqHyps ω₁ ω₂)
      exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h4
  | exs₁ φ =>
      have hlt : φ.complexity < c := Nat.lt_of_succ_le hc
      have hP := quantPremiss ih hf φ hlt
      have hsubst : (Semiproposition.shift₀ (ω₂.q ▹ φ))/[(&0 :
          FirstOrder.Semiterm ℒₒᵣ ℕ 0)] = FirstOrder.Rewriting.free (ω₂.q ▹ φ) :=
        subst_bar_shift₀ _
      have h2 : PSeq ACA ((∃¹ (Semiproposition.shift₀ (ω₂.q ▹ φ))) ::
          (∼(FirstOrder.Rewriting.free (ω₁.q ▹ φ))) ::
            SecondOrder.Sequent.shift₀ (eqHyps ω₁ ω₂)) := by
        refine PSeq.exs₁ (&0) ?_
        rw [hsubst]
        exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hP
      have hsh : Semiproposition.shift₀ (∃¹ (ω₂.q ▹ φ)) =
          ∃¹ (Semiproposition.shift₀ (ω₂.q ▹ φ)) := by
        show FirstOrder.Rew.shift ▹ (∃¹ (ω₂.q ▹ φ)) = _
        rw [Semiformula.rew_exs₀, FirstOrder.Rew.q_shift]
      have h3 : PSeq ACA ((FirstOrder.Rewriting.free (∼(ω₁.q ▹ φ))) ::
          SecondOrder.Sequent.shift₀ ((∃¹ (ω₂.q ▹ φ)) :: eqHyps ω₁ ω₂)) := by
        show PSeq ACA (_ :: (Semiproposition.shift₀ (∃¹ (ω₂.q ▹ φ))) ::
          SecondOrder.Sequent.shift₀ (eqHyps ω₁ ω₂))
        rw [hsh, LogicalConnective.HomClass.map_neg]
        exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h2
      have h4 : PSeq ACA ((∀¹ (∼(ω₁.q ▹ φ))) :: (∃¹ (ω₂.q ▹ φ)) :: eqHyps ω₁ ω₂) :=
        PSeq.all₁ ACA_shift₀_invariant h3
      show PSeq ACA ((∀¹ (∼(ω₁.q ▹ φ))) :: (∃¹ (ω₂.q ▹ φ)) :: eqHyps ω₁ ω₂)
      exact h4
  | all₂ φ =>
      have hlt : (Semiproposition.free₁ φ).complexity < c := by
        rw [complexity_free₁]; exact Nat.lt_of_succ_le hc
      have hih := ih (Semiproposition.free₁ φ) hlt ω₁ ω₂ hf
      rw [← rew_free₁, ← rew_free₁] at hih
      have hsubst : (Semiproposition.shift₁ (∼(ω₁ ▹ φ)))/⟦freeWitness⟧ =
          ∼(Semiproposition.free₁ (ω₁ ▹ φ)) := by
        rw [subst₂_shift₁]
        exact LogicalConnective.HomClass.map_neg _ _
      have h2 : PSeq ACA ((∃² (Semiproposition.shift₁ (∼(ω₁ ▹ φ)))) ::
          (Semiproposition.free₁ (ω₂ ▹ φ)) :: eqHyps ω₁ ω₂) := by
        refine PSeq.exs₂ arith_freeWitness ?_
        rw [hsubst]
        exact hih
      have hsh : Semiproposition.shift₁ (∃² (∼(ω₁ ▹ φ))) =
          ∃² (Semiproposition.shift₁ (∼(ω₁ ▹ φ))) := by
        show SecondOrder.Rew.shift.app (∃² (∼(ω₁ ▹ φ))) = _
        rw [SecondOrder.Rew.app_exs₁, SecondOrder.Rew.q_shift]
      have h3 : PSeq ACA ((Semiproposition.free₁ (ω₂ ▹ φ)) ::
          SecondOrder.Sequent.shift₁ ((∃² (∼(ω₁ ▹ φ))) :: eqHyps ω₁ ω₂)) := by
        show PSeq ACA (_ :: (Semiproposition.shift₁ (∃² (∼(ω₁ ▹ φ)))) ::
          SecondOrder.Sequent.shift₁ (eqHyps ω₁ ω₂))
        rw [hsh, shift₁_eqHyps]
        exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h2
      have h4 : PSeq ACA ((∀² (ω₂ ▹ φ)) :: (∃² (∼(ω₁ ▹ φ))) :: eqHyps ω₁ ω₂) :=
        PSeq.all₂ ACA_shift₁_invariant h3
      show PSeq ACA ((∃² (∼(ω₁ ▹ φ))) :: (∀² (ω₂ ▹ φ)) :: eqHyps ω₁ ω₂)
      exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h4
  | exs₂ φ =>
      have hlt : (Semiproposition.free₁ φ).complexity < c := by
        rw [complexity_free₁]; exact Nat.lt_of_succ_le hc
      have hih := ih (Semiproposition.free₁ φ) hlt ω₁ ω₂ hf
      rw [← rew_free₁, ← rew_free₁] at hih
      have hsubst : (Semiproposition.shift₁ (ω₂ ▹ φ))/⟦freeWitness⟧ =
          Semiproposition.free₁ (ω₂ ▹ φ) := subst₂_shift₁ _
      have h2 : PSeq ACA ((∃² (Semiproposition.shift₁ (ω₂ ▹ φ))) ::
          (∼(Semiproposition.free₁ (ω₁ ▹ φ))) :: eqHyps ω₁ ω₂) := by
        refine PSeq.exs₂ arith_freeWitness ?_
        rw [hsubst]
        exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) hih
      have hsh : Semiproposition.shift₁ (∃² (ω₂ ▹ φ)) =
          ∃² (Semiproposition.shift₁ (ω₂ ▹ φ)) := by
        show SecondOrder.Rew.shift.app (∃² (ω₂ ▹ φ)) = _
        rw [SecondOrder.Rew.app_exs₁, SecondOrder.Rew.q_shift]
      have h3 : PSeq ACA ((Semiproposition.free₁ (∼(ω₁ ▹ φ))) ::
          SecondOrder.Sequent.shift₁ ((∃² (ω₂ ▹ φ)) :: eqHyps ω₁ ω₂)) := by
        show PSeq ACA (_ :: (Semiproposition.shift₁ (∃² (ω₂ ▹ φ))) ::
          SecondOrder.Sequent.shift₁ (eqHyps ω₁ ω₂))
        have hneg : Semiproposition.free₁ (∼(ω₁ ▹ φ)) =
            ∼(Semiproposition.free₁ (ω₁ ▹ φ)) := by
          show SecondOrder.Rew.free.app (∼(ω₁ ▹ φ)) = _
          exact LogicalConnective.HomClass.map_neg _ _
        rw [hsh, shift₁_eqHyps, hneg]
        exact PSeq.wk (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto) h2
      have h4 : PSeq ACA ((∀² (∼(ω₁ ▹ φ))) :: (∃² (ω₂ ▹ φ)) :: eqHyps ω₁ ω₂) :=
        PSeq.all₂ ACA_shift₁_invariant h3
      show PSeq ACA ((∀² (∼(ω₁ ▹ φ))) :: (∃² (ω₂ ▹ φ)) :: eqHyps ω₁ ω₂)
      exact h4

/-- **The congruence induction.** -/
theorem congrOf : ∀ (c : ℕ) {n : ℕ} (χ : Semiproposition ℒₒᵣ 0 n), χ.complexity ≤ c → CongP χ
  |       0 => congrStep 0 (fun _ h => absurd h (Nat.not_lt_zero _))
  | (c + 1) => congrStep (c + 1) (fun φ h => congrOf c φ (Nat.lt_succ_iff.mp h))


/-- **Congruence**, in the form the induction produces. -/
theorem congrPSeq {n : ℕ} (χ : Semiproposition ℒₒᵣ 0 n)
    (ω₁ ω₂ : FirstOrder.Rew ℒₒᵣ ℕ n ℕ 0) (hf : ∀ x, ω₁ (&x) = ω₂ (&x)) :
    PSeq ACA ((∼(ω₁ ▹ χ)) :: (ω₂ ▹ χ) :: eqHyps ω₁ ω₂) :=
  congrOf χ.complexity χ le_rfl ω₁ ω₂ hf

end OrdinalAnalysis.ACA
