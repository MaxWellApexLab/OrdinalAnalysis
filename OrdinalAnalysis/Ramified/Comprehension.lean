/-
  Comprehension with a same-level parameter, and the per-code naming facts, in
  the finitary theories.

  The naming schema of `Ramified/Theory.lean` is one pair of axioms per formula
  `A` of shape `μ`, guarded by the arithmetical condition "`c` is a code of `A`
  with parameter `p` at a stage `s` large enough".  This file draws the two
  consequences the upper bound consumes.

  * **Comprehension** (`exists_comprehension_code`): for every formula `A` of
    shape `μ`,

        RA Λ ⊢ ∀z ∃w ∀x (x ∈̇_μ w ↔ A(x, z)).

    The guard is total — every parameter `z` has a code at some stage, provably
    in `IΣ₁` (`Ramified/Guard.lean`'s `guardTotal_provable`) — and at such a
    code the two naming axioms give the biconditional.  The case the upper
    bound needs is the **jump** (`exists_jump_code`): `A` is Gentzen's jump
    formula of `Gentzen/Jump.lean` with the predicate `X` replaced by
    `λx. x ∈̇_μ z`, which has shape `μ` because every occurrence of `X` becomes
    an atom whose set argument is the parameter.

  * **Naming by a particular code** (`exists_naming`, `exists_naming_lt`): a
    closed formula of level `< μ` is named by its canonical parameter-free code
    `code μ A`.  The guard at that code is a true numeral instance, provable in
    `PA⁻` by `Σ₁`-completeness (`guardAt_provable`).

  Both are proved semantically, through Foundation's completeness theorem: in a
  model of the theory, the arithmetical reduct satisfies `PA` (or `PA⁻`), so
  the arithmetical facts about the guard hold there, and the naming axioms do
  the rest.  No equality axiom is used, so the argument applies verbatim to
  the level-guarded theories `RAlt ν`.
-/
import OrdinalAnalysis.Ramified.Theory
import OrdinalAnalysis.Gentzen.CodedVeblenJump

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### The arithmetical reduct of a model -/

section Reduct

variable {M : Type*} [s : Structure LRA M]

/-- The value of the numeral `k` in the arithmetical reduct of `M`. -/
def numVal (M : Type*) [s : Structure LRA M] (k : ℕ) : M :=
  (Semiterm.Operator.numeral ℒₒᵣ k).val (s := s.lMap toLRA) ![]

/-- An arithmetical numeral denotes `numVal`, whatever the environment. -/
theorem val_numeral_reduct {ξ : Type*} {n : ℕ} (b : Fin n → M) (f : ξ → M) (k : ℕ) :
    Semiterm.val (s := s.lMap toLRA) b f ((k : ℕ) : Semiterm ℒₒᵣ ξ n) = numVal M k := by
  simp [numVal, Semiterm.numeral, Semiterm.val_operator, Matrix.empty_eq]

/-- A numeral of `LRA` denotes `numVal`, whatever the environment. -/
theorem val_numAtR_model {n : ℕ} (b : Fin n → M) (f : ℕ → M) (k : ℕ) :
    Semiterm.val (s := s) b f (numAtR k : Semiterm LRA ℕ n) = numVal M k := by
  have h : (numAtR k : Semiterm LRA ℕ n) = Semiterm.lMap toLRA ((k : ℕ) : Semiterm ℒₒᵣ ℕ n) :=
    (lMap_toLRA_numeral k).symm
  rw [h, Semiterm.val_lMap]
  exact val_numeral_reduct b f k

/-- Membership at level `μ` in a model. -/
def memM (μ : Lv) (x c : M) : Prop := s.rel (Sum.inr (RARel.mem μ) : LRA.Rel 2) ![x, c]

theorem eval_memAt {n : ℕ} (b : Fin n → M) (f : ℕ → M) (μ : Lv) (t u : Semiterm LRA ℕ n) :
    Semiformula.Eval (s := s) b f (memAt μ t u) ↔
      memM μ (Semiterm.val (s := s) b f t) (Semiterm.val (s := s) b f u) := by
  have h : Semiformula.Eval (s := s) b f
        (Semiformula.rel (Sum.inr (RARel.mem μ) : LRA.Rel 2) ![t, u]) ↔
      s.rel (Sum.inr (RARel.mem μ) : LRA.Rel 2) (fun i => Semiterm.val (s := s) b f (![t, u] i)) :=
    Semiformula.eval_rel
  refine h.trans (iff_of_eq (congrArg _ (funext fun i => ?_)))
  fin_cases i <;> rfl

theorem eval_nmemAt {n : ℕ} (b : Fin n → M) (f : ℕ → M) (μ : Lv) (t u : Semiterm LRA ℕ n) :
    Semiformula.Eval (s := s) b f (nmemAt μ t u) ↔
      ¬memM μ (Semiterm.val (s := s) b f t) (Semiterm.val (s := s) b f u) := by
  rw [← neg_memAt, LogicalConnective.HomClass.map_neg, eval_memAt]
  rfl

/-- **The guard in a model** reads through the arithmetical reduct. -/
theorem eval_guardR_model (μ : Lv) (A : Semiformula LRA ℕ 1) (c p t : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![c, p, t] f (guardR μ A) ↔
      Semiformula.Evalb (s := s.lMap toLRA)
        ![c, p, t, numVal M μ, numVal M (Encodable.encode A), numVal M A.complexity]
        guardDef.val := by
  rw [guardR, Semiformula.eval_lMap, Semiformula.eval_emb, guardSS, Semiformula.eval_rew]
  have hb : (Semiterm.val (s := s.lMap toLRA) ![c, p, t] (Empty.elim : Empty → M) ∘
      ⇑(Rew.subst ![(#0 : Semiterm ℒₒᵣ Empty 3), #1, #2, (μ : Semiterm ℒₒᵣ Empty 3),
        ((Encodable.encode A : ℕ) : Semiterm ℒₒᵣ Empty 3), (A.complexity : Semiterm ℒₒᵣ Empty 3)])
      ∘ Semiterm.bvar)
      = ![c, p, t, numVal M μ, numVal M (Encodable.encode A), numVal M A.complexity] := by
    funext i
    fin_cases i <;> simp [Rew.subst_bvar, numVal]
  have hf : (Semiterm.val (s := s.lMap toLRA) ![c, p, t] (Empty.elim : Empty → M) ∘
      ⇑(Rew.subst ![(#0 : Semiterm ℒₒᵣ Empty 3), #1, #2, (μ : Semiterm ℒₒᵣ Empty 3),
        ((Encodable.encode A : ℕ) : Semiterm ℒₒᵣ Empty 3), (A.complexity : Semiterm ℒₒᵣ Empty 3)])
      ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := funext fun x => x.elim
  rw [hb, hf]

/-- `A(x, p)` in a model. -/
theorem eval_instA (A : Semiformula LRA ℕ 1) (e : Fin 4 → M) (f : ℕ → M) :
    Semiformula.Eval (s := s) e f (instA A) ↔ Semiformula.Eval (s := s) ![e 0] (fun _ => e 2) A := by
  rw [instA, Semiformula.eval_rew]
  have hb : (Semiterm.val (s := s) e f ∘ ⇑(Rew.bind (ξ₁ := ℕ) ![(#0 : Semiterm LRA ℕ 4)]
      (fun _ => (#2 : Semiterm LRA ℕ 4))) ∘ Semiterm.bvar) = ![e 0] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  have hf : (Semiterm.val (s := s) e f ∘ ⇑(Rew.bind (ξ₁ := ℕ) ![(#0 : Semiterm LRA ℕ 4)]
      (fun _ => (#2 : Semiterm LRA ℕ 4))) ∘ Semiterm.fvar) = fun _ => e 2 := rfl
  rw [hb, hf]

end Reduct

/-! ### The reduct of a model of the theory is a model of arithmetic -/

private lemma lMapR_zero {n : ℕ} :
    Semiterm.lMap toLRA ((0 : ℕ) : Semiterm ℒₒᵣ ℕ n) = ((0 : ℕ) : Semiterm LRA ℕ n) :=
  lMap_toLRA_numeral 0

private lemma lMapR_succ :
    Semiterm.lMap toLRA (‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1) = (‘(#0 + 1)’ : Semiterm LRA ℕ 1) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, Semiterm.Operator.Add.term_eq, toLRA]
  apply funext
  rw [Fin.forall_fin_two]
  constructor
  · simp [Function.comp_def]
  · simp [Function.comp_def]
    exact Matrix.empty_eq _

private lemma lMapR_succInd (φ : Semiformula ℒₒᵣ ℕ 1) :
    Semiformula.lMap toLRA (succInd φ) = succInd (Semiformula.lMap toLRA φ) := by
  simp [succInd, Semiformula.lMap_subst]
  exact ⟨by congr; exact lMapR_zero, by congr; exact lMapR_succ⟩

/-- The arithmetical part of a theory of `LRA`: `PA⁻` transported, and induction
for every transported arithmetical formula. -/
structure ArithPart (T : Theory LRA) : Prop where
  peanoMinus : Theory.lMap toLRA 𝗣𝗔⁻ ⊆ T
  induction : ∀ φ : Semiformula ℒₒᵣ ℕ 1,
    Semiformula.univCl (succInd (Semiformula.lMap toLRA φ)) ∈ T

theorem arithPart_RA (Λ : Set Lv) : ArithPart (RA Λ) :=
  ⟨fun _ h => mem_RA_of_mem_peanoMinus h, fun _ => induction_mem_RA _⟩

theorem arithPart_RAlt {ν : Lv} (hν : 1 ≤ ν) : ArithPart (RAlt ν) :=
  ⟨fun _ h => mem_RAlt_of_peanoMinus h,
    fun φ => induction_mem_RAlt _ (by rw [lvlOf_lMap_toLRA]; exact hν)⟩

/-- **The arithmetical reduct of a model of `T` satisfies `PA⁻`.** -/
theorem reduct_models_peanoMinus {T : Theory LRA} (hPA : Theory.lMap toLRA 𝗣𝗔⁻ ⊆ T)
    {M : Type*} [Nonempty M] [s : Structure LRA M] (hM : M↓[LRA] ⊧* T) :
    (s.lMap toLRA).toStruc ⊧* 𝗣𝗔⁻ := by
  refine ⟨fun σ hσ => ?_⟩
  exact Semiformula.models_lMap.mp (Semantics.modelsSet_iff.mp hM (hPA ⟨σ, hσ, rfl⟩))

set_option linter.style.haveILetI false in
/-- **The arithmetical reduct of a model of `T` satisfies `PA`.** -/
theorem reduct_models_peano {T : Theory LRA} (hT : ArithPart T)
    {M : Type*} [Nonempty M] [s : Structure LRA M] (hM : M↓[LRA] ⊧* T) :
    (s.lMap toLRA).toStruc ⊧* 𝗣𝗔 := by
  letI : Structure ℒₒᵣ M := s.lMap toLRA
  refine ⟨fun σ hσ => ?_⟩
  rcases hσ with hpa | hind
  · exact Semantics.modelsSet_iff.mp (reduct_models_peanoMinus hT.peanoMinus hM) hpa
  · rcases hind with ⟨φ, -, rfl⟩
    have hInd : M↓[LRA] ⊧ (succInd (Semiformula.lMap toLRA φ)).univCl :=
      Semantics.modelsSet_iff.mp hM (hT.induction φ)
    rw [models_iff, Semiformula.eval_univCl] at hInd ⊢
    intro f
    rw [← lMapR_succInd] at hInd
    exact Semiformula.eval_lMap.mp (hInd f)

/-! ### The guard in the reduct -/

section GuardReduct

variable {M : Type*} [s : Structure LRA M]

theorem reduct_guardTotal {T : Theory LRA} (hT : ArithPart T) [Nonempty M]
    (hM : M↓[LRA] ⊧* T) (m e k p : M) :
    ∃ c t : M, Semiformula.Evalb (s := s.lMap toLRA) ![c, p, t, m, e, k] guardDef.val := by
  have h : (s.lMap toLRA).toStruc ⊧ guardTotal :=
    Theory.Proof.sound (Entailment.WeakerThan.pbl guardTotal_provable) (reduct_models_peano hT hM)
  have h' := h
  simp only [Semantics.Models, guardTotal, Semiformula.eval_all, Semiformula.eval_ex,
    Semiformula.eval_substs] at h'
  obtain ⟨c, t, hct⟩ := h' m e k p
  refine ⟨c, t, ?_⟩
  have hv : (Semiterm.val (s := s.lMap toLRA) ![t, c, p, k, e, m] Empty.elim ∘
      ![(#1 : Semiterm ℒₒᵣ Empty 6), #2, #0, #5, #4, #3]) = ![c, p, t, m, e, k] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at hct
  exact hct

theorem reduct_guardAt {T : Theory LRA} (hPA : Theory.lMap toLRA 𝗣𝗔⁻ ⊆ T) [Nonempty M]
    (hM : M↓[LRA] ⊧* T) {c p t m e k : ℕ} (hc : c = mkCode m t e p) (hs : k + stage p < t) :
    Semiformula.Evalb (s := s.lMap toLRA)
      ![numVal M c, numVal M p, numVal M t, numVal M m, numVal M e, numVal M k] guardDef.val := by
  have h : (s.lMap toLRA).toStruc ⊧ guardAt c p t m e k :=
    Theory.Proof.sound (guardAt_provable hc hs) (reduct_models_peanoMinus hPA hM)
  have h' := h
  simp only [Semantics.Models, guardAt, Semiformula.eval_rew] at h'
  have hb : (Semiterm.val (s := s.lMap toLRA) ![] (Empty.elim : Empty → M) ∘
      ⇑(Rew.subst ![(c : Semiterm ℒₒᵣ Empty 0), (p : Semiterm ℒₒᵣ Empty 0),
        (t : Semiterm ℒₒᵣ Empty 0), (m : Semiterm ℒₒᵣ Empty 0), (e : Semiterm ℒₒᵣ Empty 0),
        (k : Semiterm ℒₒᵣ Empty 0)]) ∘ Semiterm.bvar)
      = ![numVal M c, numVal M p, numVal M t, numVal M m, numVal M e, numVal M k] := by
    funext i
    fin_cases i <;> simp [Rew.subst_bvar, numVal]
  have hf : (Semiterm.val (s := s.lMap toLRA) ![] (Empty.elim : Empty → M) ∘
      ⇑(Rew.subst ![(c : Semiterm ℒₒᵣ Empty 0), (p : Semiterm ℒₒᵣ Empty 0),
        (t : Semiterm ℒₒᵣ Empty 0), (m : Semiterm ℒₒᵣ Empty 0), (e : Semiterm ℒₒᵣ Empty 0),
        (k : Semiterm ℒₒᵣ Empty 0)]) ∘ Semiterm.fvar) = (Empty.elim : Empty → M) :=
    funext fun x => x.elim
  rw [hb, hf] at h'
  exact h'

end GuardReduct

/-! ### What the naming axioms say in a model -/

section NamingModel

variable {M : Type*} [Nonempty M] [s : Structure LRA M]

/-- **`nameOutP` in a model**: a code satisfying the guard names only elements
of `{x | A(x, p)}`. -/
theorem models_nameOutP {μ : Lv} {A : Semiformula LRA ℕ 1}
    (h : M↓[LRA] ⊧ Semiformula.univCl (nameOutP μ A)) (c p t : M)
    (hg : Semiformula.Evalb (s := s.lMap toLRA)
      ![c, p, t, numVal M μ, numVal M (Encodable.encode A), numVal M A.complexity] guardDef.val)
    (x : M) (hx : memM μ x c) : Semiformula.Eval (s := s) ![x] (fun _ => p) A := by
  have h1 := (Semiformula.eval_univCl (nameOutP μ A)).mp (models_iff.mp h) (fun _ => c)
  rw [nameOutP, Semiformula.eval_allClosure] at h1
  have h2 := h1 ![c, p, t]
  rw [nameOutMat, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    Semiformula.eval_all] at h2
  rcases h2 with hng | hall
  · exact absurd ((eval_guardR_model μ A c p t _).mpr hg) hng
  · have h3 := hall x
    rw [LogicalConnective.HomClass.map_or] at h3
    rcases h3 with hn | hA
    · rw [eval_nmemAt] at hn
      exact absurd hx hn
    · rw [eval_instA] at hA
      exact hA

/-- **`nameInP` in a model**: a code satisfying the guard names all of
`{x | A(x, p)}`. -/
theorem models_nameInP {μ : Lv} {A : Semiformula LRA ℕ 1}
    (h : M↓[LRA] ⊧ Semiformula.univCl (nameInP μ A)) (c p t : M)
    (hg : Semiformula.Evalb (s := s.lMap toLRA)
      ![c, p, t, numVal M μ, numVal M (Encodable.encode A), numVal M A.complexity] guardDef.val)
    (x : M) (hA : Semiformula.Eval (s := s) ![x] (fun _ => p) A) : memM μ x c := by
  have h1 := (Semiformula.eval_univCl (nameInP μ A)).mp (models_iff.mp h) (fun _ => c)
  rw [nameInP, Semiformula.eval_allClosure] at h1
  have h2 := h1 ![c, p, t]
  rw [nameInMat, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    Semiformula.eval_all] at h2
  rcases h2 with hng | hall
  · exact absurd ((eval_guardR_model μ A c p t _).mpr hg) hng
  · have h3 := hall x
    rw [LogicalConnective.HomClass.map_or] at h3
    rcases h3 with hn | hm
    · rw [LogicalConnective.HomClass.map_neg, eval_instA] at hn
      exact absurd hA hn
    · rw [eval_memAt] at hm
      exact hm

end NamingModel

/-! ### Comprehension with a same-level parameter -/

/-- `A(x, z)` under the three binders `z w x`: the subject is `#0` and every free
variable of `A` becomes the parameter `#2`. -/
def inst3 (A : Semiformula LRA ℕ 1) : Semiformula LRA ℕ 3 :=
  Rew.bind ![(#0 : Semiterm LRA ℕ 3)] (fun _ => #2) ▹ A

/-- **The comprehension statement** `∀z ∃w ∀x (x ∈̇_μ w ↔ A(x, z))`. -/
def compr (μ : Lv) (A : Semiformula LRA ℕ 1) : Proposition LRA :=
  ∀¹ ∃¹ ∀¹ (memAt μ (#0 : Semiterm LRA ℕ 3) #1 🡘 inst3 A)

theorem eval_inst3 {M : Type*} [s : Structure LRA M] (A : Semiformula LRA ℕ 1) (z w x : M)
    (f : ℕ → M) :
    Semiformula.Eval (s := s) (x :> w :> z :> ![]) f (inst3 A)
      ↔ Semiformula.Eval (s := s) ![x] (fun _ => z) A := by
  rw [inst3, Semiformula.eval_rew]
  have hb : (Semiterm.val (s := s) (x :> w :> z :> ![]) f ∘
      ⇑(Rew.bind (ξ₁ := ℕ) ![(#0 : Semiterm LRA ℕ 3)] (fun _ => (#2 : Semiterm LRA ℕ 3)))
      ∘ Semiterm.bvar) = ![x] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  have hf : (Semiterm.val (s := s) (x :> w :> z :> ![]) f ∘
      ⇑(Rew.bind (ξ₁ := ℕ) ![(#0 : Semiterm LRA ℕ 3)] (fun _ => (#2 : Semiterm LRA ℕ 3)))
      ∘ Semiterm.fvar) = fun _ => z := rfl
  rw [hb, hf]

theorem eval_compr {M : Type*} [s : Structure LRA M] (μ : Lv) (A : Semiformula LRA ℕ 1)
    (f : ℕ → M) :
    Semiformula.Eval (s := s) ![] f (compr μ A) ↔
      ∀ z : M, ∃ w : M, ∀ x : M, memM μ x w ↔ Semiformula.Eval (s := s) ![x] (fun _ => z) A := by
  simp only [compr, Semiformula.eval_all, Semiformula.eval_ex, LogicalConnective.HomClass.map_iff,
    LO.LogicalConnective.Prop.iff_eq, eval_memAt, eval_inst3]
  rfl

/-- **Comprehension, for any theory with the arithmetical part and the two naming
axioms of `A`.** -/
theorem comprehension_of {T : Theory LRA} (hT : ArithPart T) {μ : Lv} {A : Semiformula LRA ℕ 1}
    (hout : Semiformula.univCl (nameOutP μ A) ∈ T) (hin : Semiformula.univCl (nameInP μ A) ∈ T) :
    T ⊢ Semiformula.univCl (compr μ A) := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff]
  intro M _ s hM
  rw [models_iff, Semiformula.eval_univCl]
  intro f
  rw [eval_compr]
  intro z
  obtain ⟨c, t, hct⟩ := reduct_guardTotal hT hM (numVal M μ) (numVal M (Encodable.encode A))
    (numVal M A.complexity) z
  refine ⟨c, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · exact models_nameOutP (Semantics.modelsSet_iff.mp hM hout) c z t hct x hx
  · exact models_nameInP (Semantics.modelsSet_iff.mp hM hin) c z t hct x hx

/-- **Comprehension with a same-level parameter in `RA Λ`**:
`RA Λ ⊢ ∀z ∃w ∀x (x ∈̇_μ w ↔ A(x, z))` for every `A` of shape `μ`. -/
theorem exists_comprehension_code {Λ : Set Lv} {μ : Lv} (h0 : 0 < μ) (hμ : μ ∈ Λ)
    {A : Semiformula LRA ℕ 1} (hA : Shape μ A) :
    RA Λ ⊢ Semiformula.univCl (compr μ A) :=
  comprehension_of (arithPart_RA Λ) (nameOutP_mem_RA hμ h0 hA) (nameInP_mem_RA hμ h0 hA)

/-- The same in `RA_{<ν}`, for `μ < ν`. -/
theorem exists_comprehension_code_lt {ν μ : Lv} (h0 : 0 < μ) (hμ : μ < ν)
    {A : Semiformula LRA ℕ 1} (hA : Shape μ A) :
    RAlt ν ⊢ Semiformula.univCl (compr μ A) :=
  comprehension_of (arithPart_RAlt (Nat.succ_le_of_lt (lt_trans h0 hμ)))
    (naming_mem_RAlt (mem_NamingAxioms_out (Λ := {x | x < ν}) hμ h0 hA))
    (naming_mem_RAlt (mem_NamingAxioms_in (Λ := {x | x < ν}) hμ h0 hA))

/-! ### The jump -/

/-- The terms of `LX` read in `LRA`: both languages extend arithmetic by
function-free symbols. -/
def lxToLRA : Gentzen.LX →ᵥ LRA where
  func := fun {k} f => match k, f with
    | _, Sum.inl f => Sum.inl f
    | _, Sum.inr f => PEmpty.elim f
  rel := fun {k} r => match k, r with
    | _, Sum.inl r => Sum.inl r
    | _, Sum.inr Gentzen.XRel.X => Sum.inr RARel.X

/-- **`X ↦ λx. x ∈̇_μ &0`**: an `LX`-formula read in `LRA`, with the free
predicate `X` replaced by membership in the level-`μ` set named by the
parameter. -/
def xMem (μ : Lv) : {n : ℕ} → Semiformula Gentzen.LX ℕ n → Semiformula LRA ℕ n
  | _, .verum => ⊤
  | _, .falsum => ⊥
  | _, .rel (Sum.inl r) v => .rel (Sum.inl r) fun i => Semiterm.lMap lxToLRA (v i)
  | _, .rel (Sum.inr Gentzen.XRel.X) v => memAt μ (Semiterm.lMap lxToLRA (v 0)) &0
  | _, .nrel (Sum.inl r) v => .nrel (Sum.inl r) fun i => Semiterm.lMap lxToLRA (v i)
  | _, .nrel (Sum.inr Gentzen.XRel.X) v => nmemAt μ (Semiterm.lMap lxToLRA (v 0)) &0
  | _, .and φ ψ => xMem μ φ ⋏ xMem μ ψ
  | _, .or φ ψ => xMem μ φ ⋎ xMem μ ψ
  | _, .all φ => ∀¹ xMem μ φ
  | _, .exs φ => ∃¹ xMem μ φ

/-- **Every `xMem μ`-image has shape `μ`**: its only level-`μ` atoms are the
images of `X`, whose set argument is the parameter. -/
theorem shape_xMem (μ : Lv) : {n : ℕ} → (φ : Semiformula Gentzen.LX ℕ n) → Shape μ (xMem μ φ)
  | _, .verum => trivial
  | _, .falsum => trivial
  | _, .rel (Sum.inl _) _ => trivial
  | _, .rel (Sum.inr Gentzen.XRel.X) _ => Or.inr ⟨rfl, rfl⟩
  | _, .nrel (Sum.inl _) _ => trivial
  | _, .nrel (Sum.inr Gentzen.XRel.X) _ => Or.inr ⟨rfl, rfl⟩
  | _, .and φ ψ => ⟨shape_xMem μ φ, shape_xMem μ ψ⟩
  | _, .or φ ψ => ⟨shape_xMem μ φ, shape_xMem μ ψ⟩
  | _, .all φ => shape_xMem μ φ
  | _, .exs φ => shape_xMem μ φ

/-- **The level-`μ` jump formula** `J_μ(x, z)`: Gentzen's jump of `X` over the
Veblen coding (`Gentzen/Jump.lean`, `Gentzen/CodedVeblenJump.lean`), with `X`
read as membership in the level-`μ` set `z`. -/
def jumpR (μ : Lv) : Semiformula LRA ℕ 1 :=
  xMem μ (Gentzen.jump Gentzen.CodedVeblen.precCode₁ Gentzen.CodedVeblenJump.addCode₁
    Gentzen.CodedVeblenJump.omegaPowCode₁ (Gentzen.Xat #0))

theorem shape_jumpR (μ : Lv) : Shape μ (jumpR μ) := shape_xMem μ _

/-- **Level `μ` is closed under the jump, uniformly in a level-`μ` set**:

    RA Λ ⊢ ∀z ∃w ∀x (x ∈̇_μ w ↔ J_μ(x, z)).

This is the principle the same-level parameter was introduced for. -/
theorem exists_jump_code {Λ : Set Lv} {μ : Lv} (h0 : 0 < μ) (hμ : μ ∈ Λ) :
    RA Λ ⊢ Semiformula.univCl (compr μ (jumpR μ)) :=
  exists_comprehension_code h0 hμ (shape_jumpR μ)

/-- The same in `RA_{<ν}`, for `μ < ν`. -/
theorem exists_jump_code_lt {ν μ : Lv} (h0 : 0 < μ) (hμ : μ < ν) :
    RAlt ν ⊢ Semiformula.univCl (compr μ (jumpR μ)) :=
  exists_comprehension_code_lt h0 hμ (shape_jumpR μ)

/-! ### Naming by the canonical parameter-free code -/

/-- The body of the canonical code in a model: the formula at the parameter `0`. -/
theorem eval_body_code {M : Type*} [s : Structure LRA M] (μ : Lv) (A : Semiformula LRA ℕ 1)
    (x : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![x] f (body (code μ A))
      ↔ Semiformula.Eval (s := s) ![x] (fun _ => numVal M 0) A := by
  rw [code, body_mkCode, instParam, Semiformula.eval_rewrite]
  have h : (fun _ : ℕ => Semiterm.val (s := s) ![x] f (numAtR 0 : Semiterm LRA ℕ 1))
      = fun _ => numVal M 0 := funext fun _ => val_numAtR_model _ _ 0
  rw [h]

/-- **The canonical code names its formula**, in any theory with `PA⁻` and the
two naming axioms of the formula. -/
theorem naming_of {T : Theory LRA} (hPA : Theory.lMap toLRA 𝗣𝗔⁻ ⊆ T) {μ : Lv}
    {A : Semiformula LRA ℕ 1}
    (hout : Semiformula.univCl (nameOutP μ A) ∈ T) (hin : Semiformula.univCl (nameInP μ A) ∈ T) :
    T ⊢ Semiformula.univCl (nameOut (code μ A)) ∧ T ⊢ Semiformula.univCl (nameIn (code μ A)) := by
  have hst : A.complexity + stage 0 < A.complexity + 1 := by
    rw [stage_zero]; exact Nat.lt_succ_self _
  constructor
  · apply Theory.Proof.complete.{0, 0}
    rw [consequence_iff]
    intro M _ s hM
    rw [models_iff, Semiformula.eval_univCl]
    intro f
    rw [nameOut, Semiformula.eval_all]
    intro x
    rw [LogicalConnective.HomClass.map_or, eval_nmemAt, lvl_code, eval_body_code]
    have hv : Semiterm.val (s := s) ![x] f (nameTerm (code μ A)) = numVal M (code μ A) :=
      val_numAtR_model _ _ _
    rw [hv]
    by_cases hx : memM μ (Semiterm.val (s := s) ![x] f (#0 : Semiterm LRA ℕ 1)) (numVal M (code μ A))
    · exact Or.inr (models_nameOutP (Semantics.modelsSet_iff.mp hM hout) _ _ _
        (reduct_guardAt hPA hM rfl hst) _ hx)
    · exact Or.inl hx
  · apply Theory.Proof.complete.{0, 0}
    rw [consequence_iff]
    intro M _ s hM
    rw [models_iff, Semiformula.eval_univCl]
    intro f
    rw [nameIn, Semiformula.eval_all]
    intro x
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, eval_memAt,
      lvl_code, eval_body_code]
    have hv : Semiterm.val (s := s) ![x] f (nameTerm (code μ A)) = numVal M (code μ A) :=
      val_numAtR_model _ _ _
    rw [hv]
    by_cases hx : Semiformula.Eval (s := s) ![x] (fun _ => numVal M 0) A
    · exact Or.inr (models_nameInP (Semantics.modelsSet_iff.mp hM hin) _ _ _
        (reduct_guardAt hPA hM rfl hst) _ hx)
    · exact Or.inl hx

/-- **Naming.**  For every closed `A` all of whose set atoms sit below `ν`, and
every `ν ∈ Λ`, the canonical parameter-free code of `A` at level `ν` names `A`
in `RA Λ`. -/
theorem exists_naming {Λ : Set Lv} {ν : Lv} (hν : ν ∈ Λ) {A : Semiformula LRA ℕ 1}
    (hlvl : lvlOf A < ν) (hcl : A.freeVariables = ∅) :
    ∃ a : ℕ, Good a ∧ lvl a = ν ∧ body a = A ∧
      RA Λ ⊢ Semiformula.univCl (nameOut a) ∧ RA Λ ⊢ Semiformula.univCl (nameIn a) := by
  have h0 : 0 < ν := lt_of_le_of_lt (Nat.zero_le _) hlvl
  have hA : Shape ν A := shape_of_lvlOf_lt hlvl
  exact ⟨code ν A, good_code hlvl, lvl_code ν A, body_code hcl,
    naming_of (arithPart_RA Λ).peanoMinus (nameOutP_mem_RA hν h0 hA) (nameInP_mem_RA hν h0 hA)⟩

/-- The `RA_{<ν}` form: names for every level-correct closed `A` at every level
`μ < ν` above `lvlOf A`. -/
theorem exists_naming_lt {ν μ : Lv} (hμ : μ < ν) {A : Semiformula LRA ℕ 1}
    (hlvl : lvlOf A < μ) (hcl : A.freeVariables = ∅) :
    ∃ a : ℕ, Good a ∧ lvl a = μ ∧ body a = A ∧
      RAlt ν ⊢ Semiformula.univCl (nameOut a) ∧ RAlt ν ⊢ Semiformula.univCl (nameIn a) := by
  have h0 : 0 < μ := lt_of_le_of_lt (Nat.zero_le _) hlvl
  have hA : Shape μ A := shape_of_lvlOf_lt hlvl
  exact ⟨code μ A, good_code hlvl, lvl_code μ A, body_code hcl,
    naming_of (fun _ h => mem_RAlt_of_peanoMinus h)
      (naming_mem_RAlt (mem_NamingAxioms_out (Λ := {x | x < ν}) hμ h0 hA))
      (naming_mem_RAlt (mem_NamingAxioms_in (Λ := {x | x < ν}) hμ h0 hA))⟩

end Ramified

end OrdinalAnalysis
