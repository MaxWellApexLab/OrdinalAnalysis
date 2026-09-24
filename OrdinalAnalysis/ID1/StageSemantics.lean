/-
  The stage semantics of `ID₁^∞`, and soundness below `Ω`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §5: the intended reading of `I^{≺α} t` (before
  Definition 5.1) and Proposition 5.8 (soundness of `H ⊢^α_ρ Γ` for `α ≺ Ω`); after
  Buchholz, *A simplified version of local predicativity* (1992), §3.

  **The stages.**  For an operator form `A` and a reading `P` of the free predicate `X`, the
  stages of the inductive definition are defined by well-founded recursion on the notations
  (the order of `ThetaNote` is well founded, `ThetaNote.wellFoundedLT`):

      S_α  :=  ⋃_{γ ≺ α} Γ_A(S_γ),        Γ_A(S) = { n | A(n̄, S) holds in ℕ }  (`opA P A`).

  This is exactly the equation of Definition 5.1, `I^{≺α} t ≃ ⋁_{γ≺α} A(t, I^{≺γ})`, read
  in `ℕ`.  No positivity of `A` is needed for the recursion, and none for soundness: the
  stage rules are sound because the stages satisfy their defining equation.

  **The stage model** `stageModel P A` is the `LIinf`-structure on `ℕ` with standard
  arithmetic, `X` read by `P`, and every stage predicate `I^{≺α}` (`α ⪯ Ω`) read by `S_α`.
  At `α = Ω` this is `⋃_{γ≺Ω} Γ_A(S_γ)`, which in general is not closed under `Γ_A`; this
  is why (Fix) is not sound, and why soundness is only claimed for heights `α ≺ Ω` (which
  never use (Fix), as it needs `Ω ⪯ α`).

  **Soundness** (`sound`, Proposition 5.8): if `H ⊢^α_ρ Γ` and `α ≺ Ω`, then some formula of
  `Γ` is true in the stage model, for every `A`, `ρ`, `H` and `P` (free variables read as
  `0`).  Cuts are sound whatever their rank.

  **The accessible part.**  For `A = accForm precC`, the accessibility form of the coded
  order `≺` of the ϑ-notation (all normal forms), the stages are computed from the linearity
  of `≺` alone; no well-foundedness of the accessed order enters:

      codeNote β ∈ S_γ  ⇔  β ≺ γ                      (`codeNote_mem_stageSet_acc`),

  for every notation `β` and every `γ`; in particular `S_γ ∩ field = {code β | β ≺ γ}`
  (`mem_stageSet_acc_of_fieldN`), and a number that codes no notation lies in every
  nonzero stage (`mem_stageSet_acc_of_not_code`).

  Contents.

    `iinfStruc`, `stageStruc`                     `X ↦ P`, `I^{≺α} ↦ S α`
    `val_stageStruc_congr`, `val_numeral_stageStruc`   term values
    `eval_stageAt`, `eval_XinfAt`, `eval_unfold`  the atoms and `A(t, I^{≺γ})`
    `stageSet`, `stageSet_eq`, `mem_stageSet_iff` the stages `S_α`
    `stageModel`, `TrueS`                         the stage model and truth in it
    `sound`                                       **Proposition 5.8**
    `codeNote_mem_stageSet_acc`, `mem_stageSet_acc_of_fieldN`,
    `mem_stageSet_acc_of_not_code`                the stages of the accessible part
-/
import OrdinalAnalysis.ID1.Calculus
import OrdinalAnalysis.ID1.Sound
import OrdinalAnalysis.ID1.Internal.Standard

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

namespace StageSem

open LO LO.FirstOrder

/-! ### Structures reading the stages by given sets -/

/-- The fresh symbols of `LIinf`: `X` read by `P`, the stage `I^{≺α}` by `S α`. -/
@[instance_reducible]
def iinfStruc (P : ℕ → Prop) (S : Stage → Set ℕ) : Structure IInfLang ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ r v => match r with
    | IInfRel.X => P (v 0)
    | IInfRel.stage a => v 0 ∈ S a

/-- The `LIinf`-structure on `ℕ`: arithmetic standard, `X` read by `P`, `I^{≺α}` by
`S α`. -/
@[instance_reducible]
def stageStruc (P : ℕ → Prop) (S : Stage → Set ℕ) : Structure LIinf ℕ :=
  Structure.add ℒₒᵣ IInfLang ℕ (str₂ := iinfStruc P S)

section Struc

variable (P : ℕ → Prop) (S : Stage → Set ℕ)

/-- Term values do not depend on the readings of the fresh predicates. -/
theorem val_stageStruc_congr {ξ : Type*} {n : ℕ} (e : Fin n → ℕ) (f : ξ → ℕ)
    (t : Semiterm LIinf ξ n) :
    Semiterm.val (s := stageStruc P S) e f t = Semiterm.val (s := stdInf) e f t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func fn v ih =>
      simp only [Semiterm.val_func, Function.comp_def, ih]
      rcases fn with fn | fn
      · rfl
      · exact PEmpty.elim fn

/-- The numerals of `LIinf` are the images of the numerals of arithmetic. -/
theorem numeral_lMap_toLIinf {ξ : Type*} {n : ℕ} (k : ℕ) :
    Semiterm.lMap toLIinf ((k : ℕ) : Semiterm ℒₒᵣ ξ n) = ((k : ℕ) : Semiterm LIinf ξ n) := by
  have h0 : Semiterm.lMap toLIinf ((0 : ℕ) : Semiterm ℒₒᵣ ξ n) =
      ((0 : ℕ) : Semiterm LIinf ξ n) := by
    simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
      Semiterm.Operator.Zero.term_eq, toLIinf]
  have h1 : Semiterm.lMap toLIinf ((1 : ℕ) : Semiterm ℒₒᵣ ξ n) =
      ((1 : ℕ) : Semiterm LIinf ξ n) := by
    simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
      Semiterm.Operator.One.term_eq, toLIinf]
  have hadd : ∀ v : Fin 2 → Semiterm ℒₒᵣ ξ n,
      Semiterm.lMap toLIinf (Semiterm.Operator.Add.add.operator v) =
        Semiterm.Operator.Add.add.operator (Semiterm.lMap toLIinf ∘ v) := by
    intro v
    simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, toLIinf]
    funext i
    simp
  have hss : ∀ (L : Language) [L.Zero] [L.One] [L.Add] (k : ℕ),
      ((k + 1 + 1 : ℕ) : Semiterm L ξ n) =
        Semiterm.Operator.Add.add.operator
          ![((k + 1 : ℕ) : Semiterm L ξ n), ((1 : ℕ) : Semiterm L ξ n)] := by
    intro L _ _ _ k
    have h : k + 1 ≠ 0 := Nat.succ_ne_zero k
    simp only [Semiterm.numeral, Semiterm.Operator.const,
      Semiterm.Operator.numeral_succ h, Semiterm.Operator.operator_comp]
    congr 1
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  induction k with
  | zero => exact h0
  | succ k ih =>
    cases k with
    | zero => exact h1
    | succ k =>
      rw [hss ℒₒᵣ k, hss LIinf k, hadd]
      congr 1
      funext i
      match i with
      | ⟨0, _⟩ => exact ih
      | ⟨1, _⟩ => exact h1

/-- **A numeral denotes its value.** -/
@[simp] theorem val_numeral_stageStruc {ξ : Type*} {n : ℕ} (m : ℕ) (e : Fin n → ℕ)
    (f : ξ → ℕ) :
    Semiterm.val (s := stageStruc P S) e f ((m : ℕ) : Semiterm LIinf ξ n) = m := by
  rw [← numeral_lMap_toLIinf m]
  show Semiterm.val (s := Structure.add ℒₒᵣ IInfLang ℕ (str₂ := iinfStruc P S)) e f
    (Semiterm.lMap (Language.Hom.add₁ ℒₒᵣ IInfLang) ((m : ℕ) : Semiterm ℒₒᵣ ξ n)) = m
  rw [Structure.val_lMap_add₁ (str₂ := iinfStruc P S)]
  simp

/-- `I^{≺α} t` holds when the value of `t` lies in `S α`. -/
theorem eval_stageAt {ξ : Type*} {n : ℕ} (a : Stage) (t : Semiterm LIinf ξ n)
    (e : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stageStruc P S) e f (stageAt a t) ↔
      Semiterm.val (s := stageStruc P S) e f t ∈ S a := by
  have h : (Semiterm.val (s := stageStruc P S) e f ∘ ![t] : Fin 1 → ℕ)
      = ![Semiterm.val (s := stageStruc P S) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg ((stageStruc P S).rel (Sum.inr (IInfRel.stage a))) h)

/-- `X t` holds when `P` holds at the value of `t`. -/
theorem eval_XinfAt {ξ : Type*} {n : ℕ} (t : Semiterm LIinf ξ n) (e : Fin n → ℕ)
    (f : ξ → ℕ) :
    Semiformula.Eval (s := stageStruc P S) e f (XinfAt t) ↔
      P (Semiterm.val (s := stageStruc P S) e f t) := by
  have h : (Semiterm.val (s := stageStruc P S) e f ∘ ![t] : Fin 1 → ℕ)
      = ![Semiterm.val (s := stageStruc P S) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg ((stageStruc P S).rel (Sum.inr IInfRel.X)) h)

/-- Reading `I ↦ I^{≺γ}` back: the reduct of the stage structure along `stageHom γ` is the
standard `LXI`-structure with `I` read by `S γ`. -/
theorem lMap_stageHom_stageStruc (g : Stage) :
    (stageStruc P S).lMap (stageHom g) = stdI P (S g) := by
  have hf : ((stageStruc P S).lMap (stageHom g)).func = (stdI P (S g)).func := by
    funext k fn v
    rcases fn with fn | fn
    · rfl
    · exact PEmpty.elim fn
  have hr : ((stageStruc P S).lMap (stageHom g)).rel = (stdI P (S g)).rel := by
    funext k r v
    rcases r with r | r
    · rfl
    · cases r <;> rfl
  cases h : (stageStruc P S).lMap (stageHom g)
  cases h' : stdI P (S g)
  rw [h] at hf hr
  rw [h'] at hf hr
  cases hf
  cases hr
  rfl

/-- **`A(t, I^{≺γ})` holds exactly when the value of `t` is in `Γ_A(S γ)`.** -/
theorem eval_unfold (A : Semisentence LXI 1) (g : Stage) {ξ : Type*} {n : ℕ}
    (t : Semiterm LIinf ξ n) (e : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stageStruc P S) e f (unfold A g t) ↔
      Semiterm.val (s := stageStruc P S) e f t ∈ opA P A (S g) := by
  rw [unfold, Semiformula.eval_substs, Matrix.comp₁, Semiformula.eval_emb, formAt,
    Semiformula.eval_lMap, lMap_stageHom_stageStruc]
  rfl

/-- A closed literal of arithmetic has the truth value it has in `ℕ`. -/
theorem eval_of_trueLit {φ : Proposition LIinf} (h : TrueLit φ) :
    Semiformula.Eval (s := stageStruc P S) ![] (fun _ => 0) φ := by
  obtain ⟨⟨k, r, v, hφ, -⟩, ht⟩ := h
  unfold TrueN at ht
  have e : (fun i => Semiterm.val (s := stageStruc P S) ![] (fun _ => 0) (v i)) =
      (fun i => Semiterm.val (s := stdInf) ![] (fun _ => 0) (v i)) := by
    funext i
    exact val_stageStruc_congr P S _ _ (v i)
  rcases hφ with rfl | rfl
  · have ht' : Structure.rel (L := ℒₒᵣ) (M := ℕ) r
        (fun i => Semiterm.val (s := stdInf) ![] (fun _ => 0) (v i)) := ht
    show Structure.rel (L := ℒₒᵣ) (M := ℕ) r
      (fun i => Semiterm.val (s := stageStruc P S) ![] (fun _ => 0) (v i))
    rw [e]
    exact ht'
  · have ht' : ¬Structure.rel (L := ℒₒᵣ) (M := ℕ) r
        (fun i => Semiterm.val (s := stdInf) ![] (fun _ => 0) (v i)) := ht
    show ¬Structure.rel (L := ℒₒᵣ) (M := ℕ) r
      (fun i => Semiterm.val (s := stageStruc P S) ![] (fun _ => 0) (v i))
    rw [e]
    exact ht'

end Struc

/-! ### The stages -/

section Stages

variable (P : ℕ → Prop) (A : Semisentence LXI 1)

/-- **The stages** `S_α = ⋃_{γ≺α} Γ_A(S_γ)`, by well-founded recursion on the notations. -/
noncomputable def stageSet : ThetaNote → Set ℕ :=
  WellFounded.fix (wellFounded_lt (α := ThetaNote))
    (fun a rec => ⋃ g : ThetaNote, ⋃ (h : g < a), opA P A (rec g h))

/-- The defining equation of the stages (Definition 5.1 read in `ℕ`). -/
theorem stageSet_eq (a : ThetaNote) :
    stageSet P A a = ⋃ g : ThetaNote, ⋃ (_ : g < a), opA P A (stageSet P A g) :=
  WellFounded.fix_eq _ _ a

theorem mem_stageSet_iff (a : ThetaNote) (n : ℕ) :
    n ∈ stageSet P A a ↔ ∃ g : ThetaNote, g < a ∧ n ∈ opA P A (stageSet P A g) := by
  rw [stageSet_eq]
  simp only [Set.mem_iUnion, exists_prop]

/-- **The stage model**: arithmetic standard, `X` read by `P`, and `I^{≺α}` read by the
stage `S_α`, for every `α ⪯ Ω`. -/
@[instance_reducible]
noncomputable def stageModel : Structure LIinf ℕ :=
  stageStruc P (fun a => stageSet P A a.1)

/-- Truth in the stage model, free variables read as `0`. -/
def TrueS (φ : Proposition LIinf) : Prop :=
  Semiformula.Eval (s := stageModel P A) ![] (fun _ => 0) φ

end Stages

/-! ### Soundness below `Ω` (Proposition 5.8) -/

section Soundness

variable (P : ℕ → Prop) (A : Semisentence LXI 1)

theorem trueS_stageAt (a : Stage) (t : SyntacticTerm LIinf) :
    TrueS P A (stageAt a t) ↔
      Semiterm.val (s := stageModel P A) ![] (fun _ => 0) t ∈ stageSet P A a.1 :=
  eval_stageAt P _ a t _ _

theorem trueS_unfold (g : Stage) (t : SyntacticTerm LIinf) :
    TrueS P A (unfold A g t) ↔
      Semiterm.val (s := stageModel P A) ![] (fun _ => 0) t ∈ opA P A (stageSet P A g.1) :=
  eval_unfold P _ A g t _ _

theorem trueS_neg (φ : Proposition LIinf) : TrueS P A (∼φ) ↔ ¬TrueS P A φ := by
  simp [TrueS]

theorem trueS_subst_numeral (φ : Semiproposition LIinf 1) (n : ℕ) :
    TrueS P A (φ/[numI n]) ↔
      Semiformula.Eval (s := stageModel P A) ![n] (fun _ => 0) φ := by
  unfold TrueS
  rw [Semiformula.eval_substs, Matrix.comp₁]
  have h : Semiterm.val (s := stageModel P A) ![] (fun _ => 0) (numI n) = n :=
    val_numeral_stageStruc P _ n _ _
  rw [h]

/-- **Proposition 5.8 (soundness below `Ω`)**: a sequent derived at a height `α ≺ Ω`
contains a formula true in the stage model.  This holds for every operator form, every cut
rank, every operator and every reading of `X`. -/
theorem sound {ρ : ThetaNote} {H : Set ThetaNote → Set ThetaNote} {α : ThetaNote}
    {Γ : Sequent LIinf} (d : IDerivable A ρ H α Γ) :
    α < ThetaNote.Omega → ∃ φ ∈ Γ, TrueS P A φ := by
  induction d with
  | literal _ _ hφ hm => exact fun _ => ⟨_, hm, eval_of_trueLit P _ hφ⟩
  | verum _ _ hm =>
    intro _
    refine ⟨⊤, hm, ?_⟩
    simp [TrueS]
  | idX t _ _ h1 h2 =>
    intro _
    by_cases h : TrueS P A (XinfAt t)
    · exact ⟨_, h1, h⟩
    · exact ⟨_, h2, (trueS_neg P A _).mpr h⟩
  | @and H α Γ φ ψ α₀ α₁ _ _ hm h0 h1 _ _ ih0 ih1 =>
    intro hα
    obtain ⟨χ₀, hχ₀, t₀⟩ := ih0 (lt_trans h0 hα)
    obtain ⟨χ₁, hχ₁, t₁⟩ := ih1 (lt_trans h1 hα)
    rcases List.mem_cons.mp hχ₀ with rfl | hχ₀
    · rcases List.mem_cons.mp hχ₁ with rfl | hχ₁
      · refine ⟨_, hm, ?_⟩
        unfold TrueS at t₀ t₁ ⊢
        rw [LogicalConnective.HomClass.map_and]
        exact ⟨t₀, t₁⟩
      · exact ⟨χ₁, hχ₁, t₁⟩
    · exact ⟨χ₀, hχ₀, t₀⟩
  | @orL H α Γ φ ψ α₀ _ _ hm h0 _ ih0 =>
    intro hα
    obtain ⟨χ, hχ, t⟩ := ih0 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ with rfl | hχ
    · refine ⟨_, hm, ?_⟩
      unfold TrueS at t ⊢
      rw [LogicalConnective.HomClass.map_or]
      exact Or.inl t
    · exact ⟨χ, hχ, t⟩
  | @orR H α Γ φ ψ α₀ _ _ hm _ h0 _ ih0 =>
    intro hα
    obtain ⟨χ, hχ, t⟩ := ih0 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ with rfl | hχ
    · refine ⟨_, hm, ?_⟩
      unfold TrueS at t ⊢
      rw [LogicalConnective.HomClass.map_or]
      exact Or.inr t
    · exact ⟨χ, hχ, t⟩
  | @all H α Γ φ f _ _ hm hf _ ih =>
    intro hα
    by_cases hΓ : ∃ χ ∈ Γ, TrueS P A χ
    · exact hΓ
    · refine ⟨_, hm, ?_⟩
      unfold TrueS
      rw [Semiformula.eval_all]
      intro n
      obtain ⟨χ, hχ, t⟩ := ih n (lt_trans (hf n) hα)
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact (trueS_subst_numeral P A φ n).mp t
      · exact absurd ⟨χ, hχ, t⟩ hΓ
  | @exs H α Γ φ n α₀ _ _ hm _ h0 _ ih0 =>
    intro hα
    obtain ⟨χ, hχ, t⟩ := ih0 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ with rfl | hχ
    · refine ⟨_, hm, ?_⟩
      unfold TrueS
      rw [Semiformula.eval_ex]
      exact ⟨n, (trueS_subst_numeral P A φ n).mp t⟩
    · exact ⟨χ, hχ, t⟩
  | @stage H α Γ a t g α₀ _ _ hm hga _ _ h0 _ ih0 =>
    intro hα
    obtain ⟨χ, hχ, tr⟩ := ih0 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ with rfl | hχ
    · refine ⟨_, hm, ?_⟩
      rw [trueS_stageAt, mem_stageSet_iff]
      exact ⟨g.1, hga, (trueS_unfold P A g t).mp tr⟩
    · exact ⟨χ, hχ, tr⟩
  | @nstage H α Γ a t f _ _ hm hf _ ih =>
    intro hα
    by_cases hΓ : ∃ χ ∈ Γ, TrueS P A χ
    · exact hΓ
    · refine ⟨_, hm, ?_⟩
      rw [← neg_stageAt, trueS_neg, trueS_stageAt, mem_stageSet_iff]
      rintro ⟨g, hga, hg⟩
      let g' : Stage := ⟨g, le_of_lt (lt_of_lt_of_le hga a.2)⟩
      obtain ⟨χ, hχ, tr⟩ := ih g' hga (lt_trans (hf g' hga) hα)
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact (trueS_neg P A _).mp tr ((trueS_unfold P A g' t).mpr hg)
      · exact hΓ ⟨χ, hχ, tr⟩
  | fix _ _ _ hΩ _ _ _ =>
    intro hα
    exact absurd (lt_of_le_of_lt hΩ hα) (lt_irrefl _)
  | @cut H α Γ ψ α₀ _ _ _ h0 _ _ ih0 ih1 =>
    intro hα
    obtain ⟨χ₀, hχ₀, t₀⟩ := ih0 (lt_trans h0 hα)
    obtain ⟨χ₁, hχ₁, t₁⟩ := ih1 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ₀ with rfl | hχ₀
    · rcases List.mem_cons.mp hχ₁ with rfl | hχ₁
      · exact absurd t₀ ((trueS_neg P A _).mp t₁)
      · exact ⟨χ₁, hχ₁, t₁⟩
    · exact ⟨χ₀, hχ₀, t₀⟩

end Soundness

/-! ### The stages of the accessible part -/

section Acc

open OrdinalAnalysis.ID1.Internal

variable (P : ℕ → Prop)

/-- The operator of the accessibility form of the coded order: `n` enters once every code
`≺`-below it is in `S`. -/
theorem mem_opA_acc_iff (S : Set ℕ) (n : ℕ) :
    n ∈ opA P (accForm precC) S ↔ ∀ y, precN y n → y ∈ S :=
  opA_accForm precC P S n

/-- **The stages of the accessible part** (linearity suffices): the code of `β` enters at
a stage below `γ` exactly when `β ≺ γ`. -/
theorem codeNote_mem_stageSet_acc (γ b : ThetaNote) :
    codeNote b ∈ stageSet P (accForm precC) γ ↔ b < γ := by
  induction γ using WellFoundedLT.induction generalizing b with
  | _ γ ih =>
    rw [mem_stageSet_iff]
    constructor
    · rintro ⟨g, hgγ, hg⟩
      by_contra hbγ
      have hgb : g < b := lt_of_lt_of_le hgγ (not_lt.mp hbγ)
      have hmem := (mem_opA_acc_iff P _ _).mp hg (codeNote g)
        ((precN_codeNote_iff g b).mpr hgb)
      exact lt_irrefl g ((ih g hgγ g).mp hmem)
    · intro hbγ
      refine ⟨b, hbγ, (mem_opA_acc_iff P _ _).mpr fun y hy => ?_⟩
      obtain ⟨a, b', rfl, hb', hab⟩ := precN_exists_lt hy
      exact (ih b hbγ a).mpr (codeNote_injective hb' ▸ hab)

/-- **`I^{≺γ} ∩ field = {code β | β ≺ γ}`**: on the field of the accessibility order (the
codes of the notations below `Ω`), the stage `S_γ` consists of the codes of the notations
below `γ`. -/
theorem mem_stageSet_acc_of_fieldN (γ : ThetaNote) {n : ℕ} (hn : fieldN n) :
    n ∈ stageSet P (accForm precC) γ ↔ ∃ b : ThetaField, codeField b = n ∧ b.1 < γ := by
  obtain ⟨b, rfl⟩ := (fieldN_iff n).mp hn
  constructor
  · intro h
    exact ⟨b, rfl, (codeNote_mem_stageSet_acc P γ b.1).mp h⟩
  · rintro ⟨b', hb', hlt⟩
    have e : b' = b := Subtype.ext (codeNote_injective hb')
    subst e
    exact (codeNote_mem_stageSet_acc P γ b'.1).mpr hlt

/-- A number that codes no notation has no `≺`-predecessor, so it enters at the first
stage. -/
theorem mem_stageSet_acc_of_not_code (γ : ThetaNote) {n : ℕ}
    (hn : ∀ b : ThetaNote, codeNote b ≠ n) :
    n ∈ stageSet P (accForm precC) γ ↔ ∃ g : ThetaNote, g < γ := by
  rw [mem_stageSet_iff]
  refine ⟨fun ⟨g, hg, _⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨g, hg, ?_⟩⟩
  refine (mem_opA_acc_iff P _ _).mpr fun y hy => ?_
  obtain ⟨_, b, _, hb, _⟩ := precN_exists_lt hy
  exact absurd hb (hn b)

end Acc

end StageSem

end InductiveDef

end OrdinalAnalysis
