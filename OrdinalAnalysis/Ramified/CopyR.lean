/-
  Copying sets up the levels, and the closure properties of transfinite
  induction at a level of ramified analysis.

  With `TI_κ(a) :≡ ∀z TI(≺₁, a, λx. x ∈̇_κ z)` (`tiMuR κ`):

  * **Copy lemma** (`copy_provable`).  For `κ < μ < ν`,

        RAlt ν ⊢ ∀z ∃w ∀x (x ∈̇_μ w ↔ x ∈̇_κ z):

    the body `x ∈̇_κ z` has shape `μ`, since its only set atom has level
    `κ < μ` (the shape condition allows any arguments below the top level),
    and `z` is the comprehension parameter.  At a numeral `p` the set is named
    by one particular code, the level-`μ` code of `#0 ∈̇_κ &0` with parameter
    `p` (`copyCode`, `copy_naming_provable`); this is the per-code form of the
    same fact, for numeral instances.  More generally every formula of shape
    `μ` is named at every numeral parameter by its canonical code with that
    parameter (`naming_param_provable`).

  * **Copying transfinite induction down** (`tiCopy_provable`):
    `TI_μ(a) → TI_κ(a)` for `κ < μ < ν`: a level-`κ` set is a level-`μ` set.

  * **Downward closure** (`tiDown_provable`, `tiDown_code_provable`):
    `x ≺₁ a → TI_κ(a) → TI_κ(x)`, for every level `κ < ν`; and the segment
    form `TI(≺_b, ā, X) → TI(≺_b, ā', X)` for `a' < a < b`
    (`tiUptoSegR_downward_provable`).

  * **Successor step** (`tiSucc_provable`):
    `Base(e) → e + 1 = s → TI_κ(e) → TI_κ(s)`, `Base(e)` saying that `e` is `0`
    or a single Veblen term `φ_p(q)` with `p ≠ 0`.

  * **Zero** (`tiZero_provable`): `TI_κ(0)`.

  * **Instantiation** (`tiInst_provable`): `TI_μ(t) → TI(≺₁, t, F)` for every
    closed formula `F` of level `< μ`: comprehension names `{x | F(x)}` by a
    level-`μ` set.

  As for the tower induction, everything is proved in a model of `RAlt ν`
  with true equality and turned into provability by `provable_of_eqModels`.
-/
import OrdinalAnalysis.Ramified.UpperBound

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalVNote (precDef₁)
open OrdinalAnalysis.Gentzen.InternalVNoteJump (safeIadd₁Def)
open OrdinalAnalysis.Gentzen.VeblenSuccStep (baseDef₁)
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)

/-! ### The copy formula -/

/-- The body `x ∈̇_κ z` of the copy of a level-`κ` set, with subject `#0` and
parameter `&0`. -/
def copyBody (κ : Lv) : Semiformula LRA ℕ 1 := memAt κ (#0 : Semiterm LRA ℕ 1) &0

theorem shape_copyBody {κ μ : Lv} (h : κ < μ) : Shape μ (copyBody κ) :=
  (shape_memAt κ _ _).mpr (Or.inl h)

theorem lvlOf_copyBody (κ : Lv) : lvlOf (copyBody κ) = κ := by
  rw [copyBody, lvlOf_memAt]

theorem eval_copyBody {M : Type} [s : Structure LRA M] (κ : Lv) (x z : M) :
    Semiformula.Eval (s := s) ![x] (fun _ => z) (copyBody κ) ↔ memM κ x z := by
  rw [copyBody, eval_memAt]
  rfl

/-- **The copy lemma**: `RAlt ν ⊢ ∀z ∃w ∀x (x ∈̇_μ w ↔ x ∈̇_κ z)`, for `κ < μ < ν`. -/
theorem copy_provable {ν μ κ : Lv} (hκ : κ < μ) (hμ : μ < ν) :
    RAlt ν ⊢ Semiformula.univCl (compr μ (copyBody κ)) :=
  exists_comprehension_code_lt (lt_of_le_of_lt (Gamma0Note.zero_le_note κ) hκ) hμ
    (shape_copyBody hκ)

/-! ### Naming at a numeral parameter -/

/-- The canonical level-`μ` code of `A` with parameter `p`: the stage is the
least the stage condition allows. -/
def codeP (μ : Lv) (A : Semiformula LRA ℕ 1) (p : ℕ) : ℕ :=
  mkCode μ (A.complexity + stage p + 1) (Encodable.encode A) p

@[simp] theorem lvl_codeP (μ : Lv) (A : Semiformula LRA ℕ 1) (p : ℕ) : lvl (codeP μ A p) = μ :=
  lvl_mkCode _ _ _ _

theorem body_codeP (μ : Lv) (A : Semiformula LRA ℕ 1) (p : ℕ) :
    body (codeP μ A p) = instParam p ▹ A :=
  body_mkCode _ _ _ _

theorem good_codeP {μ : Lv} {A : Semiformula LRA ℕ 1} (h0 : 0 < μ) (hA : Shape μ A) (p : ℕ) :
    Good (codeP μ A p) :=
  good_mkCode h0 hA (Nat.lt_succ_self _)

theorem eval_body_codeP {M : Type*} [s : Structure LRA M] (μ : Lv) (A : Semiformula LRA ℕ 1)
    (p : ℕ) (x : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![x] f (body (codeP μ A p))
      ↔ Semiformula.Eval (s := s) ![x] (fun _ => numVal M p) A := by
  rw [body_codeP, instParam, Semiformula.eval_rewrite]
  have h : (fun _ : ℕ => Semiterm.val (s := s) ![x] f (numAtR p : Semiterm LRA ℕ 1))
      = fun _ => numVal M p := funext fun _ => val_numAtR_model _ _ p
  rw [h]

/-- **The canonical code with parameter `p` names its body**, in any theory
with `PA⁻` and the two naming axioms of the formula. -/
theorem naming_param_of {T : Theory LRA} (hPA : Theory.lMap toLRA 𝗣𝗔⁻ ⊆ T) {μ : Lv}
    {A : Semiformula LRA ℕ 1} (p : ℕ)
    (hout : Semiformula.univCl (nameOutP μ A) ∈ T) (hin : Semiformula.univCl (nameInP μ A) ∈ T) :
    T ⊢ Semiformula.univCl (nameOut (codeP μ A p)) ∧
      T ⊢ Semiformula.univCl (nameIn (codeP μ A p)) := by
  have hst : A.complexity + stage p < A.complexity + stage p + 1 := Nat.lt_succ_self _
  constructor
  · apply Theory.Proof.complete.{0, 0}
    rw [consequence_iff]
    intro M _ s hM
    rw [models_iff, Semiformula.eval_univCl]
    intro f
    rw [nameOut, Semiformula.eval_all]
    intro x
    rw [LogicalConnective.HomClass.map_or, eval_nmemAt, lvl_codeP, eval_body_codeP]
    have hv : Semiterm.val (s := s) ![x] f (nameTerm (codeP μ A p)) = numVal M (codeP μ A p) :=
      val_numAtR_model _ _ _
    rw [hv]
    by_cases hx : memM μ (Semiterm.val (s := s) ![x] f (#0 : Semiterm LRA ℕ 1))
        (numVal M (codeP μ A p))
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
      lvl_codeP, eval_body_codeP]
    have hv : Semiterm.val (s := s) ![x] f (nameTerm (codeP μ A p)) = numVal M (codeP μ A p) :=
      val_numAtR_model _ _ _
    rw [hv]
    by_cases hx : Semiformula.Eval (s := s) ![x] (fun _ => numVal M p) A
    · exact Or.inr (models_nameInP (Semantics.modelsSet_iff.mp hM hin) _ _ _
        (reduct_guardAt hPA hM rfl hst) _ hx)
    · exact Or.inl hx

/-- **Naming at a numeral parameter** in `RA_{<ν}`: for `A` of shape `μ`,
`0 < μ < ν`, and every numeral `p`, the code `codeP μ A p` is `Good`, has level
`μ`, and names `A(·, p)`. -/
theorem naming_param_provable {ν μ : Lv} (h0 : 0 < μ) (hμ : μ < ν) {A : Semiformula LRA ℕ 1}
    (hA : Shape μ A) (p : ℕ) :
    RAlt ν ⊢ Semiformula.univCl (nameOut (codeP μ A p)) ∧
      RAlt ν ⊢ Semiformula.univCl (nameIn (codeP μ A p)) :=
  naming_param_of (fun _ h => mem_RAlt_of_peanoMinus h) p
    (naming_mem_RAlt (mem_NamingAxioms_out (Λ := {x | x < ν}) hμ h0 hA))
    (naming_mem_RAlt (mem_NamingAxioms_in (Λ := {x | x < ν}) hμ h0 hA))

/-- The level-`μ` code of the level-`κ` set named `p`. -/
def copyCode (μ κ : Lv) (p : ℕ) : ℕ := codeP μ (copyBody κ) p

@[simp] theorem lvl_copyCode (μ κ : Lv) (p : ℕ) : lvl (copyCode μ κ p) = μ := lvl_codeP _ _ _

theorem good_copyCode {μ κ : Lv} (hκ : κ < μ) (p : ℕ) : Good (copyCode μ κ p) :=
  good_codeP (lt_of_le_of_lt (Gamma0Note.zero_le_note κ) hκ) (shape_copyBody hκ) p

/-- The body of the copy code is `x ∈̇_κ p̄`. -/
theorem body_copyCode (μ κ : Lv) (p : ℕ) :
    body (copyCode μ κ p) = memAt κ (#0 : Semiterm LRA ℕ 1) (numAtR p) := by
  rw [copyCode, body_codeP, copyBody, memAt, memAt]
  refine (Semiformula.rew_rel (instParam p) (Sum.inr (RARel.mem κ) : LRA.Rel 2) _).trans ?_
  refine congrArg _ (funext fun i => ?_)
  fin_cases i <;> rfl

/-- **The copy lemma at a numeral**: the level-`μ` code `copyCode μ κ p` names
the level-`κ` set `p`, i.e. `∀x (x ∈̇_μ c̄ ↔ x ∈̇_κ p̄)` for `c = copyCode μ κ p`,
for `κ < μ < ν`. -/
theorem copy_naming_provable {ν μ κ : Lv} (hκ : κ < μ) (hμ : μ < ν) (p : ℕ) :
    RAlt ν ⊢ Semiformula.univCl (nameOut (copyCode μ κ p)) ∧
      RAlt ν ⊢ Semiformula.univCl (nameIn (copyCode μ κ p)) :=
  naming_param_provable (lt_of_le_of_lt (Gamma0Note.zero_le_note κ) hκ) hμ (shape_copyBody hκ) p

/-! ### The copy lemma and transfinite induction in a model -/

section Model

variable {M : Type} [Nonempty M] [s : Structure LRA M] [Structure.Eq LRA M] {ν μ κ : Lv}

omit [Structure.Eq LRA M] in
/-- **The copy lemma in a model.** -/
theorem copyM (hM : M↓[LRA] ⊧* RAlt ν) (hκ : κ < μ) (hμ : μ < ν) (z : M) :
    ∃ w : M, ∀ x : M, memM μ x w ↔ memM κ x z := by
  obtain ⟨w, hw⟩ := comprM hM (lt_of_le_of_lt (Gamma0Note.zero_le_note κ) hκ) hμ
    (shape_copyBody hκ) z
  exact ⟨w, fun x => (hw x).trans (eval_copyBody κ x z)⟩

omit [Structure.Eq LRA M] in
/-- **`TI_μ(a) → TI_κ(a)`** in a model, for `κ < μ < ν`. -/
theorem TImu_copy (hM : M↓[LRA] ⊧* RAlt ν) (hκ : κ < μ) (hμ : μ < ν) {a : M}
    (h : TImu μ a) : TImu κ a := by
  intro z
  obtain ⟨w, hw⟩ := copyM hM hκ hμ z
  exact (TIupM_congr hw a).mp (h w)

/-- **Downward closure** in a model: `x ≺₁ a → TI_κ(a) → TI_κ(x)`. -/
theorem TImu_down (hM : M↓[LRA] ⊧* RAlt ν) (hν : 1 ≤ ν) {a x : M} (hx : precM x a)
    (h : TImu κ a) : TImu κ x :=
  fun z hprog y hy => h z hprog y (precM_trans hM hν hy hx)

omit [Structure.Eq LRA M] in
/-- **Instantiation** in a model: `TI_μ(a) → TI(≺₁, a, F)` for a closed formula
`F` of level `< μ`, `μ < ν`. -/
theorem TImu_inst (hM : M↓[LRA] ⊧* RAlt ν) (hμ : μ < ν) {F : Semiformula LRA ℕ 1}
    (hF : lvlOf F < μ) (hcl : F.freeVariables = ∅) (f : ℕ → M) {a : M} (h : TImu μ a) :
    TIupM (fun x => Semiformula.Eval (s := s) ![x] f F) a := by
  obtain ⟨w, hw⟩ := comprM hM (lt_of_le_of_lt (Gamma0Note.zero_le_note _) hF) hμ
    (shape_of_lvlOf_lt hF) (Classical.arbitrary M)
  have hw' : ∀ x, memM μ x w ↔ Semiformula.Eval (s := s) ![x] f F := fun x =>
    (hw x).trans (Semiformula.eval_iff_of_funEqOn F fun y hy => by
      have hy' : y ∈ F.freeVariables := hy
      rw [hcl] at hy'
      exact absurd hy' (Finset.notMem_empty y))
  exact (TIupM_congr hw' a).mp (h w)

end Model

/-! ### The formulas -/

/-- `TI_μ(a) → TI_κ(a)`, with `a` the bound variable. -/
def tiCopyR (μ κ : Lv) : Semiformula LRA ℕ 1 := ∼(tiMuR μ) ⋎ tiMuR κ

/-- `x ≺₁ a → TI_κ(a) → TI_κ(x)`, with `#0 = x`, `#1 = a`. -/
def tiDownR (κ : Lv) : Semiformula LRA ℕ 2 :=
  ∼(arAt precDef₁.val ![(#0 : Semiterm LRA ℕ 2), #1]) ⋎
    (∼((tiMuR κ)/[(#1 : Semiterm LRA ℕ 2)]) ⋎ (tiMuR κ)/[(#0 : Semiterm LRA ℕ 2)])

/-- `Base(e) → e + 1 = s → TI_κ(e) → TI_κ(s)`, with `#0 = s`, `#1 = e`. -/
def tiSuccR (κ : Lv) : Semiformula LRA ℕ 2 :=
  ∼(arAt baseDef₁.val ![(#1 : Semiterm LRA ℕ 2)]) ⋎
    (∼(arAt safeIadd₁Def.val ![(#0 : Semiterm LRA ℕ 2), #1, numAtR (gamma0Code 1)]) ⋎
      (∼((tiMuR κ)/[(#1 : Semiterm LRA ℕ 2)]) ⋎ (tiMuR κ)/[(#0 : Semiterm LRA ℕ 2)]))

theorem lvlOf_tiCopyR_le {μ κ : Lv} (hκ : κ ≤ μ) : lvlOf (tiCopyR μ κ) ≤ μ := by
  rw [tiCopyR, lvlOf_or, lvlOf_neg]
  exact max_le (lvlOf_tiMuR_le μ) (le_trans (lvlOf_tiMuR_le κ) hκ)

theorem lvlOf_tiDownR_le (κ : Lv) : lvlOf (tiDownR κ) ≤ κ := by
  simp only [tiDownR, lvlOf_or, lvlOf_neg, lvlOf_arAt, lvlOf_subst₁]
  exact max_le (Gamma0Note.zero_le_note κ) (max_le (lvlOf_tiMuR_le κ) (lvlOf_tiMuR_le κ))

theorem lvlOf_tiSuccR_le (κ : Lv) : lvlOf (tiSuccR κ) ≤ κ := by
  simp only [tiSuccR, lvlOf_or, lvlOf_neg, lvlOf_arAt, lvlOf_subst₁]
  exact max_le (Gamma0Note.zero_le_note κ) (max_le (Gamma0Note.zero_le_note κ)
    (max_le (lvlOf_tiMuR_le κ) (lvlOf_tiMuR_le κ)))

section Eval

variable {M : Type} [s : Structure LRA M]

theorem eval_tiCopyR (μ κ : Lv) (a : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![a] f (tiCopyR μ κ) ↔ (TImu μ a → TImu κ a) := by
  rw [tiCopyR, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    eval_tiMuR, eval_tiMuR]
  exact imp_iff_not_or.symm

theorem eval_tiDownR (κ : Lv) (x a : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![x, a] f (tiDownR κ) ↔
      (precM x a → TImu κ a → TImu κ x) := by
  simp only [tiDownR, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, eval_arAt,
    eval_tiMuR_subst, Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  have hp : arEval precDef₁.val (fun i => Semiterm.val (s := s) ![x, a] f
      (![(#0 : Semiterm LRA ℕ 2), #1] i)) ↔ precM x a := by
    have hv : (fun i => Semiterm.val (s := s) ![x, a] f
        (![(#0 : Semiterm LRA ℕ 2), #1] i)) = ![x, a] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    rfl
  rw [hp]
  tauto

theorem eval_tiSuccR (κ : Lv) (s₀ e : M) (f : ℕ → M) :
    Semiformula.Eval (s := s) ![s₀, e] f (tiSuccR κ) ↔
      (baseM e → addM s₀ e oneM → TImu κ e → TImu κ s₀) := by
  simp only [tiSuccR, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq, eval_arAt,
    eval_tiMuR_subst, Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  have hb : arEval baseDef₁.val (fun i => Semiterm.val (s := s) ![s₀, e] f
      (![(#1 : Semiterm LRA ℕ 2)] i)) ↔ baseM e := by
    have hv : (fun i => Semiterm.val (s := s) ![s₀, e] f
        (![(#1 : Semiterm LRA ℕ 2)] i)) = ![e] := by
      funext i
      fin_cases i
      rfl
    rw [hv]
    rfl
  have ha : arEval safeIadd₁Def.val (fun i => Semiterm.val (s := s) ![s₀, e] f
      (![(#0 : Semiterm LRA ℕ 2), #1, numAtR (gamma0Code 1)] i)) ↔ addM s₀ e oneM := by
    have hv : (fun i => Semiterm.val (s := s) ![s₀, e] f
        (![(#0 : Semiterm LRA ℕ 2), #1, numAtR (gamma0Code 1)] i)) = ![s₀, e, oneM] := by
      funext i
      fin_cases i
      · rfl
      · rfl
      · exact val_numAtR_model _ _ _
    rw [hv]
    rfl
  rw [hb, ha]
  tauto

end Eval

/-! ### The provable forms -/

private theorem cons_empty_eq {N : Type} (x : N) : (x :> (![] : Fin 0 → N)) = ![x] := by
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  rfl

/-- **Copying transfinite induction down**: `RAlt ν ⊢ ∀a (TI_μ(a) → TI_κ(a))`,
for `κ < μ < ν`. -/
theorem tiCopy_provable {ν μ κ : Lv} (hκ : κ < μ) (hμ : μ < ν) :
    RAlt ν ⊢ Semiformula.univCl (∀¹ tiCopyR μ κ) := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos
    (lt_of_le_of_lt (Gamma0Note.zero_le_note κ) (lt_trans hκ hμ))
  refine provable_of_eqModels hν ?_ ?_
  · rw [lvlOf_emb_univCl, lvlOf_all]
    exact lt_of_le_of_lt (lvlOf_tiCopyR_le hκ.le) hμ
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f (∀¹ tiCopyR μ κ)
    rw [Semiformula.eval_all]
    intro a
    rw [cons_empty_eq, eval_tiCopyR]
    exact TImu_copy hN hκ hμ

/-- **Downward closure**: `RAlt ν ⊢ ∀a ∀x (x ≺₁ a → TI_κ(a) → TI_κ(x))`, for
every level `κ < ν`. -/
theorem tiDown_provable {ν κ : Lv} (hκ : κ < ν) :
    RAlt ν ⊢ Semiformula.univCl (∀¹ ∀¹ tiDownR κ) := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos (lt_of_le_of_lt (Gamma0Note.zero_le_note κ) hκ)
  refine provable_of_eqModels hν ?_ ?_
  · rw [lvlOf_emb_univCl, lvlOf_all, lvlOf_all]
    exact lt_of_le_of_lt (lvlOf_tiDownR_le κ) hκ
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f (∀¹ ∀¹ tiDownR κ)
    rw [Semiformula.eval_all]
    intro a
    rw [Semiformula.eval_all]
    intro x
    rw [cons_empty_eq, eval_tiDownR]
    exact fun hx h => TImu_down hN hν hx h

/-- **The successor step**:
`RAlt ν ⊢ ∀e ∀s (Base(e) → e + 1 = s → TI_κ(e) → TI_κ(s))`, for every level
`κ < ν`. -/
theorem tiSucc_provable {ν κ : Lv} (hκ : κ < ν) :
    RAlt ν ⊢ Semiformula.univCl (∀¹ ∀¹ tiSuccR κ) := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos (lt_of_le_of_lt (Gamma0Note.zero_le_note κ) hκ)
  refine provable_of_eqModels hν ?_ ?_
  · rw [lvlOf_emb_univCl, lvlOf_all, lvlOf_all]
    exact lt_of_le_of_lt (lvlOf_tiSuccR_le κ) hκ
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f (∀¹ ∀¹ tiSuccR κ)
    rw [Semiformula.eval_all]
    intro e
    rw [Semiformula.eval_all]
    intro s₀
    rw [cons_empty_eq, eval_tiSuccR]
    exact fun hb ha h => TImu_succ hN hκ hb ha h

/-- **`TI_κ(0)`**, for every level `κ < ν`. -/
theorem tiZero_provable {ν κ : Lv} (hκ : κ < ν) :
    RAlt ν ⊢ Semiformula.univCl ((tiMuR κ)/[(numAtR 0 : Semiterm LRA ℕ 0)]) := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos (lt_of_le_of_lt (Gamma0Note.zero_le_note κ) hκ)
  refine provable_of_eqModels hν ?_ ?_
  · rw [lvlOf_emb_univCl, lvlOf_subst₁]
    exact lt_of_le_of_lt (lvlOf_tiMuR_le κ) hκ
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f ((tiMuR κ)/[(numAtR 0 : Semiterm LRA ℕ 0)])
    rw [eval_tiMuR_subst, val_numAtR_model]
    exact TImu_zero hN hν

/-- **Downward closure at notations**: `RAlt ν ⊢ TI_κ(ā) → TI_κ(x̄)` for
notations `x < a` and every level `κ < ν`. -/
theorem tiDown_code_provable {ν κ : Lv} (hκ : κ < ν) {x a : Gamma0Note} (hxa : x < a) :
    RAlt ν ⊢ Semiformula.univCl (∼((tiMuR κ)/[(numAtR (gamma0Code a) : Semiterm LRA ℕ 0)]) ⋎
      (tiMuR κ)/[(numAtR (gamma0Code x) : Semiterm LRA ℕ 0)]) := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos (lt_of_le_of_lt (Gamma0Note.zero_le_note κ) hκ)
  refine provable_of_eqModels hν ?_ ?_
  · rw [lvlOf_emb_univCl, lvlOf_or, lvlOf_neg, lvlOf_subst₁, lvlOf_subst₁, max_self]
    exact lt_of_le_of_lt (lvlOf_tiMuR_le κ) hκ
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f (∼((tiMuR κ)/[(numAtR (gamma0Code a) :
      Semiterm LRA ℕ 0)]) ⋎ (tiMuR κ)/[(numAtR (gamma0Code x) : Semiterm LRA ℕ 0)])
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, eval_tiMuR_subst,
      eval_tiMuR_subst, val_numAtR_model, val_numAtR_model]
    by_cases h : TImu κ (numVal N (gamma0Code a))
    · exact Or.inr (TImu_down hN hν (precM_code hN hν hxa) h)
    · exact Or.inl h

/-- **Instantiation**: `RAlt ν ⊢ TI_μ(t) → TI(≺₁, t, F)` for every closed
formula `F` of level `< μ`, every term `t`, and `μ < ν`. -/
theorem tiInst_provable {ν μ : Lv} (hμ : μ < ν) {F : Semiformula LRA ℕ 1} (hF : lvlOf F < μ)
    (hcl : F.freeVariables = ∅) (t : Semiterm LRA ℕ 0) :
    RAlt ν ⊢ Semiformula.univCl (∼((tiMuR μ)/[t]) ⋎ tiUpR F t) := by
  have hν : 1 ≤ ν := Gamma0Note.one_le_of_pos
    (lt_of_le_of_lt (Gamma0Note.zero_le_note _) (lt_trans hF hμ))
  refine provable_of_eqModels hν ?_ ?_
  · rw [lvlOf_emb_univCl, lvlOf_or, lvlOf_neg, lvlOf_subst₁, lvlOf_tiUpR]
    exact max_lt (lt_of_le_of_lt (lvlOf_tiMuR_le μ) hμ) (lt_trans hF hμ)
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f (∼((tiMuR μ)/[t]) ⋎ tiUpR F t)
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, eval_tiMuR_subst,
      eval_tiUpR]
    by_cases h : TImu μ (Semiterm.val (s := sN) ![] f t)
    · exact Or.inr (TImu_inst hN hμ hF hcl f h)
    · exact Or.inl h

/-! ### Downward closure of the segment sentences -/

/-- The body of `tiUptoSegR b a`. -/
noncomputable def tiUptoSegBody (b a : Gamma0Note) : Proposition LRA :=
  ∼(Prog (precBelowR b)) ⋎
    (∀¹ (∼(precAt (precBelowR b) (#0 : Semiterm LRA ℕ 1) (numAtR (gamma0Code a))) ⋎
      Xat (#0 : Semiterm LRA ℕ 1)))

theorem tiUptoSegR_eq (b a : Gamma0Note) :
    tiUptoSegR b a = Semiformula.univCl (tiUptoSegBody b a) := rfl

theorem lvlOf_tiUptoSegBody (b a : Gamma0Note) : lvlOf (tiUptoSegBody b a) = 0 := by
  simp [tiUptoSegBody, Prog, below, precAt, precBelowR, precCode₁R, lvlOf_lMap_toLRA]

section SegModel

variable {M : Type} [Nonempty M] [s : Structure LRA M] [Structure.Eq LRA M] {ν : Lv}

/-- The downward step for the segment sentences, in a model. -/
theorem segBody_down (hM : M↓[LRA] ⊧* RAlt ν) (hν : 1 ≤ ν) {b a a' : Gamma0Note}
    (ha' : a' < a) (hab : a < b) (f : ℕ → M)
    (h : Semiformula.Eval (s := s) ![] f (tiUptoSegBody b a)) :
    Semiformula.Eval (s := s) ![] f (tiUptoSegBody b a') := by
  rw [tiUptoSegBody, eval_tiUptoSegR_body] at h ⊢
  intro hprog y hy
  have hya : precM y (numVal M (gamma0Code a)) :=
    precM_trans hM hν hy.1 (precM_code hM hν ha')
  exact h hprog y ⟨hya, precM_code hM hν hab⟩

end SegModel

/-- **Downward closure of the segment sentences**, internally:
`RAlt ν ⊢ TI(≺_b, ā, X) → TI(≺_b, ā', X)` for `a' < a < b`, `1 ≤ ν`. -/
theorem tiUptoSegR_downward_provable {ν : Lv} (hν : 1 ≤ ν) {b a a' : Gamma0Note}
    (ha' : a' < a) (hab : a < b) :
    RAlt ν ⊢ Semiformula.univCl (∼(tiUptoSegBody b a) ⋎ tiUptoSegBody b a') := by
  refine provable_of_eqModels hν ?_ ?_
  · rw [lvlOf_emb_univCl, lvlOf_or, lvlOf_neg, lvlOf_tiUptoSegBody, lvlOf_tiUptoSegBody,
      max_self]
    exact lt_of_lt_of_le Gamma0Note.zero_lt_one hν
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro f
    show Semiformula.Eval (s := sN) ![] f (∼(tiUptoSegBody b a) ⋎ tiUptoSegBody b a')
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg]
    by_cases h : Semiformula.Eval (s := sN) ![] f (tiUptoSegBody b a)
    · exact Or.inr (segBody_down hN hν ha' hab f h)
    · exact Or.inl h

/-- **Downward closure of the segment sentences**, externally: if `RAlt ν`
proves transfinite induction along `≺_b` up to `a < b`, it proves it up to every
`a' < a`. -/
theorem tiUptoSegR_downward {ν : Lv} (hν : 1 ≤ ν) {b a a' : Gamma0Note} (ha' : a' < a)
    (hab : a < b) (h : RAlt ν ⊢ tiUptoSegR b a) : RAlt ν ⊢ tiUptoSegR b a' := by
  refine provable_of_eqModels hν ?_ ?_
  · rw [tiUptoSegR_eq, lvlOf_emb_univCl, lvlOf_tiUptoSegBody]
    exact lt_of_lt_of_le Gamma0Note.zero_lt_one hν
  · intro N _ sN _ hN
    have H : N↓[LRA] ⊧ tiUptoSegR b a :=
      consequence_iff.mp (Theory.Proof.sound h) N hN
    rw [tiUptoSegR_eq, models_iff_proposition] at H ⊢
    intro f
    exact segBody_down hN hν ha' hab f (H f)

end Ramified

end OrdinalAnalysis
