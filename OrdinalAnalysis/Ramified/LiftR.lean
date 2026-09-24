/-
  Lifting `PA[X]` into the level-guarded ramified theories, and the passage from
  models with equality to provability in `RA_{<ν}`.

  Two facts, both semantic, through Foundation's completeness theorem.

  * **Truncation to equality models** (`provable_of_eqModels`).  `RAlt ν`
    contains the equality axioms only for the symbols of level `< ν`, so a
    model of `RAlt ν` need not read `=` as a congruence for `∈̇_κ`, `κ ≥ ν`, and
    cannot in general be collapsed to a model with true equality.  But a
    sentence of level `< ν` does not see those symbols.  Reading every `∈̇_κ`
    with `κ ≥ ν` as the empty relation (`truncStr ν`) changes nothing below
    `ν` (`eval_truncStr`), so the new structure is still a model of `RAlt ν`,
    and it now satisfies every equality axiom of `LRA` (the congruence axioms of
    the emptied symbols are vacuous).  Its quotient by `=` is a model with true
    equality.  Hence: *to prove a sentence of level `< ν` in `RAlt ν` it
    suffices to verify it in every model of `RAlt ν` with true equality.*

  * **Lifting** (`models_paLX_lxStr`, `lift_paLX_R`).  In a model `M` of
    `RAlt ν` with true equality, let `P` be a predicate defined by a formula
    `B` of level `< ν` (with parameters).  The `LX`-structure `lxStr P` —
    the arithmetic of `M`, with `X` read as `P` — is a model of `PA[X]`:
    equality is true equality, `PA⁻` is the arithmetic part of `RAlt ν`, and
    the induction axiom of an `LX`-formula `φ` is the `RAlt ν` induction axiom
    of `substXB B φ`, the formula `φ` with every atom `X t` replaced by
    `B(t)`, whose level is at most that of `B`.  The substitution keeps the
    free variables of `φ` and of `B` apart by sending those of `φ` to even and
    those of `B` to odd indices, so that one assignment of `M` evaluates both
    (`eval_substXB`).  Consequently every theorem of `PA[X]` holds in `lxStr P`,
    and in particular every theorem of `PA[X]` becomes a theorem of `RAlt ν`
    after replacing `X t` by `t ∈̇_μ z`, for a level `μ < ν` and a parameter
    `z` (`lift_paLX_R`).

  The same evaluation is proved for `Comprehension.lean`'s `xMem μ`
  (`eval_xMem`), the form in which the jump formula `jumpR μ` is written.
-/
import OrdinalAnalysis.Ramified.Comprehension
import OrdinalAnalysis.Ramified.AxiomsLogic

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### The levels of the equality axioms -/

/-- A formula without fresh symbols is levelless. -/
theorem lvlOf_eq_zero_of_rFree {n : ℕ} {φ : Semiformula LRA ℕ n} (h : RFree φ) :
    lvlOf φ = 0 := by
  induction φ using Semiformula.rec' with
  | hverum => exact lvlOf_verum
  | hfalsum => exact lvlOf_falsum
  | hrel r v => obtain ⟨r', rfl⟩ := h; rw [lvlOf_def]; rfl
  | hnrel r v => obtain ⟨r', rfl⟩ := h; rw [lvlOf_def]; rfl
  | hand φ ψ ihφ ihψ => simp [ihφ h.1, ihψ h.2]
  | hor φ ψ ihφ ihψ => simp [ihφ h.1, ihψ h.2]
  | hall φ ih => rw [lvlOf_all]; exact ih h
  | hexs φ ih => rw [lvlOf_exs]; exact ih h

theorem lvlOf_emb_relExtX :
    lvlOf (Rewriting.emb (Theory.Eq.relExt (Sum.inr RARel.X : LRA.Rel 1)) : Proposition LRA) = 0 := by
  rw [emb_relExtX]
  simp [relX2, eqA, XAG]
  refine le_antisymm (max_le ?_ (max_le ?_ ?_)) (Gamma0Note.zero_le_note _) <;>
    exact le_of_eq (by first | rfl | (rw [lvlOf_def]; rfl))

theorem lvlOf_emb_memExt (κ : Lv) :
    lvlOf (Rewriting.emb (Theory.Eq.relExt (Sum.inr (RARel.mem κ) : LRA.Rel 2)) : Proposition LRA)
      = κ := by
  rw [emb_memExt]
  simp [memX4, eqA, memAtG]
  have h1 : (relLevel (Language.Eq.eq : LRA.Rel 2)).getD 0 = 0 := rfl
  have h2 : ∀ (v : Fin 2 → Semiterm LRA ℕ 4),
      lvlOf (Semiformula.rel (Sum.inr (RARel.mem κ) : LRA.Rel 2) v) = κ := fun _ => by rw [lvlOf_def]; rfl
  rw [h1, h2, h2]
  simp

/-! ### Truncation above a level -/

section Trunc

variable {M : Type} [s : Structure LRA M]

set_option warn.classDefReducibility false in
/-- `M` with every `∈̇_κ`, `κ ≥ ν`, read as the empty relation. -/
def truncStr (ν : Lv) : Structure LRA M where
  func := fun {_} f v => s.func f v
  rel := fun {k} r v => match k, r with
    | _, Sum.inl r => s.rel (Sum.inl r) v
    | _, Sum.inr RARel.X => s.rel (Sum.inr RARel.X) v
    | _, Sum.inr (RARel.mem κ) => κ < ν ∧ s.rel (Sum.inr (RARel.mem κ)) v

theorem val_truncStr (ν : Lv) {ξ : Type*} {n : ℕ} (e : Fin n → M) (f : ξ → M)
    (t : Semiterm LRA ξ n) :
    Semiterm.val (s := truncStr ν) e f t = Semiterm.val (s := s) e f t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func F v ih =>
    simp only [Semiterm.val_func]
    exact congrArg _ (funext fun i => ih i)

/-- **The truncation does not see formulas of level `< ν`.** -/
theorem eval_truncStr (ν : Lv) {n : ℕ} (φ : Semiformula LRA ℕ n) (hφ : lvlOf φ < ν)
    (e : Fin n → M) (f : ℕ → M) :
    Semiformula.Eval (s := truncStr ν) e f φ ↔ Semiformula.Eval (s := s) e f φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v =>
    rcases r with r | r
    · show s.rel (Sum.inl r) (fun i => Semiterm.val (s := truncStr ν) e f (v i)) ↔
        s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e f (v i))
      simp only [val_truncStr]
    · cases r with
      | X =>
        show s.rel (Sum.inr RARel.X) (fun i => Semiterm.val (s := truncStr ν) e f (v i)) ↔
          s.rel (Sum.inr RARel.X) (fun i => Semiterm.val (s := s) e f (v i))
        simp only [val_truncStr]
      | mem κ =>
        have hκ : κ < ν := by have h := hφ; rw [lvlOf_def] at h; exact h
        show (κ < ν ∧ s.rel (Sum.inr (RARel.mem κ))
            (fun i => Semiterm.val (s := truncStr ν) e f (v i))) ↔
          s.rel (Sum.inr (RARel.mem κ)) (fun i => Semiterm.val (s := s) e f (v i))
        simp only [val_truncStr, hκ, true_and]
  | hnrel r v =>
    rcases r with r | r
    · show ¬s.rel (Sum.inl r) (fun i => Semiterm.val (s := truncStr ν) e f (v i)) ↔
        ¬s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e f (v i))
      simp only [val_truncStr]
    · cases r with
      | X =>
        show ¬s.rel (Sum.inr RARel.X) (fun i => Semiterm.val (s := truncStr ν) e f (v i)) ↔
          ¬s.rel (Sum.inr RARel.X) (fun i => Semiterm.val (s := s) e f (v i))
        simp only [val_truncStr]
      | mem κ =>
        have hκ : κ < ν := by have h := hφ; rw [lvlOf_def] at h; exact h
        show ¬(κ < ν ∧ s.rel (Sum.inr (RARel.mem κ))
            (fun i => Semiterm.val (s := truncStr ν) e f (v i))) ↔
          ¬s.rel (Sum.inr (RARel.mem κ)) (fun i => Semiterm.val (s := s) e f (v i))
        simp only [val_truncStr, hκ, true_and]
  | hand φ ψ ihφ ihψ =>
    rw [lvlOf_and] at hφ
    have h1 : lvlOf φ < ν := lt_of_le_of_lt (le_max_left _ _) hφ
    have h2 : lvlOf ψ < ν := lt_of_le_of_lt (le_max_right _ _) hφ
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and, ihφ h1 e,
      ihψ h2 e]
  | hor φ ψ ihφ ihψ =>
    rw [lvlOf_or] at hφ
    have h1 : lvlOf φ < ν := lt_of_le_of_lt (le_max_left _ _) hφ
    have h2 : lvlOf ψ < ν := lt_of_le_of_lt (le_max_right _ _) hφ
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or, ihφ h1 e,
      ihψ h2 e]
  | hall φ ih =>
    rw [lvlOf_all] at hφ
    rw [Semiformula.eval_all, Semiformula.eval_all]
    exact forall_congr' fun x => ih hφ (x :> e)
  | hexs φ ih =>
    rw [lvlOf_exs] at hφ
    rw [Semiformula.eval_ex, Semiformula.eval_ex]
    exact exists_congr fun x => ih hφ (x :> e)

/-- The sentence form. -/
theorem models_truncStr_iff [Nonempty M] (ν : Lv) {σ : Sentence LRA}
    (hσ : lvlOf (Rewriting.emb σ : Proposition LRA) < ν) :
    (truncStr (M := M) ν).toStruc ⊧ σ ↔ M↓[LRA] ⊧ σ := by
  have f : ℕ → M := fun _ => Classical.arbitrary M
  rw [models_iff (s := truncStr ν), models_iff]
  have h1 := Semiformula.eval_emb (s := truncStr ν) (b := ![]) (f := f) σ
  have h2 := Semiformula.eval_emb (s := s) (b := ![]) (f := f) σ
  exact h1.symm.trans ((eval_truncStr ν _ hσ ![] f).trans h2)

/-- **The truncation is a model of `RAlt ν` with all of `𝗘𝗤 LRA`.** -/
theorem truncStr_models [Nonempty M] {ν : Lv} (hν : 1 ≤ ν) (hM : M↓[LRA] ⊧* RAlt ν) :
    (truncStr (M := M) ν).toStruc ⊧* (RAlt ν ∪ 𝗘𝗤 LRA) := by
  have key : ∀ σ : Sentence LRA, σ ∈ RAlt ν → (truncStr (M := M) ν).toStruc ⊧ σ := fun σ hσ =>
    (models_truncStr_iff ν (lvlOf_emb_lt_of_mem_RAlt hν hσ)).mpr
      (Semantics.modelsSet_iff.mp hM hσ)
  have keyEq : ∀ σ : Sentence LRA, σ ∈ 𝗘𝗤 LRA →
      lvlOf (Rewriting.emb σ : Proposition LRA) < ν → (truncStr (M := M) ν).toStruc ⊧ σ :=
    fun σ hσ hl => key σ (mem_RAlt_of_eq hσ hl)
  have hzero : ∀ σ : Sentence LRA, σ ∈ 𝗘𝗤 LRA → RFree σ →
      (truncStr (M := M) ν).toStruc ⊧ σ := fun σ hσ hR =>
    keyEq σ hσ (by rw [lvlOf_eq_zero_of_rFree (rFree_emb hR)]; exact lt_of_lt_of_le Gamma0Note.zero_lt_one hν)
  refine Semantics.modelsSet_iff.mpr ?_
  rintro σ (hσ | hσ)
  · exact key σ hσ
  · cases hσ with
    | refl => exact hzero _ Theory.eqAxiom.refl rFree_eqRefl
    | symm => exact hzero _ Theory.eqAxiom.symm rFree_eqSymm
    | trans => exact hzero _ Theory.eqAxiom.trans rFree_eqTrans
    | funcExt f => exact hzero _ (Theory.eqAxiom.funcExt f) (rFree_funcExt f)
    | relExt r =>
      rcases r with r | r
      · exact hzero _ (Theory.eqAxiom.relExt _) (rFree_relExt_inl r)
      · cases r with
        | X =>
          exact keyEq _ (Theory.eqAxiom.relExt _) (by rw [lvlOf_emb_relExtX]; exact lt_of_lt_of_le Gamma0Note.zero_lt_one hν)
        | mem κ =>
          by_cases hκ : κ < ν
          · exact keyEq _ (Theory.eqAxiom.relExt _) (by rw [lvlOf_emb_memExt]; exact hκ)
          · have f : ℕ → M := fun _ => Classical.arbitrary M
            rw [models_iff (s := truncStr ν)]
            refine (Semiformula.eval_emb (s := truncStr ν) (b := ![]) (f := f) _).mp ?_
            rw [emb_memExt]
            simp only [Semiformula.eval_all]
            intro a b c d
            simp only [memX4, LogicalConnective.HomClass.map_or]
            refine Or.inr (Or.inl ?_)
            show ¬(κ < ν ∧ _)
            exact fun h => hκ h.1

end Trunc

/-- **Provability from truth in the models with equality.**  A sentence of level
`< ν` true in every model of `RAlt ν` whose equality is true equality is a
theorem of `RAlt ν`. -/
theorem provable_of_eqModels {ν : Lv} (hν : 1 ≤ ν) {σ : Sentence LRA}
    (hσ : lvlOf (Rewriting.emb σ : Proposition LRA) < ν)
    (H : ∀ (N : Type) [Nonempty N] [Structure LRA N] [Structure.Eq LRA N],
      N↓[LRA] ⊧* RAlt ν → N↓[LRA] ⊧ σ) :
    RAlt ν ⊢ σ := by
  apply Theory.Proof.complete.{0, 0}
  have : 𝗘𝗤 LRA ⪯ RAlt ν ∪ 𝗘𝗤 LRA := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have hT' : (RAlt ν ∪ 𝗘𝗤 LRA) ⊨[Struc.{0, 0} LRA] σ := by
    rw [consequence_iff_eq]
    intro N _ _ _ hN
    exact H N (Semantics.ModelsSet.of_subset hN Set.subset_union_left)
  rw [consequence_iff]
  intro M _ s hM
  have hTr := truncStr_models (M := M) hν hM
  have hc := consequence_iff.mp hT'
  have h1 : (truncStr (M := M) ν).toStruc ⊧ σ := @hc M _ (truncStr ν) hTr
  exact (models_truncStr_iff ν hσ).mp h1

/-! ### Reading `X` as a predicate of a model -/

section Lift

variable {M : Type} [s : Structure LRA M]

set_option warn.classDefReducibility false in
/-- The `LX`-structure on a model of `LRA`: the same arithmetic, `X` read as `P`. -/
def lxStr (P : M → Prop) : Structure Gentzen.LX M where
  func := fun {_} f v => s.func (lxToLRA.func f) v
  rel := fun {k} r v => match k, r with
    | _, Sum.inl r => s.rel (Sum.inl r) v
    | _, Sum.inr Gentzen.XRel.X => P (v 0)

theorem val_lxStr (P : M → Prop) {ξ : Type*} {n : ℕ} (e : Fin n → M) (f : ξ → M)
    (t : Semiterm Gentzen.LX ξ n) :
    Semiterm.val (s := lxStr P) e f t = Semiterm.val (s := s) e f (Semiterm.lMap lxToLRA t) := by
  rw [Semiterm.val_lMap]
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func F v ih =>
    simp only [Semiterm.val_func]
    exact congrArg _ (funext fun i => ih i)

def trmX {n : ℕ} (t : Semiterm Gentzen.LX ℕ n) : Semiterm LRA ℕ n :=
  Rew.rewriteMap (fun k => 2 * k) (Semiterm.lMap lxToLRA t)

def instB {n : ℕ} (B : Semiformula LRA ℕ 1) (t : Semiterm LRA ℕ n) : Semiformula LRA ℕ n :=
  Rew.bind ![t] (fun k => &(2 * k + 1)) ▹ B

def substXB (B : Semiformula LRA ℕ 1) : {n : ℕ} → Semiformula Gentzen.LX ℕ n → Semiformula LRA ℕ n
  | _, .verum => ⊤
  | _, .falsum => ⊥
  | _, .rel (Sum.inl r) v => .rel (Sum.inl r) fun i => trmX (v i)
  | _, .rel (Sum.inr Gentzen.XRel.X) v => instB B (trmX (v 0))
  | _, .nrel (Sum.inl r) v => .nrel (Sum.inl r) fun i => trmX (v i)
  | _, .nrel (Sum.inr Gentzen.XRel.X) v => ∼(instB B (trmX (v 0)))
  | _, .and φ ψ => substXB B φ ⋏ substXB B ψ
  | _, .or φ ψ => substXB B φ ⋎ substXB B ψ
  | _, .all φ => ∀¹ substXB B φ
  | _, .exs φ => ∃¹ substXB B φ

theorem val_trmX (P : M → Prop) (h : ℕ → M) {n : ℕ} (e : Fin n → M) (t : Semiterm Gentzen.LX ℕ n) :
    Semiterm.val (s := s) e h (trmX t) = Semiterm.val (s := lxStr P) e (fun k => h (2 * k)) t := by
  rw [trmX, Semiterm.val_rewriteMap, val_lxStr]
  rfl

theorem eval_instB (B : Semiformula LRA ℕ 1) (h : ℕ → M) {n : ℕ} (e : Fin n → M)
    (t : Semiterm LRA ℕ n) :
    Semiformula.Eval (s := s) e h (instB B t) ↔
      Semiformula.Eval (s := s) ![Semiterm.val (s := s) e h t] (fun k => h (2 * k + 1)) B := by
  rw [instB, Semiformula.eval_rew]
  have hb : (Semiterm.val (s := s) e h ∘ ⇑(Rew.bind ![t] fun k => &(2 * k + 1)) ∘
      Semiterm.bvar) = ![Semiterm.val (s := s) e h t] := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  have hf : (Semiterm.val (s := s) e h ∘ ⇑(Rew.bind ![t] fun k => &(2 * k + 1)) ∘
      Semiterm.fvar) = fun k => h (2 * k + 1) := rfl
  rw [hb, hf]

theorem eval_substXB (B : Semiformula LRA ℕ 1) (h : ℕ → M) (P : M → Prop)
    (hP : ∀ x, P x ↔ Semiformula.Eval (s := s) ![x] (fun k => h (2 * k + 1)) B)
    {n : ℕ} (φ : Semiformula Gentzen.LX ℕ n) (e : Fin n → M) :
      Semiformula.Eval (s := s) e h (substXB B φ) ↔
        Semiformula.Eval (s := lxStr P) e (fun k => h (2 * k)) φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v =>
    rcases r with r | r
    · show s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e h (trmX (v i))) ↔
        s.rel (Sum.inl r) (fun i => Semiterm.val (s := lxStr P) e (fun k => h (2 * k)) (v i))
      simp only [val_trmX P]
    · cases r
      show Semiformula.Eval (s := s) e h (instB B (trmX (v 0))) ↔
        P (Semiterm.val (s := lxStr P) e (fun k => h (2 * k)) (v 0))
      rw [eval_instB, val_trmX P]
      exact (hP _).symm
  | hnrel r v =>
    rcases r with r | r
    · show ¬s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e h (trmX (v i))) ↔
        ¬s.rel (Sum.inl r) (fun i => Semiterm.val (s := lxStr P) e (fun k => h (2 * k)) (v i))
      simp only [val_trmX P]
    · cases r
      show Semiformula.Eval (s := s) e h (∼(instB B (trmX (v 0)))) ↔
        ¬P (Semiterm.val (s := lxStr P) e (fun k => h (2 * k)) (v 0))
      rw [LogicalConnective.HomClass.map_neg, eval_instB, val_trmX P]
      exact not_congr (hP _).symm
  | hand φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := s) e h (substXB B φ ⋏ substXB B ψ) ↔ _
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := s) e h (substXB B φ ⋎ substXB B ψ) ↔ _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or, ihφ, ihψ]
  | hall φ ih =>
    show Semiformula.Eval (s := s) e h (∀¹ substXB B φ) ↔ _
    rw [Semiformula.eval_all, Semiformula.eval_all]
    exact forall_congr' fun x => ih (x :> e)
  | hexs φ ih =>
    show Semiformula.Eval (s := s) e h (∃¹ substXB B φ) ↔ _
    rw [Semiformula.eval_ex, Semiformula.eval_ex]
    exact exists_congr fun x => ih (x :> e)


theorem eval_succInd_iff {L : Language} [L.ORing] {N : Type} [Structure L N]
    (φ : Semiformula L ℕ 1) (f : ℕ → N) :
    Semiformula.Eval ![] f (succInd φ) ↔
      (Semiformula.Eval ![Semiterm.val ![] f ((0 : ℕ) : Semiterm L ℕ 0)] f φ →
        (∀ x, Semiformula.Eval ![x] f φ →
          Semiformula.Eval ![Semiterm.val ![x] f (‘(#0 + 1)’ : Semiterm L ℕ 1)] f φ) →
        ∀ x, Semiformula.Eval ![x] f φ) := by
  show Semiformula.Eval ![] f ((φ/[((0 : ℕ) : Semiterm L ℕ 0)]) 🡒
      (∀¹ (φ/[(#0 : Semiterm L ℕ 1)] 🡒 φ/[(‘(#0 + 1)’ : Semiterm L ℕ 1)])) 🡒
      ∀¹ (φ/[(#0 : Semiterm L ℕ 1)])) ↔ _
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_all, Semiformula.eval_substs]
  simp [Matrix.empty_eq]

theorem lMap_zero_LX :
    Semiterm.lMap lxToLRA ((0 : ℕ) : Semiterm Gentzen.LX ℕ 0) = ((0 : ℕ) : Semiterm LRA ℕ 0) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, lxToLRA]
  rfl

theorem lMap_succ_LX :
    Semiterm.lMap lxToLRA (‘(#0 + 1)’ : Semiterm Gentzen.LX ℕ 1) = (‘(#0 + 1)’ : Semiterm LRA ℕ 1) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, Semiterm.Operator.Add.term_eq, lxToLRA]
  congr 1
  funext i
  fin_cases i
  · rfl
  · simp [Function.comp_def, Matrix.empty_eq]
    rfl


/-- `lxStr P` has true equality when `M` has. -/
theorem lxStr_eq (P : M → Prop) [Structure.Eq LRA M] :
    letI := lxStr P; Structure.Eq Gentzen.LX M :=
  letI := lxStr P
  ⟨fun a b => Structure.Eq.eq (L := LRA) a b⟩

/-- Interleaving two assignments: even indices from `g`, odd ones from `f`. -/
def interleave (g f : ℕ → M) : ℕ → M := fun k => if k % 2 = 0 then g (k / 2) else f (k / 2)

omit s in
@[simp] theorem interleave_even (g f : ℕ → M) (k : ℕ) : interleave g f (2 * k) = g k := by
  simp [interleave]

omit s in
@[simp] theorem interleave_odd (g f : ℕ → M) (k : ℕ) : interleave g f (2 * k + 1) = f k := by
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [interleave, h1, h2]

/-- **`substXB B` in a model**, with the two assignments interleaved. -/
theorem eval_substXB_interleave (B : Semiformula LRA ℕ 1) (g fB : ℕ → M) (P : M → Prop)
    (hP : ∀ x, P x ↔ Semiformula.Eval (s := s) ![x] fB B)
    {n : ℕ} (φ : Semiformula Gentzen.LX ℕ n) (e : Fin n → M) :
    Semiformula.Eval (s := s) e (interleave g fB) (substXB B φ) ↔
      Semiformula.Eval (s := lxStr P) e g φ := by
  have h := eval_substXB B (interleave g fB) P (fun x => by
    rw [hP x]
    have hf : (fun k => interleave g fB (2 * k + 1)) = fB := funext fun k => interleave_odd g fB k
    rw [hf]) φ e
  have hg : (fun k => interleave g fB (2 * k)) = g := funext fun k => interleave_even g fB k
  rw [hg] at h
  exact h

/-- The level of `substXB B φ` is at most that of `B`. -/
theorem lvlOf_substXB_le (B : Semiformula LRA ℕ 1) {n : ℕ} (φ : Semiformula Gentzen.LX ℕ n) :
    lvlOf (substXB B φ) ≤ lvlOf B := by
  induction φ using Semiformula.rec' with
  | hverum => exact Eq.trans_le (by rw [lvlOf_def]; rfl) (Gamma0Note.zero_le_note _)
  | hfalsum => exact Eq.trans_le (by rw [lvlOf_def]; rfl) (Gamma0Note.zero_le_note _)
  | hrel r v =>
    rcases r with r | r
    · exact Eq.trans_le (by rw [lvlOf_def]; rfl) (Gamma0Note.zero_le_note _)
    · cases r
      show lvlOf (instB B _) ≤ lvlOf B
      rw [instB, lvlOf_rew]
  | hnrel r v =>
    rcases r with r | r
    · exact Eq.trans_le (by rw [lvlOf_def]; rfl) (Gamma0Note.zero_le_note _)
    · cases r
      show lvlOf (∼(instB B _)) ≤ lvlOf B
      rw [lvlOf_neg, instB, lvlOf_rew]
  | hand φ ψ ihφ ihψ =>
    show lvlOf (substXB B φ ⋏ substXB B ψ) ≤ lvlOf B
    rw [lvlOf_and]; exact max_le ihφ ihψ
  | hor φ ψ ihφ ihψ =>
    show lvlOf (substXB B φ ⋎ substXB B ψ) ≤ lvlOf B
    rw [lvlOf_or]; exact max_le ihφ ihψ
  | hall φ ih => show lvlOf (∀¹ substXB B φ) ≤ lvlOf B; rw [lvlOf_all]; exact ih
  | hexs φ ih => show lvlOf (∃¹ substXB B φ) ≤ lvlOf B; rw [lvlOf_exs]; exact ih

/-- **`lxStr P` is a model of `PA[X]`** for every `P` defined, with parameters, by
a formula of level `< ν` in a model of `RAlt ν` with true equality. -/
theorem models_paLX_lxStr [Nonempty M] [Structure.Eq LRA M] {ν : Lv}
    (hM : M↓[LRA] ⊧* RAlt ν) (B : Semiformula LRA ℕ 1) (hB : lvlOf B < ν) (fB : ℕ → M)
    (P : M → Prop) (hP : ∀ x, P x ↔ Semiformula.Eval (s := s) ![x] fB B) :
    letI := lxStr P; M↓[Gentzen.LX] ⊧* Gentzen.paLX := by
  let _ : Structure Gentzen.LX M := lxStr P
  have _ : Structure.Eq Gentzen.LX M := lxStr_eq P
  refine Semantics.modelsSet_iff.mpr ?_
  rintro σ (hσ | hσ | hσ)
  · exact Theory.models M (𝗘𝗤 Gentzen.LX) hσ
  · obtain ⟨τ, hτ, rfl⟩ := hσ
    refine Semiformula.models_lMap.mpr ?_
    exact Semantics.modelsSet_iff.mp
      (reduct_models_peanoMinus (fun _ h => mem_RAlt_of_peanoMinus h) hM) hτ
  · obtain ⟨φ, -, rfl⟩ := hσ
    have hax : M↓[LRA] ⊧ Semiformula.univCl (succInd (substXB B φ)) :=
      Semantics.modelsSet_iff.mp hM
        (induction_mem_RAlt _ (lt_of_le_of_lt (lvlOf_substXB_le B φ) hB))
    rw [models_iff_proposition] at hax ⊢
    intro g
    have hg := hax (interleave g fB)
    simp only [Semiformula.Evalf] at hg ⊢
    rw [eval_succInd_iff] at hg ⊢
    simp only [eval_substXB_interleave B g fB P hP] at hg
    have h0 : Semiterm.val (s := s) ![] (interleave g fB) ((0 : ℕ) : Semiterm LRA ℕ 0) =
        Semiterm.val (s := lxStr P) ![] g ((0 : ℕ) : Semiterm Gentzen.LX ℕ 0) := by
      rw [val_lxStr, lMap_zero_LX]
      simp [Semiterm.val_operator]
    have h1 : ∀ x : M, Semiterm.val (s := s) ![x] (interleave g fB)
          (‘(#0 + 1)’ : Semiterm LRA ℕ 1) =
        Semiterm.val (s := lxStr P) ![x] g (‘(#0 + 1)’ : Semiterm Gentzen.LX ℕ 1) := by
      intro x
      rw [val_lxStr, lMap_succ_LX]
      simp [Semiterm.val_operator]
    simp only [h0, h1] at hg
    exact hg

/-- **Every theorem of `PA[X]` holds in `lxStr P`.** -/
theorem models_of_paLX [Nonempty M] [Structure.Eq LRA M] {ν : Lv}
    (hM : M↓[LRA] ⊧* RAlt ν) (B : Semiformula LRA ℕ 1) (hB : lvlOf B < ν) (fB : ℕ → M)
    (P : M → Prop) (hP : ∀ x, P x ↔ Semiformula.Eval (s := s) ![x] fB B)
    {σ : Sentence Gentzen.LX} (h : Gentzen.paLX ⊢ σ) :
    letI := lxStr P; M↓[Gentzen.LX] ⊧ σ := by
  let _ : Structure Gentzen.LX M := lxStr P
  have _ := models_paLX_lxStr hM B hB fB P hP
  exact consequence_iff'.mp (Theory.Proof.sound h) M

/-- **`xMem μ` in a model**: the atom `X t` becomes membership in the set named
by the value of the free variable `&0`. -/
theorem eval_xMem (μ : Lv) {n : ℕ} (φ : Semiformula Gentzen.LX ℕ n) (e : Fin n → M) (f : ℕ → M) :
    Semiformula.Eval (s := s) e f (xMem μ φ) ↔
      Semiformula.Eval (s := lxStr (fun x => memM μ x (f 0))) e f φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v =>
    rcases r with r | r
    · show s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e f (Semiterm.lMap lxToLRA (v i))) ↔
        s.rel (Sum.inl r) (fun i => Semiterm.val (s := lxStr _) e f (v i))
      simp only [val_lxStr]
    · cases r
      show Semiformula.Eval (s := s) e f (memAt μ (Semiterm.lMap lxToLRA (v 0)) &0) ↔
        memM μ (Semiterm.val (s := lxStr _) e f (v 0)) (f 0)
      rw [eval_memAt, val_lxStr]
      rfl
  | hnrel r v =>
    rcases r with r | r
    · show ¬s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e f (Semiterm.lMap lxToLRA (v i))) ↔
        ¬s.rel (Sum.inl r) (fun i => Semiterm.val (s := lxStr _) e f (v i))
      simp only [val_lxStr]
    · cases r
      show Semiformula.Eval (s := s) e f (nmemAt μ (Semiterm.lMap lxToLRA (v 0)) &0) ↔
        ¬memM μ (Semiterm.val (s := lxStr _) e f (v 0)) (f 0)
      rw [eval_nmemAt, val_lxStr]
      rfl
  | hand φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := s) e f (xMem μ φ ⋏ xMem μ ψ) ↔ _
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := s) e f (xMem μ φ ⋎ xMem μ ψ) ↔ _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or, ihφ, ihψ]
  | hall φ ih =>
    show Semiformula.Eval (s := s) e f (∀¹ xMem μ φ) ↔ _
    rw [Semiformula.eval_all, Semiformula.eval_all]
    exact forall_congr' fun x => ih (x :> e)
  | hexs φ ih =>
    show Semiformula.Eval (s := s) e f (∃¹ xMem μ φ) ↔ _
    rw [Semiformula.eval_ex, Semiformula.eval_ex]
    exact exists_congr fun x => ih (x :> e)

/-- The level of `xMem μ φ` is at most `μ`. -/
theorem lvlOf_xMem_le (μ : Lv) {n : ℕ} (φ : Semiformula Gentzen.LX ℕ n) : lvlOf (xMem μ φ) ≤ μ :=
  lvlOf_le_of_shape (shape_xMem μ φ)

end Lift

/-! ### The lifting of `PA[X]` at a level-`μ` set -/

/-- **`X t ↦ t ∈̇_μ z`**, the parameter `z` being the free variable `&1` (the
free variables of the `LX`-formula are moved to even indices). -/
def substMem (μ : Lv) {n : ℕ} (φ : Semiformula Gentzen.LX ℕ n) : Semiformula LRA ℕ n :=
  substXB (memAt μ (#0 : Semiterm LRA ℕ 1) &0) φ

theorem lvlOf_substMem_le (μ : Lv) {n : ℕ} (φ : Semiformula Gentzen.LX ℕ n) :
    lvlOf (substMem μ φ) ≤ μ :=
  (lvlOf_substXB_le _ φ).trans (le_of_eq (lvlOf_memAt _ _ _))

/-- **The lifting of `PA[X]` into `RA_{<ν}` at a level-`μ` set, `μ < ν`.**  Every
theorem `σ` of `PA[X]` becomes, after replacing `X t` by `t ∈̇_μ z` for a free
parameter `z`, a theorem of `RAlt ν` — universally closed, so for every
level-`μ` set `z` at once. -/
theorem lift_paLX_R {ν μ : Lv} (hν : μ < ν) {σ : Sentence Gentzen.LX} (h : Gentzen.paLX ⊢ σ) :
    RAlt ν ⊢ Semiformula.univCl (substMem μ (Rewriting.emb σ : Semiformula Gentzen.LX ℕ 0)) := by
  have hν1 : 1 ≤ ν := Gamma0Note.one_le_of_pos (lt_of_le_of_lt (Gamma0Note.zero_le_note μ) hν)
  refine provable_of_eqModels hν1 ?_ ?_
  · rw [lvlOf_emb_univCl]
    exact lt_of_le_of_lt (lvlOf_substMem_le μ _) hν
  · intro N _ sN _ hN
    rw [models_iff_proposition]
    intro h'
    have hP : ∀ x : N, memM μ x (h' 1) ↔
        Semiformula.Eval (s := sN) ![x] (fun k => h' (2 * k + 1))
          (memAt μ (#0 : Semiterm LRA ℕ 1) &0) := by
      intro x
      rw [eval_memAt]
      rfl
    have hS := models_of_paLX hN (memAt μ (#0 : Semiterm LRA ℕ 1) &0)
      (by rw [lvlOf_memAt]; exact hν) (fun k => h' (2 * k + 1)) _ hP h
    show Semiformula.Eval (s := sN) ![] h' (substMem μ (Rewriting.emb σ))
    rw [substMem, eval_substXB _ h' _ hP]
    exact (Semiformula.eval_emb (s := lxStr _) (b := ![]) (f := fun k => h' (2 * k)) σ).mpr hS

end Ramified

end OrdinalAnalysis
