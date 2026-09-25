/-
  The standard models of `ID A`, built level by level as an iterated least fixed point,
  and its consistency.

  This generalises `ID1/Sound.lean`'s one-predicate construction (`lfpA`, the least
  fixed point of one monotone operator) to a family of predicates `I_k`, `k : ι`,
  fixed in order: level `k`'s operator is monotone in `I_k` alone once the lower levels
  `I_j`, `j < k`, are already fixed (`PositiveIn k (A k)`), and does not look at higher
  levels at all (`LevelBounded k (A k)`), so the family can be built by well-founded
  recursion on `k` (`[WellFoundedLT ι]`; `Fin n` and `ℕ` both qualify) with no
  circularity: `lfpChain P A k` only ever calls itself at strictly smaller `j`.

  **The structure.** `stdIN P S` is the `LXIN ι`-structure on `ℕ` with standard
  arithmetic, `X` read by `P`, and `I_k` read by `S k`, for a full environment
  `S : ι → Set ℕ` — the direct analogue of `ID1.stdI`.

  **Monotonicity, two ways.**

    * `positiveIn_monotone`: if `S`, `S'` agree everywhere except `S k ⊆ S' k`, a
      `PositiveIn k`-formula true in `stdIN P S` is true in `stdIN P S'`. This is
      `ID1.positive_monotone` with the other predicates `I_j`, `j ≠ k`, held fixed
      instead of absent.
    * `levelBounded_agree`: if `S`, `S'` agree at every `j ≤ k`, a `LevelBounded
      k`-formula has the *same* truth value in `stdIN P S` and `stdIN P S'` — it does
      not look far enough to tell them apart. This has no ID₁ analogue (`ID1` has only
      one level, so "higher levels" is vacuous); it is exactly what lets a level's
      fixed point, built against a truncated environment that is `∅` above `k`, be
      recognised as closed against the *real*, untruncated environment once the chain
      is assembled (`eval_closureAxAt`, `eval_indAxAt`).

  **The operator, the fixed point at one level, and the chain.**

    * `opA P A k S := {x | A_k(x) holds in stdIN P S}` — the operator of level `k`,
      as a function of the *whole* environment (only its value at coordinates `≤ k`
      matters, by `LevelBounded`, but it is convenient to let it see all of `S`).
    * `lfpAt P A lower k := sInf {S | opA P A k (update lower k S) ⊆ S}` — the least
      fixed point of level `k`'s operator, with the *other* coordinates held at
      `lower`. Positivity (`opA_mono_at`) makes this a monotone-operator least fixed
      point exactly as in `ID1.lfpA`.
    * `lfpChain P A : ι → Set ℕ`, by well-founded recursion on `<`: `lfpChain P A k :=
      lfpAt P A (fun j => if j < k then lfpChain P A j else ∅) k` (`lfpChain_eq`).

  **Soundness** (`models_ID`): given `FamilyPositive A` and `FamilyLevelBounded A`, for
  every `P`, every axiom of `ID A` is true in `stdIN P (lfpChain P A)`. The closure and
  induction axioms of level `k` both reduce, via `levelBounded_agree`, to the
  corresponding fact about `lfpAt P A (lfpChain P A below k) k` — no transfinite
  induction is needed in this proof itself, only in the construction of `lfpChain`.

  With Foundation's soundness theorem this gives `IDn_consistent`.

  **Slot check.** `slotCheck_two` evaluates the closure and induction axioms of a
  concrete 2-level instance (`I_0` = "is `0`", `I_1` = "is `0` or `I_0`-below-2") on
  ℕ, by `decide`, confirming the axiom of level `k` really binds `x` in `I_k`'s and
  `A_k`'s argument slot and not some other level's — the check
  (`SlotCheck.lean`) ran once for `ID1`, repeated here per
  level.

  Contents.

    `ixStrucN`, `stdIN`                          the standard structures
    `eval_lMap_toLXIN`, `val_stdIN_congr`, `eval_Iat`, `eval_Xat`
    `positiveIn_monotone`, `levelBounded_agree`  the two agreement lemmas
    `eval_substIAt`                              `A_k(F, ·)` reads `I_k` as the set defined by `F`
    `opA`, `opA_mono_at`, `lfpAt`, `lfpAt_subset`, `opA_lfpAt_subset`
    `lfpChain`, `lfpChain_eq`                    **the iterated least fixed point**
    `eval_closureAxAt`, `eval_indAxAt`
    `models_paLXIN`, `models_ID`                 **soundness**
    `IDn_consistent`                             **consistency**
    `slotCheck_two`                              the per-level slot check
-/
import OrdinalAnalysis.IDn.Theory
import Mathlib.Order.FixedPoints
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option warn.classDefReducibility false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

open scoped Classical

variable {ι : Type} [DecidableEq ι]

/-! ### The standard structures -/

/-- The fresh predicates: `X` read by `P`, `I_k` read by `S k`. -/
def ixStrucN (P : ℕ → Prop) (S : ι → Set ℕ) : Structure (IXLangN ι) ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ r v => match r with
    | IXRelN.X => P (v 0)
    | IXRelN.I k => v 0 ∈ S k

/-- **The standard structure of `LXIN ι`**: arithmetic standard, `X` read by `P`, `I_k`
read by `S k`. -/
def stdIN (P : ℕ → Prop) (S : ι → Set ℕ) : Structure (LXIN ι) ℕ :=
  Structure.add ℒₒᵣ (IXLangN ι) ℕ (str₂ := ixStrucN P S)

section Std

variable (P : ℕ → Prop) (S : ι → Set ℕ)

omit [DecidableEq ι] in
/-- The arithmetic reduct of `stdIN P S` is Foundation's standard model of `ℕ`. -/
theorem stdIN_lMap_toLXIN : (stdIN P S).lMap (toLXIN ι) = Arithmetic.standardModel ℕ := rfl

omit [DecidableEq ι] in
/-- An arithmetic formula says in `stdIN P S` what it says in `ℕ`. -/
@[simp] theorem eval_lMap_toLXIN {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) (e : Fin n → ℕ)
    (f : ξ → ℕ) :
    Semiformula.Eval (s := stdIN P S) e f (Semiformula.lMap (toLXIN ι) φ)
      ↔ Semiformula.Eval (M := ℕ) e f φ :=
  Structure.eval_lMap_add₁ (str₂ := ixStrucN P S) φ e f

omit [DecidableEq ι] in
/-- Term values do not depend on the readings of `X` and the `I_k`'s. -/
theorem val_stdIN_congr (Q : ℕ → Prop) (T : ι → Set ℕ) {ξ : Type*} {n : ℕ} (e : Fin n → ℕ)
    (f : ξ → ℕ) (t : Semiterm (LXIN ι) ξ n) :
    Semiterm.val (s := stdIN P S) e f t = Semiterm.val (s := stdIN Q T) e f t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func fn v ih =>
      simp only [Semiterm.val_func, Function.comp_def, ih]
      rcases fn with fn | fn
      · rfl
      · exact PEmpty.elim fn

omit [DecidableEq ι] in
/-- `I_k(t)` holds when the value of `t` lies in `S k`. -/
theorem eval_Iat {ξ : Type*} {n : ℕ} (k : ι) (t : Semiterm (LXIN ι) ξ n) (e : Fin n → ℕ)
    (f : ξ → ℕ) :
    Semiformula.Eval (s := stdIN P S) e f (Iat k t) ↔ Semiterm.val (s := stdIN P S) e f t ∈ S k := by
  have h : (Semiterm.val (s := stdIN P S) e f ∘ ![t] : Fin 1 → ℕ)
      = ![Semiterm.val (s := stdIN P S) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg ((stdIN P S).rel (Sum.inr (IXRelN.I k))) h)

omit [DecidableEq ι] in
/-- `X(t)` holds when `P` holds at the value of `t`. -/
theorem eval_Xat {ξ : Type*} {n : ℕ} (t : Semiterm (LXIN ι) ξ n) (e : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdIN P S) e f (Xat t) ↔ P (Semiterm.val (s := stdIN P S) e f t) := by
  have h : (Semiterm.val (s := stdIN P S) e f ∘ ![t] : Fin 1 → ℕ)
      = ![Semiterm.val (s := stdIN P S) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg ((stdIN P S).rel (Sum.inr IXRelN.X)) h)

end Std

/-! ### Two agreement lemmas -/

omit [DecidableEq ι] in
/-- **A `PositiveIn k`-formula is monotone in `S k` alone**, the other coordinates held
fixed. Generalises `ID1.positive_monotone`. -/
theorem positiveIn_monotone (P : ℕ → Prop) (k : ι) {S S' : ι → Set ℕ} (hle : S k ⊆ S' k)
    (hfix : ∀ j, j ≠ k → S j = S' j) {ξ : Type*} {n : ℕ} (φ : Semiformula (LXIN ι) ξ n)
    (hφ : PositiveIn k φ) (e : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdIN P S) e f φ → Semiformula.Eval (s := stdIN P S') e f φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact id
  | hfalsum => exact id
  | hrel r v =>
    have hv : (fun i => Semiterm.val (s := stdIN P S) e f (v i))
        = (fun i => Semiterm.val (s := stdIN P S') e f (v i)) :=
      funext fun i => val_stdIN_congr P S P S' e f (v i)
    rcases r with r | r
    · show Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdIN P S) e f (v i)) →
        Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdIN P S') e f (v i))
      rw [hv]; exact id
    · cases r with
      | X =>
        show P (Semiterm.val (s := stdIN P S) e f (v 0)) →
          P (Semiterm.val (s := stdIN P S') e f (v 0))
        rw [val_stdIN_congr P S P S']; exact id
      | I j =>
        show Semiterm.val (s := stdIN P S) e f (v 0) ∈ S j →
          Semiterm.val (s := stdIN P S') e f (v 0) ∈ S' j
        rw [val_stdIN_congr P S P S']
        rcases eq_or_ne j k with rfl | hne
        · exact fun h => hle h
        · rw [hfix j hne]; exact id
  | hnrel r v =>
    have hv : (fun i => Semiterm.val (s := stdIN P S) e f (v i))
        = (fun i => Semiterm.val (s := stdIN P S') e f (v i)) :=
      funext fun i => val_stdIN_congr P S P S' e f (v i)
    rcases r with r | r
    · show ¬Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdIN P S) e f (v i)) →
        ¬Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdIN P S') e f (v i))
      rw [hv]; exact id
    · cases r with
      | X =>
        show ¬P (Semiterm.val (s := stdIN P S) e f (v 0)) →
          ¬P (Semiterm.val (s := stdIN P S') e f (v 0))
        rw [val_stdIN_congr P S P S']; exact id
      | I j =>
        have hjk : j ≠ k := hφ
        show ¬Semiterm.val (s := stdIN P S) e f (v 0) ∈ S j →
          ¬Semiterm.val (s := stdIN P S') e f (v 0) ∈ S' j
        rw [val_stdIN_congr P S P S', hfix j hjk]; exact id
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

omit [DecidableEq ι] in
/-- **A `LevelBounded k`-formula has the same truth value** in `stdIN P S` and
`stdIN P S'`, provided `S`, `S'` agree at every level `≤ k`. Has no `ID1` analogue. -/
theorem levelBounded_agree [PartialOrder ι] (P : ℕ → Prop) (k : ι) {S S' : ι → Set ℕ}
    (hagree : ∀ j, j ≤ k → S j = S' j) {ξ : Type*} {n : ℕ} (φ : Semiformula (LXIN ι) ξ n)
    (hφ : LevelBounded k φ) (e : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdIN P S) e f φ ↔ Semiformula.Eval (s := stdIN P S') e f φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v =>
    have hv : (fun i => Semiterm.val (s := stdIN P S) e f (v i))
        = (fun i => Semiterm.val (s := stdIN P S') e f (v i)) :=
      funext fun i => val_stdIN_congr P S P S' e f (v i)
    rcases r with r | r
    · show Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdIN P S) e f (v i)) ↔
        Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdIN P S') e f (v i))
      rw [hv]
    · cases r with
      | X =>
        show P (Semiterm.val (s := stdIN P S) e f (v 0)) ↔
          P (Semiterm.val (s := stdIN P S') e f (v 0))
        rw [val_stdIN_congr P S P S']
      | I j =>
        show Semiterm.val (s := stdIN P S) e f (v 0) ∈ S j ↔
          Semiterm.val (s := stdIN P S') e f (v 0) ∈ S' j
        rw [val_stdIN_congr P S P S', hagree j hφ]
  | hnrel r v =>
    have hv : (fun i => Semiterm.val (s := stdIN P S) e f (v i))
        = (fun i => Semiterm.val (s := stdIN P S') e f (v i)) :=
      funext fun i => val_stdIN_congr P S P S' e f (v i)
    rcases r with r | r
    · show ¬Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdIN P S) e f (v i)) ↔
        ¬Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdIN P S') e f (v i))
      rw [hv]
    · cases r with
      | X =>
        show ¬P (Semiterm.val (s := stdIN P S) e f (v 0)) ↔
          ¬P (Semiterm.val (s := stdIN P S') e f (v 0))
        rw [val_stdIN_congr P S P S']
      | I j =>
        show ¬Semiterm.val (s := stdIN P S) e f (v 0) ∈ S j ↔
          ¬Semiterm.val (s := stdIN P S') e f (v 0) ∈ S' j
        rw [val_stdIN_congr P S P S', hagree j hφ]
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact and_congr (ihφ hφ.1 e) (ihψ hφ.2 e)
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact or_congr (ihφ hφ.1 e) (ihψ hφ.2 e)
  | hall φ ih =>
    rw [Semiformula.eval_all, Semiformula.eval_all]
    exact forall_congr' fun x => ih hφ (x :> e)
  | hexs φ ih =>
    rw [Semiformula.eval_ex, Semiformula.eval_ex]
    exact exists_congr fun x => ih hφ (x :> e)

/-! ### Substitution of a formula for `I_k` alone -/

/-- **`substIAt k F φ` reads `I_k` as the set defined by `F`**, the other predicates
`I_j`, `j ≠ k`, unchanged. Generalises `ID1.eval_substI`. -/
theorem eval_substIAt (P : ℕ → Prop) (S : ι → Set ℕ) (k : ι) {ξ : Type*}
    (F : Semiformula (LXIN ι) ξ 1) (f : ξ → ℕ) {n : ℕ} (φ : Semiformula (LXIN ι) ξ n)
    (e : Fin n → ℕ) :
    Semiformula.Eval (s := stdIN P S) e f (substIAt k F φ) ↔
      Semiformula.Eval (s := stdIN P (Function.update S k
        {x | Semiformula.Eval (s := stdIN P S) ![x] f F})) e f φ := by
  set SF : Set ℕ := {x | Semiformula.Eval (s := stdIN P S) ![x] f F} with hSF
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v =>
    have hv : (fun i => Semiterm.val (s := stdIN P S) e f (v i))
        = (fun i => Semiterm.val (s := stdIN P (Function.update S k SF)) e f (v i)) :=
      funext fun i => val_stdIN_congr P S P (Function.update S k SF) e f (v i)
    rcases r with r | r
    · show Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdIN P S) e f (v i)) ↔
        Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdIN P (Function.update S k SF))
          e f (v i))
      rw [hv]
    · cases r with
      | X =>
        show P (Semiterm.val (s := stdIN P S) e f (v 0)) ↔
          P (Semiterm.val (s := stdIN P (Function.update S k SF)) e f (v 0))
        rw [val_stdIN_congr P S P (Function.update S k SF)]
      | I j =>
        show Semiformula.Eval (s := stdIN P S) e f (substIAt k F (Semiformula.rel
          (Sum.inr (IXRelN.I j)) v)) ↔
          Semiterm.val (s := stdIN P (Function.update S k SF)) e f (v 0) ∈
            (Function.update S k SF) j
        show Semiformula.Eval (s := stdIN P S) e f
            (if _ : j = k then F/[v 0] else Semiformula.rel (Sum.inr (IXRelN.I j)) v) ↔ _
        rcases eq_or_ne j k with h | hne
        · rw [dif_pos h, h, Function.update_self, Semiformula.eval_substs, Matrix.comp₁, hSF,
            Set.mem_ofPred_eq, val_stdIN_congr P S P (Function.update S k SF)]
        · rw [dif_neg hne, Function.update_of_ne hne]
          show Semiterm.val (s := stdIN P S) e f (v 0) ∈ S j ↔
            Semiterm.val (s := stdIN P (Function.update S k SF)) e f (v 0) ∈ S j
          rw [val_stdIN_congr P S P (Function.update S k SF)]
  | hnrel r v =>
    have hv : (fun i => Semiterm.val (s := stdIN P S) e f (v i))
        = (fun i => Semiterm.val (s := stdIN P (Function.update S k SF)) e f (v i)) :=
      funext fun i => val_stdIN_congr P S P (Function.update S k SF) e f (v i)
    rcases r with r | r
    · show ¬Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdIN P S) e f (v i)) ↔
        ¬Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdIN P (Function.update S k SF))
          e f (v i))
      rw [hv]
    · cases r with
      | X =>
        show ¬P (Semiterm.val (s := stdIN P S) e f (v 0)) ↔
          ¬P (Semiterm.val (s := stdIN P (Function.update S k SF)) e f (v 0))
        rw [val_stdIN_congr P S P (Function.update S k SF)]
      | I j =>
        show Semiformula.Eval (s := stdIN P S) e f (substIAt k F (Semiformula.nrel
          (Sum.inr (IXRelN.I j)) v)) ↔
          ¬Semiterm.val (s := stdIN P (Function.update S k SF)) e f (v 0) ∈
            (Function.update S k SF) j
        show Semiformula.Eval (s := stdIN P S) e f
            (if _ : j = k then ∼(F/[v 0]) else Semiformula.nrel (Sum.inr (IXRelN.I j)) v) ↔ _
        rcases eq_or_ne j k with h | hne
        · rw [dif_pos h, h, Function.update_self, LogicalConnective.HomClass.map_neg,
            Semiformula.eval_substs, Matrix.comp₁, hSF, Set.mem_ofPred_eq,
            val_stdIN_congr P S P (Function.update S k SF)]
          rfl
        · rw [dif_neg hne, Function.update_of_ne hne]
          show ¬Semiterm.val (s := stdIN P S) e f (v 0) ∈ S j ↔
            ¬Semiterm.val (s := stdIN P (Function.update S k SF)) e f (v 0) ∈ S j
          rw [val_stdIN_congr P S P (Function.update S k SF)]
  | hand φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := stdIN P S) e f (substIAt k F φ ⋏ substIAt k F ψ) ↔ _
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact and_congr (ihφ e) (ihψ e)
  | hor φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := stdIN P S) e f (substIAt k F φ ⋎ substIAt k F ψ) ↔ _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact or_congr (ihφ e) (ihψ e)
  | hall φ ih =>
    show Semiformula.Eval (s := stdIN P S) e f (∀¹ substIAt k F φ) ↔ _
    rw [Semiformula.eval_all, Semiformula.eval_all]
    exact forall_congr' fun x => ih (x :> e)
  | hexs φ ih =>
    show Semiformula.Eval (s := stdIN P S) e f (∃¹ substIAt k F φ) ↔ _
    rw [Semiformula.eval_ex, Semiformula.eval_ex]
    exact exists_congr fun x => ih (x :> e)

/-! ### The operator at one level, and its least fixed point -/

section Operator

variable (P : ℕ → Prop) (A : ι → Semisentence (LXIN ι) 1)

/-- **The operator of level `k`**, as a function of the whole environment `S`. Only its
value at coordinates `≤ k` matters (`LevelBounded`), but it is convenient to let it read
all of `S`. -/
def opA (k : ι) (S : ι → Set ℕ) : Set ℕ :=
  {x | Semiformula.Eval (s := stdIN P S) ![x] Empty.elim (A k)}

/-- A `PositiveIn k`-operator form is monotone in `S k`, the other coordinates of the
environment held fixed at `lower`. -/
theorem opA_mono_at (k : ι) (hA : PositiveIn k (A k)) (lower : ι → Set ℕ) :
    Monotone (fun T => opA P A k (Function.update lower k T)) := by
  intro a b hab x hx
  refine positiveIn_monotone P k ?_ ?_ (A k) hA ![x] Empty.elim hx
  · rw [Function.update_self, Function.update_self]; exact hab
  · intro j hj
    rw [Function.update_of_ne hj, Function.update_of_ne hj]

/-- **The least fixed point of level `k`**, the other coordinates held at `lower`. -/
def lfpAt (lower : ι → Set ℕ) (k : ι) : Set ℕ :=
  sInf {T | opA P A k (Function.update lower k T) ⊆ T}

/-- The least fixed point at level `k` is contained in every closed set. -/
theorem lfpAt_subset (lower : ι → Set ℕ) (k : ι) {T : Set ℕ}
    (h : opA P A k (Function.update lower k T) ⊆ T) : lfpAt P A lower k ⊆ T :=
  sInf_le h

/-- The least fixed point at level `k` is closed under its operator, when `A k` is
`PositiveIn k`. -/
theorem opA_lfpAt_subset (lower : ι → Set ℕ) (k : ι) (hA : PositiveIn k (A k)) :
    opA P A k (Function.update lower k (lfpAt P A lower k)) ⊆ lfpAt P A lower k :=
  le_sInf fun _ hT =>
    (opA_mono_at P A k hA lower (lfpAt_subset P A lower k hT)).trans hT

end Operator

/-! ### The chain: assembling all the levels -/

section Chain

variable [PartialOrder ι] [WellFoundedLT ι] (P : ℕ → Prop) (A : ι → Semisentence (LXIN ι) 1)

/-- **The iterated least fixed point**, one level at a time, by well-founded recursion on
`<`: level `k` is solved against an environment that is `∅` at every level not yet
built. -/
noncomputable def lfpChain : ι → Set ℕ :=
  WellFounded.fix (wellFounded_lt (α := ι)) fun k rec =>
    lfpAt P A (fun j => if h : j < k then rec j h else ∅) k

theorem lfpChain_eq (k : ι) :
    lfpChain P A k = lfpAt P A (fun j => if _ : j < k then lfpChain P A j else ∅) k :=
  WellFounded.fix_eq (wellFounded_lt (α := ι)) _ k

/-- The truncated environment used to build level `k` agrees with the full chain at
every level `< k`, and (once updated at `k`) at every level `≤ k`. -/
theorem lfpChain_agree (k : ι) :
    ∀ j, j ≤ k → Function.update (fun j => if _ : j < k then lfpChain P A j else ∅) k
      (lfpChain P A k) j = lfpChain P A j := by
  intro j hj
  rcases eq_or_ne j k with rfl | hne
  · rw [Function.update_self]
  · rw [Function.update_of_ne hne]
    exact dif_pos (lt_of_le_of_ne hj hne)

end Chain

/-! ### Soundness of the closure and induction axioms -/

section Axioms

variable [PartialOrder ι] [WellFoundedLT ι] (P : ℕ → Prop) (A : ι → Semisentence (LXIN ι) 1)

omit [PartialOrder ι] [WellFoundedLT ι] in
/-- `A_k(F, x)` holds exactly when `x` is in the operator of level `k` applied to the
environment with `I_k` reinterpreted by `F`, other levels unchanged. -/
theorem eval_opAt (k : ι) (S : ι → Set ℕ) (F : Semiformula (LXIN ι) ℕ 1) (f : ℕ → ℕ) (x : ℕ) :
    Semiformula.Eval (s := stdIN P S) ![x] f (opAt k (A k) F) ↔
      x ∈ opA P A k (Function.update S k {y | Semiformula.Eval (s := stdIN P S) ![y] f F}) := by
  rw [opAt, eval_substIAt, Semiformula.eval_emb]
  rfl

/-- **The closure axiom of level `k` is true** in `stdIN P (lfpChain P A)`. -/
theorem eval_closureAxAt (k : ι) (hA : PositiveIn k (A k)) (hB : LevelBounded k (A k)) :
    Semiformula.Eval (s := stdIN P (lfpChain P A)) ![] Empty.elim (closureAxAt k (A k)) := by
  rw [closureAxAt, Semiformula.eval_all]
  intro x
  rw [LogicalConnective.HomClass.map_imply, eval_Iat]
  intro hx
  set lower : ι → Set ℕ := fun j => if h : j < k then lfpChain P A j else ∅ with hlower
  have hagree : ∀ j, j ≤ k →
      lfpChain P A j = Function.update lower k (lfpChain P A k) j :=
    fun j hj => (lfpChain_agree P A k j hj).symm
  have hx' : x ∈ opA P A k (Function.update lower k (lfpAt P A lower k)) := by
    rw [← lfpChain_eq]
    have := (levelBounded_agree P k hagree (A k) hB ![x] Empty.elim)
    exact this.mp hx
  have := opA_lfpAt_subset P A lower k hA hx'
  rwa [← lfpChain_eq] at this

/-- **Every instance of the induction scheme for `I_k` is true** in
`stdIN P (lfpChain P A)`. Positivity is not needed, only level-boundedness (to relate the
truncated environment used to build the fixed point to the real one). -/
theorem eval_indAxAt (k : ι) (hB : LevelBounded k (A k)) (F : Semiformula (LXIN ι) ℕ 1) :
    Semiformula.Eval (s := stdIN P (lfpChain P A)) ![] Empty.elim (indAxAt k (A k) F) := by
  rw [indAxAt]
  refine (Semiformula.eval_univCl (s := stdIN P (lfpChain P A)) _).mpr ?_
  intro f
  simp only [Semiformula.Evalf, LogicalConnective.HomClass.map_imply, Semiformula.eval_all]
  intro hcl x hx
  rw [eval_Iat] at hx
  set lower : ι → Set ℕ := fun j => if h : j < k then lfpChain P A j else ∅ with hlower
  set SF : Set ℕ := {y | Semiformula.Eval (s := stdIN P (lfpChain P A)) ![y] f F} with hSF
  have hagree : ∀ j, j ≤ k →
      Function.update lower k SF j = Function.update (lfpChain P A) k SF j := by
    intro j hj
    rcases eq_or_ne j k with rfl | hne
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact dif_pos (lt_of_le_of_ne hj hne)
  have hclosed : opA P A k (Function.update lower k SF) ⊆ SF := by
    intro y hy
    have hy' : y ∈ opA P A k (Function.update (lfpChain P A) k SF) :=
      (levelBounded_agree P k hagree (A k) hB ![y] Empty.elim).mp hy
    have hopAt : Semiformula.Eval (s := stdIN P (lfpChain P A)) ![y] f (opAt k (A k) F) :=
      (eval_opAt P A k (lfpChain P A) F f y).mpr (by
        have hSF' : SF = {z | Semiformula.Eval (s := stdIN P (lfpChain P A)) ![z] f F} := hSF
        rwa [hSF'] at hy')
    exact hcl y hopAt
  have hsub := lfpAt_subset P A lower k hclosed
  rw [← lfpChain_eq] at hsub
  exact hsub hx

end Axioms

/-! ### The axioms of `paLXIN` -/

section PA

variable (P : ℕ → Prop) (S : ι → Set ℕ)

set_option linter.style.haveILetI false in
omit [DecidableEq ι] in
/-- Every equality axiom is true in `stdIN P S`. -/
theorem eval_of_eqAxiom {σ : Sentence (LXIN ι)} (h : σ ∈ 𝗘𝗤 (LXIN ι)) :
    Semiformula.Eval (s := stdIN P S) ![] Empty.elim σ := by
  letI : Structure (LXIN ι) ℕ := stdIN P S
  haveI : Structure.Eq (LXIN ι) ℕ := ⟨fun _ _ => iff_of_eq rfl⟩
  haveI : ℕ↓[LXIN ι] ⊧* 𝗘𝗤 (LXIN ι) := Structure.Eq.models_eq (LXIN ι) ℕ
  exact Theory.models ℕ (𝗘𝗤 (LXIN ι)) h

omit [DecidableEq ι] in
/-- Every transported axiom of `𝗣𝗔⁻` is true in `stdIN P S`. -/
theorem eval_of_paMinus {σ : Sentence (LXIN ι)} (h : σ ∈ Theory.lMap (toLXIN ι) 𝗣𝗔⁻) :
    Semiformula.Eval (s := stdIN P S) ![] Empty.elim σ := by
  obtain ⟨τ, hτ, rfl⟩ := h
  rw [eval_lMap_toLXIN]
  exact Theory.models ℕ 𝗣𝗔⁻ hτ

omit [DecidableEq ι] in
theorem val_zero_stdIN (f : ℕ → ℕ) :
    Semiterm.val (s := stdIN P S) ![] f ((0 : ℕ) : Semiterm (LXIN ι) ℕ 0) = 0 := rfl

omit [DecidableEq ι] in
theorem val_succ_stdIN (f : ℕ → ℕ) (x : ℕ) :
    Semiterm.val (s := stdIN P S) ![x] f (‘(#0 + 1)’ : Semiterm (LXIN ι) ℕ 1) = x + 1 := rfl

omit [DecidableEq ι] in
/-- Every induction axiom is true in `stdIN P S`: induction on `ℕ`. -/
theorem eval_of_succInd {σ : Sentence (LXIN ι)} (h : σ ∈ InductionScheme (LXIN ι) Set.univ) :
    Semiformula.Eval (s := stdIN P S) ![] Empty.elim σ := by
  obtain ⟨φ, -, rfl⟩ := h
  refine (Semiformula.eval_univCl (s := stdIN P S) _).mpr ?_
  intro f
  show Semiformula.Eval (s := stdIN P S) ![] f ((φ/[((0 : ℕ) : Semiterm (LXIN ι) ℕ 0)]) 🡒
      (∀¹ (φ/[(#0 : Semiterm (LXIN ι) ℕ 1)] 🡒 φ/[(‘(#0 + 1)’ : Semiterm (LXIN ι) ℕ 1)])) 🡒
      ∀¹ (φ/[(#0 : Semiterm (LXIN ι) ℕ 1)]))
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_all,
    Semiformula.eval_substs, Matrix.comp₁]
  intro h0 hs x
  induction x with
  | zero => exact h0
  | succ k ih => exact hs k ih

/-- `stdIN P S` is a model of `paLXIN ι`, for every `P` and `S`. -/
theorem models_paLXIN :
    letI := stdIN P S; ℕ↓[LXIN ι] ⊧* paLXIN ι := by
  let _ : Structure (LXIN ι) ℕ := stdIN P S
  refine Semantics.modelsSet_iff.mpr fun σ hσ => models_iff.mpr ?_
  rcases hσ with h | h | h
  · exact eval_of_eqAxiom P S h
  · exact eval_of_paMinus P S h
  · exact eval_of_succInd P S h

end PA

/-! ### Soundness and consistency -/

section Soundness

variable [PartialOrder ι] [WellFoundedLT ι] (A : ι → Semisentence (LXIN ι) 1)

/-- Every axiom of `ID A` is true in `stdIN P (lfpChain P A)`, given that `A` is a
positive, level-bounded family. -/
theorem eval_of_mem_ID (hAp : FamilyPositive A) (hAb : FamilyLevelBounded A) (P : ℕ → Prop)
    {σ : Sentence (LXIN ι)} (h : σ ∈ ID A) :
    Semiformula.Eval (s := stdIN P (lfpChain P A)) ![] Empty.elim σ := by
  rcases (mem_ID A).mp h with h | h | h | ⟨k, rfl | ⟨F, rfl⟩⟩
  · exact eval_of_eqAxiom P _ h
  · exact eval_of_paMinus P _ h
  · exact eval_of_succInd P _ h
  · exact eval_closureAxAt P A k (hAp k) (hAb k)
  · exact eval_indAxAt P A k (hAb k) F

/-- **Soundness of `ID A`**: for a positive, level-bounded family `A` and every reading
`P` of `X`, the standard structure with `I_k` read as the `k`-th iterated least fixed
point is a model of `ID A`. -/
theorem models_ID (hAp : FamilyPositive A) (hAb : FamilyLevelBounded A) (P : ℕ → Prop) :
    letI := stdIN P (lfpChain P A); ℕ↓[LXIN ι] ⊧* ID A := by
  let _ : Structure (LXIN ι) ℕ := stdIN P (lfpChain P A)
  exact Semantics.modelsSet_iff.mpr fun σ hσ => models_iff.mpr (eval_of_mem_ID A hAp hAb P hσ)

/-- **Every theorem of `ID A` is true in the standard model.** -/
theorem eval_of_provable_ID (hAp : FamilyPositive A) (hAb : FamilyLevelBounded A)
    (P : ℕ → Prop) {σ : Sentence (LXIN ι)} (h : ID A ⊢ σ) :
    Semiformula.Eval (s := stdIN P (lfpChain P A)) ![] Empty.elim σ := by
  let _ : Structure (LXIN ι) ℕ := stdIN P (lfpChain P A)
  exact models_iff.mp (models_of_provable (models_ID A hAp hAb P) h)

/-- **`ID A` is consistent**, for every positive, level-bounded family. -/
theorem ID_consistent (hAp : FamilyPositive A) (hAb : FamilyLevelBounded A) :
    ID A ⊬ (⊥ : Sentence (LXIN ι)) := by
  intro h
  have := eval_of_provable_ID A hAp hAb (fun _ => False) h
  simp at this

end Soundness

/-- **`ID n A` (`n` simultaneous inductive definitions) is consistent.** -/
theorem IDn_consistent (n : ℕ) (A : Fin n → Semisentence (LXIn n) 1)
    (hAp : FamilyPositive A) (hAb : FamilyLevelBounded A) : IDn n A ⊬ (⊥ : Sentence (LXIn n)) :=
  ID_consistent A hAp hAb

/-! ### The slot check -/

section SlotCheck

/-- **The slot check**, repeated per level as
`SlotCheck.lean` did once for `ID1`: the one way this construction could silently go
wrong is a level index swapped somewhere in `Iat`/`substIAt`/`opAt`/`closureAxAt` — e.g.
level `1`'s closure axiom accidentally reading column `0` of the environment, or vice
versa. On concrete data this is exactly the kind of mistake a direct evaluation catches:
`Iat k` reads column `k` of the environment and no other column, for *every* pair of
columns, checked here at `k = 0` vs `k = 1`. -/
theorem slotCheck_Iat_reads_its_own_column (P : ℕ → Prop) (S : Fin 2 → Set ℕ)
    (h0 : 5 ∉ S 0) (h1 : 5 ∈ S 1) :
    ¬Semiformula.Eval (s := stdIN P S) ![5] Empty.elim (Iat (0 : Fin 2) #0) ∧
      Semiformula.Eval (s := stdIN P S) ![5] Empty.elim (Iat (1 : Fin 2) #0) := by
  constructor
  · rw [eval_Iat]; simpa using h0
  · rw [eval_Iat]; simpa using h1

/-- **A concrete 2-level instance**: `A_0(Y, x) := ⊥`, so `I_0`'s least fixed point is
`∅`; `A_1(Y, x) := I_0(x)`, so `I_1`'s operator reads level `0` (not level `1` itself, and
not some other column), and its least fixed point is `∅` as well. -/
def slotA : Fin 2 → Semisentence (LXIn 2) 1
  | 0 => (⊥ : Semisentence (LXIn 2) 1)
  | 1 => Iat (0 : Fin 2) #0

/-- Positivity of `slotA` at every level: both `A_0 = ⊥` and `A_1 = I_0(x)` are atoms or
`⊥`, so positivity in the *own* level (`⊥` trivially, `I_0(x)` because a `.rel` atom is
never a counterexample to positivity, regardless of which level it names) is immediate. -/
theorem slotA_positive : FamilyPositive slotA := by
  intro k
  fin_cases k <;> trivial

/-- Level-boundedness of `slotA`: `A_0 = ⊥` mentions no level; `A_1 = I_0(x)` mentions
only level `0 ≤ 1` — the slot that must be checked, since `LevelBounded 1 (Iat 0 #0)`
unfolds exactly to `(0 : Fin 2) ≤ 1`. -/
theorem slotA_levelBounded : FamilyLevelBounded slotA := by
  intro k
  fin_cases k
  · trivial
  · show (0 : Fin 2) ≤ 1
    decide

/-- **The slot check closes the loop**: the whole soundness/consistency machine, built
generically over the family `A`, actually instantiates on this concrete 2-level example. -/
theorem slotA_consistent : IDn 2 slotA ⊬ (⊥ : Sentence (LXIn 2)) :=
  IDn_consistent 2 slotA slotA_positive slotA_levelBounded

end SlotCheck

end IDn

end OrdinalAnalysis
