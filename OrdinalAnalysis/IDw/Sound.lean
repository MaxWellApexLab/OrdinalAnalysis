/-
  The standard model of `IDw A`, built as an ℕ-indexed chain of least fixed points (level
  `y`'s fixed point computed with all lower levels already fixed), and its consistency.

  Generalises `IDn/Sound.lean`'s family construction (`lfpChain`, one operator per level
  `k : ι`, level-boundedness a syntactic side condition) to the UNIFORM binary case: one
  schema `A`, applied at every level `y : ℕ` via `AAt`, with the "lower levels" reading of
  `Q` *structurally* confined to `z < y` by `AAt`'s own compilation (`Q(z,a) ↦ z < y ∧
  J(z,a)`) — so the analogue of `IDn.levelBounded_agree` (`agreeBelowJ` below) is an
  unconditional theorem, not a hypothesis-dependent one; there is no `LevelBounded` side
  condition to state for `IDw`.

  **The structure.** `stdJ P S` is the `LXJ`-structure on `ℕ` with standard arithmetic, `X`
  read by `P`, and `J` read by `S`, level = first argument (`Jat s t ↔ t ∈ S s`).

  **The operator, the fixed point at one level, and the chain.**

    * `opJ P A S y := {x | A_y(J(y,·)/J^{≺y}, x) holds in stdJ P S}`, i.e. `AAt (Jat #1 #0)
      #1 A` evaluated at `(x, y)` — the direct analogue of `IDn.opA`. Kept at `ξ = Empty`
      throughout, matching `closureAxJ`.
    * `lfpAt P A lower y := sInf {T | opJ P A (update lower y T) y ⊆ T}`.
    * `lfpChain P A : ℕ → Set ℕ`, by well-founded recursion on `<`, exactly as
      `IDn.lfpChain` with `ι := ℕ`.

  **The structural facts about `AAt`, replacing `IDn`'s positivity/boundedness pair.**

    * `AAt_monotone_of_positive`: if `PositiveP A`, and `S`, `S'` agree off `y` with
      `S y ⊆ S' y`, then `AAt (Jat #1 #0) Y A` is monotone from `S` to `S'` (`Y`'s value
      fixed at `y`). Proved by induction on `A`; the `Q`-atom case needs no positivity at
      all — `s < Y` forces `s ≠ y`, so `Q`'s reads are *unchanged* between `S` and `S'`.
    * `agreeBelowJ`: for **any** `A` (no `PositiveP` needed), if `S`, `S'` agree at every
      `z ≤ y`, then `AAt (Jat #1 #0) Y A` has the *same* truth value against `S` and `S'`.
      This is what lets a level's fixed point, built against a truncated environment that
      is `∅` above `y`, be recognised as closed against the *real* chain once assembled.
    * `eval_AAt_subst`: `A_y(F, x)` (an arbitrary `F` substituted for the level's own
      place) holds exactly when `x` lies in the operator of level `y` with `J`'s `y`-th
      column reinterpreted as `{x | F(y, x)}` — the analogue of `IDn.eval_substIAt`/
      `eval_opAt` combined, needed for the induction axiom's soundness.
    * `AAt_emb`/`eval_AAt_emb`: `AAt (Jat #1 #0) Y (Rewriting.emb A)` (the `ξ = ℕ` copy of
      `A` used inside `indAxJ`) has the same truth value as `AAt (Jat #1 #0) Y A` (the
      `ξ = Empty` copy `opJ` is built from) — bridges the two copies of `A` that
      `closureAxJ` (`ξ = Empty`) and `indAxJ` (`ξ = ℕ`, to allow `F`'s parameters) need.

  **Soundness** (`models_IDw`): given `PositiveP A`, for every `P`, every axiom of `IDw A`
  is true in `stdJ P (lfpChain P A)`. With Foundation's soundness theorem this gives
  `IDw_consistent`.

  Contents.

    `ixJStruc`, `stdJ`                                    the standard structure
    `eval_lMap_toLXJ`, `val_stdJ_congr`, `eval_Xat`, `eval_Jat`
    `eval_rel_inl_congr`, `eval_nrel_inl_congr`           arithmetic atoms are `S`-invariant
    `AAt_monotone_of_positive`, `agreeBelowJ`             the two structural facts
    `termCast_emb`, `AAt_emb`, `eval_AAt_emb`             bridging `ξ = Empty`/`ξ = ℕ`
    `eval_AAt_subst`                                       substitution of `F` for `P`
    `opJ`, `opJ_mono_at`, `lfpAt`, `lfpAt_subset`, `opJ_lfpAt_subset`
    `lfpChain`, `lfpChain_eq`, `lfpChain_agree`           **the iterated least fixed point**
    `eval_closureAxJ`, `eval_indAxJ`
    `models_paLXJ`, `models_IDw`                          **soundness**
    `IDw_consistent`                                       **consistency**
-/
import OrdinalAnalysis.IDw.Theory
import Mathlib.Order.FixedPoints
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option warn.classDefReducibility false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

open scoped Classical

/-! ### The standard structure -/

/-- The fresh predicates: `X` read by `P`, `J` read by `S`, level = first argument. -/
def ixJStruc (P : ℕ → Prop) (S : ℕ → Set ℕ) : Structure XJLang ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ r v => match r with
    | XJRel.X => P (v 0)
    | XJRel.J => v 1 ∈ S (v 0)

/-- **The standard structure of `LXJ`**: arithmetic standard, `X` read by `P`, `J` read by
`S` (`Jat s t ↔ t ∈ S s`). -/
def stdJ (P : ℕ → Prop) (S : ℕ → Set ℕ) : Structure LXJ ℕ :=
  Structure.add ℒₒᵣ XJLang ℕ (str₂ := ixJStruc P S)

section Std

variable (P : ℕ → Prop) (S : ℕ → Set ℕ)

/-- The arithmetic reduct of `stdJ P S` is Foundation's standard model of `ℕ`. -/
theorem stdJ_lMap_toLXJ : (stdJ P S).lMap toLXJ = Arithmetic.standardModel ℕ := rfl

/-- An arithmetic formula says in `stdJ P S` what it says in `ℕ`. -/
@[simp] theorem eval_lMap_toLXJ {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) (e : Fin n → ℕ)
    (f : ξ → ℕ) :
    Semiformula.Eval (s := stdJ P S) e f (Semiformula.lMap toLXJ φ)
      ↔ Semiformula.Eval (M := ℕ) e f φ :=
  Structure.eval_lMap_add₁ (str₂ := ixJStruc P S) φ e f

/-- Term values do not depend on the readings of `X` and `J`. -/
theorem val_stdJ_congr (Q : ℕ → Prop) (T : ℕ → Set ℕ) {ξ : Type*} {n : ℕ} (e : Fin n → ℕ)
    (f : ξ → ℕ) (t : Semiterm LXJ ξ n) :
    Semiterm.val (s := stdJ P S) e f t = Semiterm.val (s := stdJ Q T) e f t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func fn v ih =>
      simp only [Semiterm.val_func, Function.comp_def, ih]
      rcases fn with fn | fn
      · rfl
      · exact PEmpty.elim fn

/-- `X(t)` holds when `P` holds at the value of `t`. -/
theorem eval_Xat {ξ : Type*} {n : ℕ} (t : Semiterm LXJ ξ n) (e : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdJ P S) e f (Xat t) ↔ P (Semiterm.val (s := stdJ P S) e f t) := by
  have h : (Semiterm.val (s := stdJ P S) e f ∘ ![t] : Fin 1 → ℕ)
      = ![Semiterm.val (s := stdJ P S) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg ((stdJ P S).rel (Sum.inr XJRel.X)) h)

/-- `J(s, t)` holds when the value of `t` lies in the `s`-th level. -/
@[simp] theorem eval_Jat {ξ : Type*} {n : ℕ} (s t : Semiterm LXJ ξ n) (e : Fin n → ℕ)
    (f : ξ → ℕ) :
    Semiformula.Eval (s := stdJ P S) e f (Jat s t) ↔
      Semiterm.val (s := stdJ P S) e f t ∈ S (Semiterm.val (s := stdJ P S) e f s) := by
  have h : (Semiterm.val (s := stdJ P S) e f ∘ ![s, t] : Fin 2 → ℕ)
      = ![Semiterm.val (s := stdJ P S) e f s, Semiterm.val (s := stdJ P S) e f t] :=
    Matrix.comp₂ s t
  exact Iff.of_eq (congrArg ((stdJ P S).rel (Sum.inr XJRel.J)) h)

/-- `s < t` (arithmetic) has its usual meaning, independent of `X`, `J`. -/
@[simp] theorem eval_ltAt {ξ : Type*} {n : ℕ} (s t : Semiterm LXJ ξ n) (e : Fin n → ℕ)
    (f : ξ → ℕ) :
    Semiformula.Eval (s := stdJ P S) e f (ltAt s t) ↔
      Semiterm.val (s := stdJ P S) e f s < Semiterm.val (s := stdJ P S) e f t := by
  have h : (fun i => Semiterm.val (s := stdJ P S) e f (![s, t] i))
      = ![Semiterm.val (s := stdJ P S) e f s, Semiterm.val (s := stdJ P S) e f t] :=
    Matrix.comp₂ s t
  show Structure.rel (M := ℕ) (Language.LT.lt : (ℒₒᵣ).Rel 2)
      (fun i => Semiterm.val (s := stdJ P S) e f (![s, t] i)) ↔ _
  rw [h]
  exact Structure.lt_lang

end Std

/-! ### Arithmetic atoms do not depend on `S` -/

/-- Any arithmetic atom (an `.rel` on the `ℒₒᵣ` side) has the same truth value against any
two readings of `X`, `J`. -/
theorem eval_rel_inl_congr {ξ : Type*} {n k : ℕ} (P Q : ℕ → Prop) (S S' : ℕ → Set ℕ)
    (r : (ℒₒᵣ).Rel k) (v : Fin k → Semiterm LXJ ξ n) (e : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdJ P S) e f (Semiformula.rel (Sum.inl r) v) ↔
      Semiformula.Eval (s := stdJ Q S') e f (Semiformula.rel (Sum.inl r) v) := by
  have hv : (fun i => Semiterm.val (s := stdJ P S) e f (v i))
      = (fun i => Semiterm.val (s := stdJ Q S') e f (v i)) :=
    funext fun i => val_stdJ_congr P S Q S' e f (v i)
  show Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdJ P S) e f (v i)) ↔
      Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdJ Q S') e f (v i))
  rw [hv]

/-- Same as `eval_rel_inl_congr` for `.nrel`. -/
theorem eval_nrel_inl_congr {ξ : Type*} {n k : ℕ} (P Q : ℕ → Prop) (S S' : ℕ → Set ℕ)
    (r : (ℒₒᵣ).Rel k) (v : Fin k → Semiterm LXJ ξ n) (e : Fin n → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stdJ P S) e f (Semiformula.nrel (Sum.inl r) v) ↔
      Semiformula.Eval (s := stdJ Q S') e f (Semiformula.nrel (Sum.inl r) v) := by
  have hv : (fun i => Semiterm.val (s := stdJ P S) e f (v i))
      = (fun i => Semiterm.val (s := stdJ Q S') e f (v i)) :=
    funext fun i => val_stdJ_congr P S Q S' e f (v i)
  show ¬Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdJ P S) e f (v i)) ↔
      ¬Structure.rel (M := ℕ) r (fun i => Semiterm.val (s := stdJ Q S') e f (v i))
  rw [hv]

/-! ### `AAt` is monotone in `P`-positive forms -/

/-- **A `PositiveP`-form is monotone in `S y` alone**, the other coordinates of the
environment held fixed. `F` is fixed at `Jat #1 #0` throughout — the only instance `opJ`
ever needs. Generalises `IDn.positiveIn_monotone`. -/
theorem AAt_monotone_of_positive (P : ℕ → Prop) (y : ℕ) {S S' : ℕ → Set ℕ}
    (hle : S y ⊆ S' y) (hfix : ∀ z, z ≠ y → S z = S' z) {ξ : Type*} {n : ℕ}
    (φ : Semiformula LForm ξ n) (hφ : PositiveP φ) (Y : Semiterm LXJ ξ n) (e : Fin n → ℕ)
    (f : ξ → ℕ) (hYe : Semiterm.val (s := stdJ P S) e f Y = y) :
    Semiformula.Eval (s := stdJ P S) e f (AAt (Jat #1 #0) Y φ) →
    Semiformula.Eval (s := stdJ P S') e f (AAt (Jat #1 #0) Y φ) := by
  induction φ using Semiformula.rec' with
  | hverum => exact fun h => h
  | hfalsum => exact fun h => h
  | hrel r v =>
    rcases r with r | r
    · exact (eval_rel_inl_congr P P S S' r (fun i => termCast (v i)) e f).mp
    · cases r with
      | P =>
        show Semiformula.Eval (s := stdJ P S) e f (Jat Y (termCast (v 0))) →
          Semiformula.Eval (s := stdJ P S') e f (Jat Y (termCast (v 0)))
        intro h
        rw [eval_Jat] at h
        rw [eval_Jat]
        have hvY' : Semiterm.val (s := stdJ P S') e f Y = y := by
          rw [← val_stdJ_congr P S P S' e f Y]; exact hYe
        have hv0' : Semiterm.val (s := stdJ P S') e f (termCast (v 0))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 0)) :=
          (val_stdJ_congr P S P S' e f (termCast (v 0))).symm
        rw [hvY', hv0']
        rw [hYe] at h
        exact hle h
      | Q =>
        show Semiformula.Eval (s := stdJ P S) e f
            (ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1))) →
          Semiformula.Eval (s := stdJ P S') e f
            (ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1)))
        intro h
        simp only [LogicalConnective.HomClass.map_and, eval_Jat, eval_ltAt] at h
        obtain ⟨hlt, hmem⟩ := h
        simp only [LogicalConnective.HomClass.map_and, eval_Jat, eval_ltAt]
        have hv0' : Semiterm.val (s := stdJ P S') e f (termCast (v 0))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 0)) :=
          (val_stdJ_congr P S P S' e f (termCast (v 0))).symm
        have hv1' : Semiterm.val (s := stdJ P S') e f (termCast (v 1))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 1)) :=
          (val_stdJ_congr P S P S' e f (termCast (v 1))).symm
        have hvY' : Semiterm.val (s := stdJ P S') e f Y
            = Semiterm.val (s := stdJ P S) e f Y :=
          (val_stdJ_congr P S P S' e f Y).symm
        rw [hv0', hv1', hvY']
        refine ⟨hlt, ?_⟩
        have hne : Semiterm.val (s := stdJ P S) e f (termCast (v 0)) ≠ y := by
          rw [← hYe]; exact ne_of_lt hlt
        rwa [← hfix _ hne]
  | hnrel r v =>
    rcases r with r | r
    · exact (eval_nrel_inl_congr P P S S' r (fun i => termCast (v i)) e f).mp
    · cases r with
      | P => exact hφ.elim
      | Q =>
        show Semiformula.Eval (s := stdJ P S) e f
            (∼(ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1)))) →
          Semiformula.Eval (s := stdJ P S') e f
            (∼(ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1))))
        intro hn
        simp only [LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_and,
          eval_Jat, eval_ltAt] at hn ⊢
        rintro ⟨hlt, hmem⟩
        have hv0' : Semiterm.val (s := stdJ P S') e f (termCast (v 0))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 0)) :=
          (val_stdJ_congr P S P S' e f (termCast (v 0))).symm
        have hv1' : Semiterm.val (s := stdJ P S') e f (termCast (v 1))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 1)) :=
          (val_stdJ_congr P S P S' e f (termCast (v 1))).symm
        have hvY' : Semiterm.val (s := stdJ P S') e f Y
            = Semiterm.val (s := stdJ P S) e f Y :=
          (val_stdJ_congr P S P S' e f Y).symm
        rw [hv0', hvY'] at hlt
        rw [hv0', hv1'] at hmem
        have hne : Semiterm.val (s := stdJ P S) e f (termCast (v 0)) ≠ y := by
          rw [← hYe]; exact ne_of_lt hlt
        rw [← hfix _ hne] at hmem
        exact hn ⟨hlt, hmem⟩
  | hand φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := stdJ P S) e f (AAt (Jat #1 #0) Y φ ⋏ AAt (Jat #1 #0) Y ψ) →
      Semiformula.Eval (s := stdJ P S') e f (AAt (Jat #1 #0) Y φ ⋏ AAt (Jat #1 #0) Y ψ)
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact fun h => ⟨ihφ hφ.1 Y e hYe h.1, ihψ hφ.2 Y e hYe h.2⟩
  | hor φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := stdJ P S) e f (AAt (Jat #1 #0) Y φ ⋎ AAt (Jat #1 #0) Y ψ) →
      Semiformula.Eval (s := stdJ P S') e f (AAt (Jat #1 #0) Y φ ⋎ AAt (Jat #1 #0) Y ψ)
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact fun h => h.imp (ihφ hφ.1 Y e hYe) (ihψ hφ.2 Y e hYe)
  | hall φ ih =>
    show Semiformula.Eval (s := stdJ P S) e f (∀¹ AAt (Jat #1 #0) (Rew.bShift Y) φ) →
      Semiformula.Eval (s := stdJ P S') e f (∀¹ AAt (Jat #1 #0) (Rew.bShift Y) φ)
    rw [Semiformula.eval_all, Semiformula.eval_all]
    intro h x
    exact ih hφ (Rew.bShift Y) (x :> e) (by rw [Semiterm.val_bShift]; exact hYe) (h x)
  | hexs φ ih =>
    show Semiformula.Eval (s := stdJ P S) e f (∃¹ AAt (Jat #1 #0) (Rew.bShift Y) φ) →
      Semiformula.Eval (s := stdJ P S') e f (∃¹ AAt (Jat #1 #0) (Rew.bShift Y) φ)
    rw [Semiformula.eval_ex, Semiformula.eval_ex]
    rintro ⟨x, hx⟩
    exact ⟨x, ih hφ (Rew.bShift Y) (x :> e) (by rw [Semiterm.val_bShift]; exact hYe) hx⟩

/-! ### `AAt` is confined below `y` -/

/-- **`AAt (Jat #1 #0) Y A` has the same truth value** against any two environments that
agree at every coordinate `≤ y = val Y` — for *every* `A`, no positivity needed. Replaces
`IDn.levelBounded_agree` (which needed a `LevelBounded` hypothesis) with an unconditional
theorem: the confinement to `z < y` for `Q`'s reads, and to exactly `y` for `P`'s reads, is
structural in `AAt`'s own compilation. -/
theorem agreeBelowJ (P : ℕ → Prop) (y : ℕ) {S S' : ℕ → Set ℕ}
    (hagree : ∀ z, z ≤ y → S z = S' z) {ξ : Type*} {n : ℕ} (φ : Semiformula LForm ξ n)
    (Y : Semiterm LXJ ξ n) (e : Fin n → ℕ) (f : ξ → ℕ)
    (hYe : Semiterm.val (s := stdJ P S) e f Y = y) :
    Semiformula.Eval (s := stdJ P S) e f (AAt (Jat #1 #0) Y φ) ↔
    Semiformula.Eval (s := stdJ P S') e f (AAt (Jat #1 #0) Y φ) := by
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v =>
    rcases r with r | r
    · exact eval_rel_inl_congr P P S S' r (fun i => termCast (v i)) e f
    · cases r with
      | P =>
        show Semiformula.Eval (s := stdJ P S) e f (Jat Y (termCast (v 0))) ↔
          Semiformula.Eval (s := stdJ P S') e f (Jat Y (termCast (v 0)))
        have hvY' : Semiterm.val (s := stdJ P S') e f Y = y := by
          rw [← val_stdJ_congr P S P S' e f Y]; exact hYe
        have hv0' : Semiterm.val (s := stdJ P S') e f (termCast (v 0))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 0)) :=
          (val_stdJ_congr P S P S' e f (termCast (v 0))).symm
        constructor
        · intro h
          rw [eval_Jat] at h
          rw [hYe, hagree y le_rfl] at h
          rw [eval_Jat, hvY', hv0']
          exact h
        · intro h
          rw [eval_Jat] at h
          rw [hvY', ← hagree y le_rfl] at h
          rw [eval_Jat, hYe, ← hv0']
          exact h
      | Q =>
        show Semiformula.Eval (s := stdJ P S) e f
            (ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1))) ↔
          Semiformula.Eval (s := stdJ P S') e f
            (ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1)))
        have hv0' : Semiterm.val (s := stdJ P S') e f (termCast (v 0))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 0)) :=
          (val_stdJ_congr P S P S' e f (termCast (v 0))).symm
        have hv1' : Semiterm.val (s := stdJ P S') e f (termCast (v 1))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 1)) :=
          (val_stdJ_congr P S P S' e f (termCast (v 1))).symm
        have hvY' : Semiterm.val (s := stdJ P S') e f Y
            = Semiterm.val (s := stdJ P S) e f Y :=
          (val_stdJ_congr P S P S' e f Y).symm
        constructor
        · intro h
          simp only [LogicalConnective.HomClass.map_and, eval_Jat, eval_ltAt] at h
          obtain ⟨hlt, hmem⟩ := h
          simp only [LogicalConnective.HomClass.map_and, eval_Jat, eval_ltAt]
          rw [hv0', hv1', hvY']
          have hle : Semiterm.val (s := stdJ P S) e f (termCast (v 0)) ≤ y := by
            rw [← hYe]; exact le_of_lt hlt
          exact ⟨hlt, (hagree _ hle) ▸ hmem⟩
        · intro h
          simp only [LogicalConnective.HomClass.map_and, eval_Jat, eval_ltAt] at h
          obtain ⟨hlt, hmem⟩ := h
          rw [hv0', hvY'] at hlt
          rw [hv0', hv1'] at hmem
          simp only [LogicalConnective.HomClass.map_and, eval_Jat, eval_ltAt]
          have hle : Semiterm.val (s := stdJ P S) e f (termCast (v 0)) ≤ y := by
            rw [← hYe]; exact le_of_lt hlt
          exact ⟨hlt, (hagree _ hle).symm ▸ hmem⟩
  | hnrel r v =>
    rcases r with r | r
    · exact eval_nrel_inl_congr P P S S' r (fun i => termCast (v i)) e f
    · cases r with
      | P =>
        show Semiformula.Eval (s := stdJ P S) e f (∼(Jat Y (termCast (v 0)))) ↔
          Semiformula.Eval (s := stdJ P S') e f (∼(Jat Y (termCast (v 0))))
        have hvY' : Semiterm.val (s := stdJ P S') e f Y = y := by
          rw [← val_stdJ_congr P S P S' e f Y]; exact hYe
        have hv0' : Semiterm.val (s := stdJ P S') e f (termCast (v 0))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 0)) :=
          (val_stdJ_congr P S P S' e f (termCast (v 0))).symm
        simp only [LogicalConnective.HomClass.map_neg, eval_Jat]
        rw [hYe, hvY', hv0', hagree y le_rfl]
      | Q =>
        show Semiformula.Eval (s := stdJ P S) e f
            (∼(ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1)))) ↔
          Semiformula.Eval (s := stdJ P S') e f
            (∼(ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1))))
        have hv0' : Semiterm.val (s := stdJ P S') e f (termCast (v 0))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 0)) :=
          (val_stdJ_congr P S P S' e f (termCast (v 0))).symm
        have hv1' : Semiterm.val (s := stdJ P S') e f (termCast (v 1))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 1)) :=
          (val_stdJ_congr P S P S' e f (termCast (v 1))).symm
        have hvY' : Semiterm.val (s := stdJ P S') e f Y
            = Semiterm.val (s := stdJ P S) e f Y :=
          (val_stdJ_congr P S P S' e f Y).symm
        have hiff :
            (Semiterm.val (s := stdJ P S) e f (termCast (v 0))
                < Semiterm.val (s := stdJ P S) e f Y ∧
              Semiterm.val (s := stdJ P S) e f (termCast (v 1)) ∈
                S (Semiterm.val (s := stdJ P S) e f (termCast (v 0)))) ↔
            (Semiterm.val (s := stdJ P S') e f (termCast (v 0))
                < Semiterm.val (s := stdJ P S') e f Y ∧
              Semiterm.val (s := stdJ P S') e f (termCast (v 1)) ∈
                S' (Semiterm.val (s := stdJ P S') e f (termCast (v 0)))) := by
          rw [hv0', hv1', hvY']
          constructor
          · rintro ⟨hlt, hmem⟩
            have hle : Semiterm.val (s := stdJ P S) e f (termCast (v 0)) ≤ y := by
              rw [← hYe]; exact le_of_lt hlt
            exact ⟨hlt, (hagree _ hle) ▸ hmem⟩
          · rintro ⟨hlt, hmem⟩
            have hle : Semiterm.val (s := stdJ P S) e f (termCast (v 0)) ≤ y := by
              rw [← hYe]; exact le_of_lt hlt
            exact ⟨hlt, (hagree _ hle).symm ▸ hmem⟩
        simp only [LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_and,
          eval_Jat, eval_ltAt]
        exact not_congr hiff
  | hand φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := stdJ P S) e f (AAt (Jat #1 #0) Y φ ⋏ AAt (Jat #1 #0) Y ψ) ↔
      Semiformula.Eval (s := stdJ P S') e f (AAt (Jat #1 #0) Y φ ⋏ AAt (Jat #1 #0) Y ψ)
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact and_congr (ihφ Y e hYe) (ihψ Y e hYe)
  | hor φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := stdJ P S) e f (AAt (Jat #1 #0) Y φ ⋎ AAt (Jat #1 #0) Y ψ) ↔
      Semiformula.Eval (s := stdJ P S') e f (AAt (Jat #1 #0) Y φ ⋎ AAt (Jat #1 #0) Y ψ)
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact or_congr (ihφ Y e hYe) (ihψ Y e hYe)
  | hall φ ih =>
    show Semiformula.Eval (s := stdJ P S) e f (∀¹ AAt (Jat #1 #0) (Rew.bShift Y) φ) ↔
      Semiformula.Eval (s := stdJ P S') e f (∀¹ AAt (Jat #1 #0) (Rew.bShift Y) φ)
    rw [Semiformula.eval_all, Semiformula.eval_all]
    exact forall_congr' fun x =>
      ih (Rew.bShift Y) (x :> e) (by rw [Semiterm.val_bShift]; exact hYe)
  | hexs φ ih =>
    show Semiformula.Eval (s := stdJ P S) e f (∃¹ AAt (Jat #1 #0) (Rew.bShift Y) φ) ↔
      Semiformula.Eval (s := stdJ P S') e f (∃¹ AAt (Jat #1 #0) (Rew.bShift Y) φ)
    rw [Semiformula.eval_ex, Semiformula.eval_ex]
    exact exists_congr fun x =>
      ih (Rew.bShift Y) (x :> e) (by rw [Semiterm.val_bShift]; exact hYe)

/-! ### Substituting an arbitrary `F` for the level's own place -/

/-- **`A_y(F, x)` reads `J`'s `y`-th column as the set defined by `F`**, the other
coordinates unchanged. Generalises `IDn.eval_substIAt`/`eval_opAt`. -/
theorem eval_AAt_subst (P : ℕ → Prop) (S : ℕ → Set ℕ) (y : ℕ) (F : Semiformula LXJ ℕ 2)
    {n : ℕ} (φ : Semiformula LForm ℕ n) (f : ℕ → ℕ) (Y : Semiterm LXJ ℕ n) (e : Fin n → ℕ)
    (hYe : Semiterm.val (s := stdJ P S) e f Y = y) :
    Semiformula.Eval (s := stdJ P S) e f (AAt F Y φ) ↔
      Semiformula.Eval (s := stdJ P (Function.update S y
        {x | Semiformula.Eval (s := stdJ P S) ![x, y] f F})) e f (AAt (Jat #1 #0) Y φ) := by
  set SF : Set ℕ := {x | Semiformula.Eval (s := stdJ P S) ![x, y] f F} with hSF
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v =>
    rcases r with r | r
    · exact eval_rel_inl_congr P P S (Function.update S y SF) r (fun i => termCast (v i)) e f
    · cases r with
      | P =>
        show Semiformula.Eval (s := stdJ P S) e f (F/[termCast (v 0), Y]) ↔
          Semiformula.Eval (s := stdJ P (Function.update S y SF)) e f (Jat Y (termCast (v 0)))
        rw [Semiformula.eval_substs, eval_Jat]
        have hcomp : (Semiterm.val (s := stdJ P S) e f ∘ ![termCast (v 0), Y] : Fin 2 → ℕ)
            = ![Semiterm.val (s := stdJ P S) e f (termCast (v 0)),
                Semiterm.val (s := stdJ P S) e f Y] := Matrix.comp₂ _ _
        rw [hcomp]
        have hv0 : Semiterm.val (s := stdJ P (Function.update S y SF)) e f (termCast (v 0))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 0)) :=
          (val_stdJ_congr P S P (Function.update S y SF) e f (termCast (v 0))).symm
        have hvY : Semiterm.val (s := stdJ P (Function.update S y SF)) e f Y
            = Semiterm.val (s := stdJ P S) e f Y :=
          (val_stdJ_congr P S P (Function.update S y SF) e f Y).symm
        rw [hv0, hvY, hYe, Function.update_self]
        exact Iff.rfl
      | Q =>
        show Semiformula.Eval (s := stdJ P S) e f
            (ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1))) ↔
          Semiformula.Eval (s := stdJ P (Function.update S y SF)) e f
            (ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1)))
        have hv0 : Semiterm.val (s := stdJ P (Function.update S y SF)) e f (termCast (v 0))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 0)) :=
          (val_stdJ_congr P S P (Function.update S y SF) e f (termCast (v 0))).symm
        have hv1 : Semiterm.val (s := stdJ P (Function.update S y SF)) e f (termCast (v 1))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 1)) :=
          (val_stdJ_congr P S P (Function.update S y SF) e f (termCast (v 1))).symm
        have hvY : Semiterm.val (s := stdJ P (Function.update S y SF)) e f Y
            = Semiterm.val (s := stdJ P S) e f Y :=
          (val_stdJ_congr P S P (Function.update S y SF) e f Y).symm
        simp only [LogicalConnective.HomClass.map_and, eval_Jat, eval_ltAt]
        constructor
        · rintro ⟨hlt, hmem⟩
          have hne : Semiterm.val (s := stdJ P S) e f (termCast (v 0)) ≠ y := by
            rw [← hYe]; exact ne_of_lt hlt
          constructor
          · rw [hv0, hvY]; exact hlt
          · rw [hv0, hv1, Function.update_of_ne hne]; exact hmem
        · rintro ⟨hlt, hmem⟩
          rw [hv0, hvY] at hlt
          have hne : Semiterm.val (s := stdJ P S) e f (termCast (v 0)) ≠ y := by
            rw [← hYe]; exact ne_of_lt hlt
          rw [hv0, hv1, Function.update_of_ne hne] at hmem
          exact ⟨hlt, hmem⟩
  | hnrel r v =>
    rcases r with r | r
    · exact eval_nrel_inl_congr P P S (Function.update S y SF) r (fun i => termCast (v i)) e f
    · cases r with
      | P =>
        show Semiformula.Eval (s := stdJ P S) e f (∼(F/[termCast (v 0), Y])) ↔
          Semiformula.Eval (s := stdJ P (Function.update S y SF)) e f
            (∼(Jat Y (termCast (v 0))))
        simp only [LogicalConnective.HomClass.map_neg, Semiformula.eval_substs, eval_Jat]
        have hcomp : (Semiterm.val (s := stdJ P S) e f ∘ ![termCast (v 0), Y] : Fin 2 → ℕ)
            = ![Semiterm.val (s := stdJ P S) e f (termCast (v 0)),
                Semiterm.val (s := stdJ P S) e f Y] := Matrix.comp₂ _ _
        rw [hcomp]
        have hv0 : Semiterm.val (s := stdJ P (Function.update S y SF)) e f (termCast (v 0))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 0)) :=
          (val_stdJ_congr P S P (Function.update S y SF) e f (termCast (v 0))).symm
        have hvY : Semiterm.val (s := stdJ P (Function.update S y SF)) e f Y
            = Semiterm.val (s := stdJ P S) e f Y :=
          (val_stdJ_congr P S P (Function.update S y SF) e f Y).symm
        rw [hv0, hvY, hYe, Function.update_self]
        exact Iff.rfl
      | Q =>
        show Semiformula.Eval (s := stdJ P S) e f
            (∼(ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1)))) ↔
          Semiformula.Eval (s := stdJ P (Function.update S y SF)) e f
            (∼(ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1))))
        have hv0 : Semiterm.val (s := stdJ P (Function.update S y SF)) e f (termCast (v 0))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 0)) :=
          (val_stdJ_congr P S P (Function.update S y SF) e f (termCast (v 0))).symm
        have hv1 : Semiterm.val (s := stdJ P (Function.update S y SF)) e f (termCast (v 1))
            = Semiterm.val (s := stdJ P S) e f (termCast (v 1)) :=
          (val_stdJ_congr P S P (Function.update S y SF) e f (termCast (v 1))).symm
        have hvY : Semiterm.val (s := stdJ P (Function.update S y SF)) e f Y
            = Semiterm.val (s := stdJ P S) e f Y :=
          (val_stdJ_congr P S P (Function.update S y SF) e f Y).symm
        simp only [LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_and,
          eval_Jat, eval_ltAt]
        constructor
        · intro hn
          rintro ⟨hlt, hmem⟩
          rw [hv0, hvY] at hlt
          have hne : Semiterm.val (s := stdJ P S) e f (termCast (v 0)) ≠ y := by
            rw [← hYe]; exact ne_of_lt hlt
          rw [hv0, hv1, Function.update_of_ne hne] at hmem
          exact hn ⟨hlt, hmem⟩
        · intro hn
          rintro ⟨hlt, hmem⟩
          have hne : Semiterm.val (s := stdJ P S) e f (termCast (v 0)) ≠ y := by
            rw [← hYe]; exact ne_of_lt hlt
          apply hn
          refine ⟨?_, ?_⟩
          · rw [hv0, hvY]; exact hlt
          · rw [hv0, hv1, Function.update_of_ne hne]; exact hmem
  | hand φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := stdJ P S) e f (AAt F Y φ ⋏ AAt F Y ψ) ↔
      Semiformula.Eval (s := stdJ P (Function.update S y SF)) e f (AAt (Jat #1 #0) Y φ ⋏ AAt (Jat #1 #0) Y ψ)
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact and_congr (ihφ Y e hYe) (ihψ Y e hYe)
  | hor φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := stdJ P S) e f (AAt F Y φ ⋎ AAt F Y ψ) ↔
      Semiformula.Eval (s := stdJ P (Function.update S y SF)) e f (AAt (Jat #1 #0) Y φ ⋎ AAt (Jat #1 #0) Y ψ)
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact or_congr (ihφ Y e hYe) (ihψ Y e hYe)
  | hall φ ih =>
    show Semiformula.Eval (s := stdJ P S) e f (∀¹ AAt F (Rew.bShift Y) φ) ↔
      Semiformula.Eval (s := stdJ P (Function.update S y SF)) e f (∀¹ AAt (Jat #1 #0) (Rew.bShift Y) φ)
    rw [Semiformula.eval_all, Semiformula.eval_all]
    exact forall_congr' fun x =>
      ih (Rew.bShift Y) (x :> e) (by rw [Semiterm.val_bShift]; exact hYe)
  | hexs φ ih =>
    show Semiformula.Eval (s := stdJ P S) e f (∃¹ AAt F (Rew.bShift Y) φ) ↔
      Semiformula.Eval (s := stdJ P (Function.update S y SF)) e f (∃¹ AAt (Jat #1 #0) (Rew.bShift Y) φ)
    rw [Semiformula.eval_ex, Semiformula.eval_ex]
    exact exists_congr fun x =>
      ih (Rew.bShift Y) (x :> e) (by rw [Semiterm.val_bShift]; exact hYe)

/-! ### Bridging the `ξ = Empty` and `ξ = ℕ` copies of `A` -/

/-- `termCast` commutes with `Rew.emb`. -/
theorem termCast_emb {ξ : Type*} {n : ℕ} (t : Semiterm LForm Empty n) :
    termCast (Rew.emb t : Semiterm LForm ξ n) = (Rew.emb (termCast t) : Semiterm LXJ ξ n) := by
  simp only [termCast, Rew.emb, Semiterm.lMap_map]

/-- `Rewriting.emb` commutes with `Jat`. -/
theorem Jat_emb {ξ : Type*} {n : ℕ} (s t : Semiterm LXJ Empty n) :
    (Rewriting.emb (Jat s t) : Semiformula LXJ ξ n) = Jat (Rew.emb s) (Rew.emb t) := by
  show (Semiformula.rel (Sum.inr XJRel.J) (Rew.emb ∘ ![s, t]) : Semiformula LXJ ξ n) =
      Semiformula.rel (Sum.inr XJRel.J) ![Rew.emb s, Rew.emb t]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- `Rewriting.emb` commutes with `ltAt`. -/
theorem ltAt_emb {ξ : Type*} {n : ℕ} (s t : Semiterm LXJ Empty n) :
    (Rewriting.emb (ltAt s t) : Semiformula LXJ ξ n) = ltAt (Rew.emb s) (Rew.emb t) := by
  show (Semiformula.rel (Sum.inl (Language.LT.lt : (ℒₒᵣ).Rel 2)) (Rew.emb ∘ ![s, t])
      : Semiformula LXJ ξ n) =
      Semiformula.rel (Sum.inl (Language.LT.lt : (ℒₒᵣ).Rel 2)) ![Rew.emb s, Rew.emb t]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **`AAt (Jat #1 #0) Y (Rewriting.emb A)` equals `Rewriting.emb (AAt (Jat #1 #0) Y₀ A)`**:
compiling the `ξ = ℕ` copy of `A` gives the same formula as embedding the compiled
`ξ = Empty` copy. -/
theorem AAt_emb {ξ : Type*} {n : ℕ} (φ : Semiformula LForm Empty n) (Y₀ : Semiterm LXJ Empty n) :
    AAt (ξ := ξ) (Jat #1 #0) (Rew.emb Y₀) (Rewriting.emb φ) =
      (Rewriting.emb (AAt (ξ := Empty) (Jat #1 #0) Y₀ φ) : Semiformula LXJ ξ n) := by
  induction φ using Semiformula.rec' with
  | hverum => simp [AAt]
  | hfalsum => simp [AAt]
  | hrel r v =>
    rcases r with r | r
    · show (Semiformula.rel (Sum.inl r) (fun i => termCast (Rew.emb (v i))) : Semiformula LXJ ξ _)
          = Semiformula.rel (Sum.inl r) (fun i => Rew.emb (termCast (v i)))
      congr 1; funext i; exact termCast_emb (v i)
    · cases r with
      | P =>
        have step1 : (Rewriting.emb (Semiformula.rel (Sum.inr PQRel.P) v) : Semiformula LForm ξ _)
            = Semiformula.rel (Sum.inr PQRel.P) (fun i => Rew.emb (v i)) := rfl
        have step2 : AAt (ξ := ξ) (Jat #1 #0) (Rew.emb Y₀)
            (Semiformula.rel (Sum.inr PQRel.P) (fun i => Rew.emb (v i)))
            = (Jat #1 #0 : Semiformula LXJ ξ 2)/[termCast (Rew.emb (v 0)), Rew.emb Y₀] := rfl
        have step3 : (AAt (ξ := Empty) (Jat #1 #0) Y₀ (Semiformula.rel (Sum.inr PQRel.P) v))
            = (Jat #1 #0 : Semiformula LXJ Empty 2)/[termCast (v 0), Y₀] := rfl
        have hF : (Rewriting.emb (Jat #1 #0 : Semiformula LXJ Empty 2) : Semiformula LXJ ξ 2)
            = Jat #1 #0 := by rw [Jat_emb]; simp
        rw [step1, step2, step3, Rewriting.emb_subst_eq_subst_emb, hF]
        congr 1
        funext i
        fin_cases i <;> simp [termCast_emb]
      | Q =>
        have step1 : (Rewriting.emb (Semiformula.rel (Sum.inr PQRel.Q) v) : Semiformula LForm ξ _)
            = Semiformula.rel (Sum.inr PQRel.Q) (fun i => Rew.emb (v i)) := rfl
        have step2 : AAt (ξ := ξ) (Jat #1 #0) (Rew.emb Y₀)
            (Semiformula.rel (Sum.inr PQRel.Q) (fun i => Rew.emb (v i)))
            = ltAt (termCast (Rew.emb (v 0))) (Rew.emb Y₀) ⋏
              Jat (termCast (Rew.emb (v 0))) (termCast (Rew.emb (v 1))) := rfl
        have step3 : (AAt (ξ := Empty) (Jat #1 #0) Y₀ (Semiformula.rel (Sum.inr PQRel.Q) v))
            = ltAt (termCast (v 0)) Y₀ ⋏ Jat (termCast (v 0)) (termCast (v 1)) := rfl
        have hemb : (Rewriting.emb
              (ltAt (termCast (v 0)) Y₀ ⋏ Jat (termCast (v 0)) (termCast (v 1)))
              : Semiformula LXJ ξ _)
            = ltAt (Rew.emb (termCast (v 0))) (Rew.emb Y₀) ⋏
              Jat (Rew.emb (termCast (v 0))) (Rew.emb (termCast (v 1))) := by
          simp [ltAt_emb, Jat_emb]
        rw [step1, step2, step3, hemb, termCast_emb, termCast_emb]
  | hnrel r v =>
    rcases r with r | r
    · show (Semiformula.nrel (Sum.inl r) (fun i => termCast (Rew.emb (v i))) : Semiformula LXJ ξ _)
          = Semiformula.nrel (Sum.inl r) (fun i => Rew.emb (termCast (v i)))
      congr 1; funext i; exact termCast_emb (v i)
    · cases r with
      | P =>
        have step1 : (Rewriting.emb (Semiformula.nrel (Sum.inr PQRel.P) v) : Semiformula LForm ξ _)
            = Semiformula.nrel (Sum.inr PQRel.P) (fun i => Rew.emb (v i)) := rfl
        have step2 : AAt (ξ := ξ) (Jat #1 #0) (Rew.emb Y₀)
            (Semiformula.nrel (Sum.inr PQRel.P) (fun i => Rew.emb (v i)))
            = ∼((Jat #1 #0 : Semiformula LXJ ξ 2)/[termCast (Rew.emb (v 0)), Rew.emb Y₀]) := rfl
        have step3 : (AAt (ξ := Empty) (Jat #1 #0) Y₀ (Semiformula.nrel (Sum.inr PQRel.P) v))
            = ∼((Jat #1 #0 : Semiformula LXJ Empty 2)/[termCast (v 0), Y₀]) := rfl
        have hemb : (Rewriting.emb (∼((Jat #1 #0 : Semiformula LXJ Empty 2)/[termCast (v 0), Y₀]))
              : Semiformula LXJ ξ _)
            = ∼(Rewriting.emb ((Jat #1 #0 : Semiformula LXJ Empty 2)/[termCast (v 0), Y₀])) := rfl
        have hF : (Rewriting.emb (Jat #1 #0 : Semiformula LXJ Empty 2) : Semiformula LXJ ξ 2)
            = Jat #1 #0 := by rw [Jat_emb]; simp
        rw [step1, step2, step3, hemb, Rewriting.emb_subst_eq_subst_emb, hF]
        congr 1
        congr 1
        funext i
        fin_cases i <;> simp [termCast_emb]
      | Q =>
        have step1 : (Rewriting.emb (Semiformula.nrel (Sum.inr PQRel.Q) v) : Semiformula LForm ξ _)
            = Semiformula.nrel (Sum.inr PQRel.Q) (fun i => Rew.emb (v i)) := rfl
        have step2 : AAt (ξ := ξ) (Jat #1 #0) (Rew.emb Y₀)
            (Semiformula.nrel (Sum.inr PQRel.Q) (fun i => Rew.emb (v i)))
            = ∼(ltAt (termCast (Rew.emb (v 0))) (Rew.emb Y₀) ⋏
                Jat (termCast (Rew.emb (v 0))) (termCast (Rew.emb (v 1)))) := rfl
        have step3 : (AAt (ξ := Empty) (Jat #1 #0) Y₀ (Semiformula.nrel (Sum.inr PQRel.Q) v))
            = ∼(ltAt (termCast (v 0)) Y₀ ⋏ Jat (termCast (v 0)) (termCast (v 1))) := rfl
        have hemb : (Rewriting.emb
              (∼(ltAt (termCast (v 0)) Y₀ ⋏ Jat (termCast (v 0)) (termCast (v 1))))
              : Semiformula LXJ ξ _)
            = ∼(ltAt (Rew.emb (termCast (v 0))) (Rew.emb Y₀) ⋏
                Jat (Rew.emb (termCast (v 0))) (Rew.emb (termCast (v 1)))) := by
          simp [ltAt_emb, Jat_emb]
        rw [step1, step2, step3, hemb, termCast_emb, termCast_emb]
  | hand φ ψ ihφ ihψ => simp [AAt, ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [AAt, ihφ, ihψ]
  | hall φ ih => simp [AAt, Rew.emb_bShift_term, ih]
  | hexs φ ih => simp [AAt, Rew.emb_bShift_term, ih]

/-- The eval-level form of `AAt_emb`, at `Y₀ := #1` and `n := 2` (the only instance
`indAxJ`/`opJ` need). -/
theorem eval_AAt_emb (P : ℕ → Prop) (S : ℕ → Set ℕ) (φ : Semiformula LForm Empty 2)
    (e : Fin 2 → ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := stdJ P S) e f
        (AAt (Jat #1 #0) (Rew.emb (#1 : Semiterm LXJ Empty 2)) (Rewriting.emb φ)) ↔
      Semiformula.Eval (s := stdJ P S) e Empty.elim (AAt (Jat #1 #0) (#1 : Semiterm LXJ Empty 2) φ) := by
  rw [AAt_emb, Semiformula.eval_emb]

/-! ### The operator at one level, and its least fixed point -/

section Operator

variable (P : ℕ → Prop) (A : FormJ)

/-- **The operator of level `y`**, as a function of the whole environment `S` and the
candidate `T` for `J`'s `y`-th column: `x ∈ opJ P A S y T` iff `A_y(J(y,·), x)` holds in
`stdJ P (update S y T)`. -/
def opJ (S : ℕ → Set ℕ) (y : ℕ) (T : Set ℕ) : Set ℕ :=
  {x | Semiformula.Eval (s := stdJ P (Function.update S y T)) ![x, y] Empty.elim
    (AAt (ξ := Empty) (Jat #1 #0) #1 A)}

/-- A `PositiveP` form's operator is monotone in the candidate `T`. -/
theorem opJ_mono_at (hA : PositiveP A) (lower : ℕ → Set ℕ) (y : ℕ) :
    Monotone (fun T => opJ P A lower y T) := by
  intro a b hab x hx
  refine AAt_monotone_of_positive P y (S := Function.update lower y a)
    (S' := Function.update lower y b) ?_ ?_ A hA (#1 : Semiterm LXJ Empty 2) ![x, y]
    Empty.elim rfl hx
  · rw [Function.update_self, Function.update_self]; exact hab
  · intro j hj
    rw [Function.update_of_ne hj, Function.update_of_ne hj]

/-- **The least fixed point of level `y`**, the other coordinates held at `lower`. -/
def lfpAt (lower : ℕ → Set ℕ) (y : ℕ) : Set ℕ :=
  sInf {T | opJ P A lower y T ⊆ T}

/-- The least fixed point at level `y` is contained in every closed set. -/
theorem lfpAt_subset (lower : ℕ → Set ℕ) (y : ℕ) {T : Set ℕ}
    (h : opJ P A lower y T ⊆ T) : lfpAt P A lower y ⊆ T :=
  sInf_le h

/-- The least fixed point at level `y` is closed under its operator, when `A` is
`PositiveP`. -/
theorem opJ_lfpAt_subset (hA : PositiveP A) (lower : ℕ → Set ℕ) (y : ℕ) :
    opJ P A lower y (lfpAt P A lower y) ⊆ lfpAt P A lower y :=
  le_sInf fun _ hT =>
    (opJ_mono_at P A hA lower y (lfpAt_subset P A lower y hT)).trans hT

end Operator

/-! ### The chain: assembling all the levels -/

section Chain

variable (P : ℕ → Prop) (A : FormJ)

/-- **The iterated least fixed point**, one level at a time, by well-founded recursion on
`<`: level `y` is solved against an environment that is `∅` at every level not yet
built. -/
noncomputable def lfpChain : ℕ → Set ℕ :=
  WellFounded.fix (wellFounded_lt (α := ℕ)) fun y rec =>
    lfpAt P A (fun j => if h : j < y then rec j h else ∅) y

theorem lfpChain_eq (y : ℕ) :
    lfpChain P A y = lfpAt P A (fun j => if _ : j < y then lfpChain P A j else ∅) y :=
  WellFounded.fix_eq (wellFounded_lt (α := ℕ)) _ y

/-- The truncated environment used to build level `y` agrees with the full chain at
every level `< y`, and (once updated at `y`) at every level `≤ y`. -/
theorem lfpChain_agree (y : ℕ) :
    ∀ j, j ≤ y → Function.update (fun j => if _ : j < y then lfpChain P A j else ∅) y
      (lfpChain P A y) j = lfpChain P A j := by
  intro j hj
  rcases eq_or_ne j y with rfl | hne
  · rw [Function.update_self]
  · rw [Function.update_of_ne hne]
    exact dif_pos (lt_of_le_of_ne hj hne)

end Chain

/-! ### Soundness of the closure and induction axioms -/

section Axioms

variable (P : ℕ → Prop) (A : FormJ)

/-- **The closure axiom is true** in `stdJ P (lfpChain P A)`. -/
theorem eval_closureAxJ (hA : PositiveP A) :
    Semiformula.Eval (s := stdJ P (lfpChain P A)) ![] Empty.elim (closureAxJ A) := by
  rw [closureAxJ, Semiformula.eval_all]
  intro y
  rw [Semiformula.eval_all]
  intro x
  rw [LogicalConnective.HomClass.map_imply]
  intro hx
  set lower : ℕ → Set ℕ := fun j => if h : j < y then lfpChain P A j else ∅ with hlower
  have hagree : ∀ j, j ≤ y →
      lfpChain P A j = Function.update lower y (lfpChain P A y) j :=
    fun j hj => (lfpChain_agree P A y j hj).symm
  have hx' : x ∈ opJ P A lower y (lfpAt P A lower y) := by
    rw [← lfpChain_eq]
    have := agreeBelowJ P y hagree A (#1 : Semiterm LXJ Empty 2) (x :> y :> ![]) Empty.elim rfl
    exact this.mp hx
  have := opJ_lfpAt_subset P A hA lower y hx'
  rw [← lfpChain_eq] at this
  rw [eval_Jat]
  exact this

/-- **Every instance of the induction scheme is true** in `stdJ P (lfpChain P A)`. Positivity
is not needed. -/
theorem eval_indAxJ (F : Semiformula LXJ ℕ 2) :
    Semiformula.Eval (s := stdJ P (lfpChain P A)) ![] Empty.elim (indAxJ A F) := by
  rw [indAxJ]
  refine (Semiformula.eval_univCl (s := stdJ P (lfpChain P A)) _).mpr ?_
  intro f
  simp only [Semiformula.Evalf, LogicalConnective.HomClass.map_imply, Semiformula.eval_all]
  intro y hcl x hx
  rw [eval_Jat] at hx
  set lower : ℕ → Set ℕ := fun j => if h : j < y then lfpChain P A j else ∅ with hlower
  set SF : Set ℕ :=
    {z | Semiformula.Eval (s := stdJ P (lfpChain P A)) ![z, y] f F} with hSF
  have hagree : ∀ j, j ≤ y →
      Function.update lower y SF j = Function.update (lfpChain P A) y SF j := by
    intro j hj
    rcases eq_or_ne j y with rfl | hne
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact dif_pos (lt_of_le_of_ne hj hne)
  have hclosed : opJ P A lower y SF ⊆ SF := by
    intro z hz
    have hz' : z ∈ opJ P A (lfpChain P A) y SF :=
      (agreeBelowJ P y hagree A (#1 : Semiterm LXJ Empty 2) ![z, y] Empty.elim rfl).mp hz
    have hAF : Semiformula.Eval (s := stdJ P (lfpChain P A)) ![z, y] f
        (AAt F (#1 : Semiterm LXJ ℕ 2) (Rewriting.emb A)) := by
      rw [eval_AAt_subst P (lfpChain P A) y F (Rewriting.emb A) f (#1 : Semiterm LXJ ℕ 2)
        ![z, y] rfl]
      have := (eval_AAt_emb P (Function.update (lfpChain P A) y SF) A ![z, y] f).mpr hz'
      exact this
    exact hcl z hAF
  have hsub := lfpAt_subset P A lower y hclosed
  rw [← lfpChain_eq] at hsub
  exact hsub hx

end Axioms

/-! ### The axioms of `paLXJ` -/

section PA

variable (P : ℕ → Prop) (S : ℕ → Set ℕ)

set_option linter.style.haveILetI false in
/-- Every equality axiom is true in `stdJ P S`. -/
theorem eval_of_eqAxiom {σ : Sentence LXJ} (h : σ ∈ 𝗘𝗤 LXJ) :
    Semiformula.Eval (s := stdJ P S) ![] Empty.elim σ := by
  letI : Structure LXJ ℕ := stdJ P S
  haveI : Structure.Eq LXJ ℕ := ⟨fun _ _ => iff_of_eq rfl⟩
  haveI : ℕ↓[LXJ] ⊧* 𝗘𝗤 LXJ := Structure.Eq.models_eq LXJ ℕ
  exact Theory.models ℕ (𝗘𝗤 LXJ) h

/-- Every transported axiom of `𝗣𝗔⁻` is true in `stdJ P S`. -/
theorem eval_of_paMinus {σ : Sentence LXJ} (h : σ ∈ Theory.lMap toLXJ 𝗣𝗔⁻) :
    Semiformula.Eval (s := stdJ P S) ![] Empty.elim σ := by
  obtain ⟨τ, hτ, rfl⟩ := h
  rw [eval_lMap_toLXJ]
  exact Theory.models ℕ 𝗣𝗔⁻ hτ

/-- Every induction axiom is true in `stdJ P S`: induction on `ℕ`. -/
theorem eval_of_succInd {σ : Sentence LXJ} (h : σ ∈ InductionScheme LXJ Set.univ) :
    Semiformula.Eval (s := stdJ P S) ![] Empty.elim σ := by
  obtain ⟨φ, -, rfl⟩ := h
  refine (Semiformula.eval_univCl (s := stdJ P S) _).mpr ?_
  intro f
  show Semiformula.Eval (s := stdJ P S) ![] f ((φ/[((0 : ℕ) : Semiterm LXJ ℕ 0)]) 🡒
      (∀¹ (φ/[(#0 : Semiterm LXJ ℕ 1)] 🡒 φ/[(‘(#0 + 1)’ : Semiterm LXJ ℕ 1)])) 🡒
      ∀¹ (φ/[(#0 : Semiterm LXJ ℕ 1)]))
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_all,
    Semiformula.eval_substs, Matrix.comp₁]
  intro h0 hs x
  induction x with
  | zero => exact h0
  | succ k ih => exact hs k ih

/-- `stdJ P S` is a model of `paLXJ`, for every `P` and `S`. -/
theorem models_paLXJ :
    letI := stdJ P S; ℕ↓[LXJ] ⊧* paLXJ := by
  let _ : Structure LXJ ℕ := stdJ P S
  refine Semantics.modelsSet_iff.mpr fun σ hσ => models_iff.mpr ?_
  rcases hσ with h | h | h
  · exact eval_of_eqAxiom P S h
  · exact eval_of_paMinus P S h
  · exact eval_of_succInd P S h

end PA

/-! ### Soundness and consistency -/

section Soundness

variable (A : FormJ)

/-- Every axiom of `IDw A` is true in `stdJ P (lfpChain P A)`, given `PositiveP A`. -/
theorem eval_of_mem_IDw (hA : PositiveP A) (P : ℕ → Prop) {σ : Sentence LXJ}
    (h : σ ∈ IDw A) :
    Semiformula.Eval (s := stdJ P (lfpChain P A)) ![] Empty.elim σ := by
  rcases (mem_IDw A).mp h with rfl | h | ⟨F, rfl⟩
  · exact eval_closureAxJ P A hA
  · rcases h with h | h | h
    · exact eval_of_eqAxiom P _ h
    · exact eval_of_paMinus P _ h
    · exact eval_of_succInd P _ h
  · exact eval_indAxJ P A F

/-- **Soundness of `IDw A`**: for a `PositiveP` form `A` and every reading `P` of `X`, the
standard structure with `J` read as the ℕ-indexed chain of least fixed points is a model of
`IDw A`. -/
theorem models_IDw (hA : PositiveP A) (P : ℕ → Prop) :
    letI := stdJ P (lfpChain P A); ℕ↓[LXJ] ⊧* IDw A := by
  let _ : Structure LXJ ℕ := stdJ P (lfpChain P A)
  exact Semantics.modelsSet_iff.mpr fun σ hσ => models_iff.mpr (eval_of_mem_IDw A hA P hσ)

/-- **Every theorem of `IDw A` is true in the standard model.** -/
theorem eval_of_provable_IDw (hA : PositiveP A) (P : ℕ → Prop) {σ : Sentence LXJ}
    (h : IDw A ⊢ σ) :
    Semiformula.Eval (s := stdJ P (lfpChain P A)) ![] Empty.elim σ := by
  let _ : Structure LXJ ℕ := stdJ P (lfpChain P A)
  exact models_iff.mp (models_of_provable (models_IDw A hA P) h)

/-- **`IDw A` does not prove `⊥`**, for every `PositiveP` form `A`. -/
theorem IDw_unprovable_bot (hA : PositiveP A) : IDw A ⊬ (⊥ : Sentence LXJ) := by
  intro h
  have := eval_of_provable_IDw A hA (fun _ => False) h
  simp at this

/-- **`IDw A` is consistent**, for every `PositiveP` form `A`. -/
theorem IDw_consistent (hA : PositiveP A) : Entailment.Consistent (IDw A) :=
  Entailment.consistent_iff_exists_unprovable.mpr ⟨⊥, IDw_unprovable_bot A hA⟩

end Soundness

end IDw

end OrdinalAnalysis
