/-
  The stage semantics of `ID_{<ω}^∞`, and soundness below `Ω₁`.

  This is the multi-level analogue of `OrdinalAnalysis.ID1.StageSemantics`. Source for the one-level construction:
  A. Freund, *Impredicativity and trees with gap condition: a second course on ordinal
  analysis*, arXiv:2204.09321, §5; Buchholz, *A simplified version of local predicativity*
  (1992), §3–4 (Thm 4.9 (6)–(8): the level-0 collapse ends in the stage model, with cuts).

  **The stages, iterated.**  For `n` operator forms `A k`, `k : Fin n`, and a reading `P` of
  the free predicate `X`, level `k`'s stages are built by well-founded recursion on the
  notations *within* the level (`stageWithin`, the direct analogue of `ID1.stageSet`'s
  recursion), reading every *other* level `j` at its own top `Ω_{j+1}` — for `j < k` this is
  the value already built at a strictly lower level; for `j ≥ k` it is a placeholder (`∅`)
  that is never actually read once `A k` is `LevelBounded k`. Assembling all `n` levels is a
  second, outer well-founded recursion on `Fin n` (`stageFamily`), exactly as
  `IDn.Sound.lfpChain` assembles the least fixed points level by level — here each step
  builds an entire *family* of stages `StageAt k.val → Set ℕ`, not just its top value:

      S^k_a  :=  ⋃_{γ≺a} Γ_{A_k}(S^k_γ),        Γ_{A_k}(T) = the set A_k defines at `T`,

  every other level `j` read by `S^j_{Ω_{j+1}}` (design note §2.6). No positivity of any `A k`
  is needed for this recursion, and none for soundness: the stage rules are sound because the
  stages satisfy their defining equation. `LevelBounded k (A k)` *is* needed, to relate the
  placeholder environment used inside the recursion (`∅` above level `k`) to the real one used
  by the full stage model (`Sound.levelBounded_agree`, reused verbatim) — this bookkeeping has
  no one-level analogue in `ID1`, where "other levels" is vacuous.

  **The stage model** `stageModelN P A` is the `LIinfN n`-structure on `ℕ` with standard
  arithmetic, `X` read by `P`, and every stage predicate `I_k^{≺a}` (`a ⪯ Ω_{k+1}`) read by
  `stageSetN P A ⟨k,a⟩`. At `a = Ω_{k+1}` this is `⋃_{γ≺Ω_{k+1}} Γ_{A_k}(S^k_γ)`, which is in
  general not closed under `Γ_{A_k}`; this is why (Fix_k) is not sound at any level, and why
  soundness is only claimed for heights `α ≺ Ω₁` — which excludes every level's (Fix), since
  (Fix_k) needs `Ω_{k+1} ⪯ α` and `Ω_{k+1} ⪰ Ω₁` for every `k`.

  **Soundness** (`sound`): if `H ⊢^α_ρ Γ` (`IDnDerivable A ρ H α Γ`), the family `A` is
  level-bounded, and `α ≺ Ω₁`, then some formula of `Γ` is true in the stage model, for every
  `ρ`, `H` and `P` (free variables read as `0`). Cuts are sound whatever their rank.

  Contents.

    `iinfStrucN`, `stageStrucN`                          `X ↦ P`, `I_k^{≺a} ↦ S ⟨k,a⟩`
    `val_stageStrucN_congr`, `val_numeral_stageStrucN`    term values
    `eval_stageAt`, `eval_XinfAt`                         the fresh atoms
    `stageEnvAt`, `lMap_stageHom_stageStrucN`, `eval_unfold`   `A_k(t, I_k^{≺a})`
    `stageWithin`, `stageFamily`, `stageSetN`             **the iterated stages**
    `stageWithin_eq`, `mem_stageWithin_iff`, `stageFamily_eq`, `mem_stageSetN_iff`
    `stageModelN`, `TrueSN`                               the stage model and truth in it
    `omega_zero_le`                                       `Ω₁ ⪯ Ω_{k+1}` for every level `k`
    `sound`                                                **the truth lemma**
-/
import OrdinalAnalysis.IDn.Calculus
import OrdinalAnalysis.IDn.Sound

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

namespace StageSem

open LO LO.FirstOrder

variable {n : ℕ}

/-! ### Structures reading the stages by a given family of sets -/

/-- The fresh symbols of `LIinfN n`: `X` read by `P`, the stage `I_k^{≺a}` by `S ⟨k,a⟩`. -/
@[instance_reducible]
def iinfStrucN (P : ℕ → Prop) (S : Stage n → Set ℕ) : Structure (IInfLangN n) ℕ where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ r v => match r with
    | IInfRelN.X => P (v 0)
    | IInfRelN.stage s => v 0 ∈ S s

/-- The `LIinfN n`-structure on `ℕ`: arithmetic standard, `X` read by `P`, `I_k^{≺a}` by
`S ⟨k,a⟩`. -/
@[instance_reducible]
def stageStrucN (P : ℕ → Prop) (S : Stage n → Set ℕ) : Structure (LIinfN n) ℕ :=
  Structure.add ℒₒᵣ (IInfLangN n) ℕ (str₂ := iinfStrucN P S)

section Struc

variable (P : ℕ → Prop) (S : Stage n → Set ℕ)

/-- Term values do not depend on the readings of the fresh predicates. -/
theorem val_stageStrucN_congr {ξ : Type*} {m : ℕ} (e : Fin m → ℕ) (f : ξ → ℕ)
    (t : Semiterm (LIinfN n) ξ m) :
    Semiterm.val (s := stageStrucN P S) e f t = Semiterm.val (s := stdInfN) e f t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func fn v ih =>
      simp only [Semiterm.val_func, Function.comp_def, ih]
      rcases fn with fn | fn
      · rfl
      · exact PEmpty.elim fn

/-- The numerals of `LIinfN n` are the images of the numerals of arithmetic. -/
theorem numeral_lMap_toLIinfN {ξ : Type*} {m : ℕ} (t : ℕ) :
    Semiterm.lMap (toLIinfN n) ((t : ℕ) : Semiterm ℒₒᵣ ξ m) = ((t : ℕ) : Semiterm (LIinfN n) ξ m) := by
  have h0 : Semiterm.lMap (toLIinfN n) ((0 : ℕ) : Semiterm ℒₒᵣ ξ m) =
      ((0 : ℕ) : Semiterm (LIinfN n) ξ m) := by
    simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
      Semiterm.Operator.Zero.term_eq, toLIinfN]
  have h1 : Semiterm.lMap (toLIinfN n) ((1 : ℕ) : Semiterm ℒₒᵣ ξ m) =
      ((1 : ℕ) : Semiterm (LIinfN n) ξ m) := by
    simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
      Semiterm.Operator.One.term_eq, toLIinfN]
  have hadd : ∀ v : Fin 2 → Semiterm ℒₒᵣ ξ m,
      Semiterm.lMap (toLIinfN n) (Semiterm.Operator.Add.add.operator v) =
        Semiterm.Operator.Add.add.operator (Semiterm.lMap (toLIinfN n) ∘ v) := by
    intro v
    simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, toLIinfN]
    funext i
    simp
  have hss : ∀ (L : Language) [L.Zero] [L.One] [L.Add] (t : ℕ),
      ((t + 1 + 1 : ℕ) : Semiterm L ξ m) =
        Semiterm.Operator.Add.add.operator
          ![((t + 1 : ℕ) : Semiterm L ξ m), ((1 : ℕ) : Semiterm L ξ m)] := by
    intro L _ _ _ t
    have h : t + 1 ≠ 0 := Nat.succ_ne_zero t
    simp only [Semiterm.numeral, Semiterm.Operator.const,
      Semiterm.Operator.numeral_succ h, Semiterm.Operator.operator_comp]
    congr 1
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  induction t with
  | zero => exact h0
  | succ t ih =>
    cases t with
    | zero => exact h1
    | succ t =>
      rw [hss ℒₒᵣ t, hss (LIinfN n) t, hadd]
      congr 1
      funext i
      match i with
      | ⟨0, _⟩ => exact ih
      | ⟨1, _⟩ => exact h1

/-- **A numeral denotes its value.** -/
@[simp] theorem val_numeral_stageStrucN {ξ : Type*} {m : ℕ} (t : ℕ) (e : Fin m → ℕ)
    (f : ξ → ℕ) :
    Semiterm.val (s := stageStrucN P S) e f ((t : ℕ) : Semiterm (LIinfN n) ξ m) = t := by
  rw [← numeral_lMap_toLIinfN t]
  show Semiterm.val (s := Structure.add ℒₒᵣ (IInfLangN n) ℕ (str₂ := iinfStrucN P S)) e f
    (Semiterm.lMap (Language.Hom.add₁ ℒₒᵣ (IInfLangN n)) ((t : ℕ) : Semiterm ℒₒᵣ ξ m)) = t
  rw [Structure.val_lMap_add₁ (str₂ := iinfStrucN P S)]
  simp

/-- `I_k^{≺a} t` holds when the value of `t` lies in `S ⟨k,a⟩`. -/
theorem eval_stageAt {ξ : Type*} {m : ℕ} (s : Stage n) (t : Semiterm (LIinfN n) ξ m)
    (e : Fin m → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stageStrucN P S) e f (stageAt s t) ↔
      Semiterm.val (s := stageStrucN P S) e f t ∈ S s := by
  have h : (Semiterm.val (s := stageStrucN P S) e f ∘ ![t] : Fin 1 → ℕ)
      = ![Semiterm.val (s := stageStrucN P S) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg ((stageStrucN P S).rel (Sum.inr (IInfRelN.stage s))) h)

/-- `X t` holds when `P` holds at the value of `t`. -/
theorem eval_XinfAt {ξ : Type*} {m : ℕ} (t : Semiterm (LIinfN n) ξ m) (e : Fin m → ℕ)
    (f : ξ → ℕ) :
    Semiformula.Eval (s := stageStrucN P S) e f (XinfAt t) ↔
      P (Semiterm.val (s := stageStrucN P S) e f t) := by
  have h : (Semiterm.val (s := stageStrucN P S) e f ∘ ![t] : Fin 1 → ℕ)
      = ![Semiterm.val (s := stageStrucN P S) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg ((stageStrucN P S).rel (Sum.inr IInfRelN.X)) h)

/-- **The environment `stageHom k a` reduces `stageStrucN P S` to**: every level `j ≠ k` read
by `S` at its own top, level `k` read by `S` at the bound `a`. -/
def stageEnvAt (S : Stage n → Set ℕ) (k : Fin n) (a : StageAt k.val) : Fin n → Set ℕ :=
  fun j => if _ : j = k then S (⟨k, a⟩ : Stage n) else S (Stage.top j)

/-- Reading `I_k ↦ I_k^{≺a}` (every other level at its own top) back: the reduct of the stage
structure along `stageHom k a` is the standard `LXIn n`-structure with the environment
`stageEnvAt S k a`. -/
theorem lMap_stageHom_stageStrucN (k : Fin n) (a : StageAt k.val) :
    (stageStrucN P S).lMap (stageHom k a) = stdIN P (stageEnvAt S k a) := by
  have hf : ((stageStrucN P S).lMap (stageHom k a)).func = (stdIN P (stageEnvAt S k a)).func := by
    funext m fn v
    rcases fn with fn | fn
    · rfl
    · exact PEmpty.elim fn
  have hr : ((stageStrucN P S).lMap (stageHom k a)).rel = (stdIN P (stageEnvAt S k a)).rel := by
    funext m r v
    rcases r with r | r
    · rfl
    · cases r with
      | X => rfl
      | I j =>
        show (stageStrucN P S).rel (stageRel k a (Sum.inr (IXRelN.I j))) v =
          (v 0 ∈ stageEnvAt S k a j)
        by_cases h : j = k
        · subst h
          rw [stageRel_I, dif_pos rfl]
          show (v 0 ∈ S (⟨j, a⟩ : Stage n)) = (v 0 ∈ stageEnvAt S j a j)
          rw [stageEnvAt, dif_pos rfl]
        · rw [stageRel_I, dif_neg h]
          show (v 0 ∈ S (Stage.top j)) = (v 0 ∈ stageEnvAt S k a j)
          rw [stageEnvAt, dif_neg h]
  cases h : (stageStrucN P S).lMap (stageHom k a)
  cases h' : stdIN P (stageEnvAt S k a)
  rw [h] at hf hr
  rw [h'] at hf hr
  cases hf
  cases hr
  rfl

/-- **`A_k(t, I_k^{≺a})` holds exactly when the value of `t` is in the operator of level `k`
applied to `stageEnvAt S k a`.** -/
theorem eval_unfold (A : Fin n → Semisentence (LXIn n) 1) (k : Fin n) (a : StageAt k.val)
    {ξ : Type*} {m : ℕ} (t : Semiterm (LIinfN n) ξ m) (e : Fin m → ℕ) (f : ξ → ℕ) :
    Semiformula.Eval (s := stageStrucN P S) e f (unfold (A k) k a t) ↔
      Semiterm.val (s := stageStrucN P S) e f t ∈ opA P A k (stageEnvAt S k a) := by
  rw [unfold, Semiformula.eval_substs, Matrix.comp₁, Semiformula.eval_emb, formAt,
    Semiformula.eval_lMap, lMap_stageHom_stageStrucN]
  rfl

/-- A closed literal of arithmetic has the truth value it has in `ℕ`. -/
theorem eval_of_trueLit {φ : Proposition (LIinfN n)} (h : TrueLit φ) :
    Semiformula.Eval (s := stageStrucN P S) ![] (fun _ => 0) φ := by
  obtain ⟨⟨j, r, v, hφ, -⟩, ht⟩ := h
  unfold TrueN at ht
  have e : (fun i => Semiterm.val (s := stageStrucN P S) ![] (fun _ => 0) (v i)) =
      (fun i => Semiterm.val (s := stdInfN) ![] (fun _ => 0) (v i)) := by
    funext i
    exact val_stageStrucN_congr P S _ _ (v i)
  rcases hφ with rfl | rfl
  · have ht' : Structure.rel (L := ℒₒᵣ) (M := ℕ) r
        (fun i => Semiterm.val (s := stdInfN) ![] (fun _ => 0) (v i)) := ht
    show Structure.rel (L := ℒₒᵣ) (M := ℕ) r
      (fun i => Semiterm.val (s := stageStrucN P S) ![] (fun _ => 0) (v i))
    rw [e]
    exact ht'
  · have ht' : ¬Structure.rel (L := ℒₒᵣ) (M := ℕ) r
        (fun i => Semiterm.val (s := stdInfN) ![] (fun _ => 0) (v i)) := ht
    show ¬Structure.rel (L := ℒₒᵣ) (M := ℕ) r
      (fun i => Semiterm.val (s := stageStrucN P S) ![] (fun _ => 0) (v i))
    rw [e]
    exact ht'

end Struc

/-! ### The stages, iterated over the levels -/

section Stages

variable (P : ℕ → Prop) (A : Fin n → Semisentence (LXIn n) 1)

/-- **The within-level stages of level `k`**, given the values `lowerTop j hj` read for the
strictly lower levels `j < k` (other, higher levels are never read once `A k` is
`LevelBounded k`): `S^k_a := ⋃_{γ≺a} Γ_{A_k}(S^k_γ)`, by well-founded recursion on the
notations `a ⪯ Ω_{k+1}`. The direct analogue of `ID1.stageSet`. -/
noncomputable def stageWithin (k : Fin n) (lowerTop : ∀ j : Fin n, j < k → Set ℕ) :
    StageAt k.val → Set ℕ :=
  WellFounded.fix (wellFounded_lt (α := StageAt k.val))
    (fun a rec => ⋃ g : StageAt k.val, ⋃ (h : g < a),
      opA P A k (Function.update (fun j => if hj : j < k then lowerTop j hj else ∅) k (rec g h)))

/-- The defining equation of the within-level stages. -/
theorem stageWithin_eq (k : Fin n) (lowerTop : ∀ j : Fin n, j < k → Set ℕ) (a : StageAt k.val) :
    stageWithin P A k lowerTop a = ⋃ g : StageAt k.val, ⋃ (_ : g < a),
      opA P A k (Function.update (fun j => if hj : j < k then lowerTop j hj else ∅) k
        (stageWithin P A k lowerTop g)) :=
  WellFounded.fix_eq _ _ a

theorem mem_stageWithin_iff (k : Fin n) (lowerTop : ∀ j : Fin n, j < k → Set ℕ)
    (a : StageAt k.val) (x : ℕ) :
    x ∈ stageWithin P A k lowerTop a ↔ ∃ g : StageAt k.val, g < a ∧
      x ∈ opA P A k (Function.update (fun j => if hj : j < k then lowerTop j hj else ∅) k
        (stageWithin P A k lowerTop g)) := by
  rw [stageWithin_eq]
  simp only [Set.mem_iUnion, exists_prop]

/-- **The iterated stage family**, level by level: level `k`'s within-level recursion is fed
the strictly lower levels' *top* stages, themselves built the same way — well-founded
recursion on `Fin n`, the direct analogue of `IDn.Sound.lfpChain`, generalised from "the least
fixed point of level `k`" to "the whole stage family of level `k`". -/
noncomputable def stageFamily : ∀ k : Fin n, StageAt k.val → Set ℕ :=
  WellFounded.fix (wellFounded_lt (α := Fin n))
    (fun k rec => stageWithin P A k (fun j hj => rec j hj (StageAt.top j.val)))

theorem stageFamily_eq (k : Fin n) :
    stageFamily P A k =
      stageWithin P A k (fun j (_ : j < k) => stageFamily P A j (StageAt.top j.val)) :=
  WellFounded.fix_eq _ _ k

/-- **The stages `S_{k,a}` of `ID n`**, combined into one family over `Stage n`, for the stage
model. -/
noncomputable def stageSetN (s : Stage n) : Set ℕ := stageFamily P A s.1 s.2

@[simp] theorem stageSetN_top (k : Fin n) :
    stageSetN P A (Stage.top k) = stageFamily P A k (StageAt.top k.val) := rfl

/-- The environment `stageEnvAt (stageSetN P A) k g` agrees, at every level `j ≤ k`, with the
placeholder environment used inside `stageWithin`'s recursive definition of level `k` — the
former reads every level honestly (needed to interpret the *whole* language `LIinfN n`), the
latter puts `∅` above level `k` (needed to make the recursion well founded); they can only
differ above level `k`, which `LevelBounded k (A k)` never reads. -/
theorem stageEnvAt_agree_of_le {k : Fin n} (g : StageAt k.val) :
    ∀ j, j ≤ k → stageEnvAt (stageSetN P A) k g j =
      Function.update (fun j' => if _hj' : j' < k then stageFamily P A j' (StageAt.top j'.val) else ∅)
        k (stageFamily P A k g) j := by
  intro j hj
  rcases lt_or_eq_of_le hj with hjk | rfl
  · rw [stageEnvAt, dif_neg (ne_of_lt hjk), Function.update_of_ne (ne_of_lt hjk), dif_pos hjk]
    rfl
  · rw [stageEnvAt, dif_pos rfl, Function.update_self]
    rfl

/-- **The operator of level `k`, evaluated at the honest environment `stageEnvAt`, agrees
with the operator evaluated at the placeholder environment used by the recursion**, for a
level-bounded `A k`. -/
theorem opA_stageEnvAt_eq {k : Fin n} (hb : LevelBounded k (A k)) (g : StageAt k.val) :
    opA P A k (stageEnvAt (stageSetN P A) k g) =
      opA P A k (Function.update
        (fun j' => if _hj' : j' < k then stageFamily P A j' (StageAt.top j'.val) else ∅) k
        (stageFamily P A k g)) := by
  ext x
  exact levelBounded_agree P k (stageEnvAt_agree_of_le P A g) (A k) hb ![x] Empty.elim

/-- **The defining equation of the combined stages**: `I_k^{≺a}`'s stage is the union, over
`γ ≺ a`, of the operator of level `k` applied to the honest environment reading every other
level at its own top. -/
theorem mem_stageSetN_iff {k : Fin n} (hb : LevelBounded k (A k)) (a : StageAt k.val) (x : ℕ) :
    x ∈ stageSetN P A (⟨k, a⟩ : Stage n) ↔ ∃ g : StageAt k.val, g.1 < a.1 ∧
      x ∈ opA P A k (stageEnvAt (stageSetN P A) k g) := by
  show x ∈ stageFamily P A k a ↔ _
  rw [stageFamily_eq, mem_stageWithin_iff]
  have hcongr : ∀ g : StageAt k.val,
      stageWithin P A k (fun j (_ : j < k) => stageFamily P A j (StageAt.top j.val)) g =
        stageFamily P A k g :=
    fun g => (congrFun (stageFamily_eq P A k).symm g)
  constructor
  · rintro ⟨g, hg, hx⟩
    refine ⟨g, hg, ?_⟩
    rw [opA_stageEnvAt_eq P A hb g, ← hcongr g]
    exact hx
  · rintro ⟨g, hg, hx⟩
    rw [opA_stageEnvAt_eq P A hb g] at hx
    rw [← hcongr g] at hx
    exact ⟨g, hg, hx⟩

end Stages

/-! ### The stage model -/

section Model

variable (P : ℕ → Prop) (A : Fin n → Semisentence (LXIn n) 1)

/-- **The stage model**: arithmetic standard, `X` read by `P`, and `I_k^{≺a}` read by the
stage `stageSetN P A ⟨k,a⟩`, for every level `k` and every `a ⪯ Ω_{k+1}`. -/
@[instance_reducible]
noncomputable def stageModelN : Structure (LIinfN n) ℕ := stageStrucN P (stageSetN P A)

/-- Truth in the stage model, free variables read as `0`. -/
def TrueSN (φ : Proposition (LIinfN n)) : Prop :=
  Semiformula.Eval (s := stageModelN P A) ![] (fun _ => 0) φ

theorem trueSN_stageAt (s : Stage n) (t : SyntacticTerm (LIinfN n)) :
    TrueSN P A (stageAt s t) ↔
      Semiterm.val (s := stageModelN P A) ![] (fun _ => 0) t ∈ stageSetN P A s :=
  eval_stageAt P _ s t _ _

theorem trueSN_unfold (k : Fin n) (g : StageAt k.val) (t : SyntacticTerm (LIinfN n)) :
    TrueSN P A (unfold (A k) k g t) ↔
      Semiterm.val (s := stageModelN P A) ![] (fun _ => 0) t ∈
        opA P A k (stageEnvAt (stageSetN P A) k g) :=
  eval_unfold P _ A k g t _ _

theorem trueSN_neg (φ : Proposition (LIinfN n)) : TrueSN P A (∼φ) ↔ ¬TrueSN P A φ := by
  simp [TrueSN]

theorem trueSN_subst_numeral (φ : Semiproposition (LIinfN n) 1) (m : ℕ) :
    TrueSN P A (φ/[numI m]) ↔
      Semiformula.Eval (s := stageModelN P A) ![m] (fun _ => 0) φ := by
  unfold TrueSN
  rw [Semiformula.eval_substs, Matrix.comp₁]
  have h : Semiterm.val (s := stageModelN P A) ![] (fun _ => 0) (numI m) = m :=
    val_numeral_stageStrucN P _ m _ _
  rw [h]

end Model

/-! ### Soundness below `Ω₁` -/

section Soundness

/-- `Ω₁ ⪯ Ω_{k+1}` for every level `k` (the level-0 top is the least of all the tops), so a
height `α ≺ Ω₁` is below every level's `Fix`-threshold. -/
theorem omega_zero_le (k : ℕ) : ThetaWNoteD.Omega 0 ≤ ThetaWNoteD.Omega k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact le_refl _
  · exact le_of_lt (by theta_order)

variable (P : ℕ → Prop) (A : Fin n → Semisentence (LXIn n) 1)

/-- **The truth lemma (Proposition 5.8, at every level)**: a sequent derived at a height
`α ≺ Ω₁` contains a formula true in the stage model, for every level-bounded family `A`,
every cut rank, every operator and every reading of `X`. -/
theorem sound (hb : FamilyLevelBounded A) {ρ : ThetaWNoteD} {H : Set ThetaWNoteD → Set ThetaWNoteD}
    {α : ThetaWNoteD} {Γ : Sequent (LIinfN n)} (d : IDnDerivable A ρ H α Γ) :
    α < ThetaWNoteD.Omega 0 → ∃ φ ∈ Γ, TrueSN P A φ := by
  induction d with
  | literal _ _ hφ hm => exact fun _ => ⟨_, hm, eval_of_trueLit P _ hφ⟩
  | verum _ _ hm =>
    intro _
    refine ⟨⊤, hm, ?_⟩
    simp [TrueSN]
  | idX t _ _ h1 h2 =>
    intro _
    by_cases h : TrueSN P A (XinfAt t)
    · exact ⟨_, h1, h⟩
    · exact ⟨_, h2, (trueSN_neg P A _).mpr h⟩
  | @and H α Γ φ ψ α₀ α₁ _ _ hm h0 h1 _ _ ih0 ih1 =>
    intro hα
    obtain ⟨χ₀, hχ₀, t₀⟩ := ih0 (lt_trans h0 hα)
    obtain ⟨χ₁, hχ₁, t₁⟩ := ih1 (lt_trans h1 hα)
    rcases List.mem_cons.mp hχ₀ with rfl | hχ₀
    · rcases List.mem_cons.mp hχ₁ with rfl | hχ₁
      · refine ⟨_, hm, ?_⟩
        unfold TrueSN at t₀ t₁ ⊢
        rw [LogicalConnective.HomClass.map_and]
        exact ⟨t₀, t₁⟩
      · exact ⟨χ₁, hχ₁, t₁⟩
    · exact ⟨χ₀, hχ₀, t₀⟩
  | @orL H α Γ φ ψ α₀ _ _ hm h0 _ ih0 =>
    intro hα
    obtain ⟨χ, hχ, t⟩ := ih0 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ with rfl | hχ
    · refine ⟨_, hm, ?_⟩
      unfold TrueSN at t ⊢
      rw [LogicalConnective.HomClass.map_or]
      exact Or.inl t
    · exact ⟨χ, hχ, t⟩
  | @orR H α Γ φ ψ α₀ _ _ hm _ h0 _ ih0 =>
    intro hα
    obtain ⟨χ, hχ, t⟩ := ih0 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ with rfl | hχ
    · refine ⟨_, hm, ?_⟩
      unfold TrueSN at t ⊢
      rw [LogicalConnective.HomClass.map_or]
      exact Or.inr t
    · exact ⟨χ, hχ, t⟩
  | @all H α Γ φ f _ _ hm hf _ ih =>
    intro hα
    by_cases hΓ : ∃ χ ∈ Γ, TrueSN P A χ
    · exact hΓ
    · refine ⟨_, hm, ?_⟩
      unfold TrueSN
      rw [Semiformula.eval_all]
      intro m
      obtain ⟨χ, hχ, t⟩ := ih m (lt_trans (hf m) hα)
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact (trueSN_subst_numeral P A φ m).mp t
      · exact absurd ⟨χ, hχ, t⟩ hΓ
  | @exs H α Γ φ m α₀ _ _ hm _ h0 _ ih0 =>
    intro hα
    obtain ⟨χ, hχ, t⟩ := ih0 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ with rfl | hχ
    · refine ⟨_, hm, ?_⟩
      unfold TrueSN
      rw [Semiformula.eval_ex]
      exact ⟨m, (trueSN_subst_numeral P A φ m).mp t⟩
    · exact ⟨χ, hχ, t⟩
  | @stage H α Γ k a t g α₀ _ _ hm hga _ _ h0 _ ih0 =>
    intro hα
    obtain ⟨χ, hχ, tr⟩ := ih0 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ with rfl | hχ
    · refine ⟨_, hm, ?_⟩
      rw [trueSN_stageAt, mem_stageSetN_iff P A (hb k)]
      exact ⟨g, hga, (trueSN_unfold P A k g t).mp tr⟩
    · exact ⟨χ, hχ, tr⟩
  | @nstage H α Γ k a t f _ _ hm hf _ ih =>
    intro hα
    by_cases hΓ : ∃ χ ∈ Γ, TrueSN P A χ
    · exact hΓ
    · refine ⟨_, hm, ?_⟩
      rw [← neg_stageAt, trueSN_neg, trueSN_stageAt, mem_stageSetN_iff P A (hb k)]
      rintro ⟨g, hga, hg⟩
      obtain ⟨χ, hχ, tr⟩ := ih g hga (lt_trans (hf g hga) hα)
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact (trueSN_neg P A _).mp tr ((trueSN_unfold P A k g t).mpr hg)
      · exact hΓ ⟨χ, hχ, tr⟩
  | @fix H α Γ k t α₀ _ _ hm hΩ _ _ =>
    intro hα
    exact absurd (lt_of_le_of_lt (le_trans (omega_zero_le k.val) hΩ) hα) (lt_irrefl _)
  | @cut H α Γ ψ α₀ _ _ _ h0 _ _ ih0 ih1 =>
    intro hα
    obtain ⟨χ₀, hχ₀, t₀⟩ := ih0 (lt_trans h0 hα)
    obtain ⟨χ₁, hχ₁, t₁⟩ := ih1 (lt_trans h0 hα)
    rcases List.mem_cons.mp hχ₀ with rfl | hχ₀
    · rcases List.mem_cons.mp hχ₁ with rfl | hχ₁
      · exact absurd t₀ ((trueSN_neg P A _).mp t₁)
      · exact ⟨χ₁, hχ₁, t₁⟩
    · exact ⟨χ₀, hχ₀, t₀⟩

end Soundness

end StageSem

end IDn

end OrdinalAnalysis
