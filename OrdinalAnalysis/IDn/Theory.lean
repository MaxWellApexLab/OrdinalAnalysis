/-
  The theories `ID n A` of `n` simultaneous positive inductive definitions, and their
  union `IDlt` over all finite levels.

  This generalises `ID1/Theory.lean` from one inductively defined predicate `I` to a
  family `I_0, …, I_{n-1}` (or, for `IDlt`, `I_0, I_1, …`), each governed by its own
  operator form, with lower predicates allowed to appear (in either polarity) in a
  higher form's defining formula. See `OrdinalAnalysis.IDn.Sound` for the standard-model
  soundness (an iterated least fixed point, level by level) and
  `OrdinalAnalysis.IDn.Union` for the union over all finite levels.

  **The language.**  For an index type `ι`, `LXIN ι := ℒₒᵣ + {X} + {I_k | k : ι}` is
  built exactly as `ID1/Theory.lean` builds `LXI`: one fresh relation symbol `X`, and
  one fresh unary relation symbol `I_k` for every `k : ι`. `LXIn n := LXIN (Fin n)` is
  the language of `n` levels, `LXIomega := LXIN ℕ` (written `LXIω` in prose) the
  language of all finite levels at once.

  **Operator forms.**  A family `A : ι → Semisentence (LXIN ι) 1` gives, at each level
  `k`, an operator form `A k`. As in `ID1`, `A k` may mention `X`; it may also mention
  any `I_j`, but the two side conditions

    * `PositiveIn k (A k)`      — `I_k` occurs only positively in `A k`
    * `LevelBounded k (A k)`    — every `I_j`-atom of `A k` (either polarity) has `j ≤ k`

  are exactly what `Sound.lean`'s iterated least-fixed-point construction needs: `I_k`'s
  operator is monotone in `I_k` once the lower predicates `I_j`, `j < k`, are fixed
  (`PositiveIn`), and does not look at higher predicates at all (`LevelBounded`), so the
  levels can be built up in order.

  **The axioms of `ID A` (`ι` implicit, `[DecidableEq ι]`).**

    * `𝗘𝗤 (LXIN ι)`, `𝗣𝗔⁻` transported, induction for every `LXIN ι`-formula (`paLXIN`);
    * for every level `k`: closure `∀x (A_k(I_k, x) → I_k x)` (`closureAxAt`) and the
      induction scheme `∀x (A_k(F, x) → F x) → ∀x (I_k x → F x)` for every `LXIN ι`-formula
      `F` (`indAxAt`, `substIAt k` replacing only the atoms of `I_k`, not of other `I_j`).

  `IDn n A := ID A` at `ι := Fin n`. `Union.lean` builds `IDlt` as a genuine union, over
  `n`, of `IDn n (A ↾ Fin n)` pushed into `LXIomega` along an explicit embedding — not a
  shortcut definition at `ι := ℕ` — together with the embeddings this needs.

  Contents.

    `IXRelN`, `IXLangN`, `LXIN`, `LXIn`, `LXIomega`, `toLXIN`   the languages
    `Xat`, `Iat`                                                the atoms `X t`, `I_k t`
    `PositiveIn`, `LevelBounded`                                the two side conditions on `A k`
    `positive_lMap_toLXIN`                                      arithmetic formulas are positive
    `substIAt`, `opAt`                                           `A_k(F, x)`: `F` for the atoms of `I_k`
    `closureAxAt`, `indAxAt`                                    the two axioms of level `k`
    `paLXIN`, `idAxiomsAt`, `ID`, `IDn`                          the theories, with membership lemmas
-/
import Foundation.FirstOrder.Arithmetic.Schemata

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### The language, indexed by a level type -/

/-- The relation symbols of `LXIN ι`: the free predicate `X`, and one inductively defined
predicate `I_k` for every level `k : ι`. -/
inductive IXRelN (ι : Type) : ℕ → Type
  | X : IXRelN ι 1
  | I : ι → IXRelN ι 1

instance {ι : Type} [DecidableEq ι] {k : ℕ} : DecidableEq (IXRelN ι k) := fun a b => by
  cases a with
  | X => cases b with
    | X => exact isTrue rfl
    | I j => exact isFalse (by intro h; cases h)
  | I i => cases b with
    | X => exact isFalse (by intro h; cases h)
    | I j =>
        exact if h : i = j then isTrue (by subst h; rfl)
          else isFalse (by intro e; exact h (by injection e))

/-- The fresh part of the language: no function symbols. -/
abbrev IXLangN (ι : Type) : Language where
  Func := fun _ => PEmpty
  Rel := IXRelN ι

/-- Arithmetic together with the free predicate `X` and one predicate `I_k` per level. -/
abbrev LXIN (ι : Type) : Language := Language.add ℒₒᵣ (IXLangN ι)

instance {ι : Type} : Language.ORing (LXIN ι) where
  eq := Sum.inl Language.Eq.eq
  lt := Sum.inl Language.LT.lt
  zero := Sum.inl Language.Zero.zero
  one := Sum.inl Language.One.one
  add := Sum.inl Language.Add.add
  mul := Sum.inl Language.Mul.mul

/-- **The language of `n` levels.** -/
abbrev LXIn (n : ℕ) : Language := LXIN (Fin n)

/-- **The language of all finite levels at once** (`LXIω` in prose). -/
abbrev LXIomega : Language := LXIN ℕ

/-- The embedding of arithmetic into `LXIN ι`. -/
abbrev toLXIN (ι : Type) : ℒₒᵣ →ᵥ LXIN ι := Language.Hom.add₁ ℒₒᵣ (IXLangN ι)

/-! ### The atoms -/

variable {ι : Type} {ξ : Type*} {n : ℕ}

/-- `X(t)`. -/
def Xat (t : Semiterm (LXIN ι) ξ n) : Semiformula (LXIN ι) ξ n :=
  Semiformula.rel (Sum.inr IXRelN.X) ![t]

/-- `I_k(t)`. -/
def Iat (k : ι) (t : Semiterm (LXIN ι) ξ n) : Semiformula (LXIN ι) ξ n :=
  Semiformula.rel (Sum.inr (IXRelN.I k)) ![t]

/-! ### Positivity in a level, and level-boundedness -/

/-- **`I_k` occurs only positively.** Other predicates `I_j`, `j ≠ k`, and `X`, are
unrestricted — this is the per-level generalisation of `ID1.Positive`. -/
def PositiveIn (k : ι) : {n : ℕ} → Semiformula (LXIN ι) ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel _ _ => True
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr IXRelN.X) _ => True
  | _, .nrel (Sum.inr (IXRelN.I j)) _ => j ≠ k
  | _, .and φ ψ => PositiveIn k φ ∧ PositiveIn k ψ
  | _, .or φ ψ => PositiveIn k φ ∧ PositiveIn k ψ
  | _, .all φ => PositiveIn k φ
  | _, .exs φ => PositiveIn k φ

/-- **Every `I_j`-atom of the formula (either polarity) has `j ≤ k`.** Needs an order on
the index type; `Fin n` and `ℕ` both have one. -/
def LevelBounded [PartialOrder ι] (k : ι) : {n : ℕ} → Semiformula (LXIN ι) ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel (Sum.inl _) _ => True
  | _, .rel (Sum.inr IXRelN.X) _ => True
  | _, .rel (Sum.inr (IXRelN.I j)) _ => j ≤ k
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr IXRelN.X) _ => True
  | _, .nrel (Sum.inr (IXRelN.I j)) _ => j ≤ k
  | _, .and φ ψ => LevelBounded k φ ∧ LevelBounded k ψ
  | _, .or φ ψ => LevelBounded k φ ∧ LevelBounded k ψ
  | _, .all φ => LevelBounded k φ
  | _, .exs φ => LevelBounded k φ

section Positive

variable (k : ι)

@[simp] theorem positiveIn_verum : PositiveIn k (⊤ : Semiformula (LXIN ι) ξ n) := trivial

@[simp] theorem positiveIn_falsum : PositiveIn k (⊥ : Semiformula (LXIN ι) ξ n) := trivial

@[simp] theorem positiveIn_and (φ ψ : Semiformula (LXIN ι) ξ n) :
    PositiveIn k (φ ⋏ ψ) ↔ PositiveIn k φ ∧ PositiveIn k ψ := Iff.rfl

@[simp] theorem positiveIn_or (φ ψ : Semiformula (LXIN ι) ξ n) :
    PositiveIn k (φ ⋎ ψ) ↔ PositiveIn k φ ∧ PositiveIn k ψ := Iff.rfl

@[simp] theorem positiveIn_all (φ : Semiformula (LXIN ι) ξ (n + 1)) :
    PositiveIn k (∀¹ φ) ↔ PositiveIn k φ := Iff.rfl

@[simp] theorem positiveIn_exs (φ : Semiformula (LXIN ι) ξ (n + 1)) :
    PositiveIn k (∃¹ φ) ↔ PositiveIn k φ := Iff.rfl

theorem positiveIn_Iat (t : Semiterm (LXIN ι) ξ n) : PositiveIn k (Iat k t) := trivial

theorem positiveIn_Iat_of_ne {j : ι} (_h : j ≠ k) (t : Semiterm (LXIN ι) ξ n) :
    PositiveIn k (Iat j t) := trivial

theorem positiveIn_Xat (t : Semiterm (LXIN ι) ξ n) : PositiveIn k (Xat t) := trivial

theorem positiveIn_neg_Xat (t : Semiterm (LXIN ι) ξ n) : PositiveIn k (∼(Xat t)) := trivial

/-- An arithmetic formula, transported to `LXIN ι`, is positive in every level, and so is
its negation: it contains no `I_k` at all. -/
theorem positive_lMap_toLXIN : ∀ {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n),
    PositiveIn k (Semiformula.lMap (toLXIN ι) φ) ∧ PositiveIn k (∼(Semiformula.lMap (toLXIN ι) φ))
  | _, .verum => ⟨trivial, trivial⟩
  | _, .falsum => ⟨trivial, trivial⟩
  | _, .rel _ _ => ⟨trivial, trivial⟩
  | _, .nrel _ _ => ⟨trivial, trivial⟩
  | _, .and φ ψ => by
      have h1 := positive_lMap_toLXIN φ
      have h2 := positive_lMap_toLXIN ψ
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  | _, .or φ ψ => by
      have h1 := positive_lMap_toLXIN φ
      have h2 := positive_lMap_toLXIN ψ
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  | _, .all φ => positive_lMap_toLXIN φ
  | _, .exs φ => positive_lMap_toLXIN φ

end Positive

section LevelBounded

variable [PartialOrder ι] (k : ι)

@[simp] theorem levelBounded_verum : LevelBounded k (⊤ : Semiformula (LXIN ι) ξ n) := trivial

@[simp] theorem levelBounded_falsum : LevelBounded k (⊥ : Semiformula (LXIN ι) ξ n) := trivial

@[simp] theorem levelBounded_and (φ ψ : Semiformula (LXIN ι) ξ n) :
    LevelBounded k (φ ⋏ ψ) ↔ LevelBounded k φ ∧ LevelBounded k ψ := Iff.rfl

@[simp] theorem levelBounded_or (φ ψ : Semiformula (LXIN ι) ξ n) :
    LevelBounded k (φ ⋎ ψ) ↔ LevelBounded k φ ∧ LevelBounded k ψ := Iff.rfl

@[simp] theorem levelBounded_all (φ : Semiformula (LXIN ι) ξ (n + 1)) :
    LevelBounded k (∀¹ φ) ↔ LevelBounded k φ := Iff.rfl

@[simp] theorem levelBounded_exs (φ : Semiformula (LXIN ι) ξ (n + 1)) :
    LevelBounded k (∃¹ φ) ↔ LevelBounded k φ := Iff.rfl

theorem levelBounded_Iat (t : Semiterm (LXIN ι) ξ n) : LevelBounded k (Iat k t) := le_refl k

theorem levelBounded_Xat (t : Semiterm (LXIN ι) ξ n) : LevelBounded k (Xat t) := trivial

/-- An arithmetic formula, transported to `LXIN ι`, is level-bounded at every level, and so
is its negation. -/
theorem levelBounded_lMap_toLXIN : ∀ {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n),
    LevelBounded k (Semiformula.lMap (toLXIN ι) φ) ∧
      LevelBounded k (∼(Semiformula.lMap (toLXIN ι) φ))
  | _, .verum => ⟨trivial, trivial⟩
  | _, .falsum => ⟨trivial, trivial⟩
  | _, .rel _ _ => ⟨trivial, trivial⟩
  | _, .nrel _ _ => ⟨trivial, trivial⟩
  | _, .and φ ψ => by
      have h1 := levelBounded_lMap_toLXIN φ
      have h2 := levelBounded_lMap_toLXIN ψ
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  | _, .or φ ψ => by
      have h1 := levelBounded_lMap_toLXIN φ
      have h2 := levelBounded_lMap_toLXIN ψ
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  | _, .all φ => levelBounded_lMap_toLXIN φ
  | _, .exs φ => levelBounded_lMap_toLXIN φ

end LevelBounded

/-! ### Substituting a formula for `I_k` alone -/

/-- **`substIAt k F φ`**: every atom `I_k t` of `φ` replaced by `F(t)`, every `∼I_k t` by
`∼F(t)`; atoms of other predicates `I_j`, `j ≠ k`, are untouched. Generalises
`ID1.substI` (which had a single predicate, so no branching on the index was needed). -/
def substIAt [DecidableEq ι] (k : ι) (F : Semiformula (LXIN ι) ξ 1) :
    {n : ℕ} → Semiformula (LXIN ι) ξ n → Semiformula (LXIN ι) ξ n
  | _, .verum => ⊤
  | _, .falsum => ⊥
  | _, .rel (Sum.inl r) v => .rel (Sum.inl r) v
  | _, .rel (Sum.inr IXRelN.X) v => .rel (Sum.inr IXRelN.X) v
  | _, .rel (Sum.inr (IXRelN.I j)) v =>
      if _ : j = k then F/[v 0] else .rel (Sum.inr (IXRelN.I j)) v
  | _, .nrel (Sum.inl r) v => .nrel (Sum.inl r) v
  | _, .nrel (Sum.inr IXRelN.X) v => .nrel (Sum.inr IXRelN.X) v
  | _, .nrel (Sum.inr (IXRelN.I j)) v =>
      if _ : j = k then ∼(F/[v 0]) else .nrel (Sum.inr (IXRelN.I j)) v
  | _, .and φ ψ => substIAt k F φ ⋏ substIAt k F ψ
  | _, .or φ ψ => substIAt k F φ ⋎ substIAt k F ψ
  | _, .all φ => ∀¹ substIAt k F φ
  | _, .exs φ => ∃¹ substIAt k F φ

/-! ### Operator forms and the axioms at one level -/

variable [DecidableEq ι]

/-- `A_k(F, x)`, a formula in the bound slot `x` with the free variables of `F` and of `A`
as parameters. `A_k(I_k, x)` is `A_k` itself. -/
def opAt (k : ι) (A : Semisentence (LXIN ι) 1) (F : Semiformula (LXIN ι) ℕ 1) :
    Semiformula (LXIN ι) ℕ 1 :=
  substIAt k F (Rewriting.emb A)

/-- **Closure at level `k`**: `∀x (A_k(I_k, x) → I_k x)`. -/
def closureAxAt (k : ι) (A : Semisentence (LXIN ι) 1) : Sentence (LXIN ι) :=
  ∀¹ (A 🡒 Iat k #0)

/-- **The induction scheme for `I_k`**, at the formula `F`: the universal closure of
`∀x (A_k(F, x) → F x) → ∀x (I_k x → F x)`. -/
def indAxAt (k : ι) (A : Semisentence (LXIN ι) 1) (F : Semiformula (LXIN ι) ℕ 1) :
    Sentence (LXIN ι) :=
  Semiformula.univCl ((∀¹ (opAt k A F 🡒 F)) 🡒 ∀¹ (Iat k #0 🡒 F))

/-! ### The theory -/

/-- `PA` in the language `LXIN ι`: equality for the whole language, `𝗣𝗔⁻` transported, and
induction for every formula of `LXIN ι`. -/
def paLXIN (ι : Type) [DecidableEq ι] : Theory (LXIN ι) :=
  𝗘𝗤 (LXIN ι) ∪ (Theory.lMap (toLXIN ι) 𝗣𝗔⁻ ∪ InductionScheme (LXIN ι) Set.univ)

/-- The two axioms of the inductive definition given by `A` at level `k`. -/
def idAxiomsAt (k : ι) (A : Semisentence (LXIN ι) 1) : Theory (LXIN ι) :=
  insert (closureAxAt k A) (Set.range (indAxAt k A))

/-- **`ID A`**, for a family `A : ι → Semisentence (LXIN ι) 1` of operator forms, one per
level `k : ι`: `PA` for the whole language, plus the closure and induction axioms of every
level. No positivity/level-boundedness hypothesis is needed to *state* the theory — those
are exactly the hypotheses `Sound.lean` needs to build a standard model of it. -/
def ID (A : ι → Semisentence (LXIN ι) 1) : Theory (LXIN ι) :=
  paLXIN ι ∪ ⋃ k, idAxiomsAt k (A k)

set_option linter.dupNamespace false in
/-- **`ID n A`**: `n` simultaneous inductive definitions. -/
abbrev IDn (n : ℕ) (A : Fin n → Semisentence (LXIn n) 1) : Theory (LXIn n) := ID A

/-- **The family `A` is positive**: `A k` is positive in `I_k`, for every level `k`. -/
def FamilyPositive (A : ι → Semisentence (LXIN ι) 1) : Prop := ∀ k, PositiveIn k (A k)

/-- **The family `A` is level-bounded**: `A k` mentions no `I_j` with `j > k`, for every
level `k`. -/
def FamilyLevelBounded [PartialOrder ι] (A : ι → Semisentence (LXIN ι) 1) : Prop :=
  ∀ k, LevelBounded k (A k)

section Membership

variable (A : ι → Semisentence (LXIN ι) 1)

theorem paLXIN_subset_ID : paLXIN ι ⊆ ID A := Set.subset_union_left

theorem mem_ID_of_eq {σ : Sentence (LXIN ι)} (h : σ ∈ 𝗘𝗤 (LXIN ι)) : σ ∈ ID A :=
  Or.inl (Or.inl h)

theorem mem_ID_of_paMinus {σ : Sentence ℒₒᵣ} (h : σ ∈ 𝗣𝗔⁻) :
    Semiformula.lMap (toLXIN ι) σ ∈ ID A :=
  Or.inl (Or.inr (Or.inl ⟨σ, h, rfl⟩))

theorem succInd_mem_ID (φ : Semiformula (LXIN ι) ℕ 1) :
    Semiformula.univCl (succInd φ) ∈ ID A :=
  Or.inl (Or.inr (Or.inr ⟨φ, trivial, rfl⟩))

theorem closureAxAt_mem_ID (k : ι) : closureAxAt k (A k) ∈ ID A :=
  Or.inr (Set.mem_iUnion_of_mem k (Set.mem_insert _ _))

theorem indAxAt_mem_ID (k : ι) (F : Semiformula (LXIN ι) ℕ 1) : indAxAt k (A k) F ∈ ID A :=
  Or.inr (Set.mem_iUnion_of_mem k (Set.mem_insert_of_mem _ ⟨F, rfl⟩))

/-- The axioms of `ID A`, by kind. -/
theorem mem_ID {σ : Sentence (LXIN ι)} :
    σ ∈ ID A ↔ σ ∈ 𝗘𝗤 (LXIN ι) ∨ σ ∈ Theory.lMap (toLXIN ι) 𝗣𝗔⁻ ∨
      σ ∈ InductionScheme (LXIN ι) Set.univ ∨
      ∃ k, σ = closureAxAt k (A k) ∨ ∃ F, σ = indAxAt k (A k) F := by
  constructor
  · rintro ((h | h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
      rcases hk with rfl | ⟨F, rfl⟩
      · exact Or.inr (Or.inr (Or.inr ⟨k, Or.inl rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨k, Or.inr ⟨F, rfl⟩⟩))
  · rintro (h | h | h | ⟨k, rfl | ⟨F, rfl⟩⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact closureAxAt_mem_ID A k
    · exact indAxAt_mem_ID A k F

instance paLXIN_weakerThan_ID : paLXIN ι ⪯ ID A :=
  Entailment.WeakerThan.ofSubset (paLXIN_subset_ID A)

instance eq_weakerThan_ID : 𝗘𝗤 (LXIN ι) ⪯ ID A :=
  Entailment.WeakerThan.ofSubset fun _ h => mem_ID_of_eq A h

end Membership

end IDn

end OrdinalAnalysis
