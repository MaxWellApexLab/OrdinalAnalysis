/-
  The infinitary language of `ID n` with stage predicates, one family per level.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §5–§6 (as ported by `ID1/Language.lean`), which spells out the multi-level generalisation used here.

  **The language.**  `ID1/Language.lean` builds one infinitary language `LIinf` for the one
  operator form of `ID1`, with stage predicates `I^{≺α}`, `α ⪯ Ω`.  Here there are `n` levels,
  each with its own operator form `A k : Semisentence (LXIn n) 1` (`IDn/Theory.lean`), so the
  language carries one *family* of stage predicates per level:

      LIinfN n  :=  ℒₒᵣ  +  { X }  ∪  { I_k^{≺α} | k : Fin n, α ⪯ Ω_{k+1} }.

  The index of a stage predicate is a pair `(k, α)` with `α ⪯ Ω_{k+1}`: the type `Stage n` below,
  the direct analogue of `ID1.InductiveDef.Stage` with an extra level component.  `Ω_{k+1}` is
  `ThetaWNoteD.Omega k.val` (`ThetaW/Dom.lean`'s convention: `Omega k` denotes `Ω_{k+1}`); the
  predicate `I_k` of `IDn.ID` is identified with `I_k^{≺Ω_{k+1}}` (`Stage.top`).

  **Per-level `stageHom`.**  Unfolding the operator form `A k` at a stage `α ⪯ Ω_{k+1}`
  reads `I_k` (the predicate *this* level's operator controls) as `I_k^{≺α}`, and every other
  predicate `I_j`, `j ≠ k`, as its own full predicate `I_j^{≺Ω_{j+1}}` — never as a variable
  stage, since only one level unfolds at a time (design note §2.1: `unfold_k A t α :=
  A_k(t, I_k^{<α})` with `I_j ↦ I_j^{<Ω_{j+1}}` for the other levels).  This is `stageHom k a`
  below, taking the level `k` and the bound `a : StageAt k.val` directly (rather than a general
  `Stage n`, which would force an unused case split on whether the given stage's level equals
  `k`).  A pleasant consequence (`stageRel_top`, `formAt_top`): holding `a` at the top of level
  `k` sends *every* level to its own top, for any `k` — so there is exactly one `embed`, shared
  by every level's `stageHom` at its own top stage, exactly as Freund's `embed = stageHom Ω`
  when there is only one level.

  **`params` and `Σ(Ω_{k+1})`.**  `params φ : Set (Stage n)` is Freund's `k(φ)` generalised: the
  stage indices `(j, β)` occurring as a literal `I_j^{≺β} t` or `¬I_j^{≺β} t` of `φ`.  `SigmaW k`
  is Buchholz's `Σ(Ω_{k+1})` read for `ID n` (design note §2.1): every stage literal has level
  `≤ k` (`RelSigmaW`/`NrelSigmaW`'s first conjunct, needed for *both* polarities, unlike the
  one-level `ID1.SigmaOmega`, which has nothing to restrict positively), and a *negated* stage
  literal of level exactly `k` must not be the full predicate `I_k` (second conjunct — positive
  `I_k` is unrestricted, exactly as `ID1.SigmaOmega` allows positive `I`).

  **Bounding.**  `capAt k b` is Freund's `φ^β` read at level `k`: every literal `I_k^{≺Ω_{k+1}} t`,
  `¬I_k^{≺Ω_{k+1}} t` (the *full*, level-`k` predicate) is replaced by `I_k^{≺b} t`, `¬I_k^{≺b} t`;
  every other stage literal, at level `k` below the top or at any other level, is untouched.

  Contents.

    `StageAt`, `StageAt.top`                        the bounds `α ⪯ Ω_{k+1}` at one level
    `Stage`, `Stage.lvl`, `Stage.val`, `Stage.top`   the stage indices `(k, α)`, and `I_k`'s index
    `IInfRelN`, `IInfLangN`, `LIinfN`               the language
    `XinfAt`, `stageAt`, `nstageAt`, `IOmegaAt`      the atoms `X t`, `I_k^{≺α} t`, `¬…`, `I_k t`
    `stageHom`, `embed`, `formAt`, `unfold`          `I_k ↦ I_k^{≺α}`, `LXIn n ↪ LIinfN n`, …
    `params`                                          `k(φ)`
    `SigmaW`                                          the classes `Σ(Ω_{k+1})`
    `capAt`                                           `φ ↦ φ^β` at level `k`
-/
import OrdinalAnalysis.IDn.Theory
import OrdinalAnalysis.Ordinal.ThetaW.Arith

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder

/-! ### Stages -/

/-- The stage bounds at level `k`: the notations `α ⪯ Ω_{k+1}` (`ThetaWNoteD.Omega k`). -/
abbrev StageAt (k : ℕ) : Type := {a : ThetaWNoteD // a ≤ ThetaWNoteD.Omega k}

namespace StageAt

/-- The top stage at level `k`, `Ω_{k+1}`; `I_k^{≺Ω_{k+1}}` is the predicate `I_k`. -/
def top (k : ℕ) : StageAt k := ⟨ThetaWNoteD.Omega k, le_refl _⟩

@[simp] theorem top_val (k : ℕ) : (top k).1 = ThetaWNoteD.Omega k := rfl

/-- A countable stage `α ≺ Ω_{k+1}` at level `k`. -/
def ofLt (k : ℕ) (a : ThetaWNoteD) (h : a < ThetaWNoteD.Omega k) : StageAt k := ⟨a, le_of_lt h⟩

@[simp] theorem ofLt_val (k : ℕ) (a : ThetaWNoteD) (h : a < ThetaWNoteD.Omega k) :
    (ofLt k a h).1 = a := rfl

theorem eq_top_iff {k : ℕ} {a : StageAt k} : a = top k ↔ a.1 = ThetaWNoteD.Omega k :=
  Subtype.ext_iff

theorem lt_Omega_of_ne_top {k : ℕ} {a : StageAt k} (h : a ≠ top k) : a.1 < ThetaWNoteD.Omega k :=
  lt_of_le_of_ne a.2 (fun e => h (Subtype.ext e))

theorem ne_top_of_lt_Omega {k : ℕ} {a : StageAt k} (h : a.1 < ThetaWNoteD.Omega k) : a ≠ top k :=
  fun e => ne_of_lt h (eq_top_iff.mp e)

theorem ne_top_iff {k : ℕ} {a : StageAt k} : a ≠ top k ↔ a.1 < ThetaWNoteD.Omega k :=
  ⟨lt_Omega_of_ne_top, ne_top_of_lt_Omega⟩

end StageAt

/-- The stage indices of `ID n`: a level `k < n` together with a bound `α ⪯ Ω_{k+1}`. -/
abbrev Stage (n : ℕ) : Type := Σ k : Fin n, StageAt k.val

namespace Stage

variable {n : ℕ}

/-- The level of a stage index. -/
def lvl (s : Stage n) : Fin n := s.1

/-- The bound `α` of a stage index. -/
def val (s : Stage n) : ThetaWNoteD := s.2.1

theorem le (s : Stage n) : s.val ≤ ThetaWNoteD.Omega s.lvl.val := s.2.2

/-- The top stage `(k, Ω_{k+1})`; `I_k^{≺Ω_{k+1}}` is the predicate `I_k`. -/
def top (k : Fin n) : Stage n := ⟨k, StageAt.top k.val⟩

@[simp] theorem lvl_top (k : Fin n) : (top k).lvl = k := rfl

@[simp] theorem val_top (k : Fin n) : (top k).val = ThetaWNoteD.Omega k.val := rfl

theorem top_injective : Function.Injective (top (n := n)) := by
  intro i j h
  have := congrArg lvl h
  simpa using this

@[simp] theorem top_inj {i j : Fin n} : top i = top j ↔ i = j := top_injective.eq_iff

theorem ne_top_of_lvl_ne {s : Stage n} {k : Fin n} (h : s.lvl ≠ k) : s ≠ top k :=
  fun e => h (by rw [e, lvl_top])

end Stage

instance {n : ℕ} : DecidableEq (Stage n) := by
  unfold Stage StageAt; infer_instance

/-! ### The language -/

/-- The fresh relation symbols: the free predicate `X`, and one stage predicate `I_k^{≺α}` per
stage index `(k, α)`. -/
inductive IInfRelN (n : ℕ) : ℕ → Type
  | X : IInfRelN n 1
  | stage : Stage n → IInfRelN n 1

instance {n k : ℕ} : DecidableEq (IInfRelN n k) := fun a b => by
  cases a with
  | X => cases b with
    | X => exact isTrue rfl
    | stage _ => exact isFalse (by intro h; cases h)
  | stage a => cases b with
    | X => exact isFalse (by intro h; cases h)
    | stage b =>
      exact if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (by injection e))

/-- The fresh part of the language: no function symbols. -/
abbrev IInfLangN (n : ℕ) : Language where
  Func := fun _ => PEmpty
  Rel := IInfRelN n

/-- **The infinitary language** of `ID n`, with the free predicate `X`: arithmetic, `X`, and
the stage predicates `I_k^{≺α}`, `k < n`, `α ⪯ Ω_{k+1}`. -/
abbrev LIinfN (n : ℕ) : Language := Language.add ℒₒᵣ (IInfLangN n)

instance {n : ℕ} : Language.ORing (LIinfN n) where
  eq := Sum.inl Language.Eq.eq
  lt := Sum.inl Language.LT.lt
  zero := Sum.inl Language.Zero.zero
  one := Sum.inl Language.One.one
  add := Sum.inl Language.Add.add
  mul := Sum.inl Language.Mul.mul

/-- The embedding of arithmetic into `LIinfN n`. -/
abbrev toLIinfN (n : ℕ) : ℒₒᵣ →ᵥ LIinfN n := Language.Hom.add₁ ℒₒᵣ (IInfLangN n)

/-- The stage index of a relation symbol: `some (k, α)` for `I_k^{≺α}`, `none` for `X` and the
symbols of arithmetic. -/
def relStage {n : ℕ} : {k : ℕ} → (LIinfN n).Rel k → Option (Stage n)
  | _, Sum.inl _ => none
  | _, Sum.inr IInfRelN.X => none
  | _, Sum.inr (IInfRelN.stage s) => some s

/-! ### The atoms -/

section Atoms

variable {n : ℕ} {ξ : Type*} {m : ℕ}

/-- `X(t)`. -/
def XinfAt (t : Semiterm (LIinfN n) ξ m) : Semiformula (LIinfN n) ξ m :=
  Semiformula.rel (Sum.inr IInfRelN.X) ![t]

/-- `I_k^{≺α} t`: "`t` enters level `k` at a stage below `α`". -/
def stageAt (s : Stage n) (t : Semiterm (LIinfN n) ξ m) : Semiformula (LIinfN n) ξ m :=
  Semiformula.rel (Sum.inr (IInfRelN.stage s)) ![t]

/-- `¬I_k^{≺α} t`. -/
def nstageAt (s : Stage n) (t : Semiterm (LIinfN n) ξ m) : Semiformula (LIinfN n) ξ m :=
  Semiformula.nrel (Sum.inr (IInfRelN.stage s)) ![t]

/-- `I_k t = I_k^{≺Ω_{k+1}} t`. -/
def IOmegaAt (k : Fin n) (t : Semiterm (LIinfN n) ξ m) : Semiformula (LIinfN n) ξ m :=
  stageAt (Stage.top k) t

@[simp] theorem neg_stageAt (s : Stage n) (t : Semiterm (LIinfN n) ξ m) :
    ∼(stageAt s t) = nstageAt s t := rfl

@[simp] theorem neg_nstageAt (s : Stage n) (t : Semiterm (LIinfN n) ξ m) :
    ∼(nstageAt s t) = stageAt s t := rfl

theorem IOmegaAt_eq (k : Fin n) (t : Semiterm (LIinfN n) ξ m) :
    IOmegaAt k t = stageAt (Stage.top k) t := rfl

/-- A unary atom is `r ![v 0]`. -/
theorem rel_eq_vec {k : ℕ} (r : (LIinfN n).Rel 1) (v : Fin 1 → Semiterm (LIinfN n) ξ k) :
    Semiformula.rel r v = Semiformula.rel r ![v 0] := by
  congr 1; funext i; obtain rfl := Subsingleton.elim i 0; rfl

theorem nrel_eq_vec {k : ℕ} (r : (LIinfN n).Rel 1) (v : Fin 1 → Semiterm (LIinfN n) ξ k) :
    Semiformula.nrel r v = Semiformula.nrel r ![v 0] := by
  congr 1; funext i; obtain rfl := Subsingleton.elim i 0; rfl

end Atoms

/-! ### From `LXIn n` to `LIinfN n`: `I_k ↦ I_k^{≺α}`, one level at a time -/

section StageHom

variable {n : ℕ}

/-- The function symbols of `LXIn n` are those of arithmetic. -/
def stageFuncN : {k : ℕ} → (LXIn n).Func k → (LIinfN n).Func k
  | _, Sum.inl f => Sum.inl f
  | _, Sum.inr f => PEmpty.elim f

/-- Arithmetic and `X` are fixed; `I_k` (the level being unfolded) goes to `I_k^{≺a}`, and every
other `I_j`, `j ≠ k`, to its own top `I_j^{≺Ω_{j+1}}`. -/
def stageRel (k : Fin n) (a : StageAt k.val) :
    {m : ℕ} → (LXIn n).Rel m → (LIinfN n).Rel m
  | _, Sum.inl r => Sum.inl r
  | _, Sum.inr IXRelN.X => Sum.inr IInfRelN.X
  | _, Sum.inr (IXRelN.I j) =>
      if _ : j = k then Sum.inr (IInfRelN.stage ⟨k, a⟩)
      else Sum.inr (IInfRelN.stage (Stage.top j))

/-- The defining equation of `stageRel` on an `I_j`-atom, restated as a plain `rfl` lemma: unlike
`unfold`, which has trouble reducing the auxiliary matcher of a dependent pattern match through
`(LXIn n).Rel _`, direct term-mode `rfl` goes through the reduction without difficulty, and the
resulting equation is then usable by `rw`. -/
theorem stageRel_I (k : Fin n) (a : StageAt k.val) (j : Fin n) :
    stageRel k a (Sum.inr (IXRelN.I j)) =
      if _ : j = k then Sum.inr (IInfRelN.stage ⟨k, a⟩) else Sum.inr (IInfRelN.stage (Stage.top j)) :=
  rfl

/-- **`I_k ↦ I_k^{≺a}`** (other levels at their own top), as a homomorphism of languages. -/
def stageHom (k : Fin n) (a : StageAt k.val) : LXIn n →ᵥ LIinfN n := ⟨stageFuncN, stageRel k a⟩

/-- The terms do not see the stage. -/
theorem lMap_stageHom_term {ξ : Type*} {m : ℕ} (k k' : Fin n) (a : StageAt k.val)
    (a' : StageAt k'.val) (t : Semiterm (LXIn n) ξ m) :
    Semiterm.lMap (stageHom k a) t = Semiterm.lMap (stageHom k' a') t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih =>
    simp only [Semiterm.lMap_func]
    congr 1
    funext i
    exact ih i

/-- Arithmetic and `X` are fixed; every `I_j` goes to its own top `I_j^{≺Ω_{j+1}}`. -/
def embedRel : {m : ℕ} → (LXIn n).Rel m → (LIinfN n).Rel m
  | _, Sum.inl r => Sum.inl r
  | _, Sum.inr IXRelN.X => Sum.inr IInfRelN.X
  | _, Sum.inr (IXRelN.I j) => Sum.inr (IInfRelN.stage (Stage.top j))

/-- **The embedding of `LXIn n` into `LIinfN n`**: `I_j ↦ I_j^{≺Ω_{j+1}}` for every level `j`
(Freund identifies `I_φ` with `I^{≺Ω}_φ`; here every level's predicate is identified with its own
full stage predicate). -/
def embedHom : LXIn n →ᵥ LIinfN n := ⟨stageFuncN, embedRel⟩

/-- **Holding a level at its own top sends every level to its own top**: `stageHom k` at the top
stage of level `k` agrees with `embedHom`, for *any* `k` — the analogue, for `n` levels, of
`formAt_top`'s one-level fact that `stageHom Ω = embed`. -/
theorem stageRel_top (k : Fin n) :
    ∀ {m : ℕ} (r : (LXIn n).Rel m), stageRel k (StageAt.top k.val) r = embedRel r
  | _, Sum.inl _ => rfl
  | _, Sum.inr IXRelN.X => rfl
  | _, Sum.inr (IXRelN.I j) => by
      by_cases h : j = k
      · subst h
        rw [stageRel_I, dif_pos rfl]
        rfl
      · rw [stageRel_I, dif_neg h]
        rfl

theorem stageHom_top (k : Fin n) : stageHom k (StageAt.top k.val) = embedHom := by
  unfold stageHom embedHom
  congr 1
  funext m r
  exact stageRel_top k r

variable {ξ : Type*} {m : ℕ}

/-- **The embedding of `LXIn n` into `LIinfN n`**. -/
def embed (φ : Semiformula (LXIn n) ξ m) : Semiformula (LIinfN n) ξ m :=
  Semiformula.lMap embedHom φ

/-- `A_k(·, I_k^{≺a})`: the operator form of level `k` with `I_k` read as the stage `I_k^{≺a}`,
every other level at its own top. -/
def formAt (A : Semisentence (LXIn n) 1) (k : Fin n) (a : StageAt k.val) :
    Semisentence (LIinfN n) 1 :=
  Semiformula.lMap (stageHom k a) A

/-- **The stage unfolding** `A_k(t, I_k^{≺a})`. -/
def unfold (A : Semisentence (LXIn n) 1) (k : Fin n) (a : StageAt k.val)
    (t : Semiterm (LIinfN n) ξ m) : Semiformula (LIinfN n) ξ m :=
  (Rewriting.emb (formAt A k a) : Semiformula (LIinfN n) ξ 1)/[t]

theorem embed_neg (φ : Semiformula (LXIn n) ξ m) : embed (∼φ) = ∼(embed φ) := by
  simp [embed]

/-- `I_k t ↦ I_k^{≺Ω_{k+1}} t`. -/
theorem embed_Iat (k : Fin n) (t : Semiterm (LXIn n) ξ m) :
    embed (Iat k t) = IOmegaAt k (Semiterm.lMap embedHom t) :=
  rel_eq_vec (Sum.inr (IInfRelN.stage (Stage.top k))) (Semiterm.lMap embedHom ∘ ![t])

/-- `X t ↦ X t`. -/
theorem embed_Xat (t : Semiterm (LXIn n) ξ m) :
    embed (Xat t) = XinfAt (Semiterm.lMap embedHom t) :=
  rel_eq_vec (Sum.inr IInfRelN.X) (Semiterm.lMap embedHom ∘ ![t])

/-- The embedding of the whole form is `formAt A k` at the top of level `k`, for any `k`. -/
theorem formAt_top (A : Semisentence (LXIn n) 1) (k : Fin n) :
    formAt A k (StageAt.top k.val) = embed A := by
  unfold formAt embed; rw [stageHom_top]

end StageHom

/-! ### The parameters `k(φ)` -/

section Params

variable {n : ℕ}

/-- The parameters of a relation symbol: `{s}` for `I_{s.lvl}^{≺s.val}`, empty otherwise. -/
def relParams : {k : ℕ} → (LIinfN n).Rel k → Set (Stage n)
  | _, Sum.inl _ => ∅
  | _, Sum.inr IInfRelN.X => ∅
  | _, Sum.inr (IInfRelN.stage s) => {s}

/-- **`k(φ)`**, the stage indices of a formula: the `(j, β)` such that `φ` contains a literal
`I_j^{≺β} t` or `¬I_j^{≺β} t`. -/
def params {ξ : Type*} : {m : ℕ} → Semiformula (LIinfN n) ξ m → Set (Stage n)
  | _, .verum => ∅
  | _, .falsum => ∅
  | _, .rel r _ => relParams r
  | _, .nrel r _ => relParams r
  | _, .and φ ψ => params φ ∪ params ψ
  | _, .or φ ψ => params φ ∪ params ψ
  | _, .all φ => params φ
  | _, .exs φ => params φ

/-- `k(Γ)`, the parameters of a list of formulas. -/
def paramsList {ξ : Type*} {m : ℕ} (Γ : List (Semiformula (LIinfN n) ξ m)) : Set (Stage n) :=
  {s | ∃ φ ∈ Γ, s ∈ params φ}

variable {ξ : Type*} {m : ℕ}

@[simp] theorem params_verum : params (⊤ : Semiformula (LIinfN n) ξ m) = ∅ := rfl

@[simp] theorem params_falsum : params (⊥ : Semiformula (LIinfN n) ξ m) = ∅ := rfl

@[simp] theorem params_rel {k : ℕ} (r : (LIinfN n).Rel k) (v : Fin k → Semiterm (LIinfN n) ξ m) :
    params (Semiformula.rel r v) = relParams r := rfl

@[simp] theorem params_nrel {k : ℕ} (r : (LIinfN n).Rel k) (v : Fin k → Semiterm (LIinfN n) ξ m) :
    params (Semiformula.nrel r v) = relParams r := rfl

@[simp] theorem params_and (φ ψ : Semiformula (LIinfN n) ξ m) :
    params (φ ⋏ ψ) = params φ ∪ params ψ := rfl

@[simp] theorem params_or (φ ψ : Semiformula (LIinfN n) ξ m) :
    params (φ ⋎ ψ) = params φ ∪ params ψ := rfl

@[simp] theorem params_all (φ : Semiformula (LIinfN n) ξ (m + 1)) : params (∀¹ φ) = params φ := rfl

@[simp] theorem params_exs (φ : Semiformula (LIinfN n) ξ (m + 1)) : params (∃¹ φ) = params φ := rfl

@[simp] theorem params_stageAt (s : Stage n) (t : Semiterm (LIinfN n) ξ m) :
    params (stageAt s t) = {s} := rfl

@[simp] theorem params_nstageAt (s : Stage n) (t : Semiterm (LIinfN n) ξ m) :
    params (nstageAt s t) = {s} := rfl

@[simp] theorem params_IOmegaAt (k : Fin n) (t : Semiterm (LIinfN n) ξ m) :
    params (IOmegaAt k t) = {Stage.top k} := rfl

@[simp] theorem params_XinfAt (t : Semiterm (LIinfN n) ξ m) : params (XinfAt t) = ∅ := rfl

/-- `k(¬φ) = k(φ)`. -/
@[simp] theorem params_neg (φ : Semiformula (LIinfN n) ξ m) : params (∼φ) = params φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **The parameters do not see terms**: `k` is invariant under every rewriting. -/
@[simp] theorem params_rew {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfN n) ξ₁ m₁ ξ₂ m₂)
    (φ : Semiformula (LIinfN n) ξ₁ m₁) : params (ω ▹ φ) = params φ := by
  induction φ using Semiformula.rec' generalizing m₂ with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [Semiformula.rew_rel, params_rel, params_rel]
  | hnrel r v => rw [Semiformula.rew_nrel, params_nrel, params_nrel]
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

@[simp] theorem params_subst (φ : Semiformula (LIinfN n) ξ 1) (t : Semiterm (LIinfN n) ξ m) :
    params (φ/[t]) = params φ := params_rew _ φ

/-- The stage symbols of `A` with `I_k ↦ I_k^{≺a}`, other levels at their own top, are `⟨k,a⟩`
(from `I_k`) or a top `Stage.top j` at some level `j ≠ k` (from another `I_j` of `A`). -/
theorem relParams_stageRel (k : Fin n) (a : StageAt k.val) :
    ∀ {m : ℕ} (r : (LXIn n).Rel m),
      relParams (stageRel k a r) ⊆ {(⟨k, a⟩ : Stage n)} ∪ {s | ∃ j : Fin n, s = Stage.top j}
  | _, Sum.inl _ => Set.empty_subset _
  | _, Sum.inr IXRelN.X => Set.empty_subset _
  | _, Sum.inr (IXRelN.I j) => by
      by_cases h : j = k
      · have e : stageRel k a (Sum.inr (IXRelN.I j)) = Sum.inr (IInfRelN.stage ⟨k, a⟩) := by
          rw [stageRel_I, dif_pos h]
        rw [e]
        exact Set.subset_union_left
      · have e : stageRel k a (Sum.inr (IXRelN.I j)) =
            Sum.inr (IInfRelN.stage (Stage.top j)) := by
          rw [stageRel_I, dif_neg h]
        rw [e]
        rintro s rfl
        exact Set.mem_union_right _ ⟨j, rfl⟩

/-- Every parameter of `A` with `I_k ↦ I_k^{≺a}` is `⟨k,a⟩` or some level's top. -/
theorem params_lMap_stageHom (k : Fin n) (a : StageAt k.val) {ξ' : Type*} {m' : ℕ}
    (φ : Semiformula (LXIn n) ξ' m') :
    params (Semiformula.lMap (stageHom k a) φ) ⊆
      {(⟨k, a⟩ : Stage n)} ∪ {s | ∃ j : Fin n, s = Stage.top j} := by
  induction φ using Semiformula.rec' with
  | hverum => exact Set.empty_subset _
  | hfalsum => exact Set.empty_subset _
  | hrel r v => exact relParams_stageRel k a r
  | hnrel r v => exact relParams_stageRel k a r
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and, params_and]; exact Set.union_subset ihφ ihψ
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or, params_or]; exact Set.union_subset ihφ ihψ
  | hall φ ih => rw [Semiformula.lMap_all, params_all]; exact ih
  | hexs φ ih => rw [Semiformula.lMap_exs, params_exs]; exact ih

/-- **Level-bounded refinement of `params_lMap_stageHom`**: if `A` is level-bounded at `k`
(mentions no `I_j` with `j > k`), then every parameter of `A` with `I_k ↦ I_k^{≺a}` is `⟨k,a⟩`
itself, or the top of a level *strictly below* `k` (the case `j = k` is routed to `⟨k,a⟩` by
`stageRel`, never to `Stage.top k`). -/
theorem params_lMap_stageHom_of_levelBounded {k : Fin n} {a : StageAt k.val}
    {ξ' : Type*} {m' : ℕ} {A : Semiformula (LXIn n) ξ' m'} (hb : LevelBounded k A) :
    ∀ s ∈ params (Semiformula.lMap (stageHom k a) A),
      s = (⟨k, a⟩ : Stage n) ∨ ∃ j : Fin n, j.val < k.val ∧ s = Stage.top j := by
  induction A using Semiformula.rec' with
  | hverum => exact fun s hs => (hs : False).elim
  | hfalsum => exact fun s hs => (hs : False).elim
  | hrel r v =>
    rcases r with r | r
    · exact fun s hs => (hs : False).elim
    · cases r with
      | X => exact fun s hs => (hs : False).elim
      | I j =>
        intro s hs
        have hs' : s ∈ relParams (stageRel k a (Sum.inr (IXRelN.I j))) := hs
        by_cases h : j = k
        · have e : stageRel k a (Sum.inr (IXRelN.I j)) = Sum.inr (IInfRelN.stage ⟨k, a⟩) := by
            rw [stageRel_I, dif_pos h]
          rw [e] at hs'
          exact Or.inl hs'
        · have e : stageRel k a (Sum.inr (IXRelN.I j)) =
              Sum.inr (IInfRelN.stage (Stage.top j)) := by
            rw [stageRel_I, dif_neg h]
          rw [e] at hs'
          have hjk : j.val ≤ k.val := hb
          exact Or.inr ⟨j, lt_of_le_of_ne hjk (fun e' => h (Fin.ext e')), hs'⟩
  | hnrel r v =>
    rcases r with r | r
    · exact fun s hs => (hs : False).elim
    · cases r with
      | X => exact fun s hs => (hs : False).elim
      | I j =>
        intro s hs
        have hs' : s ∈ relParams (stageRel k a (Sum.inr (IXRelN.I j))) := hs
        by_cases h : j = k
        · have e : stageRel k a (Sum.inr (IXRelN.I j)) = Sum.inr (IInfRelN.stage ⟨k, a⟩) := by
            rw [stageRel_I, dif_pos h]
          rw [e] at hs'
          exact Or.inl hs'
        · have e : stageRel k a (Sum.inr (IXRelN.I j)) =
              Sum.inr (IInfRelN.stage (Stage.top j)) := by
            rw [stageRel_I, dif_neg h]
          rw [e] at hs'
          have hjk : j.val ≤ k.val := hb
          exact Or.inr ⟨j, lt_of_le_of_ne hjk (fun e' => h (Fin.ext e')), hs'⟩
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and, params_and]
    rintro s (hs | hs)
    · exact ihφ hb.1 s hs
    · exact ihψ hb.2 s hs
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or, params_or]
    rintro s (hs | hs)
    · exact ihφ hb.1 s hs
    · exact ihψ hb.2 s hs
  | hall φ ih => rw [Semiformula.lMap_all, params_all]; exact ih hb
  | hexs φ ih => rw [Semiformula.lMap_exs, params_exs]; exact ih hb

/-- `k(A_k(t, I_k^{≺a}))` is contained in `{⟨k,a⟩} ∪ {level-j tops}`. -/
theorem params_unfold (A : Semisentence (LXIn n) 1) (k : Fin n) (a : StageAt k.val)
    (t : Semiterm (LIinfN n) ξ m) :
    params (unfold A k a t) ⊆ {(⟨k, a⟩ : Stage n)} ∪ {s | ∃ j : Fin n, s = Stage.top j} := by
  rw [unfold, params_subst]
  show params (Rew.emb ▹ formAt A k a) ⊆ _
  rw [params_rew]
  exact params_lMap_stageHom k a A

/-- **Level-bounded refinement of `params_unfold`.** -/
theorem params_unfold_of_levelBounded {A : Semisentence (LXIn n) 1} {k : Fin n}
    (hb : LevelBounded k A) (a : StageAt k.val) (t : Semiterm (LIinfN n) ξ m) :
    ∀ s ∈ params (unfold A k a t),
      s = (⟨k, a⟩ : Stage n) ∨ ∃ j : Fin n, j.val < k.val ∧ s = Stage.top j := by
  rw [unfold, params_subst]
  show ∀ s ∈ params (Rew.emb ▹ formAt A k a), _
  rw [params_rew]
  exact params_lMap_stageHom_of_levelBounded hb

/-- `k` of an embedded formula consists only of tops. -/
theorem params_embed (φ : Semiformula (LXIn n) ξ m) :
    params (embed φ) ⊆ {s | ∃ j : Fin n, s = Stage.top j} := by
  induction φ using Semiformula.rec' with
  | hverum => exact Set.empty_subset _
  | hfalsum => exact Set.empty_subset _
  | hrel r v =>
    rcases r with r | r
    · exact Set.empty_subset _
    · cases r with
      | X => exact Set.empty_subset _
      | I j => exact fun s hs => ⟨j, hs⟩
  | hnrel r v =>
    rcases r with r | r
    · exact Set.empty_subset _
    · cases r with
      | X => exact Set.empty_subset _
      | I j => exact fun s hs => ⟨j, hs⟩
  | hand φ ψ ihφ ihψ =>
    rw [embed, LogicalConnective.HomClass.map_and, params_and]
    exact Set.union_subset ihφ ihψ
  | hor φ ψ ihφ ihψ =>
    rw [embed, LogicalConnective.HomClass.map_or, params_or]
    exact Set.union_subset ihφ ihψ
  | hall φ ih => rw [embed, Semiformula.lMap_all, params_all]; exact ih
  | hexs φ ih => rw [embed, Semiformula.lMap_exs, params_exs]; exact ih

end Params

/-! ### The classes `Σ(Ω_{k+1})` -/

section Sigma

variable {n : ℕ}

/-- A positive atom is allowed in `Σ(Ω_{k+1})` iff its stage level is `≤ k` (design note §2.1:
"every stage literal has level `≤ k`" — this restricts *both* polarities, unlike the one-level
`ID1.SigmaOmega`, which had nothing to restrict positively). -/
def RelSigmaW (k : Fin n) : {m : ℕ} → (LIinfN n).Rel m → Prop
  | _, Sum.inl _ => True
  | _, Sum.inr IInfRelN.X => True
  | _, Sum.inr (IInfRelN.stage s) => s.lvl.val ≤ k.val

/-- A negated atom is allowed in `Σ(Ω_{k+1})` iff its stage level is `≤ k` and it is not the
full, level-`k` predicate `I_k` (design note §2.1: "negated ones have index `≺ Ω_{k+1}`, so
`¬I_k` full is excluded, `¬I_j` full for `j < k` allowed"). -/
def NrelSigmaW (k : Fin n) : {m : ℕ} → (LIinfN n).Rel m → Prop
  | _, Sum.inl _ => True
  | _, Sum.inr IInfRelN.X => True
  | _, Sum.inr (IInfRelN.stage s) => s.lvl.val ≤ k.val ∧ s ≠ Stage.top k

/-- **`Σ(Ω_{k+1})`** (Buchholz's `Σ(κ)` at `κ = Ω_{k+1}`, design note §2.1). -/
def SigmaW (k : Fin n) {ξ : Type*} : {m : ℕ} → Semiformula (LIinfN n) ξ m → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel r _ => RelSigmaW k r
  | _, .nrel r _ => NrelSigmaW k r
  | _, .and φ ψ => SigmaW k φ ∧ SigmaW k ψ
  | _, .or φ ψ => SigmaW k φ ∧ SigmaW k ψ
  | _, .all φ => SigmaW k φ
  | _, .exs φ => SigmaW k φ

variable {ξ : Type*} {m : ℕ} (k : Fin n)

@[simp] theorem sigmaW_verum : SigmaW k (⊤ : Semiformula (LIinfN n) ξ m) := trivial

@[simp] theorem sigmaW_falsum : SigmaW k (⊥ : Semiformula (LIinfN n) ξ m) := trivial

@[simp] theorem sigmaW_rel {j : ℕ} (r : (LIinfN n).Rel j) (v : Fin j → Semiterm (LIinfN n) ξ m) :
    SigmaW k (Semiformula.rel r v) ↔ RelSigmaW k r := Iff.rfl

@[simp] theorem sigmaW_nrel {j : ℕ} (r : (LIinfN n).Rel j) (v : Fin j → Semiterm (LIinfN n) ξ m) :
    SigmaW k (Semiformula.nrel r v) ↔ NrelSigmaW k r := Iff.rfl

@[simp] theorem sigmaW_and (φ ψ : Semiformula (LIinfN n) ξ m) :
    SigmaW k (φ ⋏ ψ) ↔ SigmaW k φ ∧ SigmaW k ψ := Iff.rfl

@[simp] theorem sigmaW_or (φ ψ : Semiformula (LIinfN n) ξ m) :
    SigmaW k (φ ⋎ ψ) ↔ SigmaW k φ ∧ SigmaW k ψ := Iff.rfl

@[simp] theorem sigmaW_all (φ : Semiformula (LIinfN n) ξ (m + 1)) :
    SigmaW k (∀¹ φ) ↔ SigmaW k φ := Iff.rfl

@[simp] theorem sigmaW_exs (φ : Semiformula (LIinfN n) ξ (m + 1)) :
    SigmaW k (∃¹ φ) ↔ SigmaW k φ := Iff.rfl

theorem sigmaW_stageAt_iff (s : Stage n) (t : Semiterm (LIinfN n) ξ m) :
    SigmaW k (stageAt s t) ↔ s.lvl.val ≤ k.val := Iff.rfl

theorem sigmaW_nstageAt_iff (s : Stage n) (t : Semiterm (LIinfN n) ξ m) :
    SigmaW k (nstageAt s t) ↔ s.lvl.val ≤ k.val ∧ s ≠ Stage.top k := Iff.rfl

theorem not_sigmaW_neg_IOmegaAt (t : Semiterm (LIinfN n) ξ m) : ¬ SigmaW k (∼(IOmegaAt k t)) :=
  fun h => h.2 rfl

/-- `Σ(Ω_{k+1})` does not see terms. -/
@[simp] theorem sigmaW_rew {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfN n) ξ₁ m₁ ξ₂ m₂)
    (φ : Semiformula (LIinfN n) ξ₁ m₁) : SigmaW k (ω ▹ φ) ↔ SigmaW k φ := by
  induction φ using Semiformula.rec' generalizing m₂ with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [Semiformula.rew_rel]; exact Iff.rfl
  | hnrel r v => rw [Semiformula.rew_nrel]; exact Iff.rfl
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

@[simp] theorem sigmaW_subst (φ : Semiformula (LIinfN n) ξ 1) (t : Semiterm (LIinfN n) ξ m) :
    SigmaW k (φ/[t]) ↔ SigmaW k φ := sigmaW_rew k _ φ

/-- **`embed A` is `Σ(Ω_{k+1})` iff `A` is positive in `I_k`, given that `A` is level-bounded at
`k`.** The level-boundedness hypothesis is genuinely needed here, unlike the one-level
`ID1.sigmaOmega_embed_iff`: with several levels, a positive occurrence of some *other* `I_j`,
`j > k`, would violate `RelSigmaW`'s level bound even though `PositiveIn k` does not see it. -/
theorem sigmaW_embed_iff {ξ' : Type*} {k : Fin n} :
    ∀ {m : ℕ} {φ : Semiformula (LXIn n) ξ' m},
      LevelBounded k φ → (SigmaW k (embed φ) ↔ PositiveIn k φ) := by
  intro m φ
  induction φ using Semiformula.rec' with
  | hverum => intro _; exact Iff.rfl
  | hfalsum => intro _; exact Iff.rfl
  | hrel r v =>
    intro hb
    rcases r with r | r
    · exact ⟨fun _ => trivial, fun _ => trivial⟩
    · cases r with
      | X => exact ⟨fun _ => trivial, fun _ => trivial⟩
      | I j =>
        have hjk : j.val ≤ k.val := hb
        exact ⟨fun _ => trivial, fun _ => hjk⟩
  | hnrel r v =>
    intro hb
    rcases r with r | r
    · exact Iff.rfl
    · cases r with
      | X => exact Iff.rfl
      | I j =>
        show NrelSigmaW k (embedRel (Sum.inr (IXRelN.I j))) ↔ j ≠ k
        have hjk : j.val ≤ k.val := hb
        simp only [embedRel, NrelSigmaW, Stage.lvl_top]
        constructor
        · rintro ⟨-, hne⟩ rfl
          exact hne rfl
        · intro hne
          exact ⟨hjk, fun e => hne (Stage.top_inj.mp e)⟩
  | hand φ ψ ihφ ihψ => intro hb; exact and_congr (ihφ hb.1) (ihψ hb.2)
  | hor φ ψ ihφ ihψ => intro hb; exact and_congr (ihφ hb.1) (ihψ hb.2)
  | hall φ ih => intro hb; exact ih hb
  | hexs φ ih => intro hb; exact ih hb

/-- A formula all of whose stage parameters have level `≤ k` and are not the full level-`k`
predicate is `Σ(Ω_{k+1})` — the generic fact behind `sigmaW_unfold_of_ne_top`, mirroring
`ID1.sigmaOmega_of_Omega_not_mem`. The hypothesis is exactly `NrelSigmaW k` pointwise on
`params φ`, which is stronger than what a positive atom needs (`RelSigmaW k`), so it gives
`SigmaW k` for `φ` itself as well as (via `params_neg`) for `∼φ`. -/
theorem sigmaW_of_forall_params {k : Fin n} {φ : Semiformula (LIinfN n) ξ m}
    (h : ∀ s ∈ params φ, s.lvl.val ≤ k.val ∧ s ≠ Stage.top k) : SigmaW k φ := by
  induction φ using Semiformula.rec' with
  | hverum => trivial
  | hfalsum => trivial
  | hrel r v =>
    rcases r with r | r
    · trivial
    · cases r with
      | X => trivial
      | stage s => exact (h s rfl).1
  | hnrel r v =>
    rcases r with r | r
    · trivial
    · cases r with
      | X => trivial
      | stage s => exact h s rfl
  | hand φ ψ ihφ ihψ =>
    exact ⟨ihφ (fun s hs => h s (Or.inl hs)), ihψ (fun s hs => h s (Or.inr hs))⟩
  | hor φ ψ ihφ ihψ =>
    exact ⟨ihφ (fun s hs => h s (Or.inl hs)), ihψ (fun s hs => h s (Or.inr hs))⟩
  | hall φ ih => exact ih h
  | hexs φ ih => exact ih h

/-- A formula all of whose stage parameters have level `≤ k` and are not the full level-`k`
predicate is `Σ(Ω_{k+1})`, and so is its negation. -/
theorem sigmaW_and_neg_of_forall_params {k : Fin n} {φ : Semiformula (LIinfN n) ξ m}
    (h : ∀ s ∈ params φ, s.lvl.val ≤ k.val ∧ s ≠ Stage.top k) :
    SigmaW k φ ∧ SigmaW k (∼φ) :=
  ⟨sigmaW_of_forall_params h, sigmaW_of_forall_params (by rwa [params_neg])⟩

/-- **Below the top of level `k`, the unfolding is `Σ(Ω_{k+1})`, and so is its negation**: it has
no full level-`k` predicate at all — every parameter of `unfold A k a t` is either `⟨k,a⟩`
(`a ≠ top`, so not `Stage.top k`) or the top of a level strictly below `k` (so also not
`Stage.top k`, being at a different level). -/
theorem sigmaW_unfold_of_ne_top {A : Semisentence (LXIn n) 1} {k : Fin n} (hb : LevelBounded k A)
    {a : StageAt k.val} (ha : a ≠ StageAt.top k.val) (t : Semiterm (LIinfN n) ξ m) :
    SigmaW k (unfold A k a t) ∧ SigmaW k (∼(unfold A k a t)) := by
  refine sigmaW_and_neg_of_forall_params (fun s hs => ?_)
  rcases params_unfold_of_levelBounded hb a t s hs with rfl | ⟨j, hj, rfl⟩
  · exact ⟨le_refl _, fun e => ha (Subtype.ext (congrArg Stage.val e))⟩
  · refine ⟨le_of_lt hj, ?_⟩
    rw [Ne, Stage.top_inj]
    exact fun e => absurd (congrArg Fin.val e) (Nat.ne_of_lt hj)

/-- **At the top of level `k`, the unfolding of an operator form positive in `I_k` is
`Σ(Ω_{k+1})`** (Freund, proof of Theorem 6.7, case (Fix), read at level `k`). -/
theorem sigmaW_unfold_top {A : Semisentence (LXIn n) 1} {k : Fin n} (hb : LevelBounded k A)
    (hp : PositiveIn k A) (t : Semiterm (LIinfN n) ξ m) :
    SigmaW k (unfold A k (StageAt.top k.val) t) := by
  rw [unfold, sigmaW_subst]
  show SigmaW k (Rew.emb ▹ formAt A k (StageAt.top k.val))
  rw [sigmaW_rew, formAt_top]
  exact (sigmaW_embed_iff hb).mpr hp

end Sigma

/-! ### Bounding: `φ ↦ φ^β` at level `k` -/

section Cap

variable {n : ℕ}

theorem stage_mk_eq_top_iff {k : Fin n} {a : StageAt k.val} :
    (⟨k, a⟩ : Stage n) = Stage.top k ↔ a = StageAt.top k.val :=
  ⟨fun e => Subtype.ext (congrArg Stage.val e), fun e => by subst e; rfl⟩

/-- `I_k^{≺Ω_{k+1}} ↦ I_k^{≺b}`; every other symbol, including a *different* level's stage
predicate, is fixed. -/
def capRelAt (k : Fin n) (b : StageAt k.val) : {m : ℕ} → (LIinfN n).Rel m → (LIinfN n).Rel m
  | _, Sum.inl r => Sum.inl r
  | _, Sum.inr IInfRelN.X => Sum.inr IInfRelN.X
  | _, Sum.inr (IInfRelN.stage s) =>
      Sum.inr (IInfRelN.stage (if _ : s = Stage.top k then (⟨k, b⟩ : Stage n) else s))

theorem capRelAt_stage (k : Fin n) (b : StageAt k.val) (s : Stage n) :
    capRelAt k b (Sum.inr (IInfRelN.stage s)) =
      Sum.inr (IInfRelN.stage (if _ : s = Stage.top k then (⟨k, b⟩ : Stage n) else s)) :=
  rfl

variable {ξ : Type*} {m : ℕ}

/-- **`φ^β` at level `k`**: every literal `I_k^{≺Ω_{k+1}} t`, `¬I_k^{≺Ω_{k+1}} t` replaced by
`I_k^{≺b} t`, `¬I_k^{≺b} t`; every other stage literal untouched. -/
def capAt (k : Fin n) (b : StageAt k.val) : {m : ℕ} → Semiformula (LIinfN n) ξ m →
    Semiformula (LIinfN n) ξ m
  | _, .verum => .verum
  | _, .falsum => .falsum
  | _, .rel r v => .rel (capRelAt k b r) v
  | _, .nrel r v => .nrel (capRelAt k b r) v
  | _, .and φ ψ => .and (capAt k b φ) (capAt k b ψ)
  | _, .or φ ψ => .or (capAt k b φ) (capAt k b ψ)
  | _, .all φ => .all (capAt k b φ)
  | _, .exs φ => .exs (capAt k b φ)

variable (k : Fin n) (b : StageAt k.val)

@[simp] theorem capAt_verum : capAt k b (⊤ : Semiformula (LIinfN n) ξ m) = ⊤ := rfl

@[simp] theorem capAt_falsum : capAt k b (⊥ : Semiformula (LIinfN n) ξ m) = ⊥ := rfl

@[simp] theorem capAt_rel {j : ℕ} (r : (LIinfN n).Rel j) (v : Fin j → Semiterm (LIinfN n) ξ m) :
    capAt k b (Semiformula.rel r v) = Semiformula.rel (capRelAt k b r) v := rfl

@[simp] theorem capAt_nrel {j : ℕ} (r : (LIinfN n).Rel j) (v : Fin j → Semiterm (LIinfN n) ξ m) :
    capAt k b (Semiformula.nrel r v) = Semiformula.nrel (capRelAt k b r) v := rfl

@[simp] theorem capAt_and (φ ψ : Semiformula (LIinfN n) ξ m) :
    capAt k b (φ ⋏ ψ) = capAt k b φ ⋏ capAt k b ψ := rfl

@[simp] theorem capAt_or (φ ψ : Semiformula (LIinfN n) ξ m) :
    capAt k b (φ ⋎ ψ) = capAt k b φ ⋎ capAt k b ψ := rfl

@[simp] theorem capAt_all (φ : Semiformula (LIinfN n) ξ (m + 1)) :
    capAt k b (∀¹ φ) = ∀¹ capAt k b φ := rfl

@[simp] theorem capAt_exs (φ : Semiformula (LIinfN n) ξ (m + 1)) :
    capAt k b (∃¹ φ) = ∃¹ capAt k b φ := rfl

/-- `(I_k t)^β = I_k^{≺β} t`. -/
@[simp] theorem capAt_IOmegaAt (t : Semiterm (LIinfN n) ξ m) :
    capAt k b (IOmegaAt k t) = stageAt ⟨k, b⟩ t := by
  show Semiformula.rel (capRelAt k b (Sum.inr (IInfRelN.stage (Stage.top k)))) ![t] = _
  rw [capRelAt_stage, dif_pos rfl]
  rfl

/-- A stage other than the top of level `k` is untouched. -/
theorem capAt_stageAt_of_ne_top {s : Stage n} (hs : s ≠ Stage.top k) (t : Semiterm (LIinfN n) ξ m) :
    capAt k b (stageAt s t) = stageAt s t := by
  show Semiformula.rel (capRelAt k b (Sum.inr (IInfRelN.stage s))) ![t] = _
  rw [capRelAt_stage, dif_neg hs]
  rfl

theorem capAt_nstageAt_of_ne_top {s : Stage n} (hs : s ≠ Stage.top k) (t : Semiterm (LIinfN n) ξ m) :
    capAt k b (nstageAt s t) = nstageAt s t := by
  show Semiformula.nrel (capRelAt k b (Sum.inr (IInfRelN.stage s))) ![t] = _
  rw [capRelAt_stage, dif_neg hs]
  rfl

/-- `(¬φ)^β = ¬(φ^β)`. -/
@[simp] theorem capAt_neg (φ : Semiformula (LIinfN n) ξ m) : capAt k b (∼φ) = ∼(capAt k b φ) := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **Bounding commutes with every rewriting.** -/
theorem capAt_rew {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfN n) ξ₁ m₁ ξ₂ m₂)
    (φ : Semiformula (LIinfN n) ξ₁ m₁) : capAt k b (ω ▹ φ) = ω ▹ capAt k b φ := by
  induction φ using Semiformula.rec' generalizing m₂ with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [Semiformula.rew_rel, capAt_rel, capAt_rel, Semiformula.rew_rel]
  | hnrel r v => rw [Semiformula.rew_nrel, capAt_nrel, capAt_nrel, Semiformula.rew_nrel]
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

theorem capAt_subst (φ : Semiformula (LIinfN n) ξ 1) (t : Semiterm (LIinfN n) ξ m) :
    capAt k b (φ/[t]) = (capAt k b φ)/[t] := capAt_rew k b _ φ

/-- **Interaction of `capAt k b` with `stageHom k`**: `A` with `I_k ↦ I_k^{≺a}` (other levels at
their own top), bounded at level `k`, is `A` with `I_k ↦ I_k^{≺a'}`, `a' = b` if `a` was the top of
level `k` and `a' = a` otherwise — the direct analogue of `ID1.cap_lMap_stageHom`. -/
theorem capAt_lMap_stageHom (a : StageAt k.val) {ξ' : Type*} {m' : ℕ}
    (φ : Semiformula (LXIn n) ξ' m') :
    capAt k b (Semiformula.lMap (stageHom k a) φ) =
      Semiformula.lMap (stageHom k (if a = StageAt.top k.val then b else a)) φ := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
    show capAt k b (Semiformula.rel (stageRel k a r) (Semiterm.lMap (stageHom k a) ∘ v)) =
      Semiformula.rel (stageRel k (if a = StageAt.top k.val then b else a) r)
        (Semiterm.lMap (stageHom k (if a = StageAt.top k.val then b else a)) ∘ v)
    rw [capAt_rel]
    congr 1
    · rcases r with r | r
      · rfl
      · cases r with
        | X => rfl
        | I j =>
          by_cases h : j = k
          · subst h
            rw [stageRel_I, dif_pos rfl, capRelAt_stage, stageRel_I, dif_pos rfl]
            congr 1
            by_cases h' : a = StageAt.top j.val
            · rw [dif_pos (stage_mk_eq_top_iff.mpr h'), if_pos h']
            · rw [dif_neg (fun e => h' (stage_mk_eq_top_iff.mp e)), if_neg h']
          · rw [stageRel_I, dif_neg h, capRelAt_stage,
              dif_neg (Stage.ne_top_of_lvl_ne (by simpa using h)), stageRel_I, dif_neg h]
    · funext i; exact lMap_stageHom_term k k a _ (v i)
  | hnrel r v =>
    show capAt k b (Semiformula.nrel (stageRel k a r) (Semiterm.lMap (stageHom k a) ∘ v)) =
      Semiformula.nrel (stageRel k (if a = StageAt.top k.val then b else a) r)
        (Semiterm.lMap (stageHom k (if a = StageAt.top k.val then b else a)) ∘ v)
    rw [capAt_nrel]
    congr 1
    · rcases r with r | r
      · rfl
      · cases r with
        | X => rfl
        | I j =>
          by_cases h : j = k
          · subst h
            rw [stageRel_I, dif_pos rfl, capRelAt_stage, stageRel_I, dif_pos rfl]
            congr 1
            by_cases h' : a = StageAt.top j.val
            · rw [dif_pos (stage_mk_eq_top_iff.mpr h'), if_pos h']
            · rw [dif_neg (fun e => h' (stage_mk_eq_top_iff.mp e)), if_neg h']
          · rw [stageRel_I, dif_neg h, capRelAt_stage,
              dif_neg (Stage.ne_top_of_lvl_ne (by simpa using h)), stageRel_I, dif_neg h]
    · funext i; exact lMap_stageHom_term k k a _ (v i)
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and, capAt_and,
      ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or, capAt_or,
      ihφ, ihψ]
  | hall φ ih => rw [Semiformula.lMap_all, Semiformula.lMap_all, capAt_all, ih]
  | hexs φ ih => rw [Semiformula.lMap_exs, Semiformula.lMap_exs, capAt_exs, ih]

/-- `(embed φ)^β` at level `k` is `φ` with `I_k ↦ I_k^{≺b}`. -/
theorem capAt_embed (φ : Semiformula (LXIn n) ξ m) :
    capAt k b (embed φ) = Semiformula.lMap (stageHom k b) φ := by
  rw [embed, ← stageHom_top k, capAt_lMap_stageHom, if_pos rfl]

/-- The unfolding at level `k` commutes with bounding at level `k`. -/
theorem capAt_unfold (A : Semisentence (LXIn n) 1) (a : StageAt k.val)
    (t : Semiterm (LIinfN n) ξ m) :
    capAt k b (unfold A k a t) = unfold A k (if a = StageAt.top k.val then b else a) t := by
  rw [unfold, unfold, capAt_subst]
  congr 1
  show capAt k b (Rew.emb ▹ formAt A k a) = Rew.emb ▹ formAt A k _
  rw [capAt_rew, formAt, formAt, capAt_lMap_stageHom]

/-- **`A_k(t, I_k^{≺Ω_{k+1}})^β = A_k(t, I_k^{≺β})`** — the (Fix) case of boundedness, at
level `k`. -/
theorem capAt_unfold_top (A : Semisentence (LXIn n) 1) (t : Semiterm (LIinfN n) ξ m) :
    capAt k b (unfold A k (StageAt.top k.val) t) = unfold A k b t := by
  rw [capAt_unfold, if_pos rfl]

/-- **`A_k(t, I_k^{≺a})^β = A_k(t, I_k^{≺a})` for `a ≠` the top of level `k`.** -/
theorem capAt_unfold_of_ne_top {A : Semisentence (LXIn n) 1} {a : StageAt k.val}
    (ha : a ≠ StageAt.top k.val) (t : Semiterm (LIinfN n) ξ m) :
    capAt k b (unfold A k a t) = unfold A k a t := by
  rw [capAt_unfold, if_neg ha]

theorem relParams_capRelAt : ∀ {j : ℕ} (r : (LIinfN n).Rel j),
    relParams (capRelAt k b r) ⊆ relParams r ∪ {(⟨k, b⟩ : Stage n)}
  | _, Sum.inl _ => Set.empty_subset _
  | _, Sum.inr IInfRelN.X => Set.empty_subset _
  | _, Sum.inr (IInfRelN.stage s) => by
    rw [capRelAt_stage]
    split_ifs with h
    · exact fun x hx => Or.inr hx
    · exact fun x hx => Or.inl hx

/-- `k(φ^β) ⊆ k(φ) ∪ {(k,β)}`, at level `k`. -/
theorem params_capAt (φ : Semiformula (LIinfN n) ξ m) :
    params (capAt k b φ) ⊆ params φ ∪ {(⟨k, b⟩ : Stage n)} := by
  induction φ using Semiformula.rec' with
  | hverum => exact Set.empty_subset _
  | hfalsum => exact Set.empty_subset _
  | hrel r v => exact relParams_capRelAt k b r
  | hnrel r v => exact relParams_capRelAt k b r
  | hand φ ψ ihφ ihψ =>
    rw [capAt_and, params_and, params_and]
    exact Set.union_subset (ihφ.trans (Set.union_subset_union_left _ Set.subset_union_left))
      (ihψ.trans (Set.union_subset_union_left _ Set.subset_union_right))
  | hor φ ψ ihφ ihψ =>
    rw [capAt_or, params_or, params_or]
    exact Set.union_subset (ihφ.trans (Set.union_subset_union_left _ Set.subset_union_left))
      (ihψ.trans (Set.union_subset_union_left _ Set.subset_union_right))
  | hall φ ih => exact ih
  | hexs φ ih => exact ih

end Cap

end IDn

end OrdinalAnalysis
