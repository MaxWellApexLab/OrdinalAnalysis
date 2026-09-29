/-
  The infinitary language of `ID_ω`: levels `k : ℕ` (no top bound, unlike `IDn.LIinfN n`'s
  `Fin n`), stage predicates `I_k^{≺α}` exactly as in `IDn/Language.lean`, plus a genuinely new
  binary atom family `Jlev ℓ`, `ℓ : WithTop ℕ`.

  Source: the design notes §3.1 "Language `LIinfW`"; the
  multi-level `IDn/Language.lean` is the template (ported almost verbatim for `StageAt`/
  `Stage`/stage atoms/`params`/`SigmaW`/`capAt`), generalised from `k : Fin n` to `k : ℕ` and
  extended with `Jlev`. `IDw/Theory.lean` (`LXJ`, `LForm`, `FormJ`, `PQRel`) is the finitary
  theory this language embeds/unfolds; both are read as of `IDw/Theory.lean`'s current,
  `lean_warm.py`-verified-green state (its `termCast` now goes through a proper
  `homLFormLXJ : LForm →ᵥ LXJ`, the same pattern followed here for `formHomAt`).

  **`Jlev`, and why it is unavoidable** (design §3.1, §8.4's kill criterion). `IDw A`'s theory
  is *uniform*: one binary predicate `J(y,x)`, one schema `A(x,y)` reused at every level, with
  `y` a genuine *bound variable* of the closure/induction axioms — not something Lean case-splits
  on (`IDw/Theory.lean`'s header). An infinitary derivation must still expose, level by level,
  "`t` is in the `y`-th set with `y` ranging over an initial segment of `ℕ`" as an atomic,
  rank-bearing formula; a *unary* per-level family alone cannot express "for all `y`, …" as one
  atom. Hence `Jlev ℓ (s, t)` : "`val s < ℓ` and `t ∈ I_{val s}`" — `Jlev ⊤` is the full,
  unrestricted `J`; `Jlev k` (`k : ℕ`, i.e. `↑k : WithTop ℕ`) is `J` *read through levels `< k`
  only*, exactly Pohlers' `J^{≺y}` at `y = k̄`. There is no level-`ω` stage predicate (design §0
  item 3): `Jlev` is the only new relation, and it takes the place a hypothetical "`I_ω`" would
  have had to play, without ever needing one.

  **Two translations out of the finitary language(s), both by a plain `Language.Hom`** (design:
  "a plain `lMap`, simpler than today's `stageHom`, which had to fix every other level's
  symbol"):

    * `embedW : LXJ →ᵥ LIinfW` (arity-preserving: `J : XJRel 2` and `Jlev ⊤ : IInfRelW 2` are
      both binary): `X ↦ X`, `J ↦ Jlev ⊤`. This is the *one*, level-independent embedding of the
      closed theory's own binary `J` — used for the embedding theorem (stage `E`, not here).
    * `formHomAt (k) (g) : LForm →ᵥ LIinfW` (also arity-preserving: `P : PQRel 1 ↦ I_k^{≺g} :
      IInfRelW 1`, `Q : PQRel 2 ↦ Jlev k : IInfRelW 2`): the per-level unfolding of the *schema*
      `A : FormJ`. Unlike `IDn.stageHom`, which had to route every *other* level `j ≠ k` to its
      own top `I_j^{≺Ω_{j+1}}` (since `IDn`'s per-level operator forms mention other levels'
      predicates directly), `formHomAt` never needs to: `A`'s only "other levels" placeholder is
      the single symbol `Q`, uniformly compiled to `Jlev k` regardless of which level is meant.
      This is exactly what removes the syntactic side condition `LevelBounded` from every lemma
      below (`IDw/Theory.lean`'s header: "no `LevelBounded` side condition to state or
      discharge") — `sigmaW_unfoldW_of_ne_top` needs no boundedness hypothesis at all, where its
      `IDn` counterpart (`sigmaW_unfold_of_ne_top`) needs `LevelBounded k A`.
    * `unfoldW A k g t := A[y := k̄, x := t]` under `formHomAt k g` (`A : FormJ = Semisentence
      LForm 2`, `#0 = x`, `#1 = y` — `IDw/Theory.lean`'s bound-variable convention): first
      `lMap (formHomAt k g)` (a structural, non-recursive relation-symbol swap: no `Y`-threading
      or `Rew.bShift` is needed here, unlike `Theory.AAt`, precisely because `P`/`Q` become
      *fixed* atoms `I_k^{≺g}`/`Jlev k` at every depth, not a substituted formula `F/[t,Y]`), then
      the 2-ary numeral/argument substitution `/[t, k̄]`.

  **`params`, `Σ(Ω_{k+1})`, `capAt` for `Jlev`** (design §3.1, verbatim): `params (Jlev ℓ …) = ∅`
  (a `Jlev`-atom is not a stage-family index, so it never contributes a `Stage` parameter — this
  is what makes `unfoldW`'s parameter set *exactly* `{⟨k,g⟩}`, no "other levels" term at all,
  the source of the boundedness-free lemmas above); `RelSigmaW k`/`NrelSigmaW k` at `Jlev ℓ` both
  read `ℓ ≤ (k : WithTop ℕ)` ("`Jlev ℓ` for `ℓ ≤ k` in both polarities… `Jlev ⊤` never" — `⊤ ≤
  ↑k` is `False` by `WithTop`'s order, so the exclusion of `Jlev ⊤` is not a separate clause but
  a consequence, recorded below as `not_relSigmaW_jlev_top`); `capAt k b` is the *identity* on
  every `Jlev` atom (`capRelAt`'s `jlev` case, no `if`).

  Contents.

    `StageAt`, `StageAt.top`                         the bounds `α ⪯ Ω_{k+1}` at one level, `k : ℕ`
    `Stage`, `Stage.lvl`, `Stage.val`, `Stage.top`    the stage indices `(k, α)`
    `IInfRelW`, `IInfLangW`, `LIinfW`                 the language, with `Jlev`
    `XinfAt`, `stageAt`, `nstageAt`, `IOmegaAt`        `X t`, `I_k^{≺α} t`, `¬…`, `I_k t`
    `jlevAt`, `njlevAt`                                `Jlev ℓ (s,t)`, `¬…`
    `embedW`, `embed`                                  `LXJ →ᵥ LIinfW`: `X ↦ X`, `J ↦ Jlev ⊤`
    `formHomAt`, `formAtW`, `unfoldW`                  `LForm →ᵥ LIinfW` at `(k,g)`, and the unfolding
    `params`                                            `k(φ)`, `Jlev` contributes nothing
    `SigmaW`                                            the classes `Σ(Ω_{k+1})`, with `Jlev`
    `capAt`                                             `φ ↦ φ^β` at level `k`, identity on `Jlev`
    `sigmaW_unfoldW_of_ne_top`, `sigmaW_unfoldW_top`     the `L`-stage `sigmaW_unfoldW` probe (§8.3)
-/
import OrdinalAnalysis.IDw.Theory
import OrdinalAnalysis.Ordinal.ThetaV.Dom

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

open LO LO.FirstOrder

/-! ### Stages (levels `k : ℕ`, unbounded — cf. `IDn.StageAt`/`IDn.Stage`, `k : Fin n`) -/

/-- The stage bounds at level `k`: `α ⪯ Ω_{k+1}` (`ThetaVNoteD.Omega k`). -/
abbrev StageAt (k : ℕ) : Type := {a : ThetaVNoteD // a ≤ ThetaVNoteD.Omega k}

namespace StageAt

/-- The top stage at level `k`, `Ω_{k+1}`; `I_k^{≺Ω_{k+1}}` is the predicate `I_k`. -/
def top (k : ℕ) : StageAt k := ⟨ThetaVNoteD.Omega k, le_refl _⟩

@[simp] theorem top_val (k : ℕ) : (top k).1 = ThetaVNoteD.Omega k := rfl

/-- A countable stage `α ≺ Ω_{k+1}` at level `k`. -/
def ofLt (k : ℕ) (a : ThetaVNoteD) (h : a < ThetaVNoteD.Omega k) : StageAt k := ⟨a, le_of_lt h⟩

@[simp] theorem ofLt_val (k : ℕ) (a : ThetaVNoteD) (h : a < ThetaVNoteD.Omega k) :
    (ofLt k a h).1 = a := rfl

theorem eq_top_iff {k : ℕ} {a : StageAt k} : a = top k ↔ a.1 = ThetaVNoteD.Omega k :=
  Subtype.ext_iff

theorem lt_Omega_of_ne_top {k : ℕ} {a : StageAt k} (h : a ≠ top k) : a.1 < ThetaVNoteD.Omega k :=
  lt_of_le_of_ne a.2 (fun e => h (Subtype.ext e))

theorem ne_top_of_lt_Omega {k : ℕ} {a : StageAt k} (h : a.1 < ThetaVNoteD.Omega k) : a ≠ top k :=
  fun e => ne_of_lt h (eq_top_iff.mp e)

theorem ne_top_iff {k : ℕ} {a : StageAt k} : a ≠ top k ↔ a.1 < ThetaVNoteD.Omega k :=
  ⟨lt_Omega_of_ne_top, ne_top_of_lt_Omega⟩

end StageAt

/-- The stage indices of `ID_ω`: a level `k : ℕ` together with a bound `α ⪯ Ω_{k+1}`. No top
bound on `k` (`IDn.Stage n`'s `Fin n` becomes plain `ℕ`, design §3.1). -/
abbrev Stage : Type := Σ k : ℕ, StageAt k

namespace Stage

/-- The level of a stage index. -/
def lvl (s : Stage) : ℕ := s.1

/-- The bound `α` of a stage index. -/
def val (s : Stage) : ThetaVNoteD := s.2.1

theorem le (s : Stage) : s.val ≤ ThetaVNoteD.Omega s.lvl := s.2.2

/-- The top stage `(k, Ω_{k+1})`; `I_k^{≺Ω_{k+1}}` is the predicate `I_k`. -/
def top (k : ℕ) : Stage := ⟨k, StageAt.top k⟩

@[simp] theorem lvl_top (k : ℕ) : (top k).lvl = k := rfl

@[simp] theorem val_top (k : ℕ) : (top k).val = ThetaVNoteD.Omega k := rfl

theorem top_injective : Function.Injective top := by
  intro i j h; have := congrArg lvl h; simpa using this

@[simp] theorem top_inj {i j : ℕ} : top i = top j ↔ i = j := top_injective.eq_iff

theorem ne_top_of_lvl_ne {s : Stage} {k : ℕ} (h : s.lvl ≠ k) : s ≠ top k :=
  fun e => h (by rw [e, lvl_top])

theorem mk_eq_top_iff {k : ℕ} {a : StageAt k} : (⟨k, a⟩ : Stage) = top k ↔ a = StageAt.top k :=
  ⟨fun e => Subtype.ext (congrArg val e), fun e => by subst e; rfl⟩

end Stage

instance : DecidableEq Stage := by unfold Stage StageAt; infer_instance

/-! ### The language `LIinfW`: `X`, the stage predicates `I_k^{≺α}`, and the new `Jlev ℓ` -/

/-- The fresh relation symbols: the free predicate `X`, one stage predicate `I_k^{≺α}` per stage
index, and — genuinely new — one binary `Jlev ℓ` per `ℓ : WithTop ℕ` (`Jlev ⊤` is the full `J`;
`Jlev k`, `k : ℕ`, is `J` read through levels `< k` only). -/
inductive IInfRelW : ℕ → Type
  | X : IInfRelW 1
  | stage : Stage → IInfRelW 1
  | jlev : WithTop ℕ → IInfRelW 2

instance {k : ℕ} : DecidableEq (IInfRelW k) := fun a b => by
  cases a with
  | X => cases b with
    | X => exact isTrue rfl
    | stage _ => exact isFalse (by intro h; cases h)
  | stage a => cases b with
    | X => exact isFalse (by intro h; cases h)
    | stage b => exact if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (by injection e))
  | jlev a => cases b with
    | jlev b => exact if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (by injection e))

/-- The fresh part of the language: no function symbols. -/
abbrev IInfLangW : Language where
  Func := fun _ => PEmpty
  Rel := IInfRelW

/-- **The infinitary language** of `ID_ω`: arithmetic, `X`, the stage predicates `I_k^{≺α}`,
`k : ℕ`, `α ⪯ Ω_{k+1}`, and `Jlev ℓ`, `ℓ : WithTop ℕ`. -/
abbrev LIinfW : Language := Language.add ℒₒᵣ IInfLangW

instance : Language.ORing LIinfW where
  eq := Sum.inl Language.Eq.eq
  lt := Sum.inl Language.LT.lt
  zero := Sum.inl Language.Zero.zero
  one := Sum.inl Language.One.one
  add := Sum.inl Language.Add.add
  mul := Sum.inl Language.Mul.mul

/-- The embedding of arithmetic into `LIinfW`. -/
abbrev toLIinfW : ℒₒᵣ →ᵥ LIinfW := Language.Hom.add₁ ℒₒᵣ IInfLangW

/-! ### The atoms -/

section Atoms

variable {ξ : Type*} {m : ℕ}

/-- `X(t)`. -/
def XinfAt (t : Semiterm LIinfW ξ m) : Semiformula LIinfW ξ m :=
  Semiformula.rel (Sum.inr IInfRelW.X) ![t]

/-- `I_k^{≺α} t`: "`t` enters level `k` at a stage below `α`". -/
def stageAt (s : Stage) (t : Semiterm LIinfW ξ m) : Semiformula LIinfW ξ m :=
  Semiformula.rel (Sum.inr (IInfRelW.stage s)) ![t]

/-- `¬I_k^{≺α} t`. -/
def nstageAt (s : Stage) (t : Semiterm LIinfW ξ m) : Semiformula LIinfW ξ m :=
  Semiformula.nrel (Sum.inr (IInfRelW.stage s)) ![t]

/-- `I_k t = I_k^{≺Ω_{k+1}} t`. -/
def IOmegaAt (k : ℕ) (t : Semiterm LIinfW ξ m) : Semiformula LIinfW ξ m :=
  stageAt (Stage.top k) t

/-- `Jlev ℓ (s, t)`: "`val s < ℓ` and `t ∈ I_{val s}`" (`Jlev ⊤` is the full `J`). -/
def jlevAt (ℓ : WithTop ℕ) (s t : Semiterm LIinfW ξ m) : Semiformula LIinfW ξ m :=
  Semiformula.rel (Sum.inr (IInfRelW.jlev ℓ)) ![s, t]

/-- `¬Jlev ℓ (s, t)`. -/
def njlevAt (ℓ : WithTop ℕ) (s t : Semiterm LIinfW ξ m) : Semiformula LIinfW ξ m :=
  Semiformula.nrel (Sum.inr (IInfRelW.jlev ℓ)) ![s, t]

@[simp] theorem neg_stageAt (s : Stage) (t : Semiterm LIinfW ξ m) :
    ∼(stageAt s t) = nstageAt s t := rfl

@[simp] theorem neg_nstageAt (s : Stage) (t : Semiterm LIinfW ξ m) :
    ∼(nstageAt s t) = stageAt s t := rfl

@[simp] theorem neg_jlevAt (ℓ : WithTop ℕ) (s t : Semiterm LIinfW ξ m) :
    ∼(jlevAt ℓ s t) = njlevAt ℓ s t := rfl

@[simp] theorem neg_njlevAt (ℓ : WithTop ℕ) (s t : Semiterm LIinfW ξ m) :
    ∼(njlevAt ℓ s t) = jlevAt ℓ s t := rfl

theorem IOmegaAt_eq (k : ℕ) (t : Semiterm LIinfW ξ m) : IOmegaAt k t = stageAt (Stage.top k) t := rfl

/-- A unary atom is `r ![v 0]`. -/
theorem rel_eq_vec {k : ℕ} (r : LIinfW.Rel 1) (v : Fin 1 → Semiterm LIinfW ξ k) :
    Semiformula.rel r v = Semiformula.rel r ![v 0] := by
  congr 1; funext i; obtain rfl := Subsingleton.elim i 0; rfl

/-- A binary atom is `r ![v 0, v 1]`. -/
theorem rel_eq_vec2 {k : ℕ} (r : LIinfW.Rel 2) (v : Fin 2 → Semiterm LIinfW ξ k) :
    Semiformula.rel r v = Semiformula.rel r ![v 0, v 1] := by
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

end Atoms

/-! ### `embedW : LXJ →ᵥ LIinfW`: `X ↦ X`, `J ↦ Jlev ⊤` -/

section EmbedW

/-- The function symbols of `LXJ` are those of arithmetic (no function symbols of its own, same
shape as `IDn.stageFuncN`). -/
def embedFuncW : {k : ℕ} → LXJ.Func k → LIinfW.Func k
  | _, Sum.inl f => Sum.inl f
  | _, Sum.inr f => PEmpty.elim f

/-- `X ↦ X`, `J ↦ Jlev ⊤` (both binary; the *one*, level-independent translation of the closed
theory's own `J`). -/
def embedRelW : {m : ℕ} → LXJ.Rel m → LIinfW.Rel m
  | _, Sum.inl r => Sum.inl r
  | _, Sum.inr XJRel.X => Sum.inr IInfRelW.X
  | _, Sum.inr XJRel.J => Sum.inr (IInfRelW.jlev ⊤)

/-- **The embedding of `LXJ` into `LIinfW`.** -/
def embedW : LXJ →ᵥ LIinfW := ⟨embedFuncW, embedRelW⟩

variable {ξ : Type*} {m : ℕ}

/-- **The embedding of `LXJ`-formulas into `LIinfW`.** -/
def embed (φ : Semiformula LXJ ξ m) : Semiformula LIinfW ξ m := Semiformula.lMap embedW φ

theorem embed_neg (φ : Semiformula LXJ ξ m) : embed (∼φ) = ∼(embed φ) := by simp [embed]

/-- `X t ↦ X t`. -/
theorem embed_Xat (t : Semiterm LXJ ξ m) : embed (Xat t) = XinfAt (Semiterm.lMap embedW t) :=
  rel_eq_vec (Sum.inr IInfRelW.X) (Semiterm.lMap embedW ∘ ![t])

/-- `J(s,t) ↦ Jlev ⊤ (s,t)`. -/
theorem embed_Jat (s t : Semiterm LXJ ξ m) :
    embed (Jat s t) = jlevAt ⊤ (Semiterm.lMap embedW s) (Semiterm.lMap embedW t) :=
  rel_eq_vec2 (Sum.inr (IInfRelW.jlev ⊤)) (Semiterm.lMap embedW ∘ ![s, t])

end EmbedW

/-! ### `formHomAt (k) (g) : LForm →ᵥ LIinfW`, and the unfolding `unfoldW` -/

section UnfoldW

/-- The function symbols of `LForm` are those of arithmetic, same shape as `embedFuncW`. -/
def formFuncAt : {k : ℕ} → LForm.Func k → LIinfW.Func k
  | _, Sum.inl f => Sum.inl f
  | _, Sum.inr f => PEmpty.elim f

/-- `P ↦ I_k^{≺g}`, `Q ↦ Jlev k` — a *fixed*, structural relation-symbol swap, valid at every
level `k` and every occurrence depth inside `A` (no `Y`-threading needed, unlike
`Theory.AAt`/`Theory.homLFormLXJ`: here the level is already a compile-time constant `k`, not a
bound variable of the target formula). -/
def formRelAt (k : ℕ) (g : StageAt k) : {m : ℕ} → LForm.Rel m → LIinfW.Rel m
  | _, Sum.inl r => Sum.inl r
  | _, Sum.inr PQRel.P => Sum.inr (IInfRelW.stage ⟨k, g⟩)
  | _, Sum.inr PQRel.Q => Sum.inr (IInfRelW.jlev (k : WithTop ℕ))

/-- **`P ↦ I_k^{≺g}`, `Q ↦ Jlev k`, as a homomorphism of languages.** -/
def formHomAt (k : ℕ) (g : StageAt k) : LForm →ᵥ LIinfW := ⟨formFuncAt, formRelAt k g⟩

/-- `A` compiled at level `k`, bound `g`, still a 2-variable sentence (`#0 = x`, `#1 = y`, not yet
substituted). -/
def formAtW (A : FormJ) (k : ℕ) (g : StageAt k) : Semisentence LIinfW 2 :=
  Semiformula.lMap (formHomAt k g) A

variable {ξ : Type*} {m : ℕ}

/-- **The stage unfolding** `A[y := k̄, x := t]`, `P ↦ I_k^{≺g}`, `Q ↦ Jlev k` (design §3.1). -/
def unfoldW (A : FormJ) (k : ℕ) (g : StageAt k) (t : Semiterm LIinfW ξ m) :
    Semiformula LIinfW ξ m :=
  (Rewriting.emb (formAtW A k g) : Semiformula LIinfW ξ 2)/[t, (Semiterm.numeral k : Semiterm LIinfW ξ m)]

end UnfoldW

/-! ### The parameters `k(φ)` (`Jlev` contributes nothing, design §3.1: `params (Jlev …) = ∅`) -/

section Params

/-- The parameters of a relation symbol: `{s}` for `I_{s.lvl}^{≺s.val}`, empty otherwise —
including every `Jlev ℓ`, which is not a stage-family index. -/
def relParams : {k : ℕ} → LIinfW.Rel k → Set Stage
  | _, Sum.inl _ => ∅
  | _, Sum.inr IInfRelW.X => ∅
  | _, Sum.inr (IInfRelW.stage s) => {s}
  | _, Sum.inr (IInfRelW.jlev _) => ∅

/-- **`k(φ)`**, the stage indices of a formula. -/
def params {ξ : Type*} : {m : ℕ} → Semiformula LIinfW ξ m → Set Stage
  | _, .verum => ∅
  | _, .falsum => ∅
  | _, .rel r _ => relParams r
  | _, .nrel r _ => relParams r
  | _, .and φ ψ => params φ ∪ params ψ
  | _, .or φ ψ => params φ ∪ params ψ
  | _, .all φ => params φ
  | _, .exs φ => params φ

variable {ξ : Type*} {m : ℕ}

@[simp] theorem params_verum : params (⊤ : Semiformula LIinfW ξ m) = ∅ := rfl

@[simp] theorem params_falsum : params (⊥ : Semiformula LIinfW ξ m) = ∅ := rfl

@[simp] theorem params_rel {k : ℕ} (r : LIinfW.Rel k) (v : Fin k → Semiterm LIinfW ξ m) :
    params (Semiformula.rel r v) = relParams r := rfl

@[simp] theorem params_nrel {k : ℕ} (r : LIinfW.Rel k) (v : Fin k → Semiterm LIinfW ξ m) :
    params (Semiformula.nrel r v) = relParams r := rfl

@[simp] theorem params_and (φ ψ : Semiformula LIinfW ξ m) :
    params (φ ⋏ ψ) = params φ ∪ params ψ := rfl

@[simp] theorem params_or (φ ψ : Semiformula LIinfW ξ m) :
    params (φ ⋎ ψ) = params φ ∪ params ψ := rfl

@[simp] theorem params_all (φ : Semiformula LIinfW ξ (m + 1)) : params (∀¹ φ) = params φ := rfl

@[simp] theorem params_exs (φ : Semiformula LIinfW ξ (m + 1)) : params (∃¹ φ) = params φ := rfl

@[simp] theorem params_stageAt (s : Stage) (t : Semiterm LIinfW ξ m) :
    params (stageAt s t) = {s} := rfl

@[simp] theorem params_nstageAt (s : Stage) (t : Semiterm LIinfW ξ m) :
    params (nstageAt s t) = {s} := rfl

@[simp] theorem params_IOmegaAt (k : ℕ) (t : Semiterm LIinfW ξ m) :
    params (IOmegaAt k t) = {Stage.top k} := rfl

@[simp] theorem params_XinfAt (t : Semiterm LIinfW ξ m) : params (XinfAt t) = ∅ := rfl

@[simp] theorem params_jlevAt (ℓ : WithTop ℕ) (s t : Semiterm LIinfW ξ m) :
    params (jlevAt ℓ s t) = ∅ := rfl

@[simp] theorem params_njlevAt (ℓ : WithTop ℕ) (s t : Semiterm LIinfW ξ m) :
    params (njlevAt ℓ s t) = ∅ := rfl

/-- `k(¬φ) = k(φ)`. -/
@[simp] theorem params_neg (φ : Semiformula LIinfW ξ m) : params (∼φ) = params φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **The parameters do not see terms**: `k` is invariant under every rewriting. -/
@[simp] theorem params_rew {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew LIinfW ξ₁ m₁ ξ₂ m₂)
    (φ : Semiformula LIinfW ξ₁ m₁) : params (ω ▹ φ) = params φ := by
  induction φ using Semiformula.rec' generalizing m₂ with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [Semiformula.rew_rel, params_rel, params_rel]
  | hnrel r v => rw [Semiformula.rew_nrel, params_nrel, params_nrel]
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

@[simp] theorem params_subst2 (φ : Semiformula LIinfW ξ 2) (t u : Semiterm LIinfW ξ m) :
    params (φ/[t, u]) = params φ := params_rew _ φ

/-- **The parameters of a language-hom image are `∅` when the hom's `rel` never lands on a
`stage` symbol** — the abstract fact behind `params_formHomAt`, stated once for reuse. -/
theorem params_lMap_of_rel_ne_stage {L : Language} (f : L →ᵥ LIinfW)
    (hf : ∀ (r : L.Rel 1) (s : Stage), f.rel r ≠ Sum.inr (IInfRelW.stage s))
    {ξ' : Type*} {m' : ℕ} (φ : Semiformula L ξ' m') :
    params (Semiformula.lMap f φ) = ∅ := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
    show relParams (f.rel r) = ∅
    rcases hr : f.rel r with r' | r'
    · rfl
    · cases r' with
      | X => rfl
      | stage s => exact absurd hr (hf r s)
      | jlev _ => rfl
  | hnrel r v =>
    show relParams (f.rel r) = ∅
    rcases hr : f.rel r with r' | r'
    · rfl
    · cases r' with
      | X => rfl
      | stage s => exact absurd hr (hf r s)
      | jlev _ => rfl
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and, params_and, ihφ, ihψ, Set.union_empty]
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or, params_or, ihφ, ihψ, Set.union_empty]
  | hall φ ih => rw [Semiformula.lMap_all, params_all, ih]
  | hexs φ ih => rw [Semiformula.lMap_exs, params_exs, ih]

/-- **`k` of an embedded `LXJ`-formula is always empty**: `embedW` never lands on a `stage`
symbol (`X ↦ X`, `J ↦ Jlev ⊤`). -/
theorem params_embed (φ : Semiformula LXJ ξ m) : params (embed φ) = ∅ :=
  params_lMap_of_rel_ne_stage embedW
    (by
      intro r s
      rcases r with r | r
      · exact Sum.inl_ne_inr
      · cases r
        intro h
        cases h)
    φ

/-- **`k` of `formHomAt k g`'s image is contained in `{⟨k,g⟩}`**, for a schema at *any* arity
`n`: `P` always lands on the single stage `⟨k,g⟩` (`relParams = {⟨k,g⟩}`), `Q` always lands on
`jlev (↑k)` (`relParams = ∅`) — the `params`-level analogue of `sigmaW_formAtW_of_ne_top`, direct
structural induction on the schema `A`, no `hg`/boundedness hypothesis needed (unlike the `Σ`
fact, this one holds regardless of whether `g = StageAt.top k`). Stated at generic arity `n`, as
a genuine bound variable of the statement, exactly like `sigmaW_formAtW_of_ne_top`: this is what
lets `induction A using Semiformula.rec'` proceed (an arity fixed at the *concrete* `2` of `FormJ`
is not a variable index, and the recursor rejects it — the failure mode recorded in
an earlier attempt, resumed here by generalising over `n` first, mirroring the
existing `sigmaW`/`formAtW` split instead of stating the induction directly at `FormJ`). -/
theorem params_lMap_formHomAt {k : ℕ} (g : StageAt k) :
    ∀ {n : ℕ} (A : Semiformula LForm Empty n),
      params (Semiformula.lMap (formHomAt k g) A) ⊆ {(⟨k, g⟩ : Stage)} := by
  intro n A
  induction A using Semiformula.rec' with
  | hverum => exact Set.empty_subset _
  | hfalsum => exact Set.empty_subset _
  | hrel r v =>
    show relParams (formRelAt k g r) ⊆ _
    rcases r with r | r
    · exact Set.empty_subset _
    · cases r with
      | P => exact Set.Subset.refl _
      | Q => exact Set.empty_subset _
  | hnrel r v =>
    show relParams (formRelAt k g r) ⊆ _
    rcases r with r | r
    · exact Set.empty_subset _
    · cases r with
      | P => exact Set.Subset.refl _
      | Q => exact Set.empty_subset _
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and, params_and]; exact Set.union_subset ihφ ihψ
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or, params_or]; exact Set.union_subset ihφ ihψ
  | hall φ ih => rw [Semiformula.lMap_all, params_all]; exact ih
  | hexs φ ih => rw [Semiformula.lMap_exs, params_exs]; exact ih

/-- **`k(formAtW A k g) ⊆ {⟨k,g⟩}`**, the `FormJ`-specialised (`n = 2`) corollary. -/
theorem params_formAtW (A : FormJ) (k : ℕ) (g : StageAt k) :
    params (formAtW A k g) ⊆ {(⟨k, g⟩ : Stage)} := params_lMap_formHomAt g A

/-- **`k(unfoldW A k g t) ⊆ {⟨k,g⟩}`**: `unfoldW`'s only stage parameter is `⟨k,g⟩` itself, no
"other levels" term at all (the payoff of `formHomAt`'s `Q ↦ Jlev k` compiling uniformly). -/
theorem params_unfoldW {ξ : Type*} {m : ℕ} (A : FormJ) (k : ℕ) (g : StageAt k)
    (t : Semiterm LIinfW ξ m) : params (unfoldW A k g t) ⊆ {(⟨k, g⟩ : Stage)} := by
  have key := params_formAtW A k g
  unfold unfoldW
  rwa [params_subst2, params_rew]

end Params

/-! ### The classes `Σ(Ω_{k+1})` (`Jlev ℓ` allowed, both polarities, iff `ℓ ≤ k`) -/

section Sigma

/-- A positive atom is allowed in `Σ(Ω_{k+1})` iff its stage level is `≤ k`, or it is `Jlev ℓ`
with `ℓ ≤ k` (design §3.1: "add `Jlev ℓ` for `ℓ ≤ k` in both polarities"). -/
def RelSigmaW (k : ℕ) : {m : ℕ} → LIinfW.Rel m → Prop
  | _, Sum.inl _ => True
  | _, Sum.inr IInfRelW.X => True
  | _, Sum.inr (IInfRelW.stage s) => s.lvl ≤ k
  | _, Sum.inr (IInfRelW.jlev ℓ) => ℓ ≤ (k : WithTop ℕ)

/-- A negated atom is allowed in `Σ(Ω_{k+1})` iff its stage level is `≤ k` and it is not the full,
level-`k` predicate `I_k`, or it is `Jlev ℓ` with `ℓ ≤ k`. -/
def NrelSigmaW (k : ℕ) : {m : ℕ} → LIinfW.Rel m → Prop
  | _, Sum.inl _ => True
  | _, Sum.inr IInfRelW.X => True
  | _, Sum.inr (IInfRelW.stage s) => s.lvl ≤ k ∧ s ≠ Stage.top k
  | _, Sum.inr (IInfRelW.jlev ℓ) => ℓ ≤ (k : WithTop ℕ)

/-- **`Σ(Ω_{k+1})`** (Buchholz's `Σ(κ)` at `κ = Ω_{k+1}`, design §3.1). -/
def SigmaW (k : ℕ) {ξ : Type*} : {m : ℕ} → Semiformula LIinfW ξ m → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel r _ => RelSigmaW k r
  | _, .nrel r _ => NrelSigmaW k r
  | _, .and φ ψ => SigmaW k φ ∧ SigmaW k ψ
  | _, .or φ ψ => SigmaW k φ ∧ SigmaW k ψ
  | _, .all φ => SigmaW k φ
  | _, .exs φ => SigmaW k φ

variable {ξ : Type*} {m : ℕ} (k : ℕ)

@[simp] theorem sigmaW_verum : SigmaW k (⊤ : Semiformula LIinfW ξ m) := trivial

@[simp] theorem sigmaW_falsum : SigmaW k (⊥ : Semiformula LIinfW ξ m) := trivial

@[simp] theorem sigmaW_rel {j : ℕ} (r : LIinfW.Rel j) (v : Fin j → Semiterm LIinfW ξ m) :
    SigmaW k (Semiformula.rel r v) ↔ RelSigmaW k r := Iff.rfl

@[simp] theorem sigmaW_nrel {j : ℕ} (r : LIinfW.Rel j) (v : Fin j → Semiterm LIinfW ξ m) :
    SigmaW k (Semiformula.nrel r v) ↔ NrelSigmaW k r := Iff.rfl

@[simp] theorem sigmaW_and (φ ψ : Semiformula LIinfW ξ m) :
    SigmaW k (φ ⋏ ψ) ↔ SigmaW k φ ∧ SigmaW k ψ := Iff.rfl

@[simp] theorem sigmaW_or (φ ψ : Semiformula LIinfW ξ m) :
    SigmaW k (φ ⋎ ψ) ↔ SigmaW k φ ∧ SigmaW k ψ := Iff.rfl

@[simp] theorem sigmaW_all (φ : Semiformula LIinfW ξ (m + 1)) : SigmaW k (∀¹ φ) ↔ SigmaW k φ :=
  Iff.rfl

@[simp] theorem sigmaW_exs (φ : Semiformula LIinfW ξ (m + 1)) : SigmaW k (∃¹ φ) ↔ SigmaW k φ :=
  Iff.rfl

theorem sigmaW_stageAt_iff (s : Stage) (t : Semiterm LIinfW ξ m) :
    SigmaW k (stageAt s t) ↔ s.lvl ≤ k := Iff.rfl

theorem sigmaW_nstageAt_iff (s : Stage) (t : Semiterm LIinfW ξ m) :
    SigmaW k (nstageAt s t) ↔ s.lvl ≤ k ∧ s ≠ Stage.top k := Iff.rfl

theorem sigmaW_jlevAt_iff (ℓ : WithTop ℕ) (s t : Semiterm LIinfW ξ m) :
    SigmaW k (jlevAt ℓ s t) ↔ ℓ ≤ (k : WithTop ℕ) := Iff.rfl

theorem sigmaW_njlevAt_iff (ℓ : WithTop ℕ) (s t : Semiterm LIinfW ξ m) :
    SigmaW k (njlevAt ℓ s t) ↔ ℓ ≤ (k : WithTop ℕ) := Iff.rfl

/-- **`Jlev ⊤` is never in `Σ(Ω_{k+1})`, positively** (design: "`Jlev ⊤` never" is a consequence
of `ℓ ≤ ↑k`, not a separate clause: `⊤ ≤ ↑k` is `False` in `WithTop ℕ`). -/
theorem not_relSigmaW_jlev_top (k : ℕ) :
    ¬ RelSigmaW k (Sum.inr (IInfRelW.jlev (⊤ : WithTop ℕ))) := by
  show ¬ (⊤ : WithTop ℕ) ≤ (k : WithTop ℕ)
  simp

/-- **`Jlev ⊤` is never in `Σ(Ω_{k+1})`, either polarity.** -/
theorem not_sigmaW_jlevAt_top (t s : Semiterm LIinfW ξ m) : ¬ SigmaW k (jlevAt ⊤ t s) :=
  not_relSigmaW_jlev_top k

theorem not_sigmaW_njlevAt_top (t s : Semiterm LIinfW ξ m) : ¬ SigmaW k (njlevAt ⊤ t s) :=
  not_relSigmaW_jlev_top k

/-- `Σ(Ω_{k+1})` does not see terms. -/
@[simp] theorem sigmaW_rew {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew LIinfW ξ₁ m₁ ξ₂ m₂)
    (φ : Semiformula LIinfW ξ₁ m₁) : SigmaW k (ω ▹ φ) ↔ SigmaW k φ := by
  induction φ using Semiformula.rec' generalizing m₂ with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [Semiformula.rew_rel]; exact Iff.rfl
  | hnrel r v => rw [Semiformula.rew_nrel]; exact Iff.rfl
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

@[simp] theorem sigmaW_subst2 (φ : Semiformula LIinfW ξ 2) (t u : Semiterm LIinfW ξ m) :
    SigmaW k (φ/[t, u]) ↔ SigmaW k φ := sigmaW_rew k _ φ

/-- **Every relation symbol `formHomAt k g` can produce, unfolded at level `k`, satisfies
`RelSigmaW k`, and — provided the own place `g ≠ top` — `NrelSigmaW k` too.** Structural
induction directly on the schema `A`, not on `params`: `Q` always lands on `jlev (↑k)`
(`RelSigmaW`/`NrelSigmaW` both read `(k:WithTop ℕ) ≤ (k:WithTop ℕ)`, true regardless of
polarity — `Q` is unrestricted, matching `IDw.Theory`'s `PositiveP` leaving `Q` unconstrained),
and `P` always lands on `stage ⟨k,g⟩` (`RelSigmaW` always holds; `NrelSigmaW` needs `g ≠ top`,
supplied by `hg`). **No `LevelBounded`/`PositiveP A` hypothesis is needed** — the design's
promised simplification over `IDn.sigmaW_embed_iff`/`sigmaW_unfold_of_ne_top`, a direct
consequence of `Q` always compiling to the single atom `Jlev k` rather than some *other* level's
stage predicate. -/
theorem sigmaW_formAtW_of_ne_top {k : ℕ} {g : StageAt k} (hg : g ≠ StageAt.top k) :
    ∀ {n : ℕ} (A : Semiformula LForm Empty n), SigmaW k (Semiformula.lMap (formHomAt k g) A) := by
  intro n A
  induction A using Semiformula.rec' with
  | hverum => trivial
  | hfalsum => trivial
  | hrel r v =>
    show RelSigmaW k (formRelAt k g r)
    rcases r with r | r
    · trivial
    · cases r with
      | P => exact le_refl _
      | Q => exact le_refl (k : WithTop ℕ)
  | hnrel r v =>
    show NrelSigmaW k (formRelAt k g r)
    rcases r with r | r
    · trivial
    · cases r with
      | P => exact ⟨le_refl _, fun e => hg (Stage.mk_eq_top_iff.mp e)⟩
      | Q => exact le_refl (k : WithTop ℕ)
  | hand φ ψ ihφ ihψ => rw [LogicalConnective.HomClass.map_and]; exact ⟨ihφ, ihψ⟩
  | hor φ ψ ihφ ihψ => rw [LogicalConnective.HomClass.map_or]; exact ⟨ihφ, ihψ⟩
  | hall φ ih => rw [Semiformula.lMap_all]; exact ih
  | hexs φ ih => rw [Semiformula.lMap_exs]; exact ih

/-- **`L`-stage consumer probe (design §8.3: "`sigmaW_unfoldW`") — below the top of level `k`,
the unfolding is `Σ(Ω_{k+1})`.** The companion fact for `∼(unfoldW A k g t)` (needed together with
this one for the (jlev)/(njlev) calculus rules) is deferred to stage `C1`
(`IDw/{Calculus,CalculusAux}`), where the exact shape `∼φ` takes for `φ = unfoldW A k g t` is
dictated by the calculus's own literal convention; the underlying fact
(`sigmaW_formAtW_of_ne_top`) already covers it via `sigmaW_and_neg_formAtW_of_ne_top`-style reuse
once that convention is fixed. -/
theorem sigmaW_unfoldW_of_ne_top (A : FormJ) {k : ℕ} {g : StageAt k} (hg : g ≠ StageAt.top k)
    (t : Semiterm LIinfW ξ m) : SigmaW k (unfoldW A k g t) := by
  have key := sigmaW_formAtW_of_ne_top hg A
  unfold unfoldW
  rwa [sigmaW_subst2, sigmaW_rew]

end Sigma

/-! ### Bounding: `φ ↦ φ^β` at level `k` (identity on `Jlev`, design §3.1) -/

section Cap

/-- `I_k^{≺Ω_{k+1}} ↦ I_k^{≺b}`; every other symbol, including `Jlev` (design: "`capAt k` is the
identity on `Jlev`"), is fixed. -/
def capRelAt (k : ℕ) (b : StageAt k) : {m : ℕ} → LIinfW.Rel m → LIinfW.Rel m
  | _, Sum.inl r => Sum.inl r
  | _, Sum.inr IInfRelW.X => Sum.inr IInfRelW.X
  | _, Sum.inr (IInfRelW.stage s) =>
      Sum.inr (IInfRelW.stage (if _ : s = Stage.top k then (⟨k, b⟩ : Stage) else s))
  | _, Sum.inr (IInfRelW.jlev ℓ) => Sum.inr (IInfRelW.jlev ℓ)

theorem capRelAt_stage (k : ℕ) (b : StageAt k) (s : Stage) :
    capRelAt k b (Sum.inr (IInfRelW.stage s)) =
      Sum.inr (IInfRelW.stage (if _ : s = Stage.top k then (⟨k, b⟩ : Stage) else s)) :=
  rfl

variable {ξ : Type*} {m : ℕ}

/-- **`φ^β` at level `k`**: every literal `I_k^{≺Ω_{k+1}} t`, `¬I_k^{≺Ω_{k+1}} t` replaced by
`I_k^{≺b} t`, `¬I_k^{≺b} t`; every other stage literal, and every `Jlev` literal, untouched. -/
def capAt (k : ℕ) (b : StageAt k) : {m : ℕ} → Semiformula LIinfW ξ m → Semiformula LIinfW ξ m
  | _, .verum => .verum
  | _, .falsum => .falsum
  | _, .rel r v => .rel (capRelAt k b r) v
  | _, .nrel r v => .nrel (capRelAt k b r) v
  | _, .and φ ψ => .and (capAt k b φ) (capAt k b ψ)
  | _, .or φ ψ => .or (capAt k b φ) (capAt k b ψ)
  | _, .all φ => .all (capAt k b φ)
  | _, .exs φ => .exs (capAt k b φ)

variable (k : ℕ) (b : StageAt k)

@[simp] theorem capAt_verum : capAt k b (⊤ : Semiformula LIinfW ξ m) = ⊤ := rfl

@[simp] theorem capAt_falsum : capAt k b (⊥ : Semiformula LIinfW ξ m) = ⊥ := rfl

@[simp] theorem capAt_rel {j : ℕ} (r : LIinfW.Rel j) (v : Fin j → Semiterm LIinfW ξ m) :
    capAt k b (Semiformula.rel r v) = Semiformula.rel (capRelAt k b r) v := rfl

@[simp] theorem capAt_nrel {j : ℕ} (r : LIinfW.Rel j) (v : Fin j → Semiterm LIinfW ξ m) :
    capAt k b (Semiformula.nrel r v) = Semiformula.nrel (capRelAt k b r) v := rfl

@[simp] theorem capAt_and (φ ψ : Semiformula LIinfW ξ m) :
    capAt k b (φ ⋏ ψ) = capAt k b φ ⋏ capAt k b ψ := rfl

@[simp] theorem capAt_or (φ ψ : Semiformula LIinfW ξ m) :
    capAt k b (φ ⋎ ψ) = capAt k b φ ⋎ capAt k b ψ := rfl

@[simp] theorem capAt_all (φ : Semiformula LIinfW ξ (m + 1)) :
    capAt k b (∀¹ φ) = ∀¹ capAt k b φ := rfl

@[simp] theorem capAt_exs (φ : Semiformula LIinfW ξ (m + 1)) :
    capAt k b (∃¹ φ) = ∃¹ capAt k b φ := rfl

/-- `(I_k t)^β = I_k^{≺β} t`. -/
@[simp] theorem capAt_IOmegaAt (t : Semiterm LIinfW ξ m) :
    capAt k b (IOmegaAt k t) = stageAt ⟨k, b⟩ t := by
  show Semiformula.rel (capRelAt k b (Sum.inr (IInfRelW.stage (Stage.top k)))) ![t] = _
  rw [capRelAt_stage, dif_pos rfl]
  rfl

/-- `(Jlev ℓ (s,t))^β = Jlev ℓ (s,t)`: bounding never touches `Jlev`. -/
@[simp] theorem capAt_jlevAt (ℓ : WithTop ℕ) (s t : Semiterm LIinfW ξ m) :
    capAt k b (jlevAt ℓ s t) = jlevAt ℓ s t := rfl

@[simp] theorem capAt_njlevAt (ℓ : WithTop ℕ) (s t : Semiterm LIinfW ξ m) :
    capAt k b (njlevAt ℓ s t) = njlevAt ℓ s t := rfl

/-- A stage other than the top of level `k` is untouched. -/
theorem capAt_stageAt_of_ne_top {s : Stage} (hs : s ≠ Stage.top k) (t : Semiterm LIinfW ξ m) :
    capAt k b (stageAt s t) = stageAt s t := by
  show Semiformula.rel (capRelAt k b (Sum.inr (IInfRelW.stage s))) ![t] = _
  rw [capRelAt_stage, dif_neg hs]
  rfl

/-- `(¬φ)^β = ¬(φ^β)`. -/
@[simp] theorem capAt_neg (φ : Semiformula LIinfW ξ m) : capAt k b (∼φ) = ∼(capAt k b φ) := by
  induction φ using Semiformula.rec' <;> simp [*]

end Cap

end IDw

end OrdinalAnalysis
