/-
  The infinitary language of `ID₁` with stage predicates.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §5 (before Definition 5.1, Definition 5.4, and
  before Theorem 5.9), and §6 (the definition of `Σ(Ω)` before Theorem 6.7).

  **The language.**  Freund's `L^Ω_ID` extends arithmetic by a unary predicate `I^{≺α}_φ`
  for every operator form `φ` and every notation `α ⪯ Ω`; the predicate `I_φ` of `ID₁` is
  identified with `I^{≺Ω}_φ`.  The intended reading of `I^{≺α}_φ t` is "`t` enters the
  inductively defined set at some stage below `α`".  Here there is one operator form
  `A` (the theory `ID1 A` has one inductive predicate), so the index
  `φ` is dropped, and the free predicate `X` of `LXI` is kept:

      LIinf  :=  ℒₒᵣ  +  { X }  ∪  { I^{≺α} | α ⪯ Ω }.

  The stage predicates are relation symbols indexed by the notations, as the membership
  symbols of ramified analysis are indexed by levels.  The index ranges over the subtype
  `Stage = {α : ThetaNote // α ≤ Ω}`, which is exactly Freund's restriction `α ⪯ Ω`: it
  is what makes every infinite conjunction `¬I^{≺α} t ≃ ⋀_{γ≺α} ¬A(t, I^{≺γ})` range over
  `γ ≺ α ⪯ Ω` (Definition 5.1).  A stage symbol is a relation symbol, not a term, so no
  substitution of terms can change it.

  **Operator forms and the unfolding.**  An operator form is `A : Semisentence LXI 1`, the
  symbol `I` of `LXI` being the place-holder (as for `ID1 A`).  Mapping `I` to `I^{≺α}`
  and fixing arithmetic and `X` is a homomorphism of languages `stageHom α : LXI →ᵥ LIinf`,
  and

    * `formAt A α := A` with `I ↦ I^{≺α}`,
    * `unfold A α t := A(t, I^{≺α})`, the instance of `formAt A α` at the term `t`,
    * `embed φ := φ` with `I ↦ I^{≺Ω}` — the embedding of `LXI` into `LIinf`.

  Definition 5.1 reads `I^{≺α} t ≃ ⋁_{γ≺α} A(t, I^{≺γ})`: `t` is in `I^{≺α}` iff for some
  `γ ≺ α` it satisfies the operator applied to the stage `I^{≺γ}`.

  **Parameters.**  `params φ` is Freund's `k(φ)` (before Exercise 5.5): the set of `α`
  such that `φ` contains a literal `I^{≺α} t` or `¬I^{≺α} t`.  It is what an operator
  `H` controls in the infinitary calculus (`k(Γ) ⊆ H(∅)`, Definition 5.6).

  **`Σ(Ω)`.**  A formula is `Σ(Ω)` if it has no subformula `¬I^{≺Ω} t`
  (Freund §6, before Theorem 6.7), i.e. `I = I^{≺Ω}` occurs only positively.  In
  negation normal form this is a condition on negated atoms only.  An operator form is
  positive exactly when its embedding is `Σ(Ω)` (`sigmaOmega_embed_iff`).

  **Bounding.**  `cap β φ` is Freund's `φ^β` (before Theorem 5.9): every literal
  `I^{≺Ω} t`, `¬I^{≺Ω} t` is replaced by `I^{≺β} t`, `¬I^{≺β} t`; stages below `Ω` are
  untouched.  In particular `(I t)^β = I^{≺β} t`, `A(t, I^{≺Ω})^β = A(t, I^{≺β})`, and
  `A(t, I^{≺γ})^β = A(t, I^{≺γ})` for `γ ≺ Ω` — the identities the proof of boundedness
  uses.

  Contents.

    `Stage`, `Stage.top`                   the stage indices `α ⪯ Ω`, and `Ω`
    `IInfRel`, `IInfLang`, `LIinf`         the language
    `XinfAt`, `stageAt`, `nstageAt`, `IOmegaAt`   the atoms `X t`, `I^{≺α} t`, `¬I^{≺α} t`, `I t`
    `stageHom`, `embed`, `formAt`, `unfold`       `I ↦ I^{≺α}`, `LXI ↪ LIinf`, `A(·, I^{≺α})`
    `params`                               `k(φ)`
    `SigmaOmega`                           the class `Σ(Ω)`
    `cap`                                  `φ ↦ φ^β`
-/
import OrdinalAnalysis.ID1.Theory
import OrdinalAnalysis.Ordinal.Theta.Arith

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

open LO LO.FirstOrder

/-! ### Stages -/

/-- The stage indices: the notations `α ⪯ Ω` (Freund §5, before Definition 5.1). -/
abbrev Stage : Type := {a : ThetaNote // a ≤ ThetaNote.Omega}

namespace Stage

/-- The top stage `Ω`; `I^{≺Ω}` is the predicate `I` of `ID₁`. -/
def top : Stage := ⟨ThetaNote.Omega, le_refl _⟩

@[simp] theorem top_val : top.1 = ThetaNote.Omega := rfl

/-- A countable stage `α ≺ Ω`. -/
def ofLt (a : ThetaNote) (h : a < ThetaNote.Omega) : Stage := ⟨a, le_of_lt h⟩

@[simp] theorem ofLt_val (a : ThetaNote) (h : a < ThetaNote.Omega) : (ofLt a h).1 = a := rfl

theorem eq_top_iff {a : Stage} : a = top ↔ a.1 = ThetaNote.Omega := Subtype.ext_iff

/-- A stage other than `Ω` is countable. -/
theorem lt_Omega_of_ne_top {a : Stage} (h : a ≠ top) : a.1 < ThetaNote.Omega :=
  lt_of_le_of_ne a.2 (fun e => h (Subtype.ext e))

theorem ne_top_of_lt_Omega {a : Stage} (h : a.1 < ThetaNote.Omega) : a ≠ top :=
  fun e => ne_of_lt h (eq_top_iff.mp e)

theorem ne_top_iff {a : Stage} : a ≠ top ↔ a.1 < ThetaNote.Omega :=
  ⟨lt_Omega_of_ne_top, ne_top_of_lt_Omega⟩

end Stage

/-! ### The language -/

/-- The fresh relation symbols: the free predicate `X`, and the stage predicate `I^{≺α}`
for every stage `α ⪯ Ω`. -/
inductive IInfRel : ℕ → Type
  | X : IInfRel 1
  | stage : Stage → IInfRel 1

instance {k : ℕ} : DecidableEq (IInfRel k) := fun a b => by
  cases a with
  | X => cases b with
    | X => exact isTrue rfl
    | stage _ => exact isFalse (by intro h; cases h)
  | stage a => cases b with
    | X => exact isFalse (by intro h; cases h)
    | stage b =>
      exact if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (by injection e))

/-- The fresh part of the language: no function symbols. -/
abbrev IInfLang : Language where
  Func := fun _ => PEmpty
  Rel := IInfRel

/-- **The infinitary language** `L^Ω_ID` for one operator form, with the free predicate
`X`: arithmetic, `X`, and the stage predicates `I^{≺α}`, `α ⪯ Ω`. -/
abbrev LIinf : Language := Language.add ℒₒᵣ IInfLang

instance : Language.ORing LIinf where
  eq := Sum.inl Language.Eq.eq
  lt := Sum.inl Language.LT.lt
  zero := Sum.inl Language.Zero.zero
  one := Sum.inl Language.One.one
  add := Sum.inl Language.Add.add
  mul := Sum.inl Language.Mul.mul

/-- The embedding of arithmetic into `LIinf`. -/
abbrev toLIinf : ℒₒᵣ →ᵥ LIinf := Language.Hom.add₁ ℒₒᵣ IInfLang

/-- The stage of a relation symbol: `some α` for `I^{≺α}`, `none` for `X` and the symbols of
arithmetic. -/
def relStage : {k : ℕ} → LIinf.Rel k → Option Stage
  | _, Sum.inl _ => none
  | _, Sum.inr IInfRel.X => none
  | _, Sum.inr (IInfRel.stage a) => some a

/-! ### The atoms -/

section Atoms

variable {ξ : Type*} {n : ℕ}

/-- `X(t)`. -/
def XinfAt (t : Semiterm LIinf ξ n) : Semiformula LIinf ξ n :=
  Semiformula.rel (Sum.inr IInfRel.X) ![t]

/-- `I^{≺α} t`: "`t` enters at a stage below `α`". -/
def stageAt (a : Stage) (t : Semiterm LIinf ξ n) : Semiformula LIinf ξ n :=
  Semiformula.rel (Sum.inr (IInfRel.stage a)) ![t]

/-- `¬I^{≺α} t`. -/
def nstageAt (a : Stage) (t : Semiterm LIinf ξ n) : Semiformula LIinf ξ n :=
  Semiformula.nrel (Sum.inr (IInfRel.stage a)) ![t]

/-- `I t = I^{≺Ω} t`. -/
def IOmegaAt (t : Semiterm LIinf ξ n) : Semiformula LIinf ξ n := stageAt Stage.top t

@[simp] theorem neg_stageAt (a : Stage) (t : Semiterm LIinf ξ n) :
    ∼(stageAt a t) = nstageAt a t := rfl

@[simp] theorem neg_nstageAt (a : Stage) (t : Semiterm LIinf ξ n) :
    ∼(nstageAt a t) = stageAt a t := rfl

theorem IOmegaAt_eq (t : Semiterm LIinf ξ n) : IOmegaAt t = stageAt Stage.top t := rfl

/-- A unary atom is `r ![v 0]`. -/
theorem rel_eq_vec {k : ℕ} (r : LIinf.Rel 1) (v : Fin 1 → Semiterm LIinf ξ k) :
    Semiformula.rel r v = Semiformula.rel r ![v 0] := by
  congr 1; funext i; obtain rfl := Subsingleton.elim i 0; rfl

theorem nrel_eq_vec {k : ℕ} (r : LIinf.Rel 1) (v : Fin 1 → Semiterm LIinf ξ k) :
    Semiformula.nrel r v = Semiformula.nrel r ![v 0] := by
  congr 1; funext i; obtain rfl := Subsingleton.elim i 0; rfl

end Atoms

/-! ### From `LXI` to `LIinf`: `I ↦ I^{≺α}` -/

/-- The function symbols of `LXI` are those of arithmetic. -/
def stageFunc : {k : ℕ} → LXI.Func k → LIinf.Func k
  | _, Sum.inl f => Sum.inl f
  | _, Sum.inr f => PEmpty.elim f

/-- Arithmetic and `X` are fixed, `I` goes to `I^{≺α}`. -/
def stageRel (a : Stage) : {k : ℕ} → LXI.Rel k → LIinf.Rel k
  | _, Sum.inl r => Sum.inl r
  | _, Sum.inr IXRel.X => Sum.inr IInfRel.X
  | _, Sum.inr IXRel.I => Sum.inr (IInfRel.stage a)

/-- **`I ↦ I^{≺α}`**, as a homomorphism of languages. -/
def stageHom (a : Stage) : LXI →ᵥ LIinf := ⟨stageFunc, stageRel a⟩

/-- The terms do not see the stage. -/
theorem lMap_stageHom_term {ξ : Type*} {n : ℕ} (a b : Stage) (t : Semiterm LXI ξ n) :
    Semiterm.lMap (stageHom a) t = Semiterm.lMap (stageHom b) t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih =>
    simp only [Semiterm.lMap_func]
    congr 1
    funext i
    exact ih i

/-- **The embedding of `LXI` into `LIinf`**: `I ↦ I^{≺Ω}` (Freund identifies `I_φ` with
`I^{≺Ω}_φ`). -/
def embed {ξ : Type*} {n : ℕ} (φ : Semiformula LXI ξ n) : Semiformula LIinf ξ n :=
  Semiformula.lMap (stageHom Stage.top) φ

/-- `A(·, I^{≺α})`: the operator form with `I` read as the stage `I^{≺α}`. -/
def formAt (A : Semisentence LXI 1) (a : Stage) : Semisentence LIinf 1 :=
  Semiformula.lMap (stageHom a) A

/-- **The stage unfolding** `A(t, I^{≺α})` (Freund, Definition 5.1:
`I^{≺β} t ≃ ⋁_{α≺β} A(t, I^{≺α})`). -/
def unfold {ξ : Type*} {n : ℕ} (A : Semisentence LXI 1) (a : Stage) (t : Semiterm LIinf ξ n) :
    Semiformula LIinf ξ n :=
  (Rewriting.emb (formAt A a) : Semiformula LIinf ξ 1)/[t]

section Embed

variable {ξ : Type*} {n : ℕ}

theorem embed_neg (φ : Semiformula LXI ξ n) : embed (∼φ) = ∼(embed φ) := by
  simp [embed]

/-- `I t ↦ I^{≺Ω} t`. -/
theorem embed_Iat (t : Semiterm LXI ξ n) :
    embed (Iat t) = IOmegaAt (Semiterm.lMap (stageHom Stage.top) t) :=
  rel_eq_vec (Sum.inr (IInfRel.stage Stage.top)) (Semiterm.lMap (stageHom Stage.top) ∘ ![t])

/-- `X t ↦ X t`. -/
theorem embed_Xat (t : Semiterm LXI ξ n) :
    embed (Xat t) = XinfAt (Semiterm.lMap (stageHom Stage.top) t) :=
  rel_eq_vec (Sum.inr IInfRel.X) (Semiterm.lMap (stageHom Stage.top) ∘ ![t])

/-- The embedding of the whole form is `formAt A Ω`. -/
theorem formAt_top (A : Semisentence LXI 1) : formAt A Stage.top = embed A := rfl

end Embed

/-! ### The parameters `k(φ)` -/

/-- The parameters of a relation symbol: `{α}` for `I^{≺α}`, empty otherwise. -/
def relParams : {k : ℕ} → LIinf.Rel k → Set ThetaNote
  | _, Sum.inl _ => ∅
  | _, Sum.inr IInfRel.X => ∅
  | _, Sum.inr (IInfRel.stage a) => {a.1}

/-- **`k(φ)`**, the ordinal parameters of a formula (Freund, before Exercise 5.5): the
`α` such that `φ` contains a literal `I^{≺α} t` or `¬I^{≺α} t`. -/
def params {ξ : Type*} : {n : ℕ} → Semiformula LIinf ξ n → Set ThetaNote
  | _, .verum => ∅
  | _, .falsum => ∅
  | _, .rel r _ => relParams r
  | _, .nrel r _ => relParams r
  | _, .and φ ψ => params φ ∪ params ψ
  | _, .or φ ψ => params φ ∪ params ψ
  | _, .all φ => params φ
  | _, .exs φ => params φ

/-- `k(Γ)`, the parameters of a list of formulas. -/
def paramsList {ξ : Type*} {n : ℕ} (Γ : List (Semiformula LIinf ξ n)) : Set ThetaNote :=
  {a | ∃ φ ∈ Γ, a ∈ params φ}

section Params

variable {ξ : Type*} {n : ℕ}

@[simp] theorem params_verum : params (⊤ : Semiformula LIinf ξ n) = ∅ := rfl

@[simp] theorem params_falsum : params (⊥ : Semiformula LIinf ξ n) = ∅ := rfl

@[simp] theorem params_rel {k : ℕ} (r : LIinf.Rel k) (v : Fin k → Semiterm LIinf ξ n) :
    params (Semiformula.rel r v) = relParams r := rfl

@[simp] theorem params_nrel {k : ℕ} (r : LIinf.Rel k) (v : Fin k → Semiterm LIinf ξ n) :
    params (Semiformula.nrel r v) = relParams r := rfl

@[simp] theorem params_and (φ ψ : Semiformula LIinf ξ n) :
    params (φ ⋏ ψ) = params φ ∪ params ψ := rfl

@[simp] theorem params_or (φ ψ : Semiformula LIinf ξ n) :
    params (φ ⋎ ψ) = params φ ∪ params ψ := rfl

@[simp] theorem params_all (φ : Semiformula LIinf ξ (n + 1)) : params (∀¹ φ) = params φ := rfl

@[simp] theorem params_exs (φ : Semiformula LIinf ξ (n + 1)) : params (∃¹ φ) = params φ := rfl

@[simp] theorem params_stageAt (a : Stage) (t : Semiterm LIinf ξ n) :
    params (stageAt a t) = {a.1} := rfl

@[simp] theorem params_nstageAt (a : Stage) (t : Semiterm LIinf ξ n) :
    params (nstageAt a t) = {a.1} := rfl

@[simp] theorem params_IOmegaAt (t : Semiterm LIinf ξ n) :
    params (IOmegaAt t) = {ThetaNote.Omega} := rfl

@[simp] theorem params_XinfAt (t : Semiterm LIinf ξ n) : params (XinfAt t) = ∅ := rfl

/-- `k(¬φ) = k(φ)`. -/
@[simp] theorem params_neg (φ : Semiformula LIinf ξ n) : params (∼φ) = params φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **The parameters do not see terms**: `k` is invariant under every rewriting, in
particular under instantiation of a quantifier. -/
@[simp] theorem params_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LIinf ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformula LIinf ξ₁ n₁) : params (ω ▹ φ) = params φ := by
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [Semiformula.rew_rel, params_rel, params_rel]
  | hnrel r v => rw [Semiformula.rew_nrel, params_nrel, params_nrel]
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

@[simp] theorem params_subst (φ : Semiformula LIinf ξ 1) (t : Semiterm LIinf ξ n) :
    params (φ/[t]) = params φ := params_rew _ φ

/-- The stage symbols of `A` with `I ↦ I^{≺α}` are `I^{≺α}`. -/
theorem relParams_stageRel (a : Stage) :
    ∀ {k : ℕ} (r : LXI.Rel k), relParams (stageRel a r) ⊆ {a.1}
  | _, Sum.inl _ => Set.empty_subset _
  | _, Sum.inr IXRel.X => Set.empty_subset _
  | _, Sum.inr IXRel.I => subset_refl _

/-- Every parameter of `A` with `I ↦ I^{≺α}` is `α`. -/
theorem params_lMap_stageHom (a : Stage) {ξ' : Type*} {m : ℕ} (φ : Semiformula LXI ξ' m) :
    params (Semiformula.lMap (stageHom a) φ) ⊆ {a.1} := by
  induction φ using Semiformula.rec' with
  | hverum => exact Set.empty_subset _
  | hfalsum => exact Set.empty_subset _
  | hrel r v => exact relParams_stageRel a r
  | hnrel r v => exact relParams_stageRel a r
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and, params_and]; exact Set.union_subset ihφ ihψ
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or, params_or]; exact Set.union_subset ihφ ihψ
  | hall φ ih => rw [Semiformula.lMap_all, params_all]; exact ih
  | hexs φ ih => rw [Semiformula.lMap_exs, params_exs]; exact ih

/-- `k(A(t, I^{≺α})) ⊆ {α}`. -/
theorem params_unfold (A : Semisentence LXI 1) (a : Stage) (t : Semiterm LIinf ξ n) :
    params (unfold A a t) ⊆ {a.1} := by
  rw [unfold, params_subst]
  show params (Rew.emb ▹ formAt A a) ⊆ _
  rw [params_rew]
  exact params_lMap_stageHom a A

/-- `k` of an embedded formula is contained in `{Ω}`. -/
theorem params_embed (φ : Semiformula LXI ξ n) : params (embed φ) ⊆ {ThetaNote.Omega} :=
  params_lMap_stageHom Stage.top φ

end Params

/-! ### The class `Σ(Ω)` -/

/-- A negated atom `¬r v` is allowed in a `Σ(Ω)` formula unless `r = I^{≺Ω}`. -/
def NrelSigma : {k : ℕ} → LIinf.Rel k → Prop
  | _, Sum.inl _ => True
  | _, Sum.inr IInfRel.X => True
  | _, Sum.inr (IInfRel.stage a) => a ≠ Stage.top

/-- **`Σ(Ω)`** (Freund §6, before Theorem 6.7): no subformula `¬I^{≺Ω} t`, i.e. `I` occurs
only positively; the stages below `Ω` are unrestricted. -/
def SigmaOmega {ξ : Type*} : {n : ℕ} → Semiformula LIinf ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel _ _ => True
  | _, .nrel r _ => NrelSigma r
  | _, .and φ ψ => SigmaOmega φ ∧ SigmaOmega ψ
  | _, .or φ ψ => SigmaOmega φ ∧ SigmaOmega ψ
  | _, .all φ => SigmaOmega φ
  | _, .exs φ => SigmaOmega φ

section Sigma

variable {ξ : Type*} {n : ℕ}

@[simp] theorem sigmaOmega_verum : SigmaOmega (⊤ : Semiformula LIinf ξ n) := trivial

@[simp] theorem sigmaOmega_falsum : SigmaOmega (⊥ : Semiformula LIinf ξ n) := trivial

@[simp] theorem sigmaOmega_rel {k : ℕ} (r : LIinf.Rel k) (v : Fin k → Semiterm LIinf ξ n) :
    SigmaOmega (Semiformula.rel r v) := trivial

@[simp] theorem sigmaOmega_nrel {k : ℕ} (r : LIinf.Rel k) (v : Fin k → Semiterm LIinf ξ n) :
    SigmaOmega (Semiformula.nrel r v) ↔ NrelSigma r := Iff.rfl

@[simp] theorem sigmaOmega_and (φ ψ : Semiformula LIinf ξ n) :
    SigmaOmega (φ ⋏ ψ) ↔ SigmaOmega φ ∧ SigmaOmega ψ := Iff.rfl

@[simp] theorem sigmaOmega_or (φ ψ : Semiformula LIinf ξ n) :
    SigmaOmega (φ ⋎ ψ) ↔ SigmaOmega φ ∧ SigmaOmega ψ := Iff.rfl

@[simp] theorem sigmaOmega_all (φ : Semiformula LIinf ξ (n + 1)) :
    SigmaOmega (∀¹ φ) ↔ SigmaOmega φ := Iff.rfl

@[simp] theorem sigmaOmega_exs (φ : Semiformula LIinf ξ (n + 1)) :
    SigmaOmega (∃¹ φ) ↔ SigmaOmega φ := Iff.rfl

theorem sigmaOmega_stageAt (a : Stage) (t : Semiterm LIinf ξ n) : SigmaOmega (stageAt a t) :=
  trivial

theorem sigmaOmega_nstageAt_iff (a : Stage) (t : Semiterm LIinf ξ n) :
    SigmaOmega (nstageAt a t) ↔ a ≠ Stage.top := Iff.rfl

theorem not_sigmaOmega_neg_IOmegaAt (t : Semiterm LIinf ξ n) : ¬ SigmaOmega (∼(IOmegaAt t)) :=
  fun h => h rfl

/-- `Σ(Ω)` does not see terms: it is invariant under every rewriting. -/
@[simp] theorem sigmaOmega_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LIinf ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformula LIinf ξ₁ n₁) : SigmaOmega (ω ▹ φ) ↔ SigmaOmega φ := by
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [Semiformula.rew_rel]; exact ⟨fun _ => trivial, fun _ => trivial⟩
  | hnrel r v => rw [Semiformula.rew_nrel]; exact Iff.rfl
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

@[simp] theorem sigmaOmega_subst (φ : Semiformula LIinf ξ 1) (t : Semiterm LIinf ξ n) :
    SigmaOmega (φ/[t]) ↔ SigmaOmega φ := sigmaOmega_rew _ φ

theorem nrelSigma_of_not_mem :
    ∀ {k : ℕ} (r : LIinf.Rel k), ThetaNote.Omega ∉ relParams r → NrelSigma r
  | _, Sum.inl _, _ => trivial
  | _, Sum.inr IInfRel.X, _ => trivial
  | _, Sum.inr (IInfRel.stage a), h => fun e => h (by subst e; exact Set.mem_singleton _)

/-- A formula without the parameter `Ω` is `Σ(Ω)`. -/
theorem sigmaOmega_of_Omega_not_mem {m : ℕ} {φ : Semiformula LIinf ξ m}
    (h : ThetaNote.Omega ∉ params φ) : SigmaOmega φ := by
  induction φ using Semiformula.rec' with
  | hverum => trivial
  | hfalsum => trivial
  | hrel r v => trivial
  | hnrel r v => exact nrelSigma_of_not_mem r h
  | hand φ ψ ihφ ihψ => exact ⟨ihφ fun h' => h (Or.inl h'), ihψ fun h' => h (Or.inr h')⟩
  | hor φ ψ ihφ ihψ => exact ⟨ihφ fun h' => h (Or.inl h'), ihψ fun h' => h (Or.inr h')⟩
  | hall φ ih => exact ih h
  | hexs φ ih => exact ih h

/-- A formula without the parameter `Ω` is `Σ(Ω)`, and so is its negation. -/
theorem sigmaOmega_and_neg_of_Omega_not_mem {φ : Semiformula LIinf ξ n}
    (h : ThetaNote.Omega ∉ params φ) : SigmaOmega φ ∧ SigmaOmega (∼φ) :=
  ⟨sigmaOmega_of_Omega_not_mem h, sigmaOmega_of_Omega_not_mem (by rwa [params_neg])⟩

/-- **An operator form is positive iff its embedding is `Σ(Ω)`.** -/
theorem sigmaOmega_embed_iff {ξ' : Type*} :
    ∀ {m : ℕ} (φ : Semiformula LXI ξ' m), SigmaOmega (embed φ) ↔ Positive φ
  | _, .verum => Iff.rfl
  | _, .falsum => Iff.rfl
  | _, .rel _ _ => ⟨fun _ => trivial, fun _ => trivial⟩
  | _, .nrel (Sum.inl _) _ => Iff.rfl
  | _, .nrel (Sum.inr IXRel.X) _ => Iff.rfl
  | _, .nrel (Sum.inr IXRel.I) _ => ⟨fun h => h rfl, fun h => h.elim⟩
  | _, .and φ ψ => and_congr (sigmaOmega_embed_iff φ) (sigmaOmega_embed_iff ψ)
  | _, .or φ ψ => and_congr (sigmaOmega_embed_iff φ) (sigmaOmega_embed_iff ψ)
  | _, .all φ => sigmaOmega_embed_iff φ
  | _, .exs φ => sigmaOmega_embed_iff φ

/-- Below `Ω` the unfolding is `Σ(Ω)`, and so is its negation: it has no `I^{≺Ω}` at all. -/
theorem sigmaOmega_unfold_of_ne_top (A : Semisentence LXI 1) {a : Stage} (ha : a ≠ Stage.top)
    (t : Semiterm LIinf ξ n) :
    SigmaOmega (unfold A a t) ∧ SigmaOmega (∼(unfold A a t)) := by
  refine sigmaOmega_and_neg_of_Omega_not_mem fun h => ?_
  have h' := params_unfold A a t h
  exact ne_of_lt (Stage.lt_Omega_of_ne_top ha) (Set.mem_singleton_iff.mp h').symm

/-- **At `Ω` the unfolding of a positive operator form is `Σ(Ω)`** (Freund, proof of
Theorem 6.7, case (Fix)). -/
theorem sigmaOmega_unfold_top {A : Semisentence LXI 1} (hA : Positive A)
    (t : Semiterm LIinf ξ n) : SigmaOmega (unfold A Stage.top t) := by
  rw [unfold, sigmaOmega_subst]
  show SigmaOmega (Rew.emb ▹ formAt A Stage.top)
  rw [sigmaOmega_rew, formAt_top]
  exact (sigmaOmega_embed_iff A).mpr hA

end Sigma

/-! ### Bounding: `φ ↦ φ^β` -/

/-- `I^{≺Ω} ↦ I^{≺β}`; every other symbol is fixed. -/
def capRel (b : Stage) : {k : ℕ} → LIinf.Rel k → LIinf.Rel k
  | _, Sum.inl r => Sum.inl r
  | _, Sum.inr IInfRel.X => Sum.inr IInfRel.X
  | _, Sum.inr (IInfRel.stage a) => Sum.inr (IInfRel.stage (if a = Stage.top then b else a))

/-- **`φ^β`** (Freund, before Theorem 5.9): every literal `I^{≺Ω} t`, `¬I^{≺Ω} t` replaced
by `I^{≺β} t`, `¬I^{≺β} t`. -/
def cap {ξ : Type*} (b : Stage) : {n : ℕ} → Semiformula LIinf ξ n → Semiformula LIinf ξ n
  | _, .verum => .verum
  | _, .falsum => .falsum
  | _, .rel r v => .rel (capRel b r) v
  | _, .nrel r v => .nrel (capRel b r) v
  | _, .and φ ψ => .and (cap b φ) (cap b ψ)
  | _, .or φ ψ => .or (cap b φ) (cap b ψ)
  | _, .all φ => .all (cap b φ)
  | _, .exs φ => .exs (cap b φ)

section Cap

variable {ξ : Type*} {n : ℕ} (b : Stage)

@[simp] theorem cap_verum : cap b (⊤ : Semiformula LIinf ξ n) = ⊤ := rfl

@[simp] theorem cap_falsum : cap b (⊥ : Semiformula LIinf ξ n) = ⊥ := rfl

@[simp] theorem cap_rel {k : ℕ} (r : LIinf.Rel k) (v : Fin k → Semiterm LIinf ξ n) :
    cap b (Semiformula.rel r v) = Semiformula.rel (capRel b r) v := rfl

@[simp] theorem cap_nrel {k : ℕ} (r : LIinf.Rel k) (v : Fin k → Semiterm LIinf ξ n) :
    cap b (Semiformula.nrel r v) = Semiformula.nrel (capRel b r) v := rfl

@[simp] theorem cap_and (φ ψ : Semiformula LIinf ξ n) : cap b (φ ⋏ ψ) = cap b φ ⋏ cap b ψ := rfl

@[simp] theorem cap_or (φ ψ : Semiformula LIinf ξ n) : cap b (φ ⋎ ψ) = cap b φ ⋎ cap b ψ := rfl

@[simp] theorem cap_all (φ : Semiformula LIinf ξ (n + 1)) : cap b (∀¹ φ) = ∀¹ cap b φ := rfl

@[simp] theorem cap_exs (φ : Semiformula LIinf ξ (n + 1)) : cap b (∃¹ φ) = ∃¹ cap b φ := rfl

/-- `(I t)^β = I^{≺β} t`. -/
@[simp] theorem cap_IOmegaAt (t : Semiterm LIinf ξ n) : cap b (IOmegaAt t) = stageAt b t := by
  show Semiformula.rel (Sum.inr (IInfRel.stage (if Stage.top = Stage.top then b else Stage.top)))
    ![t] = _
  rw [if_pos rfl]; rfl

/-- A stage below `Ω` is untouched. -/
theorem cap_stageAt_of_ne_top {a : Stage} (ha : a ≠ Stage.top) (t : Semiterm LIinf ξ n) :
    cap b (stageAt a t) = stageAt a t := by
  show Semiformula.rel (Sum.inr (IInfRel.stage (if a = Stage.top then b else a))) ![t] = _
  rw [if_neg ha]; rfl

theorem cap_nstageAt_of_ne_top {a : Stage} (ha : a ≠ Stage.top) (t : Semiterm LIinf ξ n) :
    cap b (nstageAt a t) = nstageAt a t := by
  show Semiformula.nrel (Sum.inr (IInfRel.stage (if a = Stage.top then b else a))) ![t] = _
  rw [if_neg ha]; rfl

/-- `(¬φ)^β = ¬(φ^β)`. -/
@[simp] theorem cap_neg (φ : Semiformula LIinf ξ n) : cap b (∼φ) = ∼(cap b φ) := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **Bounding commutes with every rewriting**, in particular with instantiation. -/
theorem cap_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LIinf ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformula LIinf ξ₁ n₁) : cap b (ω ▹ φ) = ω ▹ cap b φ := by
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [Semiformula.rew_rel, cap_rel, cap_rel, Semiformula.rew_rel]
  | hnrel r v => rw [Semiformula.rew_nrel, cap_nrel, cap_nrel, Semiformula.rew_nrel]
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

theorem cap_subst (φ : Semiformula LIinf ξ 1) (t : Semiterm LIinf ξ n) :
    cap b (φ/[t]) = (cap b φ)/[t] := cap_rew b _ φ

/-- `(A with I ↦ I^{≺α})^β = A with I ↦ I^{≺α'}`, where `α' = β` if `α = Ω` and `α' = α`
otherwise. -/
theorem cap_lMap_stageHom (a : Stage) {ξ' : Type*} :
    ∀ {m : ℕ} (φ : Semiformula LXI ξ' m),
      cap b (Semiformula.lMap (stageHom a) φ) =
        Semiformula.lMap (stageHom (if a = Stage.top then b else a)) φ
  | _, .verum => rfl
  | _, .falsum => rfl
  | _, .rel r v => by
    simp only [Semiformula.lMap_rel, cap_rel]
    congr 1
    · rcases r with r | r
      · rfl
      · cases r <;> rfl
    · funext i
      exact lMap_stageHom_term _ _ (v i)
  | _, .nrel r v => by
    simp only [Semiformula.lMap_nrel, cap_nrel]
    congr 1
    · rcases r with r | r
      · rfl
      · cases r <;> rfl
    · funext i
      exact lMap_stageHom_term _ _ (v i)
  | _, .and φ ψ => by
    rw [show (Semiformula.and φ ψ : Semiformula LXI ξ' _) = φ ⋏ ψ from rfl,
      LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and, cap_and,
      cap_lMap_stageHom a φ, cap_lMap_stageHom a ψ]
  | _, .or φ ψ => by
    rw [show (Semiformula.or φ ψ : Semiformula LXI ξ' _) = φ ⋎ ψ from rfl,
      LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or, cap_or,
      cap_lMap_stageHom a φ, cap_lMap_stageHom a ψ]
  | _, .all φ => by
    rw [show (Semiformula.all φ : Semiformula LXI ξ' _) = ∀¹ φ from rfl,
      Semiformula.lMap_all, Semiformula.lMap_all, cap_all, cap_lMap_stageHom a φ]
  | _, .exs φ => by
    rw [show (Semiformula.exs φ : Semiformula LXI ξ' _) = ∃¹ φ from rfl,
      Semiformula.lMap_exs, Semiformula.lMap_exs, cap_exs, cap_lMap_stageHom a φ]

/-- `(embed φ)^β` is `φ` with `I ↦ I^{≺β}`. -/
theorem cap_embed (φ : Semiformula LXI ξ n) :
    cap b (embed φ) = Semiformula.lMap (stageHom b) φ := by
  rw [embed, cap_lMap_stageHom, if_pos rfl]

/-- The unfolding commutes with bounding at the level of the stage. -/
theorem cap_unfold (A : Semisentence LXI 1) (a : Stage) (t : Semiterm LIinf ξ n) :
    cap b (unfold A a t) = unfold A (if a = Stage.top then b else a) t := by
  rw [unfold, unfold, cap_subst]
  congr 1
  show cap b (Rew.emb ▹ formAt A a) = Rew.emb ▹ formAt A _
  rw [cap_rew, formAt, formAt, cap_lMap_stageHom]

/-- **`A(t, I^{≺Ω})^β = A(t, I^{≺β})`** — the (Fix) case of boundedness. -/
theorem cap_unfold_top (A : Semisentence LXI 1) (t : Semiterm LIinf ξ n) :
    cap b (unfold A Stage.top t) = unfold A b t := by
  rw [cap_unfold, if_pos rfl]

/-- **`A(t, I^{≺γ})^β = A(t, I^{≺γ})` for `γ ≺ Ω`** (Freund, proof of Theorem 5.9). -/
theorem cap_unfold_of_ne_top (A : Semisentence LXI 1) {a : Stage} (ha : a ≠ Stage.top)
    (t : Semiterm LIinf ξ n) : cap b (unfold A a t) = unfold A a t := by
  rw [cap_unfold, if_neg ha]

theorem relParams_capRel : ∀ {k : ℕ} (r : LIinf.Rel k), relParams (capRel b r) ⊆ relParams r ∪ {b.1}
  | _, Sum.inl _ => Set.empty_subset _
  | _, Sum.inr IInfRel.X => Set.empty_subset _
  | _, Sum.inr (IInfRel.stage a) => by
    by_cases h : a = Stage.top
    · show ({(if a = Stage.top then b else a).1} : Set ThetaNote) ⊆ {a.1} ∪ {b.1}
      rw [if_pos h]; exact Set.subset_union_right
    · show ({(if a = Stage.top then b else a).1} : Set ThetaNote) ⊆ {a.1} ∪ {b.1}
      rw [if_neg h]; exact Set.subset_union_left

/-- `k(φ^β) ⊆ k(φ) ∪ {β}` (Freund, proof of Theorem 5.9). -/
theorem params_cap {m : ℕ} (φ : Semiformula LIinf ξ m) : params (cap b φ) ⊆ params φ ∪ {b.1} := by
  induction φ using Semiformula.rec' with
  | hverum => exact Set.empty_subset _
  | hfalsum => exact Set.empty_subset _
  | hrel r v => exact relParams_capRel b r
  | hnrel r v => exact relParams_capRel b r
  | hand φ ψ ihφ ihψ =>
    rw [cap_and, params_and, params_and]
    exact Set.union_subset (ihφ.trans (Set.union_subset_union_left _ Set.subset_union_left))
      (ihψ.trans (Set.union_subset_union_left _ Set.subset_union_right))
  | hor φ ψ ihφ ihψ =>
    rw [cap_or, params_or, params_or]
    exact Set.union_subset (ihφ.trans (Set.union_subset_union_left _ Set.subset_union_left))
      (ihψ.trans (Set.union_subset_union_left _ Set.subset_union_right))
  | hall φ ih => exact ih
  | hexs φ ih => exact ih

end Cap

end InductiveDef

end OrdinalAnalysis
