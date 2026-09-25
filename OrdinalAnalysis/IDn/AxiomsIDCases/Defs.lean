/- Source: OrdinalAnalysis\ID1\AxiomsID.lean (one-level `Omega`/`Stage` generalised to level `k : Fin n`). -/

import OrdinalAnalysis.IDn.NumSubst
import OrdinalAnalysis.IDn.Sound
/-
  The axioms of the inductive definition in the infinitary calculus of `ID₁`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, §6: Proposition 6.2 (the closure axiom (F)),
  Exercise 6.3 (monotonicity of operator forms), Proposition 6.4 (the induction axiom (L)).

  **Operator forms applied to predicates.**  For the operator form `A` (the symbol `I` of
  `(LXIn n)` the place-holder), Freund writes `φ(t, θ)` for the result of applying `A` to the
  predicate `θ` at `t`.  Here the embedded form `A(t, I^{≺Ω}) = unfold A k Ω t` is the base, and
  `plugI P B` replaces in `B` every atom `I^{≺Ω} s` by `P(s)` and every `¬I^{≺Ω} s` by `¬P(s)`.
  Two predicates occur: the stage `I^{≺γ}` (`predStage γ`), for which
  `plugI (I^{≺γ}) (A(t, I^{≺Ω})) = A(t, I^{≺γ})` (`plugI_unfold`), and a formula `G` with one
  free slot (`predOf G`), for which the embedded `A(x, F)` is `plugI (F⁺) (A(x, I^{≺Ω}))`
  (`embK_substI`).  Both commute with the substitutions of the calculus (`rew_plugI`).

  **Exercise 6.3** (`ex63`): if `H ⊢^α_ρ Γ, ¬θ(s), ψ(s)` for every closed `s`, then
  `H ⊢^{α ⊕ 2c}_ρ Γ, ¬φ(t, θ), φ(t, ψ)` for every closed instance `B = A(t, I^{≺Ω})`, `c` the
  complexity of `B`.  By induction on `c`; positivity (`OpShape`: no `¬I^{≺Ω}`) is what makes
  the atom case the hypothesis, and `ω ⪯ α` makes the witnesses of clause (W) admissible.

  **Proposition 6.2** (`closure_derivable`): `H ⊢^{Ω + ω·m}_0 ∀x (A(x, I) → I x)` for the
  embedded closure axiom: Lemma 6.1 for `A(m'̄, I^{≺Ω})`, clause (Fix), two disjunctions and the
  ω-rule.

  **Proposition 6.4** (`indAx_derivable`): for `Cl := ∀x (A(x, ψ⁺) → ψ⁺(x))`, by induction on
  `δ ⪯ Ω` (well-founded, on the notations),

      H[δ] ⊢^{ω·β + ω·δ}_0 ¬Cl, ¬I^{≺δ} t, ψ⁺(t)        for every closed t,

  `β := Ω ⊕ c` with `c` the complexity of `ψ⁺` (so `rk ψ⁺ ⪯ β`, as Freund's
  `β = max{rk ψ⁺, 1}`, and `ω · β + ω · Ω = Ω · 2`).  The premise for `γ ≺ δ` of clause (V) on
  `¬I^{≺δ} t` combines the induction hypothesis through Exercise 6.3, Lemma 6.1 for `ψ⁺(t)`,
  clause (V) on the conjunction, the replacement of `t` by the numeral of its value, and
  clause (W) on `¬Cl`.  At `δ = Ω` the ω-rule and two disjunctions give the axiom at height
  `Ω · 2 + 5`, and the universal closure adds its number of variables.

  The sums `ω·β + ω·δ` are ordinal sums (`ThetaWNoteD.add`), as in the source; finite
  increments are natural sums with numerals, which agree with ordinal sums
  (`add_ofNat_eq_nadd`).

  Contents.

    `predStage`, `predOf`, `plugI`, `rew_plugI`, `plugI_unfold`, `embK_substI`
    `OpShape`, `opShape_unfold`
    `ex63`                                          **Exercise 6.3**
    `closure_derivable`, `closure_axiom`            **Proposition 6.2**
    `indAx_claim`, `indAx_derivable`, `indAx_axiom` **Proposition 6.4**
-/

set_option autoImplicit false

namespace OrdinalAnalysis
variable {n : ℕ} (k : Fin n)

namespace IDn

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting

/-! ### Predicates plugged into an operator form -/

section Plug

/-- A predicate on terms at every level. -/
abbrev Pred (n : ℕ) : Type := ∀ m : ℕ, Semiterm (LIinfN n) ℕ m → Semiformula (LIinfN n) ℕ m

/-- The stage `I_k^{≺γ}` (of the level `k` being unfolded) as a predicate. -/
def predStage (g : StageAt k.val) : Pred n := fun _ s => stageAt (⟨k, g⟩ : Stage n) s

/-- The formula `G(x)` as a predicate. -/
def predOf (G : Semiformula (LIinfN n) ℕ 1) : Pred n := fun _ s => G ⇜ ![s]

/-- An atom with `I_k^{≺Ω_{k+1}}` replaced by `P`. -/
def plugRel (P : Pred n) {m : ℕ} :
    {j : ℕ} → (LIinfN n).Rel j → (Fin j → Semiterm (LIinfN n) ℕ m) → Semiformula (LIinfN n) ℕ m
  | _, Sum.inl r, v => .rel (Sum.inl r) v
  | _, Sum.inr IInfRelN.X, v => .rel (Sum.inr IInfRelN.X) v
  | _, Sum.inr (IInfRelN.stage a), v =>
    if a = Stage.top k then P m (v 0) else .rel (Sum.inr (IInfRelN.stage a)) v

/-- A negated atom with `I_k^{≺Ω_{k+1}}` replaced by `P`. -/
def plugNrel (P : Pred n) {m : ℕ} :
    {j : ℕ} → (LIinfN n).Rel j → (Fin j → Semiterm (LIinfN n) ℕ m) → Semiformula (LIinfN n) ℕ m
  | _, Sum.inl r, v => .nrel (Sum.inl r) v
  | _, Sum.inr IInfRelN.X, v => .nrel (Sum.inr IInfRelN.X) v
  | _, Sum.inr (IInfRelN.stage a), v =>
    if a = Stage.top k then ∼(P m (v 0)) else .nrel (Sum.inr (IInfRelN.stage a)) v

/-- **`B` with every `I_k^{≺Ω_{k+1}} s` replaced by `P(s)`**: Freund's `φ(t, θ)` from
`φ(t, I^{≺Ω})`, read at level `k`. -/
def plugI (k : Fin n) (P : Pred n) : {m : ℕ} → Semiformula (LIinfN n) ℕ m → Semiformula (LIinfN n) ℕ m
  | _, .verum => ⊤
  | _, .falsum => ⊥
  | _, .rel r v => plugRel k P r v
  | _, .nrel r v => plugNrel k P r v
  | _, .and φ ψ => plugI k P φ ⋏ plugI k P ψ
  | _, .or φ ψ => plugI k P φ ⋎ plugI k P ψ
  | _, .all φ => ∀¹ plugI k P φ
  | _, .exs φ => ∃¹ plugI k P φ

variable (P : Pred n)

/-- The rewritings that fix the free variables. -/
def FixF {n₁ n₂ : ℕ} (ω : Rew (LIinfN n) ℕ n₁ ℕ n₂) : Prop := ∀ x : ℕ, ω &x = &x

/-- The rewritings that send every free variable `x` to the numeral of `f x`. -/
def NumF (f : ℕ → ℕ) {n₁ n₂ : ℕ} (ω : Rew (LIinfN n) ℕ n₁ ℕ n₂) : Prop :=
  ∀ x : ℕ, ω &x = ((f x : ℕ) : Semiterm (LIinfN n) ℕ n₂)

end Plug

/-! ### The two plugged forms -/

section PlugForms

/-- The atoms of an embedded operator form positive in level `k`, `X`-free: arithmetic atoms,
any stage atom of a level other than `k` (fixed, in either polarity), and positive atoms
`I_k^{≺Ω_{k+1}} s` of level `k` itself. -/
def OpRel (k : Fin n) : {j : ℕ} → (LIinfN n).Rel j → Prop
  | _, Sum.inl _ => True
  | _, Sum.inr IInfRelN.X => False
  | _, Sum.inr (IInfRelN.stage a) => a.lvl ≠ k ∨ a = Stage.top k

/-- Negated atoms of an embedded operator form positive in level `k`: arithmetic, or a stage
atom of a level other than `k`; never a negated `I_k^{≺Ω_{k+1}}`. -/
def OpNrel (k : Fin n) : {j : ℕ} → (LIinfN n).Rel j → Prop
  | _, Sum.inl _ => True
  | _, Sum.inr IInfRelN.X => False
  | _, Sum.inr (IInfRelN.stage a) => a.lvl ≠ k

/-- **The shape of `A(t, I_k^{≺Ω_{k+1}})`** for an operator form positive in level `k`, `X`-free. -/
def OpShape (k : Fin n) {ξ : Type*} : {m : ℕ} → Semiformula (LIinfN n) ξ m → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel r _ => OpRel k r
  | _, .nrel r _ => OpNrel k r
  | _, .and φ ψ => OpShape k φ ∧ OpShape k ψ
  | _, .or φ ψ => OpShape k φ ∧ OpShape k ψ
  | _, .all φ => OpShape k φ
  | _, .exs φ => OpShape k φ

variable (P : Pred n)

end PlugForms

/-! ### Exercise 6.3 -/

section Ex63

variable {A : Semisentence (LXIn n) 1} {ρ : ThetaWNoteD} {H : Set ThetaWNoteD → Set ThetaWNoteD}

end Ex63

/-! ### Proposition 6.2: the closure axiom -/

section Closure

variable {A : Semisentence (LXIn n) 1}

/-- The body `A(x, I^{≺Ω})` of the embedded operator form, with the slot `x` free. -/
abbrev bodyTop (A : Semisentence (LXIn n) 1) : Semiformula (LIinfN n) ℕ 1 :=
  (Rew.emb ▹ formAt A k (StageAt.top k.val) : Semiformula (LIinfN n) ℕ 1)

end Closure

/-! ### Ordinal sums for Proposition 6.4 -/

section Sums

end Sums

/-! ### Proposition 6.4: the induction axiom -/

section Induction

variable {A : Semisentence (LXIn n) 1} {H : Set ThetaWNoteD → Set ThetaWNoteD}

/-- `Cl(G) = ∀x (A(x, G) → G(x))`, the premise of the induction axiom. -/
def ClF (A : Semisentence (LXIn n) 1) (G : Semiformula (LIinfN n) ℕ 1) : Proposition (LIinfN n) :=
  ∀¹ (∼(plugI k (predOf G) (bodyTop k A)) ⋎ G)

end Induction

/-! ### Proposition 6.4, the axiom -/

section IndAxiom

variable {A : Semisentence (LXIn n) 1} {H : Set ThetaWNoteD → Set ThetaWNoteD}

end IndAxiom

end IDn

end OrdinalAnalysis
