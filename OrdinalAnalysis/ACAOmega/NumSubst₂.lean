/-
  Numeral substitutions on the second-order syntax.

  This is the second-order counterpart of `Gentzen/NumSubst.lean`, needed to
  replay a finitary `ACA.Derivation` inside `OmegaDerivable₂` for every numeral
  assignment `f : ℕ → ℕ` at once — exactly as the first-order replay does, and
  for the same reason: the `cut` rule may introduce a formula with free number
  variables the conclusion does not have, so "instantiated by `f`" is the
  invariant, not "closed".

  The base substitution `numSubst₂ f` acts only on the *number* side of the
  syntax (it sends the free number variable `&x` to the numeral `numAt (f x)`);
  it is a plain `FirstOrder.Rew ℒₒᵣ ℕ n ℕ n`, level-polymorphic in `n` exactly as
  `numAt` already is, and it acts on a second-order `Semiformula ℒₒᵣ ℕ ℕ N n`
  through the generic rewriting instance of `SecondOrder/Syntax/Rew.lean` — a
  first-order-only operation that never looks at `N`, the number of bound *set*
  variables. Two families of law are needed.

  * The **first-order laws**, at `N = 0`, are ports of `Gentzen/NumSubst.lean`'s
    three equations verbatim: `numSubst₂_free₀` (the `all₁` premise is the `n`-th
    instance of the conclusion's body), `seqSubst₂_shift₀` (the shifted context is
    unaffected), `numSubst₂_subst₁` (the `exs₁` premise, with the witness turned
    into the ground term `numSubst₂ f t`). Every proof is the same "compose, then
    compare on bound and free variables" idiom (`Rew.ext`/`smul_ext'` after
    `← comp_app`), because none of it depends on `N` — `Semiformula.rew` treats
    `N` as an inert parameter throughout.

  * The **second-order laws** say that `numSubst₂ f` commutes with the two
    structural operations the set-quantifier rules use.

      `numSubst₂_free₁`/`seqSubst₂_shift₁` (`all₂`): commuting with the
      eigenvariable operations `free₁`/`shift₁`, which are renamings of the free
      *set* variables (`Semiproposition.free₁ = SecondOrder.Rew.free.app`,
      `.shift₁ = SecondOrder.Rew.shift.app`).  Both renamings are `AtomRew`s
      (`ACAOmega.Evaluate.atomRew_free/atomRew_shift`: their `bv`/`fv` components
      are themselves atoms `#0 ∈# Y`/`#0 ∈& Y`, with no free number variable), so
      they commute with *any* first-order rewriting acting underneath — this is
      `rew_app_atom` below, the exact analogue of `ev₂_app_atom`, generalising the
      first-order rewriter over every level `n` because the induction on the
      formula descends under nested `∀¹`/`∃¹`.

      `numSubst₂_subst₂` (`exs₂`): commuting with a genuine second-order
      substitution `φ/⟦ψ⟧ = (SecondOrder.Rew.subst ![ψ]).app φ`, whose `bv 0 = ψ`
      is an arbitrary formula, not an atom. This needs its own induction
      (`numSubst₂_app`), whose only new content over `rew_app_atom` is at the
      leaves: there, commuting with a substitution `χ/[t]` (`χ` the arbitrary
      one-hole formula sitting at `Ω.bv X`) is a *composition* identity of plain
      `FirstOrder.Rew`s, `numSubst₂_comp_subst`, provable with no induction at all
      because `rew_numAt` (`ACAOmega.Evaluate`) already says every rewriting fixes
      a numeral — the one fact that makes the two sides, "substitute then
      renumber" and "renumber then substitute", land on the same numeral.

  Pitfalls carried over from `Gentzen/NumSubst.lean`.

  * `Rew` composition: `simpa [← comp_app] using smul_ext' <| by ext x <;> simp
    [Rew.comp_app, numAt]` is the idiom for every law that is really an equation
    of *rewriters* — it avoids induction on the formula entirely for the
    first-order laws.  Reaching for `induction ... using Semiformula.rec'`
    instead there does not fail, but multiplies the proof for no reason: the
    formula argument (`φ` in `numSubst₂_free₀`, `numSubst₂_subst₁`) is opaque and
    the identity is really about the two `Rew`s.
  * Wrong namespace opens: `SecondOrder.Rew.q`/`.free`/`.shift`/`.subst`/`.map`
    are written with the `SecondOrder.` prefix throughout (never bare `Rew.xxx`),
    and `FirstOrder.Rew.rewrite`/`.subst`/`.comp` likewise with the `FirstOrder.`
    prefix — both namespaces export a `Rew` and leaving the prefix off invites
    the elaborator to pick the wrong one silently.
-/
import OrdinalAnalysis.ACAOmega.Evaluate

set_option autoImplicit false

namespace OrdinalAnalysis.ACAOmega.NumSubst₂

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open OrdinalAnalysis.ACA OrdinalAnalysis.ACAOmega

/-! ### The base substitution -/

/-- The substitution sending the free *number* variable `x` to the numeral
`f x`, at any level `n` — level-polymorphic exactly as `numAt` is, so that it
can be pushed under any number of first-order binders without a separate
"one level down" definition. -/
def numSubst₂ (f : ℕ → ℕ) {n : ℕ} : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n :=
  FirstOrder.Rew.rewrite fun x => (numAt (f x) : FirstOrder.Semiterm ℒₒᵣ ℕ n)

@[simp] theorem numSubst₂_fvar (f : ℕ → ℕ) {n : ℕ} (x : ℕ) :
    (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) (&x) = numAt (f x) := rfl

@[simp] theorem numSubst₂_bvar (f : ℕ → ℕ) {n : ℕ} (x : Fin n) :
    (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) (#x) = #x := rfl

/-- Pushing `numSubst₂` under one first-order binder is again `numSubst₂`, at
the next level — the level-polymorphic replacement for a separate `numSubst₁`. -/
theorem numSubst₂_q (f : ℕ → ℕ) {n : ℕ} :
    (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n).q = (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ (n + 1) ℕ (n + 1)) := by
  simp only [numSubst₂, FirstOrder.Rew.q_rewrite]
  congr 1
  funext x
  exact rew_numAt FirstOrder.Rew.bShift (f x)

/-- The pointwise action on a sequent. -/
def seqSubst₂ (f : ℕ → ℕ) (Γ : SecondOrder.Sequent ℒₒᵣ) : SecondOrder.Sequent ℒₒᵣ :=
  Γ.map (numSubst₂ f ▹ ·)

@[simp] theorem seqSubst₂_nil (f : ℕ → ℕ) : seqSubst₂ f [] = [] := rfl

@[simp] theorem seqSubst₂_cons (f : ℕ → ℕ) (φ : Proposition ℒₒᵣ) (Γ : SecondOrder.Sequent ℒₒᵣ) :
    seqSubst₂ f (φ :: Γ) = (numSubst₂ f ▹ φ) :: seqSubst₂ f Γ := rfl

@[simp] theorem seqSubst₂_append (f : ℕ → ℕ) (Γ Δ : SecondOrder.Sequent ℒₒᵣ) :
    seqSubst₂ f (Γ ++ Δ) = seqSubst₂ f Γ ++ seqSubst₂ f Δ := List.map_append ..

theorem seqSubst₂_subset {f : ℕ → ℕ} {Δ Γ : SecondOrder.Sequent ℒₒᵣ} (h : Δ ⊆ Γ) :
    seqSubst₂ f Δ ⊆ seqSubst₂ f Γ := List.map_subset _ h

theorem mem_seqSubst₂ {f : ℕ → ℕ} {Γ : SecondOrder.Sequent ℒₒᵣ} {φ : Proposition ℒₒᵣ} (h : φ ∈ Γ) :
    numSubst₂ f ▹ φ ∈ seqSubst₂ f Γ := List.mem_map_of_mem h

/-- `numSubst₂` commutes with negation. -/
@[simp] theorem numSubst₂_neg (f : ℕ → ℕ) {N n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N n) :
    (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) ▹ (∼φ) = ∼((numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) ▹ φ) :=
  LogicalConnective.HomClass.map_neg _ _

/-! ### No free number variable, and the fixed-point law

`OmegaTruth₂.lean` has exactly this
predicate under the name `NumClosed`, but at `HEAD` that file has an unrelated
unsolved goal elsewhere and does not build, so it cannot be imported here. The
copy below is local to this file and only as large as the one fact
`seqSubst₂_eq_self` needs: a `NumClosed₂` formula is a fixed point of
`numSubst₂`, because `numSubst₂` only ever touches a free number variable, and a
`NumClosed₂` formula has none. -/

/-- **`φ` has no free number variable**: every term occurring in it is closed.
Bound number variables are permitted, so the condition is stated on each term as
`freeVariables = ∅` rather than as `Ground`, exactly as `OmegaTruth₂.NumClosed`
does. -/
def NumClosed₂ {N n : ℕ} : Semiformula ℒₒᵣ ℕ ℕ N n → Prop
  |  .rel _ v => ∀ i, (v i).freeVariables = ∅
  | .nrel _ v => ∀ i, (v i).freeVariables = ∅
  |    t ∈# _ => t.freeVariables = ∅
  |    t ∉# _ => t.freeVariables = ∅
  |    t ∈& _ => t.freeVariables = ∅
  |    t ∉& _ => t.freeVariables = ∅
  |         ⊤ => True
  |         ⊥ => True
  |     φ ⋏ ψ => NumClosed₂ φ ∧ NumClosed₂ ψ
  |     φ ⋎ ψ => NumClosed₂ φ ∧ NumClosed₂ ψ
  |      ∀¹ φ => NumClosed₂ φ
  |      ∃¹ φ => NumClosed₂ φ
  |      ∀² φ => NumClosed₂ φ
  |      ∃² φ => NumClosed₂ φ

/-- A closed term is fixed by `numSubst₂`: the only thing the rewriting can
touch is a free variable, and there is none. -/
theorem numSubst₂_eq_self_term (f : ℕ → ℕ) : ∀ {n : ℕ} {t : FirstOrder.Semiterm ℒₒᵣ ℕ n},
    t.freeVariables = ∅ → (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) t = t := by
  intro n t
  induction t with
  | bvar x => intro _; simp
  | fvar x => intro h; simp at h
  | func fn v ih =>
      intro h
      rw [FirstOrder.Semiterm.freeVariables_func] at h
      have hv : ∀ i, (v i).freeVariables = ∅ := fun i =>
        Finset.biUnion_eq_empty.mp h i (Finset.mem_univ i)
      simp only [numSubst₂, FirstOrder.Rew.func]
      exact congrArg (FirstOrder.Semiterm.func fn) (funext fun i => ih i (hv i))

/-- **On a `NumClosed₂` formula every substitution is the identity.** -/
theorem numSubst₂_eq_self (f : ℕ → ℕ) : ∀ {N n : ℕ} {φ : Semiformula ℒₒᵣ ℕ ℕ N n},
    NumClosed₂ φ → (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) ▹ φ = φ := by
  intro N n φ
  induction φ using Semiformula.rec' with
  | hRel r v =>
      intro h
      rw [Semiformula.rew_rel]
      exact congrArg (Semiformula.rel r) (funext fun i => numSubst₂_eq_self_term f (h i))
  | hNrel r v =>
      intro h
      rw [Semiformula.rew_nrel]
      exact congrArg (Semiformula.nrel r) (funext fun i => numSubst₂_eq_self_term f (h i))
  | hBvar X t => intro h; rw [Semiformula.rew_bvar, numSubst₂_eq_self_term f h]
  | hNbvar X t => intro h; rw [Semiformula.rew_nbvar, numSubst₂_eq_self_term f h]
  | hFvar X t => intro h; rw [Semiformula.rew_fvar, numSubst₂_eq_self_term f h]
  | hNfvar X t => intro h; rw [Semiformula.rew_nfvar, numSubst₂_eq_self_term f h]
  | hVerum => intro _; rfl
  | hFalsum => intro _; rfl
  | hAnd φ ψ ihφ ihψ =>
      intro h
      simp only [LogicalConnective.HomClass.map_and]
      rw [ihφ h.1, ihψ h.2]
  | hOr φ ψ ihφ ihψ =>
      intro h
      simp only [LogicalConnective.HomClass.map_or]
      rw [ihφ h.1, ihψ h.2]
  | hAll₁ φ ih =>
      intro h
      simp only [Semiformula.rew_all₀, numSubst₂_q]
      congr 1
      exact ih h
  | hExs₁ φ ih =>
      intro h
      simp only [Semiformula.rew_exs₀, numSubst₂_q]
      congr 1
      exact ih h
  | hAll₂ φ ih =>
      intro h
      rw [Semiformula.rew_all₁]
      congr 1
      exact ih h
  | hExs₂ φ ih =>
      intro h
      rw [Semiformula.rew_exs₁]
      congr 1
      exact ih h

/-- **On a sequent with no free number variable every substitution is the
identity.** -/
theorem seqSubst₂_eq_self {f : ℕ → ℕ} {Γ : SecondOrder.Sequent ℒₒᵣ}
    (h : ∀ φ ∈ Γ, NumClosed₂ φ) : seqSubst₂ f Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih =>
      rw [seqSubst₂_cons, numSubst₂_eq_self f (h φ (by simp)),
        ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))]

/-! ### Closedness of number terms after assignment -/

/-- The witness is closed after substitution. -/
theorem freeVariables_numSubst₂_term (f : ℕ → ℕ) (t : FirstOrder.SyntacticTerm ℒₒᵣ) :
    ((numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) t).freeVariables = ∅ := by
  induction t with
  | bvar x => exact Fin.elim0 x
  | fvar x => simp only [numSubst₂_fvar]; exact (ground_numAt (f x)).2
  | func fn v ih =>
      simp only [numSubst₂, FirstOrder.Rew.func, FirstOrder.Semiterm.freeVariables_func]
      exact Finset.biUnion_eq_empty.mpr (fun i _ => ih i)

theorem ground_numSubst₂_term (f : ℕ → ℕ) (t : FirstOrder.SyntacticTerm ℒₒᵣ) :
    Ground ((numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) t) :=
  ground_of_closed (freeVariables_numSubst₂_term f t)

/-! ### The first-order laws -/

/-- **The `all₁` premise.**  Assigning `n` to the fresh number variable of
`φ.free₀` is the `n`-th instance of the body under `f`. -/
theorem numSubst₂_free₀ (f : ℕ → ℕ) (n : ℕ) (φ : Semiproposition ℒₒᵣ 0 1) :
    (numSubst₂ (n :>ₙ f) : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹ (Semiproposition.free₀ φ)
      = ((numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1) ▹ φ)/[numAt n] := by
  simp only [Semiproposition.free₀]
  simpa [← comp_app] using smul_ext' <| by
    ext x <;> simp [numSubst₂, FirstOrder.Rew.comp_app, numAt]

/-- **The shifted context.**  Under `n :>ₙ f` a shifted formula is the formula
under `f`. -/
theorem numSubst₂_shift₀ (f : ℕ → ℕ) (n : ℕ) (φ : Proposition ℒₒᵣ) :
    (numSubst₂ (n :>ₙ f) : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹ (Semiproposition.shift₀ φ)
      = numSubst₂ f ▹ φ := by
  simp only [Semiproposition.shift₀]
  simpa [← comp_app] using smul_ext' <| by
    ext x <;> simp [numSubst₂, FirstOrder.Rew.comp_app, numAt]

theorem seqSubst₂_shift₀ (f : ℕ → ℕ) (n : ℕ) (Γ : SecondOrder.Sequent ℒₒᵣ) :
    seqSubst₂ (n :>ₙ f) (SecondOrder.Sequent.shift₀ Γ) = seqSubst₂ f Γ := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih =>
      simp [SecondOrder.Sequent.shift₀, seqSubst₂, numSubst₂_shift₀, ih,
        SecondOrder.Sequent.shift₀]

/-- **The `exs₁` premise.**  The witness becomes the closed term
`numSubst₂ f t`. -/
theorem numSubst₂_subst₁ (f : ℕ → ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ 0) (φ : Semiproposition ℒₒᵣ 0 1) :
    (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹ (φ/[t])
      = ((numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1) ▹ φ)/[(numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) t] := by
  simpa [← comp_app] using smul_ext' <| by
    ext x <;> simp [numSubst₂, FirstOrder.Rew.comp_app, numAt]

/-! ### Renamings of set variables commute with `numSubst₂`

The general fact: any first-order rewriting commutes with an `AtomRew`,
because an `AtomRew`'s `bv`/`fv` components have no free number variable to be
touched. This is `ev₂_app_atom`'s proof, with `ev₂` replaced by an arbitrary
first-order rewriting `ω` (generalised over every level, since the induction on
the formula descends under nested first-order quantifiers). -/

theorem rew_app_atom : ∀ {N₁ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n)
    (ω : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) {N₂ : ℕ} (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ),
    AtomRew Ω → ω ▹ (Ω.app φ) = Ω.app (ω ▹ φ) := by
  intro N₁ n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro ω N₂ Ω _; simp [Semiformula.rew_rel, Semiformula.rew_nrel]
  | hNrel r v => intro ω N₂ Ω _; simp [Semiformula.rew_rel, Semiformula.rew_nrel]
  | hBvar X t =>
      intro ω N₂ Ω hΩ
      rcases hΩ.1 X with ⟨Y, hY⟩ | ⟨Y, hY⟩ <;> simp [hY]
  | hNbvar X t =>
      intro ω N₂ Ω hΩ
      rcases hΩ.1 X with ⟨Y, hY⟩ | ⟨Y, hY⟩ <;> simp [hY]
  | hFvar X t =>
      intro ω N₂ Ω hΩ
      rcases hΩ.2 X with ⟨Y, hY⟩ | ⟨Y, hY⟩ <;> simp [hY]
  | hNfvar X t =>
      intro ω N₂ Ω hΩ
      rcases hΩ.2 X with ⟨Y, hY⟩ | ⟨Y, hY⟩ <;> simp [hY]
  | hVerum => intro ω N₂ Ω _; simp
  | hFalsum => intro ω N₂ Ω _; simp
  | hAnd φ ψ ihφ ihψ => intro ω N₂ Ω hΩ; simp [ihφ ω Ω hΩ, ihψ ω Ω hΩ]
  | hOr φ ψ ihφ ihψ => intro ω N₂ Ω hΩ; simp [ihφ ω Ω hΩ, ihψ ω Ω hΩ]
  | hAll₁ φ ih => intro ω N₂ Ω hΩ; simp [ih ω.q Ω hΩ]
  | hExs₁ φ ih => intro ω N₂ Ω hΩ; simp [ih ω.q Ω hΩ]
  | hAll₂ φ ih => intro ω N₂ Ω hΩ; simp [ih ω Ω.q hΩ.q]
  | hExs₂ φ ih => intro ω N₂ Ω hΩ; simp [ih ω Ω.q hΩ.q]

/-- **`numSubst₂` commutes with `free₁`** — the eigenvariable half of the
`(∀₂)` rule. -/
theorem numSubst₂_free₁ (f : ℕ → ℕ) (φ : Semiproposition ℒₒᵣ 1 0) :
    (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹ (Semiproposition.free₁ φ)
      = Semiproposition.free₁ ((numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹ φ) :=
  rew_app_atom φ (numSubst₂ f) SecondOrder.Rew.free atomRew_free

/-- **`numSubst₂` commutes with `shift₁`** — the context half of the `(∀₂)`
rule. -/
theorem numSubst₂_shift₁ (f : ℕ → ℕ) (φ : Proposition ℒₒᵣ) :
    (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹ (Semiproposition.shift₁ φ)
      = Semiproposition.shift₁ ((numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹ φ) :=
  rew_app_atom φ (numSubst₂ f) SecondOrder.Rew.shift atomRew_shift

theorem seqSubst₂_shift₁ (f : ℕ → ℕ) (Γ : SecondOrder.Sequent ℒₒᵣ) :
    seqSubst₂ f (SecondOrder.Sequent.shift₁ Γ) = SecondOrder.Sequent.shift₁ (seqSubst₂ f Γ) := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih =>
      simp [SecondOrder.Sequent.shift₁, seqSubst₂, numSubst₂_shift₁, ih]

/-! ### The second-order substitution law

This is the law the `exs₂` replay needs.  Unlike `free₁`/`shift₁`, a second-order
substitution `φ/⟦ψ⟧` instantiates by an *arbitrary* one-hole formula `ψ`, not an
atom, so `rew_app_atom` does not apply; the induction is redone with the one
new ingredient at the leaves, `numSubst₂_comp_subst`. -/

/-- **The leaf identity.**  Substituting a term into a one-hole formula and then
renumbering is renumbering the term and the formula separately, at the matching
levels — no induction needed, only that `numSubst₂` fixes numerals
(`rew_numAt`). -/
theorem numSubst₂_comp_subst {n : ℕ} (f : ℕ → ℕ) (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n).comp (FirstOrder.Rew.subst ![t])
      = (FirstOrder.Rew.subst ![(numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) t]).comp
          (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1) := by
  ext x
  · have hx : x = 0 := Subsingleton.elim x 0
    subst hx
    simp [FirstOrder.Rew.comp_app]
  · simp only [FirstOrder.Rew.comp_app, FirstOrder.Rew.subst_fvar, numSubst₂_fvar]
    exact (rew_numAt (FirstOrder.Rew.subst ![(numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) t]) (f x)).symm

theorem numSubst₂_subst_key {N n : ℕ} (f : ℕ → ℕ) (χ : Semiformula ℒₒᵣ ℕ ℕ N 1)
    (t : FirstOrder.Semiterm ℒₒᵣ ℕ n) :
    (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) ▹ (χ/[t])
      = ((numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1) ▹ χ)/[(numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) t] := by
  simpa [← comp_app] using smul_ext' (numSubst₂_comp_subst f t) (φ := χ)

/-- **`.q` and `Rew.map` by `numSubst₂` commute.**  Only true because
`numSubst₂` fixes the bound variable `#0` (`numSubst₂_bvar`, `.q`'s own leaf);
for `bmap`'s target this is `Semiformula.bmap_comm`, already proved generically
for *any* first-order rewriting since `bmap` only touches set-side indices. -/
theorem numSubst₂_map_q {N₁ N₂ : ℕ} (f : ℕ → ℕ) (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ) :
    Ω.q.map (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1)
      = (Ω.map (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1)).q := by
  ext X
  · cases X using Fin.cases with
    | zero =>
        simp [SecondOrder.Rew.map_bv, SecondOrder.Rew.q_bv_zero, Semiformula.rew_bvar,
          numSubst₂_bvar]
    | succ X =>
        simp only [SecondOrder.Rew.map_bv, SecondOrder.Rew.q_bv_succ]
        exact (Semiformula.bmap_comm (numSubst₂ f) (Ω.bv X) Fin.succ).symm
  · simp only [SecondOrder.Rew.map_fv, SecondOrder.Rew.q_fv]
    exact (Semiformula.bmap_comm (numSubst₂ f) (Ω.fv X) Fin.succ).symm

/-- **`numSubst₂` commutes with an arbitrary second-order substitution**, up to
transporting `Ω` itself by `numSubst₂` at the one-hole level. -/
theorem numSubst₂_app (f : ℕ → ℕ) : ∀ {N₁ n : ℕ} (φ : Semiformula ℒₒᵣ ℕ ℕ N₁ n) {N₂ : ℕ}
    (Ω : SecondOrder.Rew ℒₒᵣ ℕ N₁ ℕ N₂ ℕ),
    (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) ▹ (Ω.app φ)
      = (Ω.map (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1)).app
          ((numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ n ℕ n) ▹ φ) := by
  intro N₁ n φ
  induction φ using Semiformula.rec' with
  | hRel r v => intro N₂ Ω; simp [Semiformula.rew_rel, Semiformula.rew_nrel]
  | hNrel r v => intro N₂ Ω; simp [Semiformula.rew_rel, Semiformula.rew_nrel]
  | hBvar X t =>
      intro N₂ Ω
      simp only [SecondOrder.Rew.app_bvar, SecondOrder.Rew.map_bv]
      exact numSubst₂_subst_key f (Ω.bv X) t
  | hNbvar X t =>
      intro N₂ Ω
      simp only [SecondOrder.Rew.app_nbvar, SecondOrder.Rew.map_bv, numSubst₂_neg]
      exact congrArg (fun χ => ∼χ) (numSubst₂_subst_key f (Ω.bv X) t)
  | hFvar X t =>
      intro N₂ Ω
      simp only [SecondOrder.Rew.app_fvar, SecondOrder.Rew.map_fv]
      exact numSubst₂_subst_key f (Ω.fv X) t
  | hNfvar X t =>
      intro N₂ Ω
      simp only [SecondOrder.Rew.app_nfvar, SecondOrder.Rew.map_fv, numSubst₂_neg]
      exact congrArg (fun χ => ∼χ) (numSubst₂_subst_key f (Ω.fv X) t)
  | hVerum => intro N₂ Ω; simp
  | hFalsum => intro N₂ Ω; simp
  | hAnd φ ψ ihφ ihψ => intro N₂ Ω; simp [ihφ Ω, ihψ Ω]
  | hOr φ ψ ihφ ihψ => intro N₂ Ω; simp [ihφ Ω, ihψ Ω]
  | hAll₁ φ ih =>
      intro N₂ Ω
      simp only [SecondOrder.Rew.app_all₀, Semiformula.rew_all₀, numSubst₂_q]
      exact congrArg (fun χ => ∀¹ χ) (ih Ω)
  | hExs₁ φ ih =>
      intro N₂ Ω
      simp only [SecondOrder.Rew.app_exs₀, Semiformula.rew_exs₀, numSubst₂_q]
      exact congrArg (fun χ => ∃¹ χ) (ih Ω)
  | hAll₂ φ ih =>
      intro N₂ Ω
      simp only [SecondOrder.Rew.app_all₁, Semiformula.rew_all₁, ih Ω.q, numSubst₂_map_q f Ω]
  | hExs₂ φ ih =>
      intro N₂ Ω
      simp only [SecondOrder.Rew.app_exs₁, Semiformula.rew_exs₁, ih Ω.q, numSubst₂_map_q f Ω]

/-- The image of `Rew.subst ![ψ]` under `Rew.map` by `numSubst₂` is again a
singleton substitution, at the renumbered witness — specific to `numSubst₂`
(not an arbitrary `ω`), because the `fv` leg needs `ω` to fix the bound variable
`#0`, which only a `rewrite`-shaped `ω` does. -/
theorem numSubst₂_map_subst_singleton {N : ℕ} (f : ℕ → ℕ) (ψ : Semiformula ℒₒᵣ ℕ ℕ N 1) :
    (SecondOrder.Rew.subst (L := ℒₒᵣ) (Ξ₁ := ℕ) (N₂ := N) ![ψ]).map
        (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1)
      = SecondOrder.Rew.subst ![(numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1) ▹ ψ] := by
  ext X
  · have hX : X = 0 := Subsingleton.elim X 0
    subst hX
    simp [SecondOrder.Rew.map_bv, SecondOrder.Rew.subst_bv]
  · simp [SecondOrder.Rew.map_fv, SecondOrder.Rew.subst_fv, Semiformula.rew_fvar, numSubst₂_bvar]

/-- **`numSubst₂_subst₂`.**  Number-variable assignment commutes with a
second-order substitution: renumbering `φ/⟦ψ⟧` is substituting the renumbered
`ψ` into the renumbered `φ`. -/
theorem numSubst₂_subst₂ (f : ℕ → ℕ) (φ : Semiproposition ℒₒᵣ 1 0) (ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1) :
    (numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹ (φ/⟦ψ⟧)
      = ((numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 0 ℕ 0) ▹ φ)/⟦(numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1) ▹ ψ⟧ := by
  have h := numSubst₂_app f φ (SecondOrder.Rew.subst ![ψ])
  rwa [numSubst₂_map_subst_singleton] at h

/-- **`Arith` is preserved by `numSubst₂`** — the arithmetical-witness side
condition of `exs₂` survives the renumbering. -/
theorem arith_numSubst₂ (f : ℕ → ℕ) {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1} (h : Arith ψ) :
    Arith ((numSubst₂ f : FirstOrder.Rew ℒₒᵣ ℕ 1 ℕ 1) ▹ ψ) :=
  (arith_rew (numSubst₂ f) ψ).mpr h

end OrdinalAnalysis.ACAOmega.NumSubst₂
