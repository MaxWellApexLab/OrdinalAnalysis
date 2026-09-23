/-
  The reduction lemma and the first cut-elimination theorem for the ramified
  calculus `RA_∞` (design D2).

  This is `ACAOmega/Reduction.lean` ported to `OmegaDerivableR`.  The
  architecture is unchanged: both sequents are related to the target by `⊆`, the
  recursion is on the symmetric measure `β ⊕ γ`, the ordinal delivered is the
  doubled natural sum `redOrd β γ`, and the induction over the *right* derivation
  is done once and generically (`reduction_right`) with one handler per rule that
  could be principal.  Three things are different, and all three are savings.

  * **There is no substitution provider.**  `ACAOmega`'s (∀₂)/(∃₂) principal case
    substitutes a *formula* for an eigenvariable, which is why that file threads a
    `SubstProvider` through all of its 1368 lines and why its calculus needs
    *general* identity (the atomic leaf `[t ∈ X, t ∉ X]` becomes `[ψ(t), ∼ψ(t)]`,
    derivable only at height `2·complexity ψ`, for which `redOrd β γ` has no
    room).  D2 performs no formula-for-variable substitution anywhere: a level-`ν`
    set quantifier is a number quantifier over codes, so the ω-rule and `exs`
    already handle it, and the only substitution in the calculus is of a *term*
    into the body of a code, which `rank_subst₁_le` says cannot raise the rank.  So
    identity stays atomic and the provider disappears.

  * **Two new rules, two new handlers, one new principal case.**  (Pr) and (Pr⁻)
    add a handler each to `reduction_right`; six of the seven pairs they form
    with the other rules are refuted by a head mismatch, and the seventh —
    (Pr)/(Pr⁻) on the same atom — is `Ramified/ReductionProbe.lean`'s
    `reduction_pr_principal`, which performs **one** cut (not the two nested cuts
    of the propositional cases) and so makes no new demand on the ordinal
    arithmetic.  The cut it performs is legal because
    `rank (A_a(n̄)) ≤ rank (body a) < ω·(lvl a − 1) ⊕ stage a = rank (n̄ ∈̇ ā) ≤ ρ`,
    which is `Ramified/Rank.lean`'s `rank_body_lt_memRank`: *the* lemma of the
    design, and the reason for the stage condition on codes.

  * **`MemFree` is a hypothesis of the whole lemma.**  A set atom is a literal,
    so `Literals` alone permits one as an axiom, and a (Pr) inference against
    such an axiom would be an irreducible principal case.  `MemFree A` — no axiom
    is a set atom — rules it out, and `Ramified/Literals.lean` discharges it for
    the intended axiom set.  This is the one genuinely new side condition of D2
    and it is why `reduction` carries an extra argument that
    `ACAOmega/Reduction.lean`'s does not.

  Cut ranks are ordinal notations (`Gamma0Note`), as in `ACAOmega`, so
  `PredBound`, `Chain` and `cutElimination_chain` are restated over `Gamma0Note`
  rather than `NONote`; nothing about them changes.
-/
import OrdinalAnalysis.Ramified.Literals
import OrdinalAnalysis.Ramified.ReductionProbe

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open LO LO.FirstOrder LO.FirstOrder.Derivation

/-! ### Head mismatch

Six of the seven refutations each new rule contributes are "these two formulas
have different outermost symbols".  `Semiformula.rel`'s arity is an *index*, so
`injection` cannot be used and `simp` cannot always be relied on to normalise
`∼(memAt ν t s)` before unfolding it; a numeric tag read off the head, compared
by `congrArg`, is immune to both problems. -/

/-- A numeric tag of the outermost symbol of a formula. -/
def headTag {n : ℕ} : Semiformula LRA ℕ n → ℕ
  |  .rel _ _ => 2
  | .nrel _ _ => 3
  |         ⊤ => 0
  |         ⊥ => 1
  |     _ ⋏ _ => 4
  |     _ ⋎ _ => 5
  |      ∀¹ _ => 6
  |      ∃¹ _ => 7

section HeadTag

variable {n : ℕ}

@[simp] theorem headTag_verum : headTag (⊤ : Semiformula LRA ℕ n) = 0 := rfl

@[simp] theorem headTag_falsum : headTag (⊥ : Semiformula LRA ℕ n) = 1 := rfl

@[simp] theorem headTag_rel {k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    headTag (.rel r v : Semiformula LRA ℕ n) = 2 := rfl

@[simp] theorem headTag_nrel {k : ℕ} (r : LRA.Rel k) (v : Fin k → Semiterm LRA ℕ n) :
    headTag (.nrel r v : Semiformula LRA ℕ n) = 3 := rfl

@[simp] theorem headTag_and (φ ψ : Semiformula LRA ℕ n) : headTag (φ ⋏ ψ) = 4 := rfl

@[simp] theorem headTag_or (φ ψ : Semiformula LRA ℕ n) : headTag (φ ⋎ ψ) = 5 := rfl

@[simp] theorem headTag_all (φ : Semiformula LRA ℕ (n + 1)) : headTag (∀¹ φ) = 6 := rfl

@[simp] theorem headTag_exs (φ : Semiformula LRA ℕ (n + 1)) : headTag (∃¹ φ) = 7 := rfl

@[simp] theorem headTag_memAt (ν : Lv) (t s : Semiterm LRA ℕ n) :
    headTag (memAt ν t s) = 2 := rfl

@[simp] theorem headTag_nmemAt (ν : Lv) (t s : Semiterm LRA ℕ n) :
    headTag (nmemAt ν t s) = 3 := rfl

/-- Formulas with different head tags are different. -/
theorem ne_of_headTag {φ ψ : Semiformula LRA ℕ n} (h : headTag φ ≠ headTag ψ) : φ ≠ ψ :=
  fun he => h (congrArg headTag he)

end HeadTag

/-! ### The reduction ordinal is symmetric

`redOrd β γ = (β ⊕ γ) ⊕ (β ⊕ γ)` and the natural sum is commutative.  This is
what lets the (Pr⁻)/(Pr) principal case be the (Pr)/(Pr⁻) one with the two sides
exchanged, rather than a second proof. -/

theorem redOrd_comm {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
    (β γ : O) : OrdinalNotation.redOrd β γ = OrdinalNotation.redOrd γ β := by
  show OrdinalNotation.sq (OrdinalNotation.nadd β γ)
    = OrdinalNotation.sq (OrdinalNotation.nadd γ β)
  rw [OrdinalNotation.nadd_comm]

namespace OmegaDerivableR

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]
variable {A : Literals LRA} {I : InstantiationR}

/-! ### Two structural lemmas the reduction lemma needs

`Omega/Calculus.lean` proves `drop_falsum` for the first-order calculus and
`ACAOmega/Calculus.lean` proves `identity_cases` for the second-order one; both
are restated here because `OmegaDerivableR` has two constructors neither of them
knows about, and because identity here is *atomic*. -/

/-- `⊥` is a passenger: no rule introduces it, so it can only have entered by
weakening and can be dropped again.  Needed because the cut formula `⊤` has
`∼⊤ = ⊥`, and the reduction lemma then has to discharge a sequent carrying
one. -/
theorem drop_falsum {ρ : Gamma0Note} :
    ∀ {α : O} {Γ : Sequent LRA}, OmegaDerivableR A I ρ α Γ →
      ∀ {Θ : Sequent LRA}, Γ ⊆ (⊥ : Proposition LRA) :: Θ →
        OmegaDerivableR A I ρ α Θ := by
  intro α Γ h
  induction h with
  | @atom α' φ hφ =>
      intro Θ hss
      have hm := hss List.mem_cons_self
      simp only [List.mem_cons] at hm
      rcases hm with hbot | hm
      · exact absurd hbot (Literals.ne_falsum hφ)
      · refine .contraction ?_ (.atom hφ)
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rw [hx]; exact hm
  | @identity α' k rl v =>
      intro Θ hss
      refine of_mem_identity rl v ?_ ?_
      · have := hss (show Semiformula.rel rl v ∈
          [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (ne_of_headTag (by simp))
        · exact hm
      · have := hss (show Semiformula.nrel rl v ∈
          [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (ne_of_headTag (by simp))
        · exact hm
  | @verum α' =>
      intro Θ hss
      refine of_mem_verum ?_
      have := hss (show (⊤ : Proposition LRA) ∈ [(⊤ : Proposition LRA)] by simp)
      simp only [List.mem_cons] at this
      rcases this with hbot | hm
      · exact absurd hbot (by simp)
      · exact hm
  | @or α' β' χ ψ Γ' hlt _ ih =>
      intro Θ hss
      have hmem : (χ ⋎ ψ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have key := ih (Θ := χ :: ψ :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · rcases hx with rfl | hx
          · tauto
          · have := hss (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto)
      exact drop_head (OmegaDerivableR.or hlt key) hmem
  | @and α' β' γ' χ ψ Γ' hb hc _ _ ihp ihq =>
      intro Θ hss
      have hmem : (χ ⋏ ψ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have hsub : ∀ ζ : Proposition LRA, (ζ :: Γ') ⊆ (⊥ : Proposition LRA) :: ζ :: Θ := by
        intro ζ x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto
      exact drop_head (OmegaDerivableR.and hb hc (ihp (hsub χ)) (ihq (hsub ψ))) hmem
  | @omegaRule α' χ Γ' f hf _ ih =>
      intro Θ hss
      have hmem : (∀¹ χ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      refine drop_head (OmegaDerivableR.omegaRule f hf (fun n => ih n ?_)) hmem
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · tauto
      · have := hss (List.mem_cons_of_mem _ hx)
        simp only [List.mem_cons] at this
        tauto
  | @exs α' β' χ Γ' n hlt _ ih =>
      intro Θ hss
      have hmem : (∃¹ χ) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (by simp)
        · exact hm
      have key := ih (Θ := I.inst χ n :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto)
      exact drop_head (OmegaDerivableR.exs n hlt key) hmem
  | contraction ss _ ih =>
      intro Θ hss
      exact ih (fun x hx => hss (ss hx))
  | @cut α' β' γ' χ Γ₁ Γ₂ hc hb1 hb2 _ _ ihp ihn =>
      intro Θ hss
      have kp := ihp (Θ := χ :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_append_left _ hx)
          simp only [List.mem_cons] at this
          tauto)
      have kn := ihn (Θ := ∼χ :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_append_right _ hx)
          simp only [List.mem_cons] at this
          tauto)
      refine OmegaDerivableR.contraction ?_ (OmegaDerivableR.cut hc hb1 hb2 kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto
  | @pr α' β' a n Γ' ha hlt _ ih =>
      intro Θ hss
      have hmem : memAt (lvl a) (I.num n) (I.num a) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (ne_of_headTag (by simp))
        · exact hm
      have key := ih (Θ := I.inst (body a) n :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto)
      exact drop_head (OmegaDerivableR.pr ha hlt key) hmem
  | @npr α' β' a n Γ' ha hlt _ ih =>
      intro Θ hss
      have hmem : nmemAt (lvl a) (I.num n) (I.num a) ∈ Θ := by
        have := hss List.mem_cons_self
        simp only [List.mem_cons] at this
        rcases this with hbot | hm
        · exact absurd hbot (ne_of_headTag (by simp))
        · exact hm
      have key := ih (Θ := ∼(I.inst (body a) n) :: Θ) (by
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hss (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto)
      exact drop_head (OmegaDerivableR.npr ha hlt key) hmem

/-- An **atomic** identity sequent inside a bigger one: either both members are
in the rest, or one of them is the distinguished formula and the other — which
is its negation — sits in the rest. -/
theorem identity_cases {k : ℕ} {rl : LRA.Rel k} {v : Fin k → SyntacticTerm LRA}
    {φ : Proposition LRA} {Θ : Sequent LRA}
    (hss : ([Semiformula.rel rl v, Semiformula.nrel rl v] : Sequent LRA) ⊆ φ :: Θ) :
    (Semiformula.rel rl v ∈ Θ ∧ Semiformula.nrel rl v ∈ Θ) ∨ ∼φ ∈ Θ := by
  have hp := hss (show Semiformula.rel rl v ∈
    [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
  have hn := hss (show Semiformula.nrel rl v ∈
    [Semiformula.rel rl v, Semiformula.nrel rl v] by simp)
  simp only [List.mem_cons] at hp hn
  rcases hp with rfl | hpΘ
  · rcases hn with h | hnΘ
    · exact absurd h (ne_of_headTag (by simp))
    · exact Or.inr (by simpa using hnΘ)
  · rcases hn with rfl | hnΘ
    · exact Or.inr (by simpa using hpΘ)
    · exact Or.inl ⟨hpΘ, hnΘ⟩

/-! ### The mirror of the (Pr)/(Pr⁻) principal case

`Ramified/ReductionProbe.lean` proves the case with the *positive* rule on the
left.  The left induction meets both orientations, and the second is the first
with the sides exchanged: `RedIHR` is symmetric under swapping `β` with `γ` and
`φ` with `∼φ`, and `redOrd` is symmetric outright (`redOrd_comm`). -/

/-- The (Pr⁻)/(Pr) principal case: the left derivation concludes the *negative*
set atom, the right one the positive. -/
theorem reduction_npr_principal {ρ : Gamma0Note} {s β γ β₀ γ₀ : O}
    (ih2 : RedIHR A I ρ s) (hs : OrdinalNotation.nadd β γ ≤ s)
    {a n : ℕ} (ha : Good a) (hr : rank (prAtom I a n) ≤ ρ)
    {Γ₁ Δ₁ Θ : Sequent LRA}
    (hβ₀ : β₀ < β) (hγ₀ : γ₀ < γ)
    (hL : OmegaDerivableR A I ρ β₀ (∼(I.inst (body a) n) :: Γ₁))
    (hΓ : Γ₁ ⊆ ∼(prAtom I a n) :: Θ)
    (hR : OmegaDerivableR A I ρ γ₀ (I.inst (body a) n :: Δ₁))
    (hΔ : Δ₁ ⊆ prAtom I a n :: Θ) :
    OmegaDerivableR A I ρ (OrdinalNotation.redOrd β γ) Θ := by
  rw [redOrd_comm]
  refine reduction_pr_principal ih2 ?_ ha hr hγ₀ hβ₀ hR hΔ hL hΓ
  rw [OrdinalNotation.nadd_comm]
  exact hs

/-- The mirror case as the dispatcher meets it: the right (Pr) inference carries
its own code and subject, and the atoms are matched by `prAtom_inj`. -/
theorem reduction_npr_principal_dispatch {ρ : Gamma0Note} {s β γ β₀ γ₀ : O}
    (ih2 : RedIHR A I ρ s) (hs : OrdinalNotation.nadd β γ ≤ s)
    {a n a' n' : ℕ} (ha : Good a) (hr : rank (prAtom I a n) ≤ ρ)
    (hmatch : memAt (lvl a') (I.num n') (I.num a') = prAtom I a n)
    {Γ₁ Δ₁ Θ : Sequent LRA}
    (hβ₀ : β₀ < β) (hγ₀ : γ₀ < γ)
    (hL : OmegaDerivableR A I ρ β₀ (∼(I.inst (body a) n) :: Γ₁))
    (hΓ : Γ₁ ⊆ ∼(prAtom I a n) :: Θ)
    (hR : OmegaDerivableR A I ρ γ₀ (I.inst (body a') n' :: Δ₁))
    (hΔ : Δ₁ ⊆ prAtom I a n :: Θ) :
    OmegaDerivableR A I ρ (OrdinalNotation.redOrd β γ) Θ := by
  obtain ⟨rfl, rfl⟩ := prAtom_inj hmatch.symm
  exact reduction_npr_principal ih2 hs ha hr hβ₀ hγ₀ hL hΓ hR hΔ

/-! ### The right induction -/

set_option maxHeartbeats 2000000 in
/-- **The right induction.**  Given the left derivation `hd` of a sequent inside
`φ :: Θ`, and a handler for each rule that could be principal for `∼φ` on the
right, reduce against any right derivation of a sequent inside `∼φ :: Θ`.

Seven handlers, one per rule that can put the principal formula at the head: the
five of `Omega/Reduction.lean` plus the two predicator rules.  Doing the right
induction once is what keeps the cost of eleven constructors linear rather than
quadratic — `ACAOmega/Reduction.lean` is 1368 lines for twelve constructors
where `Omega/Reduction.lean` is 1724 for nine. -/
theorem reduction_right {ρ : Gamma0Note} {s α : O} (ih2 : RedIHR A I ρ s)
    {Γ₀ Θ : Sequent LRA} {φ : Proposition LRA}
    (hd : OmegaDerivableR A I ρ α Γ₀) (hss : Γ₀ ⊆ φ :: Θ) (hr : rank φ ≤ ρ)
    (hAtom : ∀ {δ : O} {χ : Proposition LRA}, A.T χ → χ = ∼φ →
      OrdinalNotation.nadd α δ ≤ s → OmegaDerivableR A I ρ (OrdinalNotation.redOrd α δ) Θ)
    (hOr : ∀ {δ δ₀ : O} {ψ₁ ψ₂ : Proposition LRA} {Δ₁ : Sequent LRA},
      ψ₁ ⋎ ψ₂ = ∼φ → δ₀ < δ → OrdinalNotation.nadd α δ ≤ s →
      OmegaDerivableR A I ρ δ₀ (ψ₁ :: ψ₂ :: Δ₁) → Δ₁ ⊆ ∼φ :: Θ →
      OmegaDerivableR A I ρ (OrdinalNotation.redOrd α δ) Θ)
    (hAnd : ∀ {δ δ₀ δ₁ : O} {ψ₁ ψ₂ : Proposition LRA} {Δ₁ : Sequent LRA},
      ψ₁ ⋏ ψ₂ = ∼φ → δ₀ < δ → δ₁ < δ → OrdinalNotation.nadd α δ ≤ s →
      OmegaDerivableR A I ρ δ₀ (ψ₁ :: Δ₁) → OmegaDerivableR A I ρ δ₁ (ψ₂ :: Δ₁) →
      Δ₁ ⊆ ∼φ :: Θ →
      OmegaDerivableR A I ρ (OrdinalNotation.redOrd α δ) Θ)
    (hOmega : ∀ {δ : O} {ψ : Semiproposition LRA 1} {Δ₁ : Sequent LRA} {f : ℕ → O},
      (∀¹ ψ) = ∼φ → (∀ n, f n < δ) → OrdinalNotation.nadd α δ ≤ s →
      (∀ n, OmegaDerivableR A I ρ (f n) (I.inst ψ n :: Δ₁)) → Δ₁ ⊆ ∼φ :: Θ →
      OmegaDerivableR A I ρ (OrdinalNotation.redOrd α δ) Θ)
    (hExs : ∀ {δ δ₀ : O} {ψ : Semiproposition LRA 1} {Δ₁ : Sequent LRA} {n : ℕ},
      (∃¹ ψ) = ∼φ → δ₀ < δ → OrdinalNotation.nadd α δ ≤ s →
      OmegaDerivableR A I ρ δ₀ (I.inst ψ n :: Δ₁) → Δ₁ ⊆ ∼φ :: Θ →
      OmegaDerivableR A I ρ (OrdinalNotation.redOrd α δ) Θ)
    (hPr : ∀ {δ δ₀ : O} {a n : ℕ} {Δ₁ : Sequent LRA},
      Good a → memAt (lvl a) (I.num n) (I.num a) = ∼φ → δ₀ < δ →
      OrdinalNotation.nadd α δ ≤ s →
      OmegaDerivableR A I ρ δ₀ (I.inst (body a) n :: Δ₁) → Δ₁ ⊆ ∼φ :: Θ →
      OmegaDerivableR A I ρ (OrdinalNotation.redOrd α δ) Θ)
    (hNpr : ∀ {δ δ₀ : O} {a n : ℕ} {Δ₁ : Sequent LRA},
      Good a → nmemAt (lvl a) (I.num n) (I.num a) = ∼φ → δ₀ < δ →
      OrdinalNotation.nadd α δ ≤ s →
      OmegaDerivableR A I ρ δ₀ (∼(I.inst (body a) n) :: Δ₁) → Δ₁ ⊆ ∼φ :: Θ →
      OmegaDerivableR A I ρ (OrdinalNotation.redOrd α δ) Θ) :
    ∀ {δ : O} {Δ₀ : Sequent LRA}, OmegaDerivableR A I ρ δ Δ₀ →
      OrdinalNotation.nadd α δ ≤ s → Δ₀ ⊆ ∼φ :: Θ →
        OmegaDerivableR A I ρ (OrdinalNotation.redOrd α δ) Θ := by
  have hsubL : ∀ ζ : Proposition LRA, Γ₀ ⊆ φ :: ζ :: Θ := by
    intro ζ x hx
    have := hss hx
    simp only [List.mem_cons] at this ⊢
    tauto
  have hle : ∀ δ : O, α ≤ OrdinalNotation.redOrd α δ := fun δ =>
    le_trans (OrdinalNotation.le_nadd_left α δ) (OrdinalNotation.le_nadd_left _ _)
  intro δ Δ₀ he
  induction he with
  | @atom δ' χ hχ =>
      intro hs hssR
      have h := hssR List.mem_cons_self
      simp only [List.mem_cons] at h
      rcases h with h | h
      · exact hAtom hχ h hs
      · refine .contraction ?_ (.atom hχ)
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rw [hx]; exact h
  | @identity δ' k rl v =>
      intro _ hssR
      rcases identity_cases hssR with ⟨h₁, h₂⟩ | h
      · exact of_mem_identity rl v h₁ h₂
      · have h' : φ ∈ Θ := by simpa using h
        refine (OmegaDerivableR.contraction ?_ hd).mono_ord (hle δ')
        intro x hx
        have := hss hx
        simp only [List.mem_cons] at this
        rcases this with rfl | hm
        · exact h'
        · exact hm
  | @verum δ' =>
      intro _ hssR
      have h := hssR (show (⊤ : Proposition LRA) ∈ [(⊤ : Proposition LRA)] by simp)
      simp only [List.mem_cons] at h
      rcases h with h | h
      · have hφ : φ = ⊥ := by
          have := congrArg (fun χ => ∼χ) h
          simpa using this.symm
        subst hφ
        exact (drop_falsum hd hss).mono_ord (hle δ')
      · exact of_mem_verum h
  | @contraction δ' Δ' Δ ss _ ih =>
      intro hs hssR
      exact ih hs (fun x hx => hssR (ss hx))
  | @or δ' δ₀ ψ₁ ψ₂ Δ₁ hlt heP _ =>
      intro hs hssR
      by_cases hcase : ψ₁ ⋎ ψ₂ = ∼φ
      · exact hOr hcase hlt hs heP (fun x hx => hssR (List.mem_cons_of_mem _ hx))
      · have hmem : (ψ₁ ⋎ ψ₂) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
          hd hr (Θ := ψ₁ :: ψ₂ :: Θ)
          (by
            intro x hx
            have := hss hx
            simp only [List.mem_cons] at this ⊢
            tauto)
          heP
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · rcases hx with rfl | hx
              · tauto
              · have := hssR (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
        exact drop_head (.or (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @and δ' δ₀ δ₁ ψ₁ ψ₂ Δ₁ hlt₀ hlt₁ heP heQ _ _ =>
      intro hs hssR
      by_cases hcase : ψ₁ ⋏ ψ₂ = ∼φ
      · exact hAnd hcase hlt₀ hlt₁ hs heP heQ (fun x hx => hssR (List.mem_cons_of_mem _ hx))
      · have hmem : (ψ₁ ⋏ ψ₂) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have hsubR : ∀ ζ : Proposition LRA, ζ :: Δ₁ ⊆ ∼φ :: ζ :: Θ := by
          intro ζ x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_cons_of_mem _ hx)
            simp only [List.mem_cons] at this
            tauto
        have kp := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs)
          hd hr (Θ := ψ₁ :: Θ) (hsubL ψ₁) heP (hsubR ψ₁)
        have kq := ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs)
          hd hr (Θ := ψ₂ :: Θ) (hsubL ψ₂) heQ (hsubR ψ₂)
        exact drop_head
          (.and (OrdinalNotation.redOrd_lt_right α hlt₀)
            (OrdinalNotation.redOrd_lt_right α hlt₁) kp kq) hmem
  | @omegaRule δ' ψ Δ₁ f hf heP _ =>
      intro hs hssR
      by_cases hcase : (∀¹ ψ) = ∼φ
      · exact hOmega hcase hf hs heP (fun x hx => hssR (List.mem_cons_of_mem _ hx))
      · have hmem : (∀¹ ψ) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        refine drop_head
          (.omegaRule (fun n => OrdinalNotation.redOrd α (f n))
            (fun n => OrdinalNotation.redOrd_lt_right α (hf n)) (fun n => ?_)) hmem
        refine ih2 α (f n) (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α (hf n)) hs)
          hd hr (Θ := I.inst ψ n :: Θ) (hsubL _) (heP n) ?_
        intro x hx
        simp only [List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · have := hssR (List.mem_cons_of_mem _ hx)
          simp only [List.mem_cons] at this
          tauto
  | @exs δ' δ₀ ψ Δ₁ n hlt heP _ =>
      intro hs hssR
      by_cases hcase : (∃¹ ψ) = ∼φ
      · exact hExs hcase hlt hs heP (fun x hx => hssR (List.mem_cons_of_mem _ hx))
      · have hmem : (∃¹ ψ) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
          hd hr (Θ := I.inst ψ n :: Θ) (hsubL _) heP
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hssR (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto)
        exact drop_head (.exs n (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @cut δ' δ₀ δ₁ ψ Δ₁ Δ₂ hc hlt₀ hlt₁ hpp hnn _ _ =>
      intro hs hssR
      have kp := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₀) hs)
        hd hr (Θ := ψ :: Θ) (hsubL ψ) hpp
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_left _ hx)
            simp only [List.mem_cons] at this
            tauto)
      have kn := ih2 α δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt₁) hs)
        hd hr (Θ := ∼ψ :: Θ) (hsubL (∼ψ)) hnn
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · have := hssR (List.mem_append_right _ hx)
            simp only [List.mem_cons] at this
            tauto)
      refine .contraction ?_
        (.cut hc (OrdinalNotation.redOrd_lt_right α hlt₀)
          (OrdinalNotation.redOrd_lt_right α hlt₁) kp kn)
      intro x hx
      simp only [List.mem_append] at hx
      tauto
  | @pr δ' δ₀ a n Δ₁ ha hlt heP _ =>
      intro hs hssR
      by_cases hcase : memAt (lvl a) (I.num n) (I.num a) = ∼φ
      · exact hPr ha hcase hlt hs heP (fun x hx => hssR (List.mem_cons_of_mem _ hx))
      · have hmem : memAt (lvl a) (I.num n) (I.num a) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
          hd hr (Θ := I.inst (body a) n :: Θ) (hsubL _) heP
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hssR (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto)
        exact drop_head (.pr ha (OrdinalNotation.redOrd_lt_right α hlt) key) hmem
  | @npr δ' δ₀ a n Δ₁ ha hlt heP _ =>
      intro hs hssR
      by_cases hcase : nmemAt (lvl a) (I.num n) (I.num a) = ∼φ
      · exact hNpr ha hcase hlt hs heP (fun x hx => hssR (List.mem_cons_of_mem _ hx))
      · have hmem : nmemAt (lvl a) (I.num n) (I.num a) ∈ Θ := by
          have h := hssR List.mem_cons_self
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact absurd h hcase
          · exact h
        have key := ih2 α δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α hlt) hs)
          hd hr (Θ := ∼(I.inst (body a) n) :: Θ) (hsubL _) heP
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hssR (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto)
        exact drop_head (.npr ha (OrdinalNotation.redOrd_lt_right α hlt) key) hmem

/-! ### The left induction -/

set_option maxHeartbeats 4000000 in
/-- The reduction lemma in the form the well-founded recursion needs. -/
theorem reduction_aux (hA : MemFree A) {ρ : Gamma0Note} :
    ∀ (s β γ : O), OrdinalNotation.nadd β γ ≤ s →
      ∀ {Γ₀ : Sequent LRA}, OmegaDerivableR A I ρ β Γ₀ →
        ∀ {φ : Proposition LRA}, rank φ ≤ ρ →
        ∀ {Θ Δ₀ : Sequent LRA}, Γ₀ ⊆ φ :: Θ →
          OmegaDerivableR A I ρ γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ →
            OmegaDerivableR A I ρ (OrdinalNotation.redOrd β γ) Θ := by
  intro s
  induction s using WellFoundedLT.induction with
  | _ s ihs =>
    intro β γ hbg
    have ih2 : RedIHR A I ρ (OrdinalNotation.nadd β γ) := fun β' γ' h =>
      ihs (OrdinalNotation.nadd β' γ') (lt_of_lt_of_le h hbg) β' γ' le_rfl
    suffices K : ∀ (α : O) {Γ₀ : Sequent LRA}, OmegaDerivableR A I ρ α Γ₀ →
        OrdinalNotation.nadd α γ ≤ OrdinalNotation.nadd β γ →
        ∀ {φ : Proposition LRA}, rank φ ≤ ρ →
        ∀ {Θ Δ₀ : Sequent LRA}, Γ₀ ⊆ φ :: Θ →
          OmegaDerivableR A I ρ γ Δ₀ → Δ₀ ⊆ ∼φ :: Θ →
            OmegaDerivableR A I ρ (OrdinalNotation.redOrd α γ) Θ by
      intro Γ₀ hd φ hφ Θ Δ₀ hss he hst
      exact K β hd le_rfl hφ hss he hst
    intro α Γ₀ hd
    induction hd with
    | @atom α' ψ hψ =>
        intro hs φ hφ Θ Δ₀ hss he hst
        have h := hss List.mem_cons_self
        simp only [List.mem_cons] at h
        rcases h with rfl | hΘ
        · refine reduction_right ih2 (.atom hψ) hss hφ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he hs hst
          · intro δ ξ hξ hξe _
            exact absurd (hξe ▸ hξ) (fun h => A.consistent ψ hψ h)
          · intro δ δ₀ ψ₁ ψ₂ Δ₁ h
            exact absurd h.symm (Literals.neg_ne_or hψ)
          · intro δ δ₀ δ₁ ψ₁ ψ₂ Δ₁ h
            exact absurd h.symm (Literals.neg_ne_and hψ)
          · intro δ ξ Δ₁ f h
            exact absurd h.symm (Literals.neg_ne_all hψ)
          · intro δ δ₀ ξ Δ₁ m h
            exact absurd h.symm (Literals.neg_ne_exs hψ)
          · intro δ δ₀ a₁ n₁ Δ₁ _ h
            exact absurd h.symm (MemFree.neg_ne_memAt hA hψ _ _ _)
          · intro δ δ₀ a₁ n₁ Δ₁ _ h
            exact absurd h.symm (MemFree.neg_ne_nmemAt hA hψ _ _ _)
        · refine .contraction ?_ (.atom hψ)
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rw [hx]; exact hΘ
    | @contraction α' Δ' Γ' ss _ ihprem =>
        intro hs φ hφ Θ Δ₀ hss he hst
        exact ihprem hs hφ (fun x hx => hss (ss hx)) he hst
    | @identity α' k rl v =>
        intro _ φ _ Θ Δ₀ hss he hst
        have hle : γ ≤ OrdinalNotation.redOrd α' γ :=
          le_trans (OrdinalNotation.le_nadd_right α' γ) (OrdinalNotation.le_nadd_left _ _)
        rcases identity_cases hss with ⟨h₁, h₂⟩ | h
        · exact of_mem_identity rl v h₁ h₂
        · refine (OmegaDerivableR.contraction ?_ he).mono_ord hle
          intro x hx
          have := hst hx
          simp only [List.mem_cons] at this
          rcases this with rfl | hm
          · exact h
          · exact hm
    | @verum α' =>
        intro _ φ _ Θ Δ₀ hss he hst
        have h := hss (show (⊤ : Proposition LRA) ∈ [(⊤ : Proposition LRA)] by simp)
        simp only [List.mem_cons] at h
        rcases h with hφ | hΘ
        · have hbot : Δ₀ ⊆ (⊥ : Proposition LRA) :: Θ := by
            intro x hx
            have := hst hx
            simp only [List.mem_cons] at this ⊢
            rcases this with rfl | hm
            · left; rw [← hφ]; simp
            · tauto
          exact (drop_falsum he hbot).mono_ord
            (le_trans (OrdinalNotation.le_nadd_right α' γ) (OrdinalNotation.le_nadd_left _ _))
        · exact of_mem_verum hΘ
    | @or α' α₀ χ ψ Γ' hb hprem ihp =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (χ ⋎ ψ) = φ
        · subst hcase
          have hd : OmegaDerivableR A I ρ α' ((χ ⋎ ψ) :: Γ') := .or hb hprem
          have hsubL : ∀ ζ : Proposition LRA, ((χ ⋎ ψ) :: Γ') ⊆ (χ ⋎ ψ) :: ζ :: Θ := by
            intro ζ x hx
            have := hss hx
            simp only [List.mem_cons] at this ⊢
            tauto
          have hmaxρ : OrdinalNotation.succ (max (rank χ) (rank ψ)) ≤ ρ := by
            rw [← rank_or]; exact hφ
          have hcχ : rank χ < ρ :=
            lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) (OrdinalNotation.lt_succ _)) hmaxρ
          have hcψ : rank ψ < ρ :=
            lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) (OrdinalNotation.lt_succ _)) hmaxρ
          refine reduction_right ih2 hd hss hφ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he hs hst
          · intro δ ξ hξ hξe _
            exact absurd hξe (Literals.ne_and (ψ₁ := ∼χ) (ψ₂ := ∼ψ) hξ)
          · intro δ δ₀ ψ₁ ψ₂ Δ₁ h
            exact absurd h (ne_of_headTag (by simp))
          · -- PRINCIPAL
            intro δ δ₀ δ₁ ψ₁ ψ₂ Δ₁ heq hlt₀ hlt₁ hs' heP heQ hssR
            have heq' : ψ₁ ⋏ ψ₂ = ((∼χ) ⋏ (∼ψ)) := heq
            obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp heq'
            have hA₀ : OmegaDerivableR A I ρ (OrdinalNotation.redOrd α₀ δ) (χ :: ψ :: Θ) :=
              ih2 α₀ δ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ hb) hs') hprem hφ
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · rcases hx with rfl | hx
                    · tauto
                    · have := hss (List.mem_cons_of_mem _ hx)
                      simp only [List.mem_cons] at this
                      tauto)
                (OmegaDerivableR.and hlt₀ hlt₁ heP heQ)
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · exact Or.inl rfl
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
            have hB : OmegaDerivableR A I ρ (OrdinalNotation.redOrd α' δ₀) ((∼χ) :: Θ) :=
              ih2 α' δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α' hlt₀) hs') hd hφ
                (hsubL (∼χ)) heP
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
            have hC : OmegaDerivableR A I ρ (OrdinalNotation.redOrd α' δ₁) ((∼ψ) :: Θ) :=
              ih2 α' δ₁ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α' hlt₁) hs') hd hφ
                (hsubL (∼ψ)) heQ
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
            have h₀ : OrdinalNotation.nadd α₀ δ < OrdinalNotation.nadd α' δ :=
              OrdinalNotation.nadd_lt_nadd_left δ hb
            have h₁ : OrdinalNotation.nadd α' δ₁ < OrdinalNotation.nadd α' δ :=
              OrdinalNotation.nadd_lt_nadd_right α' hlt₁
            have hA' : OmegaDerivableR A I ρ (OrdinalNotation.redOrd α₀ δ) (ψ :: χ :: Θ) := by
              refine OmegaDerivableR.contraction ?_ hA₀
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              tauto
            have step : OmegaDerivableR A I ρ
                (OrdinalNotation.mid (OrdinalNotation.nadd α₀ δ) (OrdinalNotation.nadd α' δ₁)
                  (OrdinalNotation.nadd α' δ))
                (χ :: Θ) := by
              refine OmegaDerivableR.contraction ?_
                (OmegaDerivableR.cut hcψ (OrdinalNotation.sq_lt_mid_left h₀ h₁)
                  (OrdinalNotation.sq_lt_mid_right h₀ h₁) hA' hC)
              intro x hx
              simp only [List.cons_append, List.mem_cons, List.mem_append] at hx ⊢
              tauto
            refine OmegaDerivableR.contraction ?_
              (OmegaDerivableR.cut hcχ (OrdinalNotation.mid_lt_sq h₀ h₁)
                (OrdinalNotation.redOrd_lt_right α' hlt₀) step hB)
            intro x hx
            simp only [List.mem_append] at hx
            tauto
          · intro δ ξ Δ₁ f h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ ξ Δ₁ m h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ a₁ n₁ Δ₁ _ h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ a₁ n₁ Δ₁ _ h
            exact absurd h (ne_of_headTag (by simp))
        · have hmem : (χ ⋎ ψ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          have hs' : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb) hs)
          have key := ihp hs' hφ (Θ := χ :: ψ :: Θ)
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · rcases hx with rfl | hx
                · tauto
                · have := hss (List.mem_cons_of_mem _ hx)
                  simp only [List.mem_cons] at this
                  tauto)
            he
            (by
              intro x hx
              have := hst hx
              simp only [List.mem_cons] at this ⊢
              tauto)
          exact drop_head (.or (OrdinalNotation.redOrd_lt_left γ hb) key) hmem
    | @and α' α₀ α₁ χ ψ Γ' hb1 hb2 hp hq ihp ihq =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (χ ⋏ ψ) = φ
        · subst hcase
          have hd : OmegaDerivableR A I ρ α' ((χ ⋏ ψ) :: Γ') := .and hb1 hb2 hp hq
          have hmaxρ : OrdinalNotation.succ (max (rank χ) (rank ψ)) ≤ ρ := by
            rw [← rank_and]; exact hφ
          have hcχ : rank χ < ρ :=
            lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) (OrdinalNotation.lt_succ _)) hmaxρ
          have hcψ : rank ψ < ρ :=
            lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) (OrdinalNotation.lt_succ _)) hmaxρ
          refine reduction_right ih2 hd hss hφ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he hs hst
          · intro δ ξ hξ hξe _
            exact absurd hξe (Literals.ne_or (ψ₁ := ∼χ) (ψ₂ := ∼ψ) hξ)
          · -- PRINCIPAL
            intro δ δ₀ ψ₁ ψ₂ Δ₁ heq hlt hs' heP hssR
            have heq' : ψ₁ ⋎ ψ₂ = ((∼χ) ⋎ (∼ψ)) := heq
            obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp heq'
            have hsubR : ∀ ζ : Proposition LRA,
                (((∼χ) ⋎ (∼ψ)) :: Δ₁) ⊆ ∼(χ ⋏ ψ) :: ζ :: Θ := by
              intro ζ x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · exact Or.inl rfl
              · have := hssR hx
                simp only [List.mem_cons] at this
                tauto
            have hsL : (χ :: Γ') ⊆ (χ ⋏ ψ) :: χ :: Θ := by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hss (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto
            have hsL' : (ψ :: Γ') ⊆ (χ ⋏ ψ) :: ψ :: Θ := by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hss (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto
            have hA₀ : OmegaDerivableR A I ρ (OrdinalNotation.redOrd α₀ δ) (χ :: Θ) :=
              ih2 α₀ δ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ hb1) hs') hp hφ
                hsL (OmegaDerivableR.or hlt heP) (hsubR χ)
            have hA₁ : OmegaDerivableR A I ρ (OrdinalNotation.redOrd α₁ δ) (ψ :: Θ) :=
              ih2 α₁ δ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ hb2) hs') hq hφ
                hsL' (OmegaDerivableR.or hlt heP) (hsubR ψ)
            have hB : OmegaDerivableR A I ρ (OrdinalNotation.redOrd α' δ₀)
                ((∼χ) :: (∼ψ) :: Θ) :=
              ih2 α' δ₀ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α' hlt) hs') hd hφ
                (by
                  intro x hx
                  have := hss hx
                  simp only [List.mem_cons] at this ⊢
                  tauto)
                heP
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · rcases hx with rfl | hx
                    · tauto
                    · have := hssR hx
                      simp only [List.mem_cons] at this
                      tauto)
            have h₀ : OrdinalNotation.nadd α₀ δ < OrdinalNotation.nadd α' δ :=
              OrdinalNotation.nadd_lt_nadd_left δ hb1
            have hBs : OrdinalNotation.nadd α' δ₀ < OrdinalNotation.nadd α' δ :=
              OrdinalNotation.nadd_lt_nadd_right α' hlt
            have step : OmegaDerivableR A I ρ
                (OrdinalNotation.mid (OrdinalNotation.nadd α₀ δ) (OrdinalNotation.nadd α' δ₀)
                  (OrdinalNotation.nadd α' δ))
                ((∼ψ) :: Θ) := by
              refine OmegaDerivableR.contraction ?_
                (OmegaDerivableR.cut hcχ (OrdinalNotation.sq_lt_mid_left h₀ hBs)
                  (OrdinalNotation.sq_lt_mid_right h₀ hBs) hA₀ hB)
              intro x hx
              simp only [List.mem_append, List.mem_cons] at hx ⊢
              tauto
            refine OmegaDerivableR.contraction ?_
              (OmegaDerivableR.cut hcψ (OrdinalNotation.redOrd_lt_left δ hb2)
                (OrdinalNotation.mid_lt_sq h₀ hBs) hA₁ step)
            intro x hx
            simp only [List.mem_append] at hx
            tauto
          · intro δ δ₀ δ₁ ψ₁ ψ₂ Δ₁ h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ ξ Δ₁ f h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ ξ Δ₁ m h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ a₁ n₁ Δ₁ _ h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ a₁ n₁ Δ₁ _ h
            exact absurd h (ne_of_headTag (by simp))
        · have hmem : (χ ⋏ ψ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          have hs1 : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb1) hs)
          have hs2 : OrdinalNotation.nadd α₁ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb2) hs)
          have hsubL : ∀ ζ : Proposition LRA, (ζ :: Γ') ⊆ φ :: ζ :: Θ := by
            intro ζ x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hss (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto
          have hsubR : ∀ ζ : Proposition LRA, Δ₀ ⊆ ∼φ :: ζ :: Θ := by
            intro ζ x hx
            have := hst hx
            simp only [List.mem_cons] at this ⊢
            tauto
          have kp := ihp hs1 hφ (Θ := χ :: Θ) (hsubL χ) he (hsubR χ)
          have kq := ihq hs2 hφ (Θ := ψ :: Θ) (hsubL ψ) he (hsubR ψ)
          exact drop_head
            (.and (OrdinalNotation.redOrd_lt_left γ hb1)
              (OrdinalNotation.redOrd_lt_left γ hb2) kp kq) hmem
    | @omegaRule α' χ Γ' f hf hprem ihp =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (∀¹ χ) = φ
        · subst hcase
          have hd : OmegaDerivableR A I ρ α' ((∀¹ χ) :: Γ') := .omegaRule f hf hprem
          refine reduction_right ih2 hd hss hφ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he hs hst
          · intro δ ξ hξ hξe _
            exact absurd hξe (Literals.ne_exs (ψ := ∼χ) hξ)
          · intro δ δ₀ ψ₁ ψ₂ Δ₁ h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ δ₁ ψ₁ ψ₂ Δ₁ h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ ξ Δ₁ g h
            exact absurd h (ne_of_headTag (by simp))
          · -- PRINCIPAL: the witness is the existential side's `n`.
            intro δ δ₀ ξ Δ₁ n heq hlt hs' heP hssR
            obtain rfl : ξ = ∼χ := by simpa using heq
            have hcχ : rank (I.inst χ n) < ρ :=
              lt_of_le_of_lt (I.rank_inst_le χ n) (lt_of_lt_of_le (OrdinalNotation.lt_succ _) hφ)
            have hA₀ : OmegaDerivableR A I ρ (OrdinalNotation.redOrd (f n) δ)
                (I.inst χ n :: Θ) :=
              ih2 (f n) δ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ (hf n)) hs')
                (hprem n) hφ
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hss (List.mem_cons_of_mem _ hx)
                    simp only [List.mem_cons] at this
                    tauto)
                (OmegaDerivableR.exs n hlt heP)
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · exact Or.inl rfl
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
            have hBsub : OmegaDerivableR A I ρ δ₀ ((∼I.inst χ n) :: Δ₁) := by
              simpa using heP
            have hswap : OrdinalNotation.nadd δ₀ α' < OrdinalNotation.nadd β γ := by
              rw [OrdinalNotation.nadd_comm]
              exact lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α' hlt) hs'
            have hrneg : rank (∼(∀¹ χ) : Proposition LRA) ≤ ρ := by simpa using hφ
            have hB : OmegaDerivableR A I ρ (OrdinalNotation.redOrd δ₀ α')
                ((∼I.inst χ n) :: Θ) :=
              ih2 δ₀ α' hswap hBsub hrneg
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
                hd
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · left; simp
                  · have := hss (List.mem_cons_of_mem _ hx)
                    simp only [List.mem_cons] at this
                    rcases this with rfl | hm
                    · left; simp
                    · tauto)
            have hBlt : OrdinalNotation.redOrd δ₀ α' < OrdinalNotation.redOrd α' δ := by
              have hlt' : OrdinalNotation.nadd δ₀ α' < OrdinalNotation.nadd α' δ := by
                rw [OrdinalNotation.nadd_comm]
                exact OrdinalNotation.nadd_lt_nadd_right α' hlt
              exact OrdinalNotation.sq_lt_sq hlt'
            refine OmegaDerivableR.contraction ?_
              (OmegaDerivableR.cut hcχ (OrdinalNotation.redOrd_lt_left δ (hf n)) hBlt hA₀ hB)
            intro x hx
            simp only [List.mem_append] at hx
            tauto
          · intro δ δ₀ a₁ n₁ Δ₁ _ h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ a₁ n₁ Δ₁ _ h
            exact absurd h (ne_of_headTag (by simp))
        · have hmem : (∀¹ χ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          refine drop_head
            (.omegaRule (fun n => OrdinalNotation.redOrd (f n) γ)
              (fun n => OrdinalNotation.redOrd_lt_left γ (hf n)) (fun n => ?_)) hmem
          refine ihp n (le_of_lt (lt_of_lt_of_le
            (OrdinalNotation.nadd_lt_nadd_left γ (hf n)) hs)) hφ (Θ := I.inst χ n :: Θ) ?_ he ?_
          · intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hss (List.mem_cons_of_mem _ hx)
              simp only [List.mem_cons] at this
              tauto
          · intro x hx
            have := hst hx
            simp only [List.mem_cons] at this ⊢
            tauto
    | @exs α' α₀ χ Γ' n₀ hb hprem ihp =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : (∃¹ χ) = φ
        · subst hcase
          have hd : OmegaDerivableR A I ρ α' ((∃¹ χ) :: Γ') := .exs n₀ hb hprem
          refine reduction_right ih2 hd hss hφ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he hs hst
          · intro δ ξ hξ hξe _
            exact absurd hξe (Literals.ne_all (ψ := ∼χ) hξ)
          · intro δ δ₀ ψ₁ ψ₂ Δ₁ h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ δ₁ ψ₁ ψ₂ Δ₁ h
            exact absurd h (ne_of_headTag (by simp))
          · -- PRINCIPAL: the ω-rule on the right has a premise at `n₀`.
            intro δ ξ Δ₁ f heq hf hs' heP hssR
            obtain rfl : ξ = ∼χ := by simpa using heq
            have hcχ : rank (I.inst χ n₀) < ρ :=
              lt_of_le_of_lt (I.rank_inst_le χ n₀) (lt_of_lt_of_le (OrdinalNotation.lt_succ _) hφ)
            have hA₀ : OmegaDerivableR A I ρ (OrdinalNotation.redOrd α₀ δ)
                (I.inst χ n₀ :: Θ) :=
              ih2 α₀ δ (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left δ hb) hs') hprem hφ
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hss (List.mem_cons_of_mem _ hx)
                    simp only [List.mem_cons] at this
                    tauto)
                (OmegaDerivableR.omegaRule f hf heP)
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · exact Or.inl rfl
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
            have hBsub : OmegaDerivableR A I ρ (f n₀) ((∼I.inst χ n₀) :: Δ₁) := by
              simpa using heP n₀
            have hswap : OrdinalNotation.nadd (f n₀) α' < OrdinalNotation.nadd β γ := by
              rw [OrdinalNotation.nadd_comm]
              exact lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_right α' (hf n₀)) hs'
            have hrneg : rank (∼(∃¹ χ) : Proposition LRA) ≤ ρ := by simpa using hφ
            have hB : OmegaDerivableR A I ρ (OrdinalNotation.redOrd (f n₀) α')
                ((∼I.inst χ n₀) :: Θ) :=
              ih2 (f n₀) α' hswap hBsub hrneg
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · tauto
                  · have := hssR hx
                    simp only [List.mem_cons] at this
                    tauto)
                hd
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | hx
                  · left; simp
                  · have := hss (List.mem_cons_of_mem _ hx)
                    simp only [List.mem_cons] at this
                    rcases this with rfl | hm
                    · left; simp
                    · tauto)
            have hBlt : OrdinalNotation.redOrd (f n₀) α' < OrdinalNotation.redOrd α' δ := by
              have hlt' : OrdinalNotation.nadd (f n₀) α' < OrdinalNotation.nadd α' δ := by
                rw [OrdinalNotation.nadd_comm]
                exact OrdinalNotation.nadd_lt_nadd_right α' (hf n₀)
              exact OrdinalNotation.sq_lt_sq hlt'
            refine OmegaDerivableR.contraction ?_
              (OmegaDerivableR.cut hcχ (OrdinalNotation.redOrd_lt_left δ hb) hBlt hA₀ hB)
            intro x hx
            simp only [List.mem_append] at hx
            tauto
          · intro δ δ₀ ξ Δ₁ m h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ a₁ n₁ Δ₁ _ h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ a₁ n₁ Δ₁ _ h
            exact absurd h (ne_of_headTag (by simp))
        · have hmem : (∃¹ χ) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          have hs' : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb) hs)
          have key := ihp hs' hφ (Θ := I.inst χ n₀ :: Θ)
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hss (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
            he
            (by
              intro x hx
              have := hst hx
              simp only [List.mem_cons] at this ⊢
              tauto)
          exact drop_head (.exs n₀ (OrdinalNotation.redOrd_lt_left γ hb) key) hmem
    | @pr α' α₀ a₀ n₀ Γ' ha hb hprem ihp =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : memAt (lvl a₀) (I.num n₀) (I.num a₀) = φ
        · subst hcase
          have hd : OmegaDerivableR A I ρ α'
              (memAt (lvl a₀) (I.num n₀) (I.num a₀) :: Γ') := .pr ha hb hprem
          refine reduction_right ih2 hd hss hφ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he hs hst
          · intro δ ξ hξ hξe _
            exact absurd hξe (MemFree.ne_nmemAt hA hξ _ _ _)
          · intro δ δ₀ ψ₁ ψ₂ Δ₁ h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ δ₁ ψ₁ ψ₂ Δ₁ h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ ξ Δ₁ g h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ ξ Δ₁ m h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ a₁ n₁ Δ₁ _ h
            exact absurd h (ne_of_headTag (by simp))
          · -- PRINCIPAL: (Pr) against (Pr⁻) on the same atom.
            intro δ δ₀ a₁ n₁ Δ₁ _ hmatch hlt hs' heP hssR
            exact reduction_pr_principal_dispatch ih2 hs' ha hφ hmatch hb hlt hprem
              (fun x hx => hss (List.mem_cons_of_mem _ hx)) heP hssR
        · have hmem : memAt (lvl a₀) (I.num n₀) (I.num a₀) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          have hs' : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb) hs)
          have key := ihp hs' hφ (Θ := I.inst (body a₀) n₀ :: Θ)
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hss (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
            he
            (by
              intro x hx
              have := hst hx
              simp only [List.mem_cons] at this ⊢
              tauto)
          exact drop_head (.pr ha (OrdinalNotation.redOrd_lt_left γ hb) key) hmem
    | @npr α' α₀ a₀ n₀ Γ' ha hb hprem ihp =>
        intro hs φ hφ Θ Δ₀ hss he hst
        by_cases hcase : nmemAt (lvl a₀) (I.num n₀) (I.num a₀) = φ
        · subst hcase
          have hd : OmegaDerivableR A I ρ α'
              (nmemAt (lvl a₀) (I.num n₀) (I.num a₀) :: Γ') := .npr ha hb hprem
          refine reduction_right ih2 hd hss hφ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he hs hst
          · intro δ ξ hξ hξe _
            exact absurd hξe (MemFree.ne_memAt hA hξ _ _ _)
          · intro δ δ₀ ψ₁ ψ₂ Δ₁ h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ δ₁ ψ₁ ψ₂ Δ₁ h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ ξ Δ₁ g h
            exact absurd h (ne_of_headTag (by simp))
          · intro δ δ₀ ξ Δ₁ m h
            exact absurd h (ne_of_headTag (by simp))
          · -- PRINCIPAL: (Pr⁻) against (Pr) on the same atom.
            intro δ δ₀ a₁ n₁ Δ₁ _ hmatch hlt hs' heP hssR
            -- `rank` does not see the subject, so the positive form of the rank
            -- bound has to be spelled out for unification to find `n₀`.
            have hr : rank (prAtom I a₀ n₀) ≤ ρ := hφ
            exact reduction_npr_principal_dispatch ih2 hs' ha hr hmatch hb hlt hprem
              (fun x hx => hss (List.mem_cons_of_mem _ hx)) heP hssR
          · intro δ δ₀ a₁ n₁ Δ₁ _ h
            exact absurd h (ne_of_headTag (by simp))
        · have hmem : nmemAt (lvl a₀) (I.num n₀) (I.num a₀) ∈ Θ := by
            have := hss List.mem_cons_self
            simp only [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hcase
            · exact h
          have hs' : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
            le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb) hs)
          have key := ihp hs' hφ (Θ := ∼(I.inst (body a₀) n₀) :: Θ)
            (by
              intro x hx
              simp only [List.mem_cons] at hx ⊢
              rcases hx with rfl | hx
              · tauto
              · have := hss (List.mem_cons_of_mem _ hx)
                simp only [List.mem_cons] at this
                tauto)
            he
            (by
              intro x hx
              have := hst hx
              simp only [List.mem_cons] at this ⊢
              tauto)
          exact drop_head (.npr ha (OrdinalNotation.redOrd_lt_left γ hb) key) hmem
    | @cut α' α₀ α₁ χ Γ₁ Γ₂ hc hb1 hb2 hpp hnn ihp ihn =>
        intro hs φ hφ Θ Δ₀ hss he hst
        have hs1 : OrdinalNotation.nadd α₀ γ ≤ OrdinalNotation.nadd β γ :=
          le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb1) hs)
        have hs2 : OrdinalNotation.nadd α₁ γ ≤ OrdinalNotation.nadd β γ :=
          le_of_lt (lt_of_lt_of_le (OrdinalNotation.nadd_lt_nadd_left γ hb2) hs)
        have hsubR : ∀ ζ : Proposition LRA, Δ₀ ⊆ ∼φ :: ζ :: Θ := by
          intro ζ x hx
          have := hst hx
          simp only [List.mem_cons] at this ⊢
          tauto
        have kp := ihp hs1 hφ (Θ := χ :: Θ)
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hss (List.mem_append_left _ hx)
              simp only [List.mem_cons] at this
              tauto)
          he (hsubR χ)
        have kn := ihn hs2 hφ (Θ := ∼χ :: Θ)
          (by
            intro x hx
            simp only [List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · tauto
            · have := hss (List.mem_append_right _ hx)
              simp only [List.mem_cons] at this
              tauto)
          he (hsubR (∼χ))
        refine OmegaDerivableR.contraction ?_
          (OmegaDerivableR.cut hc (OrdinalNotation.redOrd_lt_left γ hb1)
            (OrdinalNotation.redOrd_lt_left γ hb2) kp kn)
        intro x hx
        simp only [List.mem_append] at hx
        tauto

/-- **Reduction.**  Two derivations at rank `ρ` that cut against each other on a
formula of rank at most `ρ` combine into one at rank `ρ`, at the doubled sum of
their heights.

`MemFree A` is the one hypothesis `ACAOmega/Reduction.lean`'s `reduction` does
not have: without it an axiom could be a set atom and the (Pr)/axiom pair would
be an irreducible principal case. -/
theorem reduction (hA : MemFree A) {ρ : Gamma0Note} (β γ : O)
    {Γ₀ Δ₀ Θ : Sequent LRA} {φ : Proposition LRA}
    (hφ : rank φ ≤ ρ)
    (hd : OmegaDerivableR A I ρ β Γ₀) (hss : Γ₀ ⊆ φ :: Θ)
    (he : OmegaDerivableR A I ρ γ Δ₀) (hst : Δ₀ ⊆ ∼φ :: Θ) :
    OmegaDerivableR A I ρ (OrdinalNotation.redOrd β γ) Θ :=
  reduction_aux hA (OrdinalNotation.nadd β γ) β γ le_rfl hd hφ hss he hst

/-! ### Elimination and the first cut-elimination theorem -/

/-- `ρ` is a predecessor bound of `ρ'`: every rank below `ρ'` is at most `ρ`.
`PredBound ρ (ρ + 1)` holds, and this is the only way the elimination lemma
speaks about successors. -/
def PredBound (ρ ρ' : Gamma0Note) : Prop := ∀ a : Gamma0Note, a < ρ' → a ≤ ρ

theorem predBound_refl (ρ : Gamma0Note) : PredBound ρ ρ := fun _ h => le_of_lt h

/-- One level of cut rank, at the cost of one `ω`-power. -/
theorem elimination (hA : MemFree A) {ρ ρ' : Gamma0Note} (hρ : PredBound ρ ρ') :
    ∀ {α : O} {Γ : Sequent LRA}, OmegaDerivableR A I ρ' α Γ →
      OmegaDerivableR A I ρ (OrdinalNotation.omegaPow α) Γ := by
  intro α Γ h
  induction h with
  | atom h => exact .atom h
  | identity rl v => exact .identity rl v
  | verum => exact .verum
  | or hlt _ ih => exact .or (OrdinalNotation.omegaPow_lt_omegaPow hlt) ih
  | and hb hc _ _ ihp ihq =>
      exact .and (OrdinalNotation.omegaPow_lt_omegaPow hb)
        (OrdinalNotation.omegaPow_lt_omegaPow hc) ihp ihq
  | omegaRule f hf _ ih =>
      exact .omegaRule (fun n => OrdinalNotation.omegaPow (f n))
        (fun n => OrdinalNotation.omegaPow_lt_omegaPow (hf n)) ih
  | exs n hlt _ ih => exact .exs n (OrdinalNotation.omegaPow_lt_omegaPow hlt) ih
  | contraction ss _ ih => exact .contraction ss ih
  | pr ha hlt _ ih => exact .pr ha (OrdinalNotation.omegaPow_lt_omegaPow hlt) ih
  | npr ha hlt _ ih => exact .npr ha (OrdinalNotation.omegaPow_lt_omegaPow hlt) ih
  | @cut α' β' γ' φ Γ₁ Γ₂ hrank hb hc _ _ ihp ihn =>
      have hφ : rank φ ≤ ρ := hρ _ hrank
      have hkey := reduction hA (OrdinalNotation.omegaPow β') (OrdinalNotation.omegaPow γ')
        (Θ := Γ₁ ++ Γ₂) hφ ihp
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr (List.mem_append_left _ hx))
        ihn
        (by
          intro x hx
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr (List.mem_append_right _ hx))
      exact hkey.mono_ord
        (le_of_lt (OrdinalNotation.redOrd_lt_omegaPow
          (OrdinalNotation.omegaPow_lt_omegaPow hb) (OrdinalNotation.omegaPow_lt_omegaPow hc)))

/-- `Chain k ρ ρ'`: `ρ'` is reached from `ρ` by `k` predecessor-bound steps —
the generic form of `ρ' = ρ + k`. -/
def Chain : ℕ → Gamma0Note → Gamma0Note → Prop
  | 0, ρ, ρ' => ρ' ≤ ρ
  | k + 1, ρ, ρ' => ∃ ρ'', PredBound ρ'' ρ' ∧ Chain k ρ ρ''

/-- **The first cut-elimination theorem** for the ramified calculus.  Rank
`ρ + k` at height `α` becomes rank `ρ` at height the `k`-fold `ω`-tower over
`α`. -/
theorem cutElimination_chain (hA : MemFree A) :
    ∀ (k : ℕ) {ρ ρ' : Gamma0Note}, Chain k ρ ρ' → ∀ {α : O} {Γ : Sequent LRA},
      OmegaDerivableR A I ρ' α Γ →
        OmegaDerivableR A I ρ (OrdinalNotation.omegaTower k α) Γ := by
  intro k
  induction k with
  | zero =>
      intro ρ ρ' h α Γ hd
      exact hd.mono_rank h
  | succ k ih =>
      intro ρ ρ' h α Γ hd
      obtain ⟨ρ'', hpb, hch⟩ := h
      exact ih hch (elimination hA hpb hd)

/-- A `Chain` may always be raised to start at the larger of its base and its
top, which is the form the predicative elimination below consumes. -/
theorem chain_max {k : ℕ} {ρ a : Gamma0Note} (h : Chain k ρ a) :
    ∃ k', Chain k' ρ (max ρ a) := by
  rcases le_total a ρ with hle | hle
  · exact ⟨0, by rw [max_eq_left hle]; exact le_rfl⟩
  · exact ⟨k, by rw [max_eq_right hle]; exact h⟩

end OmegaDerivableR

end Ramified

end OrdinalAnalysis
